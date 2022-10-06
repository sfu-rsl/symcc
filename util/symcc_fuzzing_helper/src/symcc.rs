// This file is part of SymCC.
//
// SymCC is free software: you can redistribute it and/or modify it under the
// terms of the GNU General Public License as published by the Free Software
// Foundation, either version 3 of the License, or (at your option) any later
// version.
//
// SymCC is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
// A PARTICULAR PURPOSE. See the GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License along with
// SymCC. If not, see <https://www.gnu.org/licenses/>.

use anyhow::{bail, ensure, Context, Result};
use regex::Regex;
use std::cmp;
use std::collections::HashSet;
use std::ffi::{OsStr, OsString};
use std::fs::{self, File};
use std::io::{self, Read};
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::str;
use std::time::{Duration, Instant};
use std::env;
use nix::unistd;
use nix::sys::stat;
use std::thread;
use std::io::Write;
use std::process::Child;
use nix::sys::signal::{self, Signal};
use nix::unistd::Pid;

const TIMEOUT: u128 = 90;

/// Replace the first '@@' in the given command line with the input file.
fn insert_input_file<S: AsRef<OsStr>, P: AsRef<Path>>(
    command: &[S],
    input_file: P,
) -> Vec<OsString> {
    let mut fixed_command: Vec<OsString> = command.iter().map(|s| s.into()).collect();
    if let Some(at_signs) = fixed_command.iter_mut().find(|s| *s == "@@") {
        *at_signs = input_file.as_ref().as_os_str().to_os_string();
    }

    fixed_command
}

/// A coverage map as used by AFL.
pub struct AflMap {
    //data: [u8; 65536],
    data: Vec<u8>
}

impl AflMap {
    /// Create an empty map.
    pub fn new() -> AflMap {
        //AflMap { data: [0; 65536] }
        AflMap { data: Vec::new() }
    }

    /// Load a map from disk.
    pub fn load(path: impl AsRef<Path>) -> Result<AflMap> {
        let data = fs::read(&path).with_context(|| {
            format!(
                "Failed to read the AFL bitmap that \
                 afl-showmap should have generated at {}",
                path.as_ref().display()
            )
        })?;
        let mut result = AflMap::new();
        result.data = data;
        Ok(result)
    }

    /// Merge with another coverage map in place.
    ///
    /// Return true if the map has changed, i.e., if the other map yielded new
    /// coverage.
    pub fn merge(&mut self, other: &AflMap) -> bool {
        let mut interesting = false;
        //println!("Merging");
        //println!("Size of data: {si}", si=self.data.len());
        //println!("Size of other data: {si}", si=other.data.len());
        // The first time merge is called self.data will be empty.
        // Thus in that case we simply clone the other vector.
        if self.data.len() == 0 {
            //println!("own data is zero");
            self.data = other.data.clone();
            interesting = true;
        }
        else {
            // let mut data_counter = 0;
            // let mut diffs = 0;
            for (known, new) in self.data.iter_mut().zip(other.data.iter()) {
                // data_counter += 1;
                if *known != (*known | new) {
                    // diffs += 1;
                    *known |= new;
                    interesting = true;
                }
            }
            // println!("Data counter: {dc}", dc=data_counter);
            // println!("Diffs: {di}", di=diffs);
        }
        if interesting {
            // println!("is interesting");
        }
        else {
            // println!("Is not interesting");
        }
        interesting
    }
}

/// Score of a test case.
///
/// We use the lexical comparison implemented by the derived implementation of
/// Ord in order to compare according to various criteria.
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
struct TestcaseScore {
    /// First criterion: new coverage
    new_coverage: bool,

    /// Second criterion: being derived from seed inputs
    derived_from_seed: bool,

    /// Third criterion: size (smaller is better)
    file_size: i128,

    /// Fourth criterion: name (containing the ID)
    base_name: OsString,
}

impl TestcaseScore {
    /// Score a test case.
    ///
    /// If anything goes wrong, return the minimum score.
    fn new(t: impl AsRef<Path>) -> Self {
        let size = match fs::metadata(&t) {
            Err(e) => {
                // Has the file disappeared?
                log::warn!(
                    "Warning: failed to score test case {}: {}",
                    t.as_ref().display(),
                    e
                );

                return TestcaseScore::minimum();
            }
            Ok(meta) => meta.len(),
        };

        let name: OsString = match t.as_ref().file_name() {
            None => return TestcaseScore::minimum(),
            Some(n) => n.to_os_string(),
        };
        let name_string = name.to_string_lossy();

        TestcaseScore {
            new_coverage: name_string.ends_with("+cov"),
            derived_from_seed: name_string.contains("orig:"),
            file_size: -i128::from(size),
            base_name: name,
        }
    }

    /// Return the smallest possible score.
    fn minimum() -> TestcaseScore {
        TestcaseScore {
            new_coverage: false,
            derived_from_seed: false,
            file_size: std::i128::MIN,
            base_name: OsString::from(""),
        }
    }
}

/// A directory that we can write test cases to.
pub struct TestcaseDir {
    /// The path to the (existing) directory.
    pub path: PathBuf,
    /// The next free ID in this directory.
    current_id: u64,
}

impl TestcaseDir {
    /// Create a new test-case directory in the specified location.
    ///
    /// The parent directory must exist.
    pub fn new(path: impl AsRef<Path>) -> Result<TestcaseDir> {
        let dir = TestcaseDir {
            path: path.as_ref().into(),
            current_id: 0,
        };

        fs::create_dir(&dir.path)
            .with_context(|| format!("Failed to create directory {}", dir.path.display()))?;
        Ok(dir)
    }
}

/// Copy a test case to a directory, using the parent test case's name to derive
/// the new name.
pub fn copy_testcase(
    testcase: impl AsRef<Path>,
    target_dir: &mut TestcaseDir,
    parent: impl AsRef<Path>,
) -> Result<()> {
    let orig_name = parent
        .as_ref()
        .file_name()
        .expect("The input file does not have a name")
        .to_string_lossy();
    ensure!(
        orig_name.starts_with("id:"),
        "The name of test case {} does not start with an ID",
        parent.as_ref().display()
    );

    if let Some(orig_id) = orig_name.get(3..9) {
        let new_name = format!("id:{:06},src:{}", target_dir.current_id, &orig_id);
        let target = target_dir.path.join(new_name);
        log::debug!("Creating test case {}", target.display());
        fs::copy(testcase.as_ref(), target).with_context(|| {
            format!(
                "Failed to copy the test case {} to {}",
                testcase.as_ref().display(),
                target_dir.path.display()
            )
        })?;

        target_dir.current_id += 1;
    } else {
        bail!(
            "Test case {} does not contain a proper ID",
            parent.as_ref().display()
        );
    }

    Ok(())
}

/// Information on the run-time environment.
///
/// This should not change during execution.
#[derive(Debug)]
pub struct AflConfig {
    /// The location of the afl-showmap program.
    show_map: PathBuf,

    /// The command that AFL uses to invoke the target program.
    target_command: Vec<OsString>,

    /// Do we need to pass data to standard input?
    use_standard_input: bool,

    /// Are we using AFL's QEMU mode?
    use_qemu_mode: bool,

    /// The fuzzer instance's queue of test cases.
    queue: PathBuf,
    own_queue: Option<PathBuf>,

    aflmap_lib: bool
}

/// Possible results of afl-showmap.
pub enum AflShowmapResult {
    /// The map was created successfully.
    Success(Box<AflMap>),
    /// The target timed out or failed to execute.
    Hang,
    /// The target crashed.
    Crash,
    /// afl-showmap crashed
    Failure,
}

impl AflConfig {
    /// Read the AFL configuration from a fuzzer instance's output directory.
    pub fn load(fuzzer_output: impl AsRef<Path>, output: impl AsRef<Path>) -> Result<Self> {
        let afl_stats_file_path = fuzzer_output.as_ref().join("fuzzer_stats");
        let mut afl_stats_file = File::open(&afl_stats_file_path).with_context(|| {
            format!(
                "Failed to open the fuzzer's stats at {}",
                afl_stats_file_path.display()
            )
        })?;
        let mut afl_stats = String::new();
        afl_stats_file
            .read_to_string(&mut afl_stats)
            .with_context(|| {
                format!(
                    "Failed to read the fuzzer's stats at {}",
                    afl_stats_file_path.display()
                )
            })?;
        let afl_command: Vec<_> = afl_stats
            .lines()
            .find(|&l| l.starts_with("command_line"))
            .expect("The fuzzer stats don't contain the command line")
            .splitn(2, ':')
            .nth(1)
            .expect("The fuzzer stats follow an unknown format")
            .trim()
            .split_whitespace()
            .collect();
        let mut afl_target_command: Vec<_> = afl_command
            .iter()
            .skip_while(|s| **s != "--")
            .map(OsString::from)
            .collect();

        let mut aflmap_lib = false;
        let mut qemu_mode = afl_command.contains(&"-Q".into());
        if let Ok(_) = env::var("SYMCC_AFLMAP_LIB") {
            if !qemu_mode {
                // FIXME: specific to our setup 
                afl_target_command[1] = OsString::from(afl_target_command[1].clone().into_string().unwrap().replace(".afl", ".symqemu"));
                qemu_mode = true;
                aflmap_lib = true;
            }
        }

        let afl_binary_dir = Path::new(
            afl_command
                .get(0)
                .expect("The AFL command is unexpectedly short"),
        )
        .parent()
        .unwrap();

        let mut own_queue = None;
        if let Ok(_) = env::var("SYMCC_PICK_FROM_OWN_QUEUE") { 
            own_queue = Some(output.as_ref().join("queue"));
        }

        Ok(AflConfig {
            show_map: afl_binary_dir.join("afl-showmap"),
            use_standard_input: !afl_target_command.contains(&"@@".into()),
            use_qemu_mode: qemu_mode,
            target_command: afl_target_command,
            queue: fuzzer_output.as_ref().join("queue"),
            own_queue: own_queue,
            aflmap_lib: aflmap_lib
        })
    }

    /// Return the most promising unseen test case of this fuzzer.
    pub fn best_new_testcase(&self, seen: &HashSet<PathBuf>) -> Result<Option<PathBuf>> {

        let fuzzer_queue = fs::read_dir(&self.queue)
            .with_context(|| {
                format!(
                    "Failed to open the fuzzer's queue at {}",
                    self.queue.display()
                )
            })?
            .collect::<io::Result<Vec<_>>>()
            .with_context(|| {
                format!(
                    "Failed to read the fuzzer's queue at {}",
                    self.queue.display()
                )
            })?
            .into_iter();

        let best;
        match &self.own_queue { 
            Some(q) => {
                let own_queue = fs::read_dir(q)
                    .with_context(|| {
                        format!(
                            "Failed to open the fuzzer's queue at {}",
                            self.queue.display()
                        )
                    })?
                    .collect::<io::Result<Vec<_>>>()
                    .with_context(|| {
                        format!(
                            "Failed to read the fuzzer's queue at {}",
                            self.queue.display()
                        )
                    })?
                    .into_iter();
                best = fuzzer_queue.chain(own_queue)
                    .map(|entry| entry.path())
                    .filter(|path| path.is_file() && !seen.contains(path))
                    .max_by_key(|path| TestcaseScore::new(path));
            },
            None => {
                best = fuzzer_queue
                    .map(|entry| entry.path())
                    .filter(|path| path.is_file() && !seen.contains(path))
                    .max_by_key(|path| TestcaseScore::new(path));
            }
        }

        Ok(best)
    }

    pub fn run_showmap(
        &self,
        testcase_bitmap: impl AsRef<Path>,
        testcase: impl AsRef<Path>,
    ) -> Result<AflShowmapResult> {
        let mut afl_show_map = Command::new(&self.show_map);
        if self.use_qemu_mode {
            afl_show_map.arg("-Q");
        }
        if self.aflmap_lib {
            afl_show_map.env("AFL_INST_LIBS", "1");
            afl_show_map.env_remove("AFL_MAP_SIZE");
        }
        afl_show_map
            .args(&["-t", "10000", "-m", "none", "-b", "-o"])
            .arg(testcase_bitmap.as_ref())
            .args(insert_input_file(&self.target_command, &testcase))
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .stdin(if self.use_standard_input {
                Stdio::piped()
            } else {
                Stdio::null()
            });

        log::debug!("Running afl-showmap as follows: {:?}", &afl_show_map);
        let mut afl_show_map_child = afl_show_map.spawn().context("Failed to run afl-showmap")?;

        if self.use_standard_input {
            // NOTE: a program may quit before reading the entire input...
            //       we have to handle this scenario.
            let mut f = File::open(&testcase).expect("Cannot open testcase");
            let metadata = fs::metadata(&testcase).expect("unable to read metadata of testcase");
            let writer = afl_show_map_child
                .stdin
                .as_mut()
                .expect("Failed to open the stardard input of afl-showmap");
            for i in 0..metadata.len() {
                let mut buffer = vec![0; 1];
                f.read(&mut buffer).expect("buffer overflow");
                match writer.write(&buffer) {
                    Ok(_) => {
                        // println!("Written byte {}", i);
                    }
                    Err(e) => {
                        if i == 0 {
                            panic!("Cannot write any byte to the pipe: {}", e)
                        } else {
                            log::warn!("Error after writing {} bytes into the pipe: {}", i, e);
                            break;
                        }
                    }
                }
            }
        }

        let afl_show_map_status = afl_show_map_child
            .wait()
            .context("Failed to wait for afl-showmap")?;
        log::debug!("afl-showmap returned {}", &afl_show_map_status);
        match afl_show_map_status.code() {
            Some(code) => match code {
                0 => {
                    let map = AflMap::load(&testcase_bitmap).with_context(|| {
                        format!(
                            "Failed to read the AFL bitmap that \
                             afl-showmap should have generated at {}",
                            testcase_bitmap.as_ref().display()
                        )
                    })?;
                    Ok(AflShowmapResult::Success(Box::new(map)))
                }
                1 => Ok(AflShowmapResult::Hang),
                2 => Ok(AflShowmapResult::Crash),
                unexpected => panic!("Unexpected return code {} from afl-showmap", unexpected),
            }, 
            None => {
                log::debug!("No exit status for afl-showmap");
                Ok(AflShowmapResult::Failure)
            }
        }
    }
}

fn as_u16_le(array: &[u8; 2]) -> u32 {
    ((array[0] as u32) <<  0) +
    ((array[1] as u32) <<  8)
}

fn as_i32_le(array: &[u8; 4]) -> i32 {
    ((array[0] as i32) <<  0) +
    ((array[1] as i32) <<  8) +
    ((array[2] as i32) << 16) +
    ((array[3] as i32) << 24)
}



/// The run-time configuration of SymCC.
#[derive(Debug)]
pub struct SymCC {
    /// Do we pass data to standard input?
    use_standard_input: bool,

    /// The cumulative bitmap for branch pruning.
    bitmap: PathBuf,

    /// The place to store the current input.
    input_file: PathBuf,

    /// The command to run.
    command: Vec<OsString>,

    /// Pipes used for communicating with the forkserver
    pipe_read_path: PathBuf,
    pipe_write_path: PathBuf,
    child_pid: PathBuf,
    child_exit_status: PathBuf,
    pub pipe_read: Option<File>,
    pub pipe_write: Option<File>,
    pub forkserver: Option<Child>
}

/// The result of executing SymCC.
pub struct SymCCResult {
    /// The generated test cases.
    pub test_cases: Vec<PathBuf>,
    /// Whether the process was killed (e.g., out of memory, timeout).
    pub killed: bool,
    /// The total time taken by the execution.
    pub time: Duration,
    /// The time spent in the solver (Qsym backend only).
    pub solver_time: Option<Duration>,
}

impl SymCC {
    /// Create a new SymCC configuration.
    pub fn new(output_dir: PathBuf, command: &[String]) -> Self {
        let input_file = output_dir.join(".cur_input");
        let fifo_path_read = output_dir.join("pipe_read");
        let fifo_path_write = output_dir.join("pipe_write");

        SymCC {
            use_standard_input: !command.contains(&String::from("@@")),
            bitmap: output_dir.join("bitmap"),
            command: insert_input_file(command, &input_file),
            input_file: input_file,
            pipe_read_path: fifo_path_read,
            pipe_write_path: fifo_path_write,
            child_pid: output_dir.join("workdir").join("pid"),
            child_exit_status: output_dir.join("workdir").join("done"),
            pipe_read: None,
            pipe_write: None,
            forkserver: None
        }
    }

    pub fn initialize_pipes(&mut self, output_dir: &PathBuf) {
        if let Ok(_) = env::var("SYMFUSION_FORKSERVER") { 
            /*
            let output = Command::new("ls")
                .arg(&output_dir)
                .output()
                .expect("failed to execute process");
            println!("Output: {}", String::from_utf8(output.stdout).unwrap());
            */
            match unistd::mkfifo(&self.pipe_read_path, stat::Mode::S_IRWXU) {
                Ok(_) => println!("created {:?}", self.pipe_read_path),
                Err(err) => println!("Error creating fifo {:?}: {}", self.pipe_read_path, err),
            }
            match unistd::mkfifo(&self.pipe_write_path, stat::Mode::S_IRWXU) {
                Ok(_) => println!("created {:?}", self.pipe_write_path),
                Err(err) => println!("Error creating fifo {:?}: {}", self.pipe_write_path, err),
            }

            let file_env_var = if self.use_standard_input { "SYMCC_INPUT_STDIN_FILE" } else { "SYMCC_INPUT_FILE" }; 

            // println!("{:?}", self.command);
            let _cmd_len = self.command.len();
            let forkserver = Command::new("setsid") // &self.command[0]
                .args(&self.command) // &self.command[1..cmd_len]
                .env("SYMFUSION_PATH_FORKSERVER_DONE", &self.child_exit_status)
                .env("SYMFUSION_FORKSERVER_PIPE_WRITE", &self.pipe_read_path)
                .env("SYMFUSION_FORKSERVER_PIPE_READ", &self.pipe_write_path)
                .env("SYMFUSION_PATH_FORKSERVER_PID", &self.child_pid)
                .env("SYMCC_ENABLE_LINEARIZATION", "1")
                .env("SYMCC_AFL_COVERAGE_MAP", &self.bitmap)
                .env("SYMCC_OUTPUT_DIR", output_dir.join("workdir"))
                .env(file_env_var, &self.input_file)
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .stdin(Stdio::null())
                .spawn().unwrap();
            self.forkserver = Some(forkserver);
            self.pipe_write = Some(File::create(&self.pipe_write_path).unwrap());
            self.pipe_read = Some(File::open(&self.pipe_read_path).unwrap());
            // thread::sleep(Duration::from_secs(5));
        }
    }

    /// Try to extract the solver time from the logs produced by the Qsym
    /// backend.
    fn parse_solver_time(output: Vec<u8>) -> Option<Duration> {
        let re = Regex::new(r#""solving_time": (\d+)"#).unwrap();
        output
            // split into lines
            .rsplit(|n| *n == b'\n')
            // convert to string
            .filter_map(|s| str::from_utf8(s).ok())
            // check that it's an SMT log line
            .filter(|s| s.trim_start().starts_with("[STAT] SMT:"))
            // find the solving_time element
            .filter_map(|s| re.captures(s))
            // convert the time to an integer
            .filter_map(|c| c[1].parse().ok())
            // associate the integer with a unit
            .map(Duration::from_micros)
            // get the first one
            .next()
    }

    /// Run SymCC on the given input, writing results to the provided temporary
    /// directory.
    ///
    /// If SymCC is run with the Qsym backend, this function attempts to
    /// determine the time spent in the SMT solver and report it as part of the
    /// result. However, the mechanism that the backend uses to report solver
    /// time is somewhat brittle.
    pub fn run(
        &mut self,
        input: impl AsRef<Path>,
        output_dir: impl AsRef<Path>,
    ) -> Result<SymCCResult> {
        fs::copy(&input, &self.input_file).with_context(|| {
            format!(
                "Failed to copy the test case {} to our workbench at {}",
                input.as_ref().display(),
                self.input_file.display()
            )
        })?;

        fs::create_dir(&output_dir).with_context(|| {
            format!(
                "Failed to create the output directory {} for SymCC",
                output_dir.as_ref().display()
            )
        })?;

        let mut killed = false;
        let solver_time;
        let total_time;
        let start = Instant::now();

        match &mut self.pipe_write {
            Some(pipe) => {
                match pipe.write_all(&[0x23]) {
                    Ok(_) => {},
                    Err(e) => {
                        log::warn!("Cannot write in the pipe with forkserver: {:?}", e);
                    }
                }
                let wait_time_usecs = 200;
                let pid;
                loop {
                    match std::fs::metadata(&self.child_pid) {
                        Ok(metadata) => {
                            let mut f = File::open(&self.child_pid).expect("no file found");
                            let s = metadata.len();
                            if s == 4 {
                                let mut buffer : [u8; 4] = [0; 4];
                                f.read(&mut buffer).expect("buffer overflow");
                                pid = as_i32_le(&buffer);
                                log::info!("Child PID: {}", pid);
                                fs::remove_file(&self.child_pid)?;
                                break;
                            }
                        },
                        Err(_) => {
                            thread::sleep(Duration::from_micros(wait_time_usecs));
                        }
                    }
                    if start.elapsed().as_millis() > (TIMEOUT * 1000) {
                        log::warn!("No info about the child pid... timeout is passed!");
                        thread::sleep(Duration::from_micros(wait_time_usecs * 10));
                    }
                }
                loop {
                    match std::fs::metadata(&self.child_exit_status) {
                        Ok(metadata) => {
                            let mut f = File::open(&self.child_exit_status).expect("no file found");
                            let s = metadata.len();
                            if s == 4 {
                                let mut buffer : [u8; 4] = [0; 4];
                                f.read(&mut buffer).expect("buffer overflow");
                                let signal = as_u16_le(&[buffer[2], buffer[3]]);
                                let status_code = as_u16_le(&[buffer[0], buffer[1]]);
                                log::info!("Child exit status: {}", status_code);
                                fs::remove_file(&self.child_exit_status)?;
                                if signal > 0 {
                                    log::warn!("SymCC received signal {}", signal);
                                    killed = true;
                                }
                                break;
                            }
                        },
                        Err(_) => {
                            thread::sleep(Duration::from_micros(wait_time_usecs));
                        }
                    }
                    if start.elapsed().as_millis() > (TIMEOUT * 1000) {
                        if !killed {
                            log::warn!("Killing child due to timeout");
                            match signal::kill(Pid::from_raw(pid), Signal::SIGKILL) {
                                Ok(_) => {},
                                Err(e) => {
                                    log::warn!("Failed to kill child. Already dead? {:?}", e);
                                }
                            }
                            killed = true;
                        }
                    }
                }
                total_time = start.elapsed();
                solver_time = None;
            },
            None => {
                // setsid is needed to avoid some programs
                // from reading from /dev/tty
                let mut analysis_command = Command::new("setsid");
                analysis_command
                    .args(&["timeout", "-k", "1", &TIMEOUT.to_string()])
                    .args(&self.command)
                    .env("SYMCC_ENABLE_LINEARIZATION", "1")
                    .env("SYMCC_AFL_COVERAGE_MAP", &self.bitmap)
                    .env("SYMCC_OUTPUT_DIR", output_dir.as_ref())
                    .stdout(Stdio::null())
                    .stderr(Stdio::piped())
                    ; // capture SMT logs

                if self.use_standard_input {
                    analysis_command.stdin(Stdio::piped());
                } else {
                    analysis_command.stdin(Stdio::null());
                    analysis_command.env("SYMCC_INPUT_FILE", &self.input_file);
                }
            
                log::debug!("Running SymCC as follows: {:?}", &analysis_command);

                let mut child = analysis_command.spawn().context("Failed to run SymCC")?;
                if self.use_standard_input {
                    let pipe_stdin = child.stdin.as_mut().unwrap();
                    let r = io::copy(
                        &mut File::open(&self.input_file).with_context(|| {
                            format!(
                                "Failed to read the test input at {}",
                                self.input_file.display()
                            )
                        })?,
                        pipe_stdin,
                    );
                    match r {
                        Ok(_) => {},
                        Err(e) => {
                            log::warn!("Error when sending data through pipe: {:?}", e);
                        }
                    }
                }

                let result = child
                    .wait_with_output()
                    .context("Failed to wait for SymCC")?;

                total_time = start.elapsed();

                killed = match result.status.code() {
                    Some(code) => {
                        log::debug!("SymCC returned code {}", code);
                        (code == 124) || (code == -9) // as per the man-page of timeout
                    }
                    None => {
                        let maybe_sig = result.status.signal();
                        if let Some(signal) = maybe_sig {
                            log::warn!("SymCC received signal {} [time={}]", signal, start.elapsed().as_secs());
                        }
                        maybe_sig.is_some()
                    }
                };

                solver_time = SymCC::parse_solver_time(result.stderr);
                if solver_time.is_some() && solver_time.unwrap() > total_time {
                    log::warn!("Backend reported inaccurate solver time!");
                }
            }
        }
        
        let new_tests = fs::read_dir(&output_dir)
            .with_context(|| {
                format!(
                    "Failed to read the generated test cases at {}",
                    output_dir.as_ref().display()
                )
            })?
            .collect::<io::Result<Vec<_>>>()
            .with_context(|| {
                format!(
                    "Failed to read all test cases from {}",
                    output_dir.as_ref().display()
                )
            })?
            .iter()
            .map(|entry| entry.path())
            .collect();

        Ok(SymCCResult {
            test_cases: new_tests,
            killed,
            time: total_time,
            solver_time: solver_time.map(|t| cmp::min(t, total_time)),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_score_ordering() {
        let min_score = TestcaseScore::minimum();
        assert!(
            TestcaseScore {
                new_coverage: true,
                ..TestcaseScore::minimum()
            } > min_score
        );
        assert!(
            TestcaseScore {
                derived_from_seed: true,
                ..TestcaseScore::minimum()
            } > min_score
        );
        assert!(
            TestcaseScore {
                file_size: -4,
                ..TestcaseScore::minimum()
            } > min_score
        );
        assert!(
            TestcaseScore {
                base_name: OsString::from("foo"),
                ..TestcaseScore::minimum()
            } > min_score
        );
    }

    #[test]
    fn test_solver_time_parsing() {
        let output = r#"[INFO] New testcase: /tmp/output/000005
[STAT] SMT: { "solving_time": 14539, "total_time": 185091 }
[STAT] SMT: { "solving_time": 14869 }
[STAT] SMT: { "solving_time": 14869, "total_time": 185742 }
[STAT] SMT: { "solving_time": 15106 }"#;

        assert_eq!(
            SymCC::parse_solver_time(output.as_bytes().to_vec()),
            Some(Duration::from_micros(15106))
        );
        assert_eq!(
            SymCC::parse_solver_time("whatever".as_bytes().to_vec()),
            None
        );
    }
}