#!/bin/bash

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

set -u

function usage() {
    echo "Usage: $0 -i INPUT_DIR [-o OUTPUT_DIR] TARGET..."
    echo
    echo "Run SymCC-instrumented TARGET in a loop, feeding newly generated inputs back "
    echo "into it. Initial inputs are expected in INPUT_DIR, and new inputs are "
    echo "continuously read from there. If OUTPUT_DIR is specified, a copy of the corpus "
    echo "and of each generated input is preserved there. TARGET may contain the special "
    echo "string \"@@\", which is replaced with the name of the current input file."
    echo
    echo "Note that SymCC never changes the length of the input, so be sure that the "
    echo "initial inputs cover all required input lengths."
}

while getopts "t:i:o:" opt; do
    case "$opt" in
        i)
            in=$OPTARG
            ;;
        o)
            out=$OPTARG
            ;;
        t)
            tool=$OPTARG
            ;;
        *)
            usage
            exit 1
            ;;
    esac
done
shift $((OPTIND-1))
target=$@
timeout="timeout -k 5 90"

if [[ ! -v in ]]; then
    echo "Please specify the input directory!"
    usage
    exit 1
fi

if [ "${tool}" = "symfusion" ]; then
    export HYBRID_CONF_FILE=${out}/hybrid.conf
    export LD_BIND_NOW=1
    export SYMFUSION_HYBRID=1

    echo "Generating symfusion config..."
    "${SCRIPT_DIR}/../../runner/symfusion.py" -g "${HYBRID_CONF_FILE}" -i ${in} -o ${out} -- $target >/dev/null

#     export SYMFUSION_CEX_CACHE_DIR=${out}/cache
#     mkdir ${SYMFUSION_CEX_CACHE_DIR}

#     export SYMFUSION_AVOID_CACHE_DIR=${out}/avoid
#     mkdir ${SYMFUSION_AVOID_CACHE_DIR} 

    export CONCOLIC_WRAPPER="${SCRIPT_DIR}/../../symqemu-hybrid/x86_64-linux-user/symqemu-x86_64"

elif [ "${tool}" = "symcc" ]; then
    export CONCOLIC_WRAPPER=""

elif [ "${tool}" = "symqemu" ]; then
    export CONCOLIC_WRAPPER="${SCRIPT_DIR}/../../original/symqemu/x86_64-linux-user/symqemu-x86_64"
    # export CONCOLIC_WRAPPER="/mnt/ssd/symbolic/symqemu/x86_64-linux-user/symqemu-x86_64"
fi

# Create the work environment
work_dir=${out}/workdir # $(mktemp -d)
mkdir ${work_dir}
mkdir $work_dir/{next,symcc_out}
touch $work_dir/analyzed_inputs
mkdir -p $out/tools/concolic/queue

function cleanup() {
    rm -rf $work_dir
}

# trap cleanup EXIT

# Copy all files in the source directory to the destination directory, renaming
# them according to their hash.
function copy_with_unique_name() {
    local source_dir="$1"
    local dest_dir="$2"

    if [ -n "$(ls -A $source_dir)" ]; then
        local f
        for f in $source_dir/*; do
            local dest="$dest_dir/$(sha256sum $f | cut -d' ' -f1)"
            cp "$f" "$dest"
        done
    fi
}


COUNTER=0
function copy_with_unique_name_afl() {
    local source_dir="$1"
    local dest_dir="$2"

    if [ -n "$(ls -A $source_dir)" ]; then
        local f
        for f in $source_dir/*; do
            local dest="$dest_dir/tools/concolic/queue/id:$(printf '%06d\n' ${COUNTER})"
            COUNTER=$((COUNTER+1))
            cp "$f" "$dest"
        done
    fi
}

# Copy files from the source directory into the next generation.
function add_to_next_generation() {
    local source_dir="$1"
    copy_with_unique_name "$source_dir" "$work_dir/next"
}

# If an output directory is set, copy the files in the source directory there.
function maybe_export() {
    local source_dir="$1"
    if [[ -v out ]]; then
        copy_with_unique_name_afl "$source_dir" "$out"
    fi
    if [ -n "$(ls -A $source_dir)" ]; then
        local f
        for f in $source_dir/*; do
            rm $f
        done
    fi
}

# Copy those files from the input directory to the next generation that haven't
# been analyzed yet.
function maybe_import() {
    if [ -n "$(ls -A $in)" ]; then
        local f
        for f in $in/*; do
            if grep -q "$(basename $f)" $work_dir/analyzed_inputs; then
                continue
            fi

            if [ -e "$work_dir/next/$(basename $f)" ]; then
                continue
            fi

            echo "Importing $f from the input directory"
            cp "$f" "$work_dir/next"
        done
    fi
}

AFL_COUNTER=0
function maybe_import_from_AFL() {
    while true; do
        f=$(ls -A $out/tools/afl-master/queue/id:$(printf '%06d\n' ${AFL_COUNTER})* 2>/dev/null)
        echo $f
        if [ -n "$f" ]; then
            local dest="$work_dir/next/$(sha256sum $f | cut -d' ' -f1)"
            cp "$f" "$dest"
            echo "Importing from AFL: $f to $dest"
            AFL_COUNTER=$((AFL_COUNTER+1))
        else
            break
        fi
    done
}

function ctrlc() {
    exit 0
}
trap ctrlc SIGINT

# Set up the shell environment
export SYMCC_OUTPUT_DIR=$work_dir/symcc_out
export SYMCC_ENABLE_LINEARIZATION=1
export SYMCC_AFL_COVERAGE_MAP=$work_dir/map

export AFL_TRY_AFFINITY=1
export AFL_NO_UI=1
"/afl/afl-fuzz" -M afl-master -t 5000 -m 100M -i $in \
    -o ${out}/tools \
    -- ${target[0]/".${tool}"/".afl"} >/dev/null 2>&1 &

FUZZER_PID=$!

if [ "${tool}" = "afl" ]; then
    wait
    exit 0
fi

while ps -p $FUZZER_PID > /dev/null 2>&1 && \
    [[ ! -f "${out}/tools/afl-master/fuzz_bitmap" ]]; do
    echo "Waiting fuzzer to create bitmap..." && sleep 1
done

export AFL_MAP_SIZE=`stat --printf="%s" ${out}/tools/afl-master/fuzz_bitmap`

echo "AFL_MAP_SIZE: ${AFL_MAP_SIZE}"

# mkdir -p ${out}/tools/afl-master/queue

if [ "${tool}" = "symfusion" ]; then
    rm -rf ${out}/tools/concolic
    echo "Starting SymFusion..."
    /symfusion/runner/symfusion.py -f -i $in -o ${out}/tools/concolic -q ${QUEUE_MODE} -t 90 -a ${out}/tools/afl-master -- $target 
    exit 0
fi

# Run generation after generation until we don't generate new inputs anymore
gen_count=0
while true; do
    # Initialize the generation
    maybe_import
    maybe_import_from_AFL
    mv $work_dir/{next,cur}
    mkdir $work_dir/next

    # Run it (or wait if there's nothing to run on)
    if [ -n "$(ls -A $work_dir/cur)" ]; then
        echo "Generation $gen_count..."

        for f in $work_dir/cur/*; do
            if grep -q "$(basename $f)" $work_dir/analyzed_inputs; then
                continue
            fi

            echo "Running on $f"
            # xxd $f
            if [[ "$target " =~ " @@ " ]]; then
                env SYMCC_INPUT_FILE=$f $timeout ${CONCOLIC_WRAPPER} ${target[@]/@@/$f} >/dev/null 2>&1
            else
                $timeout ${CONCOLIC_WRAPPER} $target <$f >/dev/null 2>&1
            fi

            # ls $work_dir/symcc_out | wc -l
            # Make the new test cases part of the next generation
            add_to_next_generation $work_dir/symcc_out
            maybe_export $work_dir/symcc_out
            echo $(basename $f) >> $work_dir/analyzed_inputs
            rm -f $f
        done

        rm -rf $work_dir/cur
        gen_count=$((gen_count+1))
    else
        # echo "Waiting for more input..."
        rmdir $work_dir/cur
        exit 0
    fi
done
