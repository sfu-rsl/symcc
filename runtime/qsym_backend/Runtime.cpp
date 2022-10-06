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

//
// Definitions that we need for the Qsym backend
//

#define HYBRID_DBG_CONSISTENCY_CHECK 0

#include "Runtime.h"
#include "GarbageCollection.h"

// C++
#if __has_include(<filesystem>)
#define HAVE_FILESYSTEM 1
#elif __has_include(<experimental/filesystem>)
#define HAVE_FILESYSTEM 0
#else
#error "We need either <filesystem> or the older <experimental/filesystem>."
#endif

#include <atomic>
#include <fstream>
#include <iostream>
#include <iterator>
#include <map>
#include <unordered_set>
#include <numeric>

#if HAVE_FILESYSTEM
#include <filesystem>
#else
#include <experimental/filesystem>
#endif

#ifdef DEBUG_RUNTIME
#include <chrono>
#endif

// C
#include <cstdio>

// Qsym
#include <afl_trace_map.h>
#include <call_stack_manager.h>
#include <expr_builder.h>
#include <solver.h>

// LLVM
#include <llvm/ADT/APInt.h>
#include <llvm/ADT/ArrayRef.h>

// Runtime
#include <Config.h>
#include <LibcWrappers.h>
#include "../Shadow.h"

namespace qsym {

ExprBuilder *g_expr_builder;
Solver *g_solver;
CallStackManager g_call_stack_manager;
z3::context *g_z3_context;

} // namespace qsym

namespace {

/// Indicate whether the runtime has been initialized.
std::atomic_flag g_initialized = ATOMIC_FLAG_INIT;
std::atomic_flag g_pre_initialized = ATOMIC_FLAG_INIT;
std::atomic_flag g_finalized = ATOMIC_FLAG_INIT;

/// The file that contains out input.
std::string inputFileName;

void deleteInputFile() { std::remove(inputFileName.c_str()); }

/// A mapping of all expressions that we have ever received from Qsym to the
/// corresponding shared pointers on the heap.
///
/// We can't expect C clients to handle std::shared_ptr, so we maintain a single
/// copy per expression in order to keep the expression alive. The garbage
/// collector decides when to release our shared pointer.
///
/// std::map seems to perform slightly better than std::unordered_map on our
/// workload.
std::map<SymExpr, qsym::ExprRef> allocatedExpressions;

SymExpr registerExpression(const qsym::ExprRef &expr) {
  SymExpr rawExpr = expr.get();

  if (allocatedExpressions.count(rawExpr) == 0) {
    // We don't know this expression yet. Create a copy of the shared pointer to
    // keep the expression alive.
    allocatedExpressions[rawExpr] = expr;
  }

  return rawExpr;
}

} // namespace

using namespace qsym;

#if HAVE_FILESYSTEM
namespace fs = std::filesystem;
#else
namespace fs = std::experimental::filesystem;
#endif

#define XXH_STATIC_LINKING_ONLY   /* access advanced declarations */
#define XXH_IMPLEMENTATION   /* access definitions */
#include "qsym/qsym/pintool/third_party/xxhash/xxhash.h"

// Tracer
static int bitmapSize = 0;
static uint8_t* bitmapEdgesMain = nullptr;
static uint8_t* bitmapEdgesAll = nullptr;
static uint8_t* bitmapTrace = nullptr;
static uint16_t* bitmapUnique = nullptr;
static XXH64_state_t* edgeState = nullptr;
static XXH64_state_t* pathMainHash = nullptr;
static XXH64_state_t* pathAllHash = nullptr;
static uintptr_t lastBasicBlockMainId = 0;
static uintptr_t lastBasicBlockAllId = 0;

void _sym_initialize(void) {
  if (getenv("SYMFUSION_HYBRID") == NULL) {
    _sym_pre_initialize_qemu();
    _sym_initialize_qemu();
  }
}

void _sym_pre_initialize_qemu(void){
  if (g_pre_initialized.test_and_set())
    return;

  loadConfig();
  initLibcWrappers();
  std::cerr << "This is SymFusion running with the QSYM backend" << std::endl;

  if (!g_config.fullyConcrete) {
    g_z3_context = new z3::context{};
    g_expr_builder = g_config.pruning ? PruneExprBuilder::create()
                                      : SymbolicExprBuilder::create();
  
  }

  if (g_config.pathTracerMode) {
    pathMainHash = XXH64_createState();
    XXH64_reset(pathMainHash, 0x0);
    pathAllHash = XXH64_createState();
    XXH64_reset(pathAllHash, 0x0);

    bitmapSize = g_config.bitmapSize;
    bitmapEdgesMain = (uint8_t*) calloc(1, g_config.bitmapSize);
    bitmapEdgesAll = (uint8_t*) calloc(1, g_config.bitmapSize);
    bitmapTrace = (uint8_t*) calloc(1, g_config.bitmapSize);
    bitmapUnique =  (uint16_t*) calloc(sizeof(short), g_config.bitmapSize);
    edgeState = XXH64_createState();
  }
}

void _sym_initialize_qemu(void) {
  if (g_initialized.test_and_set())
    return;

  if (g_config.fullyConcrete && !g_config.pathTracerMode && getenv("SYMCC_INPUT_STDIN_FILE") == NULL) {
    std::cerr
        << "Performing fully concrete execution (i.e., without symbolic input)"
        << std::endl;
    return;
  }

  // Check the output directory
  if (!fs::exists(g_config.outputDir) ||
      !fs::is_directory(g_config.outputDir)) {
    std::cerr << "Error: the output directory " << g_config.outputDir
              << " (configurable via SYMCC_OUTPUT_DIR) does not exist."
              << std::endl;
    exit(-1);
  }

  // Qsym requires the full input in a file
  if (g_config.inputFile.empty()) {
    std::cerr << "Reading program input until EOF (use Ctrl+D in a terminal)..."
              << std::endl;
    
    std::vector<char> inputData;
    if (getenv("SYMCC_INPUT_STDIN_FILE")) {
      // printf("Reading from %s\n", getenv("SYMCC_INPUT_STDIN_FILE"));
      auto a = std::ifstream(getenv("SYMCC_INPUT_STDIN_FILE"), std::ios::binary);
      std::istreambuf_iterator<char> in_begin(a), in_end;
      std::vector<char> inputCopyData(in_begin, in_end);
      inputData = inputCopyData;
    } else {
      std::istreambuf_iterator<char> in_begin(std::cin), in_end;
      std::vector<char> inputCopyData(in_begin, in_end);
      inputData = inputCopyData;
    }

    inputFileName = std::tmpnam(nullptr);
    std::ofstream inputFile(inputFileName, std::ios::trunc);
    std::copy(inputData.begin(), inputData.end(),
              std::ostreambuf_iterator<char>(inputFile));
    inputFile.close();

#ifdef DEBUG_RUNTIME
    std::cerr << "Loaded input:" << std::endl;
    std::copy(inputData.begin(), inputData.end(),
              std::ostreambuf_iterator<char>(std::cerr));
    std::cerr << std::endl;
#endif

    atexit(deleteInputFile);

    // Restore some semblance of standard input
    auto *newStdin = freopen(inputFileName.c_str(), "r", stdin);
    if (newStdin == nullptr) {
      perror("Failed to reopen stdin");
      exit(-1);
    }
  } else {
    inputFileName = g_config.inputFile;
    std::cerr << "Making data read from " << inputFileName << " as symbolic"
              << std::endl;
  }

  if (g_config.pathTracerMode || g_config.fullyConcrete)
    return;

  g_solver =
      new Solver(inputFileName, g_config.outputDir, g_config.aflCoverageMap);
}

static void saveBitmap(uint8_t* bitmap, char* path, int size) {
  if (bitmap) {
    std::ofstream ofs;
    ofs.open(path, std::ios::binary);
    if (ofs.fail())
      printf("Unable to open a bitmap to commit");
    ofs.write((char*)bitmap, size);
    ofs.close();
  }
}

static const uint8_t count_class_lookup8[256] = {
  0,          // [0]
  1,          // [1]
  2,          // [3]
  4, 4, 4, 4, // [4 ... 7]
  8, 8, 8, 8, 8, 8, 8, 8,
  16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
  32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 
  32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 
  64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 
  64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 
  64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 
  64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 
  128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 
  128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 
  128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 
  128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 
  128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 
  128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 
  128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 
  128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128 
};

static void compare_bitmaps(uint8_t* virgin_bitmap, char* trace_path, char* report_file) {
  // load trace bitmap
  FILE* fp = fopen(trace_path, "r");
  if (!fp) {
    printf("Cannot open: %s\n", trace_path);
    abort();
  }
  int count = 0;
  while (count < bitmapSize) {
    int res = fread(bitmapTrace + count, 1, bitmapSize - count, fp);
    if (res <= 0) break;
    count += res;
  }
  if (count < bitmapSize) {
    printf("Cannot read full bitmap: %s [%d]\n", trace_path, count);
    abort();
  }
  fclose(fp);

  // create report
  fp = fopen(report_file, "w");
  if (!fp) {
    printf("Cannot open: %s\n", report_file);
    abort();
  }

  // compare with virgin bitmap, update trace bitmap,
  // and write report about unique entries
  for (int i = 0; i < bitmapSize; i++) {
    uint8_t v = count_class_lookup8[virgin_bitmap[i]];
    if ((v | bitmapTrace[i]) != bitmapTrace[i]) {
      uint16_t index = (uint16_t) i;
      fwrite(&index, sizeof(index), 1, fp);
      bitmapTrace[i] |= v;
      // printf("Unique ID: %d\n", i);
    }
  }

  // close report
  fclose(fp);

  // save trace bitmap
  fp = fopen(trace_path, "w");
  if (!fp) {
    printf("Cannot open: %s\n", trace_path);
    abort();
  }
  count = 0;
  while (count < bitmapSize) {
    int res = fwrite(bitmapTrace + count, 1, bitmapSize - count, fp);
    if (res <= 0) break;
    count += res;
  }
  if (count < bitmapSize) {
    printf("Cannot write full bitmap: %s [%d]\n", trace_path, count);
    abort();
  }
  fclose(fp);
}

void _sym_finalize(void) {
  if (g_finalized.test_and_set())
    return;

  if (getenv("SYMFUSION_TRACER_SKIP_DUMP"))
    return;

  if (g_config.pathTracerMode) {
    printf("Saving bitmaps for hash %llx %llx...\n", XXH64_digest(pathMainHash), XXH64_digest(pathAllHash));
    compare_bitmaps(bitmapEdgesMain, g_config.bitmapTraceMainEdges, g_config.bitmapMainEdges);
    compare_bitmaps(bitmapEdgesAll, g_config.bitmapTraceAllEdges, g_config.bitmapAllEdges);
    uint64_t value = XXH64_digest(pathMainHash);
    saveBitmap((uint8_t*) &value, g_config.bitmapMainPath, sizeof(value));
    value = XXH64_digest(pathAllHash);
    saveBitmap((uint8_t*) &value, g_config.bitmapAllPath, sizeof(value));
  }
}

SymExpr _sym_build_integer(uint64_t value, uint8_t bits) {
  // Qsym's API takes uintptr_t, so we need to be careful when compiling for
  // 32-bit systems: the compiler would helpfully truncate our uint64_t to fit
  // into 32 bits.
  if constexpr (sizeof(uint64_t) == sizeof(uintptr_t)) {
    // 64-bit case: all good.
    return registerExpression(g_expr_builder->createConstant(value, bits));
  } else {
    // 32-bit case: use the regular API if possible, otherwise create an
    // llvm::APInt.
    if (uintptr_t value32 = value; value32 == value)
      return registerExpression(g_expr_builder->createConstant(value32, bits));

    return registerExpression(
        g_expr_builder->createConstant({64, value}, bits));
  }
}

SymExpr _sym_build_integer128(uint64_t high, uint64_t low) {
  std::array<uint64_t, 2> words = {low, high};
  return registerExpression(g_expr_builder->createConstant({128, words}, 128));
}

SymExpr _sym_build_null_pointer() {
  return registerExpression(
      g_expr_builder->createConstant(0, sizeof(uintptr_t) * 8));
}

SymExpr _sym_build_true() {
  return registerExpression(g_expr_builder->createTrue());
}

SymExpr _sym_build_false() {
  return registerExpression(g_expr_builder->createFalse());
}

SymExpr _sym_build_bool(bool value) {
  return registerExpression(g_expr_builder->createBool(value));
}

#define DEF_BINARY_EXPR_BUILDER(name, qsymName)                                \
  SymExpr _sym_build_##name(SymExpr a, SymExpr b) {                            \
    return registerExpression(g_expr_builder->create##qsymName(                \
        allocatedExpressions.at(a), allocatedExpressions.at(b)));              \
  }

#define DEF_BINARY_EXPR_BUILDER_SHIFT(name, qsymName)                          \
  SymExpr _sym_build_##name(SymExpr a, SymExpr b) {                            \
    size_t s = _sym_bits_helper(a);                                            \
    SymExpr mask = _sym_build_integer(s - 1, s);                               \
    b = registerExpression(g_expr_builder->createAnd(                          \
          allocatedExpressions.at(b), allocatedExpressions.at(mask)));         \
    return registerExpression(g_expr_builder->create##qsymName(                \
        allocatedExpressions.at(a), allocatedExpressions.at(b)));              \
  }

DEF_BINARY_EXPR_BUILDER(add, Add)
DEF_BINARY_EXPR_BUILDER(sub, Sub)
DEF_BINARY_EXPR_BUILDER(mul, Mul)
DEF_BINARY_EXPR_BUILDER(unsigned_div, UDiv)
DEF_BINARY_EXPR_BUILDER(signed_div, SDiv)
DEF_BINARY_EXPR_BUILDER(unsigned_rem, URem)
DEF_BINARY_EXPR_BUILDER(signed_rem, SRem)

DEF_BINARY_EXPR_BUILDER_SHIFT(shift_left, Shl)
DEF_BINARY_EXPR_BUILDER_SHIFT(logical_shift_right, LShr)
DEF_BINARY_EXPR_BUILDER_SHIFT(arithmetic_shift_right, AShr)

DEF_BINARY_EXPR_BUILDER(signed_less_than, Slt)
DEF_BINARY_EXPR_BUILDER(signed_less_equal, Sle)
DEF_BINARY_EXPR_BUILDER(signed_greater_than, Sgt)
DEF_BINARY_EXPR_BUILDER(signed_greater_equal, Sge)
DEF_BINARY_EXPR_BUILDER(unsigned_less_than, Ult)
DEF_BINARY_EXPR_BUILDER(unsigned_less_equal, Ule)
DEF_BINARY_EXPR_BUILDER(unsigned_greater_than, Ugt)
DEF_BINARY_EXPR_BUILDER(unsigned_greater_equal, Uge)
DEF_BINARY_EXPR_BUILDER(equal, Equal)
DEF_BINARY_EXPR_BUILDER(not_equal, Distinct)

DEF_BINARY_EXPR_BUILDER(bool_and, LAnd)
DEF_BINARY_EXPR_BUILDER(and, And)
DEF_BINARY_EXPR_BUILDER(bool_or, LOr)
DEF_BINARY_EXPR_BUILDER(or, Or)
DEF_BINARY_EXPR_BUILDER(bool_xor, Distinct)
// DEF_BINARY_EXPR_BUILDER(xor, Xor)

#undef DEF_BINARY_EXPR_BUILDER

SymExpr _sym_build_xor(SymExpr a, SymExpr b) {   
  if (a == b) return nullptr; // optimization                        
  return registerExpression(g_expr_builder->createXor(               
      allocatedExpressions.at(a), allocatedExpressions.at(b)));             
}

SymExpr _sym_build_neg(SymExpr expr) {
  return registerExpression(
      g_expr_builder->createNeg(allocatedExpressions.at(expr)));
}

SymExpr _sym_build_not(SymExpr expr) {
  return registerExpression(
      g_expr_builder->createNot(allocatedExpressions.at(expr)));
}

SymExpr _sym_build_sext(SymExpr expr, uint8_t bits) {
  return registerExpression(g_expr_builder->createSExt(
      allocatedExpressions.at(expr), bits + expr->bits()));
}

SymExpr _sym_build_zext(SymExpr expr, uint8_t bits) {
  return registerExpression(g_expr_builder->createZExt(
      allocatedExpressions.at(expr), bits + expr->bits()));
}

SymExpr _sym_build_trunc(SymExpr expr, uint8_t bits) {
  return registerExpression(
      g_expr_builder->createTrunc(allocatedExpressions.at(expr), bits));
}

void _sym_push_path_constraint(SymExpr constraint, int taken,
                               uintptr_t site_id) {
  if (constraint == nullptr)
    return;

  if (_sym_is_concrete_mode_enabled())
    return;
#if 0
  if (_sym_is_emulation_mode_enabled())
    return;
#endif
#if 0
  printf("QUERY AT addr=%lx taken=%d\n", site_id, taken);
  g_call_stack_manager.printStack();
#endif
  g_solver->addJcc(allocatedExpressions.at(constraint), taken != 0, site_id);
}

SymExpr _sym_get_input_byte(size_t offset) {
  return registerExpression(g_expr_builder->createRead(offset));
}

SymExpr _sym_concat_helper(SymExpr a, SymExpr b) {
  return registerExpression(g_expr_builder->createConcat(
      allocatedExpressions.at(a), allocatedExpressions.at(b)));
}

SymExpr _sym_extract_helper(SymExpr expr, size_t first_bit, size_t last_bit) {
  return registerExpression(g_expr_builder->createExtract(
      allocatedExpressions.at(expr), last_bit, first_bit - last_bit + 1));
}

size_t _sym_bits_helper(SymExpr expr) { return expr->bits(); }

SymExpr _sym_build_bool_to_bits(SymExpr expr, uint8_t bits) {
  return registerExpression(
      g_expr_builder->boolToBit(allocatedExpressions.at(expr), bits));
}

SymExpr _sym_build_bool_to_sign_bits(SymExpr expr, uint8_t bits) {
  if (expr == NULL) return NULL;
  expr = registerExpression(
    g_expr_builder->boolToBit(allocatedExpressions.at(expr), 1));
  return registerExpression(g_expr_builder->createSExt(
    allocatedExpressions.at(expr), bits));
}

//
// Floating-point operations (unsupported in Qsym)
//

#define UNSUPPORTED(prototype)                                                 \
  prototype { return nullptr; }

UNSUPPORTED(SymExpr _sym_build_float(double, int))
UNSUPPORTED(SymExpr _sym_build_fp_add(SymExpr, SymExpr))
UNSUPPORTED(SymExpr _sym_build_fp_sub(SymExpr, SymExpr))
UNSUPPORTED(SymExpr _sym_build_fp_mul(SymExpr, SymExpr))
UNSUPPORTED(SymExpr _sym_build_fp_div(SymExpr, SymExpr))
UNSUPPORTED(SymExpr _sym_build_fp_rem(SymExpr, SymExpr))
UNSUPPORTED(SymExpr _sym_build_fp_abs(SymExpr))
UNSUPPORTED(SymExpr _sym_build_float_ordered_greater_than(SymExpr, SymExpr))
UNSUPPORTED(SymExpr _sym_build_float_ordered_greater_equal(SymExpr, SymExpr))
UNSUPPORTED(SymExpr _sym_build_float_ordered_less_than(SymExpr, SymExpr))
UNSUPPORTED(SymExpr _sym_build_float_ordered_less_equal(SymExpr, SymExpr))
UNSUPPORTED(SymExpr _sym_build_float_ordered_equal(SymExpr, SymExpr))
UNSUPPORTED(SymExpr _sym_build_float_ordered_not_equal(SymExpr, SymExpr))
UNSUPPORTED(SymExpr _sym_build_float_ordered(SymExpr, SymExpr))
UNSUPPORTED(SymExpr _sym_build_float_unordered(SymExpr, SymExpr))
UNSUPPORTED(SymExpr _sym_build_float_unordered_greater_than(SymExpr, SymExpr))
UNSUPPORTED(SymExpr _sym_build_float_unordered_greater_equal(SymExpr, SymExpr))
UNSUPPORTED(SymExpr _sym_build_float_unordered_less_than(SymExpr, SymExpr))
UNSUPPORTED(SymExpr _sym_build_float_unordered_less_equal(SymExpr, SymExpr))
UNSUPPORTED(SymExpr _sym_build_float_unordered_equal(SymExpr, SymExpr))
UNSUPPORTED(SymExpr _sym_build_float_unordered_not_equal(SymExpr, SymExpr))
UNSUPPORTED(SymExpr _sym_build_int_to_float(SymExpr, int, int))
UNSUPPORTED(SymExpr _sym_build_float_to_float(SymExpr, int))
UNSUPPORTED(SymExpr _sym_build_bits_to_float(SymExpr, int))
UNSUPPORTED(SymExpr _sym_build_float_to_bits(SymExpr))
UNSUPPORTED(SymExpr _sym_build_float_to_signed_integer(SymExpr, uint8_t))
UNSUPPORTED(SymExpr _sym_build_float_to_unsigned_integer(SymExpr, uint8_t))

#undef UNSUPPORTED
#undef H

//
// Call-stack tracing
//

void _sym_notify_call(uintptr_t site_id) {
  // printf("CALL %lx\n", site_id);
#if 0
  // _sym_concretize_memory(((uint8_t*)&fake) - 0x4000, 0x4000);
  uint64_t a = 0x40007ff1bf;
  printf("*0x%lx = %lx is_concrete=%d\n", a, *((uint8_t*)a),
    isConcrete((uint8_t*)a, 1));
#endif
  g_call_stack_manager.visitCall(site_id);
}

void _sym_notify_ret(uintptr_t site_id) {
  // printf("RET %lx\n", site_id);
#if 0
  // _sym_concretize_memory(((uint8_t*)&fake) - 0x4000, 0x4000);
  uint64_t a = 0x40007ff1bf;
  printf("*0x%lx = %lx is_concrete=%d\n", a, *((uint8_t*)a),
    isConcrete((uint8_t*)a, 1));
#endif
  g_call_stack_manager.visitRet(site_id);
  // _sym_print_stack();
}

void _sym_notify_basic_block(uintptr_t site_id) {
  // printf("BB %lx\n", site_id);
#if 0
  _sym_concretize_memory(((uint8_t*)frame) - 0x4000, 0x4000);
  uint64_t a = 0x40007ff1bf;
  printf("*0x%lx = %lx is_concrete=%d\n", a, *((uint8_t*)a),
    isConcrete((uint8_t*)a, 1));
#endif
  if (g_config.pathTracerMode) {
    int outsideMain = _sym_is_emulation_mode_enabled();
    if (bitmapSize) {
      uint32_t edgeId;
      if (!outsideMain) {
        XXH64_reset(edgeState, 0x0);
        XXH64_update(edgeState, &lastBasicBlockMainId, sizeof(lastBasicBlockMainId));
        XXH64_update(edgeState, &site_id, sizeof(site_id));
#if 1
        uint64_t context_hash = g_call_stack_manager.getContextHash();
        XXH64_update(edgeState, &context_hash, sizeof(context_hash));
#endif
        edgeId = XXH64_digest(edgeState);
        bitmapEdgesMain[edgeId % bitmapSize] += 1;
      }

      if (outsideMain || lastBasicBlockAllId != lastBasicBlockMainId) {
        XXH64_reset(edgeState, 0x0);
        XXH64_update(edgeState, &lastBasicBlockAllId, sizeof(lastBasicBlockAllId));
        XXH64_update(edgeState, &site_id, sizeof(site_id));
#if 1
        uint64_t context_hash = g_call_stack_manager.getContextHash();
        XXH64_update(edgeState, &context_hash, sizeof(context_hash));
#endif
        edgeId = XXH64_digest(edgeState);
      }
      bitmapEdgesAll[edgeId % bitmapSize] += 1;
    }

    if (!outsideMain) {
      lastBasicBlockMainId = site_id;
      XXH64_update(pathMainHash, &site_id, sizeof(site_id)); 
    }

    lastBasicBlockAllId = site_id;       
    XXH64_update(pathAllHash, &site_id, sizeof(site_id));

    // printf("PathHash: %lx\n", (uint64_t) XXH64_digest(pathHash));
  }

  g_call_stack_manager.visitBasicBlock(site_id);
}

//
// Debugging
//

const char *_sym_expr_to_string(SymExpr expr) {
  static char buffer[4096];

  auto expr_string = expr->toString();
  auto copied = expr_string.copy(
      buffer, std::min(expr_string.length(), sizeof(buffer) - 1));
  buffer[copied] = '\0';

  return buffer;
}

feasibility_result_t _sym_feasible(SymExpr expr) {
  expr->simplify();

  g_solver->push();
  g_solver->add(expr->toZ3Expr());
  bool feasible = (g_solver->check() == z3::sat);
  g_solver->pop();

  return feasible ? feasibility_result_t::SAT : feasibility_result_t::UNSAT;
}

//
// Garbage collection
//

void _sym_collect_garbage() {
  if (allocatedExpressions.size() < g_config.garbageCollectionThreshold)
    return;

#ifdef DEBUG_RUNTIME
  auto start = std::chrono::high_resolution_clock::now();
#endif

  auto reachableExpressions = collectReachableExpressions();
  for (auto expr_it = allocatedExpressions.begin();
       expr_it != allocatedExpressions.end();) {
    if (reachableExpressions.count(expr_it->first) == 0) {
      expr_it = allocatedExpressions.erase(expr_it);
    } else {
      ++expr_it;
    }
  }

#ifdef DEBUG_RUNTIME
  auto end = std::chrono::high_resolution_clock::now();

  std::cerr << "After garbage collection: " << allocatedExpressions.size()
            << " expressions remain" << std::endl
            << "\t(collection took "
            << std::chrono::duration_cast<std::chrono::milliseconds>(end -
                                                                     start)
                   .count()
            << " milliseconds)" << std::endl;
#endif
}

SymExpr _sym_read_memory(SymExpr addrExpr, uint8_t *addr, size_t length, uint8_t flags) {
  bool little_endian = flags & 1;
  assert(length && "Invalid query for zero-length memory region");

  if (flags & 2) _sym_switch_fs_to_emulation();
#if 0
  static int count = 0;
  if (addr == (uint8_t *)0x40007ff940UL)
    printf("\n[%d] Reading %ld bytes at %p\n\n", count++, length, addr);
#endif
#ifdef DEBUG_RUNTIME
  std::cerr << "Reading " << length << " bytes from address " << P(addr)
            << std::endl;
  dump_known_regions();
#endif

  if (addrExpr) {
    _sym_push_path_constraint(
        _sym_build_equal(addrExpr,
                        _sym_build_integer((uint64_t)addr, sizeof(addr) * 8)),
        true, _sym_get_basic_block_id());
    addrExpr = NULL;
  }

  // If the entire memory region is concrete, don't create a symbolic expression
  // at all.
  if (isConcrete(addr, length)) {
    if (flags & 2) _sym_switch_fs_to_native();
    return nullptr;
  }

  ReadOnlyShadow shadow(addr, length);
  SymExpr res = std::accumulate(shadow.begin_non_null(), shadow.end_non_null(),
                         static_cast<SymExpr>(nullptr),
                         [&](SymExpr result, SymExpr byteExpr) {
                           if (result == nullptr)
                             return byteExpr;

                           return little_endian
                                      ? _sym_concat_helper(byteExpr, result)
                                      : _sym_concat_helper(result, byteExpr);
                         });


#if HYBRID_DBG_CONSISTENCY_CHECK
    // printf("Reading %ld bytes at %p\n", length, addr);
    if (length <= 16) {
        uint64_t expected_value;
        switch (length) {
            case 1:
                expected_value = *((uint8_t*)addr);
                break;
            case 2:
                expected_value = *((uint16_t*)addr);
                break;
            case 4:
                expected_value = *((uint32_t*)addr);
                break;
            case 8:
                expected_value = *((uint64_t*)addr);
                break;
            case 16:
                if (res) {
                  _sym_check_consistency(
                    _sym_build_extract(res, 8, 8, 1), 
                    *((uint64_t*)(addr + 8)), (uint64_t)addr);
                  _sym_check_consistency(
                    _sym_build_extract(res, 0, 8, 1), 
                    *((uint64_t*)(addr)), (uint64_t)addr);
                }
                break;
            default:
                printf("READ SIZE: %ld\n", length);
                assert(0 && "Unexpected read size");
        }
        if (length <= 8)
          _sym_check_consistency(res, expected_value, (uint64_t)addr);
    }
#endif

  if (flags & 2) _sym_switch_fs_to_native();
  return res;
}

void _sym_debug_handle(void) {
  printf("HERE\n");
  return;
}

void _sym_write_memory(SymExpr addrExpr, uint8_t *addr, size_t length, SymExpr expr,
                       uint8_t flags, uint64_t value) {
  bool little_endian = flags & 1;
  assert(length && "Invalid query for zero-length memory region");

  if (flags & 2) _sym_switch_fs_to_emulation();

#if 0
  static int count = 0;
  if (addr >= (uint8_t *)0x40007ff940UL && addr <= (uint8_t *)(0x40007ff940UL + 8)) {
    printf("\n[%d] Writing %ld bytes at %p expr=%p\n\n", count++, length, addr, expr);
  }
#endif

#if HYBRID_DBG_CONSISTENCY_CHECK
    // printf("Writing %ld bytes at %p\n", length, addr);
    if (length <= 8 && value != 0xDEADBEEFCAFECAFE) {
      _sym_check_consistency(expr, value, (uint64_t)addr);
    }
#endif

#ifdef DEBUG_RUNTIME
  std::cerr << "Writing " << length << " bytes to address " << P(addr)
            << std::endl;
  dump_known_regions();
#endif

  if (addrExpr) {
    _sym_push_path_constraint(
        _sym_build_equal(addrExpr,
                        _sym_build_integer((uint64_t)addr, sizeof(addr) * 8)),
        true, _sym_get_basic_block_id());
    addrExpr = NULL;
  }

  if (expr == nullptr && isConcrete(addr, length)) {
    if (flags & 2) _sym_switch_fs_to_native();
    return;
  }

  ReadWriteShadow shadow(addr, length);
  if (expr == nullptr) {
    for (auto shadowByte = shadow.begin(); shadowByte != shadow.end(); ++shadowByte)
      shadowByte.writeByte(nullptr);
  } else {
    size_t i = 0;
    for (auto shadowByte = shadow.begin(); 
            shadowByte != shadow.end();
            ++shadowByte) {
      SymExpr byteExpr = little_endian
                       ? _sym_extract_helper(expr, 8 * (i + 1) - 1, 8 * i)
                       : _sym_extract_helper(expr, (length - i) * 8 - 1,
                                             (length - i - 1) * 8);
      shadowByte.writeByte(byteExpr);
      i++;
    }
  }

  if (flags & 2) _sym_switch_fs_to_native();
}

uintptr_t _sym_get_basic_block_id() {
  return g_call_stack_manager.getLastVisitedBasicBlock();
}

void _sym_concretize_memory(uint8_t *addr, size_t length) {
  while (length) {
    uintptr_t start = pageStart((uintptr_t)addr);
    size_t offset = pageOffset((uintptr_t)addr);
    size_t n_left = kPageSize - offset;
    size_t n = length > n_left ? n_left : length;
    if(!isConcrete(addr, n)) {
      ReadWriteShadow shadow(addr, n);
      for (auto shadowByte = shadow.begin(); shadowByte != shadow.end(); ++shadowByte)
        shadowByte.writeByte(nullptr);
    }
    addr += n;
    length -= n;
  }
}

SymExpr _sym_build_ite(SymExpr cond, SymExpr a, SymExpr b) {
  return registerExpression(g_expr_builder->createIte(
    allocatedExpressions.at(cond),
    allocatedExpressions.at(a),
    allocatedExpressions.at(b)
  ));
}

void _sym_print_stack(void) {
  g_call_stack_manager.printStack();
}

void _sym_check_consistency(SymExpr expr, uint64_t expected_value, uint64_t addr) {
#if HYBRID_DBG_CONSISTENCY_CHECK
  if (expr == NULL) return;
  int res = g_solver->checkConsistency(allocatedExpressions.at(expr), expected_value);
  if (res == 0) {
    uint64_t bb_id = _sym_get_basic_block_id();
#if 0
    if (bb_id == 0x15a33a0) {
      return;
    }
#endif
    printf("CONSISTENCY CHECK FAILED AT %lx\n", addr);
    _sym_print_stack();
    printf("BB ID: %lx\n", bb_id);
    abort();
  }
#else
  return;
#endif
}

uintptr_t _sym_get_call_site() {
  return g_call_stack_manager.getCurrentCall();
}

typedef uint64_t (*switch_fs_t)(void);

extern "C" {
  switch_fs_t switch_fs_to_native_ptr;
  switch_fs_t switch_fs_to_emulation_ptr;
}

void _sym_switch_fs_to_native(void) {
  switch_fs_to_native_ptr();
}

void _sym_switch_fs_to_emulation(void) {
  switch_fs_to_emulation_ptr();
}

void _sym_add_exec_map(uint64_t start, uint64_t end, char* name) {
  g_call_stack_manager.addExecMap(start, end, name);
}