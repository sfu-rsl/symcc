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
#include <Shadow.h>

#include <third_party/xxhash/xxhash.h>

#include "../../../symqemu-hybrid/accel/tcg/hybrid/hybrid_debug.h"

namespace qsym {

ExprBuilder *g_expr_builder;
Solver *g_solver;
CallStackManager g_call_stack_manager;
z3::context *g_z3_context;

#if HYBRID_CACHE_CONSTANTS
ExprBuilder *CEB;
#endif

} // namespace qsym

namespace {

/// Indicate whether the runtime has been initialized.
std::atomic_flag g_initialized = ATOMIC_FLAG_INIT;

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

void _sym_initialize(void) {}

void _sym_initialize_qemu(void) {
  if (g_initialized.test_and_set())
    return;

  loadConfig();
  initLibcWrappers();
  std::cerr << "This is SymCC running with the QSYM backend" << std::endl;
  if (g_config.fullyConcrete) {
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
    std::istreambuf_iterator<char> in_begin(std::cin), in_end;
    std::vector<char> inputData(in_begin, in_end);
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

  g_z3_context = new z3::context{};
  g_solver =
      new Solver(inputFileName, g_config.outputDir, g_config.aflCoverageMap);
  g_expr_builder = g_config.pruning ? PruneExprBuilder::create()
                                    : SymbolicExprBuilder::create();
#if HYBRID_CACHE_CONSTANTS
  CEB = g_expr_builder;
#endif
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
DEF_BINARY_EXPR_BUILDER(xor, Xor)

#undef DEF_BINARY_EXPR_BUILDER

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

#if HYBRID_DBG_DUMP_QUERY
static int debug_mode = 0;
extern "C" {
int debug_count = 0;
unsigned int debug_hash = 0;
}
XXH32_state_t debug_state;
static unsigned int expected_hash;
static int expected_count;
static int expected_taken;
#endif

// static int counter = 0;
void _sym_push_path_constraint(SymExpr constraint, int taken,
                               uintptr_t site_id) {
  if (constraint == nullptr)
    return;

#if HYBRID_DBG_DUMP_QUERY
  if (debug_count == 0) {
    XXH32_reset(&debug_state, 0);
    char* e = getenv("SYM_DEBUG");
    if (e != NULL)
      debug_mode = 1;
    if (debug_mode) {
      e = getenv("SYM_DEBUG_HASH");
      assert(e);
      expected_hash = (int)strtoul(e, NULL, 16);
      e = getenv("SYM_DEBUG_COUNT");
      assert(e);
      expected_count = (int)strtoul(e, NULL, 10);
      e = getenv("SYM_DEBUG_TAKEN");
      assert(e);
      expected_taken = (int)strtoul(e, NULL, 10);
    }
  }
  XXH32_update(&debug_state, &site_id, sizeof(site_id));
  debug_count += 1;

  const char *s_expr = _sym_expr_to_string(constraint);
  printf("QUERY AT addr=%lx hash=%x counter=%d taken=%d: %s\n", site_id, debug_hash, debug_count, taken, s_expr);
  g_call_stack_manager.printStack();

  debug_hash = XXH32_digest(&debug_state);
  if (debug_mode) {
    if (debug_count == expected_count) {
      if (debug_hash == expected_hash) {
        if (taken == expected_taken) {
          printf("OK\n");
          exit(0);
        } else {
          printf("Divergence: different taken\n");
          exit(1);
        }
      } else {
        printf("Divergence: different path\n");
        exit(1);
      }
      exit(0);
    } 
    assert(debug_count < expected_count);
  }

  if (!debug_mode)
#elif HYBRID_DBG_PRINT || HYBRID_DBG_PRINT_QUERY_ADDR
  printf("QUERY AT addr=%lx taken=%d\n", site_id, taken);
#endif
  g_solver->addJcc(allocatedExpressions.at(constraint), taken != 0, site_id);

#if HYBRID_DBG_CONSISTENCY_CHECK
  _sym_check_consistency(constraint, taken, site_id);
#endif
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
#if 0
  uint64_t* a = (uint64_t*)0x40007fee40;
  if (*a == 0x40007fee50)
    printf("VALUE %lx AT %lx %lx\n", 0x40007fee50, 0x40007fee40, site_id);
  assert(*a != 0x40007fee50);
#endif
  g_call_stack_manager.visitCall(site_id);
}

void _sym_update_call(uintptr_t site_id) {
  assert(0);
  // g_call_stack_manager.updateVisitCall(site_id);
}

uintptr_t _sym_get_call_site(void) {
  return g_call_stack_manager.getCallSite();
}

void _sym_notify_ret(uintptr_t site_id) {
#if 0
  uint64_t* a = (uint64_t*)0x40007fee40;
  if (*a == 0x40007fee50)
    printf("VALUE %lx AT %lx\n", 0x40007fee50, 0x40007fee40);
  assert(*a != 0x40007fee50);
#endif
  g_call_stack_manager.visitRet(site_id);
}

static uintptr_t last_site_id = 0;
void _sym_notify_basic_block(uintptr_t site_id) {
#if 0
  uint64_t v = 0x55555561ab90;
  uint64_t* a = (uint64_t*)0x40007ffaf8;
  if (*a == v)
    printf("VALUE %lx AT %p %lx %lx\n", v, a, last_site_id, site_id);
  // assert(*a != 0x40007fee50);
#endif
  last_site_id = site_id;
#if HYBRID_DBG_PRINT_PC
  printf("BB: %lx\n", site_id);
#endif
  g_call_stack_manager.visitBasicBlock(site_id);
}

uintptr_t _sym_get_basic_block_id(){
  return last_site_id;
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

bool _sym_feasible(SymExpr expr) {
  expr->simplify();

  g_solver->push();
  g_solver->add(expr->toZ3Expr());
  bool feasible = (g_solver->check() == z3::sat);
  g_solver->pop();

  return feasible;
}

//
// Garbage collection
//

void _sym_collect_garbage() {
  if (allocatedExpressions.size() < g_config.garbageCollectionThreshold)
    return;

  printf("GARBAGE COLLECTOR\n");
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

#if HYBRID_DBG_CONSISTENCY_CHECK

#if HYBRID_DBG_CONSISTENCY_ALT
static int consistency_counter = 0;
static int consistency_debug_mode = -1;
static int consistency_check_counter = -1;
static uint64_t consistency_check_value = 0;
#endif

void _sym_check_consistency(SymExpr expr, uint64_t expected_value, uint64_t addr) {  
#if 0
  uint64_t* a = (uint64_t*)0x40007fead0;
  if (*a == 0x40007feae0)
    printf("VALUE %lx AT %lx\n", 0x40007feae0, 0x40007fead0);
  // assert(*a != 0x40007feae0);
#endif
  if (expr == NULL) return;
  int res = g_solver->checkConsistency(allocatedExpressions.at(expr), expected_value);
  if (res == 0) {
    printf("CONSISTENCY CHECK FAILED AT %lx\n", addr);
    assert(0);
  }
#if HYBRID_DBG_CONSISTENCY_ALT
  if (consistency_debug_mode == -1) {
    consistency_debug_mode = 0;
    char* s = getenv("SYM_CONSISTENCY_ALT");
    if (s) {
      s = getenv("SYM_CONSISTENCY_COUNTER");
      if (s == NULL) 
          consistency_debug_mode = 1;
      else { 
        consistency_debug_mode = 2;
        consistency_check_counter = (int)strtoul(s, NULL, 10);
        s = getenv("SYM_CONSISTENCY_VALUE");
        assert(s);
        consistency_check_value = (uint64_t)strtoul(s, NULL, 16);
      }
    }
  }
  if (consistency_debug_mode == 2) {
    if (consistency_check_counter == consistency_counter) {
      if (expected_value == consistency_check_value)
        printf("Value is %lx but should be different from %lx\n", expected_value, consistency_check_value);
      assert(expected_value != consistency_check_value && "Inconsistent value");
      printf("ALTERNATIVE VALUE CHECK: OK\n");
      exit(0);
    }
    consistency_counter++;
    assert(consistency_counter <= consistency_check_counter);
  } else if (consistency_debug_mode == 1) {
    printf("ALT QUERY: %s\n", _sym_expr_to_string(expr));
    g_solver->alternativeSolution(allocatedExpressions.at(expr), expected_value, consistency_counter++);
    if (consistency_counter > 5000)
      exit(0);
  }
#endif
}
#else
void _sym_check_consistency(SymExpr expr, uint64_t expected_value, uint64_t addr) {}
#endif

int _sym_interesting_context(void) {
  return g_call_stack_manager.isInteresting();
}

int _sym_expr_is_constant(SymExpr expr) {
  return expr->isConstant();
}

SymExpr _sym_build_ite(SymExpr cond, SymExpr a, SymExpr b) {
  return registerExpression(g_expr_builder->createIte(
      allocatedExpressions.at(cond),
      allocatedExpressions.at(a),
      allocatedExpressions.at(b)
  ));
}