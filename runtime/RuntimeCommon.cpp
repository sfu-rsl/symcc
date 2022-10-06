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

#include <Runtime.h>

#include <array>
#include <cassert>
#include <numeric>

#include "GarbageCollection.h"
#include "RuntimeCommon.h"
#include "Shadow.h"
#include "LibcWrappers.h"

// #include "../../symqemu-hybrid/accel/tcg/hybrid/hybrid_debug.h"

extern "C" {
  uint8_t concrete_mode  = 0;
  uint8_t emulation_mode = 1;
}

namespace {

constexpr int kMaxFunctionArguments = 256;

/// Global storage for function parameters and the return value.
SymExpr                                    g_return_value;
std::array<SymExpr, kMaxFunctionArguments> g_function_arguments;
std::array<bool, kMaxFunctionArguments>    g_function_arguments_is_int;
uint8_t                                    g_function_arguments_count = 0;

uint8_t g_function_arguments_concrete_count = 0;
#define MAX_CONCRETE_ARGS 256
uint64_t g_function_concrete_arguments[MAX_CONCRETE_ARGS];
// TODO make thread-local

typedef uint64_t (*check_indirect_target_t)(uint64_t, uint64_t*, uint64_t);
check_indirect_target_t check_indirect_target;

} // namespace

void _sym_set_return_expression(SymExpr expr) { 
  // printf("Set return expr: %p %s\n", expr, expr ?_sym_expr_to_string(expr) : "");
  g_return_value = expr; 
}

SymExpr _sym_get_return_expression(void) {
  auto *result = g_return_value;
  // TODO this is a safeguard that can eventually be removed
  g_return_value = nullptr;
  return result;
}

SymExpr _sym_get_return_expression_with_truncate(uint8_t size) {
  SymExpr expr = _sym_get_return_expression();
  if (expr && size > 0) {
    size_t current_bits = _sym_bits_helper(expr);
    if (current_bits > size * 8) {
      expr = _sym_build_trunc(expr, size * 8);
    }
  }
  // printf("Return expr: %p\n", expr);
  return expr;
}

void _sym_set_parameter_expression(uint8_t index, SymExpr expr) {
  g_function_arguments[index] = expr;
}

void _sym_set_int_parameter_expression(uint8_t index, SymExpr expr,
                                       bool is_integer) {
  g_function_arguments[index]        = expr;
  g_function_arguments_is_int[index] = is_integer;
}

bool _sym_is_int_parameter(uint8_t index)
{
  return g_function_arguments_is_int[index];
}

SymExpr _sym_get_parameter_expression(uint8_t index) {
  return g_function_arguments[index];
}

SymExpr _sym_get_parameter_expression_with_truncate(uint8_t index, uint8_t size) {
  SymExpr expr = g_function_arguments[index];
  if (expr != NULL && size != 0) {
    size_t current_bits = _sym_bits_helper(expr);
    if (current_bits > size * 8) {
      expr = _sym_build_trunc(expr, size * 8);
    }
  }
  return expr;
}

uint8_t _sym_get_args_count(void) { return g_function_arguments_count; }

void _sym_set_args_count(uint8_t n) { g_function_arguments_count = n; }

void _sym_memcpy(uint8_t *dest, const uint8_t *src, size_t length) {
  
  // printf("\nmemcpy at %lx to %p from %p of %ld bytes\n\n", _sym_get_call_site(), dest, src, length);

  if (isConcrete(src, length) && isConcrete(dest, length))
    return;

  // printf("symbolic memcpy at %p from %p of %d bytes\n", dest, src, length);

  ReadOnlyShadow  srcShadow(src, length);
  ReadWriteShadow destShadow(dest, length);

  int i = 0;
  auto shadowDstByte = destShadow.begin();
  for (auto shadowSrcByte = srcShadow.begin(); shadowSrcByte != srcShadow.end(); ++shadowSrcByte, ++shadowDstByte) {
#if 1
    if (*shadowSrcByte)
      _sym_check_consistency(*shadowSrcByte, *(src + i), (uint64_t)src + i);
    i++;
#endif
    shadowDstByte.writeByte(*shadowSrcByte);
  }
}

void _sym_memset(uint8_t *memory, SymExpr value, size_t length) {
  if ((value == nullptr) && isConcrete(memory, length))
    return;

  if (value == nullptr) _sym_concretize_memory(memory, length);
  else {
    ReadWriteShadow shadow(memory, length);
    for (auto shadowByte = shadow.begin(); shadowByte != shadow.end(); ++shadowByte) {
      shadowByte.writeByte(value);
    }
  }
}

void _sym_memmove(uint8_t *dest, const uint8_t *src, size_t length) {
  if (isConcrete(src, length) && isConcrete(dest, length))
    return;

  ReadOnlyShadow  srcShadow(src, length);
  ReadWriteShadow destShadow(dest, length);

  if (dest > src) {
    auto shadowDstByte = destShadow.end();
    auto shadowSrcByte = srcShadow.end();
    do {
        --shadowSrcByte; 
        --shadowDstByte;
        shadowDstByte.writeByte(*shadowSrcByte);
    } while(shadowSrcByte != srcShadow.begin());
  } else {
    auto shadowDstByte = destShadow.begin();
    for (auto shadowSrcByte = srcShadow.begin(); shadowSrcByte != srcShadow.end(); ++shadowSrcByte, ++shadowDstByte)
        shadowDstByte.writeByte(*shadowSrcByte);
  }
}

SymExpr _sym_build_extract(SymExpr expr, uint64_t offset, uint64_t length,
                           bool little_endian) {
  if (expr == nullptr) return nullptr;
  size_t totalBits = _sym_bits_helper(expr);
  assert((totalBits % 8 == 0) && "Aggregate type contains partial bytes");

  // printf("EXTRACT EXPR: %s offset=%ld len=%ld size=%ld\n", _sym_expr_to_string(expr), offset, length, totalBits);

  SymExpr result;
  if (little_endian) {
    result = _sym_extract_helper(expr, totalBits - offset * 8 - 1,
                                 totalBits - offset * 8 - 8);
    for (size_t i = 1; i < length; i++) {
      result = _sym_concat_helper(
          _sym_extract_helper(expr, totalBits - (offset + i) * 8 - 1,
                              totalBits - (offset + i + 1) * 8),
          result);
    }
  } else {
    result = _sym_extract_helper(expr, totalBits - offset * 8 - 1,
                                 totalBits - (offset + length) * 8);
  }

  // printf("_sym_build_extract: %s\n", result ? _sym_expr_to_string(result) : "null");
  return result;
}

SymExpr _sym_build_bswap(SymExpr expr) {
  size_t bits = _sym_bits_helper(expr);
  assert((bits % 16 == 0) && "bswap is not applicable");
  return _sym_build_extract(expr, 0, bits / 8, true);
}

SymExpr _sym_build_insert(SymExpr target, SymExpr to_insert, uint64_t offset,
                          bool little_endian) {
  // TODO: handle one of the two is null
  if (target == nullptr || to_insert == nullptr)
    return nullptr;

  // printf("INSERT TARGET: %s offset=%ld len=%ld\n",_sym_expr_to_string(target), offset, _sym_bits_helper(target));
  // printf("INSERT TO_INSERT: %s len=%ld\n",_sym_expr_to_string(to_insert), _sym_bits_helper(to_insert));

  size_t bitsToInsert = _sym_bits_helper(to_insert);
  assert((bitsToInsert % 8 == 0) &&
         "Expression to insert contains partial bytes");

  SymExpr beforeInsert =
      (offset == 0) ? nullptr : _sym_build_extract(target, 0, offset, false);
  SymExpr newPiece = little_endian ? _sym_build_bswap(to_insert) : to_insert;
  uint64_t afterLen =
      (_sym_bits_helper(target) / 8) - offset - (bitsToInsert / 8);
  SymExpr afterInsert =
      (afterLen == 0) ? nullptr
                      : _sym_build_extract(target, offset + (bitsToInsert / 8),
                                           afterLen, false);

  SymExpr result = beforeInsert;
  if (result == nullptr) {
    result = newPiece;
  } else {
    result = _sym_concat_helper(result, newPiece);
  }

  if (afterInsert != nullptr) {
    result = _sym_concat_helper(result, afterInsert);
  }

  // printf("_sym_build_insert: %s\n", result ? _sym_expr_to_string(result) : "null");
  return result;
}

void _sym_libc_memset(uint8_t* s, int c, size_t n)
{
  memset_symbolized(s, c, n);
}

void _sym_libc_memcpy(void* dest, const void* src, size_t n) {
  memcpy_symbolized(dest, src, n);
}

void _sym_libc_memmove(void* dest, const void* src, size_t n) {
  memmove_symbolized(dest, src, n);
}

uint64_t _sym_wrap_indirect_call_int(uint64_t target) {
#if HYBRID_DBG_PRINT
  printf("call target: %lx count=%d callsite=%lx\n", target,
          g_function_arguments_concrete_count, _sym_get_call_site());
#endif
  uint64_t res;
  if (check_indirect_target == NULL) {
    switch (g_function_arguments_concrete_count) {
      case 0: {
        uint64_t (*f)(void) = (uint64_t(*)(void))target;
        res                 = f();
        break;
      }
      case 1: {
        uint64_t (*f)(uint64_t) = (uint64_t(*)(uint64_t))target;
        res                     = f(g_function_concrete_arguments[0]);
        break;
      }
      case 2: {
        uint64_t (*f)(uint64_t, uint64_t) =
            (uint64_t(*)(uint64_t, uint64_t))target;
        res = f(g_function_concrete_arguments[0],
                g_function_concrete_arguments[1]);
        break;
      }
      case 3: {
        uint64_t (*f)(uint64_t, uint64_t, uint64_t) =
            (uint64_t(*)(uint64_t, uint64_t, uint64_t))target;
        res = f(g_function_concrete_arguments[0],
                g_function_concrete_arguments[1],
                g_function_concrete_arguments[2]);
        break;
      }
      case 4: {
        uint64_t (*f)(uint64_t, uint64_t, uint64_t, uint64_t) =
            (uint64_t(*)(uint64_t, uint64_t, uint64_t, uint64_t))target;
        res = f(g_function_concrete_arguments[0],
                g_function_concrete_arguments[1],
                g_function_concrete_arguments[2],
                g_function_concrete_arguments[3]);
        break;
      }
      case 5: {
        uint64_t (*f)(uint64_t, uint64_t, uint64_t, uint64_t,
                      uint64_t) =
            (uint64_t(*)(uint64_t, uint64_t, uint64_t, uint64_t,
                          uint64_t))target;
        res = f(g_function_concrete_arguments[0],
                g_function_concrete_arguments[1],
                g_function_concrete_arguments[2],
                g_function_concrete_arguments[3],
                g_function_concrete_arguments[4]);
        break;
      }
      case 6: {
        uint64_t (*f)(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
                      uint64_t) =
            (uint64_t(*)(uint64_t, uint64_t, uint64_t, uint64_t,
                          uint64_t, uint64_t))target;
        res = f(g_function_concrete_arguments[0],
                g_function_concrete_arguments[1],
                g_function_concrete_arguments[2],
                g_function_concrete_arguments[3],
                g_function_concrete_arguments[4],
                g_function_concrete_arguments[5]);
        break;
      }
      case 7: {
        uint64_t (*f)(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
                      uint64_t, uint64_t) =
            (uint64_t(*)(uint64_t, uint64_t, uint64_t, uint64_t,
                          uint64_t, uint64_t, uint64_t))target;
        res = f(g_function_concrete_arguments[0],
                g_function_concrete_arguments[1],
                g_function_concrete_arguments[2],
                g_function_concrete_arguments[3],
                g_function_concrete_arguments[4],
                g_function_concrete_arguments[5],
                g_function_concrete_arguments[6]);
        break;
      }
      case 8: {
        uint64_t (*f)(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
                      uint64_t, uint64_t, uint64_t) =
            (uint64_t(*)(uint64_t, uint64_t, uint64_t, uint64_t,
                          uint64_t, uint64_t, uint64_t, uint64_t))target;
        res = f(g_function_concrete_arguments[0],
                g_function_concrete_arguments[1],
                g_function_concrete_arguments[2],
                g_function_concrete_arguments[3],
                g_function_concrete_arguments[4],
                g_function_concrete_arguments[5],
                g_function_concrete_arguments[6],
                g_function_concrete_arguments[7]);
        break;
      }
      case 9: {
        uint64_t (*f)(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
                      uint64_t, uint64_t, uint64_t, uint64_t) =
            (uint64_t(*)(uint64_t, uint64_t, uint64_t, uint64_t,
                          uint64_t, uint64_t, uint64_t, uint64_t,
                          uint64_t))target;
        res = f(g_function_concrete_arguments[0],
                g_function_concrete_arguments[1],
                g_function_concrete_arguments[2],
                g_function_concrete_arguments[3],
                g_function_concrete_arguments[4],
                g_function_concrete_arguments[5],
                g_function_concrete_arguments[6],
                g_function_concrete_arguments[7],
                g_function_concrete_arguments[8]);
        break;
      }
      case 10: {
        uint64_t (*f)(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
                      uint64_t, uint64_t, uint64_t, uint64_t,
                      uint64_t) =
            (uint64_t(*)(uint64_t, uint64_t, uint64_t, uint64_t,
                          uint64_t, uint64_t, uint64_t, uint64_t,
                          uint64_t, uint64_t))target;
        res = f(g_function_concrete_arguments[0],
                g_function_concrete_arguments[1],
                g_function_concrete_arguments[2],
                g_function_concrete_arguments[3],
                g_function_concrete_arguments[4],
                g_function_concrete_arguments[5],
                g_function_concrete_arguments[6],
                g_function_concrete_arguments[7],
                g_function_concrete_arguments[8],
                g_function_concrete_arguments[9]);
        break;
      }
      default: {
        printf("Indirect call with more than 10 arguments.");
        abort();
      }
    }
    // printf("indirect call addr=%lx res=%lx\n", target, res);
    return res;
  } else {
    return check_indirect_target(target, g_function_concrete_arguments,
                                  g_function_arguments_concrete_count);
  }
}

void _sym_indirect_call_set_arg_int(uint8_t index, uint64_t value,
                                    __attribute__((unused)) int8_t size){
  g_function_concrete_arguments[index] = value;
}

uint64_t _sym_indirect_call_get_arg_int(uint8_t index) {
  return g_function_concrete_arguments[index];
}

void _sym_indirect_call_set_arg_count(uint8_t count) {
  g_function_arguments_concrete_count = count;
}

void _sym_wrap_indirect_call_set_trumpoline(uint64_t target) {
  check_indirect_target = (check_indirect_target_t)target;
}

void _sym_check_indirect_call_target(uint64_t target) {
  if (check_indirect_target != NULL)
    check_indirect_target(target, NULL, 0);
}

int _sym_is_concrete_mode_enabled(void) { return concrete_mode; }

int _sym_set_concrete_mode(int v) {
  concrete_mode = v;
  return v;
}

int _sym_is_emulation_mode_enabled(void) { return emulation_mode; }

int _sym_set_emulation_mode(int v) {
  emulation_mode = v;
  return v;
}

void _sym_va_list_start(uint64_t* ap) {
  // printf("VA LIST PTR: %p\n", ap);
#if 0
  for (int i = 0; i < 128; i++)
    printf("VA LIST[%d] at %p = %lx\n", -i, &ap[-i], ap[-i]);
  printf("\n");
  for (int i = 0; i < 128; i++)
    printf("VA LIST[%d] at %p = %lx\n", i, &ap[i], ap[i]);
#endif
  int offset_start = ((uint32_t*)ap)[0] / sizeof(void*);
  int count        = _sym_get_args_count();
  // printf("ARGS COUNT: %d\n", count);
  // printf("START OFFSET: %d\n", offset_start);
  uint64_t* args = (uint64_t*)ap[2];
  // printf("ARGS ADDR: %p\n", args);
  int int_index = 0;
  int i         = 0;
  for (; int_index < 6 && i < count; i++) {
    int is_int = _sym_is_int_parameter(i);
    // printf("ARG[%d] is int: %d\n", i, is_int);
    if (!is_int)
      continue;
    if (int_index < offset_start || i >= count) {
      _sym_concretize_memory((uint8_t*)&args[int_index], 8);
    } else {
      // printf("ARG[%d]: value %lx\n", i, args[int_index]);
      SymExpr expr = _sym_get_parameter_expression(i);
      // printf("ARG[%d]: value %lx expr %p\n", i, args[int_index], expr);
      size_t current_bits = 64;
      if (expr) {
        // printf("EXPR[%d]: %s\n", i, _sym_expr_to_string(expr));
        current_bits = _sym_bits_helper(expr);
#if 0
        if (current_bits < 64) {
          expr = _sym_build_zext(expr, 64 - current_bits);
        }
#endif
        _sym_write_memory(nullptr, (uint8_t*)&args[int_index], current_bits / 8,
                      expr, 1, 0xDEADBEEFCAFECAFE /* FAKE VALUE */);
      } else {
        _sym_concretize_memory((uint8_t*)&args[int_index], current_bits / 8);
      }
    }
    int_index += 1;
    // printf("ARG: %lx\n", args[i]);
  }

  int_index            = 0;
  uint64_t* stack_args = (uint64_t*)ap[1];
  for (int k = 0; i < count; i++, k++) {
    int is_int = _sym_is_int_parameter(i);
    // printf("ARG[%d] is int: %d\n", i, is_int);
    if (!is_int)
      continue;

    SymExpr expr         = _sym_get_parameter_expression(i);
    size_t  current_bits = 64;
    if (expr) {
      current_bits = _sym_bits_helper(expr);
      // printf("EXPR[%d]: %s\n", i, _sym_expr_to_string(expr));

      _sym_write_memory(nullptr, (uint8_t*)&stack_args[int_index], current_bits / 8, expr, 1, 0xDEADBEEFCAFECAFE /* FAKE VALUE */);
    } else {
      _sym_concretize_memory((uint8_t*)&stack_args[int_index], current_bits / 8);
    }
    
    int_index += 1;
  }

  for (unsigned int i = 0; i < sizeof(va_list) / 8; i++)
    _sym_concretize_memory((uint8_t*)&ap[i], 8);
}

void _sym_register_expression_region(SymExpr *start, size_t length) {
  registerExpressionRegion({start, length});
}

SymExpr _sym_build_value_from_memory(uint8_t *addr, size_t length) {
  // this should be used by SymCC when reading an undef struct from
  // memory. We can ignore endianness since extractValue should
  // take care of it for each single field during extraction.
  if (!isConcrete(addr, length)) {
    printf("_sym_build_value_from_memory is building a constant value from symbolic memory. Is this correct?\n");
    abort();
  }
  SymExpr result = nullptr;
  for (int i = 0; i < length; i++) {
    uint8_t v = *(addr + i);
    SymExpr e = _sym_build_integer(v, 8);
    result = result == nullptr ? e : _sym_concat_helper(result, e);
  }
  return result;
}