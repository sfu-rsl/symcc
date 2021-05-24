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

#include "RuntimeCommon.h"
#include "Shadow.h"
#include "GarbageCollection.h"

#include "LibcWrappers.h"

namespace {

constexpr int kMaxFunctionArguments = 256;

/// Global storage for function parameters and the return value.
SymExpr g_return_value;
std::array<SymExpr, kMaxFunctionArguments> g_function_arguments;
std::array<bool, kMaxFunctionArguments>  g_function_arguments_is_int;
uint8_t g_function_arguments_count = 0;
// TODO make thread-local

} // namespace

void _sym_set_return_expression(SymExpr expr) { g_return_value = expr; }

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
  return expr;
}

void _sym_set_parameter_expression(uint8_t index, SymExpr expr) {
  g_function_arguments[index] = expr;
}

void _sym_set_int_parameter_expression(uint8_t index, SymExpr expr, bool is_integer) {
  g_function_arguments[index] = expr;
  g_function_arguments_is_int[index] = is_integer;
}

bool _sym_is_int_parameter(uint8_t index) {
  return g_function_arguments_is_int[index];
}

SymExpr _sym_get_parameter_expression(uint8_t index) {
  return g_function_arguments[index];
}

uint8_t _sym_get_args_count(void) {
  return g_function_arguments_count;
}

void _sym_set_args_count(uint8_t n) {
  g_function_arguments_count = n;
}

void _sym_memcpy(uint8_t *dest, const uint8_t *src, size_t length) {
  if (isConcrete(src, length) && isConcrete(dest, length))
    return;

  ReadOnlyShadow srcShadow(src, length);
  ReadWriteShadow destShadow(dest, length);
  std::copy(srcShadow.begin(), srcShadow.end(), destShadow.begin());
}

void _sym_memset(uint8_t *memory, SymExpr value, size_t length) {
  if ((value == nullptr) && isConcrete(memory, length))
    return;

  ReadWriteShadow shadow(memory, length);
  std::fill(shadow.begin(), shadow.end(), value);
}

void _sym_memmove(uint8_t *dest, const uint8_t *src, size_t length) {
  if (isConcrete(src, length) && isConcrete(dest, length))
    return;

  ReadOnlyShadow srcShadow(src, length);
  ReadWriteShadow destShadow(dest, length);
  if (dest > src)
    std::copy_backward(srcShadow.begin(), srcShadow.end(), destShadow.end());
  else
    std::copy(srcShadow.begin(), srcShadow.end(), destShadow.begin());
}

SymExpr _sym_read_memory(uint8_t *addr, size_t length, bool little_endian) {
  assert(length && "Invalid query for zero-length memory region");

#ifdef DEBUG_RUNTIME
  std::cerr << "Reading " << length << " bytes from address " << P(addr)
            << std::endl;
  dump_known_regions();
#endif

  // If the entire memory region is concrete, don't create a symbolic expression
  // at all.
  if (isConcrete(addr, length))
    return nullptr;

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
#if 0
  const char *s_expr = _sym_expr_to_string(res);
  printf("MEMORY READ at %p: %s\n", addr, s_expr);
#endif
  return res;
}

void _sym_write_memory(uint8_t *addr, size_t length, SymExpr expr,
                       bool little_endian) {
  assert(length && "Invalid query for zero-length memory region");

#ifdef DEBUG_RUNTIME
  std::cerr << "Writing " << length << " bytes to address " << P(addr)
            << std::endl;
  dump_known_regions();
#endif

  if (expr == nullptr && isConcrete(addr, length))
    return;

  ReadWriteShadow shadow(addr, length);
  if (expr == nullptr) {
    std::fill(shadow.begin(), shadow.end(), nullptr);
  } else {
#if 0
    const char *s_expr = _sym_expr_to_string(expr);
    printf("MEMORY WRITE at %p: %s\n", addr, s_expr);
#endif
    size_t i = 0;
    for (SymExpr &byteShadow : shadow) {
      byteShadow = little_endian
                       ? _sym_extract_helper(expr, 8 * (i + 1) - 1, 8 * i)
                       : _sym_extract_helper(expr, (length - i) * 8 - 1,
                                             (length - i - 1) * 8);
      i++;
    }
  }
}

SymExpr _sym_build_extract(SymExpr expr, uint64_t offset, uint64_t length,
                           bool little_endian) {
  size_t totalBits = _sym_bits_helper(expr);
  assert((totalBits % 8 == 0) && "Aggregate type contains partial bytes");

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

  return result;
}

SymExpr _sym_build_bswap(SymExpr expr) {
  size_t bits = _sym_bits_helper(expr);
  assert((bits % 16 == 0) && "bswap is not applicable");
  return _sym_build_extract(expr, 0, bits / 8, true);
}

void _sym_register_expression_region(SymExpr *start, size_t length) {
  registerExpressionRegion({start, length});
}

void _sym_print_path_constraints(void) {
  printf("HERE\n");
}

void _sym_debug_function_after_return(uint8_t *addr) {
  printf("FREAD(%p)\n", addr);
  for (int i = 0; i < 0xda + 1; i++) {
    SymExpr v = _sym_read_memory(addr + i, 1, 1);
    if (v) {
      const char *s_expr = _sym_expr_to_string(v);
      printf("memory value: %s\n", s_expr);
    } else {
      printf("memory value: NULL\n");
    }
  }
}

void _sym_libc_memset(uint8_t *s, int c, size_t n) {
  memset_symbolized(s, c, n);
} 

void _sym_libc_memcpy(void *dest, const void *src, size_t n) {
  memcpy_symbolized(dest, src, n);
} 

void _sym_libc_memmove(void *dest, const void *src, size_t n) {
  memmove_symbolized(dest, src, n);
} 