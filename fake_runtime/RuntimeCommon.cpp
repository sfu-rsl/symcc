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

uint8_t g_function_arguments_concrete_count = 0;
#define MAX_CONCRETE_ARGS 256
uint64_t g_function_concrete_arguments[MAX_CONCRETE_ARGS];

void _sym_set_return_expression(SymExpr expr) {}
SymExpr _sym_get_return_expression(void) { return NULL; }
SymExpr _sym_get_return_expression_with_truncate(uint8_t size) { return NULL; }
void _sym_set_parameter_expression(uint8_t index, SymExpr expr) {}
void _sym_set_int_parameter_expression(uint8_t index, SymExpr expr, bool is_integer) {}
bool _sym_is_int_parameter(uint8_t index) { return false; }
SymExpr _sym_get_parameter_expression(uint8_t index) { return NULL; }
SymExpr _sym_get_parameter_expression_with_truncate(uint8_t index, uint8_t size) { return NULL; }
uint8_t _sym_get_args_count(void) { return 0; }
void _sym_set_args_count(uint8_t n) {}
void _sym_memcpy(uint8_t *dest, const uint8_t *src, size_t length) {}
void _sym_memset(uint8_t *memory, SymExpr value, size_t length) {}
void _sym_memmove(uint8_t *dest, const uint8_t *src, size_t length) {}
SymExpr _sym_read_memory(uint8_t *addr, size_t length, bool little_endian) { return NULL; }
void _sym_write_memory(uint8_t *addr, size_t length, SymExpr expr,
                       bool little_endian) {}
SymExpr _sym_build_extract(SymExpr expr, uint64_t offset, uint64_t length,
                           bool little_endian) { return NULL; }
SymExpr _sym_build_bswap(SymExpr expr) { return NULL; }
void _sym_register_expression_region(SymExpr *start, size_t length) {}
void _sym_print_path_constraints(void) {}
void _sym_debug_function_after_return(uint8_t *addr) {}
void _sym_libc_memset(uint8_t *s, int c, size_t n) {}
void _sym_libc_memcpy(void *dest, const void *src, size_t n) {}
void _sym_libc_memmove(void *dest, const void *src, size_t n) {}
uint64_t _sym_wrap_indirect_call_int(uint64_t target) { 
  uint64_t res;
  switch (g_function_arguments_concrete_count) {
    case 0: {
        uint64_t (*f)(void) = (uint64_t(*)(void))target;
        res = f();
        break;
    }
    case 1: {
        uint64_t (*f)(uint64_t) = (uint64_t(*)(uint64_t))target;
        res = f(g_function_concrete_arguments[0]);
        break;
    }
    case 2: {
        uint64_t (*f)(uint64_t, uint64_t) =
            (uint64_t(*)(uint64_t, uint64_t))target;
        res = f(g_function_concrete_arguments[0], g_function_concrete_arguments[1]);
        break;
    }
    case 3: {
        uint64_t (*f)(uint64_t, uint64_t, uint64_t) =
            (uint64_t(*)(uint64_t, uint64_t, uint64_t))target;
        res = f(g_function_concrete_arguments[0], g_function_concrete_arguments[1], g_function_concrete_arguments[2]);
        break;
    }
    case 4: {
        uint64_t (*f)(uint64_t, uint64_t, uint64_t, uint64_t) =
            (uint64_t(*)(uint64_t, uint64_t, uint64_t, uint64_t))target;
        res = f(g_function_concrete_arguments[0], g_function_concrete_arguments[1], g_function_concrete_arguments[2], g_function_concrete_arguments[3]);
        break;
    }
    case 5: {
        uint64_t (*f)(uint64_t, uint64_t, uint64_t, uint64_t,
                      uint64_t) =
            (uint64_t(*)(uint64_t, uint64_t, uint64_t, uint64_t,
                          uint64_t))target;
        res = f(g_function_concrete_arguments[0], g_function_concrete_arguments[1], g_function_concrete_arguments[2], g_function_concrete_arguments[3], g_function_concrete_arguments[4]);
        break;
    }
    case 6: {
        uint64_t (*f)(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
                      uint64_t) =
            (uint64_t(*)(uint64_t, uint64_t, uint64_t, uint64_t,
                          uint64_t, uint64_t))target;
        res = f(g_function_concrete_arguments[0], g_function_concrete_arguments[1], g_function_concrete_arguments[2], g_function_concrete_arguments[3], g_function_concrete_arguments[4], g_function_concrete_arguments[5]);
        break;
    }
    default:
        assert(0 && "Indirect call with more than 6 arguments.");
  }
  return res;
}

void _sym_indirect_call_set_arg_int(uint8_t index, uint64_t value, __attribute__((unused)) int8_t size) {
  g_function_concrete_arguments[index] = value;
}

uint64_t _sym_indirect_call_get_arg_int(uint8_t index) {
  return g_function_concrete_arguments[index];
}

void _sym_indirect_call_set_arg_count(uint8_t count) {
  g_function_arguments_concrete_count = count;
}

void _sym_wrap_indirect_call_set_trumpoline(uint64_t target) {}
void _sym_check_indirect_call_target(uint64_t target) {}

void _sym_check_consistency(SymExpr expr, uint64_t expected_value, uint64_t addr) {}
void _sym_va_list_start(uint8_t* ap) {}
SymExpr _sym_build_bool_to_sign_bits(SymExpr expr, uint8_t bits) { return NULL; }
int _sym_interesting_context(void) { return 0; }
uintptr_t _sym_get_basic_block_id(void) { return 0; }

SymExpr _sym_build_ite(SymExpr cond, SymExpr a, SymExpr b) { return nullptr; }