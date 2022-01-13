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

#include "../../symqemu-hybrid/accel/tcg/hybrid/hybrid_debug.h"

extern "C" {
uint8_t concrete_mode  = 0;
uint8_t emulation_mode = 1;
}

namespace
{

constexpr int kMaxFunctionArguments = 256;

/// Global storage for function parameters and the return value.
SymExpr                                    g_return_value;
std::array<SymExpr, kMaxFunctionArguments> g_function_arguments;
std::array<bool, kMaxFunctionArguments>    g_function_arguments_is_int;
uint8_t                                    g_function_arguments_count = 0;
// TODO make thread-local

uint8_t g_function_arguments_concrete_count = 0;
#define MAX_CONCRETE_ARGS 256
uint64_t g_function_concrete_arguments[MAX_CONCRETE_ARGS];
typedef uint64_t (*check_indirect_target_t)(uint64_t, uint64_t*, uint64_t);
check_indirect_target_t check_indirect_target;

} // namespace

void _sym_set_return_expression(SymExpr expr) { g_return_value = expr; }

SymExpr _sym_get_return_expression(void)
{
    auto* result = g_return_value;
    // TODO this is a safeguard that can eventually be removed
    g_return_value = nullptr;
    return result;
}

SymExpr _sym_get_return_expression_with_truncate(uint8_t size)
{
    SymExpr expr = _sym_get_return_expression();
    if (expr && size > 0) {
        size_t current_bits = _sym_bits_helper(expr);
        if (current_bits > size * 8) {
            expr = _sym_build_trunc(expr, size * 8);
        }
    }
    return expr;
}

void _sym_set_parameter_expression(uint8_t index, SymExpr expr)
{
    g_function_arguments[index] = expr;
}

void _sym_set_int_parameter_expression(uint8_t index, SymExpr expr,
                                       bool is_integer)
{
    g_function_arguments[index]        = expr;
    g_function_arguments_is_int[index] = is_integer;
}

bool _sym_is_int_parameter(uint8_t index)
{
    return g_function_arguments_is_int[index];
}

SymExpr _sym_get_parameter_expression(uint8_t index)
{
    return g_function_arguments[index];
}

SymExpr _sym_get_parameter_expression_with_truncate(uint8_t index, uint8_t size)
{
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

void _sym_memcpy(uint8_t* dest, const uint8_t* src, size_t length)
{
    if (isConcrete(src, length) && isConcrete(dest, length))
        return;

    ReadOnlyShadow  srcShadow(src, length);
    ReadWriteShadow destShadow(dest, length);

    auto shadowDstByte = destShadow.begin();
    for (auto shadowSrcByte = srcShadow.begin(); shadowSrcByte != srcShadow.end(); ++shadowSrcByte, ++shadowDstByte)
      shadowDstByte.writeByte(*shadowSrcByte);
}

void _sym_memset(uint8_t* memory, SymExpr value, size_t length)
{
    if ((value == nullptr) && isConcrete(memory, length))
        return;

    ReadWriteShadow shadow(memory, length);
    for (auto shadowByte = shadow.begin(); shadowByte != shadow.end(); ++shadowByte)
      shadowByte.writeByte(value);
}

void _sym_memmove(uint8_t* dest, const uint8_t* src, size_t length)
{
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

SymExpr _sym_read_memory(SymExpr addrExpr, uint8_t* addr, size_t length, bool little_endian)
{
    assert(length && "Invalid query for zero-length memory region");
#if 0
  uint64_t* a = (uint64_t*)0x40007fee40;
  if (*a == 0x40007fee50)
    printf("VALUE %lx AT %lx\n", 0x40007fee50, 0x40007fee40);
  assert(*a != 0x40007fee50);
#endif
#ifdef DEBUG_RUNTIME
    std::cerr << "Reading " << length << " bytes from address " << P(addr)
              << std::endl;
    dump_known_regions();
#endif

#if !HYBRID_SYMBOLIC_MEMORY
    if (addrExpr) {
        _sym_push_path_constraint(
            _sym_build_equal(addrExpr,
                            _sym_build_integer((uint64_t)addr, sizeof(addr) * 8)),
            true, _sym_get_basic_block_id());
        addrExpr = NULL;
    }
#endif
#if 0
    if (addrExpr)
        printf("SYMBOLIC READ: %s\n", ""); //_sym_expr_to_string(addrExpr));
#endif
    if (_sym_is_concrete_mode_enabled())
        return nullptr;

#if 0
    if (!_sym_interesting_context())
        return nullptr;
#endif

    // If the entire memory region is concrete, don't create a symbolic
    // expression at all.
    if (addrExpr == nullptr && isConcrete(addr, length))
        return nullptr;

    SymExpr res = nullptr;
    if (addrExpr) {
        SymbolicShadow shadow(addrExpr, addr, length);
        res = shadow.read();
    }

    if (res == nullptr) {

        ReadOnlyShadow shadow(addr, length);
        bool           concreteBytes = true;
        
        res = std::accumulate(
            shadow.begin_non_null(), shadow.end_non_null(),
            static_cast<SymExpr>(nullptr), [&](SymExpr result, SymExpr byteExpr) {
                if (!_sym_expr_is_constant(byteExpr))
                    concreteBytes = false;

                if (result == nullptr)
                    return byteExpr;

                return little_endian ? _sym_concat_helper(byteExpr, result)
                                                    : _sym_concat_helper(result, byteExpr);
            });

        if (concreteBytes)
            res = nullptr;
    }

#if 0
  if (res) { // && !_sym_interesting_context()
    const char *s_expr = _sym_expr_to_string(res);
    printf("MEMORY READ at %p: %s @ %lx\n", addr, s_expr, _sym_get_basic_block_id());
  }
#endif

#if HYBRID_DBG_CONSISTENCY_CHECK
    if (length <= 8) {
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
            default:
                printf("READ SIZE: %ld\n", length);
                assert(0 && "Unexpected read size");
        }
        _sym_check_consistency(res, expected_value, (uint64_t)addr);
    }
#endif

    return res;
}

void _sym_write_memory(SymExpr addrExpr, uint8_t* addr, size_t length, SymExpr expr,
                       bool little_endian, uint64_t value)
{
    assert(length && "Invalid query for zero-length memory region");
#if 0
  uint64_t* a = (uint64_t*)0x40007fead0;
  if (*a == 0x40007feae0)
    printf("VALUE %lx AT %lx\n", 0x40007feae0, 0x40007fead0);
  assert(*a != 0x40007feae0);
  if ((uint8_t *)0x40007fead0 >= addr && (uint8_t *)0x40007fead0 < addr + length)
    printf("WRITING AT %lx\n", 0x40007fead0);
#endif
#ifdef DEBUG_RUNTIME
    std::cerr << "Writing " << length << " bytes to address " << P(addr)
              << std::endl;
    dump_known_regions();
#endif

#if !HYBRID_SYMBOLIC_MEMORY
    if (addrExpr) {
        _sym_push_path_constraint(
            _sym_build_equal(addrExpr,
                            _sym_build_integer((uint64_t)addr, sizeof(addr) * 8)),
            true, _sym_get_basic_block_id());
        addrExpr = NULL;
    }
#endif

    if (addrExpr == nullptr && expr == nullptr && isConcrete(addr, length))
        return;

#if 0
  if (!_sym_interesting_context())
    expr = nullptr;
#endif

    if (expr != nullptr && _sym_expr_is_constant(expr))
        expr = nullptr;
#if 0
  if (expr) { // && !_sym_interesting_context()
    const char *s_expr = _sym_expr_to_string(expr);
    printf("MEMORY WRITE at %p: %s @ %lx\n", addr, s_expr, _sym_get_call_site());
  }
#endif

    bool writeWasDone = false;
    if (addrExpr) {
        printf("SYMBOLIC WRITE: %s\n", ""); // _sym_expr_to_string(addrExpr));
        SymbolicShadow shadow(addrExpr, addr, length);
        writeWasDone = shadow.write(expr, value);
    } 
    
    if (!writeWasDone) {

        ReadWriteShadow shadow(addr, length);
        if (expr == nullptr) {
            for (auto shadowByte = shadow.begin(); shadowByte != shadow.end(); ++shadowByte)
                shadowByte.markByteConcrete();
        } else {
#if 0
            const char *s_expr = _sym_expr_to_string(expr);
            printf("MEMORY WRITE at %p: %s\n", addr, s_expr);
#endif
            size_t i = 0;
            for (auto shadowByte = shadow.begin(); shadowByte != shadow.end();
                ++shadowByte) {
                SymExpr byteExpr =
                    little_endian
                        ? _sym_extract_helper(expr, 8 * (i + 1) - 1, 8 * i)
                        : _sym_extract_helper(expr, (length - i) * 8 - 1,
                                            (length - i - 1) * 8);
                shadowByte.writeByte(byteExpr);
                i++;
            }
        }
    }
}

SymExpr _sym_build_extract(SymExpr expr, uint64_t offset, uint64_t length,
                           bool little_endian)
{
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

SymExpr _sym_build_bswap(SymExpr expr)
{
    size_t bits = _sym_bits_helper(expr);
    assert((bits % 16 == 0) && "bswap is not applicable");
    return _sym_build_extract(expr, 0, bits / 8, true);
}

void _sym_register_expression_region(SymExpr* start, size_t length)
{
    registerExpressionRegion({start, length});
}

void _sym_print_path_constraints(void) { printf("HERE\n"); }

void _sym_debug_function_after_return(uint8_t* addr)
{
    printf("FREAD(%p)\n", addr);
    for (int i = 0; i < 0xda + 1; i++) {
        SymExpr v = _sym_read_memory(nullptr, addr + i, 1, 1);
        if (v) {
            const char* s_expr = _sym_expr_to_string(v);
            printf("memory value: %s\n", s_expr);
        } else {
            printf("memory value: NULL\n");
        }
    }
}

void _sym_libc_memset(uint8_t* s, int c, size_t n)
{
    memset_symbolized(s, c, n);
}

void _sym_libc_memcpy(void* dest, const void* src, size_t n)
{
    memcpy_symbolized(dest, src, n);
}

void _sym_libc_memmove(void* dest, const void* src, size_t n)
{
    memmove_symbolized(dest, src, n);
}

// extern uintptr_t _sym_get_call_site(void);
uint64_t _sym_wrap_indirect_call_int(uint64_t target)
{
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
            default:
                assert(0 && "Indirect call with more than 10 arguments.");
        }
        // printf("indirect call addr=%lx res=%lx\n", target, res);
        return res;
    } else {
        return check_indirect_target(target, g_function_concrete_arguments,
                                     g_function_arguments_concrete_count);
    }
}

void _sym_indirect_call_set_arg_int(uint8_t index, uint64_t value,
                                    __attribute__((unused)) int8_t size)
{
    g_function_concrete_arguments[index] = value;
}

uint64_t _sym_indirect_call_get_arg_int(uint8_t index)
{
    return g_function_concrete_arguments[index];
}

void _sym_indirect_call_set_arg_count(uint8_t count)
{
    g_function_arguments_concrete_count = count;
}

void _sym_wrap_indirect_call_set_trumpoline(uint64_t target)
{
    check_indirect_target = (check_indirect_target_t)target;
}

void _sym_check_indirect_call_target(uint64_t target)
{
    if (check_indirect_target != NULL)
        check_indirect_target(target, NULL, 0);
}

int _sym_is_concrete_mode_enabled(void) { return concrete_mode; }

int _sym_set_concrete_mode(int v)
{
    concrete_mode = v;
    return v;
}

int _sym_is_emulation_mode_enabled(void) { return emulation_mode; }

int _sym_set_emulation_mode(int v)
{
    emulation_mode = v;
    return v;
}

void _sym_va_list_start(uint64_t* ap)
{
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
                              expr, 1, 0xDEADBEEF /* FAKE VALUE */);
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

            _sym_write_memory(nullptr, (uint8_t*)&stack_args[int_index], current_bits / 8, expr, 1, 0xDEADBEEF /* FAKE VALUE */);
        } else {
            _sym_concretize_memory((uint8_t*)&stack_args[int_index], current_bits / 8);
        }
        
        int_index += 1;
    }

    for (unsigned int i = 0; i < sizeof(va_list) / 8; i++)
        _sym_concretize_memory((uint8_t*)&ap[i], 8);
}

void _sym_concretize_memory(uint8_t *addr, size_t length) {
    ReadWriteShadow shadow(addr, length);
    for (auto shadowByte = shadow.begin(); shadowByte != shadow.end(); ++shadowByte)
        shadowByte.markByteConcrete();
}