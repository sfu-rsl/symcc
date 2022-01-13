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

#ifndef SHADOW_H
#define SHADOW_H

#include <algorithm>
#include <cassert>
#include <cstring>
#include <iterator>
#include <map>

#include <Runtime.h>

#include <z3.h>

#include "../../symqemu-hybrid/accel/tcg/hybrid/hybrid_debug.h"

extern "C" {
extern uintptr_t page_start_check;
extern uintptr_t page_end_check;
extern uintptr_t page_address_check;
}

//
// This file is dedicated to the management of shadow memory.
//
// We manage shadows at page granularity. Since the shadow for each page is
// malloc'ed and thus at an unpredictable location in memory, we need special
// handling for memory allocations that cross page boundaries. This header
// provides iterators over shadow memory that automatically handle jumps between
// memory pages (and thus shadow regions). They should work with the C++
// standard library.
//
// We represent shadowed memory as a sequence of 8-bit expressions. The
// iterators therefore expose the shadow in the form of byte expressions.
//

constexpr uintptr_t kPageSize = HYBRID_SYMBOLIC_MEMORY_PAGE_SIZE;

#include "PageState.h"

/// Compute the corresponding page address.
constexpr uintptr_t pageStart(uintptr_t addr)
{
    return (addr & ~(kPageSize - 1));
}

/// Compute the corresponding offset into the page.
constexpr uintptr_t pageOffset(uintptr_t addr)
{
    return (addr & (kPageSize - 1));
}

/// A mapping from page addresses to the corresponding shadow regions. Each
/// shadow is large enough to hold one expression per byte on the shadowed page.
extern std::map<uintptr_t, PageState*> g_shadow_pages;

/// An iterator that walks over the shadow bytes corresponding to a memory
/// region. If there is no shadow for any given memory address, it just returns
/// null.
class ReadShadowIterator
    : public std::iterator<std::bidirectional_iterator_tag, SymExpr>
{
  public:
    explicit ReadShadowIterator(uintptr_t address)
        : std::iterator<std::bidirectional_iterator_tag, SymExpr>()
    {
        uintptr_t expected_base = pageStart(address);
        state_ = getPageState(expected_base);
        if (state_ == nullptr) {
            base_ = expected_base;
            offset_ = pageOffset(address);
        } else {
            base_ = reinterpret_cast<uintptr_t>(state_->baseAddress);
            offset_ = address - base_;
        }
    }

    ReadShadowIterator& operator++()
    {
        offset_++;
        if (state_ && offset_ < state_->size)
            return *this;
        if (state_ == nullptr && offset_ < kPageSize)
            return *this;
        
        assert(pageOffset(base_ + offset_) == 0);
        auto newBase = pageStart(base_ + offset_);
        assert(newBase != base_);
        state_  = getPageState(newBase);
        if (state_)
            assert(reinterpret_cast<uintptr_t>(state_->baseAddress) == newBase);
        base_   = newBase;
        offset_ = 0;

        return *this;
    }

    ReadShadowIterator& operator--()
    {
        offset_--;
        if (state_ && offset_ < state_->size)
            return *this;
        if (state_ == nullptr && offset_ < kPageSize)
            return *this;

        auto newBase = pageStart(base_ + offset_);
        assert(newBase != base_);
        state_  = getPageState(newBase);
        if (state_) {
            offset_ = base_ + offset_ - reinterpret_cast<uintptr_t>(state_->baseAddress);
            base_   = reinterpret_cast<uintptr_t>(state_->baseAddress);
        } else {
            offset_ = base_ + offset_ - newBase;
            base_   = newBase;
        }

        return *this;
    }

    SymExpr operator*()
    {
        if (state_ == nullptr)
            return nullptr;

        // printf("READ DATA at %p:%lx:%x\n", state_, base_, offset_);

        SymExpr e = state_->read8(offset_);
        assert((e == nullptr || _sym_bits_helper(e) == 8)
                && "Shadow memory always represents bytes");
        return e;
    }

    bool operator==(const ReadShadowIterator& other) const
    {
        return (base_ == other.base_ && offset_ == other.offset_);
    }

    bool operator!=(const ReadShadowIterator& other) const
    {
        return !(*this == other);
    }

    bool isConcrete() const
    {
        if (state_ == nullptr)
            return true;
        
        bool res = state_->isByteConcrete(offset_);
        return res;
    }

  protected:
    static PageState* getPageState(uintptr_t baseAddress)
    {
        if (auto shadowPageIt = g_shadow_pages.find(baseAddress);
            shadowPageIt != g_shadow_pages.end())
            return shadowPageIt->second;

        return nullptr;
    }

    uintptr_t  base_;
    uintptr_t   offset_;
    PageState* state_;
};

/// Like ReadShadowIterator, but return an expression for the concrete memory
/// value if a region does not have a shadow.
class NonNullReadShadowIterator : public ReadShadowIterator
{
  public:
    explicit NonNullReadShadowIterator(uintptr_t address)
        : ReadShadowIterator(address)
    {
    }

    SymExpr operator*()
    {
        if (auto* symbolicResult = ReadShadowIterator::operator*())
            return symbolicResult;

        return _sym_build_integer(
            *reinterpret_cast<const uint8_t*>(base_ + offset_), 8);
    }
};

/// An iterator that walks over the shadow corresponding to a memory region and
/// exposes it for modification. If there is no shadow yet, it creates a new
/// one.
class WriteShadowIterator : public ReadShadowIterator
{
  public:
    WriteShadowIterator(uintptr_t address) : ReadShadowIterator(address)
    {
    }

    void writeByte(SymExpr value)
    {
        assert(value == nullptr || _sym_bits_helper(value) == 8);
        if (value == nullptr && state_ == nullptr)
            return;
        if (state_ == nullptr)
            state_ = getOrCreatePageState(base_);
        // printf("WRITE DATA at %p:%lx:%lu\n", state_, base_, offset_);
        state_->write(offset_, value, 0xDEADBEEF /* FAKE VALUE */, 8);
    }

    void markByteConcrete()
    {
        if (state_ != nullptr) {
            state_->markByteConcrete(offset_);
            state_->markByteUnflushed(offset_);
            state_->setKnownSymbolic(offset_, 0);
        }
    }

  protected:
    static PageState* getOrCreatePageState(uintptr_t baseAddress)
    {
        // printf("Getting PageState\n");
        if (auto* state = getPageState(baseAddress))
            return state;

        auto* state = new PageState((uint8_t*)baseAddress, kPageSize);
        g_shadow_pages[baseAddress] = state;
        return state;
    }

   friend class SymbolicShadow;
};

/// A view on shadow memory that exposes read-only functionality.
struct ReadOnlyShadow {
    template <typename T>
    ReadOnlyShadow(T* addr, size_t len)
        : address_(reinterpret_cast<uintptr_t>(addr)), length_(len)
    {
    }

    ReadShadowIterator begin() const { return ReadShadowIterator(address_); }
    ReadShadowIterator end() const
    {
        return ReadShadowIterator(address_ + length_);
    }

    NonNullReadShadowIterator begin_non_null() const
    {
        return NonNullReadShadowIterator(address_);
    }

    NonNullReadShadowIterator end_non_null() const
    {
        return NonNullReadShadowIterator(address_ + length_);
    }

    uintptr_t address_;
    size_t    length_;
};

/// A view on shadow memory that allows modifications.
template <typename T> struct ReadWriteShadow {
    ReadWriteShadow(T* addr, size_t len)
        : address_(reinterpret_cast<uintptr_t>(addr)), length_(len)
    {
    }

    WriteShadowIterator begin() { return WriteShadowIterator(address_); }
    WriteShadowIterator end()
    {
        return WriteShadowIterator(address_ + length_);
    }

    uintptr_t address_;
    size_t    length_;
};

/// Check whether the indicated memory range is concrete, i.e., there is no
/// symbolic byte in the entire region.
template <typename T> bool isConcrete(T* addr, size_t nbytes)
{
    // Fast path for allocations within one page.
    auto byteBuf = reinterpret_cast<uintptr_t>(addr);
    if (pageStart(byteBuf) == pageStart(byteBuf + nbytes) &&
        !g_shadow_pages.count(pageStart(byteBuf)))
        return true;

    ReadOnlyShadow shadow(addr, nbytes);
    for (auto shadowByte = shadow.begin(); shadowByte != shadow.end(); ++shadowByte) {
        if (!shadowByte.isConcrete()) return false;
    }

    return true;
}


/// A view on shadow memory that exposes read-only functionality.
struct SymbolicShadow {
    template <typename T>
    SymbolicShadow(SymExpr addr_expr, T* addr, size_t len)
        : addr_expr_(addr_expr), address_(reinterpret_cast<uintptr_t>(addr)), length_(len), is_concrete_(false)
    {
#if 0
        if (_sym_get_basic_block_id() == 0x99de80) {    
            static int counter = 0;
            counter += 1;
            // printf("\nSYMBOLIC ACCESS: %s\n\n", _sym_expr_to_string(addr_expr_));
            uint64_t addr2 = (uint64_t) addr;
            printf("\nSYMBOLIC ACCESS[%d] at %lx with address %lx\n\n", counter, 0x99de80, addr2);
            if (addr2 < 0x15c4280 || addr2 > 0x15c42bf) // _
                printf("\n\nInput does not reach the expected address: %lx\n\n\n", addr2);
        }
#endif

#if 1
        int checkSymbolic = _sym_feasible(
            _sym_build_not_equal(addr_expr_, _sym_build_integer(address_, _sym_bits_helper(addr_expr)))
        );
        if (checkSymbolic == -1) {
            printf("Timeout in boundary check query\nAdding constraint\n");
            SymExpr inBounds = _sym_build_equal(addr_expr_, _sym_build_integer(address_, _sym_bits_helper(addr_expr)));
            _sym_push_path_constraint(inBounds, true, _sym_get_basic_block_id());
            return;
        }
        if (checkSymbolic == 0) {
            printf("Address is concrete!\n");
            is_concrete_ = true;
            return;
        }
#endif   

        uintptr_t beginPage = pageStart(address_);
        uintptr_t endPage = beginPage + kPageSize - 1;
        if (pageStart(address_ + len - 1) != beginPage)
            abort();

        PageState* state = ReadShadowIterator::getPageState(beginPage);
        if (state) {
            beginPage = reinterpret_cast<uintptr_t>(state->baseAddress);
            endPage = beginPage + state->size - 1;
        }
#if 0
        if (endPage - beginPage > 2048) { // we assume is within page...
            printf("Symbolic access within region [%lx, %lx] of %lu bytes\n", beginPage, endPage, 1 + endPage - beginPage);
            return;
        }
#endif
        int outOfPage = -1;
        
        if (HYBRID_SYMBOLIC_MEMORY_MAX_MERGE_OPS != 0) {
            outOfPage =_sym_feasible(
                _sym_build_bool_or(
                    _sym_build_unsigned_less_than(addr_expr_, _sym_build_integer(beginPage, _sym_bits_helper(addr_expr))),
                    _sym_build_unsigned_greater_than(
                        _sym_build_add(addr_expr_, _sym_build_integer(len - 1, _sym_bits_helper(addr_expr))),
                        _sym_build_integer(endPage, _sym_bits_helper(addr_expr)))
                )
            );
        }
        if (outOfPage == -1) {
            if (HYBRID_SYMBOLIC_MEMORY_MAX_MERGE_OPS != 0)
                printf("Timeout in boundary check query\nAdding constraint\n");
            SymExpr inBounds = _sym_build_unsigned_less_equal(
                            _sym_build_add(addr_expr_, _sym_build_integer(len - 1, _sym_bits_helper(addr_expr))),
                            _sym_build_integer(endPage, _sym_bits_helper(addr_expr)));
            inBounds = _sym_build_bool_and(inBounds,
                _sym_build_unsigned_greater_equal(addr_expr_, _sym_build_integer(beginPage, _sym_bits_helper(addr_expr)))
            );
            _sym_push_path_constraint(inBounds, true, _sym_get_basic_block_id());
            return;
        }
        if (outOfPage == 0) {
#if 0
            for (uintptr_t curr = beginPage; curr < endPage && 0; curr++) {
                int checkAddr = _sym_feasible(
                    _sym_build_equal(addr_expr_, _sym_build_integer(curr, _sym_bits_helper(addr_expr)))
                );
                if (checkAddr == 1) {
                    printf("Address can be: %lx\n", curr);
                }
            }
#endif
            printf("Symbolic access within region [%lx, %lx] of %lu bytes\n", beginPage, endPage, 1 + endPage - beginPage);
            return;
        }

        printf("SYMBOLIC ACCESS: %s\n", _sym_expr_to_string(addr_expr_));
        printf("BB: %lx\n", _sym_get_basic_block_id());
        _sym_print_stack();

        int merged_pages = 0;
        int checkBefore = 0;
        do {
            // printf("CHECK BEFORE\n");
            page_start_check = beginPage - kPageSize;
            page_end_check = beginPage - 1;
            page_address_check = _sym_get_basic_block_id();
            checkBefore = _sym_feasible(
                _sym_build_bool_and(
                    _sym_build_unsigned_less_than(addr_expr_, _sym_build_integer(beginPage, _sym_bits_helper(addr_expr))),
                    _sym_build_unsigned_greater_equal(addr_expr_, _sym_build_integer(beginPage - kPageSize, _sym_bits_helper(addr_expr)))
                )
            );
            page_address_check = 0;
            if (checkBefore == -1) abort();
            // printf("CHECK BEFORE 2\n");
            if (checkBefore == 1) {
                PageState* pageBefore = ReadShadowIterator::getPageState(beginPage - 1);
                if (pageBefore) {
                    beginPage -= pageBefore->size;
                } else {
                    beginPage -= kPageSize;
                }
                merged_pages += 1;
                printf("Address can read from a previous page at %lx! [merged=%d]\n", beginPage, merged_pages);
            }
        } while (checkBefore && merged_pages < HYBRID_SYMBOLIC_MEMORY_MAX_MERGE_OPS);

        int outOfBoundaries = false;
        if (merged_pages < HYBRID_SYMBOLIC_MEMORY_MAX_MERGE_OPS) {
            outOfBoundaries = _sym_feasible(
                _sym_build_unsigned_less_than(addr_expr_, _sym_build_integer(beginPage, _sym_bits_helper(addr_expr)))
            );
            if (outOfBoundaries == -1) abort();
        } else {
            printf("Concretizing access since it spanning too many pages! [id=%lx]\n", _sym_get_basic_block_id());
            _sym_print_stack();
            SymExpr concretize = _sym_build_equal(addr_expr_, _sym_build_integer(address_, _sym_bits_helper(addr_expr)));
            _sym_push_path_constraint(concretize, true, _sym_get_basic_block_id());
            is_concrete_ = true;
            return;
        }

        int checkAfter = 0;
        do {
            checkAfter = _sym_feasible(
                _sym_build_bool_and(
                    _sym_build_unsigned_greater_than(
                        _sym_build_add(addr_expr_, _sym_build_integer(len - 1, _sym_bits_helper(addr_expr))),
                        _sym_build_integer(endPage, _sym_bits_helper(addr_expr))),
                    _sym_build_unsigned_less_than(
                        _sym_build_add(addr_expr_, _sym_build_integer(len - 1, _sym_bits_helper(addr_expr))),
                        _sym_build_integer(endPage + endPage, _sym_bits_helper(addr_expr)))
                )
            );
            if (checkAfter == -1) abort();
            if (checkAfter == 1) {
                PageState* pageAfter = ReadShadowIterator::getPageState(endPage + 1);
                if (pageAfter) {
                    endPage += pageAfter->size;
                } else {
                    endPage += kPageSize;
                }
                merged_pages += 1;
                printf("Address can read from a subsequent page at %lx! [merged=%d]\n", endPage, merged_pages);
            }
        } while (checkAfter && merged_pages < HYBRID_SYMBOLIC_MEMORY_MAX_MERGE_OPS);

        if (merged_pages < HYBRID_SYMBOLIC_MEMORY_MAX_MERGE_OPS) {
            if (outOfBoundaries == 0) {
                outOfBoundaries = _sym_feasible(
                    _sym_build_unsigned_greater_than(
                        _sym_build_add(addr_expr_, _sym_build_integer(len - 1, _sym_bits_helper(addr_expr))),
                        _sym_build_integer(endPage, _sym_bits_helper(addr_expr)))
                );
                if (outOfBoundaries == -1) abort();
            }
        } else {
            printf("Concretizing access since it spanning too many pages! [id=%lx]\n", _sym_get_basic_block_id());
            _sym_print_stack();
            SymExpr concretize = _sym_build_equal(addr_expr_, _sym_build_integer(address_, _sym_bits_helper(addr_expr)));
            _sym_push_path_constraint(concretize, true, _sym_get_basic_block_id());
            is_concrete_ = true;
            return;
        }

#if 0
        if (1 + endPage - beginPage > 4096) {
            printf("Symbolic access spanning more %lu bytes! Aborting.\n", 1 + endPage - beginPage);
            abort();
        }
#endif

        if (outOfBoundaries == 1) {
            printf("Symbolic access can go outside page boundaries. Restricting it\n");
            SymExpr outOfBounds = _sym_build_unsigned_less_equal(
                        _sym_build_add(addr_expr_, _sym_build_integer(len - 1, _sym_bits_helper(addr_expr))),
                        _sym_build_integer(endPage, _sym_bits_helper(addr_expr)));
            outOfBounds = _sym_build_bool_and(outOfBounds,
                _sym_build_unsigned_greater_equal(addr_expr_, _sym_build_integer(beginPage, _sym_bits_helper(addr_expr)))
            );
            _sym_push_path_constraint(outOfBounds, true, _sym_get_basic_block_id());
        }

        printf("Symbolic access within region [%lx, %lx] of %lu bytes\n", beginPage, endPage, 1 + endPage - beginPage);

        PageState* prevState = nullptr;
        while (beginPage < endPage) {
            PageState* state = WriteShadowIterator::getOrCreatePageState(beginPage); 
            if (prevState == nullptr)
                prevState = state; 
            else if (prevState != state) {
                prevState->extend(*state);
                g_shadow_pages[beginPage] = prevState; // FIXME: deallocate memory
                uintptr_t nextPage = beginPage + kPageSize;
                while(g_shadow_pages[nextPage] == state) {
                    g_shadow_pages[nextPage] = prevState;
                    nextPage += kPageSize;
                }
            }
            beginPage += kPageSize;
        }
    }

    SymExpr read(void) {
        if (is_concrete_)
            return nullptr;

        PageState* state = WriteShadowIterator::getOrCreatePageState(pageStart(address_));
        assert(state);
        SymExpr offset = _sym_build_sub(addr_expr_, _sym_build_integer(state->getBaseAddress(), _sym_bits_helper(addr_expr_)));
        if (_sym_bits_helper(addr_expr_) > 32)
            offset = _sym_extract_helper(offset, 31, 0);
        return state->read(offset, length_ * 8);
    }

    bool write(SymExpr e, uint64_t value) {
        if (is_concrete_)
            return false;

        PageState* state = WriteShadowIterator::getOrCreatePageState(pageStart(address_));
        assert(state);
        SymExpr offset = _sym_build_sub(addr_expr_, _sym_build_integer(state->getBaseAddress(), _sym_bits_helper(addr_expr_)));
        if (_sym_bits_helper(addr_expr_) > 32)
            offset = _sym_extract_helper(offset, 31, 0);
        // printf("SYMBOLIC WRITE: %s %s [%lx]\n", _sym_expr_to_string(offset), e ? _sym_expr_to_string(offset) : "null", value);
        state->write(offset, e, value, length_ * 8);
        return true;
    }

    SymExpr   addr_expr_;
    uintptr_t address_;
    size_t    length_;
    bool      is_concrete_;
};

#endif
