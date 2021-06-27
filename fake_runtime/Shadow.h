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

#endif
