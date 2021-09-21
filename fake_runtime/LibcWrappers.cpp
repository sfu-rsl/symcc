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

#include <cstdio>
#include <cstdlib>
#include <cstring>

#include <arpa/inet.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include <Runtime.h>

#define SYM(x) x##_symbolized

void initLibcWrappers() {}

extern "C" {

void *SYM(malloc)(size_t size) { return NULL; }
void *SYM(calloc)(size_t nmemb, size_t size) { return NULL; }

// See comment on lseek and lseek64 below; the same applies to the "off"
// parameter of mmap.

void *SYM(mmap64)(void *addr, size_t len, int prot, int flags, int fildes,
                  uint64_t off) { return NULL; }
void *SYM(mmap)(void *addr, size_t len, int prot, int flags, int fildes,
                uint32_t off) { return NULL; }
int SYM(open)(const char *path, int oflag, mode_t mode) { return 0; }
ssize_t SYM(read)(int fildes, void *buf, size_t nbyte) { return 0; }

// lseek is a bit tricky because, depending on preprocessor macros, glibc
// defines it to be a function operating on 32-bit values or aliases it to
// lseek64. Therefore, we cannot know in general whether calling lseek in our
// code takes a 32 or a 64-bit offset and whether it returns a 32 or a 64-bit
// result. In fact, since we compile this library against LLVM which requires us
// to compile with "-D_FILE_OFFSET_BITS=64", we happen to know that, for us,
// lseek is an alias to lseek64, but this may change any time. More importantly,
// client code may call one or the other, depending on its preprocessor
// definitions.
//
// Therefore, we define symbolic versions of both lseek and lseek64, but
// internally we only use lseek64 because it's the only one on whose
// availability we can rely.

uint64_t SYM(lseek64)(int fd, uint64_t offset, int whence) { return 0; }
uint32_t SYM(lseek)(int fd, uint32_t offset, int whence) { return 0; }
FILE *SYM(fopen)(const char *pathname, const char *mode) { return NULL; }
FILE *SYM(fopen64)(const char *pathname, const char *mode) { return NULL; }
size_t SYM(fread)(void *ptr, size_t size, size_t nmemb, FILE *stream) { return 0; }
char *SYM(fgets)(char *str, int n, FILE *stream) { return NULL; }
void SYM(rewind)(FILE *stream) {}
int SYM(fseek)(FILE *stream, long offset, int whence) { return 0; }
int SYM(fseeko)(FILE *stream, off_t offset, int whence) { return 0; }
int SYM(fseeko64)(FILE *stream, uint64_t offset, int whence) { return 0; }
int SYM(getc)(FILE *stream) { return 0; }
int SYM(fgetc)(FILE *stream) { return 0; }
int SYM(ungetc)(int c, FILE *stream) { return 0; }

extern "C" {
  void *SYM(memcpy)(void *dest, const void *src, size_t n) { return NULL; }
  void *SYM(memset)(void *s, int c, size_t n) { return NULL; }
  void *SYM(memmove)(void *dest, const void *src, size_t n) { return NULL; }
}

char *SYM(strncpy)(char *dest, const char *src, size_t n) { return NULL; }
const char *SYM(strchr)(const char *s, int c) { return NULL; }
int SYM(memcmp)(const void *a, const void *b, size_t n) { return 0; }
uint32_t SYM(ntohl)(uint32_t netlong) { return 0; }

uint32_t SYM(strncmp)(const char *a, const char *b, size_t n) { return 0; }
int SYM(bcmp)(const void *a, const void *b, size_t n) { return 0; }

}
