#!/bin/bash
# Builds goosecc: Goose -> C (standalone, with the runtime) -> clang -O2.
#   frontend-goose/build.sh [outdir]      (default: frontend-goose/build)
# Needs GOOSE (the goose compiler) and GOOSE_STDLIB, or the defaults below.
#   LIBC=musl|glibc   the C library of the static executable (default: musl
#                     when its static libc is installed, apt install musl-dev)
#   LDFLAGS=          a dynamic executable with glibc instead
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
OUT="${1:-$HERE/build}"
S=/tmp/claude-0/-home-user-goovm/593b2907-8413-508c-8bdb-c68ef6e66f6e/scratchpad
GOOSE="${GOOSE:-$S/work/goose-build/goose}"
export GOOSE_STDLIB="${GOOSE_STDLIB:-$S/src/goose/stdlib}"
CC="${CC:-clang-20}"
CFLAGS="${CFLAGS:--O2}"
# a static executable starts ~0.3 ms faster (no dynamic linking), which is
# 5% of a typical compile; LDFLAGS= builds a dynamic one
LDFLAGS="${LDFLAGS--static}"
# Each global growable array is a data stack, a reserved region (goose check
# --stacks). Reserving 256 MB instead of the default 2 GB per region puts
# them closer together, so that the regions a run touches share page-table
# pages: 5% of a CTMark compile. A table of one translation unit may then
# hold 256 MB (the largest, the AST, is about 2.3 times the size of the
# preprocessed source); past that, goosecc stops with a data stack overflow.
GOOSE_FLAGS="${GOOSE_FLAGS---stack-reserve 256M}"
mkdir -p "$OUT"
"$GOOSE" --standalone ${GOOSE_FLAGS} --include "$HERE/src/goosecc_rt.h" -o "$OUT/goosecc.c" "$HERE/src/main.goose"
# The header cache (B4) keys its entries by this build's identity: a hash
# of the generated C, so that a rebuilt compiler never reads entries
# written by another one.
BUILD_ID="0x$(cat "$OUT/goosecc.c" "$HERE/src/goosecc_rt.h" | sha1sum | cut -c1-16)ull"
CFLAGS="$CFLAGS -DGOOSECC_BUILD_ID=$BUILD_ID"
# musl: a static glibc executable spends 0.5-0.7 ms of every run in glibc's
# start-up, mostly probing the caches with cpuid (init_cacheinfo), which
# traps to the hypervisor in a virtual machine; musl's start-up does not.
# Same C code, same outputs; the static glibc build is LIBC=glibc.
# Each of the ~200 data stack regions gets madvise(MADV_NOHUGEPAGE) from
# the runtime at start-up, so that a region holding a few bytes does not
# take a transparent huge page. Unless the kernel's THP mode is "always",
# no region would get one anyway, and the advice only costs a system call
# and a VMA split per region: 0.27 ms of every run (B4, NOTES.md 11). The
# runtime tests the macro, so a header forced in first, which includes
# <sys/mman.h> and undefines it, drops the advice. THP=keep keeps it.
THP="${THP:-auto}"
if [ "$THP" = auto ]; then
    if grep -q '\[always\]' /sys/kernel/mm/transparent_hugepage/enabled 2>/dev/null; then THP=keep; else THP=drop; fi
fi
if [ "$THP" = drop ]; then
    printf '#include <sys/mman.h>\n#undef MADV_NOHUGEPAGE\n' > "$OUT/no_nohugepage.h"
    CFLAGS="$CFLAGS -include $OUT/no_nohugepage.h"
fi
MUSL="${MUSL:-/usr/lib/x86_64-linux-musl}"
LIBC="${LIBC:-auto}"
if [ "$LIBC" = auto ]; then
    if [ "$LDFLAGS" = -static ] && [ -f "$MUSL/libc.a" ] && [ -d /usr/include/x86_64-linux-musl ]; then LIBC=musl; else LIBC=glibc; fi
fi
if [ "$LIBC" = musl ]; then
    RT="$("$CC" --rtlib=compiler-rt -print-libgcc-file-name)"
    [ -f "$RT" ] || RT="$("$CC" -print-libgcc-file-name)"
    "$CC" $CFLAGS -static -w -nostdinc -isystem "$("$CC" -print-resource-dir)/include" \
        -isystem /usr/include/x86_64-linux-musl -nostdlib -L"$MUSL" "$MUSL/crt1.o" "$MUSL/crti.o" \
        "$OUT/goosecc.c" -lc "$RT" "$MUSL/crtn.o" -o "$OUT/goosecc"
else
    "$CC" $CFLAGS $LDFLAGS -w "$OUT/goosecc.c" -lm -pthread -o "$OUT/goosecc" 2>/dev/null ||
        "$CC" $CFLAGS -w "$OUT/goosecc.c" -lm -pthread -o "$OUT/goosecc"
fi
echo "built $OUT/goosecc ($LIBC)"
