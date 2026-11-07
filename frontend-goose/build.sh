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
# G1: patches to the Goose runtime, which a standalone program holds
# verbatim (runtime-patches/README.md). Each is a diff against the
# runtime's own sources (src/runtime/*.h of the Goose tree), applied to the
# generated C; one that does not apply stops the build, since the runtime
# it was written for has changed. RUNTIME_PATCHES=0 builds without them.
if [ "${RUNTIME_PATCHES:-1}" != 0 ]; then
    for p in "$HERE"/runtime-patches/*.patch; do
        patch --quiet --forward -p1 "$OUT/goosecc.c" "$p" ||
            { echo "build.sh: runtime patch $p does not apply (RUNTIME_PATCHES=0 skips it)" >&2; exit 1; }
    done
    rm -f "$OUT/goosecc.c.orig" "$OUT/goosecc.c.rej"
    # The regions nearly every compile touches (runtime-patches/hot-regions.txt,
    # by the names of their globals; hot_regions.py makes the list) get the
    # first slots of the reservation and are made accessible at start-up.
    # Registry indices: main's runtime stacks first (gs_rt_init's third
    # argument), then the globals in the order their stacks are set up. A
    # name the program no longer has is left out; the list only places
    # regions, so a stale one costs time, never correctness.
    printf '' > "$OUT/hot_regions.h"
    NRT=$(grep -o 'gs_rt_init(argc, argv, [0-9]*' "$OUT/goosecc.c" | grep -o '[0-9]*$')
    { seq 0 $((NRT - 1)) | sed 's/^/rt/'
      grep -o 'gs_stack_init((&GS_GL->gs_gstk_[A-Za-z0-9_]*' "$OUT/goosecc.c" | sed 's/.*gs_gstk_//'; } > "$OUT/regions.txt"
    if [ -f "$HERE/runtime-patches/hot-regions.txt" ]; then
        HOT=$(awk 'NR == FNR { if ($1 !~ /^#/) hot[$1] = 1; next } ($1 in hot) { printf "%s%d", (n++ ? "," : ""), FNR - 1 }' \
            "$HERE/runtime-patches/hot-regions.txt" "$OUT/regions.txt")
        [ -n "$HOT" ] && printf '#define GS_HOT_REGIONS %s\n' "$HOT" > "$OUT/hot_regions.h"
    fi
    CFLAGS="$CFLAGS -include $OUT/hot_regions.h"
    # PROFILE_REGIONS=1: each run lists the regions it touched on stderr
    # (runtime-patches/hot_regions.py)
    [ "${PROFILE_REGIONS:-0}" = 1 ] && CFLAGS="$CFLAGS -DGS_REGION_PROFILE"
fi
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
