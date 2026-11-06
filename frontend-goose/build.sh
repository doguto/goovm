#!/bin/bash
# Builds goosecc: Goose -> C (standalone, with the runtime) -> clang -O2.
#   frontend-goose/build.sh [outdir]      (default: frontend-goose/build)
# Needs GOOSE (the goose compiler) and GOOSE_STDLIB, or the defaults below.
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
mkdir -p "$OUT"
"$GOOSE" --standalone ${GOOSE_FLAGS:-} --include "$HERE/src/goosecc_rt.h" -o "$OUT/goosecc.c" "$HERE/src/main.goose"
"$CC" $CFLAGS $LDFLAGS -w "$OUT/goosecc.c" -lm -pthread -o "$OUT/goosecc" 2>/dev/null ||
    "$CC" $CFLAGS -w "$OUT/goosecc.c" -lm -pthread -o "$OUT/goosecc"
echo "built $OUT/goosecc"
