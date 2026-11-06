#!/usr/bin/env bash
# Generate cg.c / cg.h from cg.goose and build goovm-llc with the Goose
# back-end linked in (-DGOOVM_WITH_GOOSE=ON).
#
#   GOOSE=/path/to/goose GOOSE_STDLIB=/path/to/goose/stdlib \
#       backend-goose/build.sh [BUILD_DIR]
#
# BUILD_DIR defaults to <repo>/build-goose. The generated C goes to
# backend-goose/build/ (git-ignored; override with GEN_DIR). Other knobs:
#   CC, CXX     C/C++ compiler (default clang-20 / clang++-20, as the C++ build)
#   LLVM_DIR    LLVM 20 CMake dir (default /usr/lib/llvm-20/lib/cmake/llvm)
#   JOBS        ninja parallelism (default 4)
#   GOOSE_FLAGS extra goose options (e.g. -O1); the default is goose's -O2
#
# The generated C is compiled by CMake exactly like the C++ back-end: the
# same compiler and CMAKE_BUILD_TYPE=Release flags (-O3 -DNDEBUG).
# The result is BUILD_DIR/tools/goovm-llc/goovm-llc (--backend=goose).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(dirname "$here")"
build="${1:-$root/build-goose}"
gen="${GEN_DIR:-$here/build}"
: "${GOOSE:?set GOOSE to the goose compiler}"
: "${GOOSE_STDLIB:?set GOOSE_STDLIB to goose/stdlib}"
export GOOSE_STDLIB
CC="${CC:-clang-20}"
CXX="${CXX:-clang++-20}"
LLVM_DIR="${LLVM_DIR:-/usr/lib/llvm-20/lib/cmake/llvm}"

mkdir -p "$gen"
# shellcheck disable=SC2086
"$GOOSE" ${GOOSE_FLAGS:-} --standalone --header "$gen/cg.h" -o "$gen/cg.c" "$here/cg.goose"
echo "generated $gen/cg.c ($(wc -l < "$gen/cg.c") lines) and $gen/cg.h"

cmake -G Ninja -S "$root" -B "$build" -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_C_COMPILER="$CC" -DCMAKE_CXX_COMPILER="$CXX" -DLLVM_DIR="$LLVM_DIR" \
    -DGOOVM_WITH_GOOSE=ON -DGOOVM_GOOSE_C="$gen/cg.c" -DGOOVM_GOOSE_H="$gen/cg.h" > /dev/null
ninja -C "$build" -j"${JOBS:-4}"
echo "built $build/tools/goovm-llc/goovm-llc"
