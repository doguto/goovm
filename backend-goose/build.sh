#!/usr/bin/env bash
# Configure and build goovm-llc with the Goose back-end.
#
#   GOOSE=/path/to/goose GOOSE_STDLIB=/path/to/goose/stdlib \
#       backend-goose/build.sh [BUILD_DIR]
#
# BUILD_DIR defaults to <repo>/build. CMake runs goose on backend-goose/cg.goose
# (which imports the other *.goose files) and compiles the generated C with
# the same compiler and flags as the C++ (Release: -O3 -DNDEBUG). Knobs:
#   CC, CXX     C/C++ compiler (default clang-20 / clang++-20)
#   LLVM_DIR    LLVM 20 CMake dir (default /usr/lib/llvm-20/lib/cmake/llvm)
#   JOBS        ninja parallelism (default 3)
#   GOOSE_FLAGS extra goose options (e.g. -O1); the default is goose's -O2
# The result is BUILD_DIR/tools/goovm-llc/goovm-llc.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(dirname "$here")"
build="${1:-$root/build}"
: "${GOOSE:?set GOOSE to the goose compiler}"
: "${GOOSE_STDLIB:?set GOOSE_STDLIB to goose/stdlib}"
CC="${CC:-clang-20}"
CXX="${CXX:-clang++-20}"
LLVM_DIR="${LLVM_DIR:-/usr/lib/llvm-20/lib/cmake/llvm}"

cmake -G Ninja -S "$root" -B "$build" -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_C_COMPILER="$CC" -DCMAKE_CXX_COMPILER="$CXX" -DLLVM_DIR="$LLVM_DIR" \
    -DGOOVM_GOOSE="$GOOSE" -DGOOVM_GOOSE_STDLIB="$GOOSE_STDLIB" -DGOOVM_GOOSE_FLAGS="${GOOSE_FLAGS:-}" > /dev/null
ninja -C "$build" -j"${JOBS:-3}"
echo "built $build/tools/goovm-llc/goovm-llc"
