#!/usr/bin/env bash
# Build tpde-llc (TPDE-LLVM) against LLVM 20 in Release mode.
#
#   bench/backend/build_tpde.sh TPDE_SRC BUILD_DIR [JOBS]
#
# TPDE_SRC is a clone of https://github.com/tpde2/tpde; its submodules are
# initialized (shallow) if needed. Only the x86-64 target is built, without
# tests. Result: BUILD_DIR/tpde-llvm/tpde-llc.
set -euo pipefail
src="${1:?usage: build_tpde.sh TPDE_SRC BUILD_DIR [JOBS]}"
build="${2:?usage: build_tpde.sh TPDE_SRC BUILD_DIR [JOBS]}"
jobs="${3:-2}"
( cd "$src" && git submodule update --init --depth 1 )
cmake -G Ninja -S "$src" -B "$build" -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_C_COMPILER=clang-20 -DCMAKE_CXX_COMPILER=clang++-20 \
    -DLLVM_DIR=/usr/lib/llvm-20/lib/cmake/llvm \
    -DTPDE_INCLUDE_TESTS=OFF -DTPDE_TARGETS=x86_64
ninja -C "$build" -j"$jobs" tpde-llc
echo "$build/tpde-llvm/tpde-llc"
