#!/usr/bin/env bash
# Build bridge.goose as a C library, link it into the C++ host, and run it.
#   GOOSE=path/to/goose GOOSE_STDLIB=path/to/stdlib ./run.sh [build-dir]
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
out="${1:-$here/build}"
mkdir -p "$out"
: "${GOOSE:?set GOOSE to the goose compiler}"
CC="${CC:-clang-20}"
CXX="${CXX:-clang++-20}"

"$GOOSE" --standalone --header "$out/bridge.h" -o "$out/bridge.c" "$here/bridge.goose"
"$CC" -O2 -w -c "$out/bridge.c" -o "$out/bridge.o"
"$CXX" -O2 -std=c++17 -I"$out" "$here/host.cpp" "$out/bridge.o" -o "$out/host" -lm -pthread
"$out/host"
