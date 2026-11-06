#!/usr/bin/env bash
# Where does the Goose back-end's speed come from? Relinks goovm-llc with two
# attribution variants and times the back-end phase of all four:
#
#   cpp         backend-cpp/gir_codegen_cpp.cpp as committed (std::vector, byte loops)
#   cpp-E6      cpp_e6_bump_inline.cpp: + bulk insert, reserve, a Goose-style bump
#               buffer for .text and always_inline emitters
#   goose       backend-goose/cg.goose as committed
#   goose-E1    goose_e1_byteloop.goose: bulk append replaced by byte loops like the C++
#
#   GOOSE=... GOOSE_STDLIB=... bench/attribution/run.sh BUILD_DIR WORK_DIR [RUNS] input.bc...
#
# BUILD_DIR is a goovm build with -DGOOVM_WITH_GOOSE=ON (backend-goose/build.sh).
# Prints the best back-end time (us) of RUNS runs per variant and input, and
# checks that all four produce identical objects.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$here/../.."
B="${1:?usage: run.sh BUILD_DIR WORK_DIR [RUNS] input.bc...}"
W="${2:?}"
RUNS="${3:-7}"
shift 3
: "${GOOSE:?}" "${GOOSE_STDLIB:?}"
mkdir -p "$W"
base="$B/tools/goovm-llc/goovm-llc"
var="$W/goovm-llc-variants"

"$GOOSE" --standalone --header "$W/e1.h" -o "$W/e1.c" "$here/goose_e1_byteloop.goose"
clang++-20 -O3 -DNDEBUG -std=gnu++17 -fno-exceptions -fno-rtti -I"$root/backend-cpp" -I"$root/gir" \
    -c "$here/cpp_e6_bump_inline.cpp" -o "$W/e6.o"
clang-20 -x c -O3 -DNDEBUG -w -c "$W/e1.c" -o "$W/e1.o"
clang++-20 -O3 -DNDEBUG \
    "$B/tools/goovm-llc/CMakeFiles/goovm-llc.dir/goovm-llc.cpp.o" \
    "$B/tools/goovm-llc/CMakeFiles/goovm-llc.dir/gir_export.cpp.o" \
    "$W/e6.o" "$W/e1.o" -o "$var" \
    -Wl,-rpath,"$(llvm-config-20 --libdir)" "$(llvm-config-20 --libdir)/libLLVM.so.1" -lm -lpthread

best_us() {  # best_us BIN BACKEND INPUT OUT
    local best=""
    for _ in $(seq "$RUNS"); do
        local us
        us=$("$1" --backend="$2" --time "$3" -o "$4" 2>&1 | grep -o 'backend_us=[0-9]*' | cut -d= -f2)
        if [ -z "$best" ] || [ "$us" -lt "$best" ]; then best=$us; fi
    done
    echo "$best"
}

echo "| input | cpp | cpp-E6 | goose | goose-E1 | cpp / goose | cpp-E6 / goose | identical |"
echo "|---|---:|---:|---:|---:|---:|---:|---|"
for in in "$@"; do
    n=$(basename "$in" .bc)
    c=$(best_us "$base" cpp "$in" "$W/$n.cpp.o")
    g=$(best_us "$base" goose "$in" "$W/$n.goose.o")
    c6=$(best_us "$var" cpp "$in" "$W/$n.e6.o")
    g1=$(best_us "$var" goose "$in" "$W/$n.e1.o")
    same=yes
    for o in goose e6 e1; do cmp -s "$W/$n.cpp.o" "$W/$n.$o.o" || same=NO; done
    printf "| %s | %d | %d | %d | %d | %.2fx | %.2fx | %s |\n" "$n" "$c" "$c6" "$g" "$g1" \
        "$(echo "$c / $g" | bc -l)" "$(echo "$c6 / $g" | bc -l)" "$same"
done
echo
echo "back-end phase only (us, best of $RUNS); the same goovm-llc front end and exporter for all"
