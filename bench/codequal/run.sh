#!/usr/bin/env bash
# Code quality of the -O0 back-ends: build kernels.c through each back-end,
# check the outputs agree, and time the programs (best of N, whole process).
#
#   GOOVM=goovm-llc TPDE=tpde-llc bench/codequal/run.sh WORK_DIR [RUNS] [SCALE]
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
w="${1:?usage: run.sh WORK_DIR [RUNS] [SCALE]}"
runs="${2:-3}"
scale="${3:-1}"
: "${GOOVM:?}" "${TPDE:?}"
mkdir -p "$w"
clang-20 -O0 -w -c -emit-llvm "$here/kernels.c" -o "$w/k.bc"
clang-20 -O0 -w -c "$here/kernels.c" -o "$w/k.clang-O0.o"
clang-20 -O2 -w -c "$here/kernels.c" -o "$w/k.clang-O2.o"
llc-20 -O0 -relocation-model=pic -filetype=obj "$w/k.bc" -o "$w/k.llc.o"
"$TPDE" "$w/k.bc" -o "$w/k.tpde.o"
"$GOOVM" --backend=cpp "$w/k.bc" -o "$w/k.goovm.o"
variants="clang-O0 clang-O2 llc tpde goovm"
if "$GOOVM" --backend=goose "$w/k.bc" -o "$w/k.goose.o" 2>/dev/null; then variants="$variants goose"; fi
for v in $variants; do clang-20 "$w/k.$v.o" -o "$w/k.$v"; done
"$w/k.clang-O0" "$scale" > "$w/expected.txt"
echo "| back-end | run time (s) | vs llc -O0 | .text bytes |"
echo "|---|---:|---:|---:|"
declare -A t
for v in $variants; do
    "$w/k.$v" "$scale" | cmp -s - "$w/expected.txt" || { echo "OUTPUT MISMATCH: $v" >&2; exit 1; }
    best=""
    for i in $(seq "$runs"); do
        s=$(date +%s%N); "$w/k.$v" "$scale" > /dev/null; e=$(date +%s%N)
        d=$(( e - s )); if [ -z "$best" ] || [ "$d" -lt "$best" ]; then best=$d; fi
    done
    t[$v]=$best
done
for v in $variants; do
    text=$(size -A "$w/k.$v.o" | awk '$1==".text"{print $2}')
    printf "| %s | %.3f | %.2fx | %s |\n" "$v" "$(echo "${t[$v]} / 1000000000" | bc -l)" \
        "$(echo "${t[$v]} / ${t[llc]}" | bc -l)" "$text"
done
