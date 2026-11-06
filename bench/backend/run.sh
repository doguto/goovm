#!/usr/bin/env bash
# Time the -O0 back-ends on bitcode inputs and print a markdown table.
#
#   bench/backend/run.sh [-n RUNS] [--goovm PATH] [--tpde PATH] [--llc PATH]
#                        [--inproc] [--goose] input.bc...
#
# For every input, each tool is run RUNS times (default 5) and the best wall
# time is kept:
#   llc        llc-20 -O0 -filetype=obj in.bc -o out.o
#   tpde       tpde-llc in.bc -o out.o                     (if found)
#   goovm      goovm-llc --backend=cpp --time in.bc -o out.o
#   llvm-inproc goovm-llc --backend=llvm   (--inproc: LLVM -O0 in our process)
#   goose      goovm-llc --backend=goose   (--goose: needs GOOVM_WITH_GOOSE)
# For goovm the phase breakdown (parse/export/back-end/write) of its best run
# is printed too. Wall times include process start-up and libLLVM loading for
# every tool. Run on a quiet machine; nothing here pins CPUs.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
RUNS=5
GOOVM="${GOOVM_LLC:-$here/../../build/tools/goovm-llc/goovm-llc}"
LLC="${LLC:-llc-20}"
TPDE="${TPDE_LLC:-}"
INPROC=0
GOOSE=0
inputs=()
while [ $# -gt 0 ]; do
    case "$1" in
        -n) RUNS="$2"; shift 2 ;;
        --goovm) GOOVM="$2"; shift 2 ;;
        --tpde) TPDE="$2"; shift 2 ;;
        --llc) LLC="$2"; shift 2 ;;
        --inproc) INPROC=1; shift ;;
        --goose) GOOSE=1; shift ;;
        -h|--help) sed -n '2,17p' "$0"; exit 0 ;;
        *) inputs+=("$1"); shift ;;
    esac
done
[ ${#inputs[@]} -gt 0 ] || { echo "usage: run.sh [options] input.bc..." >&2; exit 1; }
if [ -z "$TPDE" ]; then
    for c in "$here/../../build/tpde/tpde-llvm/tpde-llc" "$(command -v tpde-llc || true)"; do
        [ -n "$c" ] && [ -x "$c" ] && { TPDE="$c"; break; }
    done
fi
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# best_of CMD... : prints the best wall time in microseconds; fails if CMD fails.
best_of() {
    local best="" t0 t1 d
    for ((r = 0; r < RUNS; r++)); do
        t0=$EPOCHREALTIME
        "$@" >/dev/null 2>"$tmp/err" || { cat "$tmp/err" >&2; echo "FAIL"; return; }
        t1=$EPOCHREALTIME
        d=$(( (${t1/./} - ${t0/./}) ))
        if [ -z "$best" ] || [ "$d" -lt "$best" ]; then best=$d; cp "$tmp/err" "$tmp/best_err"; fi
    done
    echo "$best"
}
ms() { [ "$1" = "FAIL" ] || [ "$1" = "-" ] && { echo "$1"; return; }; awk -v u="$1" 'BEGIN { printf "%.1f", u / 1000 }'; }
ratio() { [[ "$1" =~ ^[0-9]+$ && "$2" =~ ^[0-9]+$ ]] && awk -v a="$1" -v b="$2" 'BEGIN { printf "%.1fx", a / b }' || echo "-"; }

echo "best of $RUNS runs, wall time in ms (process start included); goovm phases in ms from its --time output"
echo
hdr="| input | LLVM insts | llc -O0 | tpde-llc | goovm cpp | goovm vs llc | goovm vs tpde | parse | export | back-end | write |"
sep="|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|"
[ $INPROC = 1 ] && { hdr="$hdr llvm in-proc |"; sep="$sep---:|"; }
[ $GOOSE = 1 ] && { hdr="$hdr goovm goose | goose back-end |"; sep="$sep---:|---:|"; }
echo "$hdr"
echo "$sep"
for in in "${inputs[@]}"; do
    t_llc=$(best_of "$LLC" -O0 -filetype=obj "$in" -o "$tmp/llc.o")
    t_tpde="-"
    [ -n "$TPDE" ] && t_tpde=$(best_of "$TPDE" "$in" -o "$tmp/tpde.o")
    t_goo=$(best_of "$GOOVM" --backend=cpp --time "$in" -o "$tmp/goo.o")
    line=$(grep '^goovm-time:' "$tmp/best_err" || true)
    get() { sed -n "s/.* $1=\([0-9]*\).*/\1/p" <<<"$line"; }
    row="| $(basename "$in") | $(get llvm_insts) | $(ms "$t_llc") | $(ms "$t_tpde") | $(ms "$t_goo") | $(ratio "$t_llc" "$t_goo") | $(ratio "$t_tpde" "$t_goo") | $(ms "$(get parse_us)") | $(ms "$(get export_us)") | $(ms "$(get backend_us)") | $(ms "$(get write_us)") |"
    if [ $INPROC = 1 ]; then
        row="$row $(ms "$(best_of "$GOOVM" --backend=llvm "$in" -o "$tmp/inproc.o")") |"
    fi
    if [ $GOOSE = 1 ]; then
        t_gs=$(best_of "$GOOVM" --backend=goose --time "$in" -o "$tmp/goose.o")
        gl=$(grep '^goovm-time:' "$tmp/best_err" || true)
        row="$row $(ms "$t_gs") | $(ms "$(sed -n 's/.* backend_us=\([0-9]*\).*/\1/p' <<<"$gl")") |"
        if [ -f "$tmp/goose.o" ] && ! cmp -s "$tmp/goo.o" "$tmp/goose.o"; then
            echo "warning: goose and cpp objects differ for $in" >&2
        fi
    fi
    echo "$row"
done
