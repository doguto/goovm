#!/usr/bin/env bash
# Build the benchmark inputs (LLVM bitcode as clang-20 -O0 emits it).
#
#   bench/backend/make_inputs.sh OUTDIR [SIZES...]      (default sizes: 1000 5000 20000)
#
# Produces in OUTDIR:
#   gen-<N>.c / gen-<N>.bc   synthetic programs with N functions (gen.py, seed 1)
#   spass.bc                 the 44 SPASS files (llvm-test-suite) that fit the
#                            subset, linked into one module with llvm-link-20
#   typeset.bc               the same for consumer-typeset (35 files)
# The real-world inputs are skipped when the test suite is not found
# (LLVM_TEST_SUITE, default /home/user/llvm/llvm-test-suite).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
out="${1:?usage: make_inputs.sh OUTDIR [SIZES...]}"
shift || true
sizes=("$@")
[ ${#sizes[@]} -eq 0 ] && sizes=(1000 5000 20000)
CLANG="${CLANG:-clang-20}"
LINK="${LLVM_LINK:-llvm-link-20}"
GOOVM="${GOOVM_LLC:-$here/../../build/tools/goovm-llc/goovm-llc}"
SUITE="${LLVM_TEST_SUITE:-/home/user/llvm/llvm-test-suite}"
mkdir -p "$out"

for n in "${sizes[@]}"; do
    python3 "$here/gen.py" "$n" --seed 1 -o "$out/gen-$n.c"
    "$CLANG" -O0 -w -c -emit-llvm "$out/gen-$n.c" -o "$out/gen-$n.bc"
    echo "gen-$n.bc"
done

# Real-world subsets: every file goovm-llc accepts, linked into one module.
realworld() {  # name dir flags...
    local name="$1" dir="$SUITE/$2"; shift 2
    [ -d "$dir" ] || { echo "skip $name: $dir not found"; return; }
    local tmp="$out/.$name"; mkdir -p "$tmp"
    local ok=()
    for c in "$dir"/*.c; do
        local bc="$tmp/$(basename "$c" .c).bc"
        "$CLANG" -O0 -w -c -emit-llvm "$c" -o "$bc" -I"$dir" "$@" || continue
        if "$GOOVM" --backend=llvm-only "$bc" 2>/dev/null; then ok+=("$bc"); fi
    done
    "$LINK" "${ok[@]}" -o "$out/$name.bc"
    echo "$name.bc (${#ok[@]} files)"
}
if [ -x "$GOOVM" ]; then
    realworld spass MultiSource/Applications/SPASS -DCLOCK_NO_TIMING -fno-strict-aliasing -std=gnu17
    realworld typeset MultiSource/Benchmarks/MiBench/consumer-typeset -DOS_UNIX=1 -DOS_DOS=0 -DOS_MAC=0 -DDB_FIX=0 \
        -DUSE_STAT=1 -DSAFE_DFT=0 -DCOLLATE=1 '-DLIB_DIR="lout.lib"' '-DFONT_DIR="font"' '-DMAPS_DIR="maps"' \
        '-DINCL_DIR="include"' '-DDATA_DIR="data"' '-DHYPH_DIR="hyph"' '-DLOCALE_DIR="locale"' -DCHAR_IN=1 \
        -DCHAR_OUT=0 -DLOCALE_ON=1 -DASSERT_ON=1 -DDEBUG_ON=0 -DPDF_COMPRESSION=0 -D_FORTIFY_SOURCE=0 -std=c99
else
    echo "skip real-world inputs: goovm-llc not found at $GOOVM"
fi
