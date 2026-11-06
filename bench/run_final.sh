#!/usr/bin/env bash
# The final measurements, run one after another on an otherwise idle machine.
#
#   GOOSE=... GOOSE_STDLIB=... GOOVM=... TPDE=... INPUTS=... CTMARK_O0_CC=... \
#     bench/run_final.sh OUT_DIR
#
#   GOOVM         goovm-llc built with GOOVM_WITH_GOOSE=ON (has --backend=goose)
#   TPDE          tpde-llc
#   INPUTS        directory made by bench/backend/make_inputs.sh
#   CTMARK_O0_CC  compile_commands.json of llvm-test-suite CTMark configured
#                 with cmake/caches/O0.cmake
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
out="${1:?usage: run_final.sh OUT_DIR}"
mkdir -p "$out"
: "${GOOSE:?}" "${GOOSE_STDLIB:?}" "${GOOVM:?}" "${TPDE:?}" "${INPUTS:?}" "${CTMARK_O0_CC:?}"
export GOOSE GOOSE_STDLIB

{
    echo "# machine"
    uname -srm; nproc; grep -m1 'model name' /proc/cpuinfo || true; uptime
    clang-20 --version | head -1
    "$GOOSE" --version
} > "$out/machine.txt" 2>&1

echo "== back-ends on bitcode inputs" >&2
bash "$here/backend/run.sh" -n 5 --goovm "$GOOVM" --tpde "$TPDE" --inproc --goose \
    "$INPUTS"/gen-1000.bc "$INPUTS"/gen-5000.bc "$INPUTS"/gen-20000.bc "$INPUTS"/spass.bc "$INPUTS"/typeset.bc \
    > "$out/backend.md"

echo "== in-process phase breakdown" >&2
for f in "$INPUTS"/gen-20000.bc "$INPUTS"/spass.bc; do
    for b in cpp goose llvm; do
        best=""
        for i in 1 2 3 4 5; do
            line=$("$GOOVM" --backend=$b --time "$f" -o "$out/tmp.o" 2>&1 | grep '^goovm-time:')
            us=$(echo "$line" | sed -E 's/.*backend_us=([0-9]+).*/\1/')
            if [ -z "$best" ] || [ "$us" -lt "$(echo "$best" | sed -E 's/.*backend_us=([0-9]+).*/\1/')" ]; then best="$line"; fi
        done
        echo "$(basename "$f") $b $best"
    done
    "$TPDE" --time-trace="$out/tpde-trace.json" "$f" -o "$out/tmp.o"
    python3 -I -c '
import json, sys
d = json.load(open(sys.argv[1])); d = d["traceEvents"] if isinstance(d, dict) else d
t = {e["name"]: e["dur"] for e in d if e.get("name", "").startswith("Total ")}
print(sys.argv[2], "tpde", " ".join(f"{k[6:].replace(\" \", \"_\")}_us={v}" for k, v in sorted(t.items())))
' "$out/tpde-trace.json" "$(basename "$f")"
    for b in cpp goose; do "$GOOVM" --backend=$b "$f" -o "$out/$(basename "$f" .bc).$b.o"; done
    "$TPDE" "$f" -o "$out/$(basename "$f" .bc).tpde.o"
    llc-20 -O0 -relocation-model=pic -filetype=obj "$f" -o "$out/$(basename "$f" .bc).llc.o"
    size "$out/$(basename "$f" .bc)".*.o
    cmp "$out/$(basename "$f" .bc).cpp.o" "$out/$(basename "$f" .bc).goose.o" && echo "cpp and goose objects identical"
done > "$out/phases.txt" 2>&1
rm -f "$out"/*.o "$out/tpde-trace.json"

echo "== CTMark end to end" >&2
python3 "$here/e2e/ctmark_backends.py" "$CTMARK_O0_CC" --tpde "$TPDE" --goovm "$GOOVM" --goose --runs 2 \
    --out "$out/e2e.json" > "$out/e2e.md"

echo "== IR core" >&2
python3 "$here/../poc/ircore/run.py" "$GOOSE" "$out/ircore-work" --n 2000000 --runs 5 > "$out/ircore.md"

echo "== bridge" >&2
bash "$here/../poc/bridge/run.sh" "$out/bridge-work" > "$out/bridge.txt"

echo "== code quality" >&2
GOOVM="$GOOVM" TPDE="$TPDE" bash "$here/codequal/run.sh" "$out/codequal-work" 5 2 > "$out/codequal.md"

echo "done: $out" >&2
