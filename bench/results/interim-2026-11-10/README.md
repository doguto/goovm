# Interim CTMark run times (2026-11-10)

Build: main 3eb6eed (E1 + the first E2 checkpoint 14dec17). Command:

    tests/suite.py --goovm build/tools/goovm-llc/goovm-llc --cc build/tools/goovm-cc/goovm-cc \
        --corpus ctmark,ctmark-cxx --variants O0,O1,O2,cc-O2 -j1 --time-run 3 --time-ref O1,O2

Best of 3, single-threaded, while four other agents were running (load average about 10), so
individual ratios are noisy. The optimizing variants take clang -O<l> -Xclang -disable-llvm-passes IR.

| | geomean vs clang at the same level |
|---|---:|
| O0 (goovm-llc) | 0.89 x clang -O0 |
| O1 (goovm-llc) | 1.13 x clang -O1 (E1: 1.57) |
| O2 (goovm-llc) | 1.29 x clang -O2 |
| cc-O2 (goovm-cc) | 1.20 x clang -O2 |

Full table: ctmark-runtime.md. E2 is still in progress (vectorization, libcall simplification and more remain).
