# goovm-llc correctness report

goovm-llc: `build/tools/goovm-llc/goovm-llc`; variants: O0, O1, O2, cc-O2

| corpus | tests | clang -O0 pass | excluded | O0 pass | O0 fail | O0 unsup | O0 fallback | O1 pass | O1 fail | O1 unsup | O1 fallback | O2 pass | O2 fail | O2 unsup | O2 fallback | cc-O2 pass | cc-O2 fail | cc-O2 unsup | cc-O2 fallback |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| ctmark | 6 | 6 | 0 | 6 | 0 | 0 | 0 | 6 (of 6) | 0 | 0 | 0 | 6 (of 6) | 0 | 0 | 0 | 6 (of 6) | 0 | 0 | 0 |
| ctmark-cxx | 4 | 4 | 0 | 4 | 0 | 0 | 0 | 4 (of 4) | 0 | 0 | 0 | 4 (of 4) | 0 | 0 | 0 | 4 (of 4) | 0 | 0 | 0 |

pass includes fallback; fallback counts tests in which at least one file was compiled by LLVM's code generator (goovm-llc --fallback). An optimizing variant (O1, O2-g, cc-O3, O2ir, ...) runs the tests that also pass when built with plain clang-20 at its level ("of N").

## Run times (best of 3, seconds; each variant's ratio to clang at its level when that is timed, else to clang -O0)

| test | clang -O0 | clang -O1 | clang -O2 | O0 | O0 / clang -O0 | O1 | O1 / clang -O1 | O2 | O2 / clang -O2 | cc-O2 | cc-O2 / clang -O2 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| ctmark/sqlite3 | 6.633 | 3.080 | 2.815 | 6.060 | 0.91 | 3.008 | 0.98 | 3.584 | 1.27 | 3.539 | 1.26 |
| ctmark/SPASS | 21.329 | 9.882 | 8.556 | 23.944 | 1.12 | 8.285 | 0.84 | 10.300 | 1.20 | 11.510 | 1.35 |
| ctmark/ClamAV | 0.315 | 0.271 | 0.256 | 0.313 | 0.99 | 0.287 | 1.06 | 0.361 | 1.41 | 0.256 | 1.00 |
| ctmark/lencod | 15.645 | 4.642 | 4.798 | 15.219 | 0.97 | 6.999 | 1.51 | 7.715 | 1.61 | 7.143 | 1.49 |
| ctmark/mafft | 49.349 | 24.537 | 25.029 | 44.004 | 0.89 | 26.544 | 1.08 | 28.115 | 1.12 | 26.900 | 1.07 |
| ctmark/consumer-typeset | 0.280 | 0.093 | 0.148 | 0.171 | 0.61 | 0.153 | 1.64 | 0.163 | 1.10 | 0.115 | 0.78 |
| ctmark-cxx/7zip | 18.049 | 11.840 | 9.728 | 17.030 | 0.94 | 13.016 | 1.10 | 12.542 | 1.29 | 13.357 | 1.37 |
| ctmark-cxx/Bullet | 24.121 | 3.867 | 3.848 | 22.098 | 0.92 | 5.439 | 1.41 | 4.733 | 1.23 | 5.005 | 1.30 |
| ctmark-cxx/kimwitu++ | 0.036 | 0.023 | 0.025 | 0.037 | 1.02 | 0.034 | 1.52 | 0.036 | 1.44 | 0.035 | 1.41 |
| ctmark-cxx/tramp3d-v4 | 33.766 | 0.368 | 0.220 | 26.066 | 0.77 | 0.302 | 0.82 | 0.317 | 1.44 | 0.308 | 1.40 |
| geometric mean (clang -O0 >= 50 ms) | | 0.280 x -O0 | 0.265 x -O0 | | 0.893 | | 1.127 | | 1.289 | | 1.202 |


10 tests in 3870s
