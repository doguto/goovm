# goovm-llc correctness report

goovm-llc: `$C1/build-base/tools/goovm-llc/goovm-llc`; variants: O0

| corpus | tests | clang -O0 pass | excluded | O0 pass | O0 fail | O0 unsup | O0 fallback |
|---|---:|---:|---:|---:|---:|---:|---:|
| ctmark | 6 | 6 | 0 | 6 | 0 | 0 | 0 |
| ctmark-cxx | 4 | 4 | 0 | 4 | 0 | 0 | 0 |

pass includes fallback; fallback counts tests in which at least one file was compiled by LLVM's code generator (goovm-llc --fallback).

## Run times (best of 3, seconds; ratio to clang -O0)

| test | clang -O0 | O0 | O0 / clang |
|---|---:|---:|---:|
| ctmark/sqlite3 | 3.659 | 3.756 | 1.03 |
| ctmark/SPASS | 13.526 | 13.924 | 1.03 |
| ctmark/ClamAV | 0.161 | 0.156 | 0.97 |
| ctmark/lencod | 9.305 | 9.365 | 1.01 |
| ctmark/mafft | 32.069 | 30.870 | 0.96 |
| ctmark/consumer-typeset | 0.133 | 0.125 | 0.94 |
| ctmark-cxx/7zip | 12.080 | 11.794 | 0.98 |
| ctmark-cxx/Bullet | 16.533 | 27.933 | 1.69 |
| ctmark-cxx/kimwitu++ | 0.023 | 0.022 | 0.98 |
| ctmark-cxx/tramp3d-v4 | 16.441 | 19.529 | 1.19 |
| geometric mean (clang -O0 >= 50 ms) | | | 1.070 |

