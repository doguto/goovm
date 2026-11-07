# goovm-llc correctness report

goovm-llc: `$C1/build-final2/tools/goovm-llc/goovm-llc`; variants: O0, cc

| corpus | tests | clang -O0 pass | excluded | O0 pass | O0 fail | O0 unsup | O0 fallback | cc pass | cc fail | cc unsup | cc fallback |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| ctmark | 6 | 6 | 0 | 6 | 0 | 0 | 0 | 6 | 0 | 0 | 0 |
| ctmark-cxx | 4 | 4 | 0 | 4 | 0 | 0 | 0 | 4 | 0 | 0 | 0 |

pass includes fallback; fallback counts tests in which at least one file was compiled by LLVM's code generator (goovm-llc --fallback).

## Run times (best of 3, seconds; ratio to clang -O0)

| test | clang -O0 | O0 | O0 / clang | cc | cc / clang |
|---|---:|---:|---:|---:|---:|
| ctmark/sqlite3 | 3.651 | 3.698 | 1.01 | 3.676 | 1.01 |
| ctmark/SPASS | 13.414 | 13.324 | 0.99 | 13.289 | 0.99 |
| ctmark/ClamAV | 0.164 | 0.163 | 0.99 | 0.161 | 0.98 |
| ctmark/lencod | 9.275 | 9.112 | 0.98 | 9.136 | 0.98 |
| ctmark/mafft | 32.351 | 31.308 | 0.97 | 31.113 | 0.96 |
| ctmark/consumer-typeset | 0.134 | 0.128 | 0.95 | 0.128 | 0.95 |
| ctmark-cxx/7zip | 12.296 | 11.751 | 0.96 | 11.900 | 0.97 |
| ctmark-cxx/Bullet | 16.587 | 16.071 | 0.97 | 16.119 | 0.97 |
| ctmark-cxx/kimwitu++ | 0.024 | 0.023 | 0.95 | 0.022 | 0.92 |
| ctmark-cxx/tramp3d-v4 | 16.949 | 17.327 | 1.02 | 17.178 | 1.01 |
| geometric mean (clang -O0 >= 50 ms) | | | 0.983 | | 0.981 |

