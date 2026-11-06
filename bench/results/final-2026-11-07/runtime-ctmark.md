# goovm-llc correctness report

goovm-llc: `/tmp/claude-0/-home-user-goovm/593b2907-8413-508c-8bdb-c68ef6e66f6e/scratchpad/work/main-build/tools/goovm-llc/goovm-llc`; variants: O0, cc

| corpus | tests | clang -O0 pass | excluded | O0 pass | O0 fail | O0 unsup | O0 fallback | cc pass | cc fail | cc unsup | cc fallback |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| ctmark | 6 | 6 | 0 | 6 | 0 | 0 | 0 | 6 | 0 | 0 | 0 |
| ctmark-cxx | 4 | 4 | 0 | 4 | 0 | 0 | 0 | 4 | 0 | 0 | 0 |

pass includes fallback; fallback counts tests in which at least one file was compiled by LLVM's code generator (goovm-llc --fallback).

## Run times (best of 3, seconds; ratio to clang -O0)

| test | clang -O0 | O0 | O0 / clang | cc | cc / clang |
|---|---:|---:|---:|---:|---:|
| ctmark/sqlite3 | 3.711 | 3.854 | 1.04 | 3.882 | 1.05 |
| ctmark/SPASS | 13.789 | 13.823 | 1.00 | 13.968 | 1.01 |
| ctmark/ClamAV | 0.163 | 0.157 | 0.96 | 0.157 | 0.97 |
| ctmark/lencod | 9.657 | 9.387 | 0.97 | 9.347 | 0.97 |
| ctmark/mafft | 32.566 | 32.339 | 0.99 | 32.161 | 0.99 |
| ctmark/consumer-typeset | 0.134 | 0.128 | 0.96 | 0.127 | 0.95 |
| ctmark-cxx/7zip | 11.821 | 11.535 | 0.98 | 11.485 | 0.97 |
| ctmark-cxx/Bullet | 16.788 | 29.118 | 1.73 | 28.859 | 1.72 |
| ctmark-cxx/kimwitu++ | 0.023 | 0.023 | 0.99 | 0.023 | 0.98 |
| ctmark-cxx/tramp3d-v4 | 16.590 | 20.171 | 1.22 | 20.264 | 1.22 |
| geometric mean (clang -O0 >= 50 ms) | | | 1.075 | | 1.074 |

