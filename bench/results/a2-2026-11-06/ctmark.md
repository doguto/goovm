# goovm-llc correctness report

goovm-llc: `<scratch>/work/a2/goovm-final2`; variants: O0

| corpus | tests | clang -O0 pass | excluded | O0 pass | O0 fail | O0 unsup | O0 fallback |
|---|---:|---:|---:|---:|---:|---:|---:|
| ctmark | 6 | 6 | 0 | 6 | 0 | 0 | 0 |

pass includes fallback; fallback counts tests in which at least one file was compiled by LLVM's code generator (goovm-llc --fallback).

## Run times (best of 5, seconds; ratio to clang -O0)

| test | clang -O0 | O0 | O0 / clang |
|---|---:|---:|---:|
| ctmark/sqlite3 | 3.669 | 3.694 | 1.01 |
| ctmark/SPASS | 13.616 | 13.674 | 1.00 |
| ctmark/ClamAV | 0.162 | 0.159 | 0.98 |
| ctmark/lencod | 9.518 | 9.432 | 0.99 |
| ctmark/mafft | 33.314 | 32.933 | 0.99 |
| ctmark/consumer-typeset | 0.133 | 0.126 | 0.95 |
| geometric mean (clang -O0 >= 50 ms) | | | 0.986 |
