# goovm-llc correctness report

goovm-llc: `<scratch>/work/a2/goovm-a1`; variants: O0

| corpus | tests | clang -O0 pass | excluded | O0 pass | O0 fail | O0 unsup | O0 fallback |
|---|---:|---:|---:|---:|---:|---:|---:|
| ctmark | 6 | 6 | 0 | 6 | 0 | 0 | 0 |

pass includes fallback; fallback counts tests in which at least one file was compiled by LLVM's code generator (goovm-llc --fallback).

## Run times (best of 3, seconds; ratio to clang -O0)

| test | clang -O0 | O0 | O0 / clang |
|---|---:|---:|---:|
| ctmark/sqlite3 | 3.745 | 14.803 | 3.95 |
| ctmark/SPASS | 13.749 | 27.495 | 2.00 |
| ctmark/ClamAV | 0.170 | 0.330 | 1.95 |
| ctmark/lencod | 9.562 | 30.735 | 3.21 |
| ctmark/mafft | 33.270 | 70.665 | 2.12 |
| ctmark/consumer-typeset | 0.138 | 0.608 | 4.40 |
| geometric mean (clang -O0 >= 50 ms) | | | 2.780 |
