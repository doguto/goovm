# goovm-llc correctness report

goovm-llc: `<scratch>/work/a2/goovm-a1`; variants: O0

| corpus | tests | clang -O0 pass | excluded | O0 pass | O0 fail | O0 unsup | O0 fallback |
|---|---:|---:|---:|---:|---:|---:|---:|
| unittests | 1 | 1 | 0 | 1 | 0 | 0 | 0 |

pass includes fallback; fallback counts tests in which at least one file was compiled by LLVM's code generator (goovm-llc --fallback).

## Run times (best of 1, seconds; ratio to clang -O0)

| test | clang -O0 | O0 | O0 / clang |
|---|---:|---:|---:|
| unittests/Vector/build2 | 4.762 | 51.801 | 10.88 |
| geometric mean (clang -O0 >= 50 ms) | | | 10.878 |
