# goovm-llc correctness report

goovm-llc: `<scratch>/work/a2/goovm-final2`; variants: O0

| corpus | tests | clang -O0 pass | excluded | O0 pass | O0 fail | O0 unsup | O0 fallback |
|---|---:|---:|---:|---:|---:|---:|---:|
| unittests | 1 | 1 | 0 | 1 | 0 | 0 | 0 |

pass includes fallback; fallback counts tests in which at least one file was compiled by LLVM's code generator (goovm-llc --fallback).

## Run times (best of 3, seconds; ratio to clang -O0)

| test | clang -O0 | O0 | O0 / clang |
|---|---:|---:|---:|
| unittests/Vector/build2 | 4.757 | 5.484 | 1.15 |
| geometric mean (clang -O0 >= 50 ms) | | | 1.153 |
