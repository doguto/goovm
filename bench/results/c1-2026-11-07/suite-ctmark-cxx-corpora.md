# goovm-llc correctness report

goovm-llc: `$C1/build-final2/tools/goovm-llc/goovm-llc`; variants: O0, g, mem2reg, cc, cc-g

| corpus | tests | clang -O0 pass | excluded | O0 pass | O0 fail | O0 unsup | O0 fallback | g pass | g fail | g unsup | g fallback | mem2reg pass | mem2reg fail | mem2reg unsup | mem2reg fallback | cc pass | cc fail | cc unsup | cc fallback | cc-g pass | cc-g fail | cc-g unsup | cc-g fallback |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| ctmark | 6 | 6 | 0 | 6 | 0 | 0 | 0 | 6 | 0 | 0 | 0 | 6 | 0 | 0 | 0 | 6 | 0 | 0 | 0 | 6 | 0 | 0 | 0 |
| unittests-cxx | 35 | 35 | 0 | 35 | 0 | 0 | 0 | 35 | 0 | 0 | 0 | 35 | 0 | 0 | 0 | 35 | 0 | 0 | 0 | 35 | 0 | 0 | 0 |
| regression-cxx | 31 | 31 | 0 | 31 | 0 | 0 | 0 | 31 | 0 | 0 | 0 | 31 | 0 | 0 | 0 | 31 | 0 | 0 | 0 | 31 | 0 | 0 | 0 |
| benchmarks-cxx | 41 | 41 | 0 | 41 | 0 | 0 | 0 | 41 | 0 | 0 | 0 | 41 | 0 | 0 | 0 | 41 | 0 | 0 | 0 | 41 | 0 | 0 | 0 |
| ctmark-cxx | 4 | 4 | 0 | 4 | 0 | 0 | 0 | 4 | 0 | 0 | 0 | 4 | 0 | 0 | 0 | 4 | 0 | 0 | 0 | 4 | 0 | 0 | 0 |

pass includes fallback; fallback counts tests in which at least one file was compiled by LLVM's code generator (goovm-llc --fallback).

llvm-dwarfdump --verify passed on 1478 objects (variants g / cc-g of the passing tests; a failure counts as a failed test).

