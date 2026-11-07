# goovm-llc correctness report

goovm-llc: `$C1/build-final2/tools/goovm-llc/goovm-llc`; variants: O0, g, mem2reg, cc, cc-g

| corpus | tests | clang -O0 pass | excluded | O0 pass | O0 fail | O0 unsup | O0 fallback | g pass | g fail | g unsup | g fallback | mem2reg pass | mem2reg fail | mem2reg unsup | mem2reg fallback | cc pass | cc fail | cc unsup | cc fallback | cc-g pass | cc-g fail | cc-g unsup | cc-g fallback |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| torture | 1427 | 1427 | 0 | 1427 | 0 | 0 | 0 | 1427 | 0 | 0 | 0 | 1427 | 0 | 0 | 0 | 1427 | 0 | 0 | 0 | 1427 | 0 | 0 | 0 |
| ieee | 57 | 57 | 0 | 57 | 0 | 0 | 0 | 57 | 0 | 0 | 0 | 57 | 0 | 0 | 0 | 57 | 0 | 0 | 0 | 57 | 0 | 0 | 0 |
| builtins | 54 | 48 | 6 | 48 | 0 | 0 | 0 | 48 | 0 | 0 | 0 | 48 | 0 | 0 | 0 | 48 | 0 | 0 | 0 | 48 | 0 | 0 | 0 |
| unittests | 129 | 129 | 0 | 129 | 0 | 0 | 0 | 129 | 0 | 0 | 0 | 129 | 0 | 0 | 0 | 129 | 0 | 0 | 0 | 129 | 0 | 0 | 0 |
| regression | 37 | 37 | 0 | 37 | 0 | 0 | 0 | 37 | 0 | 0 | 0 | 37 | 0 | 0 | 0 | 37 | 0 | 0 | 0 | 37 | 0 | 0 | 0 |
| benchmarks | 100 | 100 | 0 | 100 | 0 | 0 | 0 | 100 | 0 | 0 | 0 | 100 | 0 | 0 | 0 | 100 | 0 | 0 | 0 | 100 | 0 | 0 | 0 |

pass includes fallback; fallback counts tests in which at least one file was compiled by LLVM's code generator (goovm-llc --fallback).

llvm-dwarfdump --verify passed on 3788 objects (variants g / cc-g of the passing tests; a failure counts as a failed test).

## builtins: excluded (do not pass with clang-20 -O0)

- `builtins/abs-3` build: link failed:
- `builtins/fprintf` build: link failed:
- `builtins/fputs` build: link failed:
- `builtins/memops-asm` fail: exit status -6
- `builtins/printf` build: link failed:
- `builtins/strstr-asm` fail: exit status -6

