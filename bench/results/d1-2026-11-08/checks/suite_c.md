# goosecc correctness report

goosecc: `/tmp/claude-0/-home-user-goovm/593b2907-8413-508c-8bdb-c68ef6e66f6e/scratchpad/work/d1/checks2/goosecc`; variants: O0, g

| corpus | tests | clang -O0 pass | excluded | O0 pass | O0 fail | O0 error | g pass | g fail | g error |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| torture | 1427 | 1427 | 0 | 1427 | 0 | 0 | 1427 | 0 | 0 |
| ieee | 57 | 57 | 0 | 57 | 0 | 0 | 57 | 0 | 0 |
| builtins | 54 | 48 | 6 | 48 | 0 | 0 | 48 | 0 | 0 |
| unittests | 129 | 129 | 0 | 129 | 0 | 0 | 129 | 0 | 0 |
| regression | 37 | 37 | 0 | 37 | 0 | 0 | 37 | 0 | 0 |
| benchmarks | 100 | 100 | 0 | 100 | 0 | 0 | 100 | 0 | 0 |
| ctmark | 6 | 6 | 0 | 6 | 0 | 0 | 6 | 0 | 0 |

## builtins: excluded (do not pass with clang-20 -O0)

- `builtins/abs-3` build: link failed:
- `builtins/fprintf` build: link failed:
- `builtins/fputs` build: link failed:
- `builtins/memops-asm` fail: exit status -6
- `builtins/printf` build: link failed:
- `builtins/strstr-asm` fail: exit status -6

