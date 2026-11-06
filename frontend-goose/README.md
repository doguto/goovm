# goosecc: a C front end in Goose

`goosecc` is a C17 + GNU C front end written from scratch in
[Goose](https://github.com/aardappel/goose): a preprocessor, a parser and a
type checker that builds a fully typed AST (milestone B1; B2 lowers it to
GIR). It is checked against clang-20 on 2,357 C files from llvm-test-suite
and is 5-6 times faster than clang-20 with a sixth of its memory.

- [DESIGN.md](DESIGN.md): architecture, data structures, recursion under
  Goose's rules, and the AST contract for B2.
- [NOTES.md](NOTES.md): what writing it in Goose was like (errors, workarounds).

## Build

Needs the Goose compiler (commit 335fddc) and clang-20.

```bash
GOOSE=/path/to/goose GOOSE_STDLIB=/path/to/goose/stdlib frontend-goose/build.sh   # -> frontend-goose/build/goosecc
```

`build.sh [outdir]` translates `src/main.goose` to one C file with `goose
--standalone` and compiles it with `clang-20 -O2 -static` (`CFLAGS`, `LDFLAGS`
override; `LDFLAGS=` gives a dynamic executable). Without `GOOSE` and
`GOOSE_STDLIB` it uses the paths of the machine it was developed on.

## Use

```
goosecc -E [options] file.c [-o out]          preprocess (to stdout by default)
goosecc -fsyntax-only [options] file.c        parse and type-check
goosecc --layout-check [options] file.c -o check.c
                                              write the layout oracle (see Tests)
goosecc --dump-ast [options] file.c [-o out]  print the typed AST in clang's terms
```

Options are clang's: `-I`, `-iquote`, `-isystem`, `-idirafter`, `-nostdinc`,
`-D`, `-U`, `-include`, `-std=` (c89, gnu89, c99, gnu99, c11, gnu11, c17,
gnu17), `-O*`, `-pthread`, `-funsigned-char`, `-trigraphs`, `-Wno-return-type`
/ `-Wno-int-conversion` / `-Wno-implicit-function-declaration` /
`-Wno-implicit-int` (which downgrade clang-20's default errors), `-Wall`
(print warnings); the rest (`-c`, `-g`, `-f...`, `-m...`) are accepted and
ignored. `--time` prints the time spent in each phase. The target is
x86-64 Linux with clang-20's system include directories. Errors go to
stderr as `file:line:col: error: ...`, and the exit status is 1 if there
were any.

## Tests

The corpora are the C files of llvm-test-suite (`LLVM_TEST_SUITE`, default
`/home/user/llvm/llvm-test-suite`), each with the flags its CMake files use
(`tests/corpus.py`):

| corpus | files | what |
|---|---:|---|
| `torture` | 1708 | `SingleSource/Regression/C/gcc-c-torture/execute` (with `ieee/`, `builtins/`) |
| `unit` | 182 | `SingleSource/UnitTests` (without the non-x86 and AVX-512 vector tests) |
| `regress` | 37 | the rest of `SingleSource/Regression/C` |
| `bench` | 102 | `SingleSource/Benchmarks` |
| `ctmark` | 328 | the C files of the CTMark programs: sqlite3, ClamAV, SPASS, consumer-typeset, lencod, mafft, 7zip |

Each script takes `--corpus` (comma-separated), `-j` (parallel jobs) and
`--show N`, or file names followed by `--` and compiler flags.

```bash
cd frontend-goose
tests/cmp_E.py       --corpus torture,unit,regress,bench,ctmark -j 3   # -E token streams vs clang-20 -E
tests/cmp_syntax.py  --corpus torture,unit,regress,bench,ctmark -j 3   # no false errors; clang's errors found
tests/layout_check.py --corpus torture,unit,regress,bench,ctmark -j 3  # sizes/offsets/types vs clang-20
tests/cmp_ast.py     --corpus torture,unit,regress,bench,ctmark -j 3   # typed AST vs clang-20 -ast-dump=json
tests/bench.py       --corpus ctmark -n 3 --md bench.md                # speed and memory vs clang-20
tests/profile.sh -fsyntax-only file.c [flags]                          # perf profile of one compile
```

- `cmp_E.py` tokenizes both outputs and compares the token sequences
  (pragma lines included; line markers and whitespace are not compared).
- `cmp_syntax.py` runs both compilers with `-fsyntax-only`: every file clang
  accepts must be accepted (a *false error* otherwise), and every file clang
  rejects should be rejected.
- `layout_check.py` runs `goosecc --layout-check`, which writes a C file that
  `#include`s the translation unit and `_Static_assert`s goosecc's `sizeof`,
  `_Alignof` and member offsets of every file-scope struct, union and
  typedef, and goosecc's type of every file-scope object and function
  (through `__builtin_types_compatible_p`); clang-20 must compile it.
- `cmp_ast.py` walks goosecc's `--dump-ast` and clang's JSON AST of every
  function body and file-scope initializer in parallel: node kinds, types and
  cast kinds must agree, so the implicit conversions goosecc inserts are
  clang's.

The tables of clang-20 facts are generated, and the generators are kept:
`tools/gen_predef.py` (predefined macros, `__has_*` answers) and
`tools/gen_builtins.py` (builtin function types).

## Results

All five corpora, clang-20.1 and goosecc at the commit that adds this file:

| corpus | files | `-E` identical | clang-valid | accepted (false errors) | clang-invalid rejected | layout files / assertions | AST identical (bodies compared) |
|---|---:|---:|---:|---:|---:|---:|---:|
| torture | 1708 | 1708 | 1665 | 1665 (0) | 43 / 43 | 1665 / 78,173 | 1665 (7,449) |
| unit | 182 | 182 | 165 | 165 (0) | 17 / 17 | 165 / 72,194 | 165 (2,596) |
| regress | 37 | 37 | 35 | 35 (0) | 2 / 2 | 35 / 14,202 | 35 (544) |
| bench | 102 | 102 | 100 | 100 (0) | 2 / 2 | 100 / 95,677 | 100 (1,698) |
| ctmark | 328 | 328 | 324 | 324 (0) | 4 / 4 | 324 / 573,750 | 324 (29,070) |
| **total** | **2357** | **2357** | **2289** | **2289 (0)** | **68 / 68** | **2289 / 833,996** | **2289 (41,357)** |

"clang-invalid" files are those clang-20 rejects with the corpus flags
(GNU extensions clang does not implement, such as nested functions and
variable-length arrays in structs); goosecc rejects each of them too. The layout and AST checks cover the
clang-valid files.

### Speed

`tests/bench.py --corpus ctmark -n 3`: each command run alone, single
threaded, best of 3 wall-clock times, output to `/dev/null`; peak RSS is the
largest `ru_maxrss` of a run. The machine (4 cores, shared) is the same for
both compilers; goosecc is the static build from `build.sh`.

| mode | files | clang-20 total | goosecc total | speed-up | clang-20 peak RSS | goosecc peak RSS |
|---|---:|---:|---:|---:|---:|---:|
| `-E` | 328 | 9.33 s | 1.96 s | 4.77x | 84 MB | 15 MB |
| `-fsyntax-only` | 328 | 13.47 s | 2.23 s | 6.05x | 101 MB | 17 MB |

Per program (ms, sums over the files):

| program | files | `-E` clang | `-E` goosecc | x | syntax clang | syntax goosecc | x |
|---|---:|---:|---:|---:|---:|---:|---:|
| ClamAV | 103 | 2740 | 602 | 4.55 | 3642 | 646 | 5.64 |
| lencod (JM) | 55 | 1628 | 358 | 4.55 | 2413 | 409 | 5.90 |
| SPASS | 51 | 1723 | 376 | 4.59 | 2888 | 441 | 6.56 |
| sqlite3 | 2 | 92 | 30 | 3.04 | 286 | 44 | 6.44 |
| 7zip (C files) | 37 | 818 | 111 | 7.38 | 963 | 129 | 7.44 |
| consumer-typeset (MiBench) | 51 | 1397 | 288 | 4.85 | 1948 | 337 | 5.78 |
| mafft | 29 | 927 | 192 | 4.83 | 1334 | 223 | 5.99 |

`sqlite3.c` alone (2.8 MB, 276,543 tokens after preprocessing): `-E` 62.9 ms
vs 23.9 ms (2.6x), `-fsyntax-only` 240.9 ms vs 37.0 ms (6.5x). Over the 328
files the median speed-up is 4.7x for `-E` (2.6x to 12.6x) and 5.9x for
`-fsyntax-only` (4.5x to 11.3x). A run on an empty file takes 1.45 ms (clang:
20 ms), of which 0.9 ms is process creation and glibc start-up.

Where the time goes (`--time`, sqlite3.c): preprocessing 19.5 ms, parsing and
type checking 19 ms (200,834 nodes). The profile of `-E` is led by the lexer
(`lex_file_token` 19%), identifier interning (10%), the printer (inlined
into `main`, 9%) and the macro expander (8%); see NOTES.md, section 7, for
what was optimized.
