# goosecc: a C compiler in Goose

`goosecc` is a C17 + GNU C compiler written from scratch in
[Goose](https://github.com/aardappel/goose). The front end (milestone B1)
is a preprocessor, a parser and a type checker that builds a fully typed
AST; the lowering (milestone B2) turns that AST into GIR version 2
([`../gir/README.md`](../gir/README.md)), and the Goose back-end
(`../backend-goose/`, imported as a package) compiles the GIR to an x86-64
ELF object in the same process. There is no LLVM anywhere: `goosecc -c
file.c -o file.o` produces objects that link with clang-20's and glibc.

- [DESIGN.md](DESIGN.md): architecture, data structures, recursion under
  Goose's rules, the AST contract, and the lowering to GIR (section 7:
  values, the SysV calling convention, globals, static data and
  relocations, builtins, inline assembly, debug locations).
- [NOTES.md](NOTES.md): what writing it in Goose was like (errors, workarounds),
  in section 10 what B3's speed work met in the language and runtime, and
  in section 11 what B4's header cache did.

Status (milestone B4):

- goosecc keeps the preprocessing of headers in a persistent cache
  (`src/hcache.goose`; DESIGN.md, section 10) and replays it exactly:
  with the cache cold, warm or disabled, `-E`, the diagnostics, the AST
  dump, the layout check and the objects (with and without `-g`) are
  byte-identical over the 2,357 corpus files (44,783 runs,
  `tests/cache_check.py`) and in 17 adversarial situations
  (`tests/cache_adversarial.py`); the oracles and the compiler test suite
  pass with a warm cache.
- Over CTMark's 316 C files, a warm cache takes `goosecc -c` from 1.93 s
  to 1.56 s, 1.22 times faster than tcc (1.90 s; faster on 277 of the
  316 files) and 10.6 times faster than `clang-20 -O0 -c` (16.5 s).
  Preprocessing goes from 900 to 518 ms. A first build with an empty
  cache already takes 1.75 s, since later files replay what earlier ones
  recorded; the cache then holds 116 MB.
- The target of 1.5 times tcc is not reached: what remains is the
  program's own code (parsing 279 ms, lowering and the back-end 136 ms
  each), the process (1.5 ms per file: start-up, the runtime's data
  stack regions, exit: 471 ms) and the replays themselves. On
  sqlite3.c, whose own code is most of it, tcc stays ahead (45.5 ms
  against 32.0 ms).

Status at milestone B3:

- `goosecc -c` is faster than TinyCC over the 284 C files of CTMark:
  1.74 s against tcc's 1.88 s (0.92 times its time; faster on 252 of the
  284 files), and 9.4 times faster than `clang-20 -O0 -c`; B2 took
  1.40 times tcc's time. On sqlite3.c alone tcc is still ahead (45.8 ms
  against 35.1 ms). DESIGN.md, section 9, has each optimization with its
  numbers; "Speed (B3)" below the measurements.
- The outputs did not change: `-E`, the diagnostics, the AST dump, the
  layout check and the objects (with and without `-g`) are byte-identical
  to B2's over the 2,357 corpus files, and the oracles below pass as
  before.

Status at milestone B2:

- Every test of the llvm-test-suite corpora that passes when built with
  `clang-20 -O0` passes when its C files are compiled by goosecc, with and
  without `-g`: gcc-c-torture (1,427 tests), its `ieee` (57) and
  `builtins` (48) parts, the SingleSource unit tests (129), regression
  tests (37) and benchmarks (100), and the six CTMark C programs (sqlite3,
  SPASS, ClamAV, lencod, mafft, consumer-typeset): 1,804 tests, 3,608 runs,
  no failure.
- `goosecc -c` is 6.05 times faster than `clang-20 -O0 -c` over the 284 C
  files of CTMark (10.3 times on sqlite3.c), with a peak RSS of 17-26 MB
  against clang's 103-137 MB; TinyCC is 1.4 times faster still. The
  generated code is the A1 back-end's (`backend-goose`): correct, but
  larger and slower than clang -O0's (sqlite3's `.text` is 3.5 times
  clang's).

## Build

Needs the Goose compiler (commit 335fddc) and clang-20.

```bash
GOOSE=/path/to/goose GOOSE_STDLIB=/path/to/goose/stdlib frontend-goose/build.sh   # -> frontend-goose/build/goosecc
```

`build.sh [outdir]` translates `src/main.goose` (which imports
`../backend-goose` as a package) to one C file with `goose --standalone
--stack-reserve 256M` and compiles it with `clang-20 -O2 -static`, linked
against musl when its static library is installed (`apt install
musl-dev`; `LIBC=glibc` links glibc instead, 0.6 ms slower per run in a
VM). `CFLAGS`, `LDFLAGS` and `GOOSE_FLAGS` override; `LDFLAGS=` gives a
dynamic glibc executable. Without `GOOSE` and `GOOSE_STDLIB` it uses the
paths of the machine it was developed on. `tools/gen_tables.py`
regenerates `src/tables_gen.goose` (B3's static name tables) after a
change to the generated predefined or builtin tables.

## Use

```
goosecc -c [options] file.c [-o file.o]       compile to an x86-64 ELF object (default: file.o)
goosecc --emit-gir [options] file.c [-o out]  print the GIR module (goovm-llc --dump-gir's format)
goosecc -E [options] file.c [-o out]          preprocess (to stdout by default)
goosecc -fsyntax-only [options] file.c        parse and type-check
goosecc --layout-check [options] file.c -o check.c
                                              write the layout oracle (see Tests)
goosecc --dump-ast [options] file.c [-o out]  print the typed AST in clang's terms
```

Options are clang's: `-I`, `-iquote`, `-isystem`, `-idirafter`, `-nostdinc`,
`-D`, `-U`, `-include`, `-std=` (c89, gnu89, c99, gnu99, c11, gnu11, c17,
gnu17), `-O*` (the code is always -O0's; `__OPTIMIZE__` follows the flag),
`-g` (debug locations in the GIR's tables; the A1 back-end does not write
DWARF yet), `-fPIC`/`-fpic` (preemptible definitions, GOT
references), `-fPIE`, `-fno-pic`, `-fcommon`/`-fno-common` (the default),
`-fno-builtin`, `-fno-builtin-NAME`, `-pthread`, `-funsigned-char`,
`-trigraphs`, `-w`, `-Wno-return-type` / `-Wno-int-conversion` /
`-Wno-implicit-function-declaration` / `-Wno-implicit-int` (which downgrade
clang-20's default errors), `-Wall` (print warnings); other `-f`, `-m` and
`-W` options are accepted and ignored, and anything else unknown is ignored
with a note. `-o -` writes to standard output. `--time` prints the time
spent in each phase:

```
$ goosecc -c --time sqlite3.c -o sqlite3.o
goosecc: preprocess 19718 us, parse+sema 16713 us, lowering 10615 us, back-end 7664 us, write 1326 us, total 56036 us; 200834 nodes, 104726 GIR insts, 1761120 bytes
```

The target is x86-64 Linux (SysV ABI, ELF, glibc) with clang-20's system
include directories. Errors go to stderr as `file:line:col: error: ...`,
and the exit status is 1 if there were any.

### The header cache (B4)

goosecc keeps the preprocessing of headers in a persistent cache and
replays it when nothing it depends on has changed; the outputs are
byte-identical with the cache cold, warm or disabled (DESIGN.md, section
10, has the design and the argument).

| option / variable | what |
|---|---|
| `-fno-header-cache` | neither read nor write the cache for this compile (`-fheader-cache`: the default) |
| `GOOSECC_CACHE=dir` | the cache directory (default `~/.cache/goosecc`; `off`, `none`, `0` or empty: no cache) |
| `GOOSECC_CACHE_SIZE=n` | its size limit, with K, M or G (default 2G); the least recently used files are deleted beyond it |
| `GOOSECC_CACHE_QUOTED=1` | every `"..."` include of the program's files is cached at every compile (the default caches `<...>` includes from the program's files, and the main file's `"..."` includes from its second compile on) |
| `--cache-stats` | print the lookups, hits, misses, recordings, bytes written, rejected entries, and where a replay's time went |
| `--pp-state-hash`, `--pp-state-hash=v` | print a checksum of the preprocessor's whole state (with `=v`, per array): what `tests/cache_check.py` compares |

```
$ goosecc -c --cache-stats libclamav_table.c ...
goosecc: header cache: 6 lookups, 6 hits, 0 misses; 0 recorded (0 bytes written), 0 too small, 0 not cacheable, 0 corrupt, 0 write errors, 0 volatile; replay 711 us (read 116, check 77, append 222, commit 70), saving 0 us
```

Headers changed less than 2 seconds before a compile are not recorded
(their stat cannot be trusted yet); units that print a diagnostic or
expand `__DATE__`/`__TIME__` never are. The cache tolerates concurrent
compiles (files are renamed into place, manifests appended to), corrupt
or truncated files (checksums; they are ignored or deleted) and files of
other builds of goosecc (never read).

## Tests

### Header cache tests (B4)

```bash
cd frontend-goose
tests/cache_check.py --corpus torture,unit,regress,bench,ctmark -j 2     # outputs off / cold / warm / warm2 / shared identical
GOOSECC_CACHE_QUOTED=1 tests/cache_check.py -j 2                        # the same with every "..." include a unit
tests/cache_adversarial.py                                              # 17 situations where a replay could go wrong
../tests/bench_hcache.py <CTMark compile_commands.json> --goosecc build/goosecc -n 5 --build --md bench.md
```

- `cache_check.py` compiles every corpus file in five modes (`-E`,
  `--dump-ast`, `--layout-check`, `-c`, `-c -g`) with the cache disabled,
  cold (an empty cache of the file's own), warm (the same cache again),
  warm2 (once more: it must record nothing) and shared (one cache for the
  whole run, written by the parallel workers at once); the output file,
  standard output, standard error with `--pp-state-hash=v` and the exit
  status of every run must be those of the run without the cache.
- `cache_adversarial.py` builds small trees of headers and checks, in
  each, that every compile with the cache gives what the same compile
  gives without it, and that the cache hits or misses as it should: a
  header edited keeping its size and mtime, a header edited within the
  racy window, different `-D`/`-U` and macro states, include order,
  `#include_next`, `__COUNTER__`, `#pragma once`/`push_macro`/`pack`/
  `poison`/`system_header`, `__DATE__`/`__TIME__`, a symlinked and a
  moved directory, relative includes from another directory, a deleted
  or newly shadowing header, eight concurrent writers, corrupted and
  truncated cache files, eviction (by last use), and the default policy.
- With a cache in `GOOSECC_CACHE`, the oracles below and
  `tests/suite_goosecc.py` and `tests/run.py` run with it warm; README's
  results say what they gave.

### Compiler tests (B2)

The lowering and the back-end are checked by running programs: every test
of the llvm-test-suite corpora that builds and passes with `clang-20 -O0`
must pass when each of its C files is compiled by `goosecc -c` (and with
`-g`) and the objects are linked by clang-20.

```bash
tests/suite_goosecc.py --goosecc frontend-goose/build/goosecc -j 3 --work /tmp/sgc \
    --corpus torture,ieee,builtins,unittests,regression,benchmarks,ctmark --variants O0,g --report report.md
tests/run.py --goosecc frontend-goose/build/goosecc -j 3          # the 44 programs of tests/c, with and without -g
frontend-goose/tests/abi_cross.py --seeds 20 -n 50               # SysV calling convention, mixed with clang objects
tests/bench_goosecc.py --goosecc frontend-goose/build/goosecc -n 3 --md bench.md   # speed vs clang-20 -O0 -c and tcc
frontend-goose/tests/cmp_dbg.py --goovm-llc build/tools/goovm-llc/goovm-llc file.c... [-- flags]   # -g locations vs clang's
```

`suite_goosecc.py` uses `suite.py`'s corpus definitions, flags, inputs and
verification (reference outputs compared with `fpcmp`, or exit status 0 for
gcc-c-torture); see `tests/README.md`. `abi_cross.py` generates random
signatures (structs and unions with scalars, arrays, bit-fields, nested
records and `packed`; every scalar type including `__int128`, `long
double` and `_Complex`; variadic callees reading with `va_arg`), compiles
the callees and the callers by both compilers, and checks that the four
mixes print the hashes of every argument and return value that the
all-clang build prints.

### Front-end oracles (B1)

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

### Header cache (B4)

**Speed.** `tests/bench_hcache.py -n 5 --build` at the commit that adds
these results: the 316 C files of CTMark (B3's 284 and 7zip's 32), with
the suite's flags, each compile run alone and single-threaded, the
variants interleaved file by file, best of 5 wall-clock times. `off` is
`-fno-header-cache`; `cold` a compile with an empty cache (it records
the `<...>` includes); `warm` a compile with the cache that earlier
compiles filled (one cache for the whole run, so the later files of a
program also find the variants the earlier ones recorded). tcc is
Ubuntu's 0.9.27. The load average was 0.9 to 1.4 (another agent's test
runs). The raw data, per file: `../bench/results/b4-2026-11-07/hcache.{md,json}`.

| program | files | goosecc off | cold | warm | tcc -c | clang-20 -O0 -c | warm: speed-up over off | over tcc |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 7zip | 32 | 110 ms | 127 ms | 98 ms | 96 ms | 1056 ms | 1.12x | 0.98x |
| ClamAV | 98 | 538 ms | 742 ms | 461 ms | 533 ms | 4287 ms | 1.17x | 1.16x |
| SPASS | 51 | 368 ms | 458 ms | 273 ms | 380 ms | 3332 ms | 1.35x | 1.39x |
| consumer-typeset | 51 | 302 ms | 354 ms | 241 ms | 302 ms | 2618 ms | 1.25x | 1.25x |
| lencod | 55 | 360 ms | 453 ms | 291 ms | 346 ms | 3017 ms | 1.23x | 1.19x |
| mafft | 27 | 198 ms | 253 ms | 141 ms | 210 ms | 1618 ms | 1.41x | 1.49x |
| sqlite3 | 2 | 54 ms | 57 ms | 52 ms | 38 ms | 594 ms | 1.04x | 0.74x |
| **total** | 316 | 1931 ms | 2444 ms | **1558 ms** | 1904 ms | 16522 ms | **1.24x** | **1.22x** |

(Speed-up: how many times faster warm is.) Without 7zip, B3's 284
files: off 1821 ms, warm 1460 ms, tcc 1808 ms, clang 15466 ms. Per file,
warm is a median 1.21 times faster than tcc (0.70 to 1.97; faster on 277
files) and 1.23 times faster than off (0.94 to 1.58), and a cold compile
takes a median 1.27 times off's time (at most 1.57: recording costs 2-3
times preprocessing the headers).

Builds of all 316 files in order, one run each: without the cache
1.93 s; with one cache that starts empty, the first build 1.75 s (later
files replay what earlier ones recorded), the second 1.75 s (the main
files' `"..."` includes recorded too), the third 1.51 s. The cache then
holds 1,105 files, 116 MB.

goosecc's phases (`--time`, one run per file, sums in ms):

| variant | preprocess | parse + sema | lowering | back-end | write | in phases | the rest of the wall time |
|---|---:|---:|---:|---:|---:|---:|---:|
| off | 900 | 274 | 139 | 137 | 19 | 1468 | 463 |
| cold | 1422 | 268 | 132 | 134 | 16 | 1972 | |
| warm | 518 | 279 | 136 | 136 | 18 | 1087 | 471 |

sqlite3.c alone (ms): off 46.5, warm 45.5, tcc 32.0, clang 526.6; warm:
preprocessing 13.8 (off 14.8), parsing 12.5, lowering 9.4, the back-end
9.2, writing 0.2. Its 250,000 lines are its own: the cache saves only
its few system headers.

Where the warm time goes: the rest of the wall time, 1.5 ms per file, is
the process (exec, the Goose runtime's set-up of its 314 data stack
regions, the options, exit; the predefined macros are in "preprocess";
an empty file compiles in 1.35 ms, as fast as tcc); then parsing and type checking the headers' declarations again,
which the cache does not save (DESIGN.md, 10.7); of the 518 ms of
preprocessing, about 300 ms are replays (reading manifests, checking
heads with a stat per file, the blob's checksum, copying the effects
into the arrays) and the rest the main files' own text. Reaching 1.5
times tcc would take about 300 ms off these 1,558: all the replays, or
the start-up and the parsing of the headers together.

**Exactness.** `tests/cache_check.py` over the 2,357 corpus files, at
`-j 2`: per file 19 runs (`-c` and `-E` off, cold, warm, warm2 and
shared; `--dump-ast`, `--layout-check` and `-c -g` off, warm2 from the
cache `-c` filled, and shared), every one with the same output, standard
output, standard error (with the preprocessor's state checksum) and exit
status as the run without the cache:

| corpus | files | identical | runs | lookups | hits | lookups, every `"..."` a unit | hits |
|---|---:|---:|---:|---:|---:|---:|---:|
| torture | 1708 | 1708 | 32452 | 4730 | 3739 | 4934 | 3819 |
| unit | 182 | 182 | 3458 | 4109 | 3175 | 4088 | 3078 |
| regress | 37 | 37 | 703 | 700 | 586 | 700 | 586 |
| bench | 102 | 102 | 1938 | 5810 | 3592 | 6064 | 3604 |
| ctmark | 328 | 328 | 6232 | 34129 | 21820 | 36435 | 20134 |
| **total** | 2357 | 2357 | 44783 | 49478 | 32912 | 52221 | 31221 |

The last two columns are a second run with `GOOSECC_CACHE_QUOTED=1`
(also 2,357 of 2,357 identical). In both, no warm2 run recorded
anything.

With one cache filled by `-E` and `-fsyntax-only` compiles of every file
(359 MB), the front-end oracles give what they gave in B3: `cmp_E.py`
2,357 of 2,357 token streams identical to clang's, `cmp_syntax.py` no
false error and every clang error found, `layout_check.py` 2,289 files
and 834,000 assertions without a mismatch, `cmp_ast.py` 2,289 files and
41,357 functions without a difference. With one cache for the whole
compiler test suite: `tests/run.py` 98 of 98 (cold, then warm), and
`tests/suite_goosecc.py` (all corpora, `O0` and `g`) twice, the second
time with everything recorded by the first: 1,804 tests, 3,608 runs,
no failure, each time.

`tests/cache_adversarial.py`: 17 of 17 (the situations listed under
Tests).

### Speed (B3)

`tests/bench_goosecc.py -n 5` at the commit that adds these results:
every C file of the six CTMark programs with the suite's flags, each
compile run alone and single-threaded, best of 5 wall-clock times, the
object written to a scratch file. goosecc is `build.sh`'s static musl
build; tcc is Ubuntu's 0.9.27. The machine (4 cores) was shared with
another agent's test runs: the load average was 5.7 at the start and 6.6
at the end, so absolute times carry noise; the ratios are what matters.

| program | files | clang-20 -O0 -c | goosecc -c | tcc -c | goosecc / tcc | speed-up over clang | goosecc peak RSS |
|---|---:|---:|---:|---:|---:|---:|---:|
| sqlite3 | 2 | 697 ms | 53 ms | 42 ms | 1.27 | 13.2x | 25 MB |
| SPASS | 51 | 3627 ms | 357 ms | 406 ms | 0.88 | 10.2x | 17 MB |
| ClamAV | 98 | 4410 ms | 510 ms | 547 ms | 0.93 | 8.6x | 17 MB |
| lencod | 55 | 3125 ms | 350 ms | 362 ms | 0.97 | 8.9x | 17 MB |
| mafft | 27 | 1669 ms | 183 ms | 214 ms | 0.86 | 9.1x | 17 MB |
| consumer-typeset | 51 | 2768 ms | 286 ms | 314 ms | 0.91 | 9.7x | 17 MB |
| **total** | 284 | 16.30 s | 1.74 s | 1.88 s | **0.92** | 9.4x | 25 MB |

Before and after (B2 from the B2 section below, measured at another
time; the second pair from one interleaved run of both binaries and tcc,
best of 3 per file, load 3 to 7, DESIGN.md section 9):

| | goosecc B2 | goosecc B3 | tcc | B2 / tcc | B3 / tcc |
|---|---:|---:|---:|---:|---:|
| CTMark, `bench_goosecc.py` | 2867 ms | 1738 ms | 2042 / 1884 ms | 1.40 | 0.92 |
| CTMark, one interleaved run | 2614 ms | 1710 ms | 1920 ms | 1.36 | 0.89 |
| sqlite3.c, interleaved | 55.9 ms | 44.0 ms | 35.8 ms | 1.56 | 1.23 |
| a one-line file | 2.7 ms | 1.3-1.4 ms | 1.5 ms | | |

Per file, goosecc takes a median 0.91 times tcc's time (0.69 to 1.62)
and is faster on 252 of the 284 files; the median speed-up over clang is
9.0x (4.8x to 15.9x). tcc stays ahead on 32 files, by more than 20% on
five (lencod's `symbol.c` and `sei.c`, sqlite3.c, ClamAV's `spin.c` and
`filetypes.c`). On sqlite3.c, with much code and few headers, goosecc's
cost of storing every token and an AST before generating code shows
(DESIGN.md, 9.5); on CTMark's many header-heavy files its start-up and
preprocessor now cost less than tcc's.

Where the time goes (`--time`, sum over the 284 files): preprocessing
880 ms, parsing and type checking 264 ms, lowering 122 ms, the back-end
94 ms, writing 18 ms; the rest of the 1.74 s is process start-up and exit.
sqlite3.c (45.8 ms): preprocessing 14.9 ms, parsing 12.0 ms, lowering
9.4 ms, the back-end 7.1 ms, writing 0.4 ms.

### Compiler (B2)

`tests/suite_goosecc.py`, all corpora, variants `O0` and `g`, goosecc at
the commit that adds these results (clang-20.1 for the baseline and for
linking):

| corpus | tests | clang -O0 pass | excluded | O0 pass | O0 fail | O0 error | g pass | g fail | g error |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| torture | 1427 | 1427 | 0 | 1427 | 0 | 0 | 1427 | 0 | 0 |
| ieee | 57 | 57 | 0 | 57 | 0 | 0 | 57 | 0 | 0 |
| builtins | 54 | 48 | 6 | 48 | 0 | 0 | 48 | 0 | 0 |
| unittests | 129 | 129 | 0 | 129 | 0 | 0 | 129 | 0 | 0 |
| regression | 37 | 37 | 0 | 37 | 0 | 0 | 37 | 0 | 0 |
| benchmarks | 100 | 100 | 0 | 100 | 0 | 0 | 100 | 0 | 0 |
| ctmark | 6 | 6 | 0 | 6 | 0 | 0 | 6 | 0 | 0 |
| **total** | 1810 | 1804 | 6 | 1804 | 0 | 0 | 1804 | 0 | 0 |

"excluded" are the tests that do not build or pass with plain clang-20
-O0 (6 of gcc's `builtins` tests: four do not link and two abort, as in
`suite.py`); everything else passes in both variants, 3,608 runs. The run
takes 45 minutes at `-j 3`, mostly the Polybench kernels, whose code from
the A1 back-end runs several times slower than clang -O0's.

- `tests/run.py --goosecc`: the 44 programs of `tests/c`, 88 of 88 runs
  pass (with and without `-g`).
- `frontend-goose/tests/abi_cross.py --seeds 20 -n 50`: 20 of 20 seeds
  pass (1,000 random signatures, each called across the four mixes of
  clang and goosecc objects); 63 further seeds of 40-60 functions were
  run during development.
- `frontend-goose/tests/cmp_dbg.py` (debug locations against clang-20's
  through `goovm-llc --dump-gir`): of sqlite3.c's 98,000 aligned
  instructions, 99.3% have clang's line and 98.6% its line and column; of
  the 16,700 of the Misc, Stanford and Shootout benchmarks, 99.6% and
  97.0% (DESIGN.md, 7.7).
- sqlite3.c compiled by goosecc defines the same functions and data
  objects as clang's object; its `.text` is 1.52 MB against clang's
  0.43 MB (the A1 back-end keeps every value in memory), `.data` and
  `.bss` are within a few bytes of clang's.

### Speed of `goosecc -c` (B2)

`tests/bench_goosecc.py -n 3`: every C file of the six CTMark programs
with the suite's flags, each compile run alone and single-threaded, best
of 3 wall-clock times, the object written to a scratch file; peak RSS is
the largest `ru_maxrss` of a run. goosecc is the static build of
`build.sh`; TinyCC is Ubuntu's 0.9.27 (`tcc -c` with the same `-D`/`-I`
flags; it compiles all 284 files). The machine (4 cores) was shared with
another agent's test runs, so absolute times carry some noise.

| program | files | clang-20 -O0 -c | goosecc -c | speed-up | clang peak RSS | goosecc peak RSS |
|---|---:|---:|---:|---:|---:|---:|
| sqlite3 | 2 | 697 ms | 71 ms | 9.80x | 134 MB | 26 MB |
| SPASS | 51 | 3805 ms | 591 ms | 6.44x | 103 MB | 17 MB |
| ClamAV | 98 | 4800 ms | 877 ms | 5.47x | 106 MB | 17 MB |
| lencod | 55 | 3382 ms | 561 ms | 6.02x | 104 MB | 17 MB |
| mafft | 27 | 1776 ms | 292 ms | 6.09x | 104 MB | 17 MB |
| consumer-typeset | 51 | 2888 ms | 475 ms | 6.08x | 111 MB | 17 MB |
| **total** | 284 | 17.35 s | 2.87 s | 6.05x | 134 MB | 26 MB |

On the files TinyCC compiles (`tcc -c`, same -D/-I flags):

| program | files | clang-20 -O0 -c | goosecc -c | tcc -c | goosecc / tcc | tcc peak RSS |
|---|---:|---:|---:|---:|---:|---:|
| sqlite3 | 2 | 697 ms | 71 ms | 45 ms | 1.59 | 17 MB |
| SPASS | 51 | 3805 ms | 591 ms | 447 ms | 1.32 | 17 MB |
| ClamAV | 98 | 4800 ms | 877 ms | 599 ms | 1.47 | 17 MB |
| lencod | 55 | 3382 ms | 561 ms | 390 ms | 1.44 | 17 MB |
| mafft | 27 | 1776 ms | 292 ms | 226 ms | 1.29 | 17 MB |
| consumer-typeset | 51 | 2888 ms | 475 ms | 336 ms | 1.41 | 17 MB |
| **total** | 284 | 17348 ms | 2867 ms | 2042 ms | 1.40 | 17 MB |

goosecc phases (sum of one --time run per file):

| program | preprocess | parse+sema | lowering | back-end | write |
|---|---:|---:|---:|---:|---:|
| sqlite3 | 24 ms | 18 ms | 12 ms | 8 ms | 2 ms |
| SPASS | 287 ms | 89 ms | 42 ms | 17 ms | 23 ms |
| ClamAV | 423 ms | 94 ms | 58 ms | 25 ms | 40 ms |
| lencod | 256 ms | 85 ms | 35 ms | 23 ms | 23 ms |
| mafft | 144 ms | 44 ms | 15 ms | 11 ms | 11 ms |
| consumer-typeset | 207 ms | 70 ms | 31 ms | 26 ms | 23 ms |
| **total** | 1341 ms | 401 ms | 192 ms | 110 ms | 122 ms |

`sqlite3.c` alone (2.8 MB; 276,543 tokens after preprocessing, 200,834
AST nodes, 104,726 GIR instructions): clang-20 -O0 -c 624 ms, goosecc
60.4 ms (10.3x), tcc 37.6 ms. goosecc's time there is preprocessing 19.7 ms, parsing and type
checking 16.7 ms, lowering 10.6 ms, the back-end 7.7 ms and writing the
1.8 MB object 1.3 ms. Over the 284 files the median speed-up over clang
is 5.7x (4.3x to 10.3x) and goosecc takes a median 1.44 times tcc's time
(0.95 to 2.3). The phases add up to three quarters of the total: the rest
is process start-up and exit, about 2.5 ms per file, which matters for
CTMark's many small files. Lowering and code generation together are 10%
of goosecc's time; the preprocessor (B1) is 47%, because every file
re-reads the glibc headers.

Memory: the largest peak RSS of a goosecc run is 26 MB (sqlite3.c; 17 MB
for every other file), against 103-137 MB for clang-20 and 17 MB for
tcc. goosecc never frees; its tables grow by pages (DESIGN.md, 2).

### Front end (B1)

All five corpora, clang-20.1 and goosecc (B1; rerun with the B2 compiler, every number is unchanged):

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

### Front-end speed (B1)

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
