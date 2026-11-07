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
  relocations, builtins, inline assembly, debug locations), the header
  cache (section 10) and the DWARF debug information (section 11).
- [NOTES.md](NOTES.md): what writing it in Goose was like (errors, workarounds),
  in section 10 what B3's speed work met in the language and runtime, in
  section 11 what B4's header cache did, and in section 12 B5's debug
  information.

Status (milestone G1; DESIGN.md, section 12; measurements in
[`../bench/results/g1-2026-11-07/`](../bench/results/g1-2026-11-07/)):

- **Start-up.** A compile of a one-line file takes 0.65 ms (1.19 ms
  before; measured on a quiet machine, `exec` and exit included). Half of
  the old time was the Goose runtime mapping 420 data stacks one by one;
  `build.sh` now patches the runtime embedded in the generated C so that
  they are slots of one reservation, enabled on first touch, with the 146
  regions every compile uses packed and enabled at start-up
  ([runtime-patches/README.md](runtime-patches/README.md), with a
  proposal for the Goose authors).
- **Parse cache.** The parser's state after a file's leading `#include`s
  is saved next to the header cache and replayed by later compiles that
  start with the same includes (src/pcache.goose). Over CTMark,
  parse+sema with a warm cache went from 218 to 153 ms.
- **Speed** (CTMark's 316 C files, best of 3, the machine shared with
  another job): warm cache 1.19 s, **1.35 times faster than tcc** (1.61 s)
  and 11.3 times faster than `clang-20 -O0` (13.5 s); without the cache
  1.48 s, faster than tcc. Before G1, in the same run: 1.33 s warm, 1.60 s
  without the cache. **sqlite3.c** alone stays slower than tcc: 34 ms
  without the cache (best of 9) against tcc's 24.5 ms; it is nearly all
  its own code, which no cache helps.
- **clang's -O0 code generation**: reads of `const` objects folded (with
  `DW_AT_const_value` DIEs), address differences, `strlen`/`memchr`,
  `__builtin_constant_p`, GNU-mode array bounds, NRVO, `nodebug`
  functions, and the in-place expansion of `always_inline` `nodebug`
  functions (the x86 intrinsics). `tests/dwarf_diff.py`: 2,268 of the
  2,289 files both compile have clang's DWARF (2,232 before), 12 differ
  only in a frame-location form, 9 differ (44 before: 8 are `always_inline`
  functions with debug information, which goosecc still calls); CTMark: 323
  of 324 identical. gdb: 46 of B5's 79 programs give identical sessions
  (45 before).
- **Exactness.** With the parse cache, `cache_check.py` (2,357 files,
  44,783 runs, now comparing the whole parser state too), `pcache_check.py`
  (replays into a padded main file: 9,428 runs, 2,960 replays) and the 17
  adversarial tests pass; the compiler suite (1,804 tests, `-O0` and
  `-g`), `tests/run.py --goosecc` (108/108) and the four front-end oracles
  pass. Against the build before G1, `-E` is unchanged everywhere; the AST
  dump and the layout check differ in 3 files (GNU-mode array bounds that
  clang folds); 113 objects differ, every one from an intended change
  (`checks/attrib.txt` attributes each to its step: `noinit` 1, const
  folding 74, `strlen`/NRVO/`__builtin_constant_p`/pointer reads 34, the
  inlining of intrinsics 4).
- `noinit` compiles (clang-20 ignores it on x86-64); `tests/c/52` and `53`
  are new.

Status at milestone B5:

- `goosecc -g` writes the DWARF 5 of `clang-20 -O0 -g`: variables,
  parameters, types (bit-fields, VLAs, enums, function pointers, vectors,
  complex, `_Atomic`, typedef names as written), lexical scopes, labels,
  global and static local variables, string literals (DESIGN.md, section
  11). Of the 2,288 corpus files both compilers compile, 2,231 (97.5%)
  have the same normalized `llvm-dwarfdump --debug-info` as clang's (316
  of CTMark's 324), 13 more differ only in how a frame location is
  written, and the 44 others where goosecc's code differs from clang's
  (folded `const` reads, `always_inline`); `llvm-dwarfdump --verify`
  passes on every object. In gdb, at the 6,859 stops where both builds
  stop at the same place, `ptype` agrees for every variable but one and
  `print` for 98.9% of the values; 45 of 79 whole sessions are identical
  (the others stop at other lines, as before B5).
- `-g` costs goosecc 25% on CTMark (1.73 → 2.17 s); `goosecc -g` is 9.1
  times faster than `clang-20 -O0 -g`. The back-end, GIR and `tools/` did
  not change.
- `__PRETTY_FUNCTION__` is now clang's string (it was the bare name).

Status at milestone B4:

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
`-g` (DWARF 5 as `clang-20 -O0 -g` writes it: line table, variables,
parameters, types, scopes, labels; DESIGN.md, section 11), `-fPIC`/`-fpic` (preemptible definitions, GOT
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
| `GOOSECC_CACHE=dir` | the cache directory (default `~/.cache/goosecc`; `off`, `none`, `0` or empty: no cache; a relative path is taken from each compile's working directory) |
| `GOOSECC_CACHE_SIZE=n` | its size limit, with K, M or G (default 2G); the least recently used files are deleted beyond it |
| `GOOSECC_CACHE_QUOTED=1` | every `"..."` include of the program's files is cached at every compile (the default caches `<...>` includes from the program's files, and the main file's `"..."` includes from its second compile on) |
| `--cache-stats` | print the lookups, hits, misses, recordings, bytes written, rejected entries, and where a replay's time went |
| `--pp-state-hash`, `--pp-state-hash=v` | print a checksum of the preprocessor's whole state (with `=v`, per array): what `tests/cache_check.py` compares |

```
$ goosecc -c --cache-stats libclamav_table.c ...
goosecc: header cache: 6 lookups, 6 hits, 0 misses; 0 recorded (0 bytes written), 0 too small, 0 not cacheable, 0 corrupt, 0 write errors, 0 volatile; replay 711 us (read 116, check 77, append 222, commit 70), saving 0 us
```

The same directory holds the **parse cache** (G1; DESIGN.md, section
12.2): the parser's state after a file's leading `#include`s, replayed
by later compiles that start with the same includes (the same headers,
options and defines). It is on and off with the header cache;
`--cache-stats` reports its lookups, hits and where a replay's time went
(`; parse cache: 1 lookups, 1 hits, 0 recorded, ...`).

Headers changed less than 2 seconds before a compile are not recorded
(their stat cannot be trusted yet); units that print a diagnostic or
expand `__DATE__`/`__TIME__` never are. The cache tolerates concurrent
compiles (files are renamed into place, manifests appended to), corrupt
or truncated files (checksums; they are ignored or deleted) and files of
other builds of goosecc (never read). The checksums guard against
damage, not against tampering: whoever can write to the cache directory
can change what goosecc compiles, so it should be private (as
`~/.cache/goosecc` is).

## Tests

### Parse cache and object tests (G1)

```bash
frontend-goose/tests/cache_check.py --goosecc frontend-goose/build/goosecc -j 2    # outputs and the whole parser state, cache off/cold/warm/shared
frontend-goose/tests/pcache_check.py --goosecc frontend-goose/build/goosecc -j 2   # replays into a padded main file (every offset moves)
frontend-goose/tests/cmp_bins.py --ref old/goosecc --save ref.json                  # record a build's outputs (checksums)
frontend-goose/tests/cmp_bins.py --load ref.json --goosecc frontend-goose/build/goosecc --list diff.json
```

- `cache_check.py` (B4's) now compares the parser's state too:
  `--pp-state-hash` hashes every parser table after parsing, so a replay
  that left one word different in any table fails.
- `pcache_check.py` records each file's parse cache entry, then compiles
  the file again with `GOOSECC_TEST_MAIN_PAD=777` (the main file read with
  777 bytes of blank lines in front, which moves every source offset of
  the main file and everything after it) from the entry and without the
  cache: `-c`, `-c -g`, `--dump-ast` and `--layout-check` must be identical.
- `cmp_bins.py` compares two goosecc builds over the corpus (`-E`, the AST
  dump, the layout check, the objects with and without `-g`), from a saved
  record of the reference's checksums, and lists what differs with the ELF
  sections that differ.

### Debug information tests (B5)

```bash
GOOSECC_CACHE=/tmp/gcc-cache tests/dwarf_diff.py --corpus torture,unit,regress,bench,ctmark --verify -j 2 \
    --goosecc frontend-goose/build/goosecc --json dwarf.json -q          # DWARF vs clang-20 -O0 -g, every corpus file
tests/dwarf_diff.py --cc file.c ... [-- flags]                         # the same for some files
tests/dwarf_diff.py a.o b.o                                             # two objects
GOOSECC_CACHE=/tmp/gcc-cache tests/gdb_oracle.py --goosecc frontend-goose/build/goosecc --corpus c,sample,ctmark -j 2
tests/bench_goosecc.py --goosecc frontend-goose/build/goosecc --g -n 3 --md bench-g.md   # what -g costs
```

- `dwarf_diff.py` compiles each file with `clang-20 -O0 -g` and `goosecc
  -g`, prints both objects' `llvm-dwarfdump --debug-info` normalized (one
  DIE per line; references as the target's tag and name; code addresses,
  frame offsets, address indices, the producer and the section bases
  replaced) and compares them: identical, identical but for frame-location
  forms (a location list or `DW_OP_breg` against `DW_OP_fbreg`),
  identical as unordered sets of the unit's children, or differing.
  `--verify` runs `llvm-dwarfdump --verify` on every goosecc object;
  `--only report.json` reruns the files a report has as not identical.
- `gdb_oracle.py --goosecc` runs the same scripted gdb session on the
  clang `-O0 -g` build and the goosecc `-g` build of each C program
  (breakpoints on its functions and on lines of the reference line table;
  at each stop `bt`, `info args`, `info locals`, `next`, `step`, and for
  every argument and local `ptype`, `print` and `print *` of a pointer to
  a struct or union) and compares the transcripts. The corpora: `tests/c`,
  a sample of llvm-test-suite programs, and the CTMark C programs with
  their inputs.

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
tests/run.py --goosecc frontend-goose/build/goosecc -j 3          # the programs of tests/c, with and without -g
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

### Start-up, parse cache, clang's folding (G1)

**Compile time.** `tests/bench_hcache.py <CTMark compile_commands.json>
-n 3` (each file alone, single-threaded, the variants interleaved file
by file; best of 3; milliseconds; the machine was shared with another
job, load average 1.6-3). Before G1 (66ea246) and G1, run back to back:

| program | files | off (before) | warm (before) | off | cold | warm | tcc | clang `-O0` | warm/tcc |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 7zip | 32 | 96 | 87 | 79 | 100 | 70 | 83 | 852 | 1.18x |
| ClamAV | 98 | 452 | 400 | 417 | 622 | 364 | 460 | 3,486 | 1.27x |
| SPASS | 51 | 297 | 229 | 291 | 400 | 208 | 320 | 2,723 | 1.54x |
| consumer-typeset | 51 | 249 | 205 | 230 | 302 | 185 | 250 | 2,158 | 1.35x |
| lencod | 55 | 301 | 250 | 270 | 384 | 214 | 293 | 2,499 | 1.37x |
| mafft | 27 | 159 | 116 | 143 | 209 | 103 | 172 | 1,284 | 1.67x |
| sqlite3 | 2 | 41 | 41 | 49 | 48 | 44 | 29 | 451 | 0.67x |
| **total** | 316 | 1,596 | 1,328 | **1,479** | 2,067 | **1,188** | 1,607 | 13,453 | **1.35x** |

- Warm, goosecc is 1.35 times faster than tcc and 11.3 times faster than
  clang; without the cache it is faster than tcc too (1.48 s against
  1.61 s).
- sqlite3.c alone (`sq.py`, best of 9, without the cache): 37.5 ms before
  G1, 34.0 ms with it (preprocess 10.1, parse+sema 8.3, lowering 7.4,
  back-end 6.4); tcc takes 24.5 ms. The row above is noisier (one file,
  best of 3 under load). The target "faster than tcc on sqlite3.c" is not
  met: the file is a 250,000-line amalgamation whose own code is nearly
  all of it, so neither cache helps, and goosecc executes about 280
  million instructions on it against tcc's 210 million (callgrind; the
  preprocessor's macro expansion and the lexer are a quarter of it).
- On a quiet machine (earlier in G1, `qbench.py`): one-line file 1.19 →
  0.65 ms; CTMark warm 1,275 ms → 1,147 ms with the runtime patch →
  1,102 ms with the parse cache (parse+sema 218 → 153 ms); tcc 1,563 ms.
- The runtime patch moves the cost of enabling a region from start-up to
  its first touch, inside the phases: `--time`'s preprocessing phase
  grows by about that much while the whole compile gets shorter.

**DWARF against clang** (`tests/dwarf_diff.py --corpus
torture,unit,regress,bench,ctmark --verify -j 2`):

| corpus | files | identical | identical but for frame-location forms | differing | not compiled |
|---|---:|---:|---:|---:|---:|
| `torture` | 1708 | 1648 | 8 | 9 | 43 |
| `unit` | 182 | 164 | 1 | 0 | 17 |
| `regress` | 37 | 34 | 1 | 0 | 2 |
| `bench` | 102 | 99 | 1 | 0 | 2 |
| `ctmark` | 328 | 323 | 1 | 0 | 4 |
| **total** | 2357 | **2268** (B5: 2231) | 12 | **9** (B5: 44) | 68 |

The 9: eight torture tests with `always_inline` functions that have
debug information (clang inlines them and describes the expansions with
`DW_TAG_inlined_subroutine`s; goosecc calls them: `20080424-1`,
`20090113-3`, `pr33992`, `pr39228`, `pr63843`, `pr79043`, `stdarg-4`,
`va-arg-pack-1`), and `920721-2` (a VLA's location list as the back-end
writes it). `llvm-dwarfdump --verify` passes on all 2,289 objects.

**gdb** (`tests/gdb_oracle.py --goosecc --corpus c,sample,ctmark -j 2`):
49 of 84 sessions identical (1,556 stops); on B5's 79 programs 46 (B5:
45: `2006-01-23-UnionInit` now matches), and 3 of the 5 new `tests/c`
programs.

### Debug information (B5)

**DWARF against clang.** `tests/dwarf_diff.py --corpus
torture,unit,regress,bench,ctmark --verify -j 2` (warm header cache):

| corpus | files | identical | identical but for frame-location forms | differing | not compiled |
|---|---:|---:|---:|---:|---:|
| `torture` | 1708 | 1629 | 9 | 26 | 44 |
| `unit` | 182 | 158 | 1 | 6 | 17 |
| `regress` | 37 | 34 | 1 | 0 | 2 |
| `bench` | 102 | 94 | 1 | 5 | 2 |
| `ctmark` (all CTMark C files) | 328 | 316 | 1 | 7 | 4 |
| **total** | 2357 | **2231** | 13 | 44 | 69 |

"Not compiled": clang-20 rejects 68 of the files with the corpus flags
(implicit `int` and implicit declarations, errors in C99 and later; GCC
nested functions; the Integer tests' `__bitwidthof__`), as for the B1
oracles, and goosecc does not compile `noinit-attribute.c` (a section
attribute it does not lower; it did not before B5 either). Of
the 2,288 files both compile, 2,231 (97.5%) have the same normalized
`llvm-dwarfdump --debug-info`, and `llvm-dwarfdump --verify` passes on
all 2,288 goosecc objects. The 13 "frame-location" files differ only
where clang has a location list or a `DW_OP_breg` (NRVO, VLAs, realigned
frames) and goosecc a frame offset. The 44 that differ, each for one of
the reasons of DESIGN.md 11.6:

| reason | files |
|---|---:|
| clang folds reads of `const` variables with constant initializers (`const_value`, no location, order) | 18 |
| clang inlines `always_inline` functions at -O0 (inlined subroutines; the SSE tests' intrinsics) | 12 |
| clang folds what goosecc computes (address differences, `strlen`/`memchr` of literals, complex constants, `__builtin_constant_p` of a variable, an address-difference array bound) | 9 |
| an empty struct or a returned (NRVO) variable: clang drops it or gives it a location list | 3 |
| clang makes a constant array where goosecc makes a VLA (`const int` bound) | 2 |

**gdb.** `tests/gdb_oracle.py --goosecc --corpus c,sample,ctmark -j 2`:
79 C programs (the 49 of `tests/c`, 24 llvm-test-suite programs, the six
CTMark C programs with their inputs), 1,458 stops, at each `bt`, `info
args`, `info locals`, `ptype` and `print` of every argument and local
(`print *` of struct pointers), two `next` and a `step`:

| | programs | identical transcripts |
|---|---:|---:|
| `tests/c` | 49 | 31 |
| sample | 24 | 12 |
| CTMark | 6 | 2 |
| **total** | 79 | **45** |

The transcripts that differ do so where the two builds stop at different
places, not in what gdb shows of the program's data: aligning the stops
by position (function, file and line), 6,859 of clang's 7,242 stops have
a goosecc stop at the same place, and there the `ptype` of every variable
both list is the same (6,789 of 6,790; the exception is the `const
int`-sized array that goosecc makes a VLA, 11.6) and so are 7,508 of
7,588 printed values (the others are uninitialized stack or heap
contents, which the two frame layouts leave different, or a `next` that
ends on another instruction of the same line). 32 of the 34 differing
transcripts have stops at different positions: the line table, whose
statement rows B5 left as they were (below), differs from clang's where
the code does, e.g. goosecc gives the
branch out of a `then` block the line of its `}`, which makes one more
stop for `next`; and once one stop differs, the rest of the session
follows another path. The other two differ in a string read past its
end from an uninitialized buffer, and in the variable of an empty struct
that clang drops (NRVO).

**Cost.** `tests/bench_goosecc.py --g -n 3` (warm header cache, each
compile alone, best of 3) on the 284 C files of the six CTMark C
programs:

| program | files | clang-20 -O0 -g -c | goosecc -c | goosecc -g -c | -g / no -g | clang -g / goosecc -g |
|---|---:|---:|---:|---:|---:|---:|
| sqlite3 | 2 | 1036 ms | 59 ms | 92 ms | 1.57x | 11.20x |
| SPASS | 51 | 4219 ms | 312 ms | 407 ms | 1.31x | 10.37x |
| ClamAV | 98 | 5214 ms | 565 ms | 665 ms | 1.18x | 7.84x |
| lencod | 55 | 3878 ms | 352 ms | 447 ms | 1.27x | 8.67x |
| mafft | 27 | 1969 ms | 157 ms | 197 ms | 1.26x | 9.98x |
| consumer-typeset | 51 | 3452 ms | 283 ms | 358 ms | 1.27x | 9.63x |
| **total** | 284 | 19.77 s | 1.73 s | **2.17 s** | **1.25x** | **9.12x** |

`-g` costs 25% (sqlite3.c, with its 11,000 DIEs, 57%): per phase (sum of
one `--time` run per file) parse+sema 288 → 346 ms (the written types),
lowering 140 → 356 ms (the recording, clang's order and the DIE builder),
back-end 129 → 286 ms (the DWARF sections and the line table); peak RSS
24 → 35 MB (clang -g: 182 MB); objects 10.1 → 17.8 MB. goosecc -g stays
9.1 times faster than `clang-20 -O0 -g -c`.

**Regressions.** With the final build and a warm cache:
`tests/suite_goosecc.py` passes all 1,804 tests with and without `-g`
(3,608 runs), `tests/run.py --goosecc` 98/98; `cmp_E`, `cmp_syntax`,
`layout_check` and `cmp_ast` give B4's results (all identical, no false
error, 834,000 assertions, no AST difference); `cache_check.py` finds all
2,357 files identical in 44,783 runs. Objects without `-g` are
byte-identical to B4's for 2,239 of the 2,288 files; the other 49 use
`__PRETTY_FUNCTION__` (mostly through `assert`) and differ only in that
string's section (their `.text` is identical). The line tables of the
`-g` objects are B4's for 2,066 files; 207 more have extra rows that
repeat the previous row's line (B5's lexical scopes change the scope in
the middle of a line; the back-end, as LLVM, starts a row; breakpoints
and stepping are unchanged), 10 have the `__vla_exprN` stores, and 5
follow `#line` (clang's presumed locations, new in B5).

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
| torture | 1708 | 1708 | 32452 | 4730 | 3736 | 4934 | 3820 |
| unit | 182 | 182 | 3458 | 4109 | 3175 | 4088 | 3078 |
| regress | 37 | 37 | 703 | 700 | 586 | 700 | 586 |
| bench | 102 | 102 | 1938 | 5810 | 3592 | 6064 | 3604 |
| ctmark | 328 | 328 | 6232 | 34124 | 21818 | 36438 | 20134 |
| **total** | 2357 | 2357 | 44783 | 49473 | 32907 | 52224 | 31222 |

The last two columns are a second run with `GOOSECC_CACHE_QUOTED=1`
(also 2,357 of 2,357 identical). In both, no warm2 run recorded
anything. (The shared runs' counts vary slightly from one run to the
next: the parallel workers fill the shared cache in another order.)

With one cache filled by `-E` and `-fsyntax-only` compiles of every file
(358 MB; about three quarters of those compiles' lookups hit), the
front-end oracles give what they gave in B3: `cmp_E.py`
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
