# Tests

| script | what |
|---|---|
| `run.py` | the small differential tests in `c/` (49 programs), `cxx/` and `mixed/` (C and C++ linked together) |
| `suite.py` | the llvm-test-suite C and C++ corpora through goovm-llc (and goovm-cc), against their reference outputs |
| `gdb_oracle.py` | the same scripted gdb session on a clang -O0 -g build and a goovm build, compared; `--unwind`: single-step every function checking the backtrace |
| `realworld_mixed.py` | (v0) links SPASS and consumer-typeset from a mix of goovm and clang objects |
| `suite_goosecc.py` | the same corpora compiled by goosecc (`frontend-goose/`, no LLVM) |
| `bench_goosecc.py` | compile speed and memory of `goosecc -c` vs `clang-20 -O0 -c` and `tcc -c` on CTMark |
| `bench_hcache.py` | goosecc's header cache: CTMark compile times with the cache disabled, cold and warm, vs `tcc -c` and `clang-20 -O0 -c` |

## run.py

Programs: `c/*.c`, `cxx/*.cpp` (exceptions, comdat templates, thread_local
dynamic initialization, init priorities, virtual inheritance, RTTI,
iostreams) and `mixed/<name>/` (several C and C++ files linked together).
For each: a reference build with `clang-20 -O0` / `clang++-20 -O0`, then
goovm-llc builds from `-O0` bitcode and from `opt-20 -passes=mem2reg`
bitcode; stdout and exit status must match the reference. A mixed program
is also built with only its C files (`c-goovm`) or only its C++ files
(`cxx-goovm`) by goovm-llc, so that exceptions cross frames of the other
compiler: `mixed/eh_through_c` throws C++ exceptions through goovm-compiled
C frames (plain calls, `qsort` callbacks, function pointers, frames with
dynamic allocas and stack arguments) and checks that the stack pointer is
the same after each catch.

```
tests/run.py --goovm build/tools/goovm-llc/goovm-llc -j3 [--opt-passes PASSES] [filter ...]
tests/run.py --goosecc frontend-goose/build/goosecc -j3 [filter ...]
```

With `--goosecc`, the variants are `goosecc -c` and `goosecc -c -g` instead
(no LLVM involved; C programs only).

## suite.py

```
tests/suite.py --goovm build/tools/goovm-llc/goovm-llc [--corpus a,b,...] [--variants O0,g,mem2reg]
               [--cc build/tools/goovm-cc/goovm-cc] [--verify-dwarf]
               [-j 3] [--work DIR] [--fallback] [--report FILE] [--json FILE] [--rebaseline]
               [--time-run N] [filter ...]
```

Corpora (from the llvm-test-suite checkout, `--suite`, default
`/home/user/llvm/llvm-test-suite`):

| corpus | tests | source, flags |
|---|---|---|
| `torture` | gcc-c-torture/execute/*.c | the CMakeLists' flags; its UnsupportedTests and FailingTests skip lists; per-test `-fwrapv`, `-Wno-return-type`, `-lm` lists; `dg-options` picked up like `gcc_torture_dg_options_cflags` (minus `-O` levels: the harness sets the optimization level) |
| `ieee` | gcc-c-torture/execute/ieee/*.c | its CMakeLists (`-lm`, `-fno-trapping-math` lists, skip list) |
| `builtins` | gcc-c-torture/execute/builtins/X.c | not run by the llvm-test-suite; built as gcc's builtins.exp does: X.c + X-lib.c + lib/main.c, `.x` additional_flags |
| `unittests` | SingleSource/UnitTests (C files of the directories its CMakeLists adds for x86: top level, Float, HashRecognize, SignlessTypes, Threads, Vector, Vector/SSE) | per-directory flags and RUN_OPTIONS |
| `regression` | SingleSource/Regression/C (+ SSE) | |
| `benchmarks` | SingleSource/Benchmarks C programs (BenchmarkGame, CoyoteBench, Dhrystone, Linpack, McGill, Misc, Shootout, Stanford, Polybench) | per-directory flags, FP_TOLERANCE, HASH_PROGRAM_OUTPUT |
| `ctmark` | sqlite3, SPASS, ClamAV, lencod, mafft, consumer-typeset | the MultiSource CMakeLists' flags, RUN_OPTIONS, inputs (sqlite3's are generated with `tclsh speedtest.tcl`) |
| `unittests-cxx` | SingleSource/UnitTests C++ files (top level, C++11, EH, SignlessTypes, Vectorizer, X86) | per-directory flags |
| `regression-cxx` | SingleSource/Regression/C++ (+ EH) | |
| `benchmarks-cxx` | SingleSource/Benchmarks C++ programs (Misc-C++, Misc-C++-EH, Shootout-C++, Shootout-C++/EH, Adobe-C++, CoyoteBench, SmallPT, ...) | per-directory flags and tolerances |
| `ctmark-cxx` | 7zip, Bullet, kimwitu++, tramp3d-v4 | the MultiSource CMakeLists' flags and inputs |

The C++ corpora follow the same exclusion rule (a test that does not build
or pass with plain `clang++-20 -O0` is excluded); C++ sources are compiled
with `clang++-20` and the programs linked with it.

Variants: `O0` (`clang-20 -O0 -emit-llvm`), `g` (with `-g`), `mem2reg`
(`-Xclang -disable-O0-optnone`, then `opt-20 -passes=mem2reg`), and with
`--cc` `cc` and `cc-g` (each file compiled by `goovm-cc -c`, clang's front
end and the Goose back-end in one process, without and with `-g`). Each
source file becomes a goovm object; the objects are linked by `clang-20` /
`clang++-20` with the test's LDFLAGS. `--verify-dwarf` runs
`llvm-dwarfdump-20 --verify` on every object of the `g` and `cc-g`
variants; an error or warning fails the test, and the report gives the
number of verified objects.

Verification follows the llvm-test-suite:

- SingleSource and MultiSource ("traditional output", `lit.local.cfg`):
  stdout and stderr go to one file, `exit N` is appended (timeit
  `--append-exitstatus`; a signal is 128+N), the file is md5-hashed if the
  directory sets `HASH_PROGRAM_OUTPUT`, then compared with
  `<name>.reference_output` by the suite's own `fpcmp` with the directory's
  `FP_TOLERANCE` / `FP_ABSTOLERANCE`. The program runs in a directory with
  its data files symlinked (and an `Output/` directory, as lit has).
- gcc-c-torture (`traditional_output = False`): the program must exit with
  status 0 (`abort()` on failure).

The **baseline** is the same build with plain `clang-20 -O0`. Tests that do
not build or pass that way are excluded and listed in the report; the
baseline is cached in `<work>/baseline.json` (`--rebaseline` recomputes it).
Each goovm run gets a timeout of 20 times the baseline's run time (at least
60 s).

Results per test and variant: `pass`; `fail` (wrong output, crash, timeout,
link error); `unsupported` (goovm-llc exit 2 on some file); `fallback` (with
`--fallback`, some file went through LLVM's code generator; counted as
passing if the output is right, and counted separately); `error` (another
tool failed).

`--time-run N` runs every passing program and its plain `clang-20 -O0`
build N more times (best wall time of each) and adds a run-time table with
the ratio per test and their geometric mean. Use `-j 1` (and one variant)
when the numbers matter, e.g. the CTMark comparison:

```
tests/suite.py --goovm build/tools/goovm-llc/goovm-llc --corpus ctmark --variants O0 -j 1 --time-run 3
```

## gdb_oracle.py

```
tests/gdb_oracle.py --goovm build/tools/goovm-llc/goovm-llc [--cc goovm-cc] [--corpus c,sample]
                    [-j 3] [--work DIR] [--stops N] [--unwind [--unwind-calls N]] [filter ...]
```

For every program (`c`: `tests/c`; `sample`: a sample of llvm-test-suite C
and C++ programs), a reference build with `clang -O0 -g` and a goovm build
from the same `-g` bitcode, and one scripted gdb session per build (batch
mode, gdb's Python API): breakpoints on the program's functions and on a
sample of the statement lines of the reference line table; at each stop
(at most 3 per breakpoint) `bt`, `info args`, `info locals`, two `next`
with the locals, and a `step` with the frame. Uninitialized locals read the
same in both builds because the session fills the 8 KB below the stack
pointer with one byte at every function entry. The transcripts are
normalized (addresses, pids, directories, stack addresses printed as
values, the length of runs of that poison byte past a buffer, glibc's
`jmp_buf` in `__libc_start_call_main`) and compared line by line; the
first differing blocks are printed.

With `--unwind` the goovm build alone is checked: for each of the program's
functions (its first `--unwind-calls` activations), break on its first
instruction and single-step it (`stepi`, `nexti` over calls) until it has
returned, checking at every instruction boundary that the backtrace is the
function over the same callers as on entry.

## suite_goosecc.py

The same corpora, tests, flags, inputs, verification and baseline as
`suite.py`, with every source file compiled by goosecc (milestone B2)
instead of clang + goovm-llc; clang-20 links the objects.

```
tests/suite_goosecc.py --goosecc frontend-goose/build/goosecc [--corpus a,b,...] [--variants O0,g]
                       [-j 3] [--work DIR] [--report FILE] [--json FILE] [--rebaseline] [filter ...]
```

Variants: `O0` (`goosecc -c`) and `g` (`goosecc -c -g`). Results: `pass`,
`fail` (wrong output, crash, timeout, link error), `error` (goosecc exited
non-zero or crashed; the report gives the first line of its message). The
baseline cache (`<work>/baseline.json`) has `suite.py`'s format, so a work
directory of `suite.py` can be reused.

## bench_goosecc.py

Compile speed of `goosecc -c` against `clang-20 -O0 -c` and TinyCC
(`tcc -c`, when installed) on every C file of the six CTMark programs, with
`suite.py`'s flags: best of N wall-clock runs, each compile alone, peak RSS
(`ru_maxrss`), and goosecc's phases from `--time`.

```
tests/bench_goosecc.py --goosecc frontend-goose/build/goosecc -n 3 [--md out.md] [--json out.json] [program ...]
```

goosecc uses its header cache by default (`frontend-goose/README.md`);
run with `GOOSECC_CACHE=off` to measure it without, as B2 and B3 did.

## bench_hcache.py

The header cache of goosecc (milestone B4): every C file of a CTMark
`compile_commands.json` (llvm-test-suite configured with
`cmake/caches/O0.cmake`; the 316 C files of sqlite3, SPASS, ClamAV,
consumer-typeset, lencod, mafft and 7zip) compiled with the cache
disabled (`off`), with an empty cache (`cold`), with the cache a previous
compile of the same file filled (`warm`), by tcc and by the configured
clang command; the variants interleaved file by file, best of N
wall-clock runs, single-threaded, and goosecc's phases from one `--time`
run per file and variant. `--build` adds a first build: all the files
once, in order, with one cache that starts empty.

```
tests/bench_hcache.py compile_commands.json --goosecc frontend-goose/build/goosecc -n 5 \
    [--build] [--no-clang] [--md out.md] [--json out.json] [program ...]
```
