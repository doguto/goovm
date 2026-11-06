# Tests

| script | what |
|---|---|
| `run.py` | the small differential tests in `c/` (42 programs) |
| `suite.py` | the llvm-test-suite C corpora through goovm-llc, against their reference outputs |
| `realworld_mixed.py` | (v0) links SPASS and consumer-typeset from a mix of goovm and clang objects |

## run.py

For each `c/*.c`: a reference build with `clang-20 -O0`, then goovm-llc
builds from `-O0` bitcode and from `opt-20 -passes=mem2reg` bitcode; stdout
and exit status must match the reference.

```
tests/run.py --goovm build/tools/goovm-llc/goovm-llc -j3 [--opt-passes PASSES] [filter ...]
```

## suite.py

```
tests/suite.py --goovm build/tools/goovm-llc/goovm-llc [--corpus a,b,...] [--variants O0,g,mem2reg]
               [-j 3] [--work DIR] [--fallback] [--report FILE] [--json FILE] [--rebaseline] [filter ...]
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

Variants: `O0` (`clang-20 -O0 -emit-llvm`), `g` (with `-g`), `mem2reg`
(`-Xclang -disable-O0-optnone`, then `opt-20 -passes=mem2reg`). Each source
file becomes a goovm-llc object; the objects are linked by `clang-20` with
the test's LDFLAGS.

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
