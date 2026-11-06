# goovm-llc

`goovm-llc` reads LLVM bitcode, exports it to GIR version 2
([`gir/README.md`](../../gir/README.md)), runs the Goose back-end
([`backend-goose/`](../../backend-goose/DESIGN.md)) and writes an x86-64 ELF
relocatable object.

```
goovm-llc [--backend=goose|llvm|llvm-only] [--fallback] [--time] [--dump-gir] in.bc -o out.o
```

| option | meaning |
|---|---|
| `--backend=goose` | the Goose back-end (default) |
| `--backend=llvm` | LLVM's own `-O0` code generator in this process (PIC, `x86-64`); for comparison without `llc`'s start-up |
| `--backend=llvm-only` | parse and export only: no back-end runs and no object is written (`-o` is optional). This measures the LLVM-side cost, and checks that a module is in the GIR subset |
| `--fallback` | if the module uses something GIR cannot express, compile it with LLVM's `-O0` code generator instead, and say so on stderr: `goovm-llc: fallback: <reason> (<file> compiled by LLVM's code generator)`. Whole programs can then always be built; `tests/suite.py` counts such files |
| `--time` | per-phase timing to stderr (µs), plus a `goovm-time: key=value ...` line for scripts |
| `--dump-gir` | print the GIR tables to stdout |

The `--time` phases are:

| phase | what it covers |
|---|---|
| parse | reading the file and `parseBitcodeFile` |
| export | LLVM → GIR |
| backend | GIR → ELF bytes in memory (Goose), or LLVM codegen for `--backend=llvm` and fallbacks |
| write | writing the file |

Input is what `clang-20 -O0 [-g] -c -emit-llvm x.c` produces for x86-64
Linux, or that IR after `opt -passes=mem2reg`. Heavier pipelines mostly work
too, as long as they stay in the subset (scalable vectors, exception
handling and `va_arg` instructions do not).

Exit codes:

| code | meaning |
|---|---|
| 0 | object written |
| 1 | usage or I/O error |
| 2 | unsupported construct (without `--fallback`); the message names the construct, the function and the instruction |

## Files

| file | content |
|---|---|
| `goovm-llc.cpp` | the driver: parsing, export, back-end selection, fallback, timing |
| `gir_export.cpp`, `gir_export.h` | LLVM module → GIR tables, and the `--dump-gir` printer |
| `gir_asm.cpp`, `gir_asm.h` | assembling inline-asm text with LLVM's MC layer (for `GIR_ASM`) |

The exporter throws `GirUnsupported` (the target is compiled with
`-fexceptions`; the exception never crosses LLVM frames), which the driver
turns into exit status 2 or a fallback.

## Build

The build needs LLVM 20 (`/usr/lib/llvm-20`), CMake ≥ 3.20, ninja and the
goose compiler:

```
cmake -G Ninja -S . -B build -DCMAKE_BUILD_TYPE=Release \
      -DCMAKE_C_COMPILER=clang-20 -DCMAKE_CXX_COMPILER=clang++-20 \
      -DLLVM_DIR=/usr/lib/llvm-20/lib/cmake/llvm \
      -DGOOVM_GOOSE=/path/to/goose -DGOOVM_GOOSE_STDLIB=/path/to/goose/stdlib
ninja -C build -j3
# -> build/tools/goovm-llc/goovm-llc
```

(`backend-goose/build.sh` does the same from `GOOSE`/`GOOSE_STDLIB`.) CMake
runs `goose --standalone --header cg.h -o cg.c backend-goose/cg.goose` and
compiles the C with the same compiler and build type as the C++ (`-O3` in
Release), with warnings off, into a static library. `-DGOOVM_GOOSE_C=<cg.c>`
uses a pre-generated C file instead; `-DGOOVM_WITH_GOOSE=OFF` builds the
exporter and the LLVM back-end only. `goovm-llc` links the shared
`libLLVM-20.so`, the same way `llc-20` and `tpde-llc` do.

What the driver does with the Goose back-end (`goose_codegen`):

- It calls `goose_init(argc, argv)` once at start-up and `goose_exit()` at
  the end.
- It passes each GIR table as the generated slice type (`sl_Inst_g`,
  `sl_u32`, ...: `{T *data; int64_t len}` by value), without copying, and
  calls `const uint8_t *gir_codegen(..., gs_i64 *out_len)`.
- It writes the returned bytes to the output file straight from Goose's
  memory (valid until the next call).
- `static_assert`s check that every `*_g` struct has the size of its `Gir*`
  record and that key field offsets match.

The C++ reference back-end of GIR v0 (`backend-cpp/`) is frozen at commit
8f55b18 and no longer built; see `backend-cpp/README.md`.

## Tests

```
tests/run.py --goovm build/tools/goovm-llc/goovm-llc -j3        # 49 small programs, O0 + mem2reg
tests/suite.py --goovm build/tools/goovm-llc/goovm-llc -j3      # the llvm-test-suite corpora
```

`tests/run.py` builds each `tests/c/*.c` with `clang-20 -O0` as the
reference and through goovm-llc from `-O0` and `mem2reg` bitcode, and
compares stdout and exit status. `tests/suite.py` runs the gcc-c-torture,
UnitTests, Regression/C, Benchmarks and CTMark C programs of the
llvm-test-suite with their reference outputs (see its docstring and
`tests/README.md`).

## Benchmarks

```
bench/backend/make_inputs.sh /tmp/goovm-inputs            # gen-1000/5000/20000.bc, spass.bc, typeset.bc
bench/backend/time_backend.py --goovm build/tools/goovm-llc/goovm-llc -n 5 /tmp/goovm-inputs/*.bc
```

`time_backend.py` prints the best-of-N `backend_us` (and the other phases)
of `goovm-llc --time`. The other scripts in `bench/` are the v0 measurement
record (they compare `--backend=cpp` and need commit 8f55b18).
