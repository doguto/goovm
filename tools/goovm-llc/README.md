# goovm-llc

`goovm-llc` reads LLVM bitcode, exports it to GIR ([`gir/README.md`](../../gir/README.md)),
runs a back-end and writes an x86-64 ELF relocatable object.

```
goovm-llc [--backend=cpp|goose|llvm|llvm-only] [--time] [--dump-gir] in.bc -o out.o
```

| option | meaning |
|---|---|
| `--backend=cpp` | C++ reference back-end, `backend-cpp/` (default) |
| `--backend=goose` | the Goose back-end; only in builds with `-DGOOVM_WITH_GOOSE=ON` |
| `--backend=llvm` | LLVM's own `-O0` code generator in this process (PIC, `x86-64`); for comparison without `llc`'s start-up |
| `--backend=llvm-only` | parse and export only: no back-end runs and no object is written (`-o` is optional). This measures the LLVM-side cost that both GIR back-ends share |
| `--time` | per-phase timing to stderr (µs), plus a `goovm-time: key=value ...` line for scripts |
| `--dump-gir` | print the GIR tables to stdout |

The `--time` phases are:

| phase | what it covers |
|---|---|
| parse | reading the file and `parseBitcodeFile` |
| export | LLVM → GIR |
| backend | GIR → ELF bytes in memory, or LLVM codegen for `--backend=llvm` |
| write | writing the file |

It also prints the LLVM and GIR instruction counts.

Input is what `clang-20 -O0 -c -emit-llvm x.c` produces for C, without `-g`
(debug intrinsics are dropped anyway). IR after `opt -passes=mem2reg` or
heavier pipelines also works, as long as it stays in the subset.

Exit codes:

| code | meaning |
|---|---|
| 0 | object written |
| 1 | usage or I/O error |
| 2 | unsupported construct; the message names the function and the instruction |

## Build

The build needs LLVM 20 (`/usr/lib/llvm-20`), CMake ≥ 3.20 and ninja.

```
cmake -G Ninja -S . -B build -DCMAKE_BUILD_TYPE=Release \
      -DCMAKE_C_COMPILER=clang-20 -DCMAKE_CXX_COMPILER=clang++-20 \
      -DLLVM_DIR=/usr/lib/llvm-20/lib/cmake/llvm
ninja -C build -j2
# -> build/tools/goovm-llc/goovm-llc
```

`goovm-llc` links the shared `libLLVM-20.so`, the same way `llc-20` and
`tpde-llc` do.

## Tests

```
tests/run.py --goovm build/tools/goovm-llc/goovm-llc -j2
```

For each program in `tests/c/`, the script builds a reference with
`clang-20 -O0`. It also builds goovm binaries from the `-O0` bitcode and from
`opt -passes=mem2reg` bitcode, runs all of them, and compares stdout and the
exit status. Extra options:

| option | effect |
|---|---|
| `--tpde PATH` | also check `tpde-llc` |
| `--opt-passes "sroa,early-cse,instcombine,simplifycfg,gvn"` | add an optimized-IR variant. Three programs then fail on intrinsics outside the subset (`llvm.scmp`, `llvm.bitreverse`, `llvm.fshl`) |
| `--backend goose` | test the Goose back-end |

`tests/realworld_mixed.py --goovm ...` compiles every SPASS and
consumer-typeset file that is in the subset with goovm-llc and the rest with
clang. It links the program, runs it on its llvm-test-suite input and
compares the output with an all-clang build.

## Benchmarks

```
bench/backend/make_inputs.sh /tmp/goovm-inputs            # gen-1000/5000/20000.bc, spass.bc, typeset.bc
bench/backend/run.sh -n 5 --goovm build/tools/goovm-llc/goovm-llc \
    --tpde /path/to/tpde-llc [--inproc] [--goose] /tmp/goovm-inputs/*.bc
bench/backend/realworld.py --goovm build/tools/goovm-llc/goovm-llc   # what CTMark C code fits
```

`run.sh` prints a markdown table:

- the best-of-N wall time of `llc-20 -O0 -filetype=obj`, `tpde-llc` and
  `goovm-llc --backend=cpp`;
- the ratios between them (llc/goovm and tpde/goovm, so > 1 means goovm is
  faster);
- goovm's parse/export/back-end/write breakdown from its best run.

`--inproc` adds the column `goovm-llc --backend=llvm`. `--goose` adds the
Goose back-end and warns if its object is not byte-identical to the C++ one.

## Wiring in the Goose back-end

The Goose port is `backend-goose/cg.goose`. The current file is an interface
skeleton: it defines the record structs and the exported function, and
returns an empty object. It exports:

```goose
export fn gir_codegen(funcs: const Func[:], blocks: const Block[:], insts: const Inst[:],
                      opnds: const u32[:], consts: const Const[:], globals: const Global[:],
                      data: const u8[:], drelocs: const DataReloc[:], strtab: const u8[:]) -> const u8[:]
```

The structs `Func`, `Block`, `Inst`, `Const`, `Global` and `DataReloc` mirror
`gir.h` field for field. The one exception is `GirConst.pad`, which is called
`reserved` because `pad` is a Goose keyword. To build:

```
goose --standalone --header cg.h -o cg.c backend-goose/cg.goose     # e.g. in backend-goose/build/
cmake -G Ninja -S . -B build-goose -DCMAKE_BUILD_TYPE=Release \
      -DCMAKE_C_COMPILER=clang-20 -DCMAKE_CXX_COMPILER=clang++-20 \
      -DLLVM_DIR=/usr/lib/llvm-20/lib/cmake/llvm \
      -DGOOVM_WITH_GOOSE=ON -DGOOVM_GOOSE_C=$PWD/backend-goose/build/cg.c
ninja -C build-goose -j2
build-goose/tools/goovm-llc/goovm-llc --backend=goose --time x.bc -o x.o
```

What the CMake option does:

- `GOOVM_GOOSE_C` defaults to `backend-goose/build/cg.c`. `GOOVM_GOOSE_H`
  defaults to `cg.h` in the same directory.
- The generated C is compiled with the same compiler and build type as the
  C++ (`-O3` in Release), with warnings off, into a static library.
- The driver gets `GOOVM_WITH_GOOSE` and `GOOVM_GOOSE_HEADER="<path to cg.h>"`.
- With the option OFF (the default), nothing Goose-related is compiled, and
  `--backend=goose` reports that the build lacks it.

What the driver does (`goovm-llc.cpp`, `goose_codegen`):

- It calls `goose_init(argc, argv)` once at start-up and `goose_exit()` at
  the end.
- It passes each GIR table as the generated slice type, without copying.
  The slice types are `sl_Func_g`, `sl_Block_g`, `sl_Inst_g`, `sl_u32`
  (`gs_u32 *data`), `sl_Const_g`, `sl_Global_g`, `sl_u8` (`uint8_t *data`)
  and `sl_DataReloc_g`; each is `{T *data; int64_t len}` and passed by value.
- It calls `const uint8_t *gir_codegen(..., gs_i64 *out_len)`.
- It writes the returned bytes to the output file straight from Goose's
  memory, without copying. The bytes stay valid until the next call.
- `static_assert`s check that every `*_g` struct has the size of its `Gir*`
  record and that key field offsets match. A layout mismatch fails at
  compile time.
- An empty result is reported as an error (exit 1).

This was checked with the `goose` compiler on the skeleton: the generated
header matched these names, and the build and the call worked.
