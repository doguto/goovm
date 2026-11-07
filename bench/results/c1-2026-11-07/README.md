# Milestone C1 measurements (2026-11-07)

Host: 4-core Sapphire Rapids VM ("Intel Xeon Processor @ 2.10GHz"), clang/LLVM
20.1.2. Run times are wall times, best of N, single-threaded; ratios are to
the clang -O0 build timed in the same rounds. The host's speed drifted by up
to 25% within an hour (other VMs), so every comparison below is from one
session, the builds timed in interleaved rounds. `$C1` is the scratch
directory of the session (`.../scratchpad/work/c1`).

| file | what |
|---|---|
| `runtime-ctmark.md` | CTMark, final build (commit 6690a17), `tests/suite.py --corpus ctmark,ctmark-cxx --variants O0,cc -j 1 --time-run 3` |
| `runtime-ctmark-before-c1.md` | the same with the A3 back-end (commit c96510d), `--variants O0`, an hour earlier |
| `runtime-fp.md` | FP-heavy SingleSource benchmarks: clang -O0, the A3 back-end, the C1 back-end (interleaved best of 3) |
| `screening-singlesource.md` | all 141 SingleSource benchmarks with an intermediate C1 build (after the epilogue fix, before the false-dependency and load-order fixes), best of 1: the screening that found causes 7 and 8 |
| `epilogue-forms.md` | `mov rsp, rbp` / `lea rsp, [rbp-8k]` epilogues (column O0) against LLVM's `add rsp, n` (column E), interleaved best of 3 |
| `codequal-before-c1.md`, `codequal.md` | `bench/codequal/run.sh DIR 5 2` with `PER_KERNEL=1`, A3 and C1 back-ends |
| `suite-c-corpora.md`, `suite-ctmark-cxx-corpora.md` | the correctness run of the final build: all corpora, variants O0, g, mem2reg, cc, cc-g, `--verify-dwarf` |
| `gdb-oracle-c.log`, `gdb-oracle-unwind-c.log` | `tests/gdb_oracle.py --corpus c` and `--unwind --corpus c` with the final build |
| `compile-speed.md` | `bench/backend/time_backend.py -n 11` and an interleaved best of 31 of the back-end phase |

## Shares of Bullet's gap (builds adding the fixes one at a time)

Interleaved best of 3, `$C1/tround.py 3 <Bullet dir> -- clang A3 A B C D`:

| build | run time | / clang -O0 |
|---|---:|---:|
| clang -O0 | 16.270 s | 1.000 |
| A3 back-end (c96510d) | 27.562 s | 1.694 |
| + extractvalue as a load at the field's width (A) | 18.964 s | 1.166 |
| + call results in their return registers (B) | 17.434 s | 1.072 |
| + deferred aggregate loads (C, commit 286b171) | 16.321 s | 1.003 |

Later rounds: + small memcpys in 8-byte moves 0.996 -> 0.962 (another round:
clang 15.915 s, before 15.852 s, after 15.309 s).

## tramp3d-v4 and the epilogue

| build | run time | / clang -O0 |
|---|---:|---:|
| clang -O0 | 15.571 s | 1.000 |
| A3 back-end | 18.440 s | 1.184 |
| C1 before the epilogue fix (`leave`) | 18.277 s | 1.174 |
| `mov rsp, rbp; pop rbp` | 15.768 s | 1.013 |

Microbenchmark (four nested calls of a 16-byte frame, 10^8 chains, `$C1/t/epi.s`):
`leave` 0.89-0.95 s, `add rsp, 16; pop rbp` 0.47-0.50 s, `mov rsp, rbp; pop rbp`
0.43-0.48 s, `lea rsp, [rbp-8]; pop rbx; pop rbp` 0.48-0.49 s.

clang's own tramp3d-v4 with `-falign-functions=32`: 0.999x, `=64`: 0.944x
of its default build (placement sensitivity).

## Load order (linpack's daxpy loop in isolation, `$C1/t/dax2.s`)

2*10^6 calls of 100 iterations, same alignment: goovm's order (index load,
then pointer) 0.45-0.49 s; pointer first 0.38-0.39 s; clang's order 0.33-0.35 s.
