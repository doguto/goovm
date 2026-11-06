# Milestone A2 measurements (2026-11-06)

A2 = goovm-llc at commit 7b9d99e (same code as the branch head; later
commits change documentation only); A1 = commit 5d17665. Machine: the shared
4-core VM of the earlier results (another agent's test runs in parallel).
`<scratch>` stands for the session's scratch directory.

| file | what | command |
|---|---|---|
| `codequal.md` | run time and `.text` of `bench/codequal` | `PER_KERNEL=1 GOOVM=... TPDE=... bench/codequal/run.sh DIR 5 2` (A2, then A1) |
| `text.md` | `.text` bytes of the benchmark inputs | `llc-20 -O0 -relocation-model=pic`, `tpde-llc`, goovm A1 and A2 on the same bitcode |
| `backend.md` | back-end and export phases, TPDE `Compile` | `bench/backend/time_backend.py --goovm A1 --goovm A2 -n 7 ...`; `tpde-llc --time-trace`, best of 7 |
| `ctmark.md`, `ctmark-a1.md` | CTMark C run times against clang -O0 | `tests/suite.py --corpus ctmark --variants O0 -j 1 --time-run 5` (A1: 3) |
| `build2.md`, `build2-a1.md` | SingleSource/UnitTests/Vector/build2 | `tests/suite.py --corpus unittests --variants O0 -j 1 --time-run 3 build2` (A1: 1) |
| `suite.md` | correctness, all corpora, O0 / g / mem2reg | `tests/suite.py -j3` |

Summary in [`backend-goose/NOTES.md`](../../../backend-goose/NOTES.md) §9.
