
## llvm-project main (4b8f5da) built by clang 20.1.2, Release (-O3), no PCH, 150 random files of llvm/lib

| program | files | wall s | frontend | optimizer | codegen | FE % | opt % | CG % |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| ABI | 2 | 1.50 | 1.19 | 0.12 | 0.04 | 87 | 9 | 3 |
| Analysis | 9 | 41.29 | 22.84 | 11.11 | 3.77 | 60 | 29 | 10 |
| BinaryFormat | 2 | 0.80 | 0.67 | 0.02 | 0.01 | 95 | 2 | 1 |
| Bitcode | 1 | 5.27 | 2.62 | 1.55 | 0.52 | 55 | 32 | 11 |
| Bitstream | 1 | 1.30 | 0.70 | 0.36 | 0.11 | 60 | 30 | 9 |
| CAS | 2 | 3.06 | 1.94 | 0.60 | 0.20 | 70 | 22 | 7 |
| CGData | 2 | 4.51 | 3.20 | 0.71 | 0.17 | 78 | 17 | 4 |
| CodeGen | 24 | 101.61 | 73.09 | 15.72 | 4.41 | 78 | 17 | 5 |
| DebugInfo | 19 | 26.39 | 20.18 | 2.64 | 1.02 | 84 | 11 | 4 |
| Demangle | 1 | 0.22 | 0.14 | 0.02 | 0.01 | 82 | 12 | 3 |
| ExecutionEngine | 9 | 20.81 | 15.51 | 2.62 | 0.74 | 82 | 14 | 4 |
| Frontend | 1 | 1.53 | 0.94 | 0.32 | 0.14 | 67 | 23 | 10 |
| IR | 15 | 36.29 | 26.53 | 5.36 | 1.19 | 80 | 16 | 4 |
| MC | 6 | 10.69 | 7.98 | 1.39 | 0.40 | 81 | 14 | 4 |
| MCA | 1 | 0.07 | 0.00 | 0.00 | 0.00 | 27 | 18 | 17 |
| ObjCopy | 1 | 1.74 | 1.24 | 0.29 | 0.07 | 77 | 18 | 4 |
| ObjectYAML | 4 | 12.49 | 5.54 | 3.90 | 1.60 | 50 | 35 | 14 |
| Option | 1 | 1.18 | 0.66 | 0.29 | 0.11 | 62 | 27 | 10 |
| ProfileData | 2 | 5.32 | 3.02 | 1.38 | 0.36 | 63 | 29 | 8 |
| Remarks | 1 | 1.56 | 0.90 | 0.34 | 0.08 | 68 | 26 | 6 |
| SandboxIR | 1 | 1.95 | 1.75 | 0.06 | 0.01 | 95 | 3 | 1 |
| Support | 7 | 6.14 | 3.71 | 1.23 | 0.48 | 68 | 22 | 9 |
| TableGen | 2 | 3.01 | 2.51 | 0.22 | 0.05 | 90 | 8 | 2 |
| Target/AArch64 | 3 | 16.63 | 12.56 | 1.95 | 0.86 | 81 | 13 | 6 |
| Target/RISCV | 5 | 39.25 | 26.31 | 6.94 | 3.43 | 71 | 19 | 9 |
| Target/X86 | 8 | 35.35 | 30.26 | 1.98 | 0.64 | 91 | 6 | 2 |
| TextAPI | 1 | 0.67 | 0.55 | 0.04 | 0.01 | 91 | 6 | 2 |
| Transforms | 18 | 81.43 | 54.73 | 15.74 | 4.07 | 73 | 21 | 5 |
| XRay | 1 | 0.78 | 0.54 | 0.09 | 0.05 | 79 | 13 | 7 |
| **total** | 150 | 462.84 | 321.85 | 76.97 | 24.55 | 75 | 18 | 6 |

Top passes (s):
    12.17  InstCombinePass
    10.98  InlinerPass
     4.20  GVNPass
     3.43  EarlyCSEPass
     3.36  SimplifyCFGPass
     2.74  SROAPass
     2.58  BlockFrequencyAnalysis
     2.49  AAManager
     2.13  JumpThreadingPass
     2.10  CorrelatedValuePropagationPass
     2.07  MemorySSAAnalysis
     1.66  DSEPass
     1.61  BranchProbabilityAnalysis
     1.60  ConstraintEliminationPass
     1.59  IPSCCPPass
