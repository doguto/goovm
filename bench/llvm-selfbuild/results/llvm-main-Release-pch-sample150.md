
## llvm-project main (4b8f5da) built by clang 20.1.2, Release (-O3), with PCH (default), same 150 files

| program | files | wall s | frontend | optimizer | codegen | FE % | opt % | CG % |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| ABI | 2 | 0.59 | 0.33 | 0.12 | 0.04 | 66 | 24 | 8 |
| Analysis | 9 | 25.30 | 7.81 | 10.98 | 3.88 | 34 | 48 | 17 |
| BinaryFormat | 2 | 0.18 | 0.08 | 0.01 | 0.01 | 76 | 13 | 5 |
| Bitcode | 1 | 3.66 | 0.98 | 1.71 | 0.55 | 30 | 53 | 17 |
| Bitstream | 1 | 0.82 | 0.26 | 0.35 | 0.11 | 35 | 49 | 15 |
| CAS | 2 | 1.79 | 0.76 | 0.59 | 0.19 | 49 | 38 | 12 |
| CGData | 2 | 2.46 | 1.29 | 0.69 | 0.19 | 59 | 32 | 9 |
| CodeGen | 24 | 42.19 | 18.91 | 14.73 | 4.04 | 50 | 39 | 11 |
| DebugInfo | 19 | 15.91 | 10.62 | 2.62 | 0.86 | 75 | 18 | 6 |
| Demangle | 1 | 0.19 | 0.13 | 0.02 | 0.01 | 82 | 12 | 3 |
| ExecutionEngine | 9 | 13.96 | 9.28 | 2.62 | 0.61 | 74 | 21 | 5 |
| Frontend | 1 | 0.97 | 0.45 | 0.29 | 0.15 | 50 | 32 | 17 |
| IR | 15 | 13.49 | 5.49 | 4.93 | 1.12 | 47 | 42 | 10 |
| MC | 6 | 7.65 | 5.19 | 1.30 | 0.41 | 75 | 19 | 6 |
| MCA | 1 | 0.07 | 0.01 | 0.00 | 0.00 | 67 | 7 | 7 |
| ObjCopy | 1 | 1.13 | 0.69 | 0.27 | 0.06 | 67 | 26 | 6 |
| ObjectYAML | 4 | 9.85 | 2.96 | 3.91 | 1.66 | 35 | 46 | 19 |
| Option | 1 | 0.68 | 0.21 | 0.29 | 0.11 | 34 | 48 | 18 |
| ProfileData | 2 | 4.01 | 1.68 | 1.44 | 0.38 | 48 | 41 | 11 |
| Remarks | 1 | 0.94 | 0.37 | 0.31 | 0.07 | 49 | 41 | 10 |
| SandboxIR | 1 | 0.54 | 0.38 | 0.07 | 0.02 | 80 | 15 | 3 |
| Support | 7 | 3.44 | 1.12 | 1.29 | 0.50 | 38 | 44 | 17 |
| TableGen | 2 | 1.84 | 1.40 | 0.22 | 0.04 | 84 | 13 | 2 |
| Target/AArch64 | 3 | 8.53 | 4.90 | 2.05 | 0.82 | 63 | 26 | 10 |
| Target/RISCV | 5 | 22.34 | 9.63 | 7.23 | 3.77 | 46 | 35 | 18 |
| Target/X86 | 8 | 11.01 | 7.74 | 1.70 | 0.56 | 77 | 17 | 6 |
| TextAPI | 1 | 0.16 | 0.06 | 0.03 | 0.01 | 56 | 31 | 10 |
| Transforms | 18 | 42.59 | 18.36 | 15.56 | 4.13 | 48 | 41 | 11 |
| XRay | 1 | 0.32 | 0.13 | 0.09 | 0.05 | 48 | 32 | 18 |
| **total** | 150 | 236.61 | 111.22 | 75.42 | 24.34 | 52 | 36 | 11 |

Top passes (s):
    11.80  InstCombinePass
    10.91  InlinerPass
     4.28  GVNPass
     3.38  SimplifyCFGPass
     3.36  EarlyCSEPass
     2.65  SROAPass
     2.42  BlockFrequencyAnalysis
     2.19  JumpThreadingPass
     2.12  CorrelatedValuePropagationPass
     1.99  AAManager
     1.96  MemorySSAAnalysis
     1.67  DSEPass
     1.60  BranchProbabilityAnalysis
     1.56  ConstraintEliminationPass
     1.48  IPSCCPPass
