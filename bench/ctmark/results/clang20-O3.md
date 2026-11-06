
## clang 20.1.2, CTMark, O3

| program | files | wall s | frontend | optimizer | codegen | FE % | opt % | CG % |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 7zip | 212 | 48.70 | 23.64 | 9.91 | 7.24 | 57 | 24 | 17 |
| Bullet | 121 | 23.48 | 8.25 | 6.37 | 4.15 | 43 | 33 | 22 |
| ClamAV | 98 | 11.59 | 1.65 | 4.22 | 3.15 | 18 | 46 | 34 |
| SPASS | 51 | 10.93 | 1.63 | 4.65 | 2.83 | 18 | 50 | 31 |
| consumer-typeset | 51 | 7.16 | 1.08 | 2.40 | 2.20 | 19 | 41 | 38 |
| kimwitu++ | 14 | 10.52 | 3.25 | 2.90 | 2.96 | 35 | 32 | 32 |
| lencod | 55 | 12.05 | 1.41 | 5.35 | 3.61 | 13 | 51 | 34 |
| mafft | 27 | 6.96 | 0.75 | 2.94 | 2.41 | 12 | 48 | 39 |
| sqlite3 | 2 | 7.85 | 0.36 | 4.22 | 2.95 | 5 | 56 | 39 |
| tramp3d-v4 | 1 | 17.05 | 2.45 | 9.13 | 3.98 | 16 | 59 | 26 |
| **total** | 632 | 156.27 | 44.48 | 52.09 | 35.47 | 33 | 39 | 26 |

Top passes (s):
     9.36  InstCombinePass
     4.06  GVNPass
     3.90  InlinerPass
     2.95  SimplifyCFGPass
     2.42  SLPVectorizerPass
     1.92  IndVarSimplifyPass
     1.81  EarlyCSEPass
     1.53  LoopUnrollPass
     1.40  DSEPass
     1.35  LICMPass
     1.25  JumpThreadingPass
     1.23  CorrelatedValuePropagationPass
     1.12  SROAPass
     1.10  MemorySSAAnalysis
     0.89  IPSCCPPass
