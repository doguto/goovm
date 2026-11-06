
## clang 20.1.2, CTMark, O0-g

| program | files | wall s | frontend | optimizer | codegen | FE % | opt % | CG % |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 7zip | 212 | 33.05 | 23.72 | 0.05 | 2.32 | 89 | 0 | 9 |
| Bullet | 121 | 14.93 | 8.64 | 0.04 | 2.20 | 77 | 0 | 20 |
| ClamAV | 98 | 4.84 | 1.76 | 0.01 | 0.61 | 68 | 0 | 24 |
| SPASS | 51 | 4.11 | 1.81 | 0.02 | 0.73 | 68 | 1 | 27 |
| consumer-typeset | 51 | 3.19 | 1.25 | 0.01 | 0.57 | 64 | 0 | 30 |
| kimwitu++ | 14 | 5.52 | 3.58 | 0.05 | 1.10 | 74 | 1 | 23 |
| lencod | 55 | 3.35 | 1.43 | 0.01 | 0.54 | 68 | 0 | 26 |
| mafft | 27 | 1.76 | 0.76 | 0.01 | 0.28 | 69 | 0 | 25 |
| sqlite3 | 2 | 1.01 | 0.46 | 0.01 | 0.38 | 54 | 1 | 44 |
| tramp3d-v4 | 1 | 5.31 | 3.21 | 0.08 | 1.35 | 68 | 2 | 29 |
| **total** | 632 | 77.07 | 46.61 | 0.28 | 10.08 | 79 | 0 | 17 |

Top passes (s):
     0.13  AlwaysInlinerPass
     0.06  AnnotationRemarksPass
     0.02  TargetLibraryAnalysis
     0.01  EntryExitInstrumenterPass
     0.01  AAManager
     0.01  BasicAA
     0.01  AssumptionAnalysis
     0.00  TargetIRAnalysis
     0.00  DominatorTreeAnalysis
     0.00  ProfileSummaryAnalysis
     0.00  OuterAnalysisManagerProxy<ModuleAnalysisManager, Function>
     0.00  ScopedNoAliasAA
     0.00  TypeBasedAA
     0.00  InnerAnalysisManagerProxy<FunctionAnalysisManager, Module>
