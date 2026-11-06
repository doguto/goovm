| program | files | clang -O0 -c | front (→ .bc) | llc -O0 | tpde-llc | front+llc | front+tpde | e2e gain |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 7zip | 212 | 27.42 | 26.34 | 5.02 | 2.95 | 31.36 | 29.29 | 1.07x |
| Bullet | 121 | 11.23 | 10.02 | 3.60 | 1.71 | 13.61 | 11.72 | 1.16x |
| ClamAV | 98 | 3.72 | 3.33 | 1.86 | 1.23 | 5.19 | 4.56 | 1.14x |
| SPASS | 51 | 2.77 | 2.43 | 1.21 | 0.68 | 3.64 | 3.11 | 1.17x |
| consumer-typeset | 51 | 2.13 | 1.86 | 1.22 | 0.70 | 3.07 | 2.56 | 1.20x |
| kimwitu++ | 14 | 3.86 | 3.44 | 0.97 | 0.30 | 4.41 | 3.75 | 1.18x |
| lencod | 55 | 2.58 | 2.34 | 1.30 | 0.79 | 3.64 | 3.14 | 1.16x |
| mafft | 27 | 1.20 | 1.07 | 0.57 | 0.33 | 1.64 | 1.40 | 1.17x |
| sqlite3 | 2 | 0.48 | 0.34 | 0.30 | 0.09 | 0.64 | 0.42 | 1.52x |
| tramp3d-v4 | 1 | 2.89 | 2.43 | 0.83 | 0.16 | 3.26 | 2.59 | 1.26x |
| **total** | 632 | 58.27 | 53.58 | 16.87 | 8.94 | 70.46 | 62.53 | 1.13x |

back-end only: llc 16.87s vs tpde 8.94s = 1.9x (tpde failures fell back to llc: 0 files)

in-process back-end: LLVM -O0 4.97s, TPDE 0.34s (14.6x)
clang -O0 -c total 58.27s -> with TPDE built in (estimate) 53.64s = 1.09x end to end
goovm subset (268 files), in-process: LLVM 1.143s, TPDE 0.082s, goovm-cpp 0.093s, goovm-goose 0.083s
goovm subset (268 files): llc 5.30s, goovm-cpp 3.48s, goovm-goose 3.47s
