-O0 -g, best of 3, seconds (speed-up vs clang in parentheses)

| program | files (C++) | clang | goovm-cc | goosecc (C) | tcc (C, same files as goosecc) |
|---|---:|---:|---:|---:|---:|
| 7zip | 212 (180) | 40.01 | 38.18 (1.05x) | 0.14 (9.09x) | 0.11 vs 0.14 |
| Bullet | 121 (121) | 16.85 | 14.67 (1.15x) | - | - |
| ClamAV | 98 (0) | 5.16 | 4.57 (1.13x) | 0.67 (7.76x) | 0.61 vs 0.67 |
| SPASS | 51 (0) | 4.24 | 3.56 (1.19x) | 0.46 (9.30x) | 0.45 vs 0.46 |
| consumer-typeset | 51 (0) | 3.42 | 2.85 (1.20x) | 0.38 (9.04x) | 0.34 vs 0.38 |
| kimwitu++ | 14 (14) | 6.39 | 5.36 (1.19x) | - | - |
| lencod | 55 (0) | 3.87 | 3.34 (1.16x) | 0.45 (8.68x) | 0.01 vs 0.01 |
| mafft | 27 (0) | 1.96 | 1.67 (1.17x) | 0.23 (8.64x) | 0.23 vs 0.23 |
| sqlite3 | 2 (0) | 1.08 | 0.71 (1.52x) | 0.08 (14.13x) | 0.05 vs 0.08 |
| tramp3d-v4 | 1 (1) | 5.21 | 4.27 (1.22x) | - | - |
| **total** | 632 (316) | 88.19 | 79.17 (1.11x) | 2.39 (8.79x) | 1.80 vs 1.96 |

C files only: clang 21.04s over 316 files; goosecc compiled 316; tcc compiled 262 of them.
