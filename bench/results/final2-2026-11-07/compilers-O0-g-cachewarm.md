-O0 -g, best of 3, seconds (speed-up vs clang in parentheses)

| program | files (C++) | clang | goovm-cc | goosecc (C) | tcc (C, same files as goosecc) |
|---|---:|---:|---:|---:|---:|
| 7zip | 212 (180) | 30.12 | 28.38 (1.06x) | 0.12 (7.91x) | 0.08 vs 0.12 |
| Bullet | 121 (121) | 12.41 | 10.80 (1.15x) | - | - |
| ClamAV | 98 (0) | 3.85 | 3.43 (1.12x) | 0.56 (6.89x) | 0.45 vs 0.56 |
| SPASS | 51 (0) | 3.16 | 2.73 (1.16x) | 0.34 (9.42x) | 0.34 vs 0.34 |
| consumer-typeset | 51 (0) | 2.54 | 2.10 (1.21x) | 0.29 (8.73x) | 0.25 vs 0.29 |
| kimwitu++ | 14 (14) | 4.70 | 4.04 (1.16x) | - | - |
| lencod | 55 (0) | 2.92 | 2.49 (1.17x) | 0.37 (7.84x) | 0.01 vs 0.01 |
| mafft | 27 (0) | 1.44 | 1.19 (1.21x) | 0.15 (9.32x) | 0.17 vs 0.15 |
| sqlite3 | 2 (0) | 0.75 | 0.53 (1.40x) | 0.06 (11.65x) | 0.04 vs 0.06 |
| tramp3d-v4 | 1 (1) | 4.15 | 3.34 (1.24x) | - | - |
| **total** | 632 (316) | 66.05 | 59.04 (1.12x) | 1.89 (8.23x) | 1.33 vs 1.53 |

C files only: clang 15.59s over 316 files; goosecc compiled 316; tcc compiled 262 of them.
