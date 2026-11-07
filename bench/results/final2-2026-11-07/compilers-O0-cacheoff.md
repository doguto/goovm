-O0, best of 3, seconds (speed-up vs clang in parentheses)

| program | files (C++) | clang | goovm-cc | goosecc (C) | tcc (C, same files as goosecc) |
|---|---:|---:|---:|---:|---:|
| 7zip | 212 (180) | 28.41 | 27.14 (1.05x) | 0.10 (8.46x) | 0.08 vs 0.10 |
| Bullet | 121 (121) | 11.44 | 10.28 (1.11x) | - | - |
| ClamAV | 98 (0) | 3.48 | 3.17 (1.10x) | 0.47 (7.33x) | 0.45 vs 0.47 |
| SPASS | 51 (0) | 2.73 | 2.42 (1.13x) | 0.33 (8.35x) | 0.32 vs 0.33 |
| consumer-typeset | 51 (0) | 2.12 | 1.78 (1.19x) | 0.27 (7.75x) | 0.26 vs 0.27 |
| kimwitu++ | 14 (14) | 4.04 | 3.56 (1.14x) | - | - |
| lencod | 55 (0) | 2.44 | 2.13 (1.14x) | 0.31 (7.81x) | 0.28 vs 0.31 |
| mafft | 27 (0) | 1.25 | 1.14 (1.10x) | 0.17 (7.59x) | 0.17 vs 0.17 |
| sqlite3 | 2 (0) | 0.54 | 0.32 (1.68x) | 0.05 (11.92x) | 0.03 vs 0.05 |
| tramp3d-v4 | 1 (1) | 3.03 | 2.53 (1.20x) | - | - |
| **total** | 632 (316) | 59.46 | 54.46 (1.09x) | 1.69 (7.89x) | 1.59 vs 1.69 |

C files only: clang 13.38s over 316 files; goosecc compiled 316; tcc compiled 316 of them.
