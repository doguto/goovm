-O0, best of 3, seconds (speed-up vs clang in parentheses)

| program | files (C++) | clang | goovm-cc | goosecc (C) | tcc (C, same files as goosecc) |
|---|---:|---:|---:|---:|---:|
| 7zip | 212 (180) | 29.48 | 28.62 (1.03x) | 0.09 (8.86x) | 0.08 vs 0.09 |
| Bullet | 121 (121) | 11.21 | 10.03 (1.12x) | - | - |
| ClamAV | 98 (0) | 3.59 | 3.22 (1.12x) | 0.45 (7.90x) | 0.45 vs 0.45 |
| SPASS | 51 (0) | 2.70 | 2.34 (1.15x) | 0.27 (10.04x) | 0.32 vs 0.27 |
| consumer-typeset | 51 (0) | 2.09 | 1.77 (1.18x) | 0.23 (9.14x) | 0.25 vs 0.23 |
| kimwitu++ | 14 (14) | 3.94 | 3.72 (1.06x) | - | - |
| lencod | 55 (0) | 2.39 | 2.18 (1.10x) | 0.28 (8.60x) | 0.29 vs 0.28 |
| mafft | 27 (0) | 1.28 | 1.10 (1.16x) | 0.13 (9.73x) | 0.17 vs 0.13 |
| sqlite3 | 2 (0) | 0.49 | 0.32 (1.55x) | 0.04 (11.72x) | 0.03 vs 0.04 |
| tramp3d-v4 | 1 (1) | 2.69 | 2.53 (1.06x) | - | - |
| **total** | 632 (316) | 59.86 | 55.82 (1.07x) | 1.50 (8.93x) | 1.59 vs 1.50 |

C files only: clang 13.37s over 316 files; goosecc compiled 316; tcc compiled 316 of them.
