-O0, best of 3, seconds (speed-up vs clang in parentheses)

| program | files (C++) | clang | goovm-cc | goosecc (C) | tcc (C, same files as goosecc) |
|---|---:|---:|---:|---:|---:|
| 7zip | 212 (180) | 37.97 | 36.33 (1.05x) | 0.12 (9.01x) | 0.10 vs 0.12 |
| Bullet | 121 (121) | 15.14 | 13.40 (1.13x) | - | - |
| ClamAV | 98 (0) | 4.65 | 4.16 (1.12x) | 0.61 (7.66x) | 0.59 vs 0.61 |
| SPASS | 51 (0) | 3.68 | 3.20 (1.15x) | 0.42 (8.82x) | 0.42 vs 0.42 |
| consumer-typeset | 51 (0) | 2.81 | 2.38 (1.18x) | 0.33 (8.41x) | 0.33 vs 0.33 |
| kimwitu++ | 14 (14) | 5.34 | 4.66 (1.15x) | - | - |
| lencod | 55 (0) | 3.19 | 2.80 (1.14x) | 0.40 (8.07x) | 0.37 vs 0.40 |
| mafft | 27 (0) | 1.72 | 1.51 (1.13x) | 0.21 (8.16x) | 0.22 vs 0.21 |
| sqlite3 | 2 (0) | 0.67 | 0.45 (1.48x) | 0.06 (11.36x) | 0.04 vs 0.06 |
| tramp3d-v4 | 1 (1) | 3.86 | 3.06 (1.26x) | - | - |
| **total** | 632 (316) | 79.03 | 71.96 (1.10x) | 2.14 (8.30x) | 2.08 vs 2.14 |

C files only: clang 17.81s over 316 files; goosecc compiled 316; tcc compiled 316 of them.
