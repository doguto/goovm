best of 3, milliseconds, sums of per-file best times

| program | files | goosecc -E | -E warm | clang++ -E | goosecc -fsyntax-only | warm | clang++ -fsyntax-only |
|---|---:|---:|---:|---:|---:|---:|---:|
| 7zip | 180 | 3880 | 936 | 14198 | 7170 | 5396 | 44166 |
| Bullet | 121 | 1655 | 563 | 7542 | 2485 | 1906 | 16489 |
| kimwitu++ | 14 | 298 | 108 | 1100 | 745 | 667 | 5838 |
| tramp3d-v4 | 1 | 101 | 28 | 164 | 417 | 372 | 3053 |
| **total** | 316 | 5934 | 1635 | 23004 | 10817 | 8342 | 69546 |

-E: clang++ / goosecc = 3.88 (no cache), 14.07 (warm cache)
-fsyntax-only: clang++ / goosecc = 6.43 (no cache), 8.34 (warm cache)
