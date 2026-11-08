best of 3, milliseconds, sums of per-file best times

| program | files | goosecc -E | -E warm | clang++ -E | goosecc -fsyntax-only | warm | clang++ -fsyntax-only |
|---|---:|---:|---:|---:|---:|---:|---:|
| 7zip | 180 | 2439 | 597 | 8909 | 3360 | 2166 | 28281 |
| Bullet | 121 | 983 | 327 | 4552 | 1318 | 894 | 10386 |
| kimwitu++ | 14 | 195 | 78 | 653 | 336 | 279 | 3760 |
| tramp3d-v4 | 1 | 43 | 24 | 109 | 89 | 84 | 2064 |
| **total** | 316 | 3660 | 1026 | 14223 | 5103 | 3423 | 44491 |

-E: clang++ / goosecc = 3.89 (no cache), 13.86 (warm cache)
-fsyntax-only: clang++ / goosecc = 8.72 (no cache), 13.00 (warm cache)
