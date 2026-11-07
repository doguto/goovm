| program | files | off | cold | warm | tcc | clang | warm/tcc | warm/off |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 7zip | 32 | 110 | 127 | 98 | 96 | 1056 | 0.98x | 1.12x |
| ClamAV | 98 | 538 | 742 | 461 | 533 | 4287 | 1.16x | 1.17x |
| SPASS | 51 | 368 | 458 | 273 | 380 | 3332 | 1.39x | 1.35x |
| consumer-typeset | 51 | 302 | 354 | 241 | 302 | 2618 | 1.25x | 1.25x |
| lencod | 55 | 360 | 453 | 291 | 346 | 3017 | 1.19x | 1.23x |
| mafft | 27 | 198 | 253 | 141 | 210 | 1618 | 1.49x | 1.41x |
| sqlite3 | 2 | 54 | 57 | 52 | 38 | 594 | 0.74x | 1.04x |
| **total** | 316 | 1931 | 2444 | 1558 | 1904 | 16522 | 1.22x | 1.24x |

(milliseconds, best of 5 per file; warm/tcc and warm/off: how many times faster warm is)

goosecc phases (ms, sum of one --time run per file):

| program | variant | preprocess | parse+sema | lowering | back-end | write |
|---|---|---:|---:|---:|---:|---:|
| 7zip | off | 32 | 10 | 7 | 8 | 1 |
| 7zip | cold | 50 | 10 | 7 | 8 | 1 |
| 7zip | warm | 21 | 10 | 7 | 8 | 2 |
| ClamAV | off | 268 | 63 | 30 | 30 | 5 |
| ClamAV | cold | 467 | 62 | 29 | 29 | 4 |
| ClamAV | warm | 185 | 62 | 30 | 29 | 5 |
| SPASS | off | 185 | 66 | 25 | 23 | 3 |
| SPASS | cold | 271 | 62 | 24 | 22 | 3 |
| SPASS | warm | 82 | 64 | 25 | 23 | 3 |
| consumer-typeset | off | 130 | 38 | 25 | 27 | 3 |
| consumer-typeset | cold | 182 | 38 | 24 | 27 | 3 |
| consumer-typeset | warm | 70 | 45 | 25 | 27 | 3 |
| lencod | off | 169 | 55 | 26 | 26 | 3 |
| lencod | cold | 262 | 57 | 25 | 25 | 3 |
| lencod | warm | 101 | 56 | 25 | 26 | 3 |
| mafft | off | 98 | 27 | 15 | 13 | 2 |
| mafft | cold | 166 | 27 | 13 | 13 | 2 |
| mafft | warm | 42 | 27 | 14 | 13 | 2 |
| sqlite3 | off | 18 | 14 | 11 | 10 | 0 |
| sqlite3 | cold | 23 | 13 | 10 | 10 | 0 |
| sqlite3 | warm | 17 | 14 | 10 | 10 | 0 |
| **total** | off | 900 | 274 | 139 | 137 | 19 |
| **total** | cold | 1422 | 268 | 132 | 134 | 16 |
| **total** | warm | 518 | 279 | 136 | 136 | 18 |

Builds (all 316 files in order, one run each): without the cache 1.93 s; with one cache starting empty, first 1.75 s, second 1.75 s, third 1.51 s; the cache then holds 1105 files, 116.0 MB
