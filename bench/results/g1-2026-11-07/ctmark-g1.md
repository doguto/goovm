| program | files | off | cold | warm | tcc | clang | warm/tcc | warm/off |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 7zip | 32 | 79 | 100 | 70 | 83 | 852 | 1.18x | 1.12x |
| ClamAV | 98 | 417 | 622 | 364 | 460 | 3486 | 1.27x | 1.15x |
| SPASS | 51 | 291 | 400 | 208 | 320 | 2723 | 1.54x | 1.40x |
| consumer-typeset | 51 | 230 | 302 | 185 | 250 | 2158 | 1.35x | 1.24x |
| lencod | 55 | 270 | 384 | 214 | 293 | 2499 | 1.37x | 1.26x |
| mafft | 27 | 143 | 209 | 103 | 172 | 1284 | 1.67x | 1.39x |
| sqlite3 | 2 | 49 | 48 | 44 | 29 | 451 | 0.67x | 1.11x |
| **total** | 316 | 1479 | 2067 | 1188 | 1607 | 13453 | 1.35x | 1.24x |

(milliseconds, best of 3 per file; warm/tcc and warm/off: how many times faster warm is)

goosecc phases (ms, sum of one --time run per file):

| program | variant | preprocess | parse+sema | lowering | back-end | write |
|---|---|---:|---:|---:|---:|---:|
| 7zip | off | 30 | 7 | 6 | 6 | 2 |
| 7zip | cold | 45 | 12 | 6 | 6 | 1 |
| 7zip | warm | 19 | 8 | 6 | 6 | 2 |
| ClamAV | off | 234 | 54 | 28 | 24 | 6 |
| ClamAV | cold | 411 | 82 | 28 | 25 | 5 |
| ClamAV | warm | 171 | 46 | 29 | 25 | 6 |
| SPASS | off | 164 | 57 | 23 | 18 | 4 |
| SPASS | cold | 234 | 90 | 24 | 18 | 3 |
| SPASS | warm | 73 | 40 | 24 | 19 | 3 |
| consumer-typeset | off | 119 | 34 | 25 | 24 | 3 |
| consumer-typeset | cold | 167 | 53 | 24 | 25 | 3 |
| consumer-typeset | warm | 64 | 30 | 26 | 24 | 3 |
| lencod | off | 143 | 46 | 22 | 21 | 4 |
| lencod | cold | 225 | 72 | 23 | 22 | 3 |
| lencod | warm | 85 | 32 | 22 | 21 | 4 |
| mafft | off | 86 | 23 | 12 | 11 | 2 |
| mafft | cold | 152 | 41 | 13 | 15 | 3 |
| mafft | warm | 37 | 16 | 13 | 11 | 2 |
| sqlite3 | off | 16 | 12 | 10 | 9 | 0 |
| sqlite3 | cold | 20 | 13 | 11 | 9 | 0 |
| sqlite3 | warm | 13 | 11 | 10 | 8 | 0 |
| **total** | off | 792 | 233 | 126 | 113 | 21 |
| **total** | cold | 1255 | 363 | 130 | 120 | 19 |
| **total** | warm | 462 | 183 | 130 | 115 | 20 |
