| program | files | off | cold | warm | tcc | warm/tcc | warm/off |
|---|---:|---:|---:|---:|---:|---:|---:|
| 7zip | 32 | 96 | 120 | 87 | 86 | 0.99x | 1.11x |
| ClamAV | 98 | 452 | 660 | 400 | 457 | 1.14x | 1.13x |
| SPASS | 51 | 297 | 397 | 229 | 316 | 1.38x | 1.30x |
| consumer-typeset | 51 | 249 | 316 | 205 | 244 | 1.19x | 1.22x |
| lencod | 55 | 301 | 410 | 250 | 302 | 1.21x | 1.21x |
| mafft | 27 | 159 | 208 | 116 | 166 | 1.43x | 1.37x |
| sqlite3 | 2 | 41 | 46 | 41 | 31 | 0.75x | 1.00x |
| **total** | 316 | 1596 | 2158 | 1328 | 1602 | 1.21x | 1.20x |

(milliseconds, best of 3 per file; warm/tcc and warm/off: how many times faster warm is)

goosecc phases (ms, sum of one --time run per file):

| program | variant | preprocess | parse+sema | lowering | back-end | write |
|---|---|---:|---:|---:|---:|---:|
| 7zip | off | 27 | 8 | 6 | 8 | 2 |
| 7zip | cold | 45 | 8 | 5 | 6 | 1 |
| 7zip | warm | 17 | 8 | 5 | 6 | 2 |
| ClamAV | off | 222 | 50 | 23 | 23 | 6 |
| ClamAV | cold | 424 | 50 | 23 | 24 | 5 |
| ClamAV | warm | 149 | 51 | 23 | 24 | 6 |
| SPASS | off | 145 | 49 | 19 | 16 | 3 |
| SPASS | cold | 236 | 50 | 20 | 17 | 3 |
| SPASS | warm | 60 | 51 | 20 | 17 | 3 |
| consumer-typeset | off | 103 | 29 | 18 | 20 | 3 |
| consumer-typeset | cold | 166 | 29 | 20 | 22 | 3 |
| consumer-typeset | warm | 53 | 30 | 20 | 20 | 3 |
| lencod | off | 136 | 43 | 20 | 19 | 4 |
| lencod | cold | 235 | 44 | 20 | 20 | 4 |
| lencod | warm | 84 | 47 | 21 | 21 | 4 |
| mafft | off | 78 | 21 | 10 | 9 | 2 |
| mafft | cold | 129 | 21 | 10 | 10 | 2 |
| mafft | warm | 31 | 22 | 10 | 10 | 2 |
| sqlite3 | off | 17 | 14 | 11 | 10 | 0 |
| sqlite3 | cold | 21 | 10 | 8 | 7 | 0 |
| sqlite3 | warm | 18 | 18 | 15 | 13 | 0 |
| **total** | off | 728 | 214 | 107 | 105 | 19 |
| **total** | cold | 1257 | 212 | 107 | 107 | 19 |
| **total** | warm | 412 | 228 | 114 | 110 | 19 |
