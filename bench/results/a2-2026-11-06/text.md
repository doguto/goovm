# .text bytes

llc = llc-20 -O0 -relocation-model=pic; k.bc = bench/codequal/kernels.c at -O0

| input | llc -O0 | TPDE | goovm A1 | goovm A2 | A2 / llc |
|---|---:|---:|---:|---:|---:|
| gen-20000.bc | 10457901 | 12463678 | 48124970 | 10465581 | 1.001 |
| spass.bc | 515668 | 604813 | 1478415 | 525655 | 1.019 |
| typeset.bc | 483283 | 521176 | 1836072 | 516953 | 1.070 |
| k.bc | 2578 | 2980 | 10818 | 2705 | 1.049 |
