| input | cpp | cpp-E6 | goose | goose-E1 | cpp / goose | cpp-E6 / goose | identical |
|---|---:|---:|---:|---:|---:|---:|---|
| gen-5000 | 60371 | 30778 | 26454 | 49041 | 2.28x | 1.16x | yes |
| gen-20000 | 250259 | 120849 | 104610 | 188085 | 2.39x | 1.16x | yes |
| spass | 9318 | 5648 | 4465 | 7499 | 2.09x | 1.26x | yes |
| typeset | 11090 | 5820 | 4911 | 8482 | 2.26x | 1.19x | yes |

back-end phase only (us, best of 7); the same goovm-llc front end and exporter for all
