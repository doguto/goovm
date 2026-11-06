best of 5 runs, wall time in ms (process start included); goovm phases in ms from its --time output

| input | LLVM insts | llc -O0 | tpde-llc | goovm cpp | goovm vs llc | goovm vs tpde | parse | export | back-end | write | llvm in-proc | goovm goose | goose back-end |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| gen-1000.bc | 167714 | 420.8 | 91.3 | 118.3 | 3.6x | 0.8x | 58.5 | 12.8 | 12.7 | 1.8 | 329.9 | 102.6 | 5.2 |
| gen-5000.bc | 810223 | 2063.2 | 464.2 | 658.7 | 3.1x | 0.7x | 358.8 | 74.3 | 63.4 | 7.4 | 1745.3 | 551.5 | 25.5 |
| gen-20000.bc | 3238227 | 8858.4 | 2043.5 | 2741.8 | 3.2x | 0.7x | 1624.2 | 310.0 | 272.1 | 41.6 | 6682.1 | 2467.2 | 100.0 |
| spass.bc | 114953 | 425.1 | 79.7 | 99.9 | 4.3x | 0.8x | 52.0 | 11.1 | 9.3 | 1.3 | 347.1 | 103.0 | 5.0 |
| typeset.bc | 142223 | 358.1 | 112.8 | 140.1 | 2.6x | 0.8x | 83.9 | 12.3 | 11.1 | 2.4 | 272.7 | 140.7 | 5.0 |
