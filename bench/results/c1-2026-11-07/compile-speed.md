# Back-end compile speed, A3 (c96510d) against C1 (6690a17)

`bench/backend/time_backend.py --goovm <A3> --goovm <C1> -n 11` (best of 11; (0) A3, (1) C1):

| input | gir insts | backend ms (0) | export ms (0) | backend ms (1) | export ms (1) |
|---|---:|---:|---:|---:|---:|
| gen-20000.bc | 3205263 | 223.3 | 219.1 | 228.0 | 218.2 |
| spass.bc | 114371 | 12.0 | 9.4 | 12.2 | 9.5 |
| 000_tramp3d-v4.O0.bc | 159462 | 26.7 | 27.5 | 27.3 | 27.0 |

(0) $C1/build-base/tools/goovm-llc/goovm-llc

(1) $C1/build-final2/tools/goovm-llc/goovm-llc

Interleaved best of 31 of the back-end phase on gen-20000 (`$C1/tbe.py 31`), which also
measured the frame-address GEPs that were removed again:

| build | back-end | / A3 |
|---|---:|---:|
| A3 | 217.9 ms | 1.000 |
| C1 (final) | 222.5 ms | 1.021 |
| C1 with the frame-address GEPs | 230.5 ms | 1.058 |

spass: A3 12.1 ms, C1 12.2 ms (1.009); tramp3d-v4: 27.4 ms, 27.5 ms (1.004), interleaved best of 21.
