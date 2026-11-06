n = 2,000,000 instructions, best of 5 runs (ms), peak RSS (MB)

| variant | build | fold | dce | walk | total | peak MB | checksum |
|---|---:|---:|---:|---:|---:|---:|---|
| goose | 74 | 43 | 73 | 15 | 210 | 136 | 2651368052950166711 |
| c++ idx | 136 | 32 | 83 | 15 | 269 | 162 | 2651368052950166711 |
| c++ idx + reserve | 73 | 35 | 90 | 15 | 214 | 139 | 2651368052950166711 |
| c++ ptr (LLVM style) | 164 | 83 | 207 | 50 | 505 | 269 | 2651368052950166711 |
