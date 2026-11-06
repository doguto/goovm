# goovm-llc --time phases, best of 7, ms: (0) = A1 (commit 5d17665), (1) = A2

| input | gir insts | backend ms (0) | export ms (0) | backend ms (1) | export ms (1) |
|---|---:|---:|---:|---:|---:|
| gen-20000.bc | 3205263 | 179.9 | 448.8 | 208.9 | 215.1 |
| spass.bc | 114371 | 8.4 | 17.9 | 11.1 | 8.8 |
| typeset.bc | 119262 | 9.5 | 18.1 | 9.9 | 9.7 |


# TPDE (tpde-llc --time-trace), best of 7, ms

```
gen-20000.bc Compile=506.5 Total Compile=506.5 Total Parse IR=1949.2 Total TPDE_Analysis=67.8 Total TPDE_CodeGen=276.0 Total TPDE_EmitObj=11.4 Total TPDE_GlobalGen=0.5 Total TPDE_Prepass=129.5
spass.bc Compile=24.9 Total Compile=24.9 Total Parse IR=70.3 Total TPDE_Analysis=3.9 Total TPDE_CodeGen=12.4 Total TPDE_EmitObj=0.9 Total TPDE_GlobalGen=0.2 Total TPDE_Prepass=3.7
typeset.bc Compile=16.7 Total Compile=16.7 Total Parse IR=91.9 Total TPDE_Analysis=2.8 Total TPDE_CodeGen=9.8 Total TPDE_EmitObj=0.5 Total TPDE_GlobalGen=0.3 Total TPDE_Prepass=2.8
```
