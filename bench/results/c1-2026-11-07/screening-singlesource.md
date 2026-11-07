# goovm-llc correctness report

goovm-llc: `$C1/snap/c4/goovm-llc`; variants: O0

| corpus | tests | clang -O0 pass | excluded | O0 pass | O0 fail | O0 unsup | O0 fallback |
|---|---:|---:|---:|---:|---:|---:|---:|
| benchmarks | 100 | 100 | 0 | 100 | 0 | 0 | 0 |
| benchmarks-cxx | 41 | 41 | 0 | 41 | 0 | 0 | 0 |

pass includes fallback; fallback counts tests in which at least one file was compiled by LLVM's code generator (goovm-llc --fallback).

## Run times (best of 1, seconds; ratio to clang -O0)

| test | clang -O0 | O0 | O0 / clang |
|---|---:|---:|---:|
| benchmarks/BenchmarkGame/fannkuch | 4.403 | 4.366 | 0.99 |
| benchmarks/BenchmarkGame/n-body | 0.767 | 0.740 | 0.96 |
| benchmarks/BenchmarkGame/nsieve-bits | 0.644 | 0.757 | 1.18 |
| benchmarks/BenchmarkGame/partialsums | 0.097 | 0.089 | 0.92 |
| benchmarks/BenchmarkGame/puzzle | 0.510 | 0.520 | 1.02 |
| benchmarks/BenchmarkGame/recursive | 1.965 | 2.127 | 1.08 |
| benchmarks/BenchmarkGame/spectral-norm | 0.846 | 1.365 | 1.61 |
| benchmarks/BenchmarkGame/Large/fasta | 1.103 | 1.059 | 0.96 |
| benchmarks/CoyoteBench/almabench | 4.093 | 4.057 | 0.99 |
| benchmarks/CoyoteBench/huffbench | 39.578 | 39.111 | 0.99 |
| benchmarks/CoyoteBench/lpbench | 4.185 | 4.280 | 1.02 |
| benchmarks/Dhrystone/dry | 3.220 | 3.314 | 1.03 |
| benchmarks/Dhrystone/fldry | 3.978 | 3.865 | 0.97 |
| benchmarks/Linpack/linpack-pc | 9.162 | 10.236 | 1.12 |
| benchmarks/McGill/chomp | 0.811 | 0.921 | 1.13 |
| benchmarks/McGill/misr | 0.190 | 0.200 | 1.05 |
| benchmarks/McGill/queens | 2.755 | 2.695 | 0.98 |
| benchmarks/McGill/exptree | 0.001 | 0.001 | 0.86 |
| benchmarks/Misc/ReedSolomon | 6.367 | 5.873 | 0.92 |
| benchmarks/Misc/evalloop | 0.626 | 0.634 | 1.01 |
| benchmarks/Misc/fbench | 0.699 | 0.705 | 1.01 |
| benchmarks/Misc/ffbench | 0.657 | 0.633 | 0.96 |
| benchmarks/Misc/flops-1 | 1.137 | 1.417 | 1.25 |
| benchmarks/Misc/flops-2 | 1.204 | 1.029 | 0.85 |
| benchmarks/Misc/flops-3 | 1.553 | 1.471 | 0.95 |
| benchmarks/Misc/flops-4 | 3.600 | 3.472 | 0.96 |
| benchmarks/Misc/flops-5 | 4.719 | 3.450 | 0.73 |
| benchmarks/Misc/flops-6 | 4.204 | 4.192 | 1.00 |
| benchmarks/Misc/flops-7 | 2.366 | 2.389 | 1.01 |
| benchmarks/Misc/flops-8 | 4.552 | 4.536 | 1.00 |
| benchmarks/Misc/flops | 13.188 | 10.654 | 0.81 |
| benchmarks/Misc/fp-convert | 5.846 | 8.822 | 1.51 |
| benchmarks/Misc/himenobmtxpa | 2.605 | 2.684 | 1.03 |
| benchmarks/Misc/lowercase | 19.356 | 19.445 | 1.00 |
| benchmarks/Misc/mandel-2 | 1.241 | 1.256 | 1.01 |
| benchmarks/Misc/mandel | 0.478 | 0.532 | 1.11 |
| benchmarks/Misc/matmul_f64_4x4 | 4.121 | 3.623 | 0.88 |
| benchmarks/Misc/oourafft | 8.320 | 8.260 | 0.99 |
| benchmarks/Misc/perlin | 5.732 | 5.680 | 0.99 |
| benchmarks/Misc/pi | 0.911 | 0.915 | 1.00 |
| benchmarks/Misc/revertBits | 0.178 | 0.192 | 1.08 |
| benchmarks/Misc/richards_benchmark | 0.932 | 0.971 | 1.04 |
| benchmarks/Misc/salsa20 | 10.046 | 10.307 | 1.03 |
| benchmarks/Misc/whetstone | 1.661 | 1.618 | 0.97 |
| benchmarks/Misc/dt | 0.598 | 0.576 | 0.96 |
| benchmarks/Shootout/ackermann | 0.023 | 0.026 | 1.10 |
| benchmarks/Shootout/ary3 | 1.890 | 1.719 | 0.91 |
| benchmarks/Shootout/fib2 | 3.047 | 3.090 | 1.01 |
| benchmarks/Shootout/hash | 2.946 | 2.665 | 0.90 |
| benchmarks/Shootout/heapsort | 2.958 | 2.856 | 0.97 |
| benchmarks/Shootout/lists | 10.272 | 9.598 | 0.93 |
| benchmarks/Shootout/matrix | 7.144 | 7.264 | 1.02 |
| benchmarks/Shootout/methcall | 2.862 | 3.484 | 1.22 |
| benchmarks/Shootout/nestedloop | 25.078 | 24.850 | 0.99 |
| benchmarks/Shootout/objinst | 1.663 | 1.543 | 0.93 |
| benchmarks/Shootout/random | 4.013 | 3.848 | 0.96 |
| benchmarks/Shootout/sieve | 12.851 | 12.518 | 0.97 |
| benchmarks/Shootout/strcat | 0.154 | 0.155 | 1.01 |
| benchmarks/Shootout/hello | 0.001 | 0.001 | 0.99 |
| benchmarks/Stanford/Bubblesort | 0.040 | 0.039 | 0.96 |
| benchmarks/Stanford/FloatMM | 0.886 | 0.983 | 1.11 |
| benchmarks/Stanford/Oscar | 0.005 | 0.005 | 0.99 |
| benchmarks/Stanford/Perm | 0.024 | 0.019 | 0.78 |
| benchmarks/Stanford/Puzzle | 0.216 | 0.197 | 0.92 |
| benchmarks/Stanford/Queens | 0.014 | 0.014 | 1.02 |
| benchmarks/Stanford/Quicksort | 0.051 | 0.051 | 1.00 |
| benchmarks/Stanford/RealMM | 0.003 | 0.003 | 1.08 |
| benchmarks/Stanford/Towers | 0.017 | 0.019 | 1.14 |
| benchmarks/Stanford/Treesort | 0.090 | 0.091 | 1.00 |
| benchmarks/Stanford/IntMM | 0.002 | 0.002 | 1.02 |
| benchmarks/Polybench/datamining/correlation/correlation | 4.720 | 4.717 | 1.00 |
| benchmarks/Polybench/datamining/covariance/covariance | 0.002 | 0.002 | 1.00 |
| benchmarks/Polybench/linear-algebra/blas/gemm/gemm | 5.914 | 5.768 | 0.98 |
| benchmarks/Polybench/linear-algebra/blas/gemver/gemver | 0.085 | 0.087 | 1.02 |
| benchmarks/Polybench/linear-algebra/blas/gesummv/gesummv | 0.001 | 0.001 | 0.97 |
| benchmarks/Polybench/linear-algebra/blas/symm/symm | 0.002 | 0.002 | 0.95 |
| benchmarks/Polybench/linear-algebra/blas/syr2k/syr2k | 7.864 | 7.806 | 0.99 |
| benchmarks/Polybench/linear-algebra/blas/syrk/syrk | 4.276 | 4.116 | 0.96 |
| benchmarks/Polybench/linear-algebra/blas/trmm/trmm | 2.200 | 2.193 | 1.00 |
| benchmarks/Polybench/linear-algebra/kernels/2mm/2mm | 0.002 | 0.002 | 0.98 |
| benchmarks/Polybench/linear-algebra/kernels/3mm/3mm | 8.981 | 9.073 | 1.01 |
| benchmarks/Polybench/linear-algebra/kernels/atax/atax | 0.071 | 0.061 | 0.85 |
| benchmarks/Polybench/linear-algebra/kernels/bicg/bicg | 0.063 | 0.056 | 0.88 |
| benchmarks/Polybench/linear-algebra/kernels/doitgen/doitgen | 3.185 | 3.234 | 1.02 |
| benchmarks/Polybench/linear-algebra/kernels/mvt/mvt | 0.108 | 0.108 | 1.00 |
| benchmarks/Polybench/linear-algebra/solvers/cholesky/cholesky | 34.773 | 36.223 | 1.04 |
| benchmarks/Polybench/linear-algebra/solvers/durbin/durbin | 0.031 | 0.027 | 0.86 |
| benchmarks/Polybench/linear-algebra/solvers/gramschmidt/gramschmidt | 6.606 | 6.881 | 1.04 |
| benchmarks/Polybench/linear-algebra/solvers/lu/lu | 69.070 | 69.940 | 1.01 |
| benchmarks/Polybench/linear-algebra/solvers/ludcmp/ludcmp | 67.829 | 68.884 | 1.02 |
| benchmarks/Polybench/linear-algebra/solvers/trisolv/trisolv | 0.032 | 0.031 | 0.95 |
| benchmarks/Polybench/medley/deriche/deriche | 1.027 | 1.052 | 1.03 |
| benchmarks/Polybench/medley/floyd-warshall/floyd-warshall | 142.912 | 144.951 | 1.01 |
| benchmarks/Polybench/medley/nussinov/nussinov | 22.336 | 26.668 | 1.19 |
| benchmarks/Polybench/stencils/adi/adi | 15.038 | 14.815 | 0.99 |
| benchmarks/Polybench/stencils/fdtd-2d/fdtd-2d | 10.804 | 10.659 | 0.99 |
| benchmarks/Polybench/stencils/heat-3d/heat-3d | 14.731 | 14.846 | 1.01 |
| benchmarks/Polybench/stencils/jacobi-1d/jacobi-1d | 0.009 | 0.010 | 1.15 |
| benchmarks/Polybench/stencils/jacobi-2d/jacobi-2d | 12.341 | 12.814 | 1.04 |
| benchmarks/Polybench/stencils/seidel-2d/seidel-2d | 44.728 | 45.385 | 1.01 |
| benchmarks-cxx/Misc-C++/bigfib | 0.668 | 0.672 | 1.01 |
| benchmarks-cxx/Misc-C++/mandel-text | 2.349 | 2.402 | 1.02 |
| benchmarks-cxx/Misc-C++/oopack_v1p8 | 0.478 | 0.522 | 1.09 |
| benchmarks-cxx/Misc-C++/stepanov_container | 6.788 | 6.598 | 0.97 |
| benchmarks-cxx/Misc-C++/stepanov_v1p2 | 76.778 | 74.288 | 0.97 |
| benchmarks-cxx/Misc-C++/Large/ray | 4.364 | 4.713 | 1.08 |
| benchmarks-cxx/Misc-C++/Large/sphereflake | 7.907 | 7.828 | 0.99 |
| benchmarks-cxx/Misc-C++-EH/spirit | 30.688 | 32.699 | 1.07 |
| benchmarks-cxx/Shootout-C++/ackermann | 5.930 | 6.732 | 1.14 |
| benchmarks-cxx/Shootout-C++/ary | 0.134 | 0.123 | 0.92 |
| benchmarks-cxx/Shootout-C++/ary2 | 0.138 | 0.126 | 0.92 |
| benchmarks-cxx/Shootout-C++/ary3 | 6.543 | 4.325 | 0.66 |
| benchmarks-cxx/Shootout-C++/fibo | 2.714 | 3.195 | 1.18 |
| benchmarks-cxx/Shootout-C++/hash | 0.476 | 0.485 | 1.02 |
| benchmarks-cxx/Shootout-C++/hash2 | 3.669 | 3.589 | 0.98 |
| benchmarks-cxx/Shootout-C++/heapsort | 3.030 | 3.030 | 1.00 |
| benchmarks-cxx/Shootout-C++/lists | 8.346 | 7.743 | 0.93 |
| benchmarks-cxx/Shootout-C++/lists1 | 0.333 | 0.334 | 1.00 |
| benchmarks-cxx/Shootout-C++/matrix | 6.517 | 6.928 | 1.06 |
| benchmarks-cxx/Shootout-C++/methcall | 6.142 | 5.922 | 0.96 |
| benchmarks-cxx/Shootout-C++/moments | 0.287 | 0.275 | 0.96 |
| benchmarks-cxx/Shootout-C++/nestedloop | 25.243 | 25.304 | 1.00 |
| benchmarks-cxx/Shootout-C++/objinst | 2.626 | 2.538 | 0.97 |
| benchmarks-cxx/Shootout-C++/random | 4.079 | 4.011 | 0.98 |
| benchmarks-cxx/Shootout-C++/sieve | 2.749 | 2.607 | 0.95 |
| benchmarks-cxx/Shootout-C++/strcat | 0.079 | 0.079 | 1.00 |
| benchmarks-cxx/Shootout-C++/hello | 0.002 | 0.002 | 1.01 |
| benchmarks-cxx/Shootout-C++/reversefile | 0.002 | 0.002 | 0.93 |
| benchmarks-cxx/Shootout-C++/spellcheck | 0.002 | 0.002 | 1.18 |
| benchmarks-cxx/Shootout-C++/sumcol | 0.002 | 0.002 | 1.01 |
| benchmarks-cxx/Shootout-C++/wc | 0.002 | 0.002 | 1.14 |
| benchmarks-cxx/Shootout-C++/wordfreq | 0.002 | 0.002 | 1.02 |
| benchmarks-cxx/Shootout-C++/EH/except | 0.152 | 0.158 | 1.03 |
| benchmarks-cxx/Adobe-C++/functionobjects | 5.503 | 5.314 | 0.97 |
| benchmarks-cxx/Adobe-C++/loop_unroll | 12.846 | 12.701 | 0.99 |
| benchmarks-cxx/Adobe-C++/simple_types_constant_folding | 12.195 | 12.047 | 0.99 |
| benchmarks-cxx/Adobe-C++/simple_types_loop_invariant | 4.707 | 3.944 | 0.84 |
| benchmarks-cxx/Adobe-C++/stepanov_abstraction | 62.060 | 61.317 | 0.99 |
| benchmarks-cxx/Adobe-C++/stepanov_vector | 37.356 | 36.582 | 0.98 |
| benchmarks-cxx/CoyoteBench/fftbench | 2.025 | 2.199 | 1.09 |
| benchmarks-cxx/SmallPT/smallpt | 10.198 | 10.469 | 1.03 |
| geometric mean (clang -O0 >= 50 ms) | | | 1.001 |

