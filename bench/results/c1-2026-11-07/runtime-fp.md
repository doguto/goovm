# FP-heavy SingleSource benchmarks

Interleaved best of 3 (`$C1/tsuite.py 3`): clang -O0, the A3 back-end (column O0) and the
C1 back-end, each built by `tests/suite.py` (outputs verified).

## Final build (6690a17)

| test | clang -O0 | O0 | ratio | final2 | ratio |
| benchmarks/BenchmarkGame/n-body | 0.802 | 0.781 | 0.97 | 0.793 | 0.99 |
| benchmarks/BenchmarkGame/spectral-norm | 0.862 | 1.408 | 1.63 | 0.455 | 0.53 |
| benchmarks/Linpack/linpack-pc | 9.270 | 10.535 | 1.14 | 9.081 | 0.98 |
| benchmarks/Misc/flops-1 | 1.180 | 1.315 | 1.11 | 1.264 | 1.07 |
| benchmarks/Misc/flops-2 | 1.323 | 1.071 | 0.81 | 1.073 | 0.81 |
| benchmarks/Misc/flops-3 | 1.586 | 1.540 | 0.97 | 1.529 | 0.96 |
| benchmarks/Misc/flops-4 | 3.720 | 3.625 | 0.97 | 0.616 | 0.17 |
| benchmarks/Misc/flops-5 | 4.939 | 3.639 | 0.74 | 1.112 | 0.23 |
| benchmarks/Misc/flops-6 | 4.395 | 4.387 | 1.00 | 1.081 | 0.25 |
| benchmarks/Misc/flops-7 | 2.545 | 2.562 | 1.01 | 0.662 | 0.26 |
| benchmarks/Misc/flops-8 | 4.774 | 4.597 | 0.96 | 1.111 | 0.23 |
| benchmarks/Misc/flops | 11.455 | 10.609 | 0.93 | 5.025 | 0.44 |
| benchmarks/Misc/fp-convert | 5.923 | 9.036 | 1.53 | 4.558 | 0.77 |
| benchmarks/Misc/mandel-2 | 1.290 | 1.462 | 1.13 | 1.294 | 1.00 |
| benchmarks/Misc/mandel | 0.499 | 0.549 | 1.10 | 0.317 | 0.63 |
| benchmarks/Misc/matmul_f64_4x4 | 4.127 | 4.034 | 0.98 | 3.565 | 0.86 |
| benchmarks/Misc/perlin | 5.923 | 5.872 | 0.99 | 5.069 | 0.86 |
| benchmarks-cxx/Misc-C++/Large/ray | 4.589 | 5.228 | 1.14 | 4.428 | 0.96 |
| benchmarks-cxx/CoyoteBench/fftbench | 2.248 | 3.150 | 1.40 | 2.051 | 0.91 |
| benchmarks-cxx/SmallPT/smallpt | 10.175 | 10.778 | 1.06 | 10.084 | 0.99 |

## A wider sample with the build before the frame-address GEPs were removed (f7c8635)

The frame-address GEPs changed no run time measurably (see README.md); this table has
more programs.

| test | clang -O0 | O0 | ratio | final | ratio |
| benchmarks/BenchmarkGame/n-body | 0.739 | 0.735 | 1.00 | 0.764 | 1.03 |
| benchmarks/BenchmarkGame/partialsums | 0.084 | 0.088 | 1.05 | 0.088 | 1.05 |
| benchmarks/BenchmarkGame/spectral-norm | 0.842 | 1.380 | 1.64 | 0.444 | 0.53 |
| benchmarks/CoyoteBench/almabench | 4.174 | 4.113 | 0.99 | 4.041 | 0.97 |
| benchmarks/CoyoteBench/huffbench | 39.478 | 39.857 | 1.01 | 40.187 | 1.02 |
| benchmarks/Linpack/linpack-pc | 9.267 | 10.511 | 1.13 | 9.192 | 0.99 |
| benchmarks/Misc/fbench | 0.700 | 0.705 | 1.01 | 0.691 | 0.99 |
| benchmarks/Misc/ffbench | 0.648 | 0.631 | 0.97 | 0.638 | 0.98 |
| benchmarks/Misc/flops-1 | 1.169 | 1.225 | 1.05 | 1.231 | 1.05 |
| benchmarks/Misc/flops-2 | 1.315 | 1.050 | 0.80 | 1.053 | 0.80 |
| benchmarks/Misc/flops-3 | 1.570 | 1.539 | 0.98 | 1.528 | 0.97 |
| benchmarks/Misc/flops-4 | 3.695 | 3.609 | 0.98 | 0.615 | 0.17 |
| benchmarks/Misc/flops-5 | 4.898 | 3.607 | 0.74 | 1.133 | 0.23 |
| benchmarks/Misc/flops-6 | 4.381 | 4.373 | 1.00 | 1.057 | 0.24 |
| benchmarks/Misc/flops-7 | 2.507 | 2.526 | 1.01 | 0.659 | 0.26 |
| benchmarks/Misc/flops-8 | 4.756 | 4.636 | 0.97 | 1.106 | 0.23 |
| benchmarks/Misc/flops | 13.751 | 10.713 | 0.78 | 5.004 | 0.36 |
| benchmarks/Misc/fp-convert | 5.863 | 8.878 | 1.51 | 4.397 | 0.75 |
| benchmarks/Misc/mandel-2 | 1.300 | 1.461 | 1.12 | 1.292 | 0.99 |
| benchmarks/Misc/mandel | 0.495 | 0.542 | 1.10 | 0.307 | 0.62 |
| benchmarks/Misc/matmul_f64_4x4 | 4.044 | 3.959 | 0.98 | 3.528 | 0.87 |
| benchmarks/Misc/oourafft | 8.228 | 8.284 | 1.01 | 8.128 | 0.99 |
| benchmarks/Misc/perlin | 5.834 | 5.881 | 1.01 | 5.034 | 0.86 |
| benchmarks/Misc/whetstone | 1.658 | 1.637 | 0.99 | 1.648 | 0.99 |
| benchmarks/Stanford/FloatMM | 0.890 | 0.925 | 1.04 | 0.897 | 1.01 |
| benchmarks/Polybench/linear-algebra/blas/gemm/gemm | 6.134 | 5.856 | 0.95 | 5.772 | 0.94 |
| benchmarks/Polybench/linear-algebra/kernels/2mm/2mm | 0.002 | 0.002 | 0.97 | 0.002 | 0.99 |
| benchmarks/Polybench/linear-algebra/solvers/cholesky/cholesky | 36.514 | 36.917 | 1.01 | 36.312 | 0.99 |
| benchmarks/Polybench/medley/floyd-warshall/floyd-warshall | 148.202 | 148.558 | 1.00 | 148.020 | 1.00 |
| benchmarks/Polybench/stencils/fdtd-2d/fdtd-2d | 11.100 | 11.327 | 1.02 | 10.939 | 0.99 |
| benchmarks/Polybench/stencils/jacobi-2d/jacobi-2d | 12.850 | 13.226 | 1.03 | 12.742 | 0.99 |
| benchmarks/Polybench/stencils/seidel-2d/seidel-2d | 45.399 | 45.656 | 1.01 | 45.468 | 1.00 |
| benchmarks-cxx/Misc-C++/Large/ray | 4.522 | 5.256 | 1.16 | 4.450 | 0.98 |
| benchmarks-cxx/Misc-C++/Large/sphereflake | 7.981 | 8.184 | 1.03 | 7.883 | 0.99 |
| benchmarks-cxx/CoyoteBench/fftbench | 2.277 | 3.135 | 1.38 | 1.983 | 0.87 |
| benchmarks-cxx/SmallPT/smallpt | 10.087 | 10.669 | 1.06 | 9.981 | 0.99 |
