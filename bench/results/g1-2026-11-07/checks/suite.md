# goosecc correctness report

goosecc: `/tmp/claude-0/-home-user-goovm/593b2907-8413-508c-8bdb-c68ef6e66f6e/scratchpad/work/g1/final/goosecc`; variants: O0, g

| corpus | tests | clang -O0 pass | excluded | O0 pass | O0 fail | O0 error | g pass | g fail | g error |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| torture | 1427 | 1427 | 0 | 1427 | 0 | 0 | 1427 | 0 | 0 |
| ieee | 57 | 57 | 0 | 57 | 0 | 0 | 57 | 0 | 0 |
| builtins | 54 | 48 | 6 | 48 | 0 | 0 | 48 | 0 | 0 |
| unittests | 129 | 129 | 0 | 129 | 0 | 0 | 129 | 0 | 0 |
| regression | 37 | 37 | 0 | 37 | 0 | 0 | 37 | 0 | 0 |
| benchmarks | 100 | 100 | 0 | 100 | 0 | 0 | 100 | 0 | 0 |
| ctmark | 6 | 6 | 0 | 6 | 0 | 0 | 6 | 0 | 0 |
| unittests-cxx | 35 | 0 | 35 | 0 | 0 | 0 | 0 | 0 | 0 |
| regression-cxx | 31 | 0 | 31 | 0 | 0 | 0 | 0 | 0 | 0 |
| benchmarks-cxx | 41 | 0 | 41 | 0 | 0 | 0 | 0 | 0 | 0 |
| ctmark-cxx | 4 | 0 | 4 | 0 | 0 | 0 | 0 | 0 | 0 |

## builtins: excluded (do not pass with clang-20 -O0)

- `builtins/abs-3` build: link failed:
- `builtins/fprintf` build: link failed:
- `builtins/fputs` build: link failed:
- `builtins/memops-asm` fail: exit status -6
- `builtins/printf` build: link failed:
- `builtins/strstr-asm` fail: exit status -6

## unittests-cxx: excluded (do not pass with clang-20 -O0)

- `unittests-cxx/2006-12-04-DynAllocAndRestore` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/DefaultInitDynArrays` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/block-byref-cxxobj-test` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/block-call-r7674133` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/block-copied-in-cxxobj-1` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/block-copied-in-cxxobj` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/conditional-gnu-ext-cxx` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/initp1` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/matrix-types-spec` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/member-function-pointers` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/stmtexpr` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/C++11/stdthreadbug` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/EH/cleanup-1` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/EH/cleanup-2` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/EH/cleanup-3` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/EH/filter-1` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/EH/filter-2` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/EH/rethrow-1` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/EH/rethrow-2` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/EH/simple-1` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/EH/simple-2` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/SignlessTypes/cast2` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/SignlessTypes/Large/cast` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/Vectorizer/any-of` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/Vectorizer/argmin-argmax-fp` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/Vectorizer/argmin-argmax-int` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/Vectorizer/early-exit` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/Vectorizer/find-last` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/Vectorizer/fmax-reduction` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/Vectorizer/gcc-loops` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/Vectorizer/recurrences` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/Vectorizer/runtime-checks` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/Vectorizer/VPlanNativePath/outer-loop-vect` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/X86/dyn_stack_alloc_realign` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `unittests-cxx/X86/dyn_stack_alloc_realign2` fail: harness: 'Namespace' object has no attribute 'clangxx'

## regression-cxx: excluded (do not pass with clang-20 -O0)

- `regression-cxx/2003-05-14-array-init` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/2003-05-14-expr_stmt` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/2003-06-08-BaseType` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/2003-06-08-VirtualFunctions` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/2003-06-13-Crasher` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/2003-08-20-EnumSizeProblem` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/2003-09-29-NonPODsByValue` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/2008-01-29-ParamAliasesReturn` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/2011-03-28-Bitfield` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/BuiltinTypeInfo` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/custom_section_members` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/fixups` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/global_ctor` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/global_type` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/ofstream_ctor` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/pointer_member` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/pointer_method` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/pointer_method2` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/short_circuit_dtor` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/EH/ConditionalExpr` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/EH/class_hierarchy` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/EH/ctor_dtor_count-2` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/EH/ctor_dtor_count` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/EH/dead_try_block` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/EH/exception_spec_test` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/EH/function_try_block` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/EH/inlined_cleanup` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/EH/recursive-throw` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/EH/simple_rethrow` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/EH/simple_throw` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `regression-cxx/EH/throw_rethrow_test` fail: harness: 'Namespace' object has no attribute 'clangxx'

## benchmarks-cxx: excluded (do not pass with clang-20 -O0)

- `benchmarks-cxx/Misc-C++/bigfib` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Misc-C++/mandel-text` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Misc-C++/oopack_v1p8` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Misc-C++/stepanov_container` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Misc-C++/stepanov_v1p2` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Misc-C++/Large/ray` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Misc-C++/Large/sphereflake` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Misc-C++-EH/spirit` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/ackermann` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/ary` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/ary2` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/ary3` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/fibo` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/hash` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/hash2` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/heapsort` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/lists` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/lists1` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/matrix` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/methcall` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/moments` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/nestedloop` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/objinst` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/random` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/sieve` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/strcat` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/hello` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/reversefile` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/spellcheck` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/sumcol` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/wc` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/wordfreq` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Shootout-C++/EH/except` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Adobe-C++/functionobjects` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Adobe-C++/loop_unroll` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Adobe-C++/simple_types_constant_folding` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Adobe-C++/simple_types_loop_invariant` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Adobe-C++/stepanov_abstraction` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/Adobe-C++/stepanov_vector` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/CoyoteBench/fftbench` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `benchmarks-cxx/SmallPT/smallpt` fail: harness: 'Namespace' object has no attribute 'clangxx'

## ctmark-cxx: excluded (do not pass with clang-20 -O0)

- `ctmark-cxx/7zip` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `ctmark-cxx/Bullet` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `ctmark-cxx/kimwitu++` fail: harness: 'Namespace' object has no attribute 'clangxx'
- `ctmark-cxx/tramp3d-v4` fail: harness: 'Namespace' object has no attribute 'clangxx'

