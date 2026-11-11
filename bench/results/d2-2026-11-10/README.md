# D2 measurements and verification (2026-11-10/11)

goosecc's C++ front end, second stage: templates, overload resolution, the
constant evaluator. The design is in frontend-goose/DESIGN.md, section 14.
Built from the D2 branch at the commit that adds this directory, merged with
main eff232e (the codegen agent's D3 work). The machine (4 cores) was shared
with other jobs.

| file | what |
|---|---|
| `bench_cxx.{md,json}` | `frontend-goose/tests/bench_cxx.py -n 3`: goosecc `-E` / `-fsyntax-only` (no header cache, warm) against clang++-20 on the 316 CTMark C++ files |
| `checks/decls_cxx.log` | `cmp_decls_cxx.py --corpus cxx`: 8,648 declarations matched, 0 wrong, 51 missing (mostly lambdas `$_N`) |
| `checks/suite_cxx.md` | (empty: `suite_goosecc.py --corpus cxx` names no corpus `cxx`; see the codegen agent's runs for the C++ programs) |

Speed (milliseconds, best of 3):

| | goosecc | clang++-20 | ratio |
|---|---:|---:|---:|
| `-E`, no cache | 5,934 | 23,004 | 3.9 |
| `-E`, warm header cache | 1,635 | 23,004 | 14.1 |
| `-fsyntax-only`, no cache | 10,817 | 69,546 | 6.4 |
| `-fsyntax-only`, warm | 8,342 | 69,546 | 8.3 |

D1 had 8.7 and 13.0 for `-fsyntax-only`. The difference is the work D1
skipped: class and function templates are now instantiated (member bodies
on use, at the end of the translation unit), overloads are resolved, and
constant expressions are evaluated.

Other checks run during D2 (logs not kept here; commands in the report, §6):

- `tests/run.py --goosecc`: 170/170. That is 85 programs, each with and without `-g`, including tests/cxx_d2/01..08.
- `cmp_bins.py --load ref_c.json`: every C output (`-E`, AST, layout, `-c`, `-c -g` on 2,357 files) is byte-identical to the pre-D2 build.
- `cmp_syntax.py` (C corpora): no false errors.
- `layout_check.py` (C, then `--corpus cxx`): 0 mismatches. The C++ run made 330,728 assertions over 423 files.
- C++ corpus `-fsyntax-only` (423 files): 0 errors and 0 crashes, with errors inside instantiations reported (the default since D2).
- libstdc++ headers alone (`--corpus cxx-hdrs`, 678 runs): 572 accepted. The 106 others are 28 `#error` for C++98, 3 `<coroutine>` without `-fcoroutines`, and 75 `gnu++20` runs that need concepts (`requires`, not implemented yet).
- The clang Sema oracle (scratchpad `bin/sema_oracle.py`). It covers clang 20.1.2's `clang/test/{SemaCXX,SemaTemplate,CXX,Parser}`: 2,649 files and 2,846 `-verify` runs. A run passes when goosecc's error lines are exactly the expected-error lines.
  - Runs passing: 720 (25.3%).
  - Expected-error lines reported: 2,299 of 20,866 (11.0%).
  - False-error lines: 3,107, in 703 runs. Most come from features not done yet: concepts, deducing this, MS extensions, and traits and diagnostics still missing.
  - Runs that expect no errors and are accepted cleanly: 664 of 827.
  - Crashes and timeouts: 0. The first run had 34.
