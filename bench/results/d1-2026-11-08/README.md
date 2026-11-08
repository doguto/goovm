# D1 measurements and verification (2026-11-08)

goosecc's C++ front end, first stage (frontend-goose/DESIGN.md, section 13),
built from the final D1 sources (`frontend-goose/build.sh`), against the
build before D1 (d77aa81). The machine (4 cores) was shared with another
job (load average about 2.2).

| file | what |
|---|---|
| `bench_cxx.{md,json}` | `frontend-goose/tests/bench_cxx.py -n 3`: goosecc `-E` / `-fsyntax-only` (no header cache, warm) against clang++-20 on the 316 CTMark C++ files |
| `c_speed.{txt,py}` | goosecc `-c` on the CTMark C files, D1 against d77aa81 interleaved, best of 3; a one-line file, best of 300 |
| `checks/bins.log` | `cmp_bins.py --ref d77aa81`: `-E`, `--dump-ast`, `--layout-check`, `-c`, `-c -g` of the 2,357 C files identical |
| `checks/cmp_{E,syntax,ast}_c.log`, `checks/layout_c.log` | the C front-end oracles: unchanged (no difference, no false error, no mismatch) |
| `checks/cache_check_c.log`, `checks/pcache_c.log`, `checks/adversarial.log` | header and parse cache checks: 44,783 runs, 9,428 runs (2,960 replays), 17/17; no failure |
| `checks/suite_c.md` | `tests/suite_goosecc.py --variants O0,g` on the C corpora: 1,804 tests, no failure |
| `checks/run.log` | `tests/run.py --goosecc`: 124/124 (54 C programs and the 8 of `tests/cxx_d1/`, each with and without `-g`) |
| `checks/cmp_E_cxx.log` | `cmp_E.py --corpus cxx,cxx-hdrs`: 423/423 and 647/647 identical to clang++-20 -E |
| `checks/cmp_syntax_cxx.log` | `cmp_syntax.py --corpus cxx,cxx-hdrs`: 423/423 accepted; headers 572/647 (the 75 false errors are `-std=gnu++20` runs of headers with concepts) |
| `checks/layout_cxx.log` | `layout_check.py --corpus cxx`: 423/423, 307,457 assertions, 0 mismatches |
| `checks/decls_cxx.log` | `cmp_decls_cxx.py --corpus cxx`: 8,528 declarations matched, 171 missing (in templates), 0 wrong |
| `checks/cache_check_cxx.log` | `cache_check.py --corpus cxx --modes E,layout`: 423/423 identical, 3,384 runs, no failure |
| `checks/suite_cxx.md` | `suite_goosecc.py --variants O0,g` on the C++ corpora: 28 of 111 pass (both variants), 0 wrong outputs, the rest stop with a D1 "not supported" error |
