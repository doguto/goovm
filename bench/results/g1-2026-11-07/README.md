# G1 measurements and verification (2026-11-07)

goosecc built from commit 40a93bb (later commits change only tests and documents;
`frontend-goose/build.sh`, runtime patches on)
against the build before G1 (66ea246). The machine (4 cores, Linux 6.18)
was shared with another job during these runs (load average 1.6-3).

| file | what |
|---|---|
| `startup.txt` | one-line file, best and mean of 500 (G1, tcc, `/bin/true`, then the build before G1) |
| `ctmark-g1.{md,json,log}` | `tests/bench_hcache.py -n 3`, G1: off / cold / warm / tcc / clang per file, phases |
| `ctmark-base.{md,json,log}` | the same for the build before G1 (no clang) |
| `checks/run.log` | `tests/run.py --goosecc`: 108/108 |
| `checks/suite.md` | `tests/suite_goosecc.py --variants O0,g`: 1,804 tests, no failure |
| `checks/dwarf.{log,json}` | `tests/dwarf_diff.py` over the corpus: 2,268 identical, 12 frame-location forms, 9 differing, verify 0 failed |
| `checks/gdb.log` | `tests/gdb_oracle.py --goosecc --corpus c,sample,ctmark`: 49/84 |
| `checks/cache_check.log` | header + parse cache, off/cold/warm/warm2/shared, whole state hashed: 44,783 runs, 0 failures |
| `checks/pcache.log` | `pcache_check.py`: padded main files, 9,428 runs, 2,960 replays, 0 failures |
| `checks/adversarial.log` | `cache_adversarial.py`: 17/17 |
| `checks/cmp_{E,syntax,ast}.log`, `checks/layout.log` | the front-end oracles: no difference, no false error, no mismatch |
| `checks/bins.log`, `checks/bins-diff.json` | `cmp_bins.py` against the build before G1 |
| `checks/attrib.txt` | each differing object attributed to the G1 step that changed it (builds 0 base, 1 runtime patch + noinit + parse cache, 2 const folding / nodebug / prototypes, 3 strlen / memchr / pointer reads / `__builtin_constant_p` / NRVO, 4 `always_inline` expansion) |
