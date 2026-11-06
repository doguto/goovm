# backend-cpp: the frozen v0 reference back-end

`gir_codegen_cpp.cpp` is the C++ back-end of GIR version 0 (revision 1), the
reference that `backend-goose/cg.goose` was first ported from byte for byte.
It is **frozen at commit 8f55b18** (`git show 8f55b18:backend-cpp/`), the
state the 2026-11-06 measurements in `docs/research/2026-11-06-results.md`
were taken with.

It is no longer built: from milestone A1 on, GIR is version 2 (`gir/gir.h`)
and the Goose back-end in `backend-goose/` is the only one that evolves.
Keeping a v0 build alive would need the v0 `gir.h` and exporter as well, so
the sources here are kept for reference only, together with
[`DESIGN.md`](DESIGN.md), which documents the v0 algorithm, encodings and ELF
layout.

To build and run the v0 pair (C++ and Goose back-ends, byte-identical
output), check out the old commit:

```bash
git worktree add /tmp/goovm-v0 8f55b18
cd /tmp/goovm-v0
GOOSE=... GOOSE_STDLIB=... backend-goose/build.sh build-goose
tests/run.py --goovm build-goose/tools/goovm-llc/goovm-llc --backend cpp
backend-goose/check_identical.py --goovm build-goose/tools/goovm-llc/goovm-llc
```

`backend-goose/check_identical.py` (the byte-identity check between the two
back-ends) is likewise v0-only: it needs a goovm-llc that has both
`--backend=cpp` and `--backend=goose`, which only commit 8f55b18 builds.
