#!/usr/bin/env python3
# C compile speed, D1 vs the base build (d77aa81): goosecc -c on every CTMark C
# file, the two builds interleaved file by file, best of N each, with and
# without the header cache (warm). Also a one-line file, best of 300.
import os, subprocess, sys, tempfile, time
sys.path.insert(0, "/home/user/goovm/.claude/worktrees/agent-a1c5913af422270dc/frontend-goose/tests")
import corpus

W = "/tmp/claude-0/-home-user-goovm/593b2907-8413-508c-8bdb-c68ef6e66f6e/scratchpad/work/d1"
B = {"base": W + "/base-build/goosecc", "d1": W + "/checks2/goosecc"}
N = int(sys.argv[1]) if len(sys.argv) > 1 else 3
caches = {k: tempfile.mkdtemp(prefix="cspeed-" + k) for k in B}


def best(cmd, env, n):
    t = None
    for _ in range(n):
        t0 = time.perf_counter()
        r = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=env)
        dt = time.perf_counter() - t0
        if r.returncode != 0:
            return None
        t = dt if t is None else min(t, dt)
    return t


tot = {(k, m): 0.0 for k in B for m in ("off", "warm")}
nfiles = 0
for c, path, flags in corpus.corpus(["ctmark"]):
    row = {}
    for k, gc in B.items():
        out = os.path.join(caches[k], "o.o")
        env_off = dict(os.environ)
        env_c = dict(os.environ, GOOSECC_CACHE=caches[k])
        row[(k, "off")] = best([gc, "-c", "-fno-header-cache"] + flags + [path, "-o", out], env_off, N)
        subprocess.run([gc, "-c"] + flags + [path, "-o", out], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=env_c)
        row[(k, "warm")] = best([gc, "-c"] + flags + [path, "-o", out], env_c, N)
    if any(v is None for v in row.values()):
        continue
    nfiles += 1
    for key, v in row.items():
        tot[key] += v
print(f"CTMark C files: {nfiles}, best of {N}, seconds")
for m in ("off", "warm"):
    b, d = tot[("base", m)], tot[("d1", m)]
    print(f"  {m:5s} base {b:.3f}  d1 {d:.3f}  d1/base {d / b:.4f}")
one = os.path.join(caches["base"], "one.c")
open(one, "w").write("int x;\n")
for k, gc in B.items():
    t = best([gc, "-c", "-fno-header-cache", one, "-o", os.path.join(caches[k], "one.o")], dict(os.environ), 300)
    print(f"  one-line file {k}: {t * 1000:.3f} ms")
