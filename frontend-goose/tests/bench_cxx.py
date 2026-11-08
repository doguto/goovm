#!/usr/bin/env python3
"""Speed of goosecc's C++ front end (D1) against clang++-20: for every file
of the CTMark C++ programs (corpus cxx-ctmark: 7zip, Bullet, kimwitu++,
tramp3d-v4, with their flags), the best of N runs of

  goosecc -E            (no header cache, then a warm one)
  goosecc -fsyntax-only (no header cache, then a warm one)
  clang++-20 -E
  clang++-20 -fsyntax-only

one process at a time. Prints a table per program (milliseconds, sums of
the per-file best times) and the ratios.

usage: frontend-goose/tests/bench_cxx.py [--goosecc build/goosecc] [-n 3] [--md out.md] [--json out.json]
"""
import argparse, collections, json, os, shutil, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import corpus as corpus_mod


def best(cmd, n, env):
    t = None
    for _ in range(n):
        t0 = time.perf_counter()
        r = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=env)
        dt = time.perf_counter() - t0
        if r.returncode != 0:
            return None
        t = dt if t is None else min(t, dt)
    return t


def program(path):
    for name in ("7zip", "Bullet", "kimwitu++", "tramp3d-v4"):
        if "/" + name + "/" in path or path.endswith("/" + name + ".cpp"):
            return name
    return os.path.basename(os.path.dirname(path))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--goosecc", default=os.path.join(HERE, "..", "build", "goosecc"))
    ap.add_argument("--clangxx", default="clang++-20")
    ap.add_argument("-n", type=int, default=3)
    ap.add_argument("--md", default="")
    ap.add_argument("--json", default="")
    ap.add_argument("--limit", type=int, default=0, help="only the first N files (a quick try)")
    args = ap.parse_args()
    files = list(corpus_mod.corpus(["cxx-ctmark"]))
    if args.limit:
        files = files[:args.limit]
    cache = tempfile.mkdtemp(prefix="goosecc-bench-cxx-")
    env = dict(os.environ)
    envc = dict(os.environ, GOOSECC_CACHE=cache)
    cols = ["gE_off", "gE_warm", "gS_off", "gS_warm", "cE", "cS"]
    res = []
    for i, (_, path, flags) in enumerate(files):
        row = {"file": path, "program": program(path)}
        g = [args.goosecc] + flags
        row["gE_off"] = best(g + ["-E", "-fno-header-cache", path, "-o", "/dev/null"], args.n, env)
        subprocess.run(g + ["-E", path, "-o", "/dev/null"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=envc)
        row["gE_warm"] = best(g + ["-E", path, "-o", "/dev/null"], args.n, envc)
        row["gS_off"] = best(g + ["-fsyntax-only", "-fno-header-cache", path], args.n, env)
        row["gS_warm"] = best(g + ["-fsyntax-only", path], args.n, envc)
        c = [args.clangxx] + flags
        row["cE"] = best(c + ["-E", path, "-o", "/dev/null"], args.n, env)
        row["cS"] = best(c + ["-fsyntax-only", path], args.n, env)
        res.append(row)
        if (i + 1) % 50 == 0:
            print(f"... {i + 1}/{len(files)}", file=sys.stderr, flush=True)
    shutil.rmtree(cache, ignore_errors=True)
    by = collections.OrderedDict()
    for r in res:
        by.setdefault(r["program"], []).append(r)
    lines = ["| program | files | goosecc -E | -E warm | clang++ -E | goosecc -fsyntax-only | warm | clang++ -fsyntax-only |",
             "|---|---:|---:|---:|---:|---:|---:|---:|"]
    tot = collections.Counter()
    failed = collections.Counter()
    for prog, rows in list(by.items()) + [("**total**", res)]:
        s = collections.Counter()
        for r in rows:
            if any(r[c] is None for c in cols):
                failed[prog] += 1
                continue
            for c in cols:
                s[c] += r[c] * 1000
        n_ok = len(rows) - failed[prog]
        lines.append(f"| {prog} | {n_ok} | {s['gE_off']:.0f} | {s['gE_warm']:.0f} | {s['cE']:.0f} | "
                     f"{s['gS_off']:.0f} | {s['gS_warm']:.0f} | {s['cS']:.0f} |")
        if prog == "**total**":
            tot = s
    lines.append("")
    lines.append(f"-E: clang++ / goosecc = {tot['cE'] / tot['gE_off']:.2f} (no cache), {tot['cE'] / tot['gE_warm']:.2f} (warm cache)")
    lines.append(f"-fsyntax-only: clang++ / goosecc = {tot['cS'] / tot['gS_off']:.2f} (no cache), "
                 f"{tot['cS'] / tot['gS_warm']:.2f} (warm cache)")
    if sum(failed.values()):
        lines.append(f"files left out (a command failed): {dict(failed)}")
    out = "\n".join(lines)
    print(out)
    if args.md:
        open(args.md, "w").write(f"best of {args.n}, milliseconds, sums of per-file best times\n\n" + out + "\n")
    if args.json:
        json.dump(res, open(args.json, "w"), indent=1)


if __name__ == "__main__":
    main()
