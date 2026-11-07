#!/usr/bin/env python3
"""The parse cache (G1) replays exactly, also where the main file's length
differs from the compile that recorded the entry: every source offset the
entry holds past the main file's text then moves.

For each corpus file (corpus.py, with its flags) and output -- `--dump-ast`,
`--layout-check`, the object of `-c` and of `-c -g` -- goosecc runs

  rec     with an empty cache of the file's own, twice (the second compile
          records the main file's "..." includes as header units, and the
          parse cache entry of that chain)
  hit     with that cache, the main file padded by N spaces at its end
          (GOOSECC_TEST_MAIN_PAD=N: the built-in text and every header
          then start N bytes later)
  ref     the same padded compile without the cache

and `hit` must give `ref`'s output, standard output, standard error (with
--pp-state-hash=v: the preprocessor's and the parser's state, table by
table) and exit status. It reports how many `hit` runs replayed a parse
cache entry (a file without leading includes has none).

usage: frontend-goose/tests/pcache_check.py [--goosecc build/goosecc] [--corpus torture,...] [-j 2]
                                            [--modes c,g,ast,layout] [--pad N] [--show N] [files... -- flags]
"""
import argparse, concurrent.futures as cf, os, re, shutil, subprocess, sys, tempfile, threading, collections

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import corpus as corpus_mod

MODES = {"ast": ["--dump-ast"], "layout": ["--layout-check"], "c": ["-c"], "g": ["-c", "-g"]}
HITS = re.compile(rb"parse cache: (\d+) lookups, (\d+) hits")


def run(goosecc, mode, flags, path, out, cache, pad):
    env = dict(os.environ, SOURCE_DATE_EPOCH="1700000000", TZ="UTC")
    env.pop("GOOSECC_TEST_MAIN_PAD", None)
    if pad:
        env["GOOSECC_TEST_MAIN_PAD"] = str(pad)
    extra = ["--pp-state-hash=v"]
    if cache is None:
        extra.append("-fno-header-cache")
    else:
        env["GOOSECC_CACHE"] = cache
        extra.append("--cache-stats")
    r = subprocess.run([goosecc] + MODES[mode] + extra + flags + [path, "-o", out], stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE, env=env)
    data = b""
    if os.path.exists(out):
        data = open(out, "rb").read()
        os.unlink(out)
    m = HITS.search(r.stderr)
    err = re.sub(rb"goosecc: header cache: [^\n]*\n", b"", r.stderr)
    return (r.returncode, r.stdout, err, data), (int(m.group(2)) if m else 0)


def check(a, path, flags, tmp):
    tid = threading.get_ident()
    out = os.path.join(tmp, f"out.{tid}")
    own = os.path.join(tmp, f"cache.{tid}")
    res = {"fail": [], "hits": 0, "runs": 0}
    for mode in a.modes:
        shutil.rmtree(own, ignore_errors=True)
        run(a.goosecc, mode, flags, path, out, own, 0)
        run(a.goosecc, mode, flags, path, out, own, 0)
        got, hit = run(a.goosecc, mode, flags, path, out, own, a.pad)
        ref, _ = run(a.goosecc, mode, flags, path, out, None, a.pad)
        res["runs"] += 1
        res["hits"] += hit
        if got != ref:
            what = [n for n, x, y in zip(("status", "stdout", "stderr", "output"), got, ref) if x != y]
            res["fail"].append(f"{mode}: {','.join(what)}")
    shutil.rmtree(own, ignore_errors=True)
    return res


def main():
    argv, cflags = corpus_mod.split_flags(sys.argv[1:])
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goosecc", default=os.path.join(HERE, "..", "build", "goosecc"))
    ap.add_argument("--corpus", default="torture,unit,regress,bench,ctmark")
    ap.add_argument("-j", type=int, default=2)
    ap.add_argument("--modes", default="c,g,ast,layout")
    ap.add_argument("--pad", type=int, default=777)
    ap.add_argument("--show", type=int, default=20)
    ap.add_argument("files", nargs="*")
    a = ap.parse_args(argv)
    a.goosecc = os.path.abspath(a.goosecc)
    a.modes = a.modes.split(",")
    items = [("files", f, cflags) for f in a.files] if a.files else list(corpus_mod.corpus(a.corpus.split(",")))
    tmp = tempfile.mkdtemp(prefix="pcache_check_")
    by = collections.defaultdict(lambda: [0, 0, 0, 0])   # files, ok files, runs, hits
    fails = []
    with cf.ThreadPoolExecutor(a.j) as ex:
        futs = {ex.submit(check, a, p, fl, tmp): (c, p) for c, p, fl in items}
        for k, fu in enumerate(cf.as_completed(futs)):
            c, p = futs[fu]
            r = fu.result()
            b = by[c]
            b[0] += 1
            b[1] += not r["fail"]
            b[2] += r["runs"]
            b[3] += r["hits"]
            for f in r["fail"]:
                fails.append(f"{p}: {f}")
                if len(fails) <= a.show:
                    print(f"FAIL {p}: {f}", flush=True)
            if (k + 1) % 250 == 0:
                print(f"... {k + 1}/{len(items)}", flush=True)
    print("| corpus | files | identical | padded runs | parse cache hits |")
    print("|---|---:|---:|---:|---:|")
    T = [0] * 4
    for c, b in by.items():
        print(f"| {c} | {b[0]} | {b[1]} | {b[2]} | {b[3]} |")
        T = [x + y for x, y in zip(T, b)]
    print(f"| **total** | {T[0]} | {T[1]} | {T[2]} | {T[3]} |")
    print(f"failures: {len(fails)}")
    shutil.rmtree(tmp, ignore_errors=True)
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
