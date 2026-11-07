#!/usr/bin/env python3
"""The header cache (B4) changes nothing: goosecc's outputs with the cache
disabled, cold, warm and shared are byte-identical, on every corpus file.

For each file (corpus.py, with its flags) and each output -- `-E`,
`--dump-ast`, `--layout-check`, the object of `-c` and of `-c -g` --
goosecc runs

  off     -fno-header-cache
  cold    with an empty cache of the file's own (-c and -E each record
          into it; the other compile modes then read what -c recorded)
  warm    the same again, with that cache filled (a second compile also
          records the main file's "..." includes)
  warm2   once more: it must record nothing
  shared  with one cache for the whole run, filled by every file before
          (in -j parallel workers, which also write the same entries
          concurrently)

and every run's output file, standard output, standard error (with
--pp-state-hash=v: a checksum of the whole preprocessor state, array by
array) and exit status must be those of `off`. The `warm2` runs must also
record nothing new (--cache-stats): every include worth an entry was
replayed.

usage: tests/cache_check.py [--goosecc build/goosecc] [--corpus torture,...] [-j 2]
                            [--modes E,ast,layout,c,g] [--keep] [--show N] [files... -- flags]
"""
import argparse, concurrent.futures as cf, os, re, shutil, subprocess, sys, tempfile, threading, collections

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import corpus as corpus_mod

MODES = {
    "E": ["-E"],
    "ast": ["--dump-ast"],
    "layout": ["--layout-check"],
    "c": ["-c"],
    "g": ["-c", "-g"],
}
STATS = re.compile(rb"goosecc: header cache: (\d+) lookups, (\d+) hits, (\d+) misses; (\d+) recorded[^\n]*\n")


def run(goosecc, mode, flags, path, out, cache, env0):
    env = dict(env0)
    extra = ["--pp-state-hash=v"]
    if cache is None:
        extra.append("-fno-header-cache")
    else:
        env["GOOSECC_CACHE"] = cache
        extra.append("--cache-stats")
    cmd = [goosecc] + MODES[mode] + extra + flags + [path, "-o", out]
    if mode == "E":
        cmd = cmd[:-2]
    r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env)
    data = b""
    if mode != "E" and os.path.exists(out):
        data = open(out, "rb").read()
        os.unlink(out)
    stats = STATS.search(r.stderr)
    err = STATS.sub(b"", r.stderr)
    st = tuple(int(x) for x in stats.groups()) if stats else None
    return (r.returncode, r.stdout, err, data), st


def check(a, path, flags, tmp):
    env0 = dict(os.environ, SOURCE_DATE_EPOCH="1700000000", TZ="UTC")
    tid = threading.get_ident()
    out = os.path.join(tmp, f"out.{tid}")
    own = os.path.join(tmp, f"cache.{tid}")
    shutil.rmtree(own, ignore_errors=True)
    res = {"fail": [], "runs": 0, "hits": 0, "lookups": 0, "warm_miss": 0}
    order = [m for m in ["c", "E", "ast", "layout", "g"] if m in a.modes]
    for mode in order:
        ref, _ = run(a.goosecc, mode, flags, path, out, None, env0)
        res["runs"] += 1
        for kind in ("cold", "warm", "warm2", "shared"):
            if kind in ("cold", "warm") and mode not in ("c", "E"):
                continue
            cache = own if kind != "shared" else a.shared
            got, st = run(a.goosecc, mode, flags, path, out, cache, env0)
            res["runs"] += 1
            if st:
                res["lookups"] += st[0]
                res["hits"] += st[1]
                if kind == "warm2" and st[3] > 0:
                    res["warm_miss"] += 1
            if got != ref:
                what = [n for n, x, y in zip(("status", "stdout", "stderr", "output"), got, ref) if x != y]
                res["fail"].append(f"{mode}/{kind}: {','.join(what)}")
    shutil.rmtree(own, ignore_errors=True)
    return res


def main():
    argv, cflags = corpus_mod.split_flags(sys.argv[1:])
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goosecc", default=os.path.join(HERE, "..", "build", "goosecc"))
    ap.add_argument("--corpus", default="torture,unit,regress,bench,ctmark")
    ap.add_argument("-j", type=int, default=2)
    ap.add_argument("--modes", default="E,ast,layout,c,g")
    ap.add_argument("--shared", default="", help="the shared cache directory (default: a fresh one)")
    ap.add_argument("--keep", action="store_true", help="keep the shared cache")
    ap.add_argument("--show", type=int, default=20)
    ap.add_argument("files", nargs="*")
    a = ap.parse_args(argv)
    a.goosecc = os.path.abspath(a.goosecc)
    a.modes = a.modes.split(",")
    if a.files:
        items = [("files", f, cflags) for f in a.files]
    else:
        items = list(corpus_mod.corpus(a.corpus.split(",")))
    tmp = tempfile.mkdtemp(prefix="cache_check_")
    if not a.shared:
        a.shared = os.path.join(tmp, "shared")
    by = collections.defaultdict(lambda: [0, 0, 0, 0, 0])   # files, ok files, runs, lookups, hits
    fails = []
    warm_miss = 0
    with cf.ThreadPoolExecutor(a.j) as ex:
        futs = {ex.submit(check, a, p, fl, tmp): (c, p) for c, p, fl in items}
        for k, fu in enumerate(cf.as_completed(futs)):
            c, p = futs[fu]
            r = fu.result()
            b = by[c]
            b[0] += 1
            b[1] += not r["fail"]
            b[2] += r["runs"]
            b[3] += r["lookups"]
            b[4] += r["hits"]
            warm_miss += r["warm_miss"]
            for f in r["fail"]:
                fails.append(f"{p}: {f}")
                if len(fails) <= a.show:
                    print(f"FAIL {p}: {f}", flush=True)
            if (k + 1) % 200 == 0:
                print(f"... {k + 1}/{len(items)}", flush=True)
    print("| corpus | files | identical | runs | lookups | hits |")
    print("|---|---:|---:|---:|---:|---:|")
    T = [0] * 5
    for c, b in by.items():
        print(f"| {c} | {b[0]} | {b[1]} | {b[2]} | {b[3]} | {b[4]} |")
        T = [x + y for x, y in zip(T, b)]
    print(f"| **total** | {T[0]} | {T[1]} | {T[2]} | {T[3]} | {T[4]} |")
    print(f"warm2 runs that recorded: {warm_miss}; failures: {len(fails)}")
    if not a.keep:
        shutil.rmtree(tmp, ignore_errors=True)
    else:
        print("kept", tmp)
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
