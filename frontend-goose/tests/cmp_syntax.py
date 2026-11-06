#!/usr/bin/env python3
"""-fsyntax-only on the corpora: goosecc must accept every file clang-20 accepts.

For each file: clang-20 -fsyntax-only (with the corpus flags) decides whether
the file is valid; goosecc -fsyntax-only must then exit 0 without errors
("false error" otherwise). Files clang rejects are counted separately (and
whether goosecc rejects them too).

usage: tests/cmp_syntax.py [--goosecc build/goosecc] [-j 3] [--corpus torture,...]
                           [--show N] [--out results.txt] [--extra=FLAGS] [files... -- flags]
"""
import argparse, concurrent.futures as cf, os, subprocess, sys, collections

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import corpus as corpus_mod

ENV = dict(os.environ, SOURCE_DATE_EPOCH="1700000000", TZ="UTC")


def run(cmd, timeout=120):
    try:
        r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=ENV, timeout=timeout)
        return r.returncode, r.stderr.decode("utf-8", "replace")
    except subprocess.TimeoutExpired:
        return -999, "timeout"


def check(goosecc, path, flags, clang):
    rc, err = run([clang, "-fsyntax-only"] + flags + [path])
    rc2, err2 = run([goosecc, "-fsyntax-only"] + flags + [path])
    first = next((l for l in err2.splitlines() if "error" in l), (err2.strip().splitlines() or [""])[0])
    if rc == 0:
        if rc2 == 0:
            return "ok", ""
        if rc2 < 0 or rc2 > 1:
            return "crash", "rc=%d %s" % (rc2, first)
        return "false-error", first
    if rc2 != 0:
        return "both-reject", ""
    cl = next((l for l in err.splitlines() if "error" in l), "")
    return "missed-error", cl


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--goosecc", default=os.path.join(HERE, "..", "build", "goosecc"))
    ap.add_argument("--clang", default="clang-20")
    ap.add_argument("-j", type=int, default=3)
    ap.add_argument("--corpus", default="")
    ap.add_argument("--show", type=int, default=30)
    ap.add_argument("--out", default="")
    ap.add_argument("--extra", default="")
    ap.add_argument("rest", nargs="*")
    a = ap.parse_args()
    if a.rest:
        files, flags = a.rest, []
        if "--" in a.rest:
            k = a.rest.index("--")
            files, flags = a.rest[:k], a.rest[k + 1:]
        jobs = [("args", f, flags) for f in files]
    else:
        jobs = list(corpus_mod.corpus([c for c in a.corpus.split(",") if c]))
    extra = a.extra.split()
    jobs = [(c, p, fl + extra) for c, p, fl in jobs]
    with cf.ThreadPoolExecutor(a.j) as ex:
        res = list(ex.map(lambda j: (j, check(a.goosecc, j[1], j[2], a.clang)), jobs))
    by = collections.defaultdict(collections.Counter)
    lines = []
    for (c, p, fl), (st, msg) in res:
        by[c][st] += 1
        if st in ("false-error", "crash", "missed-error"):
            lines.append("%s %s\n      %s" % (st, p, msg))
    lines.sort(key=lambda l: (not l.startswith("crash"), not l.startswith("false"), l))
    for l in lines[:a.show]:
        print(l)
    print()
    for c, cnt in by.items():
        tot = sum(cnt.values())
        valid = cnt["ok"] + cnt["false-error"] + cnt["crash"]
        print("%-8s files %5d  clang-valid %5d  accepted %5d  false-errors %4d  crashes %3d  | clang-invalid %4d (goosecc rejects %d, misses %d)" % (
            c, tot, valid, cnt["ok"], cnt["false-error"], cnt["crash"], cnt["both-reject"] + cnt["missed-error"],
            cnt["both-reject"], cnt["missed-error"]))
    if a.out:
        with open(a.out, "w") as f:
            f.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
