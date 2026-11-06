#!/usr/bin/env python3
"""Summarize the failing assertions of kept --layout-check files.

usage: tests/layout_summary.py KEEPDIR [-j 3] [--corpus ...]
Recompiles each kept check file with clang-20 and histograms the failures by
the kind of assertion (size/align/offset/type) and a normalized message.
"""
import argparse, collections, concurrent.futures as cf, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import corpus as corpus_mod


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("keep")
    ap.add_argument("-j", type=int, default=3)
    ap.add_argument("--corpus", default="")
    ap.add_argument("--examples", type=int, default=3)
    a = ap.parse_args()
    jobs = list(corpus_mod.corpus([c for c in a.corpus.split(",") if c]))
    def one(j):
        c, p, fl = j
        out = os.path.join(a.keep, re.sub(r"[^A-Za-z0-9_.-]", "_", os.path.relpath(p, "/")) + ".layout.c")
        if not os.path.exists(out):
            return []
        r = subprocess.run(["clang-20", "-fsyntax-only", "-ferror-limit=0"] + fl + [out], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        res = []
        for l in r.stderr.decode(errors="replace").splitlines():
            if " error: " not in l:
                continue
            m = re.search(r"goosecc (layout|type): (.*)$", l)
            msg = l.split(" error: ", 1)[1]
            key = re.sub(r"'[^']*'", "'X'", msg)[:120]
            res.append((key, p, msg[:300]))
        return res
    with cf.ThreadPoolExecutor(a.j) as ex:
        allr = [x for r in ex.map(one, jobs) for x in r]
    cnt = collections.Counter(k for k, _, _ in allr)
    ex = collections.defaultdict(list)
    for k, p, m in allr:
        if len(ex[k]) < a.examples:
            ex[k].append((p, m))
    for k, n in cnt.most_common(40):
        print("%6d  %s" % (n, k))
        for p, m in ex[k]:
            print("          %s\n            %s" % (os.path.basename(p), m))


if __name__ == "__main__":
    main()
