#!/usr/bin/env python3
"""The layout oracle over the corpora: goosecc --layout-check writes a C file
that includes the TU and _Static_asserts goosecc's size, alignment and member
offsets of every file-scope struct/union/typedef; clang-20 must accept it.

usage: tests/layout_check.py [--goosecc build/goosecc] [-j 3] [--corpus ...] [--show N]
                             [--keep DIR] [files... -- flags]
"""
import argparse, concurrent.futures as cf, os, re, subprocess, sys, tempfile, collections

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import corpus as corpus_mod

ENV = dict(os.environ, SOURCE_DATE_EPOCH="1700000000", TZ="UTC")


def run(cmd):
    r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=ENV)
    return r.returncode, r.stderr.decode("utf-8", "replace")


def check(a, path, flags, workdir):
    rc, err = run([a.clang, "-fsyntax-only"] + flags + [path])
    if rc != 0:
        return "clang-invalid", "", 0
    out = os.path.join(workdir, re.sub(r"[^A-Za-z0-9_.-]", "_", os.path.relpath(path, "/")) + ".layout.c")
    rc, err = run([a.goosecc, "--layout-check"] + flags + [path, "-o", out])
    if rc != 0 or not os.path.exists(out):
        return "goosecc-error", (err.strip().splitlines() or ["rc=%d" % rc])[0], 0
    n = 0
    with open(out) as f:
        m = re.search(r"/\* (\d+) assertions \*/", f.read())
        if m:
            n = int(m.group(1))
    rc, err = run([a.clang, "-fsyntax-only"] + flags + [out])
    if rc != 0:
        fails = [l for l in err.splitlines() if "static assertion failed" in l or "error" in l]
        return "mismatch", "\n      ".join(fails[:4]), n
    if not a.keep:
        os.unlink(out)
    return "ok", "", n


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--goosecc", default=os.path.join(HERE, "..", "build", "goosecc"))
    ap.add_argument("--clang", default="clang-20")
    ap.add_argument("-j", type=int, default=3)
    ap.add_argument("--corpus", default="")
    ap.add_argument("--show", type=int, default=30)
    ap.add_argument("--keep", default="")
    ap.add_argument("rest", nargs="*")
    argv, cli_flags = corpus_mod.split_flags(sys.argv[1:])
    a = ap.parse_args(argv)
    if a.rest:
        files, flags = a.rest, cli_flags
        jobs = [("args", f, flags) for f in files]
    else:
        jobs = list(corpus_mod.corpus([c for c in a.corpus.split(",") if c]))
    workdir = a.keep or tempfile.mkdtemp(prefix="goosecc-layout-")
    os.makedirs(workdir, exist_ok=True)
    with cf.ThreadPoolExecutor(a.j) as ex:
        res = list(ex.map(lambda j: (j, check(a, j[1], j[2], workdir)), jobs))
    by = collections.defaultdict(collections.Counter)
    nas = collections.Counter()
    shown = 0
    for (c, p, fl), (st, msg, n) in res:
        by[c][st] += 1
        nas[c] += n
        if st in ("mismatch", "goosecc-error") and shown < a.show:
            print("%s %s\n      %s" % (st, p, msg))
            shown += 1
    print()
    for c, cnt in by.items():
        print("%-8s files %5d  checked %5d  ok %5d  mismatch %4d  goosecc-error %3d  assertions %7d" % (
            c, sum(cnt.values()), sum(cnt.values()) - cnt["clang-invalid"], cnt["ok"], cnt["mismatch"],
            cnt["goosecc-error"], nas[c]))


if __name__ == "__main__":
    main()
