#!/usr/bin/env python3
"""The C++ declaration oracle (D1): the functions and variables each C++
corpus file declares at namespace or class scope in its main file (not
templates) -- kind, name and Itanium mangled name -- as goosecc
--dump-decls prints them and as clang-20 reports them through libclang
(tests/cxx_decls.c, compiled on first use).

A file is "same" when both sets are equal; otherwise its declarations are
counted as matched, missing (clang has them, goosecc not: goosecc could not
mangle them, e.g. a parameter type of an uninstantiated template) and
wrong (goosecc's mangled name or kind is not clang's).

usage: tests/cmp_decls_cxx.py [--goosecc build/goosecc] [-j 2] [--corpus cxx] [--show N] [files... -- flags]
"""
import argparse, concurrent.futures as cf, os, subprocess, sys, collections

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import corpus as corpus_mod

TOOL_SRC = os.path.join(HERE, "cxx_decls.c")


def build_tool(work):
    exe = os.path.join(work, "cxx_decls")
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(TOOL_SRC):
        subprocess.check_call(["clang-20", "-O1", "-I/usr/lib/llvm-20/include", TOOL_SRC, "-o", exe,
                               "-L/usr/lib/llvm-20/lib", "-lclang", "-Wl,-rpath,/usr/lib/llvm-20/lib"])
    return exe


def lines(out):
    return set(l for l in out.splitlines() if l.count("|") == 2)


def check(a, tool, path, flags):
    r = subprocess.run([tool, path, "-w"] + flags, capture_output=True, text=True, errors="replace")
    if r.returncode != 0:
        return "clang-error", 0, 0, 0, []
    ref = lines(r.stdout)
    g = subprocess.run([a.goosecc, "--dump-decls"] + flags + [path], capture_output=True, text=True, errors="replace")
    if g.returncode != 0:
        return "goosecc-error", 0, 0, 0, [(g.stderr.strip().splitlines() or ["rc=%d" % g.returncode])[0]]
    got = lines(g.stdout)
    matched = len(ref & got)
    wrong = got - ref
    missing = ref - got
    # a missing declaration whose mangled name goosecc got with another kind/name counts as wrong only once
    st = "same" if not wrong and not missing else ("wrong" if wrong else "missing")
    return st, matched, len(missing), len(wrong), sorted(wrong)[:3] + ["-" + m for m in sorted(missing)[:3]]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--goosecc", default=os.path.join(HERE, "..", "build", "goosecc"))
    ap.add_argument("-j", type=int, default=2)
    ap.add_argument("--corpus", default="cxx")
    ap.add_argument("--show", type=int, default=20)
    ap.add_argument("--work", default="/tmp/goosecc-cxx-decls")
    ap.add_argument("rest", nargs="*")
    argv, cli_flags = corpus_mod.split_flags(sys.argv[1:])
    a = ap.parse_args(argv)
    os.makedirs(a.work, exist_ok=True)
    tool = build_tool(a.work)
    if a.rest:
        jobs = [("args", f, cli_flags) for f in a.rest]
    else:
        jobs = list(corpus_mod.corpus([c for c in a.corpus.split(",") if c]))
    with cf.ThreadPoolExecutor(a.j) as ex:
        res = list(ex.map(lambda j: (j, check(a, tool, j[1], j[2])), jobs))
    by = collections.defaultdict(collections.Counter)
    shown = 0
    for (c, p, fl), (st, m, mi, w, ex_) in res:
        by[c][st] += 1
        by[c]["decls"] += m
        by[c]["missing_decls"] += mi
        by[c]["wrong_decls"] += w
        if st in ("wrong", "goosecc-error") and shown < a.show:
            print("%s %s\n      %s" % (st, p, "\n      ".join(ex_)))
            shown += 1
    print()
    for c, cnt in by.items():
        files = sum(cnt[k] for k in ("same", "wrong", "missing", "goosecc-error", "clang-error"))
        print("%-11s files %4d  same %4d  only-missing %4d  wrong %4d  goosecc-error %3d | decls matched %6d  missing %5d  wrong %4d" % (
            c, files, cnt["same"], cnt["missing"], cnt["wrong"], cnt["goosecc-error"], cnt["decls"], cnt["missing_decls"],
            cnt["wrong_decls"]))


if __name__ == "__main__":
    main()
