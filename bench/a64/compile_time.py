#!/usr/bin/env python3
"""Compile time on CTMark for aarch64-linux-gnu (milestone F1).

For every source file of the CTMark programs (tests/suite.py's ctmark and
ctmark-cxx corpora, with their flags), best of N runs, serially:

  back end only (the same bitcode: clang-20 --target=aarch64-linux-gnu -O0 [-g] -emit-llvm):
    llc       llc-20 -O0 -filetype=obj (LLVM's AArch64 back end, FastISel/GlobalISel at -O0)
    goovm     goovm-llc (export + Goose back end; its --time phases are recorded too)
  optimizing, on clang -O1 -Xclang -disable-llvm-passes IR (the IR LLVM's own pipeline starts from):
    llvm-O1   opt-20 -O1, then llc-20 -O1
    goovm-O1  goovm-llc -O1 (the Goose middle end and global register allocation)
  whole compile (source to object):
    clang     clang-20 --target=aarch64-linux-gnu -O0 [-g] -c
    cc        goovm-cc --target=aarch64-linux-gnu -O0 [-g] -c (clang's front end, Goose back end)
    clang-O1, cc-O1  the same at -O1
    goosecc   goosecc --target=aarch64-linux-gnu [-g] -c (C files; with --goosecc)

Per program the sums over its files, and the geometric mean of the per-program
ratios to llc (back end) and clang (whole compile), as a markdown table; the
raw times as JSON.

usage: bench/a64/compile_time.py --goovm-llc P --goovm-cc P [--goosecc P] [-n 3] [-g]
                                  [--json out.json] [--md out.md] [--work DIR] [program ...]
"""
import argparse, json, math, os, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "tests"))
import suite  # noqa: E402

T = ["--target=aarch64-linux-gnu"]


def best(cmd, n, env=None):
    b = None
    for _ in range(n):
        t0 = time.perf_counter()
        r = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, env=env)
        dt = time.perf_counter() - t0
        if r.returncode:
            return None, r.stderr.decode(errors="replace")[-300:]
        b = dt if b is None else min(b, dt)
    return b, ""


def gmean(xs):
    xs = [x for x in xs if x and x > 0]
    return math.exp(sum(math.log(x) for x in xs) / len(xs)) if xs else float("nan")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goovm-llc", required=True)
    ap.add_argument("--goovm-cc", required=True)
    ap.add_argument("--goosecc", default="")
    ap.add_argument("-n", type=int, default=3)
    ap.add_argument("-g", action="store_true", help="with debug information")
    ap.add_argument("--work", default=tempfile.mkdtemp(prefix="ct_a64_"))
    ap.add_argument("--json", default="")
    ap.add_argument("--md", default="")
    ap.add_argument("programs", nargs="*")
    a = ap.parse_args()
    os.makedirs(a.work, exist_ok=True)
    g = ["-g"] if a.g else []
    tests = suite.all_tests("/home/user/llvm/llvm-test-suite", ["ctmark", "ctmark-cxx"])
    if a.programs:
        tests = [t for t in tests if any(p in t.id for p in a.programs)]
    obj = os.path.join(a.work, "x.o")
    res = {}
    for t in tests:
        prog = {}
        for i, s in enumerate(t.srcs):
            cxx = s.endswith((".cpp", ".cc", ".cxx", ".C"))
            cc = "clang++-20" if cxx else "clang-20"
            fl = t.flags(s)
            bc = os.path.join(a.work, f"{i}.bc")
            r = subprocess.run([cc] + T + ["-O0", "-w"] + g + fl + ["-c", "-emit-llvm", s, "-o", bc],
                               stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
            if r.returncode:
                print(f"{t.id} {os.path.basename(s)}: clang -emit-llvm failed", file=sys.stderr)
                continue
            row = {}
            row["llc"], _ = best(["llc-20", "-O0", "-filetype=obj", "-mtriple=aarch64-linux-gnu", bc, "-o", obj], a.n)
            row["goovm"], e = best([a.goovm_llc, bc, "-o", obj], a.n)
            if row["goovm"] is None:
                print(f"{t.id} {os.path.basename(s)}: goovm-llc failed: {e}", file=sys.stderr)
            bc1 = os.path.join(a.work, f"{i}.O1.bc")
            r = subprocess.run([cc] + T + ["-O1", "-Xclang", "-disable-llvm-passes", "-w"] + g + fl + ["-c", "-emit-llvm", s, "-o", bc1],
                               stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
            if r.returncode == 0:
                opt1 = os.path.join(a.work, "o1.bc")
                t1, _ = best(["opt-20", "-O1", bc1, "-o", opt1], a.n)
                t2, _ = best(["llc-20", "-O1", "-filetype=obj", "-mtriple=aarch64-linux-gnu", opt1, "-o", obj], a.n)
                row["llvm-O1"] = t1 + t2 if t1 is not None and t2 is not None else None
                row["goovm-O1"], _ = best([a.goovm_llc, "-O1", bc1, "-o", obj], a.n)
            row["clang-O1"], _ = best([cc] + T + ["-O1", "-w"] + g + fl + ["-c", s, "-o", obj], a.n)
            row["cc-O1"], _ = best([a.goovm_cc] + T + ["-O1", "-w"] + g + fl + ["-c", s, "-o", obj], a.n)
            row["clang"], _ = best([cc] + T + ["-O0", "-w"] + g + fl + ["-c", s, "-o", obj], a.n)
            row["cc"], _ = best([a.goovm_cc] + T + ["-O0", "-w"] + g + fl + ["-c", s, "-o", obj], a.n)
            if a.goosecc and not cxx:
                row["goosecc"], e = best([a.goosecc] + T + ["-w"] + g + fl + ["-c", s, "-o", obj], a.n)
                if row["goosecc"] is None:
                    print(f"{t.id} {os.path.basename(s)}: goosecc failed: {e[:200]}", file=sys.stderr)
            prog[s] = row
        res[t.id] = prog
        print(f"{t.id}: {len(prog)} files", file=sys.stderr, flush=True)
    cols = ["llc", "goovm", "llvm-O1", "goovm-O1", "clang", "cc", "clang-O1", "cc-O1"] + (["goosecc"] if a.goosecc else [])
    lines = [f"Compile time, aarch64-linux-gnu, -O0{' -g' if a.g else ''}, best of {a.n} (seconds, sums per program; "
             "files a compiler fails on count for none)", "",
             "| program | files | " + " | ".join(cols) + " | goovm / llc | goovm-O1 / llvm-O1 | cc / clang | cc-O1 / clang-O1 |"
             + (" goosecc / clang |" if a.goosecc else ""),
             "|---|---:|" + "---:|" * (len(cols) + 4 + (1 if a.goosecc else 0))]
    ratios = {"goovm": [], "goovm-O1": [], "cc": [], "cc-O1": [], "goosecc": []}
    for p, files in res.items():
        tot = {}
        for c in cols:
            refs = ("llc", "clang", "llvm-O1", "clang-O1")
            ok = [r for r in files.values() if r.get(c) is not None and all(r.get(x) is not None for x in refs)]
            tot[c] = sum(r[c] for r in ok) if ok else None
            # the reference sums over the same files
            for x in refs:
                tot[c + "_ref_" + x] = sum(r[x] for r in ok) if ok else None
        def ratio(c, ref):
            v, rv = tot.get(c), tot.get(c + "_ref_" + ref)
            return v / rv if v and rv else None
        rg, ro, rc = ratio("goovm", "llc"), ratio("goovm-O1", "llvm-O1"), ratio("cc", "clang")
        rc1 = ratio("cc-O1", "clang-O1")
        rs = ratio("goosecc", "clang") if a.goosecc else None
        for k, v in (("goovm", rg), ("goovm-O1", ro), ("cc", rc), ("cc-O1", rc1), ("goosecc", rs)):
            if v:
                ratios[k].append(v)
        f = lambda x: f"{x:.3f}" if x is not None else "-"
        lines.append(f"| {p} | {len(files)} | " + " | ".join(f(tot[c]) for c in cols)
                     + f" | {f(rg)} | {f(ro)} | {f(rc)} | {f(rc1)} |" + (f" {f(rs)} |" if a.goosecc else ""))
    lines.append("")
    lines.append(f"Geometric means of the per-program ratios: goovm-llc / llc-20 -O0 = {gmean(ratios['goovm']):.3f}, "
                 f"goovm-llc -O1 / (opt-20 -O1 + llc-20 -O1) = {gmean(ratios['goovm-O1']):.3f}, "
                 f"goovm-cc / clang -O0 = {gmean(ratios['cc']):.3f}, goovm-cc -O1 / clang -O1 = {gmean(ratios['cc-O1']):.3f}"
                 + (f", goosecc / clang -O0 = {gmean(ratios['goosecc']):.3f}" if a.goosecc else ""))
    md = "\n".join(lines) + "\n"
    print(md)
    if a.md:
        open(a.md, "w").write(md)
    if a.json:
        json.dump(res, open(a.json, "w"), indent=1)


if __name__ == "__main__":
    main()
