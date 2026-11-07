#!/usr/bin/env python3
"""Compile speed: goosecc -c vs clang-20 -O0 -c (and TinyCC, tcc -c) on the C
files of the six CTMark programs, with the flags of tests/suite.py.

Each compile runs alone, single-threaded; the time is the best of N wall-clock
runs and the peak RSS the largest ru_maxrss. Objects go to a scratch file.
goosecc's phases (preprocess, parse+sema, lowering, back-end, write) come
from one extra run with --time.

With --g, the cost of debug information instead: clang-20 -O0 -g -c,
goosecc -c and goosecc -g -c, and goosecc's phases with and without -g.

usage: tests/bench_goosecc.py [--goosecc PATH] [-n 3] [--tcc tcc] [--g] [--md out.md] [--json out.json] [program ...]
"""
import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import suite  # noqa: E402


def run_once(cmd):
    t0 = time.perf_counter()
    p = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    err = p.stderr.read()
    _, status, ru = os.wait4(p.pid, 0)
    t1 = time.perf_counter()
    return t1 - t0, ru.ru_maxrss, os.waitstatus_to_exitcode(status), err


def best(cmd, n):
    ts, rss, rc, err = [], 0, 0, b""
    for _ in range(n):
        t, r, rc, err = run_once(cmd)
        ts.append(t)
        rss = max(rss, r)
        if rc != 0:
            break
    return min(ts), rss, rc, err


PHASES = ["preprocess", "parse+sema", "lowering", "back-end", "write"]


def phases(goosecc, flags, src, obj):
    r = subprocess.run([goosecc, "-c", "--time"] + flags + [src, "-o", obj], stdout=subprocess.DEVNULL,
                       stderr=subprocess.PIPE)
    m = re.search(rb"preprocess (\d+) us, parse\+sema (\d+) us, lowering (\d+) us, back-end (\d+) us, write (\d+) us", r.stderr)
    return [int(x) / 1e6 for x in m.groups()] if m else [0.0] * 5


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goosecc", default=os.path.join(ROOT, "frontend-goose/build/goosecc"))
    ap.add_argument("--clang", default="clang-20")
    ap.add_argument("--tcc", default="tcc")
    ap.add_argument("--suite", default="/home/user/llvm/llvm-test-suite")
    ap.add_argument("-n", type=int, default=3)
    ap.add_argument("--md", default="")
    ap.add_argument("--json", default="")
    ap.add_argument("--g", action="store_true",
                    help="the cost of debug information: clang-20 -O0 -g -c, goosecc -c and goosecc -g -c")
    ap.add_argument("programs", nargs="*")
    a = ap.parse_args()
    have_tcc = subprocess.run(["which", a.tcc], stdout=subprocess.DEVNULL).returncode == 0
    tests = suite.ctmark_tests(a.suite)
    if a.programs:
        tests = [t for t in tests if t.name in a.programs]
    if a.g:
        return bench_g(a, tests)
    tmp = tempfile.mkdtemp(prefix="bench_goosecc_")
    obj = os.path.join(tmp, "x.o")
    rows = []
    files = []
    for t in tests:
        tot = {"clang": 0.0, "goosecc": 0.0, "tcc": 0.0, "tcc_files": 0, "files": 0, "rss_clang": 0, "rss_goosecc": 0,
               "rss_tcc": 0, "ph": [0.0] * 5, "fail_goosecc": 0, "fail_tcc": 0, "tcc_clang": 0.0, "tcc_goosecc": 0.0}
        for s in t.srcs:
            fl = ["-w"] + t.cflags
            tc, rc_, ec, _ = best([a.clang, "-O0", "-c"] + fl + [s, "-o", obj], a.n)
            tg, rg, eg, err = best([a.goosecc, "-c"] + fl + [s, "-o", obj], a.n)
            ph = phases(a.goosecc, fl, s, obj)
            tt, rt, et = 0.0, 0, 1
            if have_tcc:
                tfl = [f for f in fl if f.startswith(("-D", "-I", "-U", "-w"))]
                tt, rt, et, _ = best([a.tcc, "-c"] + tfl + [s, "-o", obj], a.n)
            tot["files"] += 1
            tot["clang"] += tc
            tot["goosecc"] += tg
            tot["rss_clang"] = max(tot["rss_clang"], rc_)
            tot["rss_goosecc"] = max(tot["rss_goosecc"], rg)
            tot["fail_goosecc"] += eg != 0
            for i in range(5):
                tot["ph"][i] += ph[i]
            if have_tcc and et == 0:
                tot["tcc"] += tt
                tot["tcc_files"] += 1
                tot["tcc_clang"] += tc
                tot["tcc_goosecc"] += tg
                tot["rss_tcc"] = max(tot["rss_tcc"], rt)
            elif have_tcc:
                tot["fail_tcc"] += 1
            files.append({"program": t.name, "file": os.path.relpath(s, a.suite), "clang": tc, "goosecc": tg,
                          "tcc": tt if et == 0 else None, "phases": ph, "rss_clang": rc_, "rss_goosecc": rg})
            print(f"{t.name} {os.path.basename(s)}: clang {tc * 1e3:.1f} ms, goosecc {tg * 1e3:.1f} ms"
                  + (f", tcc {tt * 1e3:.1f} ms" if have_tcc and et == 0 else "") + ("" if eg == 0 else " GOOSECC FAILED"),
                  flush=True)
        rows.append((t.name, tot))
    out = ["| program | files | clang-20 -O0 -c | goosecc -c | speed-up | clang peak RSS | goosecc peak RSS |",
           "|---|---:|---:|---:|---:|---:|---:|"]
    T = {"files": 0, "clang": 0.0, "goosecc": 0.0, "tcc": 0.0, "tcc_files": 0, "tcc_clang": 0.0, "tcc_goosecc": 0.0,
         "rss_clang": 0, "rss_goosecc": 0, "rss_tcc": 0, "ph": [0.0] * 5, "fail_goosecc": 0}
    for name, t in rows:
        out.append(f"| {name} | {t['files']} | {t['clang'] * 1e3:.0f} ms | {t['goosecc'] * 1e3:.0f} ms | "
                   f"{t['clang'] / t['goosecc']:.2f}x | {t['rss_clang'] / 1024:.0f} MB | {t['rss_goosecc'] / 1024:.0f} MB |")
        for k in ("files", "clang", "goosecc", "tcc", "tcc_files", "tcc_clang", "tcc_goosecc", "fail_goosecc"):
            T[k] += t[k]
        for k in ("rss_clang", "rss_goosecc", "rss_tcc"):
            T[k] = max(T[k], t[k])
        for i in range(5):
            T["ph"][i] += t["ph"][i]
    out.append(f"| **total** | {T['files']} | {T['clang']:.2f} s | {T['goosecc']:.2f} s | {T['clang'] / T['goosecc']:.2f}x | "
               f"{T['rss_clang'] / 1024:.0f} MB | {T['rss_goosecc'] / 1024:.0f} MB |")
    if T["fail_goosecc"]:
        out.append(f"\ngoosecc failed on {T['fail_goosecc']} files.")
    if have_tcc:
        out.append("")
        out.append("On the files TinyCC compiles (`tcc -c`, same -D/-I flags):")
        out.append("")
        out.append("| program | files | clang-20 -O0 -c | goosecc -c | tcc -c | goosecc / tcc | tcc peak RSS |")
        out.append("|---|---:|---:|---:|---:|---:|---:|")
        for name, t in rows + [("**total**", T)]:
            if t["tcc_files"] == 0:
                out.append(f"| {name} | 0 | | | | | |")
                continue
            out.append(f"| {name} | {t['tcc_files']} | {t['tcc_clang'] * 1e3:.0f} ms | {t['tcc_goosecc'] * 1e3:.0f} ms | "
                       f"{t['tcc'] * 1e3:.0f} ms | {t['tcc_goosecc'] / t['tcc']:.2f} | {t['rss_tcc'] / 1024:.0f} MB |")
    out.append("")
    out.append("goosecc phases (sum of one --time run per file):")
    out.append("")
    out.append("| program | " + " | ".join(PHASES) + " |")
    out.append("|---|" + "---:|" * 5)
    for name, t in rows:
        out.append(f"| {name} | " + " | ".join(f"{x * 1e3:.0f} ms" for x in t["ph"]) + " |")
    out.append("| **total** | " + " | ".join(f"{x * 1e3:.0f} ms" for x in T["ph"]) + " |")
    text = "\n".join(out) + "\n"
    print(text)
    if a.md:
        open(a.md, "w").write(text)
    if a.json:
        json.dump({"files": files, "programs": {n: t for n, t in rows}}, open(a.json, "w"), indent=1)


def bench_g(a, tests):
    # --g: what -g costs goosecc, next to clang -O0 -g
    tmp = tempfile.mkdtemp(prefix="bench_goosecc_")
    obj = os.path.join(tmp, "x.o")
    rows, files = [], []
    keys = ("clang_g", "goosecc", "goosecc_g")
    for t in tests:
        tot = {k: 0.0 for k in keys}
        tot.update({"files": 0, "ph": [0.0] * 5, "ph_g": [0.0] * 5, "rss_goosecc": 0, "rss_goosecc_g": 0,
                    "rss_clang_g": 0, "size": 0, "size_g": 0, "fail": 0})
        for s in t.srcs:
            fl = ["-w"] + t.cflags
            tc, rc_, ec, _ = best([a.clang, "-O0", "-g", "-c"] + fl + [s, "-o", obj], a.n)
            tg, rg, eg, _ = best([a.goosecc, "-c"] + fl + [s, "-o", obj], a.n)
            sz = os.path.getsize(obj) if eg == 0 else 0
            tgg, rgg, egg, _ = best([a.goosecc, "-g", "-c"] + fl + [s, "-o", obj], a.n)
            szg = os.path.getsize(obj) if egg == 0 else 0
            ph = phases(a.goosecc, fl, s, obj)
            phg = phases(a.goosecc, ["-g"] + fl, s, obj)
            tot["files"] += 1
            tot["clang_g"] += tc
            tot["goosecc"] += tg
            tot["goosecc_g"] += tgg
            tot["size"] += sz
            tot["size_g"] += szg
            tot["fail"] += (eg != 0) + (egg != 0)
            tot["rss_clang_g"] = max(tot["rss_clang_g"], rc_)
            tot["rss_goosecc"] = max(tot["rss_goosecc"], rg)
            tot["rss_goosecc_g"] = max(tot["rss_goosecc_g"], rgg)
            for i in range(5):
                tot["ph"][i] += ph[i]
                tot["ph_g"][i] += phg[i]
            files.append({"program": t.name, "file": os.path.relpath(s, a.suite), "clang_g": tc, "goosecc": tg,
                          "goosecc_g": tgg, "phases": ph, "phases_g": phg})
            print(f"{t.name} {os.path.basename(s)}: clang -g {tc * 1e3:.1f} ms, goosecc {tg * 1e3:.1f} ms, "
                  f"goosecc -g {tgg * 1e3:.1f} ms", flush=True)
        rows.append((t.name, tot))
    T = {k: sum(t[k] for _, t in rows) for k in keys + ("files", "size", "size_g", "fail")}
    T["ph"] = [sum(t["ph"][i] for _, t in rows) for i in range(5)]
    T["ph_g"] = [sum(t["ph_g"][i] for _, t in rows) for i in range(5)]
    for k in ("rss_clang_g", "rss_goosecc", "rss_goosecc_g"):
        T[k] = max(t[k] for _, t in rows)
    out = ["| program | files | clang-20 -O0 -g -c | goosecc -c | goosecc -g -c | -g / no -g | clang -g / goosecc -g |",
           "|---|---:|---:|---:|---:|---:|---:|"]
    for name, t in rows + [("**total**", T)]:
        out.append(f"| {name} | {t['files']} | {t['clang_g'] * 1e3:.0f} ms | {t['goosecc'] * 1e3:.0f} ms | "
                   f"{t['goosecc_g'] * 1e3:.0f} ms | {t['goosecc_g'] / t['goosecc']:.2f}x | "
                   f"{t['clang_g'] / t['goosecc_g']:.2f}x |")
    out.append("")
    out.append(f"Peak RSS: clang -g {T['rss_clang_g'] / 1024:.0f} MB, goosecc {T['rss_goosecc'] / 1024:.0f} MB, "
               f"goosecc -g {T['rss_goosecc_g'] / 1024:.0f} MB. Objects: {T['size'] / 1e6:.1f} MB without -g, "
               f"{T['size_g'] / 1e6:.1f} MB with." + (f" Failures: {T['fail']}." if T["fail"] else ""))
    out.append("")
    out.append("goosecc phases (sum of one --time run per file), without and with -g:")
    out.append("")
    out.append("| | " + " | ".join(PHASES) + " |")
    out.append("|---|" + "---:|" * 5)
    out.append("| goosecc -c | " + " | ".join(f"{x * 1e3:.0f} ms" for x in T["ph"]) + " |")
    out.append("| goosecc -g -c | " + " | ".join(f"{x * 1e3:.0f} ms" for x in T["ph_g"]) + " |")
    text = "\n".join(out) + "\n"
    print(text)
    if a.md:
        open(a.md, "w").write(text)
    if a.json:
        json.dump({"files": files, "programs": {n: t for n, t in rows}}, open(a.json, "w"), indent=1)


if __name__ == "__main__":
    main()
