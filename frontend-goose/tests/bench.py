#!/usr/bin/env python3
"""Speed: goosecc vs clang-20 for -E and -fsyntax-only, per file and in total.

Each command runs single-threaded, best of N wall-clock runs; peak RSS is the
child's ru_maxrss. Output goes to /dev/null.

usage: tests/bench.py [--goosecc build/goosecc] [-n 3] [--corpus ctmark] [--mode E,syntax]
                      [--per-file] [--md out.md] [files... -- flags]
"""
import argparse, os, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import corpus as corpus_mod


def run_once(cmd):
    t0 = time.perf_counter()
    p = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    _, status, ru = os.wait4(p.pid, 0)
    t1 = time.perf_counter()
    return t1 - t0, ru.ru_maxrss, os.waitstatus_to_exitcode(status)


def best(cmd, n):
    ts, rss, rc = [], 0, 0
    for _ in range(n):
        t, r, rc = run_once(cmd)
        ts.append(t)
        rss = max(rss, r)
    return min(ts), rss, rc


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--goosecc", default=os.path.join(HERE, "..", "build", "goosecc"))
    ap.add_argument("--clang", default="clang-20")
    ap.add_argument("-n", type=int, default=3)
    ap.add_argument("--corpus", default="ctmark")
    ap.add_argument("--mode", default="E,syntax")
    ap.add_argument("--per-file", action="store_true")
    ap.add_argument("--md", default="")
    ap.add_argument("rest", nargs="*")
    argv, cli_flags = corpus_mod.split_flags(sys.argv[1:])
    a = ap.parse_args(argv)
    if a.rest:
        files, flags = a.rest, cli_flags
        jobs = [("args", f, flags) for f in files]
    else:
        jobs = list(corpus_mod.corpus(a.corpus.split(",")))
    modes = a.mode.split(",")
    rows = []
    tot = {}
    for c, p, fl in jobs:
        prog = os.path.relpath(p, corpus_mod.SUITE)
        row = [prog]
        for m in modes:
            flag = "-E" if m == "E" else "-fsyntax-only"
            out = ["-o", "/dev/null"] if m == "E" else []
            tc, rc_, _ = best([a.clang, flag] + fl + [p] + out, a.n)
            tg, rg, rcg = best([a.goosecc, flag] + fl + [p] + out, a.n)
            k = tot.setdefault(m, [0, 0, 0, 0, 0])
            k[0] += tc; k[1] += tg; k[2] = max(k[2], rc_); k[3] = max(k[3], rg); k[4] += (rcg != 0)
            row += [tc, tg, rc_, rg, rcg]
        rows.append(row)
        if a.per_file:
            s = prog
            for i, m in enumerate(modes):
                tc, tg, rc_, rg, rcg = row[1 + 5 * i:6 + 5 * i]
                s += "  %s: clang %.1fms goosecc %.1fms (x%.2f)%s" % (m, tc * 1e3, tg * 1e3, tc / tg if tg else 0,
                                                                     "" if rcg == 0 else " rc=%d" % rcg)
            print(s, flush=True)
    lines = ["| mode | files | clang-20 total (s) | goosecc total (s) | speed-up | clang peak RSS (MB) | goosecc peak RSS (MB) | goosecc failures |",
             "|---|---:|---:|---:|---:|---:|---:|---:|"]
    for m in modes:
        k = tot[m]
        lines.append("| %s | %d | %.3f | %.3f | %.2fx | %.0f | %.0f | %d |" % (m, len(rows), k[0], k[1], k[0] / k[1] if k[1] else 0,
                                                                     k[2] / 1024, k[3] / 1024, k[4]))
    # per program (the directory under MultiSource/.../)
    progs = {}
    for r in rows:
        parts = r[0].split("/")
        key = "/".join(parts[:3]) if parts[0] == "MultiSource" else "/".join(parts[:-1])
        g = progs.setdefault(key, [0] + [0.0] * (2 * len(modes)))
        g[0] += 1
        for i in range(len(modes)):
            g[1 + 2 * i] += r[1 + 5 * i]
            g[2 + 2 * i] += r[2 + 5 * i]
    plines = ["| program | files |" + "".join(" %s clang (ms) | %s goosecc (ms) | x |" % (m, m) for m in modes),
              "|---|---:|" + "---:|---:|---:|" * len(modes)]
    for key in sorted(progs):
        g = progs[key]
        s = "| %s | %d |" % (key, g[0])
        for i in range(len(modes)):
            tc, tg = g[1 + 2 * i], g[2 + 2 * i]
            s += " %.0f | %.0f | %.2f |" % (tc * 1e3, tg * 1e3, tc / tg if tg else 0)
        plines.append(s)
    print("\n".join(lines))
    print("\n".join(plines))
    if a.md:
        with open(a.md, "w") as f:
            f.write("\n".join(lines) + "\n\n")
            f.write("\n".join(plines) + "\n\n")
            hdr = "| file |" + "".join(" %s clang (ms) | %s goosecc (ms) | x | goosecc RSS (MB) |" % (m, m) for m in modes)
            f.write(hdr + "\n|---|" + "---:|---:|---:|---:|" * len(modes) + "\n")
            for r in rows:
                s = "| %s |" % r[0]
                for i in range(len(modes)):
                    tc, tg, rc_, rg, rcg = r[1 + 5 * i:6 + 5 * i]
                    s += " %.1f | %.1f | %.2f | %.0f |" % (tc * 1e3, tg * 1e3, tc / tg if tg else 0, rg / 1024)
                f.write(s + "\n")


if __name__ == "__main__":
    main()
