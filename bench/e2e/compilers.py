#!/usr/bin/env python3
"""End-to-end compile time of every CTMark file with each compiler.

For every compile command of llvm-test-suite's CTMark (configured with
cmake/caches/O0.cmake), each compiler compiles the file to an object, alone
and single-threaded; the fastest of --runs runs is kept:

  clang     the command as configured (clang-20 / clang++-20 -O0 -c)
  goovm-cc  the same arguments through goovm-cc --backend=goose
            (clang's front end in-process + the Goose back-end), C and C++
  goosecc   the Goose C compiler (front end and back-end in Goose), C only
  tcc       TinyCC, C only, when installed and when it accepts the file

With --g every compiler also gets -g. A compiler that fails on a file is
reported and left out of that file's comparison (and of the totals where
noted). Prints a markdown table per program and the totals.

usage: compilers.py compile_commands.json --goovm-cc PATH --goosecc PATH
                    [--tcc tcc] [--runs 3] [--g] [--out results.json]
"""
import argparse, json, os, shlex, subprocess, sys, tempfile, time
from collections import defaultdict

PROGRAMS = ["7zip", "Bullet", "ClamAV", "SPASS", "consumer-typeset",
            "kimwitu++", "lencod", "mafft", "sqlite3", "tramp3d-v4"]
CXX = (".cpp", ".cc", ".cxx", ".C")


def program_of(path):
    return next((p for p in PROGRAMS if f"/{p}/" in path), None)


def compiler_args(entry):
    args = shlex.split(entry["command"]) if "command" in entry else list(entry["arguments"])
    for i, a in enumerate(args):
        if os.path.basename(a).startswith(("clang", "gcc", "g++", "cc", "c++")):
            return args[i:]
    return args


def best(cmd, cwd, runs):
    t = None
    for _ in range(runs):
        t0 = time.perf_counter()
        r = subprocess.run(cmd, cwd=cwd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        dt = time.perf_counter() - t0
        if r.returncode != 0:
            return None
        t = dt if t is None else min(t, dt)
    return t


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("ccjson")
    ap.add_argument("--goovm-cc", required=True)
    ap.add_argument("--goosecc", required=True)
    ap.add_argument("--tcc", default="tcc")
    ap.add_argument("--runs", type=int, default=3)
    ap.add_argument("--g", action="store_true")
    ap.add_argument("--out", default="")
    a = ap.parse_args()
    # Each compile runs in its own directory, so tool paths must be absolute.
    a.goovm_cc, a.goosecc = os.path.abspath(a.goovm_cc), os.path.abspath(a.goosecc)
    have_tcc = subprocess.run(["which", a.tcc], capture_output=True).returncode == 0

    entries = [e for e in json.load(open(a.ccjson)) if program_of(e["file"])]
    tmp = tempfile.mkdtemp(prefix="compilers-")
    obj = os.path.join(tmp, "x.o")
    per = defaultdict(lambda: defaultdict(float))
    fails = defaultdict(int)
    for i, e in enumerate(entries):
        prog = program_of(e["file"])
        cxx = e["file"].endswith(CXX)
        args = compiler_args(e)
        oi = args.index("-o")
        rest = args[1:oi] + args[oi + 2:] + (["-g"] if a.g else []) + ["-o", obj]
        cwd = e["directory"]
        d = per[prog]
        d["files"] += 1
        d["cxx"] += 1 if cxx else 0
        tc = best([args[0]] + rest, cwd, a.runs)
        if tc is None:
            fails["clang"] += 1
            continue
        d["clang"] += tc
        tg = best([a.goovm_cc, "--backend=goose"] + rest, cwd, a.runs)
        if tg is None:
            fails["goovm-cc"] += 1
        else:
            d["goovm-cc"] += tg
            d["goovm-cc_clang"] += tc
        if not cxx:
            d["c_files"] += 1
            d["c_clang"] += tc
            ts = best([a.goosecc] + rest, cwd, a.runs)
            if ts is None:
                fails["goosecc"] += 1
            else:
                d["goosecc"] += ts
                d["goosecc_clang"] += tc
                d["goosecc_files"] += 1
            if have_tcc:
                tt = best([a.tcc] + [x for x in rest if not x.startswith(("-std=", "-Werror", "-W"))], cwd, a.runs)
                if tt is not None and ts is not None:
                    d["tcc"] += tt
                    d["tcc_goosecc"] += ts
                    d["tcc_files"] += 1
        if (i + 1) % 50 == 0:
            print(f"  {i + 1}/{len(entries)}", file=sys.stderr, flush=True)

    if a.out:
        with open(a.out, "w") as f:
            json.dump({"per": per, "fails": fails, "g": a.g, "runs": a.runs}, f, indent=1)

    def r(x, y):
        return f"{x / y:.2f}x" if y else "-"
    print(f"{'-O0 -g' if a.g else '-O0'}, best of {a.runs}, seconds (speed-up vs clang in parentheses)\n")
    print("| program | files (C++) | clang | goovm-cc | goosecc (C) | tcc (C, same files as goosecc) |")
    print("|---|---:|---:|---:|---:|---:|")
    tot = defaultdict(float)
    for p in PROGRAMS:
        d = per.get(p)
        if not d:
            continue
        for k, v in d.items():
            tot[k] += v
        gs = f"{d['goosecc']:.2f} ({r(d['goosecc_clang'], d['goosecc'])})" if d["goosecc_files"] else "-"
        tt = f"{d['tcc']:.2f} vs {d['tcc_goosecc']:.2f}" if d["tcc_files"] else "-"
        print(f"| {p} | {int(d['files'])} ({int(d['cxx'])}) | {d['clang']:.2f} | "
              f"{d['goovm-cc']:.2f} ({r(d['goovm-cc_clang'], d['goovm-cc'])}) | {gs} | {tt} |")
    print(f"| **total** | {int(tot['files'])} ({int(tot['cxx'])}) | {tot['clang']:.2f} | "
          f"{tot['goovm-cc']:.2f} ({r(tot['goovm-cc_clang'], tot['goovm-cc'])}) | "
          f"{tot['goosecc']:.2f} ({r(tot['goosecc_clang'], tot['goosecc'])}) | "
          f"{tot['tcc']:.2f} vs {tot['tcc_goosecc']:.2f} |")
    print(f"\nC files only: clang {tot['c_clang']:.2f}s over {int(tot['c_files'])} files; "
          f"goosecc compiled {int(tot['goosecc_files'])}; tcc compiled {int(tot['tcc_files'])} of them.")
    if fails:
        print("failures: " + ", ".join(f"{k} {v}" for k, v in fails.items()))


if __name__ == "__main__":
    main()
