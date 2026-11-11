#!/usr/bin/env python3
"""Compile time per optimization level on CTMark (milestone E2).

For every CTMark source file of the test suite (the files tests/suite.py
builds for the ctmark and ctmark-cxx corpora, with their flags), at each
level L of --levels:

  clang -L -c -ftime-trace       wall time, and LLVM's middle end + code
                                 generation (the time-trace totals of
                                 Optimizer and CodeGenPasses)
  goovm-cc -L --time -c          wall time, and goovm's part: GIR export +
                                 the Goose middle end and back end
                                 (export_us + codegen_us of `--time`)

Each compile is run --runs times, the fastest kept; one file at a time.
Prints a Markdown table per level (seconds, per program) and writes the
raw numbers as JSON.

usage: compile_levels.py --cc GOOVM_CC [--levels O1,O2,O3,Os,Oz] [--runs 2]
                         [--out results.json] [--programs a,b]
"""
import argparse, json, os, re, subprocess, sys, tempfile, time
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "tests"))
import suite  # noqa: E402

SUITE = "/home/user/llvm/llvm-test-suite"


def best(n, f):
    r = None
    for _ in range(n):
        x = f()
        if x is None:
            return None
        if r is None or x[0] < r[0]:
            r = x
    return r


def clang_one(cc, lv, flags, src, obj, trace_dir):
    def run():
        t0 = time.perf_counter()
        p = subprocess.run([cc, "-" + lv, "-c", "-w", "-ftime-trace", "-ftime-trace-granularity=0"] + flags +
                           [src, "-o", obj], capture_output=True)
        wall = time.perf_counter() - t0
        if p.returncode != 0:
            return None
        tr = os.path.splitext(obj)[0] + ".json"
        opt = cg = 0.0
        try:
            with open(tr) as f:
                d = json.load(f)
            for e in d.get("traceEvents", []):
                if e.get("ph") != "X" or not e.get("name", "").startswith("Total "):
                    continue
                n = e["name"][6:]
                if n == "Optimizer":
                    opt = e["dur"] / 1e6
                elif n == "CodeGenPasses":
                    cg = e["dur"] / 1e6
        except (OSError, ValueError):
            pass
        return (wall, opt + cg)
    return best(ARGS.runs, run)


def goovm_one(cc, lv, flags, src, obj):
    def run():
        t0 = time.perf_counter()
        p = subprocess.run([cc, "-" + lv, "--time", "-c", "-w"] + flags + [src, "-o", obj], capture_output=True)
        wall = time.perf_counter() - t0
        if p.returncode != 0:
            return None
        m = re.search(rb"goovm-cc-time:.*", p.stderr)
        part = 0.0
        if m:
            kv = dict(re.findall(rb"(\w+)=(\d+)", m.group(0)))
            part = (int(kv.get(b"export_us", 0)) + int(kv.get(b"codegen_us", 0))) / 1e6
        return (wall, part)
    return best(ARGS.runs, run)


def main():
    global ARGS
    ap = argparse.ArgumentParser()
    ap.add_argument("--cc", required=True)
    ap.add_argument("--clang", default="clang-20")
    ap.add_argument("--clangxx", default="clang++-20")
    ap.add_argument("--levels", default="O1,O2,O3,Os,Oz")
    ap.add_argument("--runs", type=int, default=2)
    ap.add_argument("--programs", default="")
    ap.add_argument("--out", default="")
    ARGS = ap.parse_args()
    tests = suite.all_tests(SUITE, ["ctmark", "ctmark-cxx"])
    if ARGS.programs:
        want = ARGS.programs.split(",")
        tests = [t for t in tests if any(w in t.id for w in want)]
    levels = [l for l in ARGS.levels.split(",") if l]
    res = defaultdict(lambda: defaultdict(lambda: [0.0, 0.0, 0.0, 0.0, 0]))
    tmp = tempfile.mkdtemp(prefix="ctlv")
    for t in tests:
        prog = t.id.split("/")[-1]
        for s in t.srcs:
            cxx = s.endswith(suite.CXX_EXTS)
            flags = t.flags(s)
            for lv in levels:
                o1 = os.path.join(tmp, "c.o")
                o2 = os.path.join(tmp, "g.o")
                c = clang_one(ARGS.clangxx if cxx else ARGS.clang, lv, flags, s, o1, tmp)
                g = goovm_one(ARGS.cc, lv, flags, s, o2)
                if c is None or g is None:
                    print(f"skip {s} {lv}", file=sys.stderr)
                    continue
                r = res[lv][prog]
                r[0] += c[0]
                r[1] += c[1]
                r[2] += g[0]
                r[3] += g[1]
                r[4] += 1
        print(f"{prog} done", file=sys.stderr)
    for lv in levels:
        print(f"\n### -{lv}\n")
        print("| program | files | clang wall | goovm-cc wall | wall ratio | LLVM opt+codegen | goovm export+back end | ratio |")
        print("|---|---:|---:|---:|---:|---:|---:|---:|")
        tot = [0.0] * 4
        for prog in sorted(res[lv]):
            r = res[lv][prog]
            for k in range(4):
                tot[k] += r[k]
            print(f"| {prog} | {r[4]} | {r[0]:.2f} | {r[2]:.2f} | {r[0] / r[2]:.2f}x | {r[1]:.2f} | {r[3]:.2f} | "
                  f"{r[1] / max(r[3], 1e-9):.1f}x |")
        print(f"| **total** | | {tot[0]:.2f} | {tot[2]:.2f} | **{tot[0] / tot[2]:.2f}x** | {tot[1]:.2f} | {tot[3]:.2f} | "
              f"**{tot[1] / max(tot[3], 1e-9):.1f}x** |")
    if ARGS.out:
        with open(ARGS.out, "w") as f:
            json.dump({lv: dict(v) for lv, v in res.items()}, f, indent=1)


if __name__ == "__main__":
    main()
