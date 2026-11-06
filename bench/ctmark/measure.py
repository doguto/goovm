#!/usr/bin/env python3
"""Measure where clang spends compile time on CTMark.

Reads a compile_commands.json produced by configuring llvm-test-suite with
TEST_SUITE_SUBDIRS=CTMark, reruns every CTMark compile serially with
-ftime-trace, and aggregates the clang time-trace totals per program:
Frontend, Optimizer (middle end), CodeGenPasses (back end), plus the
hottest individual passes. Each file is compiled `--runs` times and the
fastest run is kept. Nothing that is compiled is executed.

With --groups llvm it instead measures llvm-project's own sources, grouped
by directory under llvm/lib (Target/X86, Transforms, ...), optionally on a
random --sample of the files.

usage: measure.py compile_commands.json out.json [--runs N] [--label L]
                  [--groups ctmark|llvm] [--sample N] [--seed S]
"""
import argparse, json, os, random, re, shlex, subprocess, sys, tempfile, time
from collections import defaultdict

PROGRAMS = ["7zip", "Bullet", "ClamAV", "SPASS", "consumer-typeset",
            "kimwitu++", "lencod", "mafft", "sqlite3", "tramp3d-v4"]
KEYS = ["ExecuteCompiler", "Frontend", "Optimizer", "CodeGenPasses", "Backend"]
# Container events whose time is already counted by their children.
CONTAINERS = ("PassManager", "Adaptor", "Wrapper", "DevirtSCC", "OptModule",
              "OptFunction", "RunPass", "RunLoopPass", "Parse", "CodeGen Function",
              "ExecuteCompiler", "Frontend", "Optimizer", "CodeGenPasses",
              "Backend", "Source", "PerformPendingInstantiations",
              "InstantiateFunction", "InstantiateClass", "Evaluate",
              "isIntegerConstantExpr", "DebugType", "DebugFunction",
              "DebugGlobalVariable", "DebugConstGlobalVariable",
              "CodeGen", "Machine", "LoopPass", "CGSCC")


GROUPS = "ctmark"


def program_of(path):
    if GROUPS == "llvm":
        m = re.search(r"/llvm/lib/([^/]+)(?:/([^/]+))?/", path)
        if not m:
            return None
        return f"{m.group(1)}/{m.group(2)}" if m.group(1) == "Target" and m.group(2) else m.group(1)
    for p in PROGRAMS:
        if f"/{p}/" in path:
            return p
    return None


def run_one(entry, trace_path, obj_path):
    args = shlex.split(entry["command"]) if "command" in entry else list(entry["arguments"])
    # The test-suite wraps compiles in its own `timeit` tool; drop the wrapper
    # and run the compiler directly.
    for i, a in enumerate(args):
        if os.path.basename(a).startswith(("clang", "gcc", "g++", "cc", "c++")):
            args = args[i:]
            break
    # Redirect the object file so the build tree is untouched.
    if "-o" in args:
        args[args.index("-o") + 1] = obj_path
    args += [f"-ftime-trace={trace_path}", "-ftime-trace-granularity=0"]
    t0 = time.perf_counter()
    r = subprocess.run(args, cwd=entry["directory"], stdout=subprocess.DEVNULL,
                       stderr=subprocess.PIPE)
    wall = time.perf_counter() - t0
    if r.returncode != 0:
        raise RuntimeError(f"compile failed: {entry['file']}\n{r.stderr.decode()[:2000]}")
    with open(trace_path) as f:
        trace = json.load(f)
    totals = {}
    for e in trace["traceEvents"]:
        n = e.get("name", "")
        if n.startswith("Total ") and "dur" in e:
            totals[n[6:]] = e["dur"] / 1e6
    return wall, totals


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("ccjson")
    ap.add_argument("out")
    ap.add_argument("--runs", type=int, default=2)
    ap.add_argument("--label", default="")
    ap.add_argument("--groups", choices=["ctmark", "llvm"], default="ctmark")
    ap.add_argument("--sample", type=int, default=0)
    ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args()
    global GROUPS
    GROUPS = a.groups

    entries = [e for e in json.load(open(a.ccjson)) if program_of(e["file"])]
    if a.sample and a.sample < len(entries):
        entries = random.Random(a.seed).sample(entries, a.sample)
    print(f"{len(entries)} CTMark compile commands", file=sys.stderr)
    tmp = tempfile.mkdtemp(prefix="ctmark-")
    trace_path, obj_path = os.path.join(tmp, "t.json"), os.path.join(tmp, "o.o")

    per_prog = defaultdict(lambda: defaultdict(float))
    per_pass = defaultdict(float)
    files = []
    for i, e in enumerate(entries):
        best = None
        for _ in range(a.runs):
            wall, totals = run_one(e, trace_path, obj_path)
            if best is None or wall < best[0]:
                best = (wall, totals)
        wall, totals = best
        prog = program_of(e["file"])
        per_prog[prog]["wall"] += wall
        per_prog[prog]["files"] += 1
        for k in KEYS:
            per_prog[prog][k] += totals.get(k, 0.0)
        for k, v in totals.items():
            if not any(c in k for c in CONTAINERS):
                per_pass[k] += v
        files.append({"file": e["file"], "program": prog, "wall": wall,
                      **{k: totals.get(k, 0.0) for k in KEYS}})
        if (i + 1) % 50 == 0:
            print(f"  {i + 1}/{len(entries)}", file=sys.stderr)

    result = {"label": a.label, "programs": per_prog, "files": files,
              "top_passes": sorted(per_pass.items(), key=lambda kv: -kv[1])[:40]}
    with open(a.out, "w") as f:
        json.dump(result, f, indent=1)

    # Human-readable summary.
    print(f"\n## {a.label}\n")
    print("| program | files | wall s | frontend | optimizer | codegen | FE % | opt % | CG % |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---:|")
    tot = defaultdict(float)
    for p in (PROGRAMS if GROUPS == "ctmark" else sorted(per_prog)):
        d = per_prog.get(p)
        if not d:
            continue
        for k, v in d.items():
            tot[k] += v
        ec = d["ExecuteCompiler"] or 1
        print(f"| {p} | {int(d['files'])} | {d['wall']:.2f} | {d['Frontend']:.2f} | "
              f"{d['Optimizer']:.2f} | {d['CodeGenPasses']:.2f} | "
              f"{100 * d['Frontend'] / ec:.0f} | {100 * d['Optimizer'] / ec:.0f} | "
              f"{100 * d['CodeGenPasses'] / ec:.0f} |")
    ec = tot["ExecuteCompiler"] or 1
    print(f"| **total** | {int(tot['files'])} | {tot['wall']:.2f} | {tot['Frontend']:.2f} | "
          f"{tot['Optimizer']:.2f} | {tot['CodeGenPasses']:.2f} | "
          f"{100 * tot['Frontend'] / ec:.0f} | {100 * tot['Optimizer'] / ec:.0f} | "
          f"{100 * tot['CodeGenPasses'] / ec:.0f} |")
    print("\nTop passes (s):")
    for k, v in result["top_passes"][:15]:
        print(f"  {v:7.2f}  {k}")


if __name__ == "__main__":
    main()
