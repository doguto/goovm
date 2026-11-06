#!/usr/bin/env python3
"""End to end: how much of a CTMark -O0 build does a faster back-end save?

Every CTMark compile is split in two steps, and the second step is done by
each back-end in turn:

  front   clang -O0 -c -emit-llvm x.c -o x.bc    (front end + bitcode write)
  llc     llc-20 -O0 -relocation-model=pic -filetype=obj x.bc           (LLVM's -O0 back-end)
  tpde    tpde-llc x.bc                            (TPDE-LLVM)
  goovm   goovm-llc --backend=cpp|goose x.bc       (only files in its subset)

and, for reference, the normal one-step compile:

  clang   clang -O0 -c x.c                         (integrated)

Process start-up (about 15-20 ms per tool with Ubuntu's shared libLLVM)
dominates small files, so the in-process back-end time is also collected:
LLVM -O0 code generation as run inside goovm-llc --backend=llvm, TPDE's
"Compile" span from its --time-trace, and goovm's export + back-end. From
these, "clang+X in-process" estimates a compiler with back-end X built in:
  clang -O0 -c wall  -  LLVM back-end time  +  X back-end time.

Each step is run --runs times, keeping the fastest. Splitting adds a bitcode
write and read that the integrated compile doesn't have; it is the same for
every back-end, so the back-end columns compare like with like.

usage: ctmark_backends.py compile_commands.json --tpde PATH [--goovm PATH]
                          [--goose] [--runs 2] [--out results.json]
"""
import argparse, json, os, shlex, subprocess, sys, tempfile, time
from collections import defaultdict

PROGRAMS = ["7zip", "Bullet", "ClamAV", "SPASS", "consumer-typeset",
            "kimwitu++", "lencod", "mafft", "sqlite3", "tramp3d-v4"]


def program_of(path):
    for p in PROGRAMS:
        if f"/{p}/" in path:
            return p
    return None


def compiler_args(entry):
    args = shlex.split(entry["command"]) if "command" in entry else list(entry["arguments"])
    for i, a in enumerate(args):
        if os.path.basename(a).startswith(("clang", "gcc", "g++", "cc", "c++")):
            return args[i:]
    return args


def goovm_time(goovm, backend, bc, obj, cwd, runs):
    """Best in-process (export + back-end) time of goovm-llc, in seconds."""
    best = None
    for _ in range(runs):
        r = subprocess.run([goovm, f"--backend={backend}", "--time", bc, "-o", obj], cwd=cwd,
                           stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
        if r.returncode != 0:
            return None
        kv = dict(x.split("=") for x in r.stderr.split("goovm-time:")[1].split())
        t = (int(kv["export_us"]) + int(kv["backend_us"])) / 1e6
        best = t if best is None else min(best, t)
    return best


def tpde_compile_time(tpde, bc, obj, cwd, runs, trace):
    best = None
    for _ in range(runs):
        r = subprocess.run([tpde, f"--time-trace={trace}", bc, "-o", obj], cwd=cwd,
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        if r.returncode != 0:
            return None
        ev = json.load(open(trace))
        ev = ev["traceEvents"] if isinstance(ev, dict) else ev
        t = sum(e.get("dur", 0) for e in ev if e.get("name") == "Total Compile") / 1e6
        best = t if best is None else min(best, t)
    return best


def timed(cmd, cwd, runs):
    best, rc = None, 0
    for _ in range(runs):
        t0 = time.perf_counter()
        r = subprocess.run(cmd, cwd=cwd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        dt = time.perf_counter() - t0
        rc = r.returncode
        if rc != 0:
            return None, rc
        best = dt if best is None else min(best, dt)
    return best, rc


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("ccjson")
    ap.add_argument("--tpde", required=True)
    ap.add_argument("--llc", default="llc-20")
    ap.add_argument("--goovm")
    ap.add_argument("--goose", action="store_true", help="also time goovm-llc --backend=goose")
    ap.add_argument("--runs", type=int, default=2)
    ap.add_argument("--out", default="ctmark_backends.json")
    a = ap.parse_args()

    entries = [e for e in json.load(open(a.ccjson)) if program_of(e["file"])]
    tmp = tempfile.mkdtemp(prefix="e2e-")
    bc, obj = os.path.join(tmp, "x.bc"), os.path.join(tmp, "x.o")
    trace = os.path.join(tmp, "t.json")
    per = defaultdict(lambda: defaultdict(float))
    goovm_files = defaultdict(int)
    for i, e in enumerate(entries):
        prog = program_of(e["file"])
        args = compiler_args(e)
        oi = args.index("-o")
        base = args[:oi] + args[oi + 2:]
        cwd = e["directory"]
        t_clang, _ = timed(base + ["-o", obj], cwd, a.runs)
        t_front, rc = timed(base + ["-emit-llvm", "-o", bc], cwd, a.runs)
        if t_front is None:
            print(f"front end failed ({rc}): {e['file']}", file=sys.stderr)
            continue
        t_llc, _ = timed([a.llc, "-O0", "-relocation-model=pic", "-filetype=obj", bc, "-o", obj], cwd, a.runs)
        t_tpde, rc_t = timed([a.tpde, bc, "-o", obj], cwd, a.runs)
        d = per[prog]
        if a.goovm:
            ip_llvm = goovm_time(a.goovm, "llvm", bc, obj, cwd, a.runs)
            ip_tpde = tpde_compile_time(a.tpde, bc, obj, cwd, a.runs, trace) if t_tpde is not None else None
            d["ip_llvm"] += ip_llvm or 0
            d["ip_tpde"] += ip_tpde if ip_tpde is not None else (ip_llvm or 0)
        d["files"] += 1
        d["clang"] += t_clang or 0
        d["front"] += t_front
        d["llc"] += t_llc or 0
        if t_tpde is None:
            d["tpde_fail"] += 1
            d["tpde"] += t_llc or 0  # count the fallback a real integration would use
        else:
            d["tpde"] += t_tpde
        if a.goovm:
            t_g, rc_g = timed([a.goovm, "--backend=cpp", bc, "-o", obj], cwd, 1)
            if t_g is not None:
                t_g, _ = timed([a.goovm, "--backend=cpp", bc, "-o", obj], cwd, a.runs)
                goovm_files[prog] += 1
                d["goovm_files"] += 1
                d["goovm_llc"] += t_llc or 0      # llc on the same subset
                d["goovm_cpp"] += t_g
                d["ip_goovm_llvm"] += ip_llvm or 0
                d["ip_goovm_tpde"] += ip_tpde or 0
                d["ip_goovm_cpp"] += goovm_time(a.goovm, "cpp", bc, obj, cwd, a.runs) or 0
                if a.goose:
                    t_gs, _ = timed([a.goovm, "--backend=goose", bc, "-o", obj], cwd, a.runs)
                    d["goovm_goose"] += t_gs or 0
                    d["ip_goovm_goose"] += goovm_time(a.goovm, "goose", bc, obj, cwd, a.runs) or 0
        if (i + 1) % 50 == 0:
            print(f"  {i + 1}/{len(entries)}", file=sys.stderr, flush=True)

    with open(a.out, "w") as f:
        json.dump(per, f, indent=1)

    print("| program | files | clang -O0 -c | front (→ .bc) | llc -O0 | tpde-llc | front+llc | front+tpde | e2e gain |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---:|")
    tot = defaultdict(float)
    for p in PROGRAMS:
        d = per.get(p)
        if not d:
            continue
        for k, v in d.items():
            tot[k] += v
        fl, ft = d["front"] + d["llc"], d["front"] + d["tpde"]
        print(f"| {p} | {int(d['files'])} | {d['clang']:.2f} | {d['front']:.2f} | {d['llc']:.2f} | {d['tpde']:.2f} | "
              f"{fl:.2f} | {ft:.2f} | {fl / ft:.2f}x |")
    fl, ft = tot["front"] + tot["llc"], tot["front"] + tot["tpde"]
    print(f"| **total** | {int(tot['files'])} | {tot['clang']:.2f} | {tot['front']:.2f} | {tot['llc']:.2f} | "
          f"{tot['tpde']:.2f} | {fl:.2f} | {ft:.2f} | {fl / ft:.2f}x |")
    print(f"\nback-end only: llc {tot['llc']:.2f}s vs tpde {tot['tpde']:.2f}s = {tot['llc'] / max(tot['tpde'], 1e-9):.1f}x"
          f" (tpde failures fell back to llc: {int(tot['tpde_fail'])} files)")
    if a.goovm:
        est = tot["clang"] - tot["ip_llvm"] + tot["ip_tpde"]
        print(f"\nin-process back-end: LLVM -O0 {tot['ip_llvm']:.2f}s, TPDE {tot['ip_tpde']:.2f}s "
              f"({tot['ip_llvm'] / max(tot['ip_tpde'], 1e-9):.1f}x)")
        print(f"clang -O0 -c total {tot['clang']:.2f}s -> with TPDE built in (estimate) {est:.2f}s "
              f"= {tot['clang'] / est:.2f}x end to end")
        if tot["goovm_files"]:
            line = (f"goovm subset ({int(tot['goovm_files'])} files), in-process: LLVM {tot['ip_goovm_llvm']:.3f}s, "
                    f"TPDE {tot['ip_goovm_tpde']:.3f}s, goovm-cpp {tot['ip_goovm_cpp']:.3f}s")
            if a.goose:
                line += f", goovm-goose {tot['ip_goovm_goose']:.3f}s"
            print(line)
    if a.goovm and tot["goovm_files"]:
        line = (f"goovm subset ({int(tot['goovm_files'])} files): llc {tot['goovm_llc']:.2f}s, "
                f"goovm-cpp {tot['goovm_cpp']:.2f}s")
        if a.goose:
            line += f", goovm-goose {tot['goovm_goose']:.2f}s"
        print(line)


if __name__ == "__main__":
    main()
