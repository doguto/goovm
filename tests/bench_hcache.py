#!/usr/bin/env python3
"""goosecc's header cache (B4): compile time of CTMark's C files with the
cache disabled, cold and warm, against TinyCC and clang-20 -O0.

Every C file of a CTMark compile_commands.json (llvm-test-suite configured
with cmake/caches/O0.cmake; the 316 C files of sqlite3, SPASS, ClamAV,
consumer-typeset, lencod, mafft and 7zip) is compiled to an object, each
run alone and single-threaded, the variants interleaved file by file so
that the machine's load hits them alike; the time is the best of N:

  off    goosecc -fno-header-cache
  cold   goosecc with an empty cache (emptied before each run: the cost of
         recording every header the file includes)
  warm   goosecc with the cache that a previous compile of the same file
         filled
  tcc    tcc -c with the -D/-I flags (when installed)
  clang  the command as configured (clang-20 -O0 -c), unless --no-clang

--build adds builds of all the files in order, one run each: one without
the cache, then three with one cache that starts empty (a first build of
the whole suite, where later files replay what earlier ones recorded; a
second, where the main files' "..." includes are recorded too; a third,
all warm), and the size of that cache.

goosecc's phases come from one extra --time run per file and variant.

usage: tests/bench_hcache.py compile_commands.json --goosecc PATH [-n 5] [--no-clang]
                             [--build] [--md out.md] [--json out.json] [program ...]
"""
import argparse, json, os, re, shlex, shutil, subprocess, sys, tempfile, time
from collections import defaultdict

PROGRAMS = ["7zip", "ClamAV", "SPASS", "consumer-typeset", "lencod", "mafft", "sqlite3"]
PHASES = ["preprocess", "parse+sema", "lowering", "back-end", "write"]


def program_of(path):
    return next((p for p in PROGRAMS if f"/{p}/" in path), None)


def entries(ccjson):
    out = []
    for e in json.load(open(ccjson)):
        if not e["file"].endswith(".c") or not program_of(e["file"]):
            continue
        args = shlex.split(e["command"]) if "command" in e else list(e["arguments"])
        for i, a in enumerate(args):
            if os.path.basename(a).startswith(("clang", "gcc", "cc")):
                args = args[i:]
                break
        oi = args.index("-o")
        out.append((program_of(e["file"]), e["file"], e["directory"], args[0], args[1:oi] + args[oi + 2:]))
    return out


def run(cmd, cwd, env):
    t0 = time.perf_counter()
    r = subprocess.run(cmd, cwd=cwd, env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return time.perf_counter() - t0, r.returncode


def phases(cmd, cwd, env):
    r = subprocess.run(cmd + ["--time"], cwd=cwd, env=env, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    m = re.search(rb"preprocess (\d+) us, parse\+sema (\d+) us, lowering (\d+) us, back-end (\d+) us, write (\d+) us", r.stderr)
    return [int(x) / 1e6 for x in m.groups()] if m else [0.0] * 5


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("ccjson")
    ap.add_argument("--goosecc", required=True)
    ap.add_argument("--tcc", default="tcc")
    ap.add_argument("-n", type=int, default=5)
    ap.add_argument("--no-clang", action="store_true")
    ap.add_argument("--build", action="store_true")
    ap.add_argument("--md", default="")
    ap.add_argument("--json", default="")
    ap.add_argument("programs", nargs="*")
    a = ap.parse_args()
    g = os.path.abspath(a.goosecc)
    have_tcc = shutil.which(a.tcc) is not None
    ents = [e for e in entries(a.ccjson) if not a.programs or e[0] in a.programs]
    tmp = tempfile.mkdtemp(prefix="bench_hcache_")
    obj = os.path.join(tmp, "x.o")
    warm = os.path.join(tmp, "warm")
    cold = os.path.join(tmp, "cold")
    env = dict(os.environ)
    env_off = dict(env)
    env_warm = dict(env, GOOSECC_CACHE=warm)
    env_cold = dict(env, GOOSECC_CACHE=cold)
    variants = ["off", "cold", "warm"] + (["tcc"] if have_tcc else []) + ([] if a.no_clang else ["clang"])
    per = defaultdict(lambda: defaultdict(float))
    files = []
    # each variant overwrites an object of its own, as a rebuild does: on
    # ext4, truncating the file clang has just renamed into place often
    # costs a few tenths of a millisecond more (its delayed allocation),
    # which would go to whichever variant follows clang
    o = {v: os.path.join(tmp, f"{v}.o") for v in ("off", "cold", "warm", "tcc", "clang")}
    for k, (prog, f, d, cc, rest) in enumerate(ents):
        cmds = {
            "off": ([g, "-fno-header-cache"] + rest + ["-o", o["off"]], env_off),
            "cold": ([g] + rest + ["-o", o["cold"]], env_cold),
            "warm": ([g] + rest + ["-o", o["warm"]], env_warm),
            "tcc": ([a.tcc] + [x for x in rest if x.startswith(("-D", "-I", "-U", "-w", "-c"))] + [f, "-o", o["tcc"]], env),
            "clang": (["clang-20"] + rest + ["-o", o["clang"]], env),
        }
        run(cmds["warm"][0], d, env_warm)   # fill the warm cache
        best = {v: 1e9 for v in variants}
        ok = {v: True for v in variants}
        for _ in range(a.n):
            for v in variants:
                if v == "cold":
                    shutil.rmtree(cold, ignore_errors=True)
                t, rc = run(cmds[v][0], d, cmds[v][1])
                if rc != 0:
                    ok[v] = False
                best[v] = min(best[v], t)
        shutil.rmtree(cold, ignore_errors=True)
        ph = {v: phases(cmds[v][0], d, cmds[v][1]) for v in ("off", "warm")}
        shutil.rmtree(cold, ignore_errors=True)
        ph["cold"] = phases(cmds["cold"][0], d, env_cold)
        p = per[prog]
        p["files"] += 1
        for v in variants:
            p[v] += best[v]
            p["fail_" + v] += not ok[v]
        for v in ("off", "cold", "warm"):
            for i in range(5):
                p[f"{v}_{PHASES[i]}"] += ph[v][i]
        files.append({"program": prog, "file": f, **{v: best[v] for v in variants}, "phases": ph})
        print(f"[{k + 1}/{len(ents)}] {prog} {os.path.basename(f)}: " +
              ", ".join(f"{v} {best[v] * 1e3:.1f}" for v in variants), flush=True)
    build = None
    if a.build:
        shared = os.path.join(tmp, "build")
        envb = dict(env, GOOSECC_CACHE=shared)
        t0 = time.perf_counter()
        for prog, f, d, cc, rest in ents:
            run([g, "-fno-header-cache"] + rest + ["-o", obj], d, env)
        build = {"times": [], "off": time.perf_counter() - t0}
        for _ in range(3):
            t0 = time.perf_counter()
            for prog, f, d, cc, rest in ents:
                run([g] + rest + ["-o", obj], d, envb)
            build["times"].append(time.perf_counter() - t0)
        sizes = [os.path.getsize(os.path.join(dp, x)) for dp, dn, fn in os.walk(shared) for x in fn]
        build["bytes"], build["files"] = sum(sizes), len(sizes)
    T = defaultdict(float)
    for prog in per:
        for k2, v in per[prog].items():
            T[k2] += v
    rows = [(p, per[p]) for p in PROGRAMS if p in per] + [("**total**", T)]
    out = ["| program | files | " + " | ".join(variants) + " | warm/tcc | warm/off |", "|---|---:|" + "---:|" * (len(variants) + 2)]
    for name, p in rows:
        cells = [f"{p[v] * 1e3:.0f}" for v in variants]
        r_tcc = f"{p['tcc'] / p['warm']:.2f}x" if have_tcc else ""
        out.append(f"| {name} | {p['files']:.0f} | " + " | ".join(cells) + f" | {r_tcc} | {p['off'] / p['warm']:.2f}x |")
    out.append("")
    out.append("(milliseconds, best of %d per file; warm/tcc and warm/off: how many times faster warm is)" % a.n)
    out.append("")
    out.append("goosecc phases (ms, sum of one --time run per file):")
    out.append("")
    out.append("| program | variant | " + " | ".join(PHASES) + " |")
    out.append("|---|---|" + "---:|" * 5)
    for name, p in rows:
        for v in ("off", "cold", "warm"):
            out.append(f"| {name} | {v} | " + " | ".join(f"{p[f'{v}_{ph}'] * 1e3:.0f}" for ph in PHASES) + " |")
    if build is not None:
        b1, b2, b3 = build["times"]
        out.append("")
        out.append(f"Builds (all {len(ents)} files in order, one run each): without the cache {build['off']:.2f} s; "
                   f"with one cache starting empty, first {b1:.2f} s, "
                   f"second {b2:.2f} s, third {b3:.2f} s; the cache then holds {build['files']} files, "
                   f"{build['bytes'] / 1e6:.1f} MB")
    fails = {v: T["fail_" + v] for v in variants if T["fail_" + v]}
    if fails:
        out.append(f"\nfailures: {fails}")
    text = "\n".join(out) + "\n"
    print(text)
    if a.md:
        open(a.md, "w").write(text)
    if a.json:
        json.dump({"files": files, "build": build}, open(a.json, "w"), indent=1)
    shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    main()
