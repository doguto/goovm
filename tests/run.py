#!/usr/bin/env python3
"""Differential tests for goovm-llc.

For every tests/c/*.c program:
  reference:  clang-20 -O0 x.c -o ref                      (run, record stdout + exit code)
  O0:         clang-20 -O0 -emit-llvm -> goovm-llc --backend=cpp -> clang-20 link -> run, compare
  mem2reg:    clang-20 -O0 -Xclang -disable-O0-optnone -emit-llvm
              -> opt-20 -passes=mem2reg -> goovm-llc -> link -> run, compare (PHI-heavy input)
Optional extra variants:
  --opt PASSES   also run opt-20 -passes=PASSES on the mem2reg input (e.g. "sroa,instcombine,simplifycfg")
  --backend B    goovm-llc back-end to test (cpp, goose, llvm)
  --tpde PATH    also compile the O0 bitcode with tpde-llc and compare

usage: tests/run.py [--goovm PATH] [-j N] [--work DIR] [--keep] [filter ...]
Exit status 0 iff every comparison passed.
"""
import argparse
import concurrent.futures as cf
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)


def run(cmd, timeout=60, **kw):
    return subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout, **kw)


class Fail(Exception):
    pass


def step(cmd, what):
    r = run(cmd)
    if r.returncode != 0:
        raise Fail(f"{what} failed ({r.returncode}): {' '.join(cmd)}\n{r.stderr.decode(errors='replace')[-2000:]}")
    return r


def execute(exe):
    try:
        r = run([exe], timeout=20)
    except subprocess.TimeoutExpired:
        return (b"<timeout>", -999)
    return (r.stdout, r.returncode)


def test_one(src, args):
    name = os.path.splitext(os.path.basename(src))[0]
    wd = os.path.join(args.work, name)
    os.makedirs(wd, exist_ok=True)
    cc = args.clang
    results = []
    try:
        ref = os.path.join(wd, "ref")
        step([cc, "-O0", "-w", src, "-o", ref], "reference build")
        expect = execute(ref)

        bcs = []
        bc = os.path.join(wd, "O0.bc")
        step([cc, "-O0", "-w", "-c", "-emit-llvm", src, "-o", bc], "clang -emit-llvm")
        bcs.append(("O0", bc))
        raw = os.path.join(wd, "noopt.bc")
        step([cc, "-O0", "-w", "-Xclang", "-disable-O0-optnone", "-c", "-emit-llvm", src, "-o", raw], "clang -emit-llvm")
        m2r = os.path.join(wd, "mem2reg.bc")
        step([args.opt, "-passes=mem2reg", raw, "-o", m2r], "opt mem2reg")
        bcs.append(("mem2reg", m2r))
        if args.opt_passes:
            ob = os.path.join(wd, "opt.bc")
            step([args.opt, f"-passes={args.opt_passes}", raw, "-o", ob], "opt")
            bcs.append(("opt", ob))

        for variant, bcf in bcs:
            obj = bcf[:-3] + ".o"
            exe = bcf[:-3] + ".exe"
            try:
                r = run([args.goovm, f"--backend={args.backend}", bcf, "-o", obj])
                if r.returncode != 0:
                    raise Fail(f"goovm-llc exit {r.returncode}: {r.stderr.decode(errors='replace').strip()}")
                step([cc, obj, "-o", exe], "link")
                got = execute(exe)
                if got != expect:
                    raise Fail(f"output mismatch: expected exit {expect[1]}, got {got[1]}\n"
                               f"--- expected\n{expect[0].decode(errors='replace')[:1500]}\n"
                               f"--- got\n{got[0].decode(errors='replace')[:1500]}")
                results.append((variant, True, ""))
            except Fail as e:
                results.append((variant, False, str(e)))
        if args.tpde:
            obj = os.path.join(wd, "tpde.o")
            exe = os.path.join(wd, "tpde.exe")
            try:
                step([args.tpde, bc, "-o", obj], "tpde-llc")
                step([cc, obj, "-o", exe], "link")
                got = execute(exe)
                if got != expect:
                    raise Fail(f"tpde output mismatch: expected exit {expect[1]}, got {got[1]}")
                results.append(("tpde", True, ""))
            except Fail as e:
                results.append(("tpde", False, str(e)))
    except Fail as e:
        results.append(("setup", False, str(e)))
    return name, results


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goovm", default=os.environ.get("GOOVM_LLC", os.path.join(ROOT, "build/tools/goovm-llc/goovm-llc")))
    ap.add_argument("--backend", default="goose")
    ap.add_argument("--clang", default="clang-20")
    ap.add_argument("--opt", default="opt-20")
    ap.add_argument("--opt-passes", dest="opt_passes", default="")
    ap.add_argument("--tpde", default="")
    ap.add_argument("-j", type=int, default=2)
    ap.add_argument("--work", default="")
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("filter", nargs="*")
    args = ap.parse_args()
    if not os.path.exists(args.goovm):
        sys.exit(f"goovm-llc not found at {args.goovm} (use --goovm or GOOVM_LLC)")
    tmp = None
    if not args.work:
        tmp = tempfile.mkdtemp(prefix="goovm-tests-")
        args.work = tmp
    srcs = sorted(os.path.join(HERE, "c", f) for f in os.listdir(os.path.join(HERE, "c")) if f.endswith(".c"))
    if args.filter:
        srcs = [s for s in srcs if any(f in os.path.basename(s) for f in args.filter)]

    passed = failed = 0
    with cf.ThreadPoolExecutor(max_workers=args.j) as ex:
        for name, results in ex.map(lambda s: test_one(s, args), srcs):
            line = []
            for variant, ok, msg in results:
                line.append(f"{variant}:{'ok' if ok else 'FAIL'}")
                if ok:
                    passed += 1
                else:
                    failed += 1
            print(f"{name:28s} {'  '.join(line)}")
            for variant, ok, msg in results:
                if not ok:
                    print("    [" + variant + "] " + msg.replace("\n", "\n    "))
    print(f"\n{passed} passed, {failed} failed ({len(srcs)} programs)")
    if tmp and not args.keep and failed == 0:
        shutil.rmtree(tmp, ignore_errors=True)
    elif tmp:
        print(f"work dir: {tmp}")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
