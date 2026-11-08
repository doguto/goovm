#!/usr/bin/env python3
"""Differential tests for goovm-llc.

Programs: tests/c/*.c, tests/cxx/*.cpp, tests/mixed/<name>/ (several C
and C++ files linked together) and tests/ll/<name>/ (hand-written LLVM IR
files, for IR shapes clang does not produce, with a C driver; the reference
build compiles the IR with clang -O0 too). For each program:
  reference:  clang-20 / clang++-20 -O0 (run, record stdout + exit code)
  O0:         -O0 -emit-llvm -> goovm-llc --backend=goose -> link -> run, compare
  mem2reg:    -O0 -Xclang -disable-O0-optnone -emit-llvm
              -> opt-20 -passes=mem2reg -> goovm-llc -> link -> run, compare (PHI-heavy input)
  mixed programs also: c-goovm (the C files by goovm-llc, the C++ files by
              clang++) and cxx-goovm (the other way round), so that C++
              exceptions cross frames of the other compiler
Optional extra variants:
  --opt-passes P also run opt-20 -passes=P on the mem2reg input (e.g. "sroa,instcombine,simplifycfg")
  --backend B    goovm-llc back-end to test (goose, llvm)
  --tpde PATH    also compile the O0 bitcode with tpde-llc and compare
  --goosecc PATH instead of the goovm-llc variants, compile the C programs with goosecc -c
                 (variants goosecc and goosecc-g, i.e. with -g); no LLVM involved; with it the
                 programs of tests/cxx_d1/ (goosecc's C++ subset, milestone D1) run too

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


def is_cxx(s):
    return s.endswith((".cpp", ".cc"))


def is_ll(s):
    return s.endswith(".ll")


class Prog:
    def __init__(self, name, srcs):
        self.name = name
        self.srcs = srcs

    @property
    def cxx(self):
        return any(is_cxx(s) for s in self.srcs)

    @property
    def mixed(self):
        return self.cxx and not all(is_cxx(s) for s in self.srcs)


def compiler(s, args):
    return args.clangxx if is_cxx(s) else args.clang


def test_one(p, args):
    wd = os.path.join(args.work, p.name.replace("/", "__"))
    os.makedirs(wd, exist_ok=True)
    link = args.clangxx if p.cxx else args.clang
    results = []

    def compare(variant, objs):
        exe = os.path.join(wd, variant + ".exe")
        step([link] + objs + ["-o", exe, "-lm"], "link")
        got = execute(exe)
        if got != expect:
            raise Fail(f"output mismatch: expected exit {expect[1]}, got {got[1]}\n"
                       f"--- expected\n{expect[0].decode(errors='replace')[:1500]}\n"
                       f"--- got\n{got[0].decode(errors='replace')[:1500]}")

    try:
        refs = []
        for i, s in enumerate(p.srcs):
            o = os.path.join(wd, f"ref{i}.o")
            step([compiler(s, args), "-O0", "-w", "-c", s, "-o", o], "reference build")
            refs.append(o)
        ref = os.path.join(wd, "ref")
        step([link] + refs + ["-o", ref, "-lm"], "reference link")
        expect = execute(ref)

        if args.goosecc:
            for variant, flags in (("goosecc", []), ("goosecc-g", ["-g"])):
                try:
                    objs = []
                    for i, s in enumerate(p.srcs):
                        obj = os.path.join(wd, f"{variant}{i}.o")
                        r = run([args.goosecc, "-c", "-w"] + flags + [s, "-o", obj])
                        if r.returncode != 0:
                            raise Fail(f"goosecc exit {r.returncode}: {r.stderr.decode(errors='replace').strip()[:2000]}")
                        objs.append(obj)
                    compare(variant, objs)
                    results.append((variant, True, ""))
                except Fail as e:
                    results.append((variant, False, str(e)))
            return p.name, results

        def bitcode(s, i, variant):
            cc = compiler(s, args)
            base = os.path.join(wd, f"{variant}{i}")
            if is_ll(s):
                passes = "verify" if variant == "O0" else "mem2reg" if variant == "mem2reg" else args.opt_passes
                step([args.opt, f"-passes={passes}", s, "-o", base + ".bc"], "opt")
                return base + ".bc"
            if variant == "O0":
                step([cc, "-O0", "-w", "-c", "-emit-llvm", s, "-o", base + ".bc"], "clang -emit-llvm")
                return base + ".bc"
            raw = base + ".noopt.bc"
            step([cc, "-O0", "-w", "-Xclang", "-disable-O0-optnone", "-c", "-emit-llvm", s, "-o", raw],
                 "clang -emit-llvm")
            passes = "mem2reg" if variant == "mem2reg" else args.opt_passes
            step([args.opt, f"-passes={passes}", raw, "-o", base + ".bc"], "opt")
            return base + ".bc"

        def goovm(bcf):
            obj = bcf[:-3] + ".o"
            r = run([args.goovm, f"--backend={args.backend}", bcf, "-o", obj])
            if r.returncode != 0:
                raise Fail(f"goovm-llc exit {r.returncode} on {os.path.basename(bcf)}: "
                           f"{r.stderr.decode(errors='replace').strip()}")
            return obj

        variants = ["O0", "mem2reg"] + (["opt"] if args.opt_passes else [])
        for variant in variants:
            try:
                compare(variant, [goovm(bitcode(s, i, variant)) for i, s in enumerate(p.srcs)])
                results.append((variant, True, ""))
            except Fail as e:
                results.append((variant, False, str(e)))
        if p.mixed:
            for variant, which in (("c-goovm", False), ("cxx-goovm", True)):
                try:
                    objs = [goovm(bitcode(s, i, "O0")) if is_cxx(s) == which else refs[i]
                            for i, s in enumerate(p.srcs)]
                    compare(variant, objs)
                    results.append((variant, True, ""))
                except Fail as e:
                    results.append((variant, False, str(e)))
        if args.tpde and not p.cxx:
            try:
                objs = []
                for i, s in enumerate(p.srcs):
                    obj = os.path.join(wd, f"tpde{i}.o")
                    step([args.tpde, bitcode(s, i, "O0"), "-o", obj], "tpde-llc")
                    objs.append(obj)
                compare("tpde", objs)
                results.append(("tpde", True, ""))
            except Fail as e:
                results.append(("tpde", False, str(e)))
    except Fail as e:
        results.append(("setup", False, str(e)))
    return p.name, results


def programs():
    out = []
    for f in sorted(os.listdir(os.path.join(HERE, "c"))):
        if f.endswith(".c"):
            out.append(Prog(f[:-2], [os.path.join(HERE, "c", f)]))
    for f in sorted(os.listdir(os.path.join(HERE, "cxx"))):
        if f.endswith(".cpp"):
            out.append(Prog("cxx/" + f[:-4], [os.path.join(HERE, "cxx", f)]))
    for f in sorted(os.listdir(os.path.join(HERE, "cxx_d1"))):
        if f.endswith(".cpp"):
            out.append(Prog("cxx_d1/" + f[:-4], [os.path.join(HERE, "cxx_d1", f)]))
    for kind in ("mixed", "ll"):
        md = os.path.join(HERE, kind)
        for d in sorted(os.listdir(md)):
            srcs = sorted(os.path.join(md, d, f) for f in os.listdir(os.path.join(md, d))
                          if f.endswith((".c", ".cpp", ".ll")))
            if srcs:
                out.append(Prog(kind + "/" + d, srcs))
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goovm", default=os.environ.get("GOOVM_LLC", os.path.join(ROOT, "build/tools/goovm-llc/goovm-llc")))
    ap.add_argument("--backend", default="goose")
    ap.add_argument("--clang", default="clang-20")
    ap.add_argument("--clangxx", default="clang++-20")
    ap.add_argument("--opt", default="opt-20")
    ap.add_argument("--opt-passes", dest="opt_passes", default="")
    ap.add_argument("--tpde", default="")
    ap.add_argument("--goosecc", default="")
    ap.add_argument("-j", type=int, default=2)
    ap.add_argument("--work", default="")
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("filter", nargs="*")
    args = ap.parse_args()
    if args.goosecc:
        args.goosecc = os.path.abspath(args.goosecc)
    elif not os.path.exists(args.goovm):
        sys.exit(f"goovm-llc not found at {args.goovm} (use --goovm or GOOVM_LLC)")
    tmp = None
    if not args.work:
        tmp = tempfile.mkdtemp(prefix="goovm-tests-")
        args.work = tmp
    progs = programs()
    if args.goosecc:
        # goosecc compiles C, and the C++ of tests/cxx_d1
        progs = [p for p in progs if (not p.cxx or p.name.startswith("cxx_d1/")) and not any(is_ll(s) for s in p.srcs)]
    else:
        progs = [p for p in progs if not p.name.startswith("cxx_d1/")]
    if args.filter:
        progs = [p for p in progs if any(f in p.name for f in args.filter)]

    passed = failed = 0
    with cf.ThreadPoolExecutor(max_workers=args.j) as ex:
        for name, results in ex.map(lambda p: test_one(p, args), progs):
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
    print(f"\n{passed} passed, {failed} failed ({len(progs)} programs)")
    if tmp and not args.keep and failed == 0:
        shutil.rmtree(tmp, ignore_errors=True)
    elif tmp:
        print(f"work dir: {tmp}")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
