#!/usr/bin/env python3
"""Mixed-link validation of goovm-llc on real programs (llvm-test-suite).

For each program, every C file is compiled twice:
  clang-20 -O0 -c                                 -> ref/<file>.o
  clang-20 -O0 -emit-llvm | goovm-llc --backend=B -> goovm/<file>.o (when supported)
Two executables are linked: one from the clang objects only, one where each
supported file uses the goovm object. Both run once on the program's test
input and their stdout and exit status are compared.

usage: tests/realworld_mixed.py [--suite DIR] [--goovm PATH] [--backend goose] [--work DIR] [-j 2] [program ...]
"""
import argparse, concurrent.futures as cf, os, subprocess, sys

PROGRAMS = {
    "SPASS": dict(dir="MultiSource/Applications/SPASS", flags=["-DCLOCK_NO_TIMING", "-fno-strict-aliasing", "-std=gnu17"],
                  incs=["."], libs=["-lm"], args=["small_problem.dfg"]),
    "consumer-typeset": dict(dir="MultiSource/Benchmarks/MiBench/consumer-typeset",
                             flags=["-DOS_UNIX=1", "-DOS_DOS=0", "-DOS_MAC=0", "-DDB_FIX=0", "-DUSE_STAT=1",
                                    "-DSAFE_DFT=0", "-DCOLLATE=1", '-DLIB_DIR="lout.lib"', '-DFONT_DIR="font"',
                                    '-DMAPS_DIR="maps"', '-DINCL_DIR="include"', '-DDATA_DIR="data"',
                                    '-DHYPH_DIR="hyph"', '-DLOCALE_DIR="locale"', "-DCHAR_IN=1", "-DCHAR_OUT=0",
                                    "-DLOCALE_ON=1", "-DASSERT_ON=1", "-DDEBUG_ON=0", "-DPDF_COMPRESSION=0",
                                    "-D_FORTIFY_SOURCE=0", "-std=c99"],
                             incs=["."], libs=["-lm"],
                             args=["-x", "-I", "data/include", "-D", "data/data", "-F", "data/font", "-C", "data/maps",
                                   "-H", "data/hyph", "small.lout"]),
}


def sh(cmd, **kw):
    return subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, **kw)


def build_file(args, p, root, src, wd):
    base = os.path.relpath(src, root).replace("/", "_")[:-2]
    flags = p["flags"] + ["-I" + os.path.join(root, i) for i in p["incs"]]
    ref = os.path.join(wd, "ref", base + ".o")
    r = sh([args.clang, "-O0", "-w", "-c", src, "-o", ref] + flags)
    if r.returncode:
        raise SystemExit(f"clang failed on {src}:\n{r.stderr.decode()}")
    bc = os.path.join(wd, "bc", base + ".bc")
    sh([args.clang, "-O0", "-w", "-c", "-emit-llvm", src, "-o", bc] + flags)
    goo = os.path.join(wd, "goovm", base + ".o")
    r = sh([args.goovm, f"--backend={args.backend}", bc, "-o", goo])
    if r.returncode == 0:
        return ref, goo, ""
    return ref, None, r.stderr.decode(errors="replace").strip().splitlines()[0]


def main():
    ap = argparse.ArgumentParser()
    here = os.path.dirname(os.path.abspath(__file__))
    ap.add_argument("--suite", default="/home/user/llvm/llvm-test-suite")
    ap.add_argument("--goovm", default=os.path.join(here, "../build/tools/goovm-llc/goovm-llc"))
    ap.add_argument("--backend", default="goose")
    ap.add_argument("--clang", default="clang-20")
    ap.add_argument("--work", default="/tmp/goovm-mixed")
    ap.add_argument("-j", type=int, default=2)
    ap.add_argument("programs", nargs="*")
    args = ap.parse_args()
    failed = 0
    for name, p in PROGRAMS.items():
        if args.programs and name not in args.programs:
            continue
        root = os.path.join(args.suite, p["dir"])
        wd = os.path.join(args.work, name)
        for d in ("ref", "bc", "goovm"):
            os.makedirs(os.path.join(wd, d), exist_ok=True)
        srcs = sorted(os.path.join(root, f) for f in os.listdir(root) if f.endswith(".c"))
        with cf.ThreadPoolExecutor(args.j) as ex:
            res = list(ex.map(lambda s: build_file(args, p, root, s, wd), srcs))
        ref_exe, mix_exe = os.path.join(wd, "ref.exe"), os.path.join(wd, "mixed.exe")
        for exe, objs in ((ref_exe, [r[0] for r in res]), (mix_exe, [r[1] or r[0] for r in res])):
            r = sh([args.clang] + objs + p["libs"] + ["-o", exe])
            if r.returncode:
                print(f"{name}: link failed:\n{r.stderr.decode()}")
                failed += 1
                break
        else:
            outs = []
            for exe in (ref_exe, mix_exe):
                try:
                    r = sh([exe] + p["args"], cwd=root, timeout=300)
                    outs.append((r.returncode, r.stdout))
                except subprocess.TimeoutExpired:
                    outs.append((-999, b"timeout"))
            n_goo = sum(1 for r in res if r[1])
            same = outs[0] == outs[1]
            failed += not same
            print(f"{name}: {n_goo}/{len(res)} files compiled by goovm-llc; output {len(outs[0][1])} bytes, "
                  f"exit {outs[0][0]}/{outs[1][0]}: {'SAME' if same else 'DIFFERENT'}")
            for r in res:
                if not r[1]:
                    print(f"    clang-only: {os.path.basename(r[0])}: {r[2]}")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
