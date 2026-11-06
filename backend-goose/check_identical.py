#!/usr/bin/env python3
"""Check that the Goose back-end writes byte-identical objects to the C++ one.

For every tests/c/*.c program it builds the two bitcode variants that
tests/run.py uses:
  O0       clang-20 -O0 -emit-llvm
  mem2reg  clang-20 -O0 -Xclang -disable-O0-optnone -emit-llvm, then opt-20 -passes=mem2reg
(plus `opt` with --opt-passes), and it adds every *.bc file found in the
--inputs directories (the benchmark inputs from bench/backend/make_inputs.sh).
Each bitcode file is compiled with `goovm-llc --backend=cpp` and
`goovm-llc --backend=goose` by the same goovm-llc binary (built with
-DGOOVM_WITH_GOOSE=ON, so both back-ends see the same GIR), and the two
objects are compared byte for byte.

usage: backend-goose/check_identical.py --goovm BUILD/tools/goovm-llc/goovm-llc
           [--inputs DIR ...] [--opt-passes PASSES] [-j N] [--work DIR] [--keep]
Prints one line per mismatch or failure and a pass count; exit status 0 iff
every pair is identical.
"""
import argparse
import concurrent.futures as cf
import filecmp
import glob
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)


def run(cmd, timeout=600):
    return subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)


def make_bitcode(src, args):
    """Returns [(label, bc_path)] for one C test, or raises RuntimeError."""
    name = os.path.splitext(os.path.basename(src))[0]
    wd = os.path.join(args.work, "tests", name)
    os.makedirs(wd, exist_ok=True)
    out = []
    bc = os.path.join(wd, "O0.bc")
    r = run([args.clang, "-O0", "-w", "-c", "-emit-llvm", src, "-o", bc])
    if r.returncode:
        raise RuntimeError(f"clang failed on {src}: {r.stderr.decode(errors='replace')[-500:]}")
    out.append((f"{name}/O0", bc))
    raw = os.path.join(wd, "noopt.bc")
    r = run([args.clang, "-O0", "-w", "-Xclang", "-disable-O0-optnone", "-c", "-emit-llvm", src, "-o", raw])
    if r.returncode:
        raise RuntimeError(f"clang failed on {src}")
    m2r = os.path.join(wd, "mem2reg.bc")
    r = run([args.opt, "-passes=mem2reg", raw, "-o", m2r])
    if r.returncode:
        raise RuntimeError(f"opt failed on {raw}")
    out.append((f"{name}/mem2reg", m2r))
    if args.opt_passes:
        ob = os.path.join(wd, "opt.bc")
        r = run([args.opt, f"-passes={args.opt_passes}", raw, "-o", ob])
        if r.returncode:
            raise RuntimeError(f"opt failed on {raw}")
        out.append((f"{name}/opt", ob))
    return out


def compare(label, bc, args):
    """Returns (label, status, detail); status is 'ok', 'DIFF', 'FAIL' or 'skip'."""
    base = os.path.join(args.work, "objs", label.replace("/", "__"))
    os.makedirs(os.path.dirname(base), exist_ok=True)
    a, b = base + ".cpp.o", base + ".goose.o"
    ra = run([args.goovm, "--backend=cpp", bc, "-o", a])
    rb = run([args.goovm, "--backend=goose", bc, "-o", b])
    if ra.returncode == 2 and rb.returncode == 2:
        return label, "skip", "unsupported input (both back-ends: exit 2)"
    if ra.returncode or rb.returncode:
        return label, "FAIL", (f"cpp exit {ra.returncode}, goose exit {rb.returncode}: "
                               f"{(ra.stderr + rb.stderr).decode(errors='replace').strip()[-800:]}")
    if not filecmp.cmp(a, b, shallow=False):
        r = run(["cmp", a, b])
        return label, "DIFF", f"{r.stdout.decode().strip()} ({os.path.getsize(a)} vs {os.path.getsize(b)} bytes)"
    size = os.path.getsize(a)
    if not args.keep:
        os.remove(a)
        os.remove(b)
    return label, "ok", f"{size} bytes"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goovm", default=os.environ.get("GOOVM_LLC", os.path.join(ROOT, "build-goose/tools/goovm-llc/goovm-llc")),
                    help="goovm-llc built with -DGOOVM_WITH_GOOSE=ON")
    ap.add_argument("--inputs", nargs="*", default=[], help="directories with benchmark *.bc files")
    ap.add_argument("--clang", default="clang-20")
    ap.add_argument("--opt", default="opt-20")
    ap.add_argument("--opt-passes", dest="opt_passes", default="", help="also check an opt -passes=... variant")
    ap.add_argument("-j", type=int, default=4)
    ap.add_argument("--work", default="")
    ap.add_argument("--keep", action="store_true", help="keep the objects and bitcode")
    ap.add_argument("-v", action="store_true", help="print a line for every input, not only failures")
    args = ap.parse_args()
    if not os.path.exists(args.goovm):
        sys.exit(f"goovm-llc not found at {args.goovm} (use --goovm or GOOVM_LLC)")
    tmp = None
    if not args.work:
        tmp = tempfile.mkdtemp(prefix="goovm-identical-")
        args.work = tmp

    srcs = sorted(glob.glob(os.path.join(ROOT, "tests", "c", "*.c")))
    jobs = []
    with cf.ThreadPoolExecutor(max_workers=args.j) as ex:
        for pairs in ex.map(lambda s: make_bitcode(s, args), srcs):
            jobs.extend(pairs)
    for d in args.inputs:
        for bc in sorted(glob.glob(os.path.join(d, "*.bc"))):
            jobs.append((f"{os.path.basename(os.path.normpath(d))}/{os.path.basename(bc)}", bc))

    counts = {"ok": 0, "DIFF": 0, "FAIL": 0, "skip": 0}
    with cf.ThreadPoolExecutor(max_workers=args.j) as ex:
        for label, status, detail in ex.map(lambda j: compare(j[0], j[1], args), jobs):
            counts[status] += 1
            if status != "ok" or args.v:
                print(f"{status:4s}  {label:40s} {detail}")
    total = len(jobs)
    print(f"\nidentical: {counts['ok']}/{total}  (differ: {counts['DIFF']}, failed: {counts['FAIL']}, "
          f"unsupported: {counts['skip']}; {len(srcs)} test programs x {2 + bool(args.opt_passes)} variants "
          f"+ {total - len(srcs) * (2 + bool(args.opt_passes))} benchmark inputs)")
    if tmp and not args.keep and counts["DIFF"] == counts["FAIL"] == 0:
        shutil.rmtree(tmp, ignore_errors=True)
    elif tmp:
        print(f"work dir: {tmp}")
    sys.exit(0 if counts["DIFF"] == counts["FAIL"] == 0 else 1)


if __name__ == "__main__":
    main()
