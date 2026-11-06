#!/usr/bin/env python3
"""Which real-world C code fits goovm's subset?

Compiles every C file of the CTMark C programs (llvm-test-suite) with
clang-20 -O0 -emit-llvm and runs goovm-llc --backend=cpp on it. Prints, per
program, how many files and functions compile, and a histogram of the first
unsupported construct per failing file (goovm-llc stops at the first one).

usage: realworld.py [--suite /home/user/llvm/llvm-test-suite] [--goovm PATH]
                    [--work DIR] [-j 2] [--keep-bc]
"""
import argparse, collections, concurrent.futures as cf, os, re, subprocess, sys

PROGRAMS = {
    # name: (dir under CTMark, extra flags, include dirs relative to program dir)
    "sqlite3": ("sqlite3", ["-DSTDC_HEADERS=1", "-DHAVE_SYS_TYPES_H=1", "-DHAVE_SYS_STAT_H=1", "-DHAVE_STDLIB_H=1",
                            "-DHAVE_STRING_H=1", "-DHAVE_MEMORY_H=1", "-DHAVE_STRINGS_H=1", "-DHAVE_INTTYPES_H=1",
                            "-DHAVE_STDINT_H=1", "-DHAVE_UNISTD_H=1", "-DSQLITE_OMIT_LOAD_EXTENSION=1",
                            "-DSQLITE_THREADSAFE=0", "-std=gnu17"], ["."]),
    "ClamAV": ("ClamAV", ["-DHAVE_CONFIG_H", "-DDONT_LOCK_DBDIRS", "-Wno-error=incompatible-pointer-types"], [".", "zlib"]),
    "SPASS": ("SPASS", ["-DCLOCK_NO_TIMING", "-fno-strict-aliasing", "-std=gnu17"], ["."]),
    "consumer-typeset": ("consumer-typeset", ["-DOS_UNIX=1", "-DOS_DOS=0", "-DOS_MAC=0", "-DDB_FIX=0", "-DUSE_STAT=1",
                         "-DSAFE_DFT=0", "-DCOLLATE=1", '-DLIB_DIR="lout.lib"', '-DFONT_DIR="font"', '-DMAPS_DIR="maps"',
                         '-DINCL_DIR="include"', '-DDATA_DIR="data"', '-DHYPH_DIR="hyph"', '-DLOCALE_DIR="locale"',
                         "-DCHAR_IN=1", "-DCHAR_OUT=0", "-DLOCALE_ON=1", "-DASSERT_ON=1", "-DDEBUG_ON=0",
                         "-DPDF_COMPRESSION=0", "-D_FORTIFY_SOURCE=0", "-std=c99"], ["."]),
    "lencod": ("lencod", ["-fcommon", "-D__USE_LARGEFILE64", "-D_FILE_OFFSET_BITS=64", "-std=gnu17"], ["."]),
    "mafft": ("mafft", ["-DLLVM"], ["."]),
    "7zip-C": ("7zip", ["-DBREAK_HANDLER", "-DUNICODE", "-D_UNICODE", "-D_FILE_OFFSET_BITS=64", "-D_LARGEFILE_SOURCE",
                        "-DNDEBUG", "-D_REENTRANT", "-DENV_UNIX", "-D_7ZIP_LARGE_PAGES", "-pthread"],
               ["C", "CPP/myWindows", "CPP/include_windows", "CPP", "."]),
}


def classify(msg):
    m = re.search(r"unsupported: (.*?)(?: in function '| in global '|$)", msg, re.M)
    if not m:
        return "other: " + msg.strip().splitlines()[0][:80] if msg.strip() else "other"
    r = m.group(1)
    r = re.sub(r"floating-point (type|constant).*", "floating point", r)
    r = re.sub(r"integer type i\d+", "odd-width integer (iN)", r)
    r = re.sub(r"intrinsic 'llvm\.([a-z_]+)[^']*'", r"intrinsic llvm.\1", r)
    r = re.sub(r"aggregate \(by-value\) type .*", "aggregate SSA value (struct return/arg)", r)
    r = re.sub(r"vector type .*", "vector type", r)
    return r


def one(args, prog, flags, incs, root, src):
    rel = os.path.relpath(src, root)
    bc = os.path.join(args.work, prog, rel.replace("/", "_") + ".bc")
    os.makedirs(os.path.dirname(bc), exist_ok=True)
    cmd = [args.clang, "-O0", "-w", "-c", "-emit-llvm", src, "-o", bc] + flags + ["-I" + os.path.join(root, i) for i in incs]
    r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if r.returncode:
        return rel, "clang-error", r.stderr.decode(errors="replace")[:300], 0
    obj = bc[:-3] + ".o"
    r = subprocess.run([args.goovm, "--backend=cpp", bc, "-o", obj], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    nfun = 0
    d = subprocess.run([args.llvm_dis, bc, "-o", "-"], stdout=subprocess.PIPE)
    nfun = d.stdout.count(b"\ndefine ")
    if not args.keep_bc and r.returncode == 0:
        os.remove(bc)
    return rel, "ok" if r.returncode == 0 else "unsupported", r.stderr.decode(errors="replace"), nfun


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--suite", default="/home/user/llvm/llvm-test-suite")
    here = os.path.dirname(os.path.abspath(__file__))
    ap.add_argument("--goovm", default=os.path.join(here, "../../build/tools/goovm-llc/goovm-llc"))
    ap.add_argument("--clang", default="clang-20")
    ap.add_argument("--llvm-dis", dest="llvm_dis", default="llvm-dis-20")
    ap.add_argument("--work", default="/tmp/goovm-realworld")
    ap.add_argument("-j", type=int, default=2)
    ap.add_argument("--keep-bc", dest="keep_bc", action="store_true")
    ap.add_argument("programs", nargs="*")
    args = ap.parse_args()
    total_reasons = collections.Counter()
    print("| program | C files | files OK | functions in OK files / all | first unsupported construct (files) |")
    print("|---|---:|---:|---:|---|")
    for prog, (d, flags, incs) in PROGRAMS.items():
        if args.programs and prog not in args.programs:
            continue
        root = os.path.realpath(os.path.join(args.suite, "CTMark", d))
        srcs = sorted(os.path.join(dp, f) for dp, _, fs in os.walk(root) for f in fs if f.endswith(".c"))
        with cf.ThreadPoolExecutor(args.j) as ex:
            res = list(ex.map(lambda s: one(args, prog, flags, incs, root, s), srcs))
        ok = [r for r in res if r[1] == "ok"]
        reasons = collections.Counter(classify(r[2]) if r[1] == "unsupported" else "clang error" for r in res if r[1] != "ok")
        total_reasons.update(reasons)
        fn_ok = sum(r[3] for r in ok)
        fn_all = sum(r[3] for r in res)
        rs = "; ".join(f"{k} ({v})" for k, v in reasons.most_common())
        print(f"| {prog} | {len(res)} | {len(ok)} | {fn_ok} / {fn_all} | {rs} |")
        if os.environ.get("VERBOSE"):
            for r in res:
                if r[1] != "ok":
                    print(f"    {r[0]}: {r[2].strip().splitlines()[0] if r[2].strip() else r[1]}")
    print("\nAll programs, first unsupported construct per file:")
    for k, v in total_reasons.most_common():
        print(f"  {v:4d}  {k}")


if __name__ == "__main__":
    main()
