#!/usr/bin/env python3
"""The test corpora: (corpus, path, flags) for every C file.

Corpora (llvm-test-suite at SUITE):
  torture   SingleSource/Regression/C/gcc-c-torture/execute (+ ieee, builtins)
  unit      SingleSource/UnitTests (C files)
  regress   SingleSource/Regression/C (not torture)
  bench     SingleSource/Benchmarks (C files)
  ctmark    the C files of the CTMark programs, with their -D/-I flags
"""
import os

SUITE = os.environ.get("LLVM_TEST_SUITE", "/home/user/llvm/llvm-test-suite")

TORTURE_FLAGS = ["-w", "-Wno-implicit-int", "-Wno-int-conversion", "-Wno-implicit-function-declaration"]

CTMARK = {
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


def c_files(root, skip=()):
    out = []
    for dp, dn, fs in os.walk(root):
        dn.sort()
        if any(s in dp for s in skip):
            continue
        for f in sorted(fs):
            if f.endswith(".c"):
                out.append(os.path.join(dp, f))
    return out


def corpus(names=None):
    """Yields (corpus, path, flags)."""
    ss = os.path.join(SUITE, "SingleSource")
    want = lambda n: not names or n in names
    if want("torture"):
        # per-test flags from the torture CMakeLists.txt
        extra = {"920302-1.c": ["-Wno-return-type"], "920501-3.c": ["-Wno-return-type"], "920728-1.c": ["-Wno-return-type"],
                 "20040409-1.c": ["-fwrapv"], "20040409-2.c": ["-fwrapv"], "20040409-3.c": ["-fwrapv"], "950704-1.c": ["-fwrapv"]}
        for p in c_files(os.path.join(ss, "Regression/C/gcc-c-torture/execute")):
            yield "torture", p, list(TORTURE_FLAGS) + extra.get(os.path.basename(p), [])
    if want("unit"):
        # Non-x86 vector tests are left out; AVX512 tests need -march=skylake-avx512.
        skip = ("ObjC", "Altivec", "NEON", "AArch64", "HVX", "LASX", "LSX", "AVX512")
        for p in c_files(os.path.join(ss, "UnitTests"), skip=skip):
            fl = ["-w", "-Wno-implicit-function-declaration", "-Wno-implicit-int", "-Wno-error=incompatible-pointer-types"]
            if "/Vector" in p:
                fl.append("-I" + os.path.join(ss, "UnitTests/Vector"))
            yield "unit", p, fl
    if want("regress"):
        for p in c_files(os.path.join(ss, "Regression/C"), skip=("gcc-c-torture",)):
            yield "regress", p, ["-w"]
    if want("bench"):
        for p in c_files(os.path.join(ss, "Benchmarks")):
            fl = ["-w", "-Wno-implicit-int", "-Wno-implicit-function-declaration", "-I" + os.path.dirname(p)]
            if "/Polybench/" in p:
                if p.endswith("utilities/polybench.c"):
                    continue    # compiled together with each kernel, not alone
                fl += ["-I" + os.path.join(ss, "Benchmarks/Polybench/utilities"), "-DPOLYBENCH_DUMP_ARRAYS",
                       "-DFP_ABSTOLERANCE=1e-5", "-DFMA_DISABLED=1"]
            yield "bench", p, fl
    for name, (d, flags, incs) in CTMARK.items():
        if not want("ctmark") and not want(name):
            continue
        root = os.path.realpath(os.path.join(SUITE, "CTMark", d))
        for p in c_files(root):
            yield "ctmark", p, ["-w"] + flags + ["-I" + os.path.join(root, i) for i in incs]


if __name__ == "__main__":
    import collections, sys
    c = collections.Counter(k for k, _, _ in corpus(sys.argv[1:]))
    print(dict(c), sum(c.values()))
