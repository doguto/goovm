#!/usr/bin/env python3
"""Correctness harness: llvm-test-suite C programs through goovm-llc.

For every test of the selected corpora:

  baseline   clang-20 -O0 <test flags> srcs -o exe; run; verify
  O0         clang-20 -O0 -emit-llvm      -> goovm-llc -> clang-20 link -> run, verify
  g          clang-20 -O0 -g -emit-llvm   -> goovm-llc -> link -> run, verify
  mem2reg    clang-20 -O0 -Xclang -disable-O0-optnone -emit-llvm, opt-20 -passes=mem2reg
             -> goovm-llc -> link -> run, verify
  O1         clang-20 -O0 -emit-llvm      -> goovm-llc -O1 (Goose middle-end, global RA) -> link -> run
  O1-g       clang-20 -O0 -g -emit-llvm   -> goovm-llc -O1 -> link -> run
  O2ir       clang-20 -O2 -emit-llvm      -> goovm-llc -O1 (LLVM's middle-end, Goose back-end)
  cc-O1      goovm-cc -O1 (opt-in, with --cc)

The O1, O1-g, O2ir and cc-O1 variants run only the tests that pass when built
with plain clang-20 -O1 (a second baseline, which also excludes programs whose
undefined behaviour shows at -O1).

Verification follows the llvm-test-suite conventions:
  - SingleSource/MultiSource ("traditional output"): stdout and stderr go to one
    file, "exit N" is appended, the file is md5-hashed if the directory sets
    HASH_PROGRAM_OUTPUT, then compared with <name>.reference_output by fpcmp
    with the directory's FP_TOLERANCE / FP_ABSTOLERANCE;
  - gcc-c-torture: the program must exit with status 0 (abort() on failure).

Tests that do not build or do not pass with plain clang-20 -O0 are excluded
and listed in the report. A goovm-llc result is one of:
  pass, fail (wrong output, crash, timeout, link error), unsupported (goovm-llc
  exit 2 on some file), fallback (goovm-llc --fallback compiled some file with
  LLVM's code generator; the test result is still recorded), error (goovm-llc
  crashed or another tool failed).

Corpora: torture, ieee, builtins (gcc-c-torture/execute and its ieee/ and
builtins/ directories), unittests, regression, benchmarks (SingleSource), ctmark
(the six CTMark C programs: sqlite3, SPASS, ClamAV, lencod, mafft,
consumer-typeset).

usage: tests/suite.py [--goovm PATH] [--corpus a,b] [--variants O0,g,mem2reg]
                      [-j 3] [--work DIR] [--fallback] [--report FILE] [--json FILE]
                      [--rebaseline] [--emit-bc] [--time-run N] [filter ...]
"""
import argparse
import concurrent.futures as cf
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
CORPORA = ["torture", "ieee", "builtins", "unittests", "regression", "benchmarks", "ctmark",
           "unittests-cxx", "regression-cxx", "benchmarks-cxx", "ctmark-cxx"]
CXX_EXTS = (".cpp", ".cc", ".cxx", ".C")


def is_cxx(src):
    return os.path.splitext(src)[1] in CXX_EXTS
VARIANTS = ["O0", "g", "mem2reg"]
# Opt-in variants: "cc" builds each file with goovm-cc (clang front end in-process
# + the Goose back-end) instead of clang -emit-llvm + goovm-llc.
EXTRA_VARIANTS = ["cc", "cc-g", "cc-O1"]
# Optimizing variants (milestone E1): compared against the clang -O1 baseline.
OPT_VARIANTS = ["O1", "O1-g", "O2ir"]


def opt_variant(v):
    return v in OPT_VARIANTS or v == "cc-O1"


class Test:
    def __init__(self, corpus, name, srcs, cflags=(), ldflags=(), args=(), stdin=None, rundir=None,
                 ref=None, hash_output=False, fp_rel=None, fp_abs=None, exit0=False, data=(), prepare=None,
                 timeout=None, cxxflags=None):
        self.corpus = corpus
        self.name = name                 # unique within the corpus
        self.srcs = list(srcs)
        self.cflags = list(cflags)
        self.cxxflags = list(cflags if cxxflags is None else cxxflags)   # flags for C++ sources
        self.ldflags = list(ldflags)
        self.args = list(args)
        self.stdin = stdin               # path relative to the run directory
        self.rundir = rundir             # directory whose files the program reads (symlinked)
        self.ref = ref                   # reference output file
        self.hash_output = hash_output
        self.fp_rel = fp_rel
        self.fp_abs = fp_abs
        self.exit0 = exit0               # gcc-c-torture convention
        self.data = list(data)           # files/dirs (relative to rundir) linked into the run dir
        self.prepare = prepare           # callable(run_dir) for generated inputs
        self.timeout = timeout

    @property
    def id(self):
        return f"{self.corpus}/{self.name}"

    @property
    def cxx(self):
        return any(is_cxx(s) for s in self.srcs)

    def flags(self, src):
        return self.cxxflags if is_cxx(src) else self.cflags

    def key(self):
        k = [self.srcs, self.cflags, self.ldflags, self.args, self.stdin, self.ref,
             self.hash_output, self.fp_rel, self.fp_abs, self.exit0]
        if self.cxxflags != self.cflags:
            k.append(self.cxxflags)
        h = hashlib.sha1(json.dumps(k).encode())
        return h.hexdigest()[:16]


# ------------------------------------------------------------------ corpora

def cmake_globs(path):
    """{var: [file names]} for every `file(GLOB var [CONFIGURE_DEPENDS] ...)` block of a CMakeLists."""
    txt = re.sub(r"#[^\n]*", "", open(path).read())
    out = {}
    for m in re.finditer(r"file\(GLOB\s+(\w+)(.*?)\)", txt, re.S):
        names = re.findall(r"^\s*([\w.+-]+\.c)\b", m.group(2), re.M)
        out[m.group(1)] = names
    return out


ERRORING = {"-fno-early-inlining", "-fno-ira-share-spill-slots", "-ftree-loop-distribution",
            "-fno-tree-bit-ccp", "-fno-tree-coalesce-vars"}


def dg_options(path):
    """The dg-options / dg-additional-options flags the test-suite picks up (gcc_torture_dg_options_cflags),
    minus the flags that make clang error and minus -O levels (the harness sets the optimization level)."""
    flags = []
    for line in open(path, errors="replace"):
        m = re.search(r'dg-(additional-)?options ({ )?"([^"]*)"( })?(.*)', line)
        if m and not re.search(r"{ +target", m.group(5)):
            flags += m.group(3).split()
    return [f for f in flags if f not in ERRORING and not re.match(r"-O[0-9sgz]?$", f)]


def torture_tests(suite):
    base = os.path.join(suite, "SingleSource/Regression/C/gcc-c-torture/execute")
    tests = []
    g = cmake_globs(os.path.join(base, "CMakeLists.txt"))
    skip = set(g.get("UnsupportedTests", [])) | set(g.get("FailingTests", []))
    fwrapv = set(g.get("TestRequiresFWrapV", []))
    noret = set(g.get("TestRequiresWNoReturnType", []))
    libm = set(g.get("TestRequiresLibM", []))
    common = ["-Wno-implicit-int", "-Wno-int-conversion", "-Wno-implicit-function-declaration", "-w"]
    for f in sorted(os.listdir(base)):
        if not f.endswith(".c") or f in skip:
            continue
        p = os.path.join(base, f)
        cf_ = common + dg_options(p) + (["-Wno-return-type"] if f in noret else []) + (["-fwrapv"] if f in fwrapv else [])
        tests.append(Test("torture", f[:-2], [p], cf_, ["-lm"] if f in libm else [], exit0=True))
    # ieee/
    ib = os.path.join(base, "ieee")
    g = cmake_globs(os.path.join(ib, "CMakeLists.txt"))
    iskip = set(g.get("UnsupportedTests", []))
    ilibm = set(g.get("TestRequiresLibM", []))
    notrap = set(g.get("TestRequiresFNoTrappingMath", []))
    icommon = ["-Wno-implicit-int", "-Wno-implicit-function-declaration", "-w"]
    for f in sorted(os.listdir(ib)):
        if not f.endswith(".c") or f in iskip:
            continue
        p = os.path.join(ib, f)
        cf_ = icommon + dg_options(p) + (["-fno-trapping-math"] if f in notrap else [])
        tests.append(Test("ieee", f[:-2], [p], cf_, ["-lm"] if f in ilibm else [], exit0=True))
    # builtins/: X.c + X-lib.c + lib/main.c (gcc's builtins.exp); not run by the llvm-test-suite.
    bb = os.path.join(base, "builtins")
    for f in sorted(os.listdir(bb)):
        if not f.endswith(".c") or f.endswith("-lib.c"):
            continue
        n = f[:-2]
        srcs = [os.path.join(bb, f)]
        if os.path.exists(os.path.join(bb, n + "-lib.c")):
            srcs.append(os.path.join(bb, n + "-lib.c"))
        srcs.append(os.path.join(bb, "lib/main.c"))
        extra = []
        xf = os.path.join(bb, n + ".x")
        if os.path.exists(xf):
            m = re.search(r"set additional_flags (\S+)", open(xf).read())
            if m:
                extra.append(m.group(1))
        tests.append(Test("builtins", n, srcs, common + dg_options(srcs[0]) + extra, ["-lm"], exit0=True))
    return tests


def ref_output(d, name):
    for suffix in (".reference_output.little-endian", ".reference_output.Linux", ".reference_output"):
        p = os.path.join(d, name + suffix)
        if os.path.exists(p):
            return p
    return None


def singlesource(corpus, d, cflags=(), ldflags=(), args=(), hash_output=False, fp_rel=None, fp_abs=None,
                 only=None, prefix="", exts=(".c",), flags_of=None):
    tests = []
    files = only if only is not None else sorted(f for f in os.listdir(d) if os.path.splitext(f)[1] in exts)
    for f in files:
        name = re.sub(r"\.[^.]*$", "", f)
        ref = ref_output(d, name)
        stdin = None
        if os.path.exists(os.path.join(d, name + ".reference_input")):
            stdin = name + ".reference_input"
        fl = list(cflags) + (flags_of(f) if flags_of else [])
        tests.append(Test(corpus, prefix + os.path.relpath(os.path.join(d, name), d0(corpus)),
                          [os.path.join(d, f)], fl, ldflags, args, stdin=stdin, rundir=d, ref=ref,
                          hash_output=hash_output, fp_rel=fp_rel, fp_abs=fp_abs,
                          data=[stdin] if stdin else []))
    return tests


_D0 = {}


def d0(corpus):
    return _D0[corpus]


def unittest_tests(suite):
    u = os.path.join(suite, "SingleSource/UnitTests")
    _D0["unittests"] = u
    common = ["-Wno-implicit-function-declaration", "-Wno-implicit-int"]
    t = singlesource("unittests", u, common)
    t += singlesource("unittests", os.path.join(u, "Float"), common)
    t += singlesource("unittests", os.path.join(u, "HashRecognize"), common)
    t += singlesource("unittests", os.path.join(u, "SignlessTypes"), common, args=["31415926"])
    t += singlesource("unittests", os.path.join(u, "Threads"), common + ["-pthread"], ["-pthread"])
    vcommon = common + ["-Wno-error=incompatible-pointer-types"]
    t += singlesource("unittests", os.path.join(u, "Vector"), vcommon)
    t += singlesource("unittests", os.path.join(u, "Vector/SSE"),
                      vcommon + ["-msse2", "-ffp-contract=off", "-DFMA_DISABLED=1"], ["-lm"], fp_rel=0.016)
    return t


def regression_tests(suite):
    r = os.path.join(suite, "SingleSource/Regression/C")
    _D0["regression"] = r
    common = ["-Wno-implicit-int", "-Wno-error=incompatible-pointer-types"]
    t = singlesource("regression", r, common, ["-lm"])
    t += singlesource("regression", os.path.join(r, "SSE"), common + ["-msse2"], ["-lm"])
    return t


def benchmark_tests(suite):
    b = os.path.join(suite, "SingleSource/Benchmarks")
    _D0["benchmarks"] = b
    t = []
    j = os.path.join
    t = _benchmark_tests(b, j)
    for x in t:
        x.timeout = 600
    return t


def _benchmark_tests(b, j):
    t = []
    t += singlesource("benchmarks", j(b, "BenchmarkGame"), [], ["-lm"])
    t += singlesource("benchmarks", j(b, "BenchmarkGame/Large"), [], ["-lm"], hash_output=True)
    t += singlesource("benchmarks", j(b, "CoyoteBench"), [], ["-lm"])
    t += singlesource("benchmarks", j(b, "Dhrystone"), ["-Wno-implicit-int", "-std=gnu17"], ["-lm"])
    t += singlesource("benchmarks", j(b, "Linpack"), ["-ffp-contract=off", "-DFMA_DISABLED=1"], ["-lm"], fp_rel=0.0001)
    t += singlesource("benchmarks", j(b, "McGill"), [], ["-lm"], fp_rel=0.001,
                      only=["chomp.c", "misr.c", "queens.c", "exptree.c"])
    misc = ["ReedSolomon.c", "evalloop.c", "fbench.c", "ffbench.c", "flops-1.c", "flops-2.c", "flops-3.c",
            "flops-4.c", "flops-5.c", "flops-6.c", "flops-7.c", "flops-8.c", "flops.c", "fp-convert.c",
            "himenobmtxpa.c", "lowercase.c", "mandel-2.c", "mandel.c", "matmul_f64_4x4.c", "oourafft.c",
            "perlin.c", "pi.c", "revertBits.c", "richards_benchmark.c", "salsa20.c", "whetstone.c", "dt.c"]
    t += singlesource("benchmarks", j(b, "Misc"), ["-Wno-implicit-int"], ["-lm"], fp_rel=0.001, only=misc)
    shoot = ["ackermann.c", "ary3.c", "fib2.c", "hash.c", "heapsort.c", "lists.c", "matrix.c", "methcall.c",
             "nestedloop.c", "objinst.c", "random.c", "sieve.c", "strcat.c", "hello.c"]
    t += singlesource("benchmarks", j(b, "Shootout"), ["-Wno-error=incompatible-pointer-types"], ["-lm"],
                      only=shoot)
    stan = ["Bubblesort.c", "FloatMM.c", "Oscar.c", "Perm.c", "Puzzle.c", "Queens.c", "Quicksort.c", "RealMM.c",
            "Towers.c", "Treesort.c", "IntMM.c"]
    t += singlesource("benchmarks", j(b, "Stanford"), [], ["-lm"], fp_rel=0.001, only=stan)
    pb = j(b, "Polybench")
    for dp, dn, fn in sorted(os.walk(pb)):
        dn.sort()
        cs = sorted(f for f in fn if f.endswith(".c"))
        if not cs or "utilities" in dp:
            continue
        srcs_extra = []  # polybench.h carries the support code (the CMake adds no polybench.c)
        extra = []
        if "-ffp-contract=off" in open(j(dp, "CMakeLists.txt")).read():
            extra = ["-ffp-contract=off", "-DFMA_DISABLED=1"]
        for c in cs:
            name = c[:-2]
            tt = Test("benchmarks", os.path.relpath(j(dp, name), b), [j(dp, c)] + srcs_extra,
                      ["-I", j(pb, "utilities"), "-DPOLYBENCH_DUMP_ARRAYS", "-DFP_ABSTOLERANCE=1e-5",
                       "-Wno-error=incompatible-pointer-types"] + extra, ["-lm"], rundir=dp,
                      ref=ref_output(dp, name), hash_output=True)
            t.append(tt)
    return t


def sqlite_prepare(src):
    def prep(rundir):
        if os.path.exists(os.path.join(rundir, "test15.sql")):
            return
        r = subprocess.run(["tclsh", os.path.join(src, "speedtest.tcl")], cwd=rundir,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if r.returncode:
            raise RuntimeError("tclsh speedtest.tcl failed: " + r.stderr.decode(errors="replace"))
    return prep


def ctmark_tests(suite):
    m = os.path.join(suite, "MultiSource")
    j = os.path.join
    t = []
    d = j(m, "Applications/sqlite3")
    t.append(Test("ctmark", "sqlite3", [j(d, "sqlite3.c"), j(d, "shell.c")],
                  ["-DSTDC_HEADERS=1", "-DHAVE_SYS_TYPES_H=1", "-DHAVE_SYS_STAT_H=1", "-DHAVE_STDLIB_H=1",
                   "-DHAVE_STRING_H=1", "-DHAVE_MEMORY_H=1", "-DHAVE_STRINGS_H=1", "-DHAVE_INTTYPES_H=1",
                   "-DHAVE_STDINT_H=1", "-DHAVE_UNISTD_H=1", "-DSQLITE_OMIT_LOAD_EXTENSION=1",
                   "-DSQLITE_THREADSAFE=0", "-I" + d, "-std=gnu17"], [],
                  ["-init", "sqlite3rc", ":memory:"], stdin="commands", rundir=d,
                  ref=j(d, "sqlite3.reference_output"), fp_rel=1.0e-9, data=["sqlite3rc", "commands"],
                  prepare=sqlite_prepare(d)))
    d = j(m, "Applications/SPASS")
    t.append(Test("ctmark", "SPASS", sorted(j(d, f) for f in os.listdir(d) if f.endswith(".c")),
                  ["-DCLOCK_NO_TIMING", "-fno-strict-aliasing", "-std=gnu17", "-I" + d], ["-lm"],
                  ["problem.dfg"], rundir=d, ref=j(d, "SPASS.reference_output"), hash_output=True,
                  data=["problem.dfg"]))
    d = j(m, "Applications/ClamAV")
    inputs = ["inputs/clam.cab", "inputs/clamdoc.tar.gz", "inputs/clam.exe", "inputs/clam.exe.bz2",
              "inputs/clam-v2.rar", "inputs/clam-v3.rar", "inputs/clam.zip", "inputs/README",
              "inputs/rtf-test/Doc11.rtf", "inputs/rtf-test/Doc1.rtf", "inputs/rtf-test/Doc22.rtf",
              "inputs/rtf-test/Doc2.rtf", "inputs/rtf-test/doc3.rtf", "inputs/rtf-test/docCLAMexe.rtf",
              "inputs/rtf-test/rtf1.rtf", "inputs/rtf-test/rtf-novirus.rtf"]
    cl = re.search(r"llvm_multisource\(clamscan(.*?)\)", open(j(d, "CMakeLists.txt")).read(), re.S).group(1).split()
    t.append(Test("ctmark", "ClamAV", [j(d, f) for f in cl],
                  ["-DHAVE_CONFIG_H", "-I" + d, "-I" + j(d, "zlib"), "-DDONT_LOCK_DBDIRS",
                   "-Wno-error=incompatible-pointer-types", "-DC_LINUX", "-DFPU_WORDS_BIGENDIAN=0",
                   "-DWORDS_BIGENDIAN=0", "-std=gnu17", "-fno-define-target-os-macros"], [],
                  ["--debug", "--exclude-dir", ".svn", "--verbose", "-d" + j(d, "dbdir"), "-r"] + inputs, rundir=d,
                  ref=j(d, "clamscan.reference_output"), data=["inputs", "dbdir"]))
    d = j(m, "Applications/JM/lencod")
    t.append(Test("ctmark", "lencod", sorted(j(d, f) for f in os.listdir(d) if f.endswith(".c")),
                  ["-fcommon", "-D__USE_LARGEFILE64", "-D_FILE_OFFSET_BITS=64", "-std=gnu17", "-I" + d], ["-lm"],
                  ["-d", "data/encoder.cfg", "-p", "InputFile=data/foreman_part_qcif_444.yuv",
                   "-p", "LeakyBucketRateFile=data/leakybucketrate.cfg", "-p", "QmatrixFile=data/q_matrix.cfg"],
                  rundir=d, ref=j(d, "lencod.reference_output"), fp_rel=0.025, data=["data"]))
    d = j(m, "Benchmarks/mafft")
    mf = re.search(r"llvm_multisource\(pairlocalalign(.*?)\)", open(j(d, "CMakeLists.txt")).read(), re.S).group(1).split()
    t.append(Test("ctmark", "mafft", [j(d, f) for f in mf], ["-DLLVM", "-std=gnu17", "-I" + d], ["-lm"],
                  ["-b", "62", "-g", "0.100", "-f", "2.00", "-h", "0.100", "-L"], stdin="pyruvate_decarboxylase.fasta",
                  rundir=d, ref=j(d, "pairlocalalign.reference_output"), hash_output=True,
                  data=["pyruvate_decarboxylase.fasta"]))
    d = j(m, "Benchmarks/MiBench/consumer-typeset")
    t.append(Test("ctmark", "consumer-typeset", sorted(j(d, f) for f in os.listdir(d) if f.endswith(".c")),
                  ["-DOS_UNIX=1", "-DOS_DOS=0", "-DOS_MAC=0", "-DDB_FIX=0", "-DUSE_STAT=1", "-DSAFE_DFT=0",
                   "-DCOLLATE=1", '-DLIB_DIR="lout.lib"', '-DFONT_DIR="font"', '-DMAPS_DIR="maps"',
                   '-DINCL_DIR="include"', '-DDATA_DIR="data"', '-DHYPH_DIR="hyph"', '-DLOCALE_DIR="locale"',
                   "-DCHAR_IN=1", "-DCHAR_OUT=0", "-DLOCALE_ON=1", "-DASSERT_ON=1", "-DDEBUG_ON=0",
                   "-DPDF_COMPRESSION=0", "-D_FORTIFY_SOURCE=0", "-std=c99", "-I" + d], ["-lm"],
                  ["-x", "-I", "data/include", "-D", "data/data", "-F", "data/font", "-C", "data/maps", "-H",
                   "data/hyph", "large.lout"], rundir=d, ref=j(d, "consumer-typeset.reference_output"),
                  data=["large.lout", "data"]))
    for x in t:
        x.timeout = 1200
    return t


CXX_EXT = (".cpp", ".cc")


def unittest_cxx_tests(suite):
    """The C++ files of SingleSource/UnitTests (the directories its CMakeLists adds for x86, plus EH/)."""
    u = os.path.join(suite, "SingleSource/UnitTests")
    _D0["unittests-cxx"] = u
    j = os.path.join
    common = ["-Wno-implicit-function-declaration", "-Wno-implicit-int"]
    t = singlesource("unittests-cxx", u, common, exts=CXX_EXT,
                     flags_of=lambda f: ["-fenable-matrix"] if f == "matrix-types-spec.cpp" else [])
    t += singlesource("unittests-cxx", j(u, "C++11"), common + ["-std=c++11", "-pthread"], ["-pthread"], exts=CXX_EXT)
    t += singlesource("unittests-cxx", j(u, "EH"), common + ["-std=gnu++14"], exts=CXX_EXT)  # dynamic exception specs
    t += singlesource("unittests-cxx", j(u, "SignlessTypes"), common, args=["31415926"], exts=CXX_EXT)
    t += singlesource("unittests-cxx", j(u, "SignlessTypes/Large"), common, args=["31415926"], hash_output=True,
                      exts=CXX_EXT)
    t += singlesource("unittests-cxx", j(u, "Vectorizer"), common + ["-std=gnu++17"], exts=CXX_EXT)
    t += singlesource("unittests-cxx", j(u, "Vectorizer/VPlanNativePath"),
                      common + ["-mllvm", "-enable-vplan-native-path", "-fno-vectorize"], exts=CXX_EXT)
    t += singlesource("unittests-cxx", j(u, "X86"), common, exts=CXX_EXT)
    return t


def regression_cxx_tests(suite):
    r = os.path.join(suite, "SingleSource/Regression/C++")
    _D0["regression-cxx"] = r
    t = singlesource("regression-cxx", r, [], exts=CXX_EXT)
    t += singlesource("regression-cxx", os.path.join(r, "EH"), ["-std=gnu++14"], exts=CXX_EXT)
    return t


def benchmark_cxx_tests(suite):
    b = os.path.join(suite, "SingleSource/Benchmarks")
    _D0["benchmarks-cxx"] = b
    j = os.path.join
    t = []
    t += singlesource("benchmarks-cxx", j(b, "Misc-C++"), ["-std=gnu++14"], ["-lm"], fp_abs=0.01, exts=CXX_EXT)
    t += singlesource("benchmarks-cxx", j(b, "Misc-C++/Large"), ["-ffp-contract=off", "-DFMA_DISABLED=1"], ["-lm"],
                      fp_abs=0.01, hash_output=True, exts=CXX_EXT)
    t += singlesource("benchmarks-cxx", j(b, "Misc-C++-EH"), ["-std=gnu++14", "-pthread"], ["-lm", "-pthread"],
                      exts=CXX_EXT)
    shoot = ["ackermann.cpp", "ary.cpp", "ary2.cpp", "ary3.cpp", "fibo.cpp", "hash.cpp", "hash2.cpp", "heapsort.cpp",
             "lists.cpp", "lists1.cpp", "matrix.cpp", "methcall.cpp", "moments.cpp", "nestedloop.cpp", "objinst.cpp",
             "random.cpp", "sieve.cpp", "strcat.cpp", "hello.cpp", "reversefile.cpp", "spellcheck.cpp", "sumcol.cpp",
             "wc.cpp", "wordfreq.cpp"]
    t += singlesource("benchmarks-cxx", j(b, "Shootout-C++"), ["-Wno-deprecated"], ["-lm"], fp_rel=0.00000001,
                      only=shoot)
    t += singlesource("benchmarks-cxx", j(b, "Shootout-C++/EH"), [], exts=CXX_EXT)
    t += singlesource("benchmarks-cxx", j(b, "Adobe-C++"), [], ["-lm"], fp_abs=0.01, exts=CXX_EXT)
    t += singlesource("benchmarks-cxx", j(b, "CoyoteBench"), [], ["-lm"], exts=CXX_EXT)
    t += singlesource("benchmarks-cxx", j(b, "SmallPT"), ["-std=gnu++98"], ["-lm"], fp_rel=0.001, exts=CXX_EXT)
    for x in t:
        x.timeout = 600
    return t


def ctmark_cxx_tests(suite):
    """The four CTMark C++ programs, with their MultiSource CMakeLists' flags and RUN_OPTIONS."""
    m = os.path.join(suite, "MultiSource")
    j = os.path.join
    t = []
    d = j(m, "Benchmarks/7zip")
    zs = re.search(r"llvm_multisource\(7zip-benchmark(.*?)\)", open(j(d, "CMakeLists.txt")).read(), re.S).group(1).split()
    zf = ["-DBREAK_HANDLER", "-DUNICODE", "-D_UNICODE", "-I" + j(d, "C"), "-I" + j(d, "CPP/myWindows"),
          "-I" + j(d, "CPP/include_windows"), "-I" + j(d, "CPP"), "-D_FILE_OFFSET_BITS=64", "-D_LARGEFILE_SOURCE",
          "-DNDEBUG", "-D_REENTRANT", "-DENV_UNIX", "-D_7ZIP_LARGE_PAGES", "-pthread"]
    t.append(Test("ctmark-cxx", "7zip", [j(d, f) for f in zs], zf + ["-std=gnu17"], ["-pthread"], ["b"], rundir=d,
                  cxxflags=["-Wno-error=narrowing"] + zf))
    d = j(m, "Benchmarks/Bullet")
    t.append(Test("ctmark-cxx", "Bullet", sorted(j(d, f) for f in os.listdir(d) if f.endswith(".cpp")),
                  ["-I" + j(d, "include"), "-DNO_TIME", "-std=gnu++98"], ["-lm"], rundir=d,
                  ref=j(d, "bullet.reference_output")))
    d = j(m, "Applications/kimwitu++")
    t.append(Test("ctmark-cxx", "kimwitu++", sorted(j(d, f) for f in os.listdir(d) if f.endswith(".cc")),
                  ["-I" + d, "-DYYDEBUG=1", "-std=gnu++14"], [],
                  ["-f", "test", "-o", "-v", "-s", "kcc", "inputs/f3.k", "inputs/f2.k", "inputs/f1.k"], rundir=d,
                  ref=j(d, "kc.reference_output"), hash_output=True, data=["inputs"]))
    d = j(m, "Benchmarks/tramp3d-v4")
    t.append(Test("ctmark-cxx", "tramp3d-v4", [j(d, "tramp3d-v4.cpp")], ["-std=gnu++14", "-fno-exceptions"], [],
                  ["--cartvis", "1.0", "0.0", "--rhomin", "1e-8", "-n", "10", "--domain", "32", "32", "32"], rundir=d,
                  ref=j(d, "tramp3d-v4.reference_output"), fp_abs=0.0000001))
    for x in t:
        x.timeout = 1200
    return t


def all_tests(suite, corpora):
    out = []
    if {"torture", "ieee", "builtins"} & set(corpora):
        out += [t for t in torture_tests(suite) if t.corpus in corpora]
    if "unittests" in corpora:
        out += unittest_tests(suite)
    if "regression" in corpora:
        out += regression_tests(suite)
    if "benchmarks" in corpora:
        out += benchmark_tests(suite)
    if "ctmark" in corpora:
        out += ctmark_tests(suite)
    if "unittests-cxx" in corpora:
        out += unittest_cxx_tests(suite)
    if "regression-cxx" in corpora:
        out += regression_cxx_tests(suite)
    if "benchmarks-cxx" in corpora:
        out += benchmark_cxx_tests(suite)
    if "ctmark-cxx" in corpora:
        out += ctmark_cxx_tests(suite)
    return out


# ------------------------------------------------------------------ running

def sh(cmd, timeout=600, **kw):
    try:
        return subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout, **kw)
    except subprocess.TimeoutExpired:
        return subprocess.CompletedProcess(cmd, -999, b"", b"timeout")


class Fail(Exception):
    def __init__(self, kind, msg):
        super().__init__(msg)
        self.kind = kind
        self.msg = msg


def setup_rundir(t, wd):
    """Directory to run in: the test's files are symlinked into it (like llvm_test_data)."""
    rd = os.path.join(wd, "run")
    os.makedirs(os.path.join(rd, "Output"), exist_ok=True)  # lit's Output/ (lencod writes there)
    for f in t.data:
        dst = os.path.join(rd, f)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        if not os.path.lexists(dst):
            os.symlink(os.path.join(t.rundir, f), dst)
    if t.prepare:
        t.prepare(rd)
    return rd


def run_and_verify(t, exe, wd, args, timeout):
    rd = setup_rundir(t, wd)
    out = os.path.join(wd, os.path.basename(exe) + ".out")
    stdin = open(os.path.join(rd, t.stdin), "rb") if t.stdin else subprocess.DEVNULL
    t0 = time.time()
    with open(out, "wb") as fo:
        try:
            p = subprocess.run([exe] + t.args, stdout=fo, stderr=fo, stdin=stdin, cwd=rd, timeout=timeout)
            code = p.returncode
        except subprocess.TimeoutExpired:
            code = None
    dt = time.time() - t0
    if t.stdin:
        stdin.close()
    if code is None:
        raise Fail("fail", f"timeout after {timeout:.0f}s")
    if t.exit0:
        if code != 0:
            raise Fail("fail", f"exit status {code}")
        return dt
    if code < 0:
        # A signal: timeit reports it as an exit status of 128+N.
        code = 128 - code
    with open(out, "ab") as fo:
        fo.write(f"exit {code}\n".encode())
    if t.ref is None:
        if code != 0:
            raise Fail("fail", f"exit status {code} (no reference output)")
        return dt
    cmp_file = out
    if t.hash_output:
        cmp_file = out + ".md5"
        with open(cmp_file, "w") as fo:
            fo.write(hashlib.md5(open(out, "rb").read()).hexdigest() + "\n")
    cmd = [args.fpcmp]
    if t.fp_rel is not None:
        cmd += ["-r", str(t.fp_rel)]
    if t.fp_abs is not None:
        cmd += ["-a", str(t.fp_abs)]
    r = sh(cmd + [cmp_file, t.ref])
    if r.returncode != 0:
        head = open(out, "rb").read()[-600:].decode(errors="replace")
        raise Fail("fail", f"output differs from {os.path.basename(t.ref)} (exit {code}): "
                   f"{r.stdout.decode(errors='replace')[:300]}\n--- tail of output\n{head}")
    return dt


def time_exe(t, exe, wd, n):
    """Best wall time of n runs of exe (output discarded, not verified again)."""
    rd = setup_rundir(t, wd)
    best = None
    for _ in range(n):
        stdin = open(os.path.join(rd, t.stdin), "rb") if t.stdin else subprocess.DEVNULL
        t0 = time.perf_counter()
        subprocess.run([exe] + t.args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, stdin=stdin, cwd=rd)
        dt = time.perf_counter() - t0
        if t.stdin:
            stdin.close()
        best = dt if best is None else min(best, dt)
    return best


def obj_name(src, i):
    return f"{i:03d}_{os.path.splitext(os.path.basename(src))[0]}"


def compiler(t, src, args):
    return args.clangxx if is_cxx(src) else args.clang


def linker(t, args):
    return args.clangxx if t.cxx else args.clang


def build_baseline(t, wd, args, level="O0"):
    exe = os.path.join(wd, "base.exe" if level == "O0" else f"base-{level}.exe")
    objs = []
    for i, s in enumerate(t.srcs):
        o = os.path.join(wd, obj_name(s, i) + (".base.o" if level == "O0" else f".base-{level}.o"))
        r = sh([compiler(t, s, args), "-" + level] + t.flags(s) + ["-c", s, "-o", o])
        if r.returncode:
            raise Fail("build", f"clang -{level} failed on {os.path.basename(s)}:\n{r.stderr.decode(errors='replace')[-800:]}")
        objs.append(o)
    r = sh([linker(t, args)] + objs + t.ldflags + ["-o", exe])
    if r.returncode:
        raise Fail("build", f"link failed:\n{r.stderr.decode(errors='replace')[-800:]}")
    return exe


def emit_bc(t, s, i, wd, variant, args):
    base = os.path.join(wd, obj_name(s, i) + "." + variant)
    bc = base + ".bc"
    cc = compiler(t, s, args)
    if variant in ("O0", "O1"):
        cmd = [cc, "-O0"] + t.flags(s) + ["-c", "-emit-llvm", s, "-o", bc]
    elif variant in ("g", "O1-g"):
        cmd = [cc, "-O0", "-g"] + t.flags(s) + ["-c", "-emit-llvm", s, "-o", bc]
    elif variant == "O2ir":
        cmd = [cc, "-O2"] + t.flags(s) + ["-c", "-emit-llvm", s, "-o", bc]
    else:
        raw = base + ".raw.bc"
        r = sh([cc, "-O0", "-Xclang", "-disable-O0-optnone"] + t.flags(s) + ["-c", "-emit-llvm", s, "-o", raw])
        if r.returncode:
            raise Fail("error", f"clang -emit-llvm failed on {os.path.basename(s)}")
        cmd = [args.opt, "-passes=mem2reg", raw, "-o", bc]
    r = sh(cmd)
    if r.returncode:
        raise Fail("error", f"{os.path.basename(cmd[0])} failed on {os.path.basename(s)}: "
                   f"{r.stderr.decode(errors='replace')[-400:]}")
    return base, bc


def verify_dwarf(o, s, args, info):
    """--verify-dwarf: llvm-dwarfdump --verify on a -g object; a failure fails the test."""
    if not args.verify_dwarf:
        return
    r = sh([args.dwarfdump, "--verify", o], timeout=600)
    out = (r.stdout + r.stderr).decode(errors="replace")
    bad = [l for l in out.splitlines() if l.startswith(("error:", "warning:"))]
    if r.returncode != 0 or bad:
        raise Fail("fail", f"llvm-dwarfdump --verify on {os.path.basename(s)}: {(bad or out.splitlines()[-1:] or [''])[0][:300]}")
    info["dwarf_verified"] = info.get("dwarf_verified", 0) + 1


def build_goovm_cc(t, wd, variant, args, info):
    exe = os.path.join(wd, variant + ".exe")
    objs = []
    for i, s in enumerate(t.srcs):
        o = os.path.join(wd, obj_name(s, i) + "." + variant + ".o")
        cmd = ([args.cc, "--backend=goose"] + (["--fallback"] if args.fallback else [])
               + (["-O1"] if variant == "cc-O1" else ["-O0"])
               + (["-g"] if variant == "cc-g" else []) + t.flags(s) + ["-c", s, "-o", o])
        r = sh(cmd, timeout=600)
        err = r.stderr.decode(errors="replace")
        if r.returncode == 2:
            raise Fail("unsupported", f"{os.path.basename(s)}: {err.strip().splitlines()[0] if err.strip() else ''}")
        if r.returncode != 0:
            raise Fail("error", f"goovm-cc exit {r.returncode} on {os.path.basename(s)}: {err[-600:]}")
        if "goovm-cc: falling back to LLVM:" in err:
            info.setdefault("fallback", []).append(
                f"{os.path.basename(s)}: {err.split('goovm-cc: falling back to LLVM:', 1)[1].strip().splitlines()[0]}")
        if variant == "cc-g":
            verify_dwarf(o, s, args, info)
        objs.append(o)
    r = sh([linker(t, args)] + objs + t.ldflags + ["-o", exe])
    if r.returncode:
        raise Fail("fail", f"link failed:\n{r.stderr.decode(errors='replace')[-800:]}")
    return exe


def build_goovm(t, wd, variant, args, info):
    if variant in EXTRA_VARIANTS:
        return build_goovm_cc(t, wd, variant, args, info)
    exe = os.path.join(wd, variant + ".exe")
    objs = []
    for i, s in enumerate(t.srcs):
        base, bc = emit_bc(t, s, i, wd, variant, args)
        o = base + ".o"
        cmd = ([args.goovm, "--backend=goose"] + (["--fallback"] if args.fallback else [])
               + (["-O1"] if variant in OPT_VARIANTS else []) + [bc, "-o", o])
        r = sh(cmd, timeout=600)
        err = r.stderr.decode(errors="replace")
        if r.returncode == 2:
            raise Fail("unsupported", f"{os.path.basename(s)}: {err.strip().splitlines()[0] if err.strip() else ''}")
        if r.returncode != 0:
            raise Fail("error", f"goovm-llc exit {r.returncode} on {os.path.basename(s)}: {err[-600:]}")
        if "goovm-llc: fallback:" in err:
            info.setdefault("fallback", []).append(
                f"{os.path.basename(s)}: {err.split('goovm-llc: fallback:', 1)[1].strip().splitlines()[0]}")
        if variant in ("g", "O1-g"):
            verify_dwarf(o, s, args, info)
        objs.append(o)
    r = sh([linker(t, args)] + objs + t.ldflags + ["-o", exe])
    if r.returncode:
        raise Fail("fail", f"link failed:\n{r.stderr.decode(errors='replace')[-800:]}")
    return exe


def baseline_at(t, wd, args, cache, level):
    """The clang -<level> baseline of t ({"key", "status", "time"}), from the cache if current."""
    key = t.key()
    ck = t.id if level == "O0" else f"{t.id}@{level}"
    b = cache.get(ck)
    if b is None or b.get("key") != key or args.rebaseline:
        try:
            exe = build_baseline(t, wd, args, level)
            dt = run_and_verify(t, exe, wd, args, timeout=t.timeout or 120)
            b = {"key": key, "status": "pass", "time": dt}
        except Fail as e:
            b = {"key": key, "status": "build" if e.kind == "build" else "fail", "msg": e.msg[:2000]}
        except Exception as e:  # noqa
            b = {"key": key, "status": "fail", "msg": f"harness: {e}"}
    return ck, b


def do_test(t, args, baseline_cache):
    wd = os.path.join(args.work, t.corpus, t.name.replace("/", "__"))
    os.makedirs(wd, exist_ok=True)
    res = {"id": t.id}
    key = t.key()
    b = baseline_cache.get(t.id)
    if args.emit_bc:
        for v in args.variants:
            for i, s in enumerate(t.srcs):
                try:
                    emit_bc(t, s, i, wd, v, args)
                except Fail as e:
                    res.setdefault("emit_errors", []).append(e.msg)
        return res
    if b is None or b.get("key") != key or args.rebaseline:
        try:
            exe = build_baseline(t, wd, args)
            dt = run_and_verify(t, exe, wd, args, timeout=t.timeout or 120)
            b = {"key": key, "status": "pass", "time": dt}
        except Fail as e:
            b = {"key": key, "status": "build" if e.kind == "build" else "fail", "msg": e.msg[:2000]}
        except Exception as e:  # noqa
            b = {"key": key, "status": "fail", "msg": f"harness: {e}"}
    res["baseline"] = b
    if b["status"] != "pass" or args.baseline_only:
        return res
    tmo = max(60.0, 20 * b["time"]) if t.timeout is None else max(t.timeout, 20 * b["time"])
    b1 = None
    if any(opt_variant(v) for v in args.variants):
        ck, b1 = baseline_at(t, wd, args, baseline_cache, "O1")
        res["baseline_O1"] = b1
        res["baseline_O1_key"] = ck
    if args.time_run:
        exe = os.path.join(wd, "base.exe")
        if not os.path.exists(exe):
            exe = build_baseline(t, wd, args)
        res["base_run"] = time_exe(t, exe, wd, args.time_run)
        for lv in args.time_ref:
            try:
                exe = os.path.join(wd, f"base-{lv}.exe")
                if not os.path.exists(exe):
                    exe = build_baseline(t, wd, args, lv)
                res[f"base_run_{lv}"] = time_exe(t, exe, wd, args.time_run)
            except Fail:
                pass
    for v in args.variants:
        info = {}
        if opt_variant(v) and b1["status"] != "pass":
            info["status"] = "excluded"
            res[v] = info
            continue
        try:
            exe = build_goovm(t, wd, v, args, info)
            run_and_verify(t, exe, wd, args, timeout=tmo)
            info["status"] = "fallback" if info.get("fallback") else "pass"
            if args.time_run:
                info["run"] = time_exe(t, exe, wd, args.time_run)
        except Fail as e:
            info["status"] = e.kind if e.kind in ("unsupported", "error") else "fail"
            info["msg"] = e.msg[:3000]
        except Exception as e:  # noqa
            info["status"] = "error"
            info["msg"] = f"harness: {e}"
        res[v] = info
    if not args.keep and all(res.get(v, {}).get("status") in ("pass", "excluded") for v in args.variants):
        for f in os.listdir(wd):
            if f != "run":
                p = os.path.join(wd, f)
                if os.path.isfile(p):
                    os.unlink(p)
    return res


def report(results, tests, args):
    by = {}
    for t in tests:
        by.setdefault(t.corpus, []).append(results[t.id])
    lines = ["# goovm-llc correctness report", ""]
    lines.append(f"goovm-llc: `{args.goovm}`{' (--fallback)' if args.fallback else ''}; variants: {', '.join(args.variants)}")
    lines.append("")
    hdr = "| corpus | tests | clang -O0 pass | excluded |"
    sep = "|---|---:|---:|---:|"
    for v in args.variants:
        hdr += f" {v} pass | {v} fail | {v} unsup | {v} fallback |"
        sep += "---:|---:|---:|---:|"
    lines += [hdr, sep]
    tot = {}
    for c in CORPORA:
        if c not in by:
            continue
        rs = by[c]
        bp = [r for r in rs if r.get("baseline", {}).get("status") == "pass"]
        row = f"| {c} | {len(rs)} | {len(bp)} | {len(rs) - len(bp)} |"
        for v in args.variants:
            st = [r.get(v, {}).get("status") for r in bp]
            ex = f" (of {len(st) - st.count('excluded')})" if opt_variant(v) else ""
            row += (f" {st.count('pass') + st.count('fallback')}{ex} | {st.count('fail') + st.count('error')} |"
                    f" {st.count('unsupported')} | {st.count('fallback')} |")
        lines.append(row)
    lines.append("")
    lines.append("pass includes fallback; fallback counts tests in which at least one file was compiled by "
                 "LLVM's code generator (goovm-llc --fallback). The optimizing variants (O1, O1-g, O2ir, cc-O1) "
                 "run the tests that also pass when built with plain clang-20 -O1 (\"of N\").")
    if args.verify_dwarf:
        nv = sum(r.get(v, {}).get("dwarf_verified", 0) for r in results.values() for v in args.variants)
        lines.append("")
        lines.append(f"llvm-dwarfdump --verify passed on {nv} objects (variants g / cc-g of the passing tests; "
                     "a failure counts as a failed test).")
    lines.append("")
    if args.time_run:
        refs = ["O0"] + [lv for lv in args.time_ref if lv != "O0"]
        rk = {lv: ("base_run" if lv == "O0" else f"base_run_{lv}") for lv in refs}

        def ref_of(v):
            # the optimizing variants against clang -O1 when it is timed
            return "O1" if opt_variant(v) and "O1" in refs else "O0"
        lines.append(f"## Run times (best of {args.time_run}, seconds; each variant's ratio to clang at its level: "
                     f"-O1 for the optimizing variants when timed, else -O0)")
        lines.append("")
        hdr = "| test |" + "".join(f" clang -{lv} |" for lv in refs) + \
              "".join(f" {v} | {v} / clang -{ref_of(v)} |" for v in args.variants)
        lines += [hdr, "|---|" + "---:|" * len(refs) + "---:|---:|" * len(args.variants)]
        import math
        logs = {v: [] for v in args.variants}
        rlogs = {lv: [] for lv in refs}
        for t in tests:
            r = results[t.id]
            if "base_run" not in r:
                continue
            row = f"| {t.id} |"
            for lv in refs:
                x = r.get(rk[lv])
                row += " - |" if x is None else f" {x:.3f} |"
                if x and r["base_run"] >= 0.05 and lv != "O0":
                    rlogs[lv].append(math.log(x / r["base_run"]))
            for v in args.variants:
                x = r.get(v, {}).get("run")
                base = r.get(rk[ref_of(v)])
                if x is None or not base:
                    row += " - | - |"
                else:
                    q = x / base
                    row += f" {x:.3f} | {q:.2f} |"
                    if r["base_run"] >= 0.05 and q > 0:
                        logs[v].append(math.log(q))
            lines.append(row)
        geo = "| geometric mean (clang -O0 >= 50 ms) |"
        for lv in refs:
            geo += " |" if lv == "O0" or not rlogs[lv] else f" {math.exp(sum(rlogs[lv]) / len(rlogs[lv])):.3f} x -O0 |"
        for v in args.variants:
            g = math.exp(sum(logs[v]) / len(logs[v])) if logs[v] else 0
            geo += f" | {g:.3f} |"
        lines.append(geo)
        lines.append("")
    for c in CORPORA:
        if c not in by:
            continue
        rs = by[c]
        bad = []
        for r in rs:
            if r.get("baseline", {}).get("status") != "pass":
                continue
            for v in args.variants:
                s = r.get(v, {}).get("status")
                if s not in ("pass", "excluded", None):
                    msg = r[v].get("msg", "") or "; ".join(r[v].get("fallback", []))
                    bad.append(f"- `{r['id']}` [{v}] {s}: {msg.splitlines()[0][:200] if msg else ''}")
        if bad:
            lines.append(f"## {c}: not passing")
            lines.append("")
            lines += bad
            lines.append("")
        excl = [r for r in rs if r.get("baseline", {}).get("status") != "pass"]
        if excl:
            lines.append(f"## {c}: excluded (do not pass with clang-20 -O0)")
            lines.append("")
            for r in excl:
                m = r.get("baseline", {}).get("msg", "")
                lines.append(f"- `{r['id']}` {r['baseline']['status']}: {m.splitlines()[0][:160] if m else ''}")
            lines.append("")
    return "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goovm", default=os.environ.get("GOOVM_LLC", os.path.join(ROOT, "build/tools/goovm-llc/goovm-llc")))
    ap.add_argument("--suite", default="/home/user/llvm/llvm-test-suite")
    ap.add_argument("--corpus", default=",".join(CORPORA))
    ap.add_argument("--variants", default=",".join(VARIANTS))
    ap.add_argument("--clang", default="clang-20")
    ap.add_argument("--clangxx", default="clang++-20")
    ap.add_argument("--cc", default=os.environ.get("GOOVM_CC", os.path.join(ROOT, "build/tools/goovm-cc/goovm-cc")),
                    help="goovm-cc, for the cc and cc-g variants")
    ap.add_argument("--opt", default="opt-20")
    ap.add_argument("-j", type=int, default=3)
    ap.add_argument("--work", default=os.path.join(ROOT, "build-suite"))
    ap.add_argument("--fallback", action="store_true", help="pass --fallback to goovm-llc")
    ap.add_argument("--keep", action="store_true", help="keep build products of passing tests")
    ap.add_argument("--verify-dwarf", action="store_true",
                    help="run llvm-dwarfdump --verify on every object of the g and cc-g variants")
    ap.add_argument("--dwarfdump", default="llvm-dwarfdump-20")
    ap.add_argument("--rebaseline", action="store_true", help="recompute the clang -O0 baseline")
    ap.add_argument("--baseline-only", action="store_true")
    ap.add_argument("--emit-bc", action="store_true", help="only write the bitcode of each variant (for analysis)")
    ap.add_argument("--time-run", type=int, default=0, metavar="N",
                    help="also time each passing program and its clang -O0 build: best of N runs (use -j 1)")
    ap.add_argument("--time-ref", default="", metavar="LEVELS",
                    help="with --time-run, also time clang builds at these levels (e.g. O1,O2)")
    ap.add_argument("--report", default="")
    ap.add_argument("--json", default="")
    ap.add_argument("filter", nargs="*", help="substrings of test ids to run")
    args = ap.parse_args()
    args.variants = [v for v in args.variants.split(",") if v]
    args.time_ref = [v for v in args.time_ref.split(",") if v and v != "O0"]
    corpora = [c for c in args.corpus.split(",") if c]
    for v in args.variants:
        if v not in VARIANTS + EXTRA_VARIANTS + OPT_VARIANTS:
            sys.exit(f"unknown variant {v}")
    os.makedirs(args.work, exist_ok=True)
    args.work = os.path.abspath(args.work)
    if not args.emit_bc and not args.baseline_only and not os.path.exists(args.goovm):
        sys.exit(f"goovm-llc not found at {args.goovm} (use --goovm or GOOVM_LLC)")
    args.fpcmp = os.path.join(args.work, "fpcmp")
    if not os.path.exists(args.fpcmp):
        r = sh([args.clang, "-O2", "-w", os.path.join(args.suite, "tools/fpcmp.c"), "-o", args.fpcmp])
        if r.returncode:
            sys.exit("cannot build fpcmp: " + r.stderr.decode())
    tests = all_tests(args.suite, corpora)
    if args.filter:
        tests = [t for t in tests if any(f in t.id for f in args.filter)]
    bfile = os.path.join(args.work, "baseline.json")
    baseline_cache = json.load(open(bfile)) if os.path.exists(bfile) else {}
    results = {}
    t0 = time.time()
    done = 0
    with cf.ThreadPoolExecutor(max_workers=args.j) as ex:
        futs = {ex.submit(do_test, t, args, baseline_cache): t for t in tests}
        for fu in cf.as_completed(futs):
            t = futs[fu]
            r = fu.result()
            results[t.id] = r
            done += 1
            if "baseline" in r:
                baseline_cache[t.id] = r["baseline"]
            if "baseline_O1" in r:
                baseline_cache[r["baseline_O1_key"]] = r["baseline_O1"]
            st = [f"{v}:{r[v]['status']}" for v in args.variants if v in r]
            bad = [s for s in st if not s.endswith((":pass", ":excluded"))]
            if bad or r.get("baseline", {}).get("status") not in ("pass", None):
                print(f"[{done}/{len(tests)}] {t.id}: baseline={r.get('baseline', {}).get('status')} {' '.join(st)}",
                      flush=True)
            elif done % 100 == 0:
                print(f"[{done}/{len(tests)}] {time.time() - t0:.0f}s", flush=True)
    if not args.emit_bc:
        json.dump(baseline_cache, open(bfile, "w"), indent=1, sort_keys=True)
        rep = report(results, tests, args)
        print(rep)
        if args.report:
            open(args.report, "w").write(rep)
        if args.json:
            json.dump(results, open(args.json, "w"), indent=1, sort_keys=True)
    print(f"{len(tests)} tests in {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
