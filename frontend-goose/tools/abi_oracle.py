#!/usr/bin/env python3
"""The C++ ABI oracle for goosecc (milestone D3): objects of goosecc and of
clang++-20 must be interchangeable at every function boundary.

For every translation unit (the C++ corpora of tests/suite.py, or files):

  syms    goosecc -c and clang++-20 -O0 -c of the same source; the global
          and weak symbols (and the local ones with mangled names: internal
          entities) of both objects are compared: name, defined or not,
          binding, visibility, type, the kind of its section (text, data,
          data.rel.ro, rodata, bss, tdata, tbss, init_array ...) and whether
          it is in a comdat group (and the group's signature). Each
          difference is listed.

  split   a program whose TUs are each split between the two compilers:
          both objects of every TU are linked, and every function defined
          in both is taken from one of them (objcopy --weaken-symbol on the
          other copy), alternately, so that calls, returns, exceptions,
          vtables, typeinfo and dynamic_cast cross from code of one
          compiler to code of the other at half of the function
          boundaries. Variables come from the goosecc object (the clang
          object's copies are weakened, its .init_array dropped). Two
          assignments are run (functions with even / odd index from
          goosecc) and both object orders (which comdat copy the linker
          keeps); each run's output must be the reference output.

usage: frontend-goose/tools/abi_oracle.py [--goosecc PATH] [--modes syms,split]
         [--corpus unittests-cxx,regression-cxx,...] [-j N] [--work DIR] [--json FILE]
         [--show N] [filter ...]
       frontend-goose/tools/abi_oracle.py --files a.cpp [b.cpp ...] [-- flags]
"""
import argparse, concurrent.futures as cf, json, os, re, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "tests"))
import suite  # noqa: E402

CXX = "clang++-20"


def sh(cmd, **kw):
    return subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=kw.pop("timeout", 600), **kw)


SEC_KINDS = [
    (r"^\.text", "text"), (r"^\.data\.rel\.ro", "relro"), (r"^\.rodata", "rodata"), (r"^\.bss", "bss"),
    (r"^\.tbss", "tbss"), (r"^\.tdata", "tdata"), (r"^\.data", "data"), (r"^\.init_array", "init_array"),
    (r"^\.fini_array", "fini_array"), (r"^\.gcc_except_table", "except"),
]


def sec_kind(name):
    for pat, k in SEC_KINDS:
        if re.match(pat, name):
            return k
    return name


def read_syms(obj):
    """{name: (defined, bind, vis, type, section kind, comdat signature)}"""
    secs = {}
    r = sh(["readelf", "-SW", obj])
    for ln in r.stdout.decode(errors="replace").splitlines():
        m = re.match(r"\s*\[\s*(\d+)\]\s+(\S+)", ln)
        if m:
            secs[int(m.group(1))] = m.group(2)
    groups = {}
    r = sh(["readelf", "-gW", obj])
    sig = None
    for ln in r.stdout.decode(errors="replace").splitlines():
        m = re.match(r"COMDAT group section \[\s*\d+\] `\.group' \[(.*)\] contains", ln)
        if m:
            sig = m.group(1)
            continue
        m = re.match(r"\s*\[\s*(\d+)\]\s+(\S+)", ln)
        if m and sig is not None:
            groups[int(m.group(1))] = sig
    out = {}
    r = sh(["readelf", "-sW", obj])
    for ln in r.stdout.decode(errors="replace").splitlines():
        p = ln.split()
        if len(p) < 8 or not p[0].endswith(":"):
            continue
        typ, bind, vis, ndx, name = p[3], p[4], p[5], p[6], p[7]
        if typ in ("FILE", "SECTION") or name.startswith(".L"):
            continue
        if bind == "LOCAL" and not name.startswith("_Z"):
            continue
        defined = ndx != "UND"
        sk = ""
        grp = ""
        if ndx.isdigit():
            sk = sec_kind(secs.get(int(ndx), "?"))
            grp = groups.get(int(ndx), "")
        elif ndx == "COM":
            sk = "common"
        # an undefined symbol's type does not matter (clang: NOTYPE)
        if not defined:
            typ = ""
        out[name] = (defined, bind, vis, typ, sk, grp)
    return out


def cmp_syms(ref, got):
    diffs = []
    for n in sorted(set(ref) | set(got)):
        a, b = ref.get(n), got.get(n)
        if a == b:
            continue
        if a is None:
            # an undefined reference clang does not make (a call goosecc keeps) is still a difference
            diffs.append(f"extra {n}: {fmt(b)}")
        elif b is None:
            diffs.append(f"missing {n}: {fmt(a)}")
        else:
            diffs.append(f"{n}: clang {fmt(a)} / goosecc {fmt(b)}")
    return diffs


def fmt(x):
    defined, bind, vis, typ, sk, grp = x
    s = ("def " if defined else "und ") + bind + " " + vis
    if typ:
        s += " " + typ
    if sk:
        s += " " + sk
    if grp:
        s += " comdat[" + grp + "]"
    return s


def compile_both(t, s, i, wd, args):
    base = os.path.join(wd, suite.obj_name(s, i))
    flags = t.flags(s)
    co = base + ".clang.o"
    go = base + ".gc.o"
    r = sh([CXX, "-O0", "-c", "-w"] + flags + [s, "-o", co])
    if r.returncode:
        raise suite.Fail("build", "clang++: " + r.stderr.decode(errors="replace")[:500])
    r = sh([args.goosecc, "-c", "-O0"] + flags + [s, "-o", go])
    if r.returncode:
        lines = [ln for ln in r.stderr.decode(errors="replace").splitlines() if "note: ignoring" not in ln]
        raise suite.Fail("error", "goosecc: " + (lines[0] if lines else f"exit {r.returncode}")[:400])
    return co, go


def defined_globals(obj):
    out = []
    for n, v in read_syms(obj).items():
        if v[0] and v[1] != "LOCAL":
            out.append((n, v))
    return out


def split_objects(co, go, wd, tag, parity):
    """Copies of the two objects where each function defined (global, not in
    a comdat) in both comes from one of them: index parity -> goosecc."""
    gsyms = dict(defined_globals(go))
    csyms = dict(defined_globals(co))
    both = sorted(n for n in gsyms if n in csyms and gsyms[n][1] == "GLOBAL" and csyms[n][1] == "GLOBAL")
    weak_in_g, weak_in_c = [], []
    for k, n in enumerate(both):
        if gsyms[n][3] == "FUNC" and k % 2 != parity:
            weak_in_g.append(n)     # from clang
        else:
            weak_in_c.append(n)     # from goosecc (all variables too)
    g2 = os.path.join(wd, f"{tag}.g.o")
    c2 = os.path.join(wd, f"{tag}.c.o")
    cmd = ["objcopy"] + [f"--weaken-symbol={n}" for n in weak_in_g] + [go, g2]
    r = sh(cmd)
    if r.returncode:
        raise suite.Fail("fail", "objcopy: " + r.stderr.decode(errors="replace")[:300])
    cmd = ["objcopy", "--remove-section=.init_array", "--remove-section=.rela.init_array"]
    cmd += [f"--weaken-symbol={n}" for n in weak_in_c] + [co, c2]
    r = sh(cmd)
    if r.returncode:
        raise suite.Fail("fail", "objcopy: " + r.stderr.decode(errors="replace")[:300])
    return g2, c2, len(both)


def do_test(t, args, baseline):
    wd = os.path.join(args.work, t.corpus, t.name.replace("/", "__"))
    os.makedirs(wd, exist_ok=True)
    res = {"id": t.id}
    b = baseline.get(t.id)
    if b is not None and b.get("status") != "pass":
        res["status"] = "excluded"
        return res
    try:
        objs = []
        for i, s in enumerate(t.srcs):
            if not suite.is_cxx(s):
                o = os.path.join(wd, suite.obj_name(s, i) + ".c.o")
                r = sh(["clang-20", "-O0", "-c", "-w"] + t.flags(s) + [s, "-o", o])
                if r.returncode:
                    raise suite.Fail("build", r.stderr.decode(errors="replace")[:300])
                objs.append((None, o, s))
                continue
            co, go = compile_both(t, s, i, wd, args)
            objs.append((co, go, s))
        if "syms" in args.modes:
            diffs = []
            for co, go, s in objs:
                if co is None:
                    continue
                d = cmp_syms(read_syms(co), read_syms(go))
                diffs += [os.path.basename(s) + ": " + x for x in d]
            res["syms"] = diffs
        if "split" in args.modes:
            runs = []
            for parity in (0, 1):
                for order in ("gc", "cg"):
                    tag = f"split{parity}{order}"
                    link = []
                    nb = 0
                    for k, (co, go, s) in enumerate(objs):
                        if co is None:
                            link.append(go)
                            continue
                        g2, c2, n = split_objects(co, go, wd, f"{tag}.{k}", parity)
                        nb += n
                        link += [g2, c2] if order == "gc" else [c2, g2]
                    exe = os.path.join(wd, tag + ".exe")
                    r = sh([suite.linker(t, args)] + link + t.ldflags + ["-o", exe])
                    if r.returncode:
                        runs.append(f"{tag}: link failed: {r.stderr.decode(errors='replace')[-400:]}")
                        continue
                    try:
                        suite.run_and_verify(t, exe, wd, args, timeout=max(120, 20 * (b or {}).get("time", 5)))
                    except suite.Fail as e:
                        runs.append(f"{tag}: {e.msg[:600]}")
            res["split"] = runs
            res["boundaries"] = nb
        ok = not res.get("syms") and not res.get("split")
        res["status"] = "pass" if ok else "fail"
    except suite.Fail as e:
        res["status"] = e.kind
        res["msg"] = e.msg
    except subprocess.TimeoutExpired:
        res["status"] = "fail"
        res["msg"] = "timeout"
    if not args.keep:
        shutil.rmtree(wd, ignore_errors=True)
    return res


def files_mode(args, files, flags):
    t = suite.Test("files", "files", files, flags, [], exit0=False)
    wd = tempfile.mkdtemp(prefix="abi-oracle-")
    objs = []
    for i, s in enumerate(files):
        co, go = compile_both(t, s, i, wd, args)
        objs.append((co, go, s))
    bad = 0
    for co, go, s in objs:
        d = cmp_syms(read_syms(co), read_syms(go))
        print(f"{s}: {len(d)} symbol differences")
        for x in d[:args.show]:
            print("  " + x)
        bad += len(d)
    # the split links: the reference is the clang build
    ref = os.path.join(wd, "ref.exe")
    r = sh([CXX] + [co for co, _, _ in objs] + ["-o", ref])
    exp = sh([ref])
    for parity in (0, 1):
        for order in ("gc", "cg"):
            link = []
            for k, (co, go, s) in enumerate(objs):
                g2, c2, n = split_objects(co, go, wd, f"s{parity}{order}{k}", parity)
                link += [g2, c2] if order == "gc" else [c2, g2]
            exe = os.path.join(wd, f"s{parity}{order}.exe")
            r = sh([CXX] + link + ["-o", exe])
            if r.returncode:
                print(f"split {parity}{order}: link failed\n{r.stderr.decode(errors='replace')[-600:]}")
                bad += 1
                continue
            got = sh([exe])
            same = (got.stdout, got.returncode) == (exp.stdout, exp.returncode)
            print(f"split {parity}{order}: {'ok' if same else 'DIFFERENT OUTPUT'}")
            if not same:
                bad += 1
    shutil.rmtree(wd, ignore_errors=True)
    return 1 if bad else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goosecc", default=os.path.join(ROOT, "frontend-goose/build/goosecc"))
    ap.add_argument("--suite", default="/home/user/llvm/llvm-test-suite")
    ap.add_argument("--corpus", default="unittests-cxx,regression-cxx,benchmarks-cxx,ctmark-cxx")
    ap.add_argument("--modes", default="syms,split")
    ap.add_argument("-j", type=int, default=2)
    ap.add_argument("--work", default="")
    ap.add_argument("--baseline", default="", help="a suite_goosecc baseline.json: tests that fail with clang are excluded")
    ap.add_argument("--json", default="")
    ap.add_argument("--show", type=int, default=20)
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--files", action="store_true", help="the arguments are source files of one program")
    ap.add_argument("rest", nargs="*")
    argv = sys.argv[1:]
    flags = []
    if "--" in argv:
        k = argv.index("--")
        flags = argv[k + 1:]
        argv = argv[:k]
    args = ap.parse_args(argv)
    args.goosecc = os.path.abspath(args.goosecc)
    args.modes = args.modes.split(",")
    args.clang = "clang-20"
    args.clangxx = CXX
    if args.files:
        sys.exit(files_mode(args, args.rest, flags))
    if not args.work:
        args.work = tempfile.mkdtemp(prefix="abi-oracle-")
    tests = suite.all_tests(args.suite, args.corpus.split(","))
    if args.rest:
        tests = [t for t in tests if any(f in t.id for f in args.rest)]
    baseline = {}
    if args.baseline and os.path.exists(args.baseline):
        baseline = json.load(open(args.baseline))
    results = []
    with cf.ThreadPoolExecutor(max_workers=args.j) as ex:
        for res in ex.map(lambda t: do_test(t, args, baseline), tests):
            results.append(res)
            st = res["status"]
            line = f"{res['id']:50s} {st}"
            if st == "fail":
                line += f"  (syms: {len(res.get('syms') or [])} differences, split: {len(res.get('split') or [])} failing runs)"
            elif res.get("msg"):
                line += "  " + res["msg"].splitlines()[0][:150]
            print(line, flush=True)
            for x in (res.get("syms") or [])[:args.show]:
                print("    " + x)
            for x in (res.get("split") or [])[:4]:
                print("    " + x.replace("\n", "\n      ")[:800])
    n = len(results)
    counts = {}
    for r in results:
        counts[r["status"]] = counts.get(r["status"], 0) + 1
    print("\n" + ", ".join(f"{k}: {v}" for k, v in sorted(counts.items())) + f" ({n} tests)")
    if args.json:
        json.dump(results, open(args.json, "w"), indent=1)


if __name__ == "__main__":
    main()
