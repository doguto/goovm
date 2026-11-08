#!/usr/bin/env python3
"""Correctness harness for goosecc (milestone B2): the corpora of suite.py,
every source file compiled by goosecc instead of clang + goovm-llc (C++
sources too, since D1: the C++ corpora unittests-cxx, regression-cxx ...).

For every test of the selected corpora:

  baseline   clang-20 -O0 <test flags> srcs -o exe; run; verify   (shared with suite.py's rules)
  O0         goosecc -c <test flags> src -o obj, per source; clang-20 links; run; verify
  g          the same with -g

The tests, their flags, inputs, verification (traditional output with
fpcmp, or exit status 0 for gcc-c-torture) and the exclusion rule (a test
that does not build or pass with plain clang-20 -O0 is excluded) are
suite.py's. A goosecc result is one of: pass, fail (wrong output, crash,
timeout, link error), error (goosecc exited non-zero or crashed on some
file; the first line of its message is recorded).

usage: tests/suite_goosecc.py [--goosecc PATH] [--corpus a,b] [--variants O0,g] [-j 3]
                              [--work DIR] [--report FILE] [--json FILE] [--rebaseline] [filter ...]
"""
import argparse
import concurrent.futures as cf
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
import suite  # noqa: E402

VARIANTS = ["O0", "g", "O1"]   # O1 (milestone E1): goosecc -O1, the tests that also pass with clang -O1


def build_goosecc(t, wd, variant, args, info):
    exe = os.path.join(wd, "gcc_" + variant + ".exe")
    objs = []
    for i, s in enumerate(t.srcs):
        o = os.path.join(wd, suite.obj_name(s, i) + "." + variant + ".gc.o")
        cmd = ([args.goosecc, "-c", "-O1" if variant == "O1" else "-O0"] + (["-g"] if variant == "g" else [])
               + t.flags(s) + [s, "-o", o])
        r = suite.sh(cmd, timeout=600)
        err = r.stderr.decode(errors="replace")
        if r.returncode != 0:
            lines = [ln for ln in err.strip().splitlines() if "note: ignoring" not in ln]
            first = lines[0] if lines else f"exit {r.returncode}"
            raise suite.Fail("error", f"goosecc exit {r.returncode} on {os.path.basename(s)}: {first[:300]}")
        objs.append(o)
    r = suite.sh([suite.linker(t, args)] + objs + t.ldflags + ["-o", exe])
    if r.returncode:
        raise suite.Fail("fail", f"link failed:\n{r.stderr.decode(errors='replace')[-800:]}")
    return exe


def do_test(t, args, baseline_cache):
    wd = os.path.join(args.work, t.corpus, t.name.replace("/", "__"))
    os.makedirs(wd, exist_ok=True)
    res = {"id": t.id}
    key = t.key()
    b = baseline_cache.get(t.id)
    if b is None or b.get("key") != key or args.rebaseline:
        try:
            exe = suite.build_baseline(t, wd, args)
            dt = suite.run_and_verify(t, exe, wd, args, timeout=t.timeout or 120)
            b = {"key": key, "status": "pass", "time": dt}
        except suite.Fail as e:
            b = {"key": key, "status": "build" if e.kind == "build" else "fail", "msg": e.msg[:2000]}
        except Exception as e:  # noqa
            b = {"key": key, "status": "fail", "msg": f"harness: {e}"}
    res["baseline"] = b
    if b["status"] != "pass":
        return res
    tmo = max(60.0, 20 * b["time"]) if t.timeout is None else max(t.timeout, 20 * b["time"])
    b1 = None
    if "O1" in args.variants:
        ck, b1 = suite.baseline_at(t, wd, args, baseline_cache, "O1")
        res["baseline_O1"] = b1
        res["baseline_O1_key"] = ck
    for v in args.variants:
        info = {}
        if v == "O1" and b1["status"] != "pass":
            res[v] = {"status": "excluded"}
            continue
        try:
            exe = build_goosecc(t, wd, v, args, info)
            info["time"] = suite.run_and_verify(t, exe, wd, args, timeout=tmo)
            info["status"] = "pass"
        except suite.Fail as e:
            info["status"] = e.kind if e.kind == "error" else "fail"
            info["msg"] = e.msg[:3000]
        except Exception as e:  # noqa
            info["status"] = "error"
            info["msg"] = f"harness: {e}"
        res[v] = info
    if not args.keep and all(res.get(v, {}).get("status") in ("pass", "excluded") for v in args.variants):
        for f in os.listdir(wd):
            p = os.path.join(wd, f)
            if f != "run" and os.path.isfile(p) and not f.endswith(".base.o"):
                os.unlink(p)
    return res


def report(results, tests, args):
    by = {}
    for t in tests:
        by.setdefault(t.corpus, []).append(results[t.id])
    lines = ["# goosecc correctness report", ""]
    lines.append(f"goosecc: `{args.goosecc}`; variants: {', '.join(args.variants)}")
    lines.append("")
    hdr = "| corpus | tests | clang -O0 pass | excluded |"
    sep = "|---|---:|---:|---:|"
    for v in args.variants:
        hdr += f" {v} pass | {v} fail | {v} error |"
        sep += "---:|---:|---:|"
    lines += [hdr, sep]
    for c in suite.CORPORA:
        if c not in by:
            continue
        rs = by[c]
        bp = [r for r in rs if r.get("baseline", {}).get("status") == "pass"]
        row = f"| {c} | {len(rs)} | {len(bp)} | {len(rs) - len(bp)} |"
        for v in args.variants:
            st = [r.get(v, {}).get("status") for r in bp]
            ex = f" (of {len(st) - st.count('excluded')})" if v == "O1" else ""
            row += f" {st.count('pass')}{ex} | {st.count('fail')} | {st.count('error')} |"
        lines.append(row)
    lines.append("")
    for c in suite.CORPORA:
        if c not in by:
            continue
        bad = []
        for r in by[c]:
            if r.get("baseline", {}).get("status") != "pass":
                continue
            for v in args.variants:
                s = r.get(v, {}).get("status")
                if s not in ("pass", "excluded", None):
                    msg = r[v].get("msg", "")
                    bad.append(f"- `{r['id']}` [{v}] {s}: {msg.splitlines()[0][:200] if msg else ''}")
        if bad:
            lines.append(f"## {c}: not passing")
            lines.append("")
            lines += bad
            lines.append("")
        excl = [r for r in by[c] if r.get("baseline", {}).get("status") != "pass"]
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
    ap.add_argument("--goosecc", default=os.environ.get("GOOSECC", os.path.join(ROOT, "frontend-goose/build/goosecc")))
    ap.add_argument("--suite", default="/home/user/llvm/llvm-test-suite")
    ap.add_argument("--corpus", default=",".join(suite.CORPORA))
    ap.add_argument("--variants", default="O0")
    ap.add_argument("--clang", default="clang-20")
    ap.add_argument("--clangxx", default="clang++-20")
    ap.add_argument("-j", type=int, default=3)
    ap.add_argument("--work", default=os.path.join(ROOT, "build-suite-goosecc"))
    ap.add_argument("--keep", action="store_true", help="keep build products of passing tests")
    ap.add_argument("--rebaseline", action="store_true", help="recompute the clang -O0 baseline")
    ap.add_argument("--report", default="")
    ap.add_argument("--json", default="")
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("filter", nargs="*", help="substrings of test ids to run")
    args = ap.parse_args()
    args.variants = [v for v in args.variants.split(",") if v]
    for v in args.variants:
        if v not in VARIANTS:
            sys.exit(f"unknown variant {v}")
    corpora = [c for c in args.corpus.split(",") if c]
    os.makedirs(args.work, exist_ok=True)
    args.work = os.path.abspath(args.work)
    args.goosecc = os.path.abspath(args.goosecc)
    if not os.path.exists(args.goosecc):
        sys.exit(f"goosecc not found at {args.goosecc} (use --goosecc or GOOSECC)")
    args.fpcmp = os.path.join(args.work, "fpcmp")
    if not os.path.exists(args.fpcmp):
        r = suite.sh([args.clang, "-O2", "-w", os.path.join(args.suite, "tools/fpcmp.c"), "-o", args.fpcmp])
        if r.returncode:
            sys.exit("cannot build fpcmp: " + r.stderr.decode())
    tests = suite.all_tests(args.suite, corpora)
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
            if (bad or r.get("baseline", {}).get("status") not in ("pass", None)) and not args.quiet:
                msg = ""
                for v in args.variants:
                    if v in r and r[v]["status"] not in ("pass", "excluded"):
                        msg = r[v].get("msg", "").splitlines()[0][:150] if r[v].get("msg") else ""
                        break
                print(f"[{done}/{len(tests)}] {t.id}: baseline={r.get('baseline', {}).get('status')} {' '.join(st)} {msg}",
                      flush=True)
            elif done % 100 == 0:
                print(f"[{done}/{len(tests)}] {time.time() - t0:.0f}s", flush=True)
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
