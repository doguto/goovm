#!/usr/bin/env python3
"""The clang Sema test oracle: clang/test/{SemaCXX,SemaTemplate,CXX,Parser}/**/*.cpp
with `-verify` RUN lines. For each file and RUN configuration (its -std), the
lines clang's expected-error annotations name are compared with the lines
goosecc -fsyntax-only reports errors on (in the test file itself).

A file passes when the two sets are equal. Also counted: false errors (lines
goosecc reports but clang does not expect: goosecc rejects valid code) and
missed errors (expected lines goosecc accepts: false acceptance).

usage: frontend-goose/tests/sema_oracle.py --root <llvm-project>/clang/test [-j 4] [--goosecc G] [--filter substr] [--save results.json] [--show N]
                      [--compare old.json]
"""
import argparse, concurrent.futures as cf, json, os, re, subprocess, sys, collections

ROOT = os.environ.get("CLANG_TEST_ROOT", "")     # clang/test of the llvm-project sources (clang 20.1.2)
DIRS = ["SemaCXX", "SemaTemplate", "CXX", "Parser"]
ap = argparse.ArgumentParser()
ap.add_argument("-j", type=int, default=4)
ap.add_argument("--goosecc", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "build", "goosecc"))
ap.add_argument("--root", default=ROOT)
ap.add_argument("--filter", default="")
ap.add_argument("--save", default="")
ap.add_argument("--compare", default="")
ap.add_argument("--show", type=int, default=0)
ap.add_argument("--timeout", type=int, default=20)
a = ap.parse_args()
ROOT = a.root
if not ROOT: sys.exit("set CLANG_TEST_ROOT or --root to clang/test")

def files():
    out = []
    for d in DIRS:
        for dp, dn, fn in os.walk(os.path.join(ROOT, d)):
            for f in fn:
                if f.endswith(".cpp"):
                    p = os.path.join(dp, f)
                    if a.filter in p:
                        out.append(p)
    return sorted(out)

RUN = re.compile(r"//\s*RUN:(.*)")
def run_configs(text):
    """The -std of each `%clang_cc1 ... -verify` RUN line (plain -verify only)."""
    lines = text.splitlines()
    runs = []
    cur = ""
    for l in lines:
        m = RUN.search(l)
        if not m:
            if cur: runs.append(cur); cur = ""
            continue
        part = m.group(1).strip()
        if part.endswith("\\"):
            cur += part[:-1] + " "
            continue
        cur += part
        runs.append(cur); cur = ""
    if cur: runs.append(cur)
    out = []
    for r in runs:
        if "%clang_cc1" not in r or "-verify" not in r: continue
        if "-fsyntax-only" not in r and "-emit" in r: continue
        if re.search(r"-verify=", r): continue
        if "not " in r.split("%clang_cc1")[0]: continue
        tr = re.search(r"-triple[ =](\S+)", r)
        if tr and not tr.group(1).startswith("x86_64") and "%itanium_abi_triple" not in tr.group(1):
            continue
        if re.search(r"-x\s+(c|objective-c\+?\+?|cuda|hip)\b", r) or "-fms-compatibility" in r or "-fcuda" in r or "-fopenmp" in r or "-fsycl" in r:
            continue
        m = re.search(r"-std=(\S+)", r)
        std = m.group(1) if m else "c++17"
        defs = re.findall(r"(-D\s*\S+)", r)
        flags = ["-std=" + std] + [d.replace(" ", "") for d in defs]
        for f in ["-fms-extensions", "-fblocks", "-fenable-matrix", "-fcoroutines", "-fno-rtti", "-fno-exceptions", "-fexceptions", "-fcxx-exceptions", "-fchar8_t", "-fno-char8_t"]:
            if f in r.split(): flags.append(f)
        key = " ".join(flags)
        if key not in [" ".join(x) for x in out]:
            out.append(flags)
    return out

EXP = re.compile(r"expected-(error|warning|note|remark|no-diagnostics)(@[^\s{]*)?(\s+\d+)?(\s+\d+-\d+)?\s*(\{\{|$)")
def expected_lines(text):
    """Line numbers (1-based) with expected errors."""
    out = collections.Counter()
    lines = text.splitlines()
    for i, l in enumerate(lines):
        for m in EXP.finditer(l):
            if m.group(1) != "error": continue
            ln = i + 1
            at = m.group(2)
            if at:
                at = at[1:]
                if at.startswith("+") or at.startswith("-"):
                    try: ln = ln + int(at)
                    except ValueError: continue
                elif at.isdigit():
                    ln = int(at)
                else:
                    continue    # a marker (@#name) or another file: not counted
            out[ln] += 1
    return set(out)

ERR = re.compile(r"^(.*?):(\d+):(\d+): error: ")
def run_one(job):
    p, flags = job
    env = dict(os.environ, GOOSECC_CACHE="off")
    try:
        r = subprocess.run([a.goosecc, "-fsyntax-only", "-x", "c++"] + flags + [p], capture_output=True, env=env, timeout=a.timeout)
        err = r.stderr.decode("utf-8", "replace")
        rc = r.returncode
    except subprocess.TimeoutExpired:
        return p, flags, "timeout", set(), ""
    got = set()
    first = ""
    global msgs
    for l in err.splitlines():
        m = ERR.match(l)
        if m:
            if os.path.abspath(m.group(1)) == os.path.abspath(p):
                got.add(int(m.group(2)))
                msgs.setdefault((p, " ".join(flags)), {}).setdefault(int(m.group(2)), l[m.end():][:120])
            if not first: first = l
    if rc < 0 or rc > 1:
        return p, flags, "crash", got, err.strip().splitlines()[-1] if err.strip() else ""
    return p, flags, "ran", got, first

msgs = {}
jobs = []
exp = {}
for p in files():
    t = open(p, encoding="utf-8", errors="replace").read()
    for flags in run_configs(t):
        jobs.append((p, flags))
    exp[p] = expected_lines(t)

with cf.ThreadPoolExecutor(a.j) as ex:
    res = list(ex.map(run_one, jobs))

stats = collections.Counter()
per = {}
for p, flags, st, got, first in res:
    e = exp[p]
    key = p[len(ROOT) + 1:] + " " + " ".join(flags)
    fp = sorted(got - e)
    fn = sorted(e - got)
    ok = st == "ran" and not fp and not fn
    mm = msgs.get((p, " ".join(flags)), {})
    per[key] = {"st": st, "fp": fp, "fn": fn, "exp": len(e), "first": first, "fpmsg": [mm.get(x, "") for x in fp]}
    stats["runs"] += 1
    stats["pass"] += ok
    stats[st] += 1
    stats["exp_lines"] += len(e)
    stats["hit_lines"] += len(e & got)
    stats["fp_lines"] += len(fp)
    stats["fn_lines"] += len(fn)
    if not e: stats["valid_runs"] += 1; stats["valid_ok"] += (st == "ran" and not got)
    if fp: stats["runs_with_false_errors"] += 1

d = sys.argv[0]
print("clang Sema tests (%s): %d files, %d runs" % (", ".join(DIRS), len(exp), stats["runs"]))
print("  pass (error lines equal): %d / %d = %.1f%%" % (stats["pass"], stats["runs"], 100.0 * stats["pass"] / max(1, stats["runs"])))
print("  expected-error lines: %d, reported: %d (%.1f%%), missed (false acceptance): %d" % (stats["exp_lines"], stats["hit_lines"], 100.0 * stats["hit_lines"] / max(1, stats["exp_lines"]), stats["fn_lines"]))
print("  false-error lines: %d in %d runs" % (stats["fp_lines"], stats["runs_with_false_errors"]))
print("  runs expecting no errors: %d, accepted cleanly: %d" % (stats["valid_runs"], stats["valid_ok"]))
print("  crashes: %d, timeouts: %d" % (stats["crash"], stats["timeout"]))
fpm = collections.Counter()
for k, v in per.items():
    for m in v["fpmsg"]:
        fpm[re.sub(r"'[^']*'", "'X'", m)] += 1
print("  top false-error messages:")
for m, c in fpm.most_common(40): print("    %5d %s" % (c, m))
if a.save:
    json.dump({"stats": stats, "per": per}, open(a.save, "w"), indent=0)
if a.compare:
    old = json.load(open(a.compare))["per"]
    better = [k for k in per if k in old and per[k]["st"] == "ran" and not per[k]["fp"] and not per[k]["fn"] and (old[k]["fp"] or old[k]["fn"] or old[k]["st"] != "ran")]
    worse = [k for k in per if k in old and (per[k]["fp"] or per[k]["fn"] or per[k]["st"] != "ran") and not old[k]["fp"] and not old[k]["fn"] and old[k]["st"] == "ran"]
    newfp = [k for k in per if k in old and len(per[k]["fp"]) > len(old[k]["fp"])]
    print("  vs %s: %d newly passing, %d newly failing, %d with more false errors" % (a.compare, len(better), len(worse), len(newfp)))
    for k in worse[:a.show or 20]: print("    worse:", k, per[k]["fp"][:5], per[k]["fn"][:5], per[k]["first"][:150])
if a.show:
    crashes = [k for k in per if per[k]["st"] in ("crash", "timeout")]
    for k in crashes[:a.show]: print("  crash:", k, per[k]["first"][:200])
    fps = sorted([k for k in per if per[k]["fp"]], key=lambda k: -len(per[k]["fp"]))
    for k in fps[:a.show]: print("  false errors:", k, per[k]["fp"][:8], per[k]["first"][:150])
