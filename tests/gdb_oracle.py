#!/usr/bin/env python3
"""Debugger oracle: the same gdb session on a clang -O0 -g build and a goovm
build of a program, compared.

For every program, two builds:
  ref      clang -O0 -g (the oracle)
  goovm    clang -O0 -g -emit-llvm -> goovm-llc (or goovm-cc with --cc)
and one scripted gdb session per build (batch mode, gdb's Python API):
breakpoints on the program's functions and on a sample of the statement
lines of the reference line table; at each stop (at most 3 per breakpoint,
--stops in all) `bt`, `info args`, `info locals`, two `next` with the
locals, a `step` with the frame, then `continue`. The
values of variables that are not initialized yet depend on what the stack
held, which differs between the two builds; so on entry to each of the
program's functions (the first instruction, an internal breakpoint) the
script fills the 8 KB below the stack pointer with one byte pattern, and an
uninitialized local reads the same in both builds. The transcripts are
normalized (addresses, pids, directories) and compared line by line.

With --unwind, the goovm build alone is checked instead: for each of the
program's functions (its first --unwind-calls activations), the session
breaks on the function's first instruction and single-steps it (`stepi`,
`nexti` over calls) until it has returned, checking at every instruction
boundary - the prologue's pushes, the body, the epilogue's pops and `ret` -
that the backtrace is the function over the same callers as on entry.

usage: tests/gdb_oracle.py [--goovm PATH | --cc PATH] [-j 3] [--work DIR] [--stops N]
                           [--corpus c,sample] [--unwind] [--keep] [filter ...]
Corpora: c (tests/c/*.c), sample (a sample of llvm-test-suite programs, C and C++).
Exit status 0 iff every transcript matches.
"""
import argparse
import concurrent.futures as cf
import difflib
import json
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
SUITE = "/home/user/llvm/llvm-test-suite"

GDB_SCRIPT = r'''
import gdb, json
cfg = json.load(open(CFG))
out = open(cfg["out"], "w")
def ex(c):
    try:
        return gdb.execute(c, to_string=True)
    except gdb.error as e:
        return "gdb.error: " + str(e) + "\n"
for c in ["set pagination off", "set confirm off", "set width 0", "set height 0", "set print address off",
          "set print symbol off", "set breakpoint pending on", "set disable-randomization on",
          "set print frame-arguments scalars", "set print entry-values no", "set step-mode off"]:
    ex(c)
bps = []
for loc in cfg["locs"]:
    try:
        bps.append(gdb.Breakpoint(loc, internal=False))
    except gdb.error:
        pass
def alive():
    try:
        return gdb.selected_inferior().pid != 0 and gdb.selected_thread() is not None
    except gdb.error:
        return False
def stopped_in_code():
    try:
        gdb.selected_frame()
        return True
    except gdb.error:
        return False
PAT = bytes([0xA5]) * 8192
npoison = [0]
class Poison(gdb.Breakpoint):
    def stop(self):
        npoison[0] += 1
        if npoison[0] > cfg["poison_cap"]:
            self.enabled = False
            return False
        sp = int(gdb.parse_and_eval("$rsp"))
        n = len(PAT)
        while n >= 512:
            try:
                gdb.selected_inferior().write_memory(sp - n, PAT[:n])
                break
            except gdb.MemoryError:
                n //= 2
        return False
for f in cfg["funcs"]:
    try:
        Poison("*" + f, internal=True)
    except gdb.error:
        pass
out.write(ex("run " + " ".join(cfg["args"])))
stops = 0
while stops < cfg["stops"] and alive() and stopped_in_code():
    stops += 1
    out.write("=== stop %d\n" % stops)
    out.write(ex("bt"))
    out.write(ex("info args"))
    out.write(ex("info locals"))
    for i in range(2):
        out.write("--- next\n" + ex("next"))
        if not (alive() and stopped_in_code()):
            break
        out.write(ex("frame"))
        out.write(ex("info locals"))
    if alive() and stopped_in_code():
        out.write("--- step\n" + ex("step"))
        if alive() and stopped_in_code():
            out.write(ex("bt 2"))
            # (no `finish`: it stops at the call's return address, which may
            # start the next statement in one build and not in the other -
            # clang reserves the outgoing argument area in the prologue,
            # goovm pops it after the call - and that decides whether the
            # `continue` below stops at a breakpoint there)
    for b in bps:
        if b.is_valid() and b.hit_count >= 3 and b.enabled:
            b.enabled = False
    if not any(b.is_valid() and b.enabled for b in bps):
        break
    if alive() and stopped_in_code():
        out.write("--- continue\n" + ex("continue"))
out.write("=== end after %d stops\n" % stops)
out.close()
ex("kill")
'''


UNWIND_SCRIPT = r'''
import gdb, json
cfg = json.load(open(CFG))
out = open(cfg["out"], "w")
for c in ["set pagination off", "set confirm off", "set width 0", "set breakpoint pending on",
          "set disable-randomization on"]:
    gdb.execute(c, to_string=True)
def chain():
    names = []
    f = gdb.newest_frame()
    while f is not None and len(names) < 64:
        names.append(f.name() or "??")
        if f.name() == "main":
            break
        f = f.older()
    return names
checked = 0
bad = 0
steps = 0
bps = {}
for fn in cfg["funcs"]:
    try:
        bps[fn] = gdb.Breakpoint("*" + fn, internal=True)
    except gdb.error:
        pass
try:
    gdb.execute("run " + " ".join(cfg["args"]), to_string=True)
except gdb.error:
    pass
def returned(c, entry):
    callers = entry[1:]
    if entry[0] == "main":
        return "main" not in c
    return c == callers or (len(c) == len(callers) and c[1:] == callers[1:])
while checked < cfg["max_checks"] and steps < cfg["max_steps"]:
    try:
        gdb.selected_frame()
    except gdb.error:
        break
    for b in bps.values():
        if b.is_valid() and b.enabled and b.hit_count >= cfg["calls"]:
            b.enabled = False
    stack = [(chain(), 0)]
    checked += 1
    while stack and steps < cfg["max_steps"]:
        entry, n = stack[-1]
        if n >= 20000:
            stack.pop()
            continue
        insn = gdb.execute("x/i $pc", to_string=True)
        try:
            if "call" in insn.split(":", 1)[-1]:
                gdb.execute("nexti", to_string=True)
            else:
                gdb.execute("stepi", to_string=True)
        except gdb.error:
            stack = []
            break
        steps += 1
        stack[-1] = (entry, n + 1)
        try:
            c = chain()
        except gdb.error:
            stack = []
            break
        if c == entry:
            continue
        if returned(c, entry):
            stack.pop()
            continue
        if len(c) > len(entry) and c[-len(entry):] == entry:
            # nexti stopped at a breakpoint in a callee: check it too
            for b in bps.values():
                if b.is_valid() and b.enabled and b.hit_count >= cfg["calls"]:
                    b.enabled = False
            stack.append((c, 0))
            checked += 1
            continue
        out.write("MISMATCH in %s after %d instructions: %s / entry %s\n" % (entry[0], n + 1, c, entry))
        out.write(insn)
        bad += 1
        stack.pop()
    try:
        gdb.execute("continue", to_string=True)
    except gdb.error:
        break
out.write("checked %d activations, %d instructions, %d mismatches\n" % (checked, steps, bad))
out.close()
try:
    gdb.execute("kill", to_string=True)
except gdb.error:
    pass
'''


def sh(cmd, timeout=600, **kw):
    try:
        return subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout, **kw)
    except subprocess.TimeoutExpired:
        return subprocess.CompletedProcess(cmd, -999, b"", b"timeout")


class Prog:
    def __init__(self, name, srcs, cflags=(), ldflags=(), args=(), rundir=None):
        self.name = name
        self.srcs = list(srcs)
        self.cflags = list(cflags)
        self.ldflags = list(ldflags)
        self.args = list(args)
        self.rundir = rundir

    @property
    def cxx(self):
        return any(s.endswith((".cpp", ".cc")) for s in self.srcs)


def programs(corpora):
    out = []
    if "c" in corpora:
        for f in sorted(os.listdir(os.path.join(HERE, "c"))):
            if f.endswith(".c"):
                out.append(Prog("c/" + f[:-2], [os.path.join(HERE, "c", f)], ["-w"], ["-lm"]))
    if "sample" in corpora:
        S = SUITE + "/SingleSource"
        j = os.path.join
        for d, fs, fl in [
            ("Benchmarks/Stanford", ["Bubblesort.c", "Queens.c", "Towers.c", "Treesort.c", "Perm.c", "Puzzle.c"], []),
            ("Benchmarks/Shootout", ["ackermann.c", "lists.c", "matrix.c", "objinst.c", "sieve.c", "hash.c"], []),
            ("Benchmarks/McGill", ["queens.c", "exptree.c"], []),
            ("Benchmarks/Misc", ["evalloop.c", "richards_benchmark.c", "fbench.c", "perlin.c"], ["-Wno-implicit-int"]),
            ("UnitTests", ["2003-05-07-VarArgs.c", "2003-09-18-BitFieldTest.c", "2005-05-12-Int64ToFP.c",
                           "2006-01-23-UnionInit.c", "2009-04-16-BitfieldInitialization.c", "2002-10-12-StructureArgs.c"],
             ["-w"]),
            ("Benchmarks/Shootout-C++", ["ackermann.cpp", "ary3.cpp", "hash.cpp", "lists.cpp", "methcall.cpp",
                                         "objinst.cpp", "sieve.cpp", "wc.cpp"], ["-Wno-deprecated"]),
            ("Benchmarks/Shootout-C++/EH", ["except.cpp"], []),
            ("Regression/C++/EH", ["class_hierarchy.cpp", "function_try_block.cpp", "simple_rethrow.cpp",
                                   "ctor_dtor_count.cpp", "exception_spec_test.cpp"], ["-std=gnu++14"]),
            ("Regression/C++", ["2003-06-08-VirtualFunctions.cpp", "pointer_method.cpp", "global_ctor.cpp",
                                "short_circuit_dtor.cpp"], []),
            ("Benchmarks/Misc-C++", ["bigfib.cpp", "mandel-text.cpp"], []),
        ]:
            for f in fs:
                p = j(S, d, f)
                if os.path.exists(p):
                    out.append(Prog("sample/" + d + "/" + os.path.splitext(f)[0], [p], fl, ["-lm"]))
    return out


def compile_ref(p, wd, extra, args, tag):
    exe = os.path.join(wd, tag + ".exe")
    objs = []
    for i, s in enumerate(p.srcs):
        cc = args.clangxx if s.endswith((".cpp", ".cc")) else args.clang
        o = os.path.join(wd, f"{tag}{i}.o")
        r = sh([cc, "-O0", "-g"] + extra + p.cflags + ["-c", s, "-o", o])
        if r.returncode:
            raise RuntimeError(f"{tag}: {r.stderr.decode(errors='replace')[-400:]}")
        objs.append(o)
    r = sh([args.clangxx if p.cxx else args.clang] + objs + p.ldflags + ["-o", exe])
    if r.returncode:
        raise RuntimeError(f"{tag} link: {r.stderr.decode(errors='replace')[-400:]}")
    return exe, objs


def compile_goovm(p, wd, args):
    exe = os.path.join(wd, "goovm.exe")
    objs = []
    for i, s in enumerate(p.srcs):
        cc = args.clangxx if s.endswith((".cpp", ".cc")) else args.clang
        o = os.path.join(wd, f"goovm{i}.o")
        if args.cc:
            r = sh([args.cc, "--backend=goose", "-O0", "-g"] + p.cflags + ["-c", s, "-o", o])
        else:
            bc = os.path.join(wd, f"goovm{i}.bc")
            r = sh([cc, "-O0", "-g"] + p.cflags + ["-c", "-emit-llvm", s, "-o", bc])
            if r.returncode == 0:
                r = sh([args.goovm, bc, "-o", o])
        if r.returncode:
            raise RuntimeError(f"goovm: {r.stderr.decode(errors='replace')[-400:]}")
        objs.append(o)
    r = sh([args.clangxx if p.cxx else args.clang] + objs + p.ldflags + ["-o", exe])
    if r.returncode:
        raise RuntimeError(f"goovm link: {r.stderr.decode(errors='replace')[-400:]}")
    return exe


def breakpoints(p, ref_objs, nlines):
    """Function breakpoints (file:function) and a sample of statement lines of the reference line table;
    the functions (for the stack poisoning)."""
    locs = []
    lines = []
    funcs = []
    for s, o in zip(p.srcs, ref_objs):
        base = os.path.basename(s)
        info = sh(["llvm-dwarfdump-20", "--debug-info", o]).stdout.decode(errors="replace")
        # subprograms defined in this file (they have a low_pc)
        for m in re.finditer(r"DW_TAG_subprogram\n((?:\s+DW_AT_.*\n)+)", info):
            body = m.group(1)
            if "DW_AT_low_pc" not in body:
                continue
            nm = re.search(r'DW_AT_name\s+\("([^"]+)"\)', body)
            df = re.search(r'DW_AT_decl_file\s+\("([^"]+)"\)', body)
            if not nm or (df and os.path.basename(df.group(1)) != base):
                continue
            n = nm.group(1)
            ln = re.search(r'DW_AT_linkage_name\s+\("([^"]+)"\)', body)
            funcs.append(ln.group(1) if ln else n)
            if re.match(r"^[A-Za-z_]\w*$", n):
                locs.append(f"{base}:{n}")
        tab = sh(["llvm-dwarfdump-20", "--debug-line", o]).stdout.decode(errors="replace")
        cur = None
        for l in tab.splitlines():
            m = re.match(r"file_names\[\s*(\d+)\]:", l)
            m2 = re.match(r"0x[0-9a-f]+\s+(\d+)\s+(\d+)\s+(\d+)\s.*is_stmt", l)
            if m2 and int(m2.group(1)) > 0:
                lines.append((base, int(m2.group(1))))
    seen = set()
    uniq = []
    for x in lines:
        if x not in seen:
            seen.add(x)
            uniq.append(x)
    if uniq:
        step = max(1, len(uniq) // max(1, nlines))
        locs += [f"{b}:{ln}" for b, ln in uniq[::step][:nlines]] if nlines else []
    return locs[:60], funcs


def run_gdb(exe, locs, funcs, p, wd, tag, args):
    out = os.path.join(wd, tag + ".gdb.txt")
    cfgf = os.path.join(wd, tag + ".cfg.json")
    json.dump({"out": out, "locs": locs, "funcs": funcs, "args": p.args, "stops": args.stops,
               "poison_cap": args.poison_cap}, open(cfgf, "w"))
    scr = os.path.join(wd, tag + ".gdb.py")
    open(scr, "w").write(f"CFG = {cfgf!r}\n" + GDB_SCRIPT)
    r = sh(["gdb", "-nx", "-batch", "-x", scr, exe], timeout=600, cwd=p.rundir or wd,
           stdin=subprocess.DEVNULL)
    if not os.path.exists(out):
        raise RuntimeError(f"gdb ({tag}) wrote no transcript: {r.stderr.decode(errors='replace')[-400:]}")
    return normalize(open(out, errors="replace").read(), p)


def normalize(t, p):
    lines = []
    for l in t.splitlines():
        l = re.sub(r"0x[0-9a-f]+", "0xADDR", l)
        # glibc's __libc_start_call_main (after `next` out of main): its
        # jmp_buf holds stack addresses and mangled pointers, which depend on
        # the executable's name and the random pointer guard
        if l.startswith("unwind_buf = "):
            l = re.sub(r"-?\d+", "N", l)
        # stack addresses as values (the frames are laid out differently):
        # as integers (0x7ff000000000 .. 0x7fffffffffff, the stack without
        # ASLR) and as the bytes of a pointer in a char array
        l = re.sub(r"\b14\d{13}\b", lambda m: "STACK" if 0x7FF000000000 <= int(m.group(0)) < 0x800000000000
                   else m.group(0), l)
        l = re.sub(r'(\\\d{3}|[^\\"]){2}\\377\\377\\377\\177', "STACK", l)
        # how far uninitialized (poisoned) stack memory extends past a buffer
        # depends on the frame layout too
        l = re.sub(r"'\\245' <repeats \d+ times>", "'\\245' <repeats N times>", l)
        l = re.sub(r"process \d+", "process N", l)
        l = re.sub(r"Thread 0xADDR \(LWP \d+\)", "Thread", l)
        l = re.sub(r"\[Inferior 1 \(process N\) exited", "[Inferior exited", l)
        if l.startswith("[Thread debugging") or l.startswith("Using host libthread_db") or "Download" in l:
            continue
        l = re.sub(r"/[^\s:\"]*/", "", l)   # directory prefixes
        lines.append(l.rstrip())
    return lines


def compare(ref, got):
    bad = []
    sm = difflib.SequenceMatcher(None, ref, got, autojunk=False)
    for op, a0, a1, b0, b1 in sm.get_opcodes():
        if op != "equal":
            bad.append((op, ref[a0:a1], got[b0:b1]))
    return bad


def unwind_test(p, args):
    wd = os.path.join(args.work, p.name.replace("/", "__"))
    os.makedirs(wd, exist_ok=True)
    try:
        goo = compile_goovm(p, wd, args)
        _, ref_objs = compile_ref(p, wd, [], args, "ref")
    except RuntimeError as e:
        return p.name, "error", str(e), 0
    _, funcs = breakpoints(p, ref_objs, 0)
    out = os.path.join(wd, "unwind.txt")
    cfgf = os.path.join(wd, "unwind.json")
    json.dump({"out": out, "funcs": funcs, "args": p.args, "calls": args.unwind_calls,
               "max_checks": 400, "max_steps": 200000}, open(cfgf, "w"))
    scr = os.path.join(wd, "unwind.py")
    open(scr, "w").write(f"CFG = {cfgf!r}\n" + UNWIND_SCRIPT)
    sh(["gdb", "-nx", "-batch", "-x", scr, goo], timeout=1200, cwd=p.rundir or wd, stdin=subprocess.DEVNULL)
    if not os.path.exists(out):
        return p.name, "error", "no unwind transcript", 0
    t = open(out).read().strip().splitlines()
    last = t[-1] if t else ""
    m = re.match(r"checked (\d+) activations, (\d+) instructions, (\d+) mismatches", last)
    if not m:
        return p.name, "error", last, 0
    if int(m.group(3)):
        return p.name, "diff", "\n".join(t[:6]), int(m.group(2))
    return p.name, "same", last, int(m.group(2))


def test(p, args):
    if args.unwind:
        return unwind_test(p, args)
    wd = os.path.join(args.work, p.name.replace("/", "__"))
    os.makedirs(wd, exist_ok=True)
    try:
        ref, ref_objs = compile_ref(p, wd, [], args, "ref")
        goo = compile_goovm(p, wd, args)
    except RuntimeError as e:
        return p.name, "error", str(e), 0
    locs, funcs = breakpoints(p, ref_objs, args.lines)
    try:
        tr = run_gdb(ref, locs, funcs, p, wd, "ref", args)
        tg = run_gdb(goo, locs, funcs, p, wd, "goovm", args)
    except RuntimeError as e:
        return p.name, "error", str(e), 0
    bad = compare(tr, tg)
    nstops = sum(1 for l in tr if l.startswith("=== stop"))
    if bad:
        msg = []
        for op, a, b in bad[:3]:
            msg.append(f"  {op}: clang {a[:4]}\n          goovm {b[:4]}")
        return p.name, "diff", f"{len(bad)} differing blocks\n" + "\n".join(msg), nstops
    if not args.keep:
        for f in os.listdir(wd):
            if f.endswith((".o", ".bc", ".exe")):
                os.unlink(os.path.join(wd, f))
    return p.name, "same", f"{len(tr)} lines", nstops


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goovm", default=os.path.join(ROOT, "build/tools/goovm-llc/goovm-llc"))
    ap.add_argument("--cc", default="", help="use goovm-cc for the goovm build")
    ap.add_argument("--clang", default="clang-20")
    ap.add_argument("--clangxx", default="clang++-20")
    ap.add_argument("-j", type=int, default=3)
    ap.add_argument("--work", default="/tmp/gdb-oracle")
    ap.add_argument("--stops", type=int, default=80)
    ap.add_argument("--lines", type=int, default=25)
    ap.add_argument("--poison-cap", type=int, default=200000,
                    help="stop filling the stack after this many function entries")
    ap.add_argument("--corpus", default="c,sample")
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--unwind", action="store_true", help="single-step the goovm build's functions, checking bt")
    ap.add_argument("--unwind-calls", type=int, default=2)
    ap.add_argument("--json", default="")
    ap.add_argument("filter", nargs="*")
    args = ap.parse_args()
    progs = programs(args.corpus.split(","))
    if args.filter:
        progs = [p for p in progs if any(f in p.name for f in args.filter)]
    os.makedirs(args.work, exist_ok=True)
    res = []
    with cf.ThreadPoolExecutor(max_workers=args.j) as ex:
        for name, st, msg, n in ex.map(lambda p: test(p, args), progs):
            res.append((name, st, msg, n))
            print(f"{name:55s} {st:5s} stops={n:3d} {msg if st != 'same' else msg}", flush=True)
    same = sum(1 for r in res if r[1] == "same")
    what = "instructions" if args.unwind else "stops"
    print(f"\n{same}/{len(res)} {'programs unwind correctly' if args.unwind else 'transcripts match'} "
          f"({sum(r[3] for r in res)} {what})")
    if args.json:
        json.dump(res, open(args.json, "w"), indent=1)
    sys.exit(0 if same == len(res) else 1)


if __name__ == "__main__":
    main()
