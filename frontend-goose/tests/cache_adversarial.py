#!/usr/bin/env python3
"""Adversarial tests of goosecc's header cache (B4): situations where a
replay could go wrong. In each, every compile with the cache must give
what the same compile gives without it (-fno-header-cache): the same -E
output, object (with -g) and --pp-state-hash; and the cache must behave as
expected (a hit where nothing changed, a miss where something did).

usage: tests/cache_adversarial.py [--goosecc build/goosecc] [-v] [test ...]
"""
import argparse, os, re, shutil, subprocess, sys, tempfile, threading, time, random, concurrent.futures as cf

HERE = os.path.dirname(os.path.abspath(__file__))
STATS = re.compile(r"header cache: (\d+) lookups, (\d+) hits, (\d+) misses; (\d+) recorded[^;]*?, (\d+) too small, (\d+) not cacheable, (\d+) corrupt")
RACY = 2.2      # seconds a new file must age before a recording trusts its stat


class T:
    def __init__(self, a, name):
        self.a, self.name = a, name
        self.dir = tempfile.mkdtemp(prefix=f"hcadv_{name}_")
        self.cache = os.path.join(self.dir, "cache")
        self.fails = []
        self.checks = 0

    def path(self, p):
        return os.path.join(self.dir, p)

    def write(self, p, text):
        full = self.path(p)
        os.makedirs(os.path.dirname(full), exist_ok=True)
        with open(full, "w") as f:
            f.write(text)
        return full

    def run(self, args, cache=True, cwd=None, env_extra=None, obj=None):
        """goosecc args (with -E or -c), with or without the cache: (status, stdout, stderr, object, stats)"""
        # "..." includes are units at every compile here (the default makes
        # them units from a translation unit's second compile on: t_policy)
        env = dict(os.environ, SOURCE_DATE_EPOCH="1700000000", TZ="UTC", GOOSECC_CACHE=self.cache, GOOSECC_CACHE_QUOTED="1")
        if env_extra:
            env.update(env_extra)
        obj = obj or self.path("out.o")
        cmd = [self.a.goosecc, "--pp-state-hash=v"] + (["--cache-stats"] if cache else ["-fno-header-cache"]) + args
        if "-c" in args:
            cmd += ["-o", obj]
        r = subprocess.run(cmd, capture_output=True, cwd=cwd or self.dir, env=env)
        data = b""
        if os.path.exists(obj):
            data = open(obj, "rb").read()
            os.unlink(obj)
        err = r.stderr.decode(errors="replace")
        m = STATS.search(err)
        st = dict(zip(["lookups", "hits", "misses", "recorded", "small", "bad", "corrupt"], map(int, m.groups()))) if m else None
        err = re.sub(r"goosecc: header cache:[^\n]*\n", "", err)
        return (r.returncode, r.stdout, err, data), st

    def same(self, args, what="", cwd=None, env_extra=None, expect=None):
        """compile with and without the cache; check equality and the expected stats"""
        got, st = self.run(args, True, cwd, env_extra)
        ref, _ = self.run(args, False, cwd, env_extra)
        self.checks += 1
        if got != ref:
            diff = [n for n, x, y in zip(("status", "stdout", "stderr", "object"), got, ref) if x != y]
            self.fails.append(f"{what}: differs from -fno-header-cache in {diff}")
            if self.a.v:
                print("   cache stderr:", got[2][:400], "\n   off stderr:", ref[2][:400])
        if expect and st:
            for k, v in expect.items():
                ok = v(st[k]) if callable(v) else st[k] == v
                if not ok:
                    self.fails.append(f"{what}: expected {k} {v if not callable(v) else '(cond)'}, got {st}")
        elif expect and not st:
            self.fails.append(f"{what}: no cache statistics ({got[2][:200]})")
        if self.a.v:
            print(f"   {what}: {st}")
        return got, st

    def done(self):
        if not self.a.keep:
            shutil.rmtree(self.dir, ignore_errors=True)
        return self.fails


BIG = "".join(f"int filler_{i}(int x);  /* {'.' * 40} */\n" for i in range(150))   # makes a header worth an entry


def age():
    time.sleep(RACY)


# --- the tests -------------------------------------------------------------

def t_edit_same_size(a):
    """A header edited between compiles, same size, mtime restored (touch -d): the replay must not use the old text."""
    t = T(a, "edit")
    h = t.write("inc/h.h", "#define V 1\nint value_one;\n" + BIG)
    c = t.write("a.c", '#include "inc/h.h"\nint get(void) { return V; }\n')
    age()
    t.same(["-c", "-g", c], "first (records)", expect={"recorded": lambda x: x >= 1})
    t.same(["-c", "-g", c], "second (replays)", expect={"hits": 1})
    st0 = os.stat(h)
    t.write("inc/h.h", "#define V 2\nint value_two;\n" + BIG)       # same size
    os.utime(h, ns=(st0.st_atime_ns, st0.st_mtime_ns))             # same mtime
    assert os.stat(h).st_size == st0.st_size
    t.same(["-c", "-g", c], "after the edit", expect={"hits": 0})
    t.same(["-E", c], "after the edit, -E")
    age()
    t.same(["-c", "-g", c], "after the edit, aged (records)", expect={"recorded": lambda x: x >= 1})
    t.same(["-c", "-g", c], "after the edit, aged (replays)", expect={"hits": 1})
    return t.done()


def t_racy(a):
    """A header changed just before the compile is not recorded (its stat cannot show a change in the same tick)."""
    t = T(a, "racy")
    t.write("h.h", "int racy_a;\n" + BIG)
    c = t.write("a.c", '#include "h.h"\nint main(void) { return 0; }\n')
    t.same(["-c", c], "fresh header", expect={"recorded": 0, "bad": lambda x: x >= 1})
    t.write("h.h", "int racy_b;\n" + BIG)
    t.same(["-c", c], "changed again at once", expect={"hits": 0})
    return t.done()


def t_macros(a):
    """-D/-U and the macros defined before an include change a header's meaning."""
    t = T(a, "macros")
    t.write("h.h", "#ifdef WIDE\ntypedef long num;\n#else\ntypedef int num;\n#endif\n#ifndef LIMIT\n#define LIMIT 10\n#endif\nnum lim = LIMIT;\n" + BIG)
    c = t.write("a.c", '#include "h.h"\nint size(void) { return sizeof(num) + LIMIT; }\n')
    c2 = t.write("b.c", '#define WIDE\n#include "h.h"\nint size(void) { return sizeof(num) + LIMIT; }\n')
    c3 = t.write("c.c", '#define LIMIT 99\n#include "h.h"\nint size(void) { return sizeof(num) + LIMIT; }\n')
    c4 = t.write("d.c", '#define LIMIT 98\n#include "h.h"\nint size(void) { return sizeof(num) + LIMIT; }\n')
    age()
    t.same(["-c", c], "plain", expect={"recorded": 1})
    t.same(["-c", c], "plain again", expect={"hits": 1})
    t.same(["-c", "-DWIDE", c], "-DWIDE", expect={"hits": 0, "recorded": 1})
    t.same(["-c", c2], "#define WIDE", expect={"hits": 1})     # the same state as -DWIDE
    t.same(["-c", "-DLIMIT=7", c], "-DLIMIT=7", expect={"hits": 0})
    t.same(["-c", c3], "#define LIMIT 99", expect={"hits": 0})
    t.same(["-c", c4], "#define LIMIT 98 (another definition)", expect={"hits": 0})
    t.same(["-c", c3], "#define LIMIT 99 again", expect={"hits": 1})
    t.same(["-c", "-UWIDE", c2], "-UWIDE then #define WIDE", expect={"hits": 1})
    return t.done()


def t_order(a):
    """Include order: b.h depends on what a.h defined; guards seen in another order."""
    t = T(a, "order")
    t.write("a.h", "#ifndef A_H\n#define A_H\n#define FROM_A 1\nint in_a;\n#include \"c.h\"\n#endif\n" + BIG)
    t.write("b.h", "#ifndef B_H\n#define B_H\n#ifdef FROM_A\nint b_saw_a;\n#else\nint b_alone;\n#endif\n#include \"c.h\"\n#endif\n" + BIG)
    t.write("c.h", "#ifndef C_H\n#define C_H\nint in_c;\n#endif\n" + BIG)
    ab = t.write("ab.c", '#include "a.h"\n#include "b.h"\nint x;\n')
    ba = t.write("ba.c", '#include "b.h"\n#include "a.h"\nint x;\n')
    age()
    for k in range(2):
        t.same(["-E", ab], f"a then b, -E #{k}")
        t.same(["-c", ab], f"a then b #{k}", expect={"hits": 2} if k else None)
        t.same(["-E", ba], f"b then a, -E #{k}")
        t.same(["-c", ba], f"b then a #{k}", expect={"hits": 2} if k else None)
    return t.done()


def t_include_next(a):
    """#include_next chains, and a header created later in an earlier directory (shadowing)."""
    t = T(a, "next")
    t.write("d1/x.h", "int x_d1;\n#include_next <x.h>\n" + BIG)
    t.write("d2/x.h", "int x_d2;\n#include_next <x.h>\n")
    t.write("d3/x.h", "int x_d3;\n")
    t.write("d0/keep", "")
    c = t.write("a.c", "#include <x.h>\nint main(void) { return 0; }\n")
    flags = ["-I" + t.path("d0"), "-I" + t.path("d1"), "-I" + t.path("d2"), "-I" + t.path("d3")]
    age()
    t.same(["-c"] + flags + [c], "chain d1 d2 d3", expect={"recorded": 1})
    t.same(["-c"] + flags + [c], "chain again", expect={"hits": 1})
    t.same(["-E"] + flags + [c], "chain -E")
    t.write("d0/x.h", "int x_d0_shadows;\n")          # a new header in an earlier directory
    t.same(["-c"] + flags + [c], "after d0/x.h appears", expect={"hits": 0})
    t.same(["-E"] + flags + [c], "after d0/x.h appears, -E")
    os.unlink(t.path("d0/x.h"))
    t.write("d2/sub/y.h", "int y;\n")                   # changes d2 (a directory whose entries the chain read)
    t.same(["-c"] + flags + [c], "after d0/x.h is gone again")
    return t.done()


def t_counter(a):
    """__COUNTER__ in a header: its value depends on what was counted before."""
    t = T(a, "counter")
    t.write("h.h", "int uniq_##__COUNTER__;\nint var_c = __COUNTER__;\n" + BIG)
    c1 = t.write("a.c", '#include "h.h"\nint z = __COUNTER__;\n')
    c2 = t.write("b.c", 'int y = __COUNTER__;\n#include "h.h"\nint z = __COUNTER__;\n')
    age()
    for k in range(2):
        t.same(["-E", c1], f"counter from 0 -E #{k}")
        t.same(["-c", c1], f"counter from 0 #{k}", expect={"hits": 1} if k else None)
        t.same(["-E", c2], f"counter from 1 -E #{k}")
        t.same(["-c", c2], f"counter from 1 #{k}", expect={"hits": 1} if k else None)
    return t.done()


def t_states(a):
    """One header included under different macro states: guard predefined, a macro it expands redefined."""
    t = T(a, "states")
    t.write("h.h", "#ifndef H_H\n#define H_H\nT make(void);\nint uses = COUNT;\n#endif\n" + BIG)
    c = t.write("a.c", '#include "h.h"\nint main(void) { return 0; }\n')
    age()
    t.same(["-c", "-DT=int", "-DCOUNT=1", c], "T=int", expect={"recorded": 1})
    t.same(["-c", "-DT=long", "-DCOUNT=1", c], "T=long", expect={"hits": 0})
    t.same(["-c", "-DT=int", "-DCOUNT=1", c], "T=int again", expect={"hits": 1})
    t.same(["-c", "-DT=int", "-DCOUNT=2", c], "COUNT=2", expect={"hits": 0})
    t.same(["-c", "-DT=int", "-DCOUNT=1", "-DH_H", c], "guard predefined")
    t.same(["-c", "-DT=int", "-DCOUNT=(1)", c], "COUNT=(1)", expect={"hits": 0})
    t.same(["-c", "-DT=int", "-DCOUNT= 1", c], "COUNT= 1 (spacing)")
    return t.done()


def t_symlink(a):
    """A symlinked include directory retargeted, and a relocated one."""
    t = T(a, "symlink")
    t.write("v1/h.h", "#define VER 1\nint ver1;\n" + BIG)
    t.write("v2/h.h", "#define VER 2\nint ver2;\n" + BIG)
    os.symlink(t.path("v1"), t.path("cur"))
    c = t.write("a.c", "#include <h.h>\nint ver(void) { return VER; }\n")
    flags = ["-I" + t.path("cur")]
    age()
    t.same(["-c"] + flags + [c], "cur -> v1", expect={"recorded": 1})
    t.same(["-c"] + flags + [c], "cur -> v1 again", expect={"hits": 1})
    os.unlink(t.path("cur"))
    os.symlink(t.path("v2"), t.path("cur"))
    t.same(["-c"] + flags + [c], "cur -> v2", expect={"hits": 0})
    t.same(["-E"] + flags + [c], "cur -> v2 -E")
    shutil.move(t.path("v1"), t.path("moved"))
    t.same(["-c", "-I" + t.path("moved"), c], "v1 moved", expect={"hits": 0})
    return t.done()


def t_relative(a):
    """Quoted includes from the same spelling in different directories (relative paths, two working directories)."""
    t = T(a, "relative")
    for d, v in (("p1", 1), ("p2", 2)):
        t.write(f"{d}/inc/h.h", f"int rel{v};\n" + BIG)
        t.write(f"{d}/a.c", '#include "inc/h.h"\nint main(void) { return 0; }\n')
    age()
    for k in range(2):
        t.same(["-c", "a.c"], f"p1 #{k}", cwd=t.path("p1"))
        t.same(["-c", "a.c"], f"p2 #{k}", cwd=t.path("p2"))
        t.same(["-E", "a.c"], f"p2 -E #{k}", cwd=t.path("p2"))
    return t.done()


def t_pragmas(a):
    """#pragma once, push_macro/pop_macro, pack, GCC system_header, poison, __FILE__/__LINE__/__INCLUDE_LEVEL__."""
    t = T(a, "pragmas")
    t.write("once.h", "#pragma once\nint once_v;\n" + BIG)
    t.write("pm.h", '#pragma push_macro("X")\n#undef X\n#define X 7\nint pmx = X;\n#pragma pop_macro("X")\n' + BIG)
    t.write("pk.h", "#pragma pack(push, 2)\nstruct P { char c; int i; };\n#pragma pack(pop)\nstruct Q { char c; int i; };\n" + BIG)
    t.write("sys.h", "#pragma GCC system_header\nint sysv;\nconst char *f = __FILE__; int l = __LINE__; int lev = __INCLUDE_LEVEL__;\n" + BIG)
    t.write("lev.h", '#include "sys.h"\n' + BIG)
    c = t.write("a.c", '#define X 1\n#include "once.h"\n#include "once.h"\n#include "pm.h"\nint after = X;\n#include "pk.h"\n'
                '#include "sys.h"\nint s1 = sizeof(struct P), s2 = sizeof(struct Q);\n')
    c2 = t.write("b.c", '#include "lev.h"\n#pragma pack(4)\n#include "pk.h"\nint s1 = sizeof(struct P), s2 = sizeof(struct Q);\n')
    age()
    for k in range(2):
        for f in (c, c2):
            t.same(["-E", f], f"{os.path.basename(f)} -E #{k}")
            t.same(["-c", "-g", f], f"{os.path.basename(f)} -c -g #{k}", expect={"misses": lambda x: True} if k else None)
            t.same(["--layout-check", f, "-o", t.path("lc.c")], f"{os.path.basename(f)} layout #{k}")
    return t.done()


def t_time(a):
    """__DATE__/__TIME__ in a header: never recorded."""
    t = T(a, "time")
    t.write("h.h", "const char *when = __DATE__ \" \" __TIME__;\n" + BIG)
    c = t.write("a.c", '#include "h.h"\nint main(void) { return 0; }\n')
    age()
    t.same(["-c", c], "first", expect={"recorded": 0, "bad": lambda x: x >= 1})
    t.same(["-c", c], "second", env_extra={"SOURCE_DATE_EPOCH": "1800000000"}, expect={"hits": 0})
    return t.done()


def t_deleted(a):
    """A header deleted after it was recorded: the same error as without the cache."""
    t = T(a, "deleted")
    t.write("h.h", "int gone;\n" + BIG)
    c = t.write("a.c", '#include "h.h"\nint main(void) { return 0; }\n')
    age()
    t.same(["-c", c], "first", expect={"recorded": 1})
    os.unlink(t.path("h.h"))
    t.same(["-c", c], "deleted")
    return t.done()


def t_concurrent(a):
    """Concurrent compiles writing the same entries: 16 files sharing headers, 8 at a time, twice."""
    t = T(a, "concurrent")
    for i in range(6):
        t.write(f"h{i}.h", f"#ifndef H{i}\n#define H{i}\n#include <stdio.h>\n#include <stdlib.h>\nint h{i};\n#endif\n" + BIG)
    files = []
    for i in range(16):
        inc = "".join(f'#include "h{(i + j) % 6}.h"\n' for j in range(3))
        files.append(t.write(f"f{i}.c", inc + f"#include <string.h>\nint f{i}(void) {{ return 0; }}\n"))
    age()
    jobs = [(f, k) for k in range(2) for f in files]
    obj = lambda f, k: f + f".{k}.o"
    refs = {(f, k): t.run(["-c", f], False, obj=obj(f, k))[0] for f, k in jobs}
    for rnd in range(2):
        with cf.ThreadPoolExecutor(8) as ex:
            res = list(ex.map(lambda j: (j, t.run(["-c", j[0]], True, obj=obj(*j))[0]), jobs))
        for j, got in res:
            t.checks += 1
            if got != refs[j]:
                t.fails.append(f"round {rnd}: {os.path.basename(j[0])} differs")
    leftovers = [p for dp, dn, fn in os.walk(t.cache) for p in fn if p.endswith(".tmp")]
    if leftovers:
        t.fails.append(f"temporary files left: {leftovers[:3]}")
    return t.done()


def t_corrupt(a):
    """Corrupted cache files: flipped bytes, truncation, garbage, an empty file; none may change a result or crash."""
    t = T(a, "corrupt")
    t.write("h.h", "#include <stdio.h>\n#include <stdlib.h>\nint corr;\n" + BIG)
    c = t.write("a.c", '#include "h.h"\n#include <string.h>\nint main(void) { return 0; }\n')
    age()
    t.same(["-c", c], "record", expect={"recorded": lambda x: x >= 1})
    files = sorted(os.path.join(dp, f) for dp, dn, fn in os.walk(t.cache) for f in fn)
    blobs = [f for f in files if f.endswith(".b")]
    mans = [f for f in files if f.endswith(".m")]
    rng = random.Random(1)
    saved = {f: open(f, "rb").read() for f in files}

    def restore():
        for f, data in saved.items():
            with open(f, "wb") as fh:
                fh.write(data)

    damages = []
    for f in blobs[:3] + mans[:3]:
        n = len(saved[f])
        for kind in ("flip", "flip-late", "truncate", "garbage", "empty", "zero-tail"):
            damages.append((f, kind))
    for f, kind in damages:
        restore()
        data = bytearray(saved[f])
        if kind == "flip":
            i = rng.randrange(20, len(data))
            data[i] ^= 1 << rng.randrange(8)
        elif kind == "flip-late":
            i = len(data) - 1 - rng.randrange(min(64, len(data) - 20))
            data[i] ^= 0x40
        elif kind == "truncate":
            data = data[:len(data) // 2]
        elif kind == "garbage":
            data = bytearray(rng.randrange(256) for _ in range(len(data)))
        elif kind == "empty":
            data = bytearray()
        elif kind == "zero-tail":
            data = data[:len(data) - 64] + bytearray(64)
        with open(f, "wb") as fh:
            fh.write(data)
        t.same(["-c", c], f"{os.path.basename(f)} {kind}")
        t.same(["-E", c], f"{os.path.basename(f)} {kind} -E")
    restore()
    t.same(["-c", c], "restored", expect={"hits": lambda x: x >= 1})
    return t.done()


def t_policy(a):
    """The default units: <...> includes from the program's files; "..." includes of the main file from its second compile on."""
    t = T(a, "policy")
    t.write("p.h", "#include <stdio.h>\nint p_h;\n" + BIG)
    c = t.write("a.c", '#include "p.h"\n#include <stdlib.h>\nint main(void) { return 0; }\n')
    age()
    q = {"GOOSECC_CACHE_QUOTED": ""}
    t.same(["-c", c], "first compile: the <...> includes", env_extra=q, expect={"lookups": 2, "recorded": 2})
    t.same(["-c", c], "second compile: also \"p.h\" (its <stdio.h> replayed inside)", env_extra=q, expect={"lookups": 3, "hits": 2, "recorded": 1})
    t.same(["-c", c], "third compile", env_extra=q, expect={"lookups": 2, "hits": 2, "recorded": 0})
    return t.done()


TESTS = [t_policy, t_edit_same_size, t_racy, t_macros, t_order, t_include_next, t_counter, t_states, t_symlink, t_relative,
         t_pragmas, t_time, t_deleted, t_concurrent, t_corrupt]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goosecc", default=os.path.join(HERE, "..", "build", "goosecc"))
    ap.add_argument("-v", action="store_true")
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("tests", nargs="*")
    a = ap.parse_args()
    a.goosecc = os.path.abspath(a.goosecc)
    todo = [x for x in TESTS if not a.tests or x.__name__[2:] in a.tests]
    total_fail = 0
    for fn in todo:
        print(f"{fn.__name__[2:]}: {fn.__doc__}", flush=True)
        fails = fn(a)
        for f in fails:
            print("   FAIL", f)
        total_fail += len(fails)
        print("   ok" if not fails else f"   {len(fails)} failures", flush=True)
    print(f"{len(todo)} tests, {total_fail} failures")
    sys.exit(1 if total_fail else 0)


if __name__ == "__main__":
    main()
