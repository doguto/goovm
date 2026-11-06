#!/usr/bin/env python3
"""ABI cross test for goosecc -c: random signatures (structs and unions of
scalars, arrays, bit-fields and nested records, packed or not; every scalar
type including __int128, long double and _Complex; variadic functions read
with va_arg), the callees in one file and the calls in another. Each file is
compiled by clang-20 -O0 and by goosecc; the four mixes are linked and must
print the same hashes of every argument and return value as the all-clang
build.

usage: frontend-goose/tests/abi_cross.py [--goosecc PATH] [--seeds 20] [--first 0] [-n 50] [--work DIR]
"""
import argparse, os, random, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))


def generate(seed, n):
    """Returns (lib.c, main.c) for one seed with n functions."""
    R = random.Random(seed)
    SCAL = ["char", "signed char", "unsigned char", "short", "unsigned short", "int", "unsigned", "long", "unsigned long",
            "long long", "float", "double", "long double", "_Bool", "void *", "__int128", "_Complex float", "_Complex double"]
    types = []   # (name, decl, is_struct)


    def rnd_field_type(depth):
        r = R.random()
        if depth < 2 and r < 0.15 and types:
            cands = [t for t in types if t[2]]
            if cands:
                return R.choice(cands)[0]
        return R.choice(SCAL)


    decls = []
    tinfo = {}   # name -> (kind, [(type, name, arrn, bits)])
    for i in range(12):
        kind = "union" if R.random() < 0.15 else "struct"
        nf = R.randint(1, 5)
        fields = []
        flist = []
        for j in range(nf):
            ft = rnd_field_type(0)
            arr = ""
            if R.random() < 0.15 and ft not in ("_Bool",):
                arr = "[%d]" % R.randint(1, 3)
            fields.append("%s f%d%s;" % (ft, j, arr))
            flist.append((ft, "f%d" % j, int(arr[1:-1]) if arr else 0, 0))
        if R.random() < 0.1 and kind == "struct":
            bw = R.randint(1, 20)
            fields.append("unsigned b%d : %d;" % (nf, bw))
            flist.append(("unsigned", "b%d" % nf, 0, bw))
        packed = " __attribute__((packed))" if R.random() < 0.08 else ""
        name = "%s S%d" % (kind, i)
        decls.append("%s { %s }%s;" % (name, " ".join(fields), packed))
        types.append((name, None, True))
        tinfo[name] = (kind, flist)

    hdr = ["#include <stdio.h>", "#include <string.h>"] + decls
    hdr.append("static unsigned long hb(const void *p, unsigned long n) { const unsigned char *c = p; unsigned long h = 5381; "
               "for (unsigned long i = 0; i < n; i++) h = h * 33 + c[i]; return h; }")
    hdr.append("static void fill(void *p, unsigned long n, unsigned k) { unsigned char *c = p; for (unsigned long i = 0; i < n; i++) "
               "c[i] = (unsigned char)(k * 7 + i * 13 + 1); }")
    def hexpr(t, e):
        """an expression hashing the value bytes of lvalue e of type t"""
        if t in tinfo:
            return "h%s(&%s)" % (t.split()[1], e)
        if t == "long double":
            return "hb(&%s, 10)" % e
        if t == "_Bool":
            return "(unsigned long)%s" % e
        return "hb(&%s, sizeof %s)" % (e, e)


    def lv(e):
        return e


    for name, (kind, flist) in tinfo.items():
        tn = name.split()[1]
        hdr.append("static unsigned long h%s(const %s *p);" % (tn, name))
    for name, (kind, flist) in tinfo.items():
        tn = name.split()[1]
        body = ["unsigned long h = 1;"]
        if kind == "union":
            # the bytes of the largest member (all of them carry values)
            body.append("unsigned long m = 0;")
            for (ft, fn, an, bw) in flist:
                body.append("if (sizeof p->%s > m) m = sizeof p->%s;" % (fn, fn))
            body.append("h = hb(p, m);")
        else:
            for (ft, fn, an, bw) in flist:
                if bw:
                    body.append("h = h * 31 + p->%s;" % fn)
                elif an:
                    body.append("for (int i = 0; i < %d; i++) h = h * 31 + %s;" % (an, hexpr(ft, "p->%s[i]" % fn)))
                else:
                    body.append("h = h * 31 + %s;" % hexpr(ft, "p->%s" % fn))
        body.append("return h;")
        hdr.append("static unsigned long h%s(const %s *p) { %s }" % (tn, name, " ".join(body)))
    all_t = [t[0] for t in types] + SCAL
    funcs = []
    for i in range(n):
        rt = R.choice(all_t + ["void"])
        na = R.randint(0, 9)
        args = [R.choice(all_t) for _ in range(na)]
        var = R.random() < 0.2
        funcs.append((i, rt, args, var))


    def proto(i, rt, args, var):
        ps = ", ".join("%s a%d" % (a, k) for k, a in enumerate(args))
        if var:
            ps = (ps + ", " if ps else "int cnt, ") + "..."
        if not ps:
            ps = "void"
        return "%s f%d(%s)" % (rt, i, ps)


    lib = list(hdr) + ["#include <stdarg.h>"]
    main = list(hdr) + ["#include <stdarg.h>"]
    for i, rt, args, var in funcs:
        p = proto(i, rt, args, var)
        main.append(p + ";")
        body = ["unsigned long h = %d;" % i]
        for k, a in enumerate(args):
            if a in ("float", "double", "long double", "_Complex float", "_Complex double"):
                body.append("{ %s t = a%d; h = h * 31 + hb(&t, %s); }" % (a, k,
                            "10" if a == "long double" else "sizeof t"))
            elif a == "_Bool":
                body.append("h = h * 31 + a%d;" % k)
            else:
                body.append("{ %s t = a%d; h = h * 31 + hb(&t, sizeof t); }" % (a, k) if not a.startswith(("struct", "union"))
                            else "h = h * 31 + %s;" % hexpr(a, "a%d" % k))
        if var:
            body.append("va_list ap; va_start(ap, %s);" % ("a%d" % (len(args) - 1) if args else "cnt"))
            for k, a in enumerate(args[:3]):
                pa = {"float": "double", "char": "int", "signed char": "int", "unsigned char": "int", "short": "int",
                      "unsigned short": "int", "_Bool": "int"}.get(a, a)
                if pa == "long double":
                    body.append("{ long double t = va_arg(ap, long double); h = h * 31 + hb(&t, 10); }")
                elif pa.startswith(("struct", "union")):
                    body.append("{ %s t = va_arg(ap, %s); h = h * 31 + %s; }" % (pa, pa, hexpr(pa, "t")))
                elif pa in ("double", "_Complex float", "_Complex double"):
                    body.append("{ %s t = va_arg(ap, %s); h = h * 31 + hb(&t, sizeof t); }" % (pa, pa))
                else:
                    body.append("{ %s t = va_arg(ap, %s); h = h * 31 + hb(&t, sizeof t); }" % (pa, pa))
            body.append("va_end(ap);")
        body.append('printf("f%d %%lu\\n", h);' % i)
        if rt != "void":
            body.append("%s r; memset(&r, 0, sizeof r); fill(&r, sizeof r, %d);" % (rt, i))
            if rt == "_Bool":
                body.append("r = %d;" % (i & 1))
            if rt == "long double":
                body.append("r = %d.5L;" % i)
            if rt == "float":
                body.append("r = %d.25f;" % i)
            if rt == "double":
                body.append("r = %d.125;" % i)
            if rt in ("_Complex float", "_Complex double"):
                body.append("r = %d.5 + %d.25i;" % (i, i))
            body.append("return r;")
        lib.append(p + " { " + " ".join(body) + " }")

    main.append("int main(void) {")
    for i, rt, args, var in funcs:
        pre = []
        vals = []
        for k, a in enumerate(args):
            pre.append("%s v%d_%d; memset(&v%d_%d, 0, sizeof v%d_%d); fill(&v%d_%d, sizeof v%d_%d, %d);" %
                       (a, i, k, i, k, i, k, i, k, i, k, i * 10 + k))
            if a == "_Bool":
                pre.append("v%d_%d = %d;" % (i, k, (i + k) & 1))
            if a == "long double":
                pre.append("v%d_%d = %d.75L;" % (i, k, k))
            if a in ("float", "double"):
                pre.append("v%d_%d = %d.5;" % (i, k, k))
            if a in ("_Complex float", "_Complex double"):
                pre.append("v%d_%d = %d.5 + 1.0i;" % (i, k, k))
            vals.append("v%d_%d" % (i, k))
        call_args = vals
        if var:
            call_args = (vals + vals[:3]) if vals else ["3"]
            if not vals:
                call_args = ["0"]
        main.append("{ " + " ".join(pre))
        c = "f%d(%s)" % (i, ", ".join(call_args))
        if rt == "void":
            main.append(c + "; }")
        else:
            main.append('%s r = %s; printf("r%d %%lu\\n", %s); }' % (rt, c, i, hexpr(rt, "r")))
    main.append("return 0; }")

    return "\n".join(lib) + "\n", "\n".join(main) + "\n"


def run(cmd, cwd):
    return subprocess.run(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)


def one(seed, n, gc, clang, work):
    d = os.path.join(work, str(seed))
    os.makedirs(d, exist_ok=True)
    lib, main = generate(seed, n)
    open(os.path.join(d, "lib.c"), "w").write(lib)
    open(os.path.join(d, "main.c"), "w").write(main)
    for f in ("lib", "main"):
        if run([clang, "-O0", "-w", "-c", f + ".c", "-o", f + ".cl.o"], d).returncode:
            return "clang failed on %s.c" % f
        r = run([gc, "-c", "-w", f + ".c", "-o", f + ".gc.o"], d)
        if r.returncode:
            return "goosecc failed on %s.c: %s" % (f, r.stdout.decode(errors="replace").splitlines()[:1])
    outs = {}
    for name, objs in (("cc", "lib.cl.o main.cl.o"), ("gc_lib", "lib.gc.o main.cl.o"),
                       ("gc_main", "lib.cl.o main.gc.o"), ("gg", "lib.gc.o main.gc.o")):
        if run([clang] + objs.split() + ["-o", name], d).returncode:
            return "link failed: " + name
        outs[name] = run(["./" + name], d).stdout
    bad = [k for k in ("gc_lib", "gc_main", "gg") if outs[k] != outs["cc"]]
    if bad:
        return "differs: " + ", ".join(bad)
    return None


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goosecc", default=os.path.join(HERE, "..", "build", "goosecc"))
    ap.add_argument("--clang", default="clang-20")
    ap.add_argument("--seeds", type=int, default=20)
    ap.add_argument("--first", type=int, default=0)
    ap.add_argument("-n", type=int, default=50, help="functions per seed")
    ap.add_argument("--work", default=None)
    a = ap.parse_args()
    work = a.work or tempfile.mkdtemp(prefix="abi_cross_")
    gc = os.path.abspath(a.goosecc)
    fails = 0
    for seed in range(a.first, a.first + a.seeds):
        err = one(seed, a.n, gc, a.clang, work)
        if err:
            fails += 1
            print("seed %d: %s (%s)" % (seed, err, os.path.join(work, str(seed))))
    print("%d of %d seeds pass (%d functions each; work: %s)" % (a.seeds - fails, a.seeds, a.n, work))
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
