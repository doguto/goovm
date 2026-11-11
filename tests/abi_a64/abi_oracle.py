#!/usr/bin/env python3
"""The AAPCS64 ABI oracle (milestone F1): code of clang, goovm-llc and goosecc
must call each other with every kind of argument and result.

It generates one C program in two translation units: callee.c defines, per
type T of a list (integers of every size, __int128, float, double, long
double (binary128), _Float16, pointers, enums, complex types, vectors, HFAs
and HVAs of one to five members, mixed and padded structures of 1 to 100
bytes, unions, arrays in structures, bit-fields, packed and over-aligned
structures, empty structures), functions taking T in registers and on the
stack (after the registers are used up), returning T, variadic functions
reading T with va_arg, functions passing a va_list on, and callbacks;
caller.c calls all of them with known values and prints a checksum of each
result (each member hashed by value: padding is not compared). Every pair of
compilers (caller, callee) out of
  clang   clang-20 --target=aarch64-linux-gnu -O0
  llc     clang -O0 -emit-llvm, then goovm-llc (the Goose back-end)
  cc      goovm-cc
  gcc     goosecc (when --goosecc is given)
builds the two objects, links them with clang and runs the program under
qemu-aarch64; the output must be the clang/clang output.

With --cxx the program is C++ (the functions extern "C"), goovm-cc is left
out and C++ classes with bases are added (HFAs split across base and
derived, empty bases, non-HFA bases, several bases, an over-aligned base);
an empty class is passed as one byte there. (C++ leaves out the vector types
and the variadic functions: goosecc's C++ has no vector_size types and no
AArch64 va_list yet.)

usage: tests/abi_a64/abi_oracle.py [--goovm-llc P] [--goovm-cc P] [--goosecc P]
                                   [--work DIR] [--o1] [--cxx] [--comps LIST]
"""
import argparse, itertools, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
T = ["--target=aarch64-linux-gnu"]
QENV = dict(os.environ, QEMU_LD_PREFIX="/usr/aarch64-linux-gnu")

# name: (definition or "", C type, list of (member access, member type) for hashing; "" = scalar)
TYPES = []


def scalar(name, ctype, kind):
    TYPES.append((name, "", ctype, [("", kind)]))


def struct(name, body, members):
    TYPES.append((name, f"typedef {body} {name};", name, members))


scalar("c", "char", "i")
scalar("sc", "signed char", "i")
scalar("uc", "unsigned char", "i")
scalar("b", "_Bool", "i")
scalar("s", "short", "i")
scalar("us", "unsigned short", "i")
scalar("i", "int", "i")
scalar("u", "unsigned", "i")
scalar("l", "long", "i")
scalar("ll", "long long", "i")
scalar("i128", "__int128", "i128")
scalar("f", "float", "f")
scalar("d", "double", "f")
scalar("ld", "long double", "f")
scalar("h", "_Float16", "f")
scalar("p", "vp", "p")
scalar("e", "enum E", "i")
scalar("cf", "_Complex float", "cf")
scalar("cd", "_Complex double", "cf")
scalar("cld", "_Complex long double", "cf")
scalar("v8", "v8b", "v8")       # 8-byte vector
scalar("v16", "v4f", "v16")     # 16-byte vector
scalar("v32", "v8f", "v32")     # 32-byte vector (illegal: by reference)
scalar("v3", "v3f", "v3")       # three lanes (illegal: <4 x i32>)
scalar("v2s", "v2s", "v2s")     # 4-byte vector (illegal: i32)
struct("S1", "struct { char a; }", [(".a", "i")])
struct("S2", "struct { short a; }", [(".a", "i")])
struct("S3", "struct { char a[3]; }", [(".a[0]", "i"), (".a[1]", "i"), (".a[2]", "i")])
struct("S5", "struct { char a; int b; }", [(".a", "i"), (".b", "i")])
struct("S7", "struct { char a[7]; }", [(f".a[{k}]", "i") for k in range(7)])
struct("S8", "struct { int a, b; }", [(".a", "i"), (".b", "i")])
struct("S12", "struct { int a, b, c; }", [(".a", "i"), (".b", "i"), (".c", "i")])
struct("S16", "struct { long a, b; }", [(".a", "i"), (".b", "i")])
struct("S16q", "struct { __int128 a; }", [(".a", "i128")])
struct("S24", "struct { long a, b, c; }", [(".a", "i"), (".b", "i"), (".c", "i")])
struct("S100", "struct { char a[100]; }", [(f".a[{k}]", "i") for k in range(0, 100, 7)])
struct("Sid", "struct { int a; double b; }", [(".a", "i"), (".b", "f")])
struct("Sfd", "struct { float a; double b; }", [(".a", "f"), (".b", "f")])
struct("Hf1", "struct { float a; }", [(".a", "f")])
struct("Hf2", "struct { float a, b; }", [(".a", "f"), (".b", "f")])
struct("Hf3", "struct { float a[3]; }", [(".a[0]", "f"), (".a[1]", "f"), (".a[2]", "f")])
struct("Hf4", "struct { struct { float x, y; } p; float a[2]; }", [(".p.x", "f"), (".p.y", "f"), (".a[0]", "f"), (".a[1]", "f")])
struct("Hf5", "struct { float a, b, c, d, e; }", [(f".{x}", "f") for x in "abcde"])
struct("Hd2", "struct { double a, b; }", [(".a", "f"), (".b", "f")])
struct("Hd4", "struct { double a, b, c, d; }", [(f".{x}", "f") for x in "abcd"])
struct("Hld2", "struct { long double a, b; }", [(".a", "f"), (".b", "f")])
struct("Hh3", "struct { _Float16 a, b, c; }", [(".a", "f"), (".b", "f"), (".c", "f")])
struct("Hv2", "struct { v4f a, b; }", [(".a", "v16"), (".b", "v16")])
struct("Hv8", "struct { v8b a, b, c; }", [(".a", "v8"), (".b", "v8"), (".c", "v8")])
struct("Hcf", "struct { _Complex float a; float b; }", [(".a", "cf"), (".b", "f")])
struct("U8", "union { double d; long l; }", [(".l", "i")])
struct("Uf", "union { float a; float b[2]; }", [(".b[0]", "f"), (".b[1]", "f")])
struct("Bf", "struct { int a : 3; unsigned b : 13; long c : 40; }", [(".a", "i"), (".b", "i"), (".c", "i")])
struct("Pk", "struct __attribute__((packed)) { char a; int b; short c; }", [(".a", "i"), (".b", "i"), (".c", "i")])
struct("Al", "struct __attribute__((aligned(16))) { long a; }", [(".a", "i")])
struct("Emp", "struct { }", [])

# C++ classes with bases (--cxx): bases are classified with the class (an HFA
# split across base and derived, empty bases, a base that is not floating
# point, several bases, an over-aligned base)
CXX_TYPES = []


def cxx(name, body, members):
    CXX_TYPES.append((name, body, name, members))


cxx("D0", "struct B0 {}; struct D0 : B0 {};", [])
cxx("DF", "struct BF { float a; }; struct DF : BF { float b; };", [(".a", "f"), (".b", "f")])
cxx("DFI", "struct BI { int a; }; struct DFI : BI { float b; };", [(".a", "i"), (".b", "f")])
cxx("DMix", "struct BD { double a; }; struct DMix : BD { float b; };", [(".a", "f"), (".b", "f")])
cxx("DE", "struct E0 {}; struct DE : E0 { double a, b; };", [(".a", "f"), (".b", "f")])
cxx("D4", "struct B2 { float x, y; }; struct D4 : B2 { float z, w; };", [(f".{x}", "f") for x in "xyzw"])
cxx("D5", "struct D5 : B2 { float z, w, v; };", [(f".{x}", "f") for x in "xyzwv"])
cxx("MM", "struct BG { float g; }; struct MM : BF, BG { float c; };", [(".a", "f"), (".g", "f"), (".c", "f")])
cxx("DEE", "struct E1 {}; struct DEE : E0, E1 { float a; };", [(".a", "f")])
cxx("BL", "struct BL : BI { long l; };", [(".a", "i"), (".l", "i")])
cxx("DA", "struct alignas(16) BA { long a; }; struct DA : BA { long b; };", [(".a", "i"), (".b", "i")])
cxx("DDd", "struct BDd { double a; }; struct DDd : BDd { double b[3]; };", [(".a", "f")] + [(f".b[{k}]", "f") for k in range(3)])
cxx("DH", "struct BH { _Float16 a; }; struct DH : BH { _Float16 b, c; };", [(".a", "f"), (".b", "f"), (".c", "f")])
cxx("DEm", "struct DEm : B0, E0 {};", [])

KIND_TYPES = {"i": "long long", "f": "long double"}


def defs():
    return """#include <stdarg.h>
#include <stdio.h>
#include <string.h>
enum E { E0, E1 = 1000, E2 = -7 };
typedef unsigned char v8b __attribute__((vector_size(8)));
typedef float v4f __attribute__((vector_size(16)));
typedef float v8f __attribute__((vector_size(32)));
typedef float v3f __attribute__((ext_vector_type(3)));
typedef short v2s __attribute__((vector_size(4)));
typedef void *vp;
""" + "\n".join(d for _, d, _, _ in TYPES if d) + "\n"


def hash_expr(acc, kind):
    """C statements hashing the value expression acc of member kind into h."""
    if kind == "i":
        return [f"h = h * 1000003u + (unsigned long long)({acc});"]
    if kind == "i128":
        return [f"h = h * 1000003u + (unsigned long long)({acc}) + (unsigned long long)(({acc}) >> 64);"]
    if kind == "f":
        return [f"h = h * 1000003u + (unsigned long long)(long long)(({acc}) * 64);"]
    if kind == "p":
        return [f"h = h * 1000003u + (unsigned long long)((char *)({acc}) - gbuf);"]
    if kind == "cf":
        return [f"h = h * 1000003u + (unsigned long long)(long long)(__real__ ({acc}) * 64);",
                f"h = h * 1000003u + (unsigned long long)(long long)(__imag__ ({acc}) * 64);"]
    n = {"v8": 8, "v16": 4, "v32": 8, "v3": 3, "v2s": 2}[kind]
    return [f"for (int k = 0; k < {n}; k++) h = h * 1000003u + (unsigned long long)(long long)((({ELT[kind]} *)&({acc}))[k] * 4);"]


def setter(acc, kind, seed):
    """C statements giving member acc a value from seed (an int expression)."""
    if kind in ("i", "i128"):
        return [f"{acc} = (seed * 37 + {seed}) & 0x7f;"] if acc.endswith("]") or kind == "i" and False else \
               [f"{acc} = seed * 37 + {seed};"]
    if kind == "f":
        return [f"{acc} = (seed + {seed}) * 0.75 - 3;"]
    if kind == "p":
        return [f"{acc} = (char *)&gbuf + ((seed + {seed}) & 15);"]
    if kind == "cf":
        return [f"__real__ {acc} = seed + {seed} + 0.5; __imag__ {acc} = -seed - {seed};"]
    n = {"v8": 8, "v16": 4, "v32": 8, "v3": 3, "v2s": 2}[kind]
    return [f"for (int k = 0; k < {n}; k++) (({ELT[kind]} *)&({acc}))[k] = seed + {seed} + k;"]


VEC_KINDS = ("v8", "v16", "v32", "v3", "v2s")


# vector lanes through an element pointer (goosecc's C++ has no vector subscripts)
ELT = {"v8": "unsigned char", "v16": "float", "v32": "float", "v3": "float", "v2s": "short"}


def gen(dirn, cxx_mode=False):
    types = TYPES + (CXX_TYPES if cxx_mode else [])
    if cxx_mode:
        # (no vector types: goosecc's C++ does not have vector_size types yet)
        types = [(n, d, "bool" if ct == "_Bool" else ct, m) for n, d, ct, m in types
                 if not any(k in VEC_KINDS for _, k in m)]
    d = defs() + ("\n".join(b for _, b, _, _ in CXX_TYPES) + "\nextern \"C\" {\n" if cxx_mode else "")
    callee = [d, "char gbuf[64];"]
    caller = [d, "extern char gbuf[64];"]
    for name, _, ct, members in types:
        # hash_T, make_T (in both units: static)
        for out in (callee, caller):
            out.append(f"static unsigned long long hash_{name}({ct} v) {{ unsigned long long h = 7; (void)v;")
            for acc, kind in members:
                out += ["  " + x for x in hash_expr("v" + acc, kind)]
            out.append("  return h; }")
            out.append(f"static {ct} make_{name}(int seed) {{ {ct} v; memset(&v, 0, sizeof v); (void)seed;")
            for k, (acc, kind) in enumerate(members):
                st = setter("v" + acc, kind, k + 1)
                if ct.startswith("enum"):
                    st = [f"v = ({ct})(seed * 37 + {k + 1});"]
                out += ["  " + x for x in st]
            out.append("  return v; }")
        # callee functions; the variadic ones (C++: stubs: classes with bases
        # are not POD for va_arg, and goosecc's C++ does not take AArch64's
        # va_list yet)
        if cxx_mode:
            callee.append(f"""
unsigned long long va_{name}(int n, ...) {{ return 0; }}
unsigned long long vafwd_{name}(int n, ...) {{ return 0; }}""")
        else:
            callee.append(f"""
unsigned long long va_{name}(int n, ...) {{
  va_list ap; va_start(ap, n);
  unsigned long long h = 0;
  for (int k = 0; k < n; k++) {{ {ct} v = va_arg(ap, {ct}); h = h * 31 + hash_{name}(v); int i = va_arg(ap, int); h += i; }}
  va_end(ap); return h; }}
static unsigned long long vl_{name}(int n, va_list ap) {{
  unsigned long long h = 0;
  for (int k = 0; k < n; k++) {{ {ct} v = va_arg(ap, {ct}); h = h * 17 + hash_{name}(v); }}
  return h; }}
unsigned long long vafwd_{name}(int n, ...) {{
  va_list ap, aq; va_start(ap, n); va_copy(aq, ap);
  unsigned long long h = vl_{name}(n, ap) + 3 * vl_{name}(n, aq);
  va_end(aq); va_end(ap); return h; }}
""")
        callee.append(f"""
{ct} ret_{name}(int seed) {{ return make_{name}(seed); }}
unsigned long long args_{name}({ct} a, int x, {ct} b, double y, {ct} c) {{
  return hash_{name}(a) * 3 + hash_{name}(b) * 5 + hash_{name}(c) * 7 + x + (long long)(y * 2); }}
unsigned long long stack_{name}(long r0, long r1, long r2, long r3, long r4, long r5, long r6,
    double f0, double f1, double f2, double f3, double f4, double f5, double f6, {ct} a, char z, {ct} b) {{
  return hash_{name}(a) * 11 + hash_{name}(b) * 13 + z + r0 + r6 + (long long)(f0 + f6); }}
unsigned long long cb_{name}({ct} (*f)(int, {ct}), {ct} a) {{ return hash_{name}(f(5, a)); }}
""")
        caller.append(f"""
{ct} ret_{name}(int seed);
unsigned long long args_{name}({ct} a, int x, {ct} b, double y, {ct} c);
unsigned long long stack_{name}(long r0, long r1, long r2, long r3, long r4, long r5, long r6,
    double f0, double f1, double f2, double f3, double f4, double f5, double f6, {ct} a, char z, {ct} b);
unsigned long long va_{name}(int n, ...);
unsigned long long vafwd_{name}(int n, ...);
unsigned long long cb_{name}({ct} (*f)(int, {ct}), {ct} a);
static {ct} back_{name}(int k, {ct} a) {{ return k == 5 ? a : make_{name}(1); }}
static void test_{name}(void) {{
  {ct} a = make_{name}(1), b = make_{name}(2), c = make_{name}(3);
  printf("{name} ret %llx\\n", hash_{name}(ret_{name}(4)));
  printf("{name} args %llx\\n", args_{name}(a, 9, b, 2.5, c));
  printf("{name} stack %llx\\n", stack_{name}(1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, a, 'z', b));
  printf("{name} va %llx\\n", {"va_" + name + "(0)" if cxx_mode else "va_" + name + "(3, a, 10, b, 20, c, 30)"});
  printf("{name} vafwd %llx\\n", {"vafwd_" + name + "(0)" if cxx_mode else "vafwd_" + name + "(3, a, b, c)"});
  printf("{name} cb %llx\\n", cb_{name}(back_{name}, b));
}}""")
    if cxx_mode:
        callee.append("}")
        caller.append("}")
    caller.append("int main(void) {")
    for name, _, _, _ in types:
        caller.append(f"  test_{name}();")
    caller.append("  return 0; }")
    ext = ".cpp" if cxx_mode else ".c"
    open(os.path.join(dirn, "callee" + ext), "w").write("\n".join(callee) + "\n")
    open(os.path.join(dirn, "caller" + ext), "w").write("\n".join(caller) + "\n")


def run(cmd, **kw):
    return subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=600, **kw)


def build(comp, src, obj, args):
    if comp == "clang":
        r = run(["clang-20"] + T + ["-O0", "-w", "-c", src, "-o", obj])
    elif comp == "llc" and src.endswith(".cpp"):
        bc = obj + ".bc"
        r = run(["clang-20"] + T + ["-O0", "-w", "-c", "-emit-llvm", src, "-o", bc])
        if r.returncode == 0:
            r = run([args.goovm_llc] + (["-O1"] if args.o1 else []) + [bc, "-o", obj])
    elif comp == "llc":
        bc = obj + ".bc"
        r = run(["clang-20"] + T + ["-O0", "-w", "-c", "-emit-llvm", src, "-o", bc])
        if r.returncode == 0:
            r = run([args.goovm_llc] + (["-O1"] if args.o1 else []) + [bc, "-o", obj])
    elif comp == "cc":
        r = run([args.goovm_cc] + T + ["-O0", "-w", "-c", src, "-o", obj])
    else:
        r = run([args.goosecc] + T + ["-w", "-c", src, "-o", obj])
    if r.returncode != 0:
        return r.stderr.decode(errors="replace")[-1500:]
    return None


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goovm-llc", default=os.path.join(ROOT, "build/tools/goovm-llc/goovm-llc"))
    ap.add_argument("--goovm-cc", default=os.path.join(ROOT, "build/tools/goovm-cc/goovm-cc"))
    ap.add_argument("--goosecc", default="")
    ap.add_argument("--work", default="/tmp/abi_a64")
    ap.add_argument("--o1", action="store_true", help="goovm-llc -O1")
    ap.add_argument("--comps", default="", help="comma-separated subset of clang,llc,cc,gcc")
    ap.add_argument("--cxx", action="store_true", help="C++ (extern \"C\" functions; adds classes with bases; no goovm-cc)")
    a = ap.parse_args()
    os.makedirs(a.work, exist_ok=True)
    gen(a.work, a.cxx)
    ext = ".cpp" if a.cxx else ".c"
    comps = ["clang", "llc"] + ([] if a.cxx else ["cc"]) + (["gcc"] if a.goosecc else [])
    if a.comps:
        comps = a.comps.split(",")
    objs = {}
    fails = 0
    for c in comps:
        for part in ("caller", "callee"):
            o = os.path.join(a.work, f"{part}.{c}.o")
            err = build(c, os.path.join(a.work, part + ext), o, a)
            if err:
                print(f"BUILD FAIL {c} {part}:\n{err}")
                fails += 1
            else:
                objs[(c, part)] = o
    ref = None
    for x, y in itertools.product(comps, comps):
        if (x, "caller") not in objs or (y, "callee") not in objs:
            continue
        exe = os.path.join(a.work, f"t.{x}.{y}")
        r = run(["clang++-20" if a.cxx else "clang-20"] + T + ["-fuse-ld=lld", objs[(x, "caller")], objs[(y, "callee")], "-o", exe])
        if r.returncode:
            print(f"LINK FAIL {x}/{y}: {r.stderr.decode()[-500:]}")
            fails += 1
            continue
        r = run(["qemu-aarch64", exe], env=QENV)
        out = r.stdout.decode(errors="replace") + f"exit {r.returncode}\n"
        if x == "clang" and y == "clang":
            ref = out
            open(os.path.join(a.work, "ref.out"), "w").write(out)
            print(f"clang/clang: {len(out.splitlines()) - 1} checks")
            continue
        if ref is None:
            print("no reference")
            return 1
        if out != ref:
            fails += 1
            bad = [f"  {p} / {q}" for p, q in zip(ref.splitlines(), out.splitlines()) if p != q]
            print(f"FAIL caller {x} / callee {y}: {len(bad)} lines differ")
            print("\n".join(bad[:12]))
        else:
            print(f"ok   caller {x} / callee {y}")
    print("all passed" if fails == 0 else f"{fails} failures")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
