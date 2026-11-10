#!/usr/bin/env python3
"""Generate src/predef_a64_gen.goose: what clang-20 / clang++-20 predefine and
answer for --target=aarch64-linux-gnu (milestone F1), against the x86-64
tables of predef_gen.goose and predef_cxx_gen.goose.

  PREDEF_A64_BASE      clang-20 --target=aarch64-linux-gnu -dM -E -x c /dev/null
  PREDEF_CXX_A64_BASE  the same with clang++-20 -x c++
  A64_DELTA            the __has_* answers that differ from the x86-64 tables:
                       lines "TABLE WORD VALUE" (TABLE: the table index of
                       ppexpr.goose's table_lookup, 0 __has_builtin .. 5
                       __has_declspec_attribute, 7 __has_cpp_attribute, 8
                       the C++ words that are not identifiers; value 0: absent)
  A64_CXX_DELTA        the same for C++ (gnu++17)
  A64_MARCH            per accepted -march= value ("=VALUE" lines), its macro delta
                       ("-NAME" removes, "+NAME VALUE" adds or replaces); the same
                       in C and C++

The option deltas goosecc applies by hand (-O, -std=, -pthread, PIC levels,
the C++ standards, -fno-exceptions, -fno-rtti) are checked to be the same
for AArch64 as for x86-64; -fsigned-char removes __CHAR_UNSIGNED__ (char is
unsigned on AArch64).

usage: tools/gen_predef_a64.py [--lib /usr/lib/x86_64-linux-gnu/libclang-cpp.so.20.1]
Run tools/gen_tables.py afterwards (nothing of this file is hashed there).
"""
import argparse, os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "src", "predef_a64_gen.goose")
T = "--target=aarch64-linux-gnu"
# the -march= values goosecc accepts for AArch64
MARCHES = ["armv8-a", "armv8-a+crc", "armv8-a+crypto", "armv8-a+crc+crypto", "armv8-a+simd", "armv8-a+fp16",
           "armv8-a+lse", "armv8.1-a", "armv8.2-a", "armv8.2-a+fp16", "armv8.2-a+dotprod",
           "armv8.2-a+crc+aes+sha2+dotprod", "armv8.3-a", "armv8.4-a", "armv8.5-a", "armv8.6-a", "armv9-a"]
STDS = ["c++98", "gnu++98", "c++11", "gnu++11", "c++14", "gnu++14", "c++17", "c++20", "gnu++20", "c++23", "gnu++23"]


def run(cmd, inp=None):
    r = subprocess.run(cmd, input=inp, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    return r.stdout.decode(errors="replace"), r.stderr.decode(errors="replace"), r.returncode


def macros(clang, lang, flags):
    out, err, rc = run([clang, "-dM", "-E", "-x", lang] + flags + ["/dev/null"])
    assert rc == 0, err
    d = {}
    for line in out.splitlines():
        m = re.match(r"#define (\S+)(?: (.*))?$", line)
        assert m, line
        d[m.group(1)] = m.group(2) or ""
    return out, d


def delta(base, d):
    out = []
    for k in sorted(base):
        if k not in d:
            out.append(f"-{k}")
    for k in sorted(d):
        if k not in base or d[k] != base[k]:
            out.append(f"+{k} {d[k]}".rstrip() if d[k] else f"+{k}")
    return out


def probe(clang, lang, words, fn, flags=()):
    lines = []
    for i, w in enumerate(words):
        val = "1" if fn.startswith("!") else f"{fn}({w})"
        lines.append(f"#if {fn}({w})\nGOOSECC_YES_{i} = {val}\n#endif\n")
    with tempfile.NamedTemporaryFile("w", suffix=".cpp" if lang == "c++" else ".c", delete=False) as f:
        f.write("".join(lines))
        path = f.name
    try:
        out, err, rc = run([clang, "-E", "-P", "-w", "-x", lang] + list(flags) + [path])
    finally:
        os.unlink(path)
    res = {}
    for line in out.splitlines():
        m = re.match(r"GOOSECC_YES_(\d+) = (\d+)L?", line.strip())
        if m:
            res[words[int(m.group(1))]] = int(m.group(2))
    return res


def goose_text(name, path):
    text = open(path).read()
    m = re.search(r'^let ' + name + r' = """\n(.*?)\n""";', text, re.S | re.M)
    assert m, name
    return m.group(1)


def table(name, path):
    t = {}
    for line in goose_text(name, path).split("\n"):
        if not line:
            continue
        w, _, v = line.partition(" ")
        t[w] = int(v) if v else 1
    return t


def goose_str(name, text):
    assert '"""' not in text
    return f'let {name} = """\n{text}\n""";\n'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--clang", default="clang-20")
    ap.add_argument("--clangxx", default="clang++-20")
    ap.add_argument("--lib", default="/usr/lib/x86_64-linux-gnu/libclang-cpp.so.20.1")
    a = ap.parse_args()
    src = os.path.join(HERE, "..", "src")
    pc = os.path.join(src, "predef_gen.goose")
    pcx = os.path.join(src, "predef_cxx_gen.goose")

    # C: the base, and the deltas goosecc applies (as for x86-64)
    ctext, cbase = macros(a.clang, "c", [T])
    def check(clang, lang, base, flags, add, rem, changed=None):
        _, d = macros(clang, lang, [T] + flags)
        exp = dict(base)
        for k in rem:
            exp.pop(k, None)
        exp.update(add)
        exp.update(changed or {})
        if d != exp:
            print("delta mismatch for", lang, flags, delta(exp, d), file=sys.stderr)
            sys.exit(1)
    for clang, lang, base in [(a.clang, "c", cbase), (a.clangxx, "c++", None)]:
        if base is None:
            _, base = macros(clang, lang, [T])
        check(clang, lang, base, ["-O2"], {"__OPTIMIZE__": "1"}, ["__NO_INLINE__"])
        check(clang, lang, base, ["-Os"], {"__OPTIMIZE__": "1", "__OPTIMIZE_SIZE__": "1"}, ["__NO_INLINE__"])
        check(clang, lang, base, ["-pthread"], {"_REENTRANT": "1"}, [])
        check(clang, lang, base, ["-fsigned-char"], {}, ["__CHAR_UNSIGNED__"])
        check(clang, lang, base, ["-funsigned-char"], {}, [])
        check(clang, lang, base, ["-fno-pic"], {}, ["__PIC__", "__pic__", "__PIE__", "__pie__"])
        check(clang, lang, base, ["-fPIC"], {}, ["__PIE__", "__pie__"])
        check(clang, lang, base, ["-fpic"], {}, ["__PIE__", "__pie__"], {"__PIC__": "1", "__pic__": "1"})
        check(clang, lang, base, ["-fpie"], {}, [], {"__PIC__": "1", "__pic__": "1", "__PIE__": "1", "__pie__": "1"})
    check(a.clang, "c", cbase, ["-std=c99"], {"__STRICT_ANSI__": "1"}, ["linux", "unix"], {"__STDC_VERSION__": "199901L"})
    check(a.clang, "c", cbase, ["-std=c11"], {"__STRICT_ANSI__": "1"}, ["linux", "unix"], {"__STDC_VERSION__": "201112L"})
    check(a.clang, "c", cbase, ["-std=c17"], {"__STRICT_ANSI__": "1"}, ["linux", "unix"])
    check(a.clang, "c", cbase, ["-std=c89"], {"__STRICT_ANSI__": "1", "__GNUC_GNU_INLINE__": "1"},
          ["linux", "unix", "__STDC_VERSION__", "__GNUC_STDC_INLINE__"])
    check(a.clang, "c", cbase, ["-std=gnu89"], {"__GNUC_GNU_INLINE__": "1"}, ["__STDC_VERSION__", "__GNUC_STDC_INLINE__"])
    check(a.clang, "c", cbase, ["-std=gnu99"], {}, [], {"__STDC_VERSION__": "199901L"})

    # C++: the base; the standards' deltas must be x86-64's
    xtext, xbase = macros(a.clangxx, "c++", [T])
    std_x86 = goose_text("PREDEF_CXX_STD", pcx).split("\n")
    std_a64 = []
    for s in STDS:
        _, d = macros(a.clangxx, "c++", [T, "-std=" + s])
        std_a64.append("=" + s)
        std_a64 += delta(xbase, d)
    if std_a64 != std_x86:
        print("C++ standard deltas differ on AArch64", file=sys.stderr)
        sys.exit(1)
    check(a.clangxx, "c++", xbase, ["-fno-exceptions"], {}, ["__EXCEPTIONS", "__cpp_exceptions"])
    check(a.clangxx, "c++", xbase, ["-fno-rtti"], {}, ["__GXX_RTTI", "__cpp_rtti"])

    # -march= values: their deltas against the base (C; C++ checked equal)
    march_lines = []
    for m in MARCHES:
        _, d = macros(a.clang, "c", [T, "-march=" + m])
        _, dx = macros(a.clangxx, "c++", [T, "-march=" + m])
        dl = delta(cbase, d)
        if delta(xbase, dx) != dl:
            print("C++ -march delta differs for", m, file=sys.stderr)
            sys.exit(1)
        march_lines.append("=" + m)
        march_lines += dl

    # the __has_* tables
    out, _, _ = run(["strings", "-n", "3", a.lib])
    words = sorted(set(w for w in out.split("\n") if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", w)))
    # and the target builtins clang's AArch64 headers call (not all of them are strings of libclang-cpp)
    inc = "/usr/lib/llvm-20/lib/clang/20/include"
    for h in ("arm_acle.h", "arm_neon.h", "arm_fp16.h", "arm_bf16.h", "arm_vector_types.h"):
        if os.path.exists(os.path.join(inc, h)):
            words += re.findall(r"__builtin_(?:arm|neon|aarch64)_\w+", open(os.path.join(inc, h)).read())
    words = sorted(set(words))
    print(f"{len(words)} candidate words", file=sys.stderr)
    c_tabs = [(0, "__has_builtin", "HAS_BUILTIN"), (1, "__has_feature", "HAS_FEATURE"),
              (2, "__has_extension", "HAS_EXTENSION"), (3, "__has_attribute", "HAS_ATTRIBUTE"),
              (4, "__has_c_attribute", "HAS_C_ATTRIBUTE"), (5, "__has_declspec_attribute", "HAS_DECLSPEC_ATTRIBUTE")]
    cx_tabs = [(0, "__has_builtin", "HAS_CXX_BUILTIN"), (1, "__has_feature", "HAS_CXX_FEATURE"),
               (2, "__has_extension", "HAS_CXX_EXTENSION"), (3, "__has_attribute", "HAS_CXX_ATTRIBUTE"),
               (5, "__has_declspec_attribute", "HAS_CXX_DECLSPEC_ATTRIBUTE"),
               (7, "__has_cpp_attribute", "HAS_CXX_CPP_ATTRIBUTE"), (8, "!__is_identifier", "CXX_KEYWORDS")]
    deltas = {}
    for lang, clang, tabs, path in [("c", a.clang, c_tabs, pc), ("c++", a.clangxx, cx_tabs, pcx)]:
        lines = []
        for k, fn, name in tabs:
            x86 = table(name, path)
            cand = sorted(set(words) | set(x86))
            t = probe(clang, lang, cand, fn, [T])
            for w in sorted(set(t) | set(x86)):
                if t.get(w, 0) != x86.get(w, 0):
                    lines.append(f"{k} {w} {t.get(w, 0)}")
            print(f"{lang} {fn}: {len(lines)} delta lines so far", file=sys.stderr)
        deltas[lang] = lines
    # the C++ standards' table deltas (HAS_CXX_STD_DELTA) must hold on AArch64 too: spot-check builtins
    with open(OUT, "w") as f:
        f.write("// Generated by tools/gen_predef_a64.py from clang-20 / clang++-20 --target=aarch64-linux-gnu.\n")
        f.write("// Do not edit.\n\n")
        f.write(goose_str("PREDEF_A64_BASE", ctext.rstrip("\n")))
        f.write(goose_str("PREDEF_CXX_A64_BASE", xtext.rstrip("\n")))
        f.write(goose_str("A64_MARCH", "\n".join(march_lines)))
        f.write(goose_str("A64_DELTA", "\n".join(deltas["c"])))
        f.write(goose_str("A64_CXX_DELTA", "\n".join(deltas["c++"])))
    print("wrote", OUT, file=sys.stderr)


if __name__ == "__main__":
    main()
