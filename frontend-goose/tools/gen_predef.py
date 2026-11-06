#!/usr/bin/env python3
"""Generate src/predef_gen.goose: clang-20's predefined macros and the answers
clang-20 gives to __has_builtin / __has_feature / __has_extension /
__has_attribute / __has_c_attribute / __has_declspec_attribute.

The macro set is `clang-20 -dM -E -x c /dev/null` (gnu17, -O0, x86_64 linux).
goosecc derives the other modes from it (see pp_init in pp.goose):
  -O1.. : -__NO_INLINE__ +__OPTIMIZE__ (+__OPTIMIZE_SIZE__ for -Os/-Oz)
  -std=c89/c99/c11/c17 : __STDC_VERSION__, +__STRICT_ANSI__, -linux -unix
  -std=gnu89 : +__GNUC_GNU_INLINE__ -__GNUC_STDC_INLINE__ -__STDC_VERSION__
  -pthread : +_REENTRANT
This script also checks those deltas against clang.

The __has_* answers are found by probing clang-20 with every identifier-like
string in libclang-cpp (a superset of the builtin, feature and attribute
names it knows). Only non-zero answers are kept.

usage: tools/gen_predef.py [--clang clang-20] [--lib /usr/lib/x86_64-linux-gnu/libclang-cpp.so.20.1]
"""
import argparse, os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "src", "predef_gen.goose")


def run(cmd, inp=None):
    r = subprocess.run(cmd, input=inp, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    return r.stdout.decode(errors="replace"), r.stderr.decode(errors="replace"), r.returncode


def macros(clang, flags):
    out, err, rc = run([clang, "-dM", "-E", "-x", "c"] + flags + ["/dev/null"])
    assert rc == 0, err
    d = {}
    for line in out.splitlines():
        m = re.match(r"#define (\S+)(?: (.*))?$", line)
        assert m, line
        d[m.group(1)] = m.group(2) or ""
    return out, d


def probe(clang, words, fn, scoped=False, flags=()):
    """Return {word: value} for fn(word) != 0."""
    lines = []
    for i, w in enumerate(words):
        lines.append(f"#if {fn}({w})\nGOOSECC_YES_{i} = {fn}({w})\n#endif\n")
    src = "".join(lines)
    with tempfile.NamedTemporaryFile("w", suffix=".c", delete=False) as f:
        f.write(src)
        path = f.name
    try:
        out, err, rc = run([clang, "-E", "-P", "-w", "-x", "c"] + list(flags) + [path])
    finally:
        os.unlink(path)
    res = {}
    for line in out.splitlines():
        m = re.match(r"GOOSECC_YES_(\d+) = (\d+)L?", line.strip())
        if m:
            res[words[int(m.group(1))]] = int(m.group(2))
    return res


def goose_str(name, text):
    assert '"""' not in text
    return f'let {name} = """\n{text}\n""";\n'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--clang", default="clang-20")
    ap.add_argument("--lib", default="/usr/lib/x86_64-linux-gnu/libclang-cpp.so.20.1")
    a = ap.parse_args()

    base_text, base = macros(a.clang, [])
    # Check the deltas goosecc applies.
    def check(flags, add, rem, changed):
        _, d = macros(a.clang, flags)
        exp = dict(base)
        for k in rem:
            exp.pop(k, None)
        exp.update(add)
        exp.update(changed)
        if d != exp:
            print("delta mismatch for", flags, file=sys.stderr)
            for k in sorted(set(d) | set(exp)):
                if d.get(k) != exp.get(k):
                    print("  ", k, d.get(k), exp.get(k), file=sys.stderr)
            sys.exit(1)
    check(["-O2"], {"__OPTIMIZE__": "1"}, ["__NO_INLINE__"], {})
    check(["-Os"], {"__OPTIMIZE__": "1", "__OPTIMIZE_SIZE__": "1"}, ["__NO_INLINE__"], {})
    check(["-pthread"], {"_REENTRANT": "1"}, [], {})
    check(["-std=c99"], {"__STRICT_ANSI__": "1"}, ["linux", "unix"], {"__STDC_VERSION__": "199901L"})
    check(["-std=c11"], {"__STRICT_ANSI__": "1"}, ["linux", "unix"], {"__STDC_VERSION__": "201112L"})
    check(["-std=c17"], {"__STRICT_ANSI__": "1"}, ["linux", "unix"], {})
    check(["-std=c89"], {"__STRICT_ANSI__": "1", "__GNUC_GNU_INLINE__": "1"},
          ["linux", "unix", "__STDC_VERSION__", "__GNUC_STDC_INLINE__"], {})
    check(["-std=gnu89"], {"__GNUC_GNU_INLINE__": "1"}, ["__STDC_VERSION__", "__GNUC_STDC_INLINE__"], {})
    check(["-std=gnu99"], {}, [], {"__STDC_VERSION__": "199901L"})
    check(["-std=gnu11"], {}, [], {"__STDC_VERSION__": "201112L"})

    out, _, _ = run(["strings", "-n", "3", a.lib])
    words = sorted(set(w for w in out.split("\n") if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", w)))
    print(f"{len(words)} candidate words", file=sys.stderr)
    tables = {}
    for fn in ["__has_builtin", "__has_feature", "__has_extension", "__has_attribute",
               "__has_c_attribute", "__has_declspec_attribute"]:
        tables[fn] = probe(a.clang, words, fn)
        print(f"{fn}: {len(tables[fn])}", file=sys.stderr)
    attrs = sorted(set(tables["__has_attribute"]) | set(tables["__has_c_attribute"]))
    for ns in ["gnu", "clang"]:
        sc = probe(a.clang, [f"{ns}::{w}" for w in attrs], "__has_c_attribute")
        tables["__has_c_attribute"].update(sc)
        sc = probe(a.clang, [f"{ns}::{w}" for w in attrs], "__has_attribute")
        tables["__has_attribute"].update(sc)
    # Is __has_cpp_attribute available in C?
    o, _, _ = run([a.clang, "-E", "-P", "-x", "c", "-"], b"#ifdef __has_cpp_attribute\nYES\n#endif\n")
    has_cpp_attr = "YES" in o

    out, _, _ = run([a.clang, "--print-diagnostic-options"])
    warnings = sorted(set(l.strip()[2:] for l in out.splitlines()
                          if l.strip().startswith("-W") and not l.strip().startswith("-Wno-") and len(l.strip()) > 2))
    print(f"warning options: {len(warnings)}", file=sys.stderr)

    with open(OUT, "w") as f:
        f.write("// Generated by tools/gen_predef.py from clang-20. Do not edit.\n\n")
        f.write(goose_str("PREDEF_BASE", base_text.rstrip("\n")))
        f.write(f"let HAS_CPP_ATTRIBUTE_IN_C = {'true' if has_cpp_attr else 'false'};\n")
        for fn, t in tables.items():
            name = "HAS_" + fn[len("__has_"):].upper()
            body = "\n".join(f"{k} {v}" for k, v in sorted(t.items()))
            f.write(goose_str(name, body))
        f.write(goose_str("WARNING_OPTIONS", "\n".join(warnings)))
    print("wrote", OUT, file=sys.stderr)


if __name__ == "__main__":
    main()
