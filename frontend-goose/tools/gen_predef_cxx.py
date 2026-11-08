#!/usr/bin/env python3
"""Generate src/predef_cxx_gen.goose: clang++-20's predefined macros and its
answers to the __has_* operators in C++ mode (milestone D1).

The macro set is `clang++-20 -dM -E -x c++ /dev/null` (gnu++17, -O0, x86_64
linux). Every other -std= is a delta against it (PREDEF_CXX_STD: a line
"=NAME" starts the delta of -std=NAME, then "-MACRO" removes and "+MACRO
VALUE" adds or changes a macro). -fno-exceptions and -fno-rtti remove two
macros each; -O, -pthread, -funsigned-char and -fPIC are the C deltas
(gen_predef.py), and this script checks that they are the same in C++.

The __has_builtin / __has_feature / __has_extension / __has_attribute /
__has_cpp_attribute / __has_declspec_attribute answers are probed from
clang++ over the same candidate words as gen_predef.py (every
identifier-like string in libclang-cpp). __has_feature, __has_extension
and __has_cpp_attribute depend on the standard: the tables hold the
gnu++17 answers, and HAS_CXX_STD_DELTA the differences per standard
("=NAME" then "TABLE WORD VALUE" lines, value 0 = not present).

usage: tools/gen_predef_cxx.py [--clang clang++-20] [--lib /usr/lib/x86_64-linux-gnu/libclang-cpp.so.20.1]
"""
import argparse, os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "src", "predef_cxx_gen.goose")

STDS = ["c++98", "gnu++98", "c++11", "gnu++11", "c++14", "gnu++14", "c++17", "c++20", "gnu++20", "c++23", "gnu++23"]


def run(cmd, inp=None):
    r = subprocess.run(cmd, input=inp, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    return r.stdout.decode(errors="replace"), r.stderr.decode(errors="replace"), r.returncode


def macros(clang, flags):
    out, err, rc = run([clang, "-dM", "-E", "-x", "c++"] + flags + ["/dev/null"])
    assert rc == 0, err
    d = {}
    for line in out.splitlines():
        m = re.match(r"#define (\S+)(?: (.*))?$", line)
        assert m, line
        d[m.group(1)] = m.group(2) or ""
    return out, d


def probe(clang, words, fn, flags=()):
    """{word: value} for fn(word) != 0."""
    lines = []
    for i, w in enumerate(words):
        lines.append(f"#if {fn}({w})\nGOOSECC_YES_{i} = {fn}({w})\n#endif\n")
    with tempfile.NamedTemporaryFile("w", suffix=".cpp", delete=False) as f:
        f.write("".join(lines))
        path = f.name
    try:
        out, err, rc = run([clang, "-E", "-P", "-w", "-x", "c++"] + list(flags) + [path])
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


def delta(base, d):
    out = []
    for k in sorted(base):
        if k not in d:
            out.append(f"-{k}")
    for k in sorted(d):
        if k not in base or d[k] != base[k]:
            out.append(f"+{k} {d[k]}".rstrip() if d[k] else f"+{k}")
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--clang", default="clang++-20")
    ap.add_argument("--lib", default="/usr/lib/x86_64-linux-gnu/libclang-cpp.so.20.1")
    a = ap.parse_args()

    base_text, base = macros(a.clang, [])
    std_lines = []
    for s in STDS:
        _, d = macros(a.clang, ["-std=" + s])
        std_lines.append("=" + s)
        std_lines += delta(base, d)
    # deltas goosecc applies by hand: they must be exactly these
    def check(flags, add, rem):
        _, d = macros(a.clang, flags)
        exp = dict(base)
        for k in rem:
            exp.pop(k, None)
        exp.update(add)
        if d != exp:
            print("delta mismatch for", flags, delta(exp, d), file=sys.stderr)
            sys.exit(1)
    check(["-fno-exceptions"], {}, ["__EXCEPTIONS", "__cpp_exceptions"])
    check(["-fno-rtti"], {}, ["__GXX_RTTI", "__cpp_rtti"])
    check(["-O2"], {"__OPTIMIZE__": "1"}, ["__NO_INLINE__"])
    check(["-Os"], {"__OPTIMIZE__": "1", "__OPTIMIZE_SIZE__": "1"}, ["__NO_INLINE__"])
    check(["-pthread"], {"_REENTRANT": "1"}, [])
    check(["-funsigned-char"], {"__CHAR_UNSIGNED__": "1"}, [])

    out, _, _ = run(["strings", "-n", "3", a.lib])
    words = sorted(set(w for w in out.split("\n") if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", w)))
    print(f"{len(words)} candidate words", file=sys.stderr)
    fns = ["__has_builtin", "__has_feature", "__has_extension", "__has_attribute",
           "__has_cpp_attribute", "__has_declspec_attribute"]
    tables = {}
    for fn in fns:
        tables[fn] = probe(a.clang, words, fn)
        print(f"{fn}: {len(tables[fn])}", file=sys.stderr)
    attrs = sorted(set(tables["__has_attribute"]) | set(tables["__has_cpp_attribute"]))
    scoped = [f"{ns}::{w}" for ns in ["gnu", "clang", "_Clang", "__gnu__", "__clang__", "msvc", "omp"] for w in attrs]
    tables["__has_cpp_attribute"].update(probe(a.clang, scoped, "__has_cpp_attribute"))
    tables["__has_attribute"].update(probe(a.clang, scoped, "__has_attribute"))
    # the standard-dependent tables, per standard
    dep = ["__has_feature", "__has_extension", "__has_cpp_attribute", "__has_builtin"]
    dwords = {fn: sorted(set(tables[fn]) | set(words if fn != "__has_cpp_attribute" else [])) for fn in dep}
    dwords["__has_cpp_attribute"] = sorted(set(tables["__has_cpp_attribute"]) | set(attrs) | set(scoped))
    sdelta = []
    for s in STDS:
        sdelta.append("=" + s)
        for fn in dep:
            t = probe(a.clang, dwords[fn], fn, ["-std=" + s])
            short = fn[len("__has_"):]
            for w in sorted(set(t) | set(tables[fn])):
                if t.get(w, 0) != tables[fn].get(w, 0):
                    sdelta.append(f"{short} {w} {t.get(w, 0)}")
        print(f"std {s}: {len(sdelta)} delta lines so far", file=sys.stderr)

    with open(OUT, "w") as f:
        f.write("// Generated by tools/gen_predef_cxx.py from clang++-20. Do not edit.\n\n")
        f.write(goose_str("PREDEF_CXX_BASE", base_text.rstrip("\n")))
        f.write(goose_str("PREDEF_CXX_STD", "\n".join(std_lines)))
        for fn in fns:
            name = "HAS_CXX_" + fn[len("__has_"):].upper()
            body = "\n".join(f"{k} {v}" for k, v in sorted(tables[fn].items()))
            f.write(goose_str(name, body))
        f.write(goose_str("HAS_CXX_STD_DELTA", "\n".join(sdelta)))
    print("wrote", OUT, file=sys.stderr)


if __name__ == "__main__":
    main()
