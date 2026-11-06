#!/usr/bin/env python3
"""Compare `goosecc -E` with `clang-20 -E` token by token.

Line markers (# N "file" ...) and whitespace are ignored; everything else,
#pragma lines included, must be the same token sequence.

usage: tests/cmp_E.py [--goosecc build/goosecc] [-j 3] [--corpus torture,unit,...]
                      [--show N] [--out results.txt] [files... -- flags]
With file arguments, compares just those (using the flags after --).
"""
import argparse, concurrent.futures as cf, os, re, subprocess, sys, collections

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import corpus as corpus_mod

PUNCTS = sorted("""%:%: ... <<= >>= -> ++ -- << >> <= >= == != && || *= /= %= += -= &= ^= |= ## <: :> <% %> %:
[ ] ( ) { } . & * + - ~ ! / % < > ^ | ? : ; = , #""".split(), key=len, reverse=True)
IDSTART = re.compile(r"[A-Za-z_$\x80-￿]")
IDENT = re.compile(r"[A-Za-z0-9_$\x80-￿]*")
MARKER = re.compile(r"^\s*#\s*(\d+|line)\b")


def tokenize(text):
    toks = []
    for line in text.split("\n"):
        if MARKER.match(line):
            continue
        i, n = 0, len(line)
        while i < n:
            c = line[i]
            if c in " \t\r\f\v":
                i += 1
                continue
            # string / char with prefix
            m = re.match(r"(u8|u|U|L)?(\"|')", line[i:])
            if m:
                q = m.group(2)
                j = i + m.end()
                while j < n and line[j] != q:
                    j += 2 if line[j] == "\\" else 1
                j = min(j + 1, n)
                toks.append(line[i:j])
                i = j
                continue
            if IDSTART.match(c):
                j = i + 1 + IDENT.match(line, i + 1).end() - (i + 1)
                toks.append(line[i:j])
                i = j
                continue
            if c.isdigit() or (c == "." and i + 1 < n and line[i + 1].isdigit()):
                j = i + 1
                while j < n:
                    if line[j] in "eEpP" and j + 1 < n and line[j + 1] in "+-":
                        j += 2
                    elif line[j].isalnum() or line[j] in "._$":
                        j += 1
                    else:
                        break
                toks.append(line[i:j])
                i = j
                continue
            for p in PUNCTS:
                if line.startswith(p, i):
                    toks.append(p)
                    i += len(p)
                    break
            else:
                toks.append(c)
                i += 1
    return toks


def run(cmd, env=None):
    r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env)
    return r.returncode, r.stdout.decode("utf-8", "surrogateescape"), r.stderr.decode("utf-8", "replace")


ENV = dict(os.environ, SOURCE_DATE_EPOCH="1700000000", TZ="UTC")


def compare(goosecc, path, flags, clang="clang-20"):
    rc, ref, err = run([clang, "-E"] + flags + [path], ENV)
    if rc != 0:
        return "clang-error", err.strip().splitlines()[-1:] if err.strip() else ""
    rc2, got, err2 = run([goosecc, "-E"] + flags + [path], ENV)
    if rc2 != 0 and not got:
        return "goosecc-error", (err2.strip().splitlines() or ["rc=%d" % rc2])[0]
    a, b = tokenize(ref), tokenize(got)
    if a == b:
        return ("same" if rc2 == 0 else "same-but-rc"), (err2.strip().splitlines() or [""])[0]
    k = 0
    while k < min(len(a), len(b)) and a[k] == b[k]:
        k += 1
    ctx = "clang: %s\n      goosecc: %s" % (" ".join(a[max(0, k - 8):k + 8]), " ".join(b[max(0, k - 8):k + 8]))
    return "diff", "token %d of %d/%d\n      %s" % (k, len(a), len(b), ctx)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--goosecc", default=os.path.join(HERE, "..", "build", "goosecc"))
    ap.add_argument("-j", type=int, default=3)
    ap.add_argument("--corpus", default="")
    ap.add_argument("--show", type=int, default=20)
    ap.add_argument("--out", default="")
    ap.add_argument("--extra", default="", help="extra flags for every file (space separated)")
    ap.add_argument("rest", nargs="*")
    argv, cli_flags = corpus_mod.split_flags(sys.argv[1:])
    a = ap.parse_args(argv)
    extra = a.extra.split()
    if a.rest:
        files, flags = a.rest, cli_flags
        jobs = [("args", f, flags) for f in files]
    else:
        jobs = list(corpus_mod.corpus([c for c in a.corpus.split(",") if c]))
    jobs = [(c, p, fl + extra) for c, p, fl in jobs]
    with cf.ThreadPoolExecutor(a.j) as ex:
        res = list(ex.map(lambda j: (j, compare(a.goosecc, j[1], j[2])), jobs))
    by = collections.defaultdict(collections.Counter)
    shown = 0
    lines = []
    for (c, p, fl), (st, msg) in res:
        by[c][st] += 1
        if st not in ("same", "clang-error"):
            lines.append("%s %s: %s\n      %s" % (st, p, " ".join(fl), msg))
    for l in lines:
        if shown < a.show:
            print(l)
            shown += 1
    print()
    for c, cnt in by.items():
        tot = sum(cnt.values())
        ok = cnt["same"]
        print("%-8s files %5d  clang-ok %5d  identical %5d  %s" % (c, tot, tot - cnt["clang-error"], ok,
              dict((k, v) for k, v in cnt.items() if k not in ("same",))))
    if a.out:
        with open(a.out, "w") as f:
            f.write("\n".join(lines) + "\n")
            for c, cnt in by.items():
                f.write("%s %s\n" % (c, dict(cnt)))


if __name__ == "__main__":
    main()
