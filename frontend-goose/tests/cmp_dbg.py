#!/usr/bin/env python3
"""Debug locations of `goosecc -g` against clang-20's.

For each file: `clang-20 -O0 -g -emit-llvm` and `goovm-llc --dump-gir` give
clang's GIR with the line:col of every instruction; `goosecc --emit-gir -g`
gives goosecc's. The instructions of each function (allocas left out) are
aligned by opcode (difflib), and the locations of the aligned instructions
are compared: same line, and same line and column.

usage: frontend-goose/tests/cmp_dbg.py [--goosecc PATH] [--goovm-llc PATH] [--show N] file.c... [-- flags]
"""
import argparse, collections, difflib, os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))


def parse(text):
    funcs = {}
    cur = None
    for line in text.splitlines():
        m = re.match(r'func \d+ @(\S+)\(', line)
        if m:
            cur = funcs.setdefault(m.group(1), [])
            continue
        if cur is None:
            continue
        m = re.match(r'\s+%\d+ = (\w+)(.*?)(?:  !(\d+):(\d+))?$', line)
        if m and m.group(1) != 'alloca':
            loc = (int(m.group(3)), int(m.group(4))) if m.group(3) else None
            cur.append((m.group(1), loc, line.strip()))
    return funcs


def compare(f, flags, a, work, show):
    bc = os.path.join(work, os.path.basename(f) + '.bc')
    subprocess.run([a.clang, '-O0', '-g', '-w', '-c', '-emit-llvm'] + flags + [f, '-o', bc], check=True)
    ref = subprocess.run([a.goovm_llc, '--dump-gir', bc, '-o', os.devnull], stdout=subprocess.PIPE, check=True).stdout
    got = subprocess.run([a.goosecc, '--emit-gir', '-g', '-w'] + flags + [f], stdout=subprocess.PIPE, check=True).stdout
    R, G = parse(ref.decode()), parse(got.decode())
    tot = same_line = same = 0
    bad = collections.Counter()
    for name, ri in R.items():
        gi = G.get(name)
        if gi is None:
            continue
        sm = difflib.SequenceMatcher(None, [x[0] for x in ri], [x[0] for x in gi], autojunk=False)
        for i, j, n in sm.get_matching_blocks():
            for k in range(n):
                r, g = ri[i + k], gi[j + k]
                tot += 1
                if r[1] == g[1]:
                    same += 1
                    same_line += 1
                    continue
                if r[1] and g[1] and r[1][0] == g[1][0]:
                    same_line += 1
                bad[r[0]] += 1
                if show[0] > 0:
                    show[0] -= 1
                    print('  %s: clang %s, goosecc %s: %s' % (name, r[1], g[1], g[2][:80]))
    print('%s: %d instructions aligned, same line %.1f%%, same line:col %.1f%%%s' % (
        os.path.basename(f), tot, 100.0 * same_line / max(tot, 1), 100.0 * same / max(tot, 1),
        ('; differing: ' + ', '.join('%s %d' % kv for kv in bad.most_common(6))) if bad else ''))
    return tot, same_line, same


def main():
    argv = sys.argv[1:]
    flags = []
    if '--' in argv:
        k = argv.index('--')
        argv, flags = argv[:k], argv[k + 1:]
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--goosecc', default=os.path.join(HERE, '..', 'build', 'goosecc'))
    ap.add_argument('--goovm-llc', dest='goovm_llc', default=os.path.join(ROOT, 'build', 'tools', 'goovm-llc', 'goovm-llc'))
    ap.add_argument('--clang', default='clang-20')
    ap.add_argument('--show', type=int, default=0, help='print the first N differences')
    ap.add_argument('files', nargs='+')
    a = ap.parse_args(argv)
    work = tempfile.mkdtemp(prefix='cmp_dbg_')
    T = [0, 0, 0]
    show = [a.show]
    for f in a.files:
        r = compare(f, flags, a, work, show)
        T = [x + y for x, y in zip(T, r)]
    if len(a.files) > 1:
        print('total: %d instructions, same line %.1f%%, same line:col %.1f%%' % (
            T[0], 100.0 * T[1] / max(T[0], 1), 100.0 * T[2] / max(T[0], 1)))


if __name__ == '__main__':
    main()
