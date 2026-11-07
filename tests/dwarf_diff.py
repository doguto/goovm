#!/usr/bin/env python3
"""The DWARF of two objects (`llvm-dwarfdump --debug-info`), normalized and compared.

The DIE trees are printed one DIE per line, with what depends on the code
or on the object layout normalized:
  - DIE offsets and references: references name the target DIE by its
    position in the tree (#N) and print its name, as llvm-dwarfdump does;
  - code addresses (low_pc/high_pc, ranges) become CODE;
  - frame offsets (DW_OP_fbreg N) become fbreg (the frame layouts differ),
    DW_OP_addrx N addrx, location lists LOCLIST;
  - the producer, the section offsets (str_offsets/addr/rnglists/loclists
    bases, stmt_list) are dropped.

usage:
  tests/dwarf_diff.py a.o b.o              print the differences (unified, normalized)
  tests/dwarf_diff.py --dump a.o           print the normalized tree
  tests/dwarf_diff.py --pairs DIR          compare DIR/*.clang.o with DIR/*.goosecc.o, summarize
  tests/dwarf_diff.py --cc ... file.c ...  compile each file with clang-20 -O0 -g and goosecc -g, compare
Exit status 0 iff no difference.
"""
import argparse
import collections
import concurrent.futures as cf
import difflib
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

DIE_RE = re.compile(r'^(0x[0-9a-f]+):(\s+)(DW_TAG_\w+|NULL)\s*$')
ATTR_RE = re.compile(r'^\s+(DW_AT_\w+)\s+\((.*)\)\s*$')
ATTR_OPEN_RE = re.compile(r'^\s+(DW_AT_\w+)\s+\((.*)$')
DROP = {"DW_AT_str_offsets_base", "DW_AT_addr_base", "DW_AT_rnglists_base", "DW_AT_loclists_base",
        "DW_AT_stmt_list", "DW_AT_high_pc"}


class Die:
    __slots__ = ("off", "tag", "attrs", "kids", "depth", "idx", "parent")

    def __init__(self, off, tag, depth):
        self.off = off
        self.tag = tag
        self.attrs = []
        self.kids = []
        self.depth = depth
        self.idx = -1
        self.parent = None


def parse(text):
    """The DIE trees of every unit: a list of root DIEs."""
    roots = []
    stack = []
    cur = None
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        l = lines[i]
        i += 1
        m = DIE_RE.match(l)
        if m:
            depth = len(m.group(2))
            tag = m.group(3)
            if tag == "NULL":
                if stack:
                    stack.pop()
                cur = None
                continue
            d = Die(int(m.group(1), 16), tag, depth)
            while stack and stack[-1].depth >= depth:
                stack.pop()
            if stack:
                d.parent = stack[-1]
                stack[-1].kids.append(d)
            else:
                roots.append(d)
            stack.append(d)
            cur = d
            continue
        if cur is None:
            continue
        m = ATTR_OPEN_RE.match(l)
        if m:
            # the value runs to the next attribute or DIE (location lists and
            # range lists continue on lines of their own); a type name may
            # hold unbalanced parentheses ("int (*[3])(int)")
            val = [m.group(2).rstrip()]
            while i < len(lines) and lines[i].strip() and not DIE_RE.match(lines[i]) and \
                    not re.match(r"^\s+DW_AT_\w+\s+\(", lines[i]):
                val.append(lines[i].strip())
                i += 1
            v = " ".join(val)
            if v.endswith(")"):
                v = v[:-1]
            cur.attrs.append((m.group(1), v))
    return roots


def number(roots):
    byoff = {}
    order = []

    def walk(d):
        d.idx = len(order)
        order.append(d)
        byoff[d.off] = d
        for k in d.kids:
            walk(k)
    for r in roots:
        walk(r)
    return byoff, order


REF_RE = re.compile(r'^0x([0-9a-f]{8})(?: (".*"))?$')
POSITIONS = False   # --positions: references as #N (the target's position in the tree)


def norm_attr(at, val, byoff):
    if at in DROP:
        return None
    if at == "DW_AT_producer":
        return "PRODUCER"
    if at in ("DW_AT_decl_file", "DW_AT_call_file", "DW_AT_comp_dir"):
        # the same paths in both; shortened for reading
        return '"%s"' % os.path.basename(val.strip('"'))
    if at in ("DW_AT_low_pc", "DW_AT_ranges"):
        return "CODE"
    m = REF_RE.match(val)
    if m and at in ("DW_AT_type", "DW_AT_count", "DW_AT_upper_bound", "DW_AT_lower_bound", "DW_AT_abstract_origin",
                    "DW_AT_specification", "DW_AT_import", "DW_AT_containing_type", "DW_AT_object_pointer",
                    "DW_AT_sibling", "DW_AT_data_location"):
        t = byoff.get(int(m.group(1), 16))
        if t is None:
            return "->?"
        if POSITIONS:
            return "#%s %s" % (t.idx, m.group(2) or "")
        # by what the target is: its tag and name (llvm-dwarfdump's spelling
        # of a type), so that one DIE more or less does not renumber the rest
        nm = m.group(2)
        if not nm:
            nm = next((v for a, v in t.attrs if a == "DW_AT_name"), "")
        return "->%s %s" % (t.tag[7:], nm)
    if at == "DW_AT_location" or at == "DW_AT_frame_base":
        if "loclist" in val:
            return "LOCLIST"
        val = re.sub(r"DW_OP_fbreg [+-]?\d+", "DW_OP_fbreg", val)
        val = re.sub(r"DW_OP_addrx 0x[0-9a-f]+", "DW_OP_addrx", val)
        val = re.sub(r"DW_OP_const8u 0x[0-9a-f]+", "DW_OP_const8u", val)
        return val
    return val


def lines_of(roots):
    byoff, order = number(roots)
    out = []
    for d in order:
        depth = 0
        p = d.parent
        while p is not None:
            depth += 1
            p = p.parent
        attrs = []
        for at, val in d.attrs:
            v = norm_attr(at, val, byoff)
            if v is None:
                continue
            attrs.append("%s=%s" % (at[6:], v))
        out.append("%s%s %s" % ("  " * depth, d.tag[7:], " ".join(attrs)))
    return out


def dump(obj):
    r = subprocess.run(["llvm-dwarfdump-20", "--debug-info", obj], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if r.returncode:
        raise RuntimeError("llvm-dwarfdump failed on %s: %s" % (obj, r.stderr.decode(errors="replace")[:200]))
    return lines_of(parse(r.stdout.decode(errors="replace")))


def diff(a, b, na="clang", nb="goosecc", ctx=1):
    return list(difflib.unified_diff(a, b, na, nb, n=ctx, lineterm=""))


def kind_of_line(l):
    """A short category for a differing line: the DIE tag and the attribute names."""
    s = l.strip()
    tag = s.split(" ", 1)[0]
    return tag


def summarize(ra, rb):
    """Counts of differing lines by tag, each side."""
    sm = difflib.SequenceMatcher(None, ra, rb, autojunk=False)
    c = collections.Counter()
    for op, a0, a1, b0, b1 in sm.get_opcodes():
        if op == "equal":
            continue
        for l in ra[a0:a1]:
            c["-" + kind_of_line(l)] += 1
        for l in rb[b0:b1]:
            c["+" + kind_of_line(l)] += 1
    return c


def compile_pair(f, flags, work, goosecc, cache):
    base = os.path.join(work, os.path.basename(f))
    co, go = base + ".clang.o", base + ".goosecc.o"
    r1 = subprocess.run(["clang-20", "-O0", "-g", "-w", "-c"] + flags + [f, "-o", co], stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE)
    env = dict(os.environ)
    if cache:
        env["GOOSECC_CACHE"] = cache
    r2 = subprocess.run([goosecc, "-g", "-w", "-c"] + flags + [f, "-o", go], stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE, env=env)
    if r1.returncode or r2.returncode:
        return None
    return co, go


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dump", action="store_true")
    ap.add_argument("--cc", action="store_true", help="the arguments are C files: compile them with both compilers")
    ap.add_argument("--goosecc", default=os.path.join(ROOT, "frontend-goose", "build", "goosecc"))
    ap.add_argument("--cache", default=os.environ.get("GOOSECC_CACHE", ""))
    ap.add_argument("--work", default="")
    ap.add_argument("-j", type=int, default=2)
    ap.add_argument("--show", type=int, default=40, help="lines of diff to print per file (0: none)")
    ap.add_argument("-U", type=int, default=1)
    ap.add_argument("--positions", action="store_true", help="print references as the target's position")
    ap.add_argument("files", nargs="+")
    argv = sys.argv[1:]
    flags = []
    if "--" in argv:
        k = argv.index("--")
        argv, flags = argv[:k], argv[k + 1:]
    a = ap.parse_args(argv)
    global POSITIONS
    POSITIONS = a.positions
    if a.dump:
        for f in a.files:
            print("\n".join(dump(f)))
        return 0
    if not a.cc:
        x, y = dump(a.files[0]), dump(a.files[1])
        d = diff(x, y, a.files[0], a.files[1], a.U)
        print("\n".join(d))
        return 1 if d else 0
    work = a.work or tempfile.mkdtemp(prefix="dwarf_diff_")
    os.makedirs(work, exist_ok=True)
    tot = collections.Counter()
    same = 0
    n = 0

    def one(f):
        p = compile_pair(f, flags, work, a.goosecc, a.cache)
        if not p:
            return f, None, None
        x, y = dump(p[0]), dump(p[1])
        return f, x, y
    with cf.ThreadPoolExecutor(max_workers=a.j) as ex:
        for f, x, y in ex.map(one, a.files):
            if x is None:
                print("%s: compile failed" % f)
                continue
            n += 1
            d = diff(x, y, "clang", "goosecc", a.U)
            if not d:
                same += 1
                print("%s: same (%d DIEs)" % (os.path.basename(f), len(x)))
                continue
            c = summarize(x, y)
            tot.update(c)
            print("%s: %d vs %d DIEs, %s" % (os.path.basename(f), len(x), len(y),
                                            ", ".join("%s %d" % kv for kv in c.most_common(8))))
            if a.show:
                print("\n".join(d[:a.show]))
    if n > 1:
        print("\n%d/%d files identical; differing lines: %s" % (same, n, ", ".join("%s %d" % kv for kv in tot.most_common(20))))
    return 0 if same == n else 1


if __name__ == "__main__":
    sys.exit(main())
