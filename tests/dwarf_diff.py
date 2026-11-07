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
import json
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
            # one code range or several (DW_AT_ranges): the code layout's
            if at in ("DW_AT_low_pc", "DW_AT_ranges"):
                at = "DW_AT_code"
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


def compile_pair(f, flags, work, goosecc, cache, tag=""):
    base = os.path.join(work, tag + os.path.basename(f))
    co, go = base + ".clang.o", base + ".goosecc.o"
    r1 = subprocess.run(["clang-20", "-O0", "-g", "-w", "-c"] + flags + [f, "-o", co], stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE)
    env = dict(os.environ)
    if cache:
        env["GOOSECC_CACHE"] = cache
    r2 = subprocess.run([goosecc, "-g", "-w", "-c"] + flags + [f, "-o", go], stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE, env=env)
    if r1.returncode:
        return None, "clang failed"
    if r2.returncode:
        return None, "goosecc failed: " + r2.stderr.decode(errors="replace").strip().split("\n")[-1][:200]
    return (co, go), ""


def verify(obj):
    r = subprocess.run(["llvm-dwarfdump-20", "--verify", obj], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    out = r.stdout.decode(errors="replace")
    ok = r.returncode == 0 and "No errors." in out
    return ok, "" if ok else "\n".join(l for l in out.splitlines() if "error" in l.lower() or "warning" in l.lower())[:500]


LOC_RE = re.compile(r"location=(LOCLIST|DW_OP_breg7 RSP[+-]\d+|DW_OP_breg5 RDI\+0|DW_OP_fbreg(, DW_OP_deref)?)( |$)")


def relax(lines):
    """Frame locations of either form (an offset from the frame base, from the
    stack pointer, a location list, a pointer kept in a slot) as LOC: where
    the two compilers' code differs (VLAs, the return slot, realigned frames)."""
    return [LOC_RE.sub(r"location=LOC\3", l) for l in lines]


def subtrees(lines):
    """The children of the unit as text blocks (a DIE with its subtree)."""
    out = []
    cur = None
    for l in lines[1:]:
        if l.startswith("  ") and not l.startswith("   "):
            if cur is not None:
                out.append("\n".join(cur))
            cur = [l]
        elif cur is not None:
            cur.append(l)
    if cur is not None:
        out.append("\n".join(cur))
    return out


def compare_lines(x, y):
    """(strict equal, equal with frame locations relaxed, equal as an unordered
    set of the unit's children with locations relaxed)."""
    if x == y:
        return True, True, True
    rx, ry = relax(x), relax(y)
    if rx == ry:
        return False, True, True
    return False, False, collections.Counter(subtrees(rx)) == collections.Counter(subtrees(ry)) and rx[:1] == ry[:1]


def items_of(a, flags):
    items = [(f, list(flags)) for f in a.files]
    if a.corpus:
        sys.path.insert(0, os.path.join(ROOT, "frontend-goose", "tests"))
        import corpus
        only = None
        if a.only:
            # a --json report: its files that were not the same
            only = {f["file"] for f in json.load(open(a.only))["files"] if not f["status"].startswith("same")}
        for c, p, fl in corpus.corpus(a.corpus.split(",")):
            if only is None or p in only:
                items.append((p, fl + list(flags)))
    if a.every > 1:
        items = items[::a.every]
    if a.limit:
        items = items[:a.limit]
    return items


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dump", action="store_true")
    ap.add_argument("--cc", action="store_true", help="the arguments are C files: compile them with both compilers")
    ap.add_argument("--corpus", default="", help="also the files of these corpora (frontend-goose/tests/corpus.py)")
    ap.add_argument("--every", type=int, default=1, help="every N-th file only")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--only", default="", help="with --corpus: only the files a --json report has as differing")
    ap.add_argument("--verify", action="store_true", help="llvm-dwarfdump --verify every goosecc object")
    ap.add_argument("--goosecc", default=os.path.join(ROOT, "frontend-goose", "build", "goosecc"))
    ap.add_argument("--cache", default=os.environ.get("GOOSECC_CACHE", ""))
    ap.add_argument("--work", default="")
    ap.add_argument("--keep", action="store_true", help="keep the objects of identical files")
    ap.add_argument("--json", default="")
    ap.add_argument("-j", type=int, default=2)
    ap.add_argument("--show", type=int, default=40, help="lines of diff to print per file (0: none)")
    ap.add_argument("-q", action="store_true", help="print only differing files")
    ap.add_argument("-U", type=int, default=1)
    ap.add_argument("--positions", action="store_true", help="print references as the target's position")
    ap.add_argument("files", nargs="*")
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
    if not a.cc and not a.corpus:
        x, y = dump(a.files[0]), dump(a.files[1])
        d = diff(x, y, a.files[0], a.files[1], a.U)
        print("\n".join(d))
        return 1 if d else 0
    work = a.work or tempfile.mkdtemp(prefix="dwarf_diff_")
    os.makedirs(work, exist_ok=True)
    items = items_of(a, flags)
    tot = collections.Counter()
    st = collections.Counter()
    nv = nverr = 0
    results = []

    def one(it):
        f, fl = it
        tag = "%x_" % (hash(f) & 0xFFFFFF)
        p, why = compile_pair(f, fl, work, a.goosecc, a.cache, tag)
        if not p:
            return f, None, None, why, None
        v = verify(p[1]) if a.verify else None
        x, y = dump(p[0]), dump(p[1])
        if x == y and not a.keep:
            for o in p:
                os.unlink(o)
        return f, x, y, "", v
    with cf.ThreadPoolExecutor(max_workers=a.j) as ex:
        for f, x, y, why, v in ex.map(one, items):
            name = os.path.relpath(f, os.path.commonpath([f, ROOT])) if f.startswith(ROOT) else f
            if v is not None:
                nv += 1
                if not v[0]:
                    nverr += 1
                    print("%s: VERIFY FAILED\n%s" % (name, v[1]))
            if x is None:
                st["error"] += 1
                print("%s: %s" % (name, why))
                results.append({"file": f, "status": "error", "why": why})
                continue
            strict, rel, unord = compare_lines(x, y)
            status = "same" if strict else "same-loc" if rel else "same-unordered" if unord else "diff"
            st[status] += 1
            rec = {"file": f, "status": status, "dies": [len(x), len(y)]}
            if strict:
                if not a.q:
                    print("%s: same (%d DIEs)" % (name, len(x)))
                results.append(rec)
                continue
            c = summarize(relax(x), relax(y)) if rel or unord else summarize(x, y)
            if not rel:
                tot.update(c)
            rec["kinds"] = dict(c)
            results.append(rec)
            print("%s: %s, %d vs %d DIEs%s" % (name, status, len(x), len(y),
                                              (", " + ", ".join("%s %d" % kv for kv in c.most_common(8))) if c else ""))
            if a.show and status == "diff":
                print("\n".join(diff(x, y, "clang", "goosecc", a.U)[:a.show]))
    n = sum(st.values())
    print("\n%d files: %d identical, %d identical but for frame-location forms, %d identical as unordered sets, "
          "%d differing, %d not compiled" % (n, st["same"], st["same-loc"], st["same-unordered"], st["diff"], st["error"]))
    if tot:
        print("differing lines (diff only): %s" % ", ".join("%s %d" % kv for kv in tot.most_common(24)))
    if a.verify:
        print("llvm-dwarfdump --verify: %d objects, %d failed" % (nv, nverr))
    if a.json:
        json.dump({"summary": dict(st), "verified": nv, "verify_failed": nverr, "files": results}, open(a.json, "w"), indent=1)
    return 0 if st["same"] == n else 1


if __name__ == "__main__":
    sys.exit(main())
