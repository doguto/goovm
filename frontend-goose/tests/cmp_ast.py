#!/usr/bin/env python3
"""The AST oracle: compares goosecc's expression trees with clang-20's.

For every function body (and file-scope initializer) both compilers see,
the trees are walked in parallel. Node kinds, types (clang's canonical
spelling) and cast kinds must agree, so the implicit conversions goosecc
makes explicit are the ones clang makes. ParenExpr and ConstantExpr are
transparent; the representation differences that are not semantic are
normalized in from_clang() and compare() (each one says why). Types that
clang prints with typedef sugar below the top level are not compared.

Files over --max-bytes (default 4 MB) are skipped: clang's JSON dump is
about 100 times the source (277 MB for sqlite3.c, which takes a minute and
a few GB of memory here).

usage: tests/cmp_ast.py [--goosecc build/goosecc] [-j 3] [--corpus ...] [--show N]
                        [--max-bytes N] [--hist] [--grep RE] [files... -- flags]
"""
import argparse, collections, concurrent.futures as cf, json, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import corpus as corpus_mod

ENV = dict(os.environ, SOURCE_DATE_EPOCH="1700000000", TZ="UTC")


class N:
    __slots__ = ("kind", "type", "extra", "kids")

    def __init__(self, kind, type_, extra=""):
        self.kind, self.type, self.extra, self.kids = kind, type_, extra, []


def strip_param_quals(s):
    """Top-level qualifiers of function parameters are not part of the type."""
    s = re.sub(r"\*\s*(?:const|restrict|volatile)(?:\s+(?:const|restrict|volatile))*(?=[,)])", "*", s)
    s = re.sub(r"(?<=[(,] )(?:const |volatile )+(?=[A-Za-z_ ]+[,)])", "", s)
    s = re.sub(r"(?<=\()(?:const |volatile )+(?=[A-Za-z_ ]+[,)])", "", s)
    return s


def norm_type(t):
    t = re.sub(r"[A-Za-z_][A-Za-z0-9_]*::(?=\((?:unnamed|anonymous))", "", t)
    t = re.sub(r"\((?:unnamed|anonymous)(?: struct| union| enum)? at [^)]*\)", r"(anonymous)", t)
    t = t.replace("__restrict", "restrict")
    t = re.sub(r"\bbool\b", "_Bool", t)
    # clang prints a decayed parameter type T *[] as T *(*)
    t = re.sub(r" ?\(\*\)$", "*", t) if t.endswith("*(*)") else t
    t = t.replace(" __attribute__((noreturn))", "")
    t = strip_param_quals(t)
    if re.search(r"\[[^\]0-9]", t):
        t = "<vla>"
    return t


def clang_type(n):
    t = n.get("type")
    if not t:
        return "-"
    return norm_type(t.get("desugaredQualType", t.get("qualType", "-")))


CAST = {"FloatingRealToComplex": "RealToComplex", "IntegralRealToComplex": "RealToComplex",
        "FloatingComplexToReal": "ComplexToReal", "IntegralComplexToReal": "ComplexToReal",
        "FloatingComplexCast": "ComplexCast", "IntegralComplexCast": "ComplexCast",
        "FloatingComplexToIntegralComplex": "ComplexCast", "IntegralComplexToFloatingComplex": "ComplexCast",
        "FloatingComplexToBoolean": "ComplexToReal", "IntegralComplexToBoolean": "ComplexToReal",
        "NonAtomicToAtomic": "AtomicConversion", "AtomicToNonAtomic": "AtomicConversion"}


def from_clang(n):
    """clang JSON node -> N (or None to drop)."""
    k = n.get("kind")
    inner = [c for c in n.get("inner", []) if c]
    if k in ("ParenExpr", "ConstantExpr", "FullExpr", "ExprWithCleanups"):
        return from_clang(inner[0]) if inner else None
    if k == "DeclStmt":
        r = N("DeclGroup", "-")
        for c in inner:
            if c.get("kind") == "VarDecl":
                v = N("VarDecl", norm_type((c.get("type") or {}).get("desugaredQualType", (c.get("type") or {}).get("qualType", "-"))), c.get("name", ""))
                for ic in c.get("inner", []):
                    ik = ic.get("kind", "")
                    if not (ik.endswith("Attr") or ik.endswith("Comment") or ik.endswith("Decl")):
                        x = from_clang(ic)
                        if x:
                            v.kids.append(x)
                r.kids.append(v)
        return r
    if k == "PredefinedExpr":
        return N("StringLiteral", clang_type(n))
    if k == "TypeTraitExpr":
        # __builtin_types_compatible_p: goosecc folds it
        return N("IntegerLiteral", clang_type(n))
    if k == "BinaryOperator" and n.get("opcode") == "+" and len(inner) == 2:
        # goosecc puts the pointer operand of integer + pointer first
        t0, t1 = clang_type(inner[0]), clang_type(inner[1])
        if not ("*" in t0 or "[" in t0) and ("*" in t1 or "[" in t1):
            inner = [inner[1], inner[0]]
            n = dict(n, inner=inner)
    if k == "ChooseExpr":
        return N("ChooseExpr", "-")
    if k == "DeclRefExpr" and (n.get("referencedDecl") or {}).get("kind") == "EnumConstantDecl":
        return N("IntegerLiteral", clang_type(n))
    if k == "CharacterLiteral":
        return N("IntegerLiteral", clang_type(n))
    extra = ""
    if k == "ImplicitCastExpr" and n.get("castKind") == "BitCast" and inner and clang_type(n) == clang_type(inner[0]):
        # e.g. dropping noreturn from a function pointer type: goosecc's
        # function types do not carry noreturn
        return from_clang(inner[0])
    if k == "ImplicitCastExpr" or k == "CStyleCastExpr":
        extra = CAST.get(n.get("castKind", ""), n.get("castKind", ""))
    elif k in ("BinaryOperator", "UnaryOperator"):
        extra = n.get("opcode", "")
        if k == "UnaryOperator" and extra in ("__extension__",):
            return from_clang(inner[0])
    elif k == "CompoundAssignOperator":
        extra = norm_type((n.get("computeResultType") or {}).get("desugaredQualType", (n.get("computeResultType") or {}).get("qualType", "")))
    elif k == "DeclRefExpr":
        extra = (n.get("referencedDecl") or {}).get("name", "")
    elif k == "MemberExpr":
        extra = ("->" if n.get("isArrow") else ".") + n.get("name", "")
    r = N(k, clang_type(n), extra)
    if k in ("UnaryExprOrTypeTraitExpr", "StmtExpr", "VAArgExpr", "BinaryConditionalOperator", "OffsetOfExpr",
             "AddrLabelExpr", "GCCAsmStmt", "GotoStmt", "IndirectGotoStmt", "BreakStmt", "ContinueStmt", "NullStmt",
             "StringLiteral", "IntegerLiteral", "FloatingLiteral", "ImaginaryLiteral", "PredefinedExpr",
             "ImplicitValueInitExpr", "ShuffleVectorExpr", "ConvertVectorExpr", "ChooseExpr", "GenericSelectionExpr",
             "AtomicExpr", "BuiltinBitCastExpr", "SourceLocExpr"):
        return r
    if k == "InitListExpr":
        kids = inner
        # clang lists the filler separately ("array_filler"): not compared
        for c in kids:
            x = from_clang(c)
            if x:
                r.kids.append(x)
        return r
    if k == "CallExpr" and inner:
        callee = inner[0]
        while callee.get("kind") in ("ParenExpr",):
            callee = callee["inner"][0]
        if callee.get("kind") == "ImplicitCastExpr" and callee.get("castKind") == "BuiltinFnToFnPtr":
            r.kind = "BuiltinCall"
            r.extra = ((callee.get("inner") or [{}])[0].get("referencedDecl") or {}).get("name", "")
            # clang names the sized variant of a __sync builtin
            r.extra = re.sub(r"^(__sync_\w+?)_(?:1|2|4|8|16)$", r"\1", r.extra)
            inner = inner[1:]
            if r.extra in ("__builtin_classify_type", "__builtin_constant_p"):
                return N("IntegerLiteral", r.type)
    if k == "ArraySubscriptExpr" and len(inner) == 2:
        # goosecc puts the pointer first
        t0 = clang_type(inner[0])
        if not ("*" in t0 or "[" in t0) and ("*" in clang_type(inner[1]) or "[" in clang_type(inner[1])):
            inner = [inner[1], inner[0]]
    if k == "ForStmt":
        # init, condVar, cond, inc, body: absent parts are {} in the JSON
        parts = n.get("inner", [])
        if len(parts) == 5:
            parts = [parts[0], parts[2], parts[3], parts[4]]
        for c in parts:
            x = from_clang(c) if c else None
            r.kids.append(x if x else N("<null>", "-"))
        return r
    if k == "CaseStmt":
        # the value(s) are not compared (a GNU range has two)
        r.kids = [x for x in (from_clang(c) for c in inner[-1:]) if x]
        return r
    if k == "LabelStmt":
        r.extra = ""
    for c in inner:
        x = from_clang(c)
        if x:
            r.kids.append(x)
    return r


def clang_funcs(path, flags):
    r = subprocess.run(["clang-20", "-fsyntax-only", "-w", "-Xclang", "-ast-dump=json"] + flags + [path],
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=ENV)
    if r.returncode != 0:
        return None
    d = json.loads(r.stdout)
    out = {}
    todo = [d]
    while todo:
        n = todo.pop()
        if n.get("kind") == "TypedefDecl":
            TYPEDEFS.add(n.get("name", ""))
        elif n.get("kind", "").endswith(("Stmt", "Decl")):
            todo.extend(c for c in n.get("inner", []) if c)
    for n in d.get("inner", []):
        if n.get("kind") == "FunctionDecl" and n.get("inner"):
            body = [c for c in n["inner"] if c.get("kind") == "CompoundStmt"]
            if body:
                out["F " + n["name"]] = from_clang(body[0])
        elif n.get("kind") == "VarDecl" and n.get("inner") and n.get("init"):
            init = [c for c in n["inner"] if c.get("kind") not in ("FullComment",)]
            if init:
                x = from_clang(init[-1])
                if x:
                    out["V " + n["name"]] = x
    return out


def goosecc_funcs(goosecc, path, flags):
    r = subprocess.run([goosecc, "--dump-ast"] + flags + [path], stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=ENV)
    if r.returncode != 0:
        return None, r.stderr.decode(errors="replace")
    out = {}
    stack = []
    cur = None
    for line in r.stdout.decode(errors="replace").splitlines():
        if line.startswith("F ") or line.startswith("V "):
            cur = line.strip()
            stack = []
            continue
        parts = line.split("\t")
        depth = int(parts[0])
        kind = parts[1]
        typ = parts[2] if len(parts) > 2 else "-"
        extra = parts[3] if len(parts) > 3 else ""
        n = N(kind, norm_type(typ), extra)
        del stack[depth:]
        if depth == 0:
            out[cur] = n
            # merge consecutive VarDecls into a DeclGroup lazily (compare handles it)
        else:
            stack[depth - 1].kids.append(n)
        stack.append(n)
    return out, ""


EXTRA_KINDS = {"ImplicitCastExpr", "CStyleCastExpr", "BinaryOperator", "UnaryOperator", "DeclRefExpr", "MemberExpr",
               "BuiltinCall", "VarDecl", "LabelStmt", "CaseStmt"}


def split_type_extra(kind, rest):
    if kind in ("CompoundAssignOperator",):
        # "<type> <comptype>": split at the middle by trying both halves
        parts = rest.split(" ")
        for i in range(1, len(parts)):
            a, b = " ".join(parts[:i]), " ".join(parts[i:])
            if a == b or (balanced(a) and balanced(b)):
                return a, b
        return rest, ""
    if kind in EXTRA_KINDS and " " in rest:
        a, b = rest.rsplit(" ", 1)
        return a, b
    return rest, ""


def balanced(s):
    return s.count("(") == s.count(")") and s.count("[") == s.count("]")


def group_decls(kids):
    """goosecc lists VarDecls one by one; clang groups them in a DeclStmt."""
    out = []
    for k in kids:
        out.append(k)
    return out


def compare(a, b, path, diffs):
    """a: clang, b: goosecc."""
    if a.kind == "DeclGroup" and b.kind != "DeclGroup":
        return None
    if a.kind == "ChooseExpr":
        return True
    same_type = a.type == b.type or has_typedef(a.type)
    if a.type == "<vla>" and re.search(r"\[\d+\]$", b.type):
        # clang prints a bound written as an expression even when it folded
        # the array to a constant size (a ConstantArrayType keeps its size
        # expression since clang 18; GNU modes fold, G1): only "an array"
        # can be told from its JSON
        same_type = True
    if a.kind in ("ShuffleVectorExpr", "ConvertVectorExpr") and b.kind in ("BuiltinCall", "Builtin"):
        # goosecc represents these as builtin calls: only the type is compared
        if same_type:
            return True
    if a.kind == "GenericSelectionExpr" and same_type:
        return True     # goosecc keeps only the selected expression
    if a.kind == "InitListExpr" and b.kind == "StringLiteral" and len(a.kids) == 1 and a.kids[0].kind == "StringLiteral":
        # clang wraps the string initializing a flexible array member
        return compare(a.kids[0], b, path, diffs)
    if a.kind == "CompoundLiteralExpr" and b.kind == "ImplicitCastExpr" and b.extra == "ToUnion" and a.kids \
            and a.kids[0].kind == "InitListExpr" and len(a.kids[0].kids) == 1 and b.kids:
        # a transparent-union argument: clang builds a compound literal
        return compare(a.kids[0].kids[0], b.kids[0], path, diffs)
    same_extra = a.extra == b.extra or a.kind in ("LabelStmt", "VarDecl", "CaseStmt") or \
        (a.kind == "CompoundAssignOperator" and has_typedef(a.extra))
    if a.kind != b.kind or not same_type or not same_extra:
        diffs.append("%s: clang %s '%s' %s | goosecc %s '%s' %s" % ("/".join(path[-6:]), a.kind, a.type, a.extra, b.kind, b.type, b.extra))
        return False
    ak = flatten_decls(a.kids)
    bk = flatten_decls(b.kids)
    if a.kind in ("InitListExpr",) and len(ak) != len(bk):
        n = min(len(ak), len(bk))
        ak, bk = ak[:n], bk[:n]
    if len(ak) != len(bk):
        diffs.append("%s: %s children: clang %d [%s] | goosecc %d [%s]" % ("/".join(path[-6:]), a.kind, len(ak),
                     ",".join(x.kind for x in ak[:6]), len(bk), ",".join(x.kind for x in bk[:6])))
        return False
    for i, (x, y) in enumerate(zip(ak, bk)):
        if compare(x, y, path + ["%s%d" % (a.kind[:6], i)], diffs) is False:
            return False
    return True


TYPEDEFS = set()
KEYWORDS = set("""void char short int long float double signed unsigned _Bool _Complex const volatile restrict
struct union enum __int128 __float128 _Float16 __bf16 _Atomic __attribute__ __vector_size__ sizeof ext_vector_type
anonymous""".split())


def has_typedef(t):
    """clang prints typedef names (sugar) below the top level: such types are not compared."""
    for w in re.findall(r"[A-Za-z_][A-Za-z0-9_]*", t):
        if w in TYPEDEFS:
            return True
    return False


def flatten_decls(kids):
    out = []
    for k in kids:
        if k.kind == "DeclGroup":
            out.extend(k.kids)
        else:
            out.append(k)
    return out


def check(a, path, flags):
    if os.path.getsize(path) > a.max_bytes:
        return "skipped", [], 0
    c = clang_funcs(path, flags)
    if c is None:
        return "clang-invalid", [], 0
    g, err = goosecc_funcs(a.goosecc, path, flags)
    if g is None:
        return "goosecc-error", [err.strip()[:200]], 0
    diffs = []
    n = 0
    for name, ct in c.items():
        gt = g.get(name)
        if gt is None:
            continue
        n += 1
        top = ct
        if name.startswith("V "):
            r = compare(top, gt, [name], diffs)
        else:
            r = compare(top, gt, [name], diffs)
    return ("ok" if not diffs else "diff"), diffs, n


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--goosecc", default=os.path.join(HERE, "..", "build", "goosecc"))
    ap.add_argument("-j", type=int, default=3)
    ap.add_argument("--corpus", default="")
    ap.add_argument("--show", type=int, default=30)
    ap.add_argument("--max-bytes", type=int, default=4000000)
    ap.add_argument("--hist", action="store_true")
    ap.add_argument("--grep", default="", help="show the files and paths of differences matching this regex")
    ap.add_argument("rest", nargs="*")
    argv, cli_flags = corpus_mod.split_flags(sys.argv[1:])
    a = ap.parse_args(argv)
    if a.rest:
        files, flags = a.rest, cli_flags
        jobs = [("args", f, flags) for f in files]
    else:
        jobs = list(corpus_mod.corpus([c for c in a.corpus.split(",") if c]))
    with cf.ThreadPoolExecutor(a.j) as ex:
        res = list(ex.map(lambda j: (j, check(a, j[1], j[2])), jobs))
    by = collections.defaultdict(collections.Counter)
    nf = collections.Counter()
    hist = collections.Counter()
    shown = 0
    for (c, p, fl), (st, diffs, n) in res:
        by[c][st] += 1
        nf[c] += n
        for d in diffs:
            hist[re.sub(r"^[^:]*: ", "", d)[:150]] += 1
            if a.grep and re.search(a.grep, d):
                print("GREP %s\n    %s" % (p, d))
        if diffs and shown < a.show:
            print("%s: %d diffs" % (p, len(diffs)))
            for d in diffs[:3]:
                print("    " + d)
            shown += 1
    if a.hist:
        print("\nmost common differences:")
        for k, v in hist.most_common(40):
            print("%6d  %s" % (v, k))
    print()
    for c, cnt in by.items():
        print("%-8s files %5d  ok %5d  diff %4d  clang-invalid %3d  goosecc-error %3d  skipped %3d  functions compared %6d" % (
            c, sum(cnt.values()), cnt["ok"], cnt["diff"], cnt["clang-invalid"], cnt["goosecc-error"], cnt["skipped"], nf[c]))


if __name__ == "__main__":
    main()
