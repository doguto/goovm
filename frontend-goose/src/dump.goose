// goosecc: --dump-ast, a line-per-node dump of the function bodies in the
// shape of clang's AST (kinds, types, cast kinds), used by
// tests/cmp_ast.py to check the semantic analysis against clang-20.
//
// Format: "F name" starts a function; then one line per node:
//   <depth> <Kind> <type> [extra]
// Types are printed as clang prints canonical types.

import std;
import os;
import .common;
import .types;
import .ast;
import .builtins;

var dout: u8[>..] = [];

// clang's TypePrinter: the part before the name, then the part after.
recursive fn ct_before(out: u8[>..]&, q: u32) {
    let t = types[q >> 4];
    let k = t.kind as i64;
    let qs = quals(q);
    if k == TY_POINTER {
        let pk = kind_of(t.base);
        ct_before(out, t.base);
        if pk == TY_ARRAY || pk == TY_VLA || pk == TY_FUNC {
            if out.len > 0 && out[out.len - 1] != '*' { out.push(' '); }
            out.push('(');
        } else if out.len > 0 && out[out.len - 1] != '*' && out[out.len - 1] != '(' {
            out.push(' ');
        }
        out.push('*');
        if qs & Q_CONST != 0 { out.append("const"); }
        if qs & Q_VOLATILE != 0 { if qs & Q_CONST != 0 { out.push(' '); } out.append("volatile"); }
        if qs & Q_RESTRICT != 0 { if qs & (Q_CONST | Q_VOLATILE) != 0 { out.push(' '); } out.append("restrict"); }
        return;
    }
    if k == TY_ARRAY || k == TY_VLA {
        ct_before(out, t.base);
        return;
    }
    if k == TY_FUNC {
        ct_before(out, t.base);
        return;
    }
    if qs & Q_ATOMIC != 0 {
        out.append("_Atomic(");
        ct_full(out, unqual(q) & ~(Q_ATOMIC as! u32));
        out.push(')');
        return;
    }
    if k == TY_VECTOR || k == TY_EXTVECTOR {
        // clang prints the qualifiers of a vector type after it
        ct_base(out, q);
        if qs & Q_CONST != 0 { out.append(" const"); }
        if qs & Q_VOLATILE != 0 { out.append(" volatile"); }
        return;
    }
    if qs & Q_CONST != 0 { out.append("const "); }
    if qs & Q_VOLATILE != 0 { out.append("volatile "); }
    if qs & Q_RESTRICT != 0 { out.append("restrict "); }
    ct_base(out, q);
}

recursive fn ct_after(out: u8[>..]&, q: u32) {
    let t = types[q >> 4];
    let k = t.kind as i64;
    if k == TY_POINTER {
        let pk = kind_of(t.base);
        if pk == TY_ARRAY || pk == TY_VLA || pk == TY_FUNC { out.push(')'); }
        ct_after(out, t.base);
        return;
    }
    if k == TY_ARRAY {
        if t.n >= 0 { format(out, "[", t.n, "]"); } else { out.append("[]"); }
        ct_after(out, t.base);
        return;
    }
    if k == TY_VLA {
        out.append("[*]");
        ct_after(out, t.base);
        return;
    }
    if k == TY_FUNC {
        out.push('(');
        if t.flags & TF_NOPROTO == 0 {
            if t.n == 0 && t.flags & TF_VARIADIC == 0 { out.append("void"); }
            for i in t.n {
                if i > 0 { out.append(", "); }
                ct_full(out, tparams[t.extra + i]);
            }
            if t.flags & TF_VARIADIC != 0 { out.append(if t.n > 0 { ", ..." } else { "..." }); }
        }
        out.push(')');
        ct_after(out, t.base);
        return;
    }
}

recursive fn ct_full(out: u8[>..]&, q: u32) {
    let start = out.len;
    ct_before(out, q);
    let k = kind_of(q);
    if k == TY_FUNC || k == TY_ARRAY || k == TY_VLA {
        if k == TY_FUNC && out.len > start && out[out.len - 1] != '*' { out.push(' '); }
    }
    ct_after(out, q);
}

recursive fn ct_base(out: u8[>..]&, q: u32) {
    let t = types[q >> 4];
    let k = t.kind as i64;
    if k == TY_VECTOR {
        let es = type_size(t.base);
        format(out, "__attribute__((__vector_size__(", t.n, " * sizeof(");
        ct_full(out, t.base);
        out.append(")))) ");
        ct_full(out, t.base);
        return;
    }
    if k == TY_EXTVECTOR {
        ct_full(out, t.base);
        format(out, " __attribute__((ext_vector_type(", t.n, ")))");
        return;
    }
    base_name(out, q & ~(15 as u32));
}

fn dump_type(q: u32) {
    if q == 0 { dout.append("-"); return; }
    ct_full(dout, q);
}

let CK_NAMES = ["", "LValueToRValue", "ArrayToPointerDecay", "FunctionToPointerDecay", "NullToPointer", "IntegralCast",
    "IntegralToBoolean", "IntegralToFloating", "FloatingToIntegral", "FloatingToBoolean", "FloatingCast",
    "PointerToIntegral", "IntegralToPointer", "PointerToBoolean", "BitCast", "NoOp", "ToVoid", "ToUnion",
    "RealToComplex", "ComplexToReal", "ComplexCast", "VectorSplat", "VectorBitCast", "AtomicConversion", "BuiltinFnToFnPtr"];

let BOP_NAMES = ["", "*", "/", "%", "+", "-", "<<", ">>", "<", ">", "<=", ">=", "==", "!=", "&", "^", "|", "&&", "||", ",", "+", "-", "-"];
let UOP_NAMES = ["", "-", "+", "!", "~", "*", "&", "++", "--", "++", "--", "__real", "__imag", "__extension__"];

fn dline(depth: i64, kind: const u8[:], ty: u32) {
    format(dout, depth, "\t", kind, "\t");
    dump_type(ty);
}

// One node and its children. depth is bounded by the AST depth.
recursive fn dump_node(n: u32, depth: i64) {
    if n == 0 { format(dout, depth, "\t<null>\t-\n"); return; }
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_INT { dline(depth, "IntegerLiteral", nd.ty); dout.push('\n'); return; }
    if k == N_FLOAT { dline(depth, "FloatingLiteral", nd.ty); dout.push('\n'); return; }
    if k == N_STRING { dline(depth, "StringLiteral", nd.ty); dout.push('\n'); return; }
    if k == N_DECLREF {
        dline(depth, "DeclRefExpr", nd.ty);
        format(dout, "\t", sym_name(nd.a as i64), "\n");
        return;
    }
    if k == N_UNARY {
        if nd.op as i64 == U_EXTENSION { dump_node(nd.a, depth); return; }
        dline(depth, "UnaryOperator", nd.ty);
        format(dout, "\t", UOP_NAMES[nd.op], "\n");
        dump_node(nd.a, depth + 1);
        return;
    }
    if k == N_BINARY {
        dline(depth, "BinaryOperator", nd.ty);
        format(dout, "\t", BOP_NAMES[nd.op], "\n");
        dump_node(nd.a, depth + 1);
        dump_node(nd.b, depth + 1);
        return;
    }
    if k == N_ASSIGN {
        if nd.op == 0 {
            dline(depth, "BinaryOperator", nd.ty);
            dout.append("\t=\n");
        } else {
            dline(depth, "CompoundAssignOperator", nd.ty);
            dout.append("\t");
            dump_type(nd.c);
            dout.push('\n');
        }
        dump_node(nd.a, depth + 1);
        dump_node(nd.b, depth + 1);
        return;
    }
    if k == N_COND {
        if nd.b == 0 {
            dline(depth, "BinaryConditionalOperator", nd.ty);
            dout.push('\n');
            return;
        }
        dline(depth, "ConditionalOperator", nd.ty);
        dout.push('\n');
        dump_node(nd.a, depth + 1);
        dump_node(nd.b, depth + 1);
        dump_node(nd.c, depth + 1);
        return;
    }
    if k == N_CALL {
        dline(depth, "CallExpr", nd.ty);
        dout.push('\n');
        dump_node(nd.a, depth + 1);
        for i in nd.c { dump_node(nlist[nd.v + i], depth + 1); }
        return;
    }
    if k == N_BUILTIN {
        if nd.op as i64 == BI_CALL {
            dline(depth, "BuiltinCall", nd.ty);
            format(dout, "\t", sym_name(nd.a as i64), "\n");
            for i in nd.c { dump_node(nlist[nd.v + i], depth + 1); }
            return;
        }
        dline(depth, if nd.op as i64 == BI_IMAG_CONST { "ImaginaryLiteral" } else { "Builtin" }, nd.ty);
        dout.push('\n');
        return;
    }
    if k == N_MEMBER {
        dline(depth, "MemberExpr", nd.ty);
        let f = fields[nd.b];
        format(dout, "\t", if nd.op != 0 { "->" } else { "." }, if f.name != 0 { ident_text(f.name as i64) } else { "" }, "\n");
        dump_node(nd.a, depth + 1);
        return;
    }
    if k == N_INDEX {
        dline(depth, "ArraySubscriptExpr", nd.ty);
        dout.push('\n');
        dump_node(nd.a, depth + 1);
        dump_node(nd.b, depth + 1);
        return;
    }
    if k == N_CAST || k == N_ICAST {
        dline(depth, if k == N_CAST { "CStyleCastExpr" } else { "ImplicitCastExpr" }, nd.ty);
        format(dout, "\t", CK_NAMES[nd.op], "\n");
        dump_node(nd.a, depth + 1);
        return;
    }
    if k == N_SIZEOF { dline(depth, "UnaryExprOrTypeTraitExpr", nd.ty); dout.push('\n'); return; }
    if k == N_OFFSETOF { dline(depth, "OffsetOfExpr", nd.ty); dout.push('\n'); return; }
    if k == N_COMPLIT {
        dline(depth, "CompoundLiteralExpr", nd.ty);
        dout.push('\n');
        dump_node(nd.a, depth + 1);
        return;
    }
    if k == N_STMTEXPR {
        dline(depth, "StmtExpr", nd.ty);
        dout.push('\n');
        return;
    }
    if k == N_INITLIST {
        dline(depth, "InitListExpr", nd.ty);
        dout.push('\n');
        for i in nd.c { dump_node(nlist[nd.v + i], depth + 1); }
        return;
    }
    if k == N_ZEROINIT { dline(depth, "ImplicitValueInitExpr", nd.ty); dout.push('\n'); return; }
    if k == N_VAARG {
        dline(depth, "VAArgExpr", nd.ty);
        dout.push('\n');
        return;
    }
    if k == N_LABELADDR { dline(depth, "AddrLabelExpr", nd.ty); dout.push('\n'); return; }
    if k == N_ERROR { dline(depth, "Error", nd.ty); dout.push('\n'); return; }
    // statements
    if k == N_COMPOUND {
        format(dout, depth, "\tCompoundStmt\t-\n");
        for i in nd.c { dump_node(nlist[nd.v + i], depth + 1); }
        return;
    }
    if k == N_DECL {
        let s = nd.a as i64;
        if syms[s].kind != SK_VAR { return; }    // block-scope function declarations
        format(dout, depth, "\tVarDecl\t");
        dump_type(syms[s].ty);
        format(dout, "\t", sym_name(s), "\n");
        if nd.b != 0 { dump_node(nd.b, depth + 1); }
        return;
    }
    if k == N_TYPEDEF || k == N_TAGDEF || k == N_STATICASSERT { return; }
    if k == N_IF {
        format(dout, depth, "\tIfStmt\t-\n");
        dump_node(nd.a, depth + 1);
        dump_node(nd.b, depth + 1);
        if nd.c != 0 { dump_node(nd.c, depth + 1); }
        return;
    }
    if k == N_WHILE {
        format(dout, depth, "\tWhileStmt\t-\n");
        dump_node(nd.a, depth + 1);
        dump_node(nd.b, depth + 1);
        return;
    }
    if k == N_DO {
        format(dout, depth, "\tDoStmt\t-\n");
        dump_node(nd.a, depth + 1);
        dump_node(nd.b, depth + 1);
        return;
    }
    if k == N_FOR {
        format(dout, depth, "\tForStmt\t-\n");
        if nd.a != 0 && nodes[nd.a].kind == N_COMPOUND {
            // a declaration: clang's DeclStmt
            format(dout, depth + 1, "\tDeclGroup\t-\n");
            let ci = nodes[nd.a];
            for j in ci.c { dump_node(nlist[ci.v + j], depth + 2); }
        } else {
            dump_node(nd.a, depth + 1);
        }
        dump_node(nd.b, depth + 1);
        dump_node(nd.c, depth + 1);
        dump_node(nd.v as! u32, depth + 1);
        return;
    }
    if k == N_SWITCH {
        format(dout, depth, "\tSwitchStmt\t-\n");
        dump_node(nd.a, depth + 1);
        dump_node(nd.b, depth + 1);
        return;
    }
    if k == N_CASE {
        format(dout, depth, "\tCaseStmt\t-\t", nd.v, "\n");
        dump_node(nd.a, depth + 1);
        return;
    }
    if k == N_DEFAULT {
        format(dout, depth, "\tDefaultStmt\t-\n");
        dump_node(nd.a, depth + 1);
        return;
    }
    if k == N_LABEL {
        format(dout, depth, "\tLabelStmt\t-\t", sym_name(nd.a as i64), "\n");
        dump_node(nd.b, depth + 1);
        return;
    }
    if k == N_RETURN {
        format(dout, depth, "\tReturnStmt\t-\n");
        if nd.a != 0 { dump_node(nd.a, depth + 1); }
        return;
    }
    if k == N_EXPR { dump_node(nd.a, depth); return; }
    let name = match k {
        N_GOTO => "GotoStmt", N_IGOTO => "IndirectGotoStmt", N_BREAK => "BreakStmt", N_CONTINUE => "ContinueStmt",
        N_NULL => "NullStmt", N_ASM => "GCCAsmStmt", _ => "Unknown",
    };
    format(dout, depth, "\t", name, "\t-\n");
}

fn dump_ast(out_path: const u8[:]) -> bool {
    let tu = nodes[tu_node];
    for i in tu.c {
        let n = nlist[tu.v + i];
        let nd = nodes[n];
        if nd.kind == N_FUNCDEF {
            format(dout, "F ", sym_name(nd.a as i64), "\n");
            dump_node(nd.b, 0);
        } else if nd.kind == N_DECL && nd.b != 0 {
            format(dout, "V ", sym_name(nd.a as i64), "\n");
            dump_node(nd.b, 0);
        }
    }
    if out_path.len == 0 {
        write_stdout(dout);
        return true;
    }
    return write_file(out_path, dout);
}
