// goosecc D2: C++ spellings of types and declarations for diagnostics
// (clang's style: 'std::vector<int>', 'const char *', 'int (*)(int)'),
// template arguments included.
//
// The text is built on a global stack (cts): each type's text is appended
// at its top, function parameter types and template arguments nesting
// above it (Goose: no growable locals across the recursion).

namespace cx;

import std;
import .common;
import .types;
import .ast;
import .sema;
import .cx_core;

var ctn_buf: u8[>..] = [];

// 't' quoted, the C++ spelling.
fn ctname(t: u32) -> const u8[:] {
    ctn_buf.clear();
    ctn_buf.push('\'');
    cx_type_text(ctn_buf, t);
    ctn_buf.push('\'');
    return ctn_buf;
}

// The type t (declaring nothing) to out.
recursive fn cx_type_text(out: u8[>..]&, t: u32) {
    let m = cts.len;
    cts_type(t);
    for i in m..cts.len { out.push(cts[i]); }
    cts.resize(m);
}

// The qualifier of scope sc (X<int>::, std::) to out.
recursive fn cx_scope_prefix(out: u8[>..]&, sc: i64) {
    let m = cts.len;
    cts_scope(sc);
    for i in m..cts.len { out.push(cts[i]); }
    cts.resize(m);
}

// The template argument list l (<int, 3>) to out.
recursive fn cx_targs_text(out: u8[>..]&, l: i64) {
    let m = cts.len;
    cts_targs(l);
    for i in m..cts.len { out.push(cts[i]); }
    cts.resize(m);
}

var cts: u8[>..<] = [];
var ctt: u8[>..] = [];

fn cts_insert(at: i64, text: const u8[:]) {
    let n = text.len;
    let old = cts.len;
    for i in n { cts.push(0); }
    var j = old - 1;
    while j >= at { cts[j + n] = cts[j]; j--; }
    for i in n { cts[at + i] = text[i]; }
}
fn cts_append(text: const u8[:]) { for c in text { cts.push(c); } }

// Moves the text from `from` to the top of the stack to position `at`.
fn cts_move_to(at: i64, from: i64) {
    ctt.clear();
    for i in from..cts.len { ctt.push(cts[i]); }
    cts.resize(from);
    cts_insert(at, ctt);
}

// Appends the spelling of t0: the declarator is built inside out
// (pointers prefix it, arrays and functions suffix it), then the base type
// goes before it.
recursive fn cts_type(t0: u32) {
    let m = cts.len;
    var t = t0;
    loop {
        let k = kind_of(t);
        if k == TY_POINTER || k == TY_LREF || k == TY_RREF || k == TY_MEMPTR {
            let b = tbase(t);
            let bk = kind_of(b);
            let paren = bk == TY_FUNC || bk == TY_ARRAY || bk == TY_VLA;
            let q = quals(t);
            var qs = 0;
            if q & Q_CONST != 0 { cts_insert(m + qs, " const"); qs += 6; }
            if q & Q_VOLATILE != 0 { cts_insert(m + qs, " volatile"); qs += 9; }
            if qs > 0 && cts.len > m + qs { cts_insert(m + qs, " "); }
            cts_insert(m, if k == TY_LREF { "&" } else if k == TY_RREF { "&&" } else { "*" });
            if k == TY_MEMPTR {
                // C::* : the class first
                let mk = cts.len;
                cts_type(types[t >> 4].extra);
                cts_append("::");
                cts_move_to(m, mk);
            }
            if paren { cts_insert(m, "("); cts.push(')'); }
            t = b;
            continue;
        }
        if k == TY_ARRAY || k == TY_VLA {
            let n = types[t >> 4].n;
            cts.push('[');
            if k == TY_ARRAY && n >= 0 {
                ctt.clear();
                format(ctt, n);
                cts_append(ctt);
            }
            cts.push(']');
            t = tbase(t);
            continue;
        }
        if k == TY_FUNC {
            let ft = types[t >> 4];
            cts.push('(');
            for i in ft.n {
                if i > 0 { cts_append(", "); }
                cts_type(tparams[ft.extra + i]);
            }
            if ft.flags & TF_VARIADIC != 0 { cts_append(if ft.n > 0 { ", ..." } else { "..." }); }
            cts.push(')');
            let fl = ft.flags as i64;
            if fl & TF_MCONST != 0 { cts_append(" const"); }
            if fl & TF_MVOLATILE != 0 { cts_append(" volatile"); }
            if fl & TF_MLREF != 0 { cts_append(" &"); }
            if fl & TF_MRREF != 0 { cts_append(" &&"); }
            t = ft.base;
            continue;
        }
        break;
    }
    let d = cts.len;
    let q = quals(t);
    if q & Q_CONST != 0 { cts_append("const "); }
    if q & Q_VOLATILE != 0 { cts_append("volatile "); }
    cts_base(t);
    if d == m { return; }
    // the base (and a space) before the declarator
    if cts[m] != '[' { cts.push(' '); }
    cts_move_to(m, d);
}

recursive fn cts_base(t: u32) {
    let k = kind_of(t);
    let u = unqual(t);
    if u == t_wchar_cxx { cts_append("wchar_t"); return; }
    if u == t_char16 { cts_append("char16_t"); return; }
    if u == t_char32 { cts_append("char32_t"); return; }
    if u == t_char8 { cts_append("char8_t"); return; }
    if k == TY_STRUCT || k == TY_UNION { cts_record(rec_of(t)); return; }
    if k == TY_ENUM {
        let e = enums[types[t >> 4].extra];
        if e.name != 0 { cts_append(ident_text(e.name as i64)); } else { cts_append("(unnamed enum)"); }
        return;
    }
    if k == TY_BOOL { cts_append("bool"); return; }
    if k == TY_NULLPTR { cts_append("std::nullptr_t"); return; }
    ctt.clear();
    base_name(ctt, t);
    cts_append(ctt);
}

recursive fn cts_scope(sc: i64) {
    if sc <= 0 { return; }
    let k = scopes[sc].kind as i64;
    if k != CS_NS && k != CS_CLASS { return; }
    cts_scope(scopes[sc].parent as i64);
    if k == CS_NS && (scopes[sc].name == 0 || scopes[sc].flags & SCF_ANON != 0) { cts_append("(anonymous namespace)::"); return; }
    if k == CS_NS && scopes[sc].flags & SCF_INLINE != 0 && ident_text(scopes[sc].name as i64).len > 2 &&
       ident_text(scopes[sc].name as i64)[0] == '_' && ident_text(scopes[sc].name as i64)[1] == '_' {
        // std::__cxx11:: is not printed by clang
        return;
    }
    if k == CS_CLASS {
        let r = scopes[sc].rec as i64;
        if r >= 0 { cts_record(r); cts_append("::"); return; }
    }
    cts_append(ident_text(scopes[sc].name as i64));
    cts_append("::");
}

recursive fn cts_record(r: i64) {
    let cs = if r < crecs.len { crecs[r].sym as i64 } else { -1 };
    if cs >= 0 { cts_scope(cxs[cs].dscope as i64); }
    if records[r].name == 0 { cts_append("(anonymous)"); return; }
    cts_append(ident_text(records[r].name as i64));
    if cs >= 0 && cxs[cs].targs >= 0 && cxs[cs].tmpl >= 0 { cts_targs(cxs[cs].targs as i64); }
}

recursive fn cts_targs(l: i64) {
    cts.push('<');
    var first = true;
    for i in tl_count(l) {
        let a = tl_arg(l, i);
        if a.kind as i64 == TA_PACK {
            for j in tl_count(a.v) {
                if !first { cts_append(", "); }
                first = false;
                cts_targ(tl_arg(a.v, j));
            }
            continue;
        }
        if !first { cts_append(", "); }
        first = false;
        cts_targ(a);
    }
    cts.push('>');
}

recursive fn cts_targ(a: TArg) {
    let k = a.kind as i64;
    if k == TA_TYPE { cts_type(a.ty); return; }
    if k == TA_TEMPLATE {
        if a.v >= 0 { cts_append(ident_text(syms[a.v].name as i64)); }
        return;
    }
    if k == TA_VALUE {
        if a.ty != 0 && kind_of(a.ty) == TY_BOOL { cts_append(if a.v != 0 { "true" } else { "false" }); return; }
        if a.ty != 0 && is_dep(a.ty) { cts_append("<expression>"); return; }
        ctt.clear();
        format(ctt, a.v);
        cts_append(ctt);
    }
}
