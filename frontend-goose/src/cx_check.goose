// goosecc D1: the C++ oracles' outputs.
//
// --dump-decls: one line per function and variable declared at namespace
// or class scope in the main file (not templates): its kind, name and
// mangled name, compared with what libclang reports for clang-20
// (tests/cmp_decls_cxx.py, tests/cxx_decls.c).
//
// --layout-check (C++): a C++ file that includes the translation unit and
// static_asserts, for every complete non-template class that can be named
// (namespaces and classes, not local or anonymous ones), its size and
// alignment, the offset of each named non-static data member (members of
// bases through the derived class), whether it is polymorphic and empty,
// and the declared types of its members and of the namespace-scope
// variables (__is_same with decltype); clang++-20 must accept it
// (compiled with -fno-access-control).

namespace cx;

import std;
import os;
import dictionary;
import .common;
import .types;
import .ast;
import .sema;
import .pp;
import .cx_core;
import .cx_names;
import .cx_mangle;

var ck: u8[>..] = [];
var ck_count: i64 = 0;
var ck_name: u8[>..] = [];

fn in_main_file(loc: u32) -> bool { file_of(loc as i64) == main_file_idx }

// The kind name clang's libclang reports for a declaration.
fn decl_kind(s: i64) -> const u8[:] {
    if syms[s].kind as i64 == SK_VAR { return "VarDecl"; }
    let f = cxs[s].flags;
    if f & CF_CTOR != 0 { return "CXXConstructor"; }
    if f & CF_DTOR != 0 { return "CXXDestructor"; }
    if f & CF_CONV != 0 { return "CXXConversion"; }
    if f & CF_MEMBER != 0 { return "CXXMethod"; }
    return "FunctionDecl";
}

// Can scope sc be named from the global scope (only named namespaces and
// classes on the way)?
recursive fn nameable(sc: i64) -> bool {
    if sc == 0 { return true; }
    if sc < 0 { return false; }
    let k = scopes[sc].kind as i64;
    if k != CS_NS && k != CS_CLASS { return false; }
    if scopes[sc].flags & (SCF_ANON | SCF_PATTERN) != 0 || scopes[sc].name == 0 { return false; }
    if k == CS_CLASS {
        let r = scopes[sc].rec as i64;
        if r < 0 { return false; }
        let cs = crecs[r].sym as i64;
        if cs >= 0 && cxs[cs].flags & CF_SPEC != 0 { return false; }
        if cs < 0 || syms[cs].scope > 0 { return false; }
    }
    return nameable(scopes[sc].parent as i64);
}

// ::a::b::C
recursive fn scope_qname(out: u8[>..]&, sc: i64) {
    if sc <= 0 { return; }
    scope_qname(out, scopes[sc].parent as i64);
    out.append("::");
    out.append(ident_text(scopes[sc].name as i64));
}

var dbg_decls: bool = false;
fn dump_decls(out_path: const u8[:]) -> bool {
    var o: u8[>..] = [];
    var dv: u8[>..] = [];
    dbg_decls = env("GOOSECC_DEBUG_DECLS", dv);
    mg_debug = dbg_decls;
    for s0, s in syms {
        let k = s0.kind as i64;
        if k != SK_FUNC && k != SK_VAR { continue; }
        if s >= cxs.len { continue; }
        let f = cxs[s].flags;
        if dbg_decls && s0.name != 0 && f & CF_MAINDECL != 0 { write_stderr(str("decl ", ident_text(s0.name as i64), " scope=", s0.scope, " dscope=", cxs[s].dscope, " flags=", f, "\n")); }
        if f & (CF_PATTERN | CF_IMPLICIT | CF_TPARAM | CF_FRIEND) != 0 { continue; }
        if s0.scope > 0 || s0.flags & SF_PARAM != 0 { continue; }
        let sc = cxs[s].dscope as i64;
        if sc < 0 || f & CF_MAINDECL == 0 { continue; }
        if scopes[sc].flags & SCF_PATTERN != 0 { continue; }
        if s0.name == 0 { continue; }
        if !mangle_sym(s) {
            if dbg_decls {
                write_stderr(str("  mangle failed: ", mg, "\n"));
                if s0.kind as i64 == SK_FUNC {
                    let ft = types[s0.ty >> 4];
                    for i in ft.n {
                        let pt = tparams[ft.extra + i];
                        write_stderr(str("    param kind ", kind_of(pt), " base kind ", kind_of(tbase(pt)), "\n"));
                        var x = pt;
                        if is_ref(x) { x = tbase(x); }
                        if kind_of(x) == TY_DEPSPEC {
                            let l = types[x >> 4].n;
                            for j in tl_count(l) {
                                let a = tl_arg(l, j);
                                write_stderr(str("      arg ", a.kind, " ty kind ", kind_of(a.ty), " v ", a.v, "\n"));
                                if kind_of(a.ty) == TY_DEPSPEC {
                                    let l2 = types[a.ty >> 4].n;
                                    for j2 in tl_count(l2) { let a2 = tl_arg(l2, j2); write_stderr(str("        inner arg ", a2.kind, " ty kind ", kind_of(a2.ty), " v ", a2.v, " ty ", a2.ty, " t_char ", t_char, "\n")); }
                                }
                            }
                        }
                    }
                }
            }
            continue;
        }
        o.append(decl_kind(s));
        o.push('|');
        if f & (CF_CTOR | CF_DTOR | CF_CONV | CF_OPERATOR) != 0 { o.push('-'); }
        else { o.append(ident_text(s0.name as i64)); }
        o.push('|');
        o.append(mg);
        o.push('\n');
    }
    if out_path.len == 0 || out_path == "-" { write_stdout(o); return true; }
    return write_file(out_path, o);
}

// ---------------------------------------------------------------------------
// C++ type names (valid C++98 and later, fully qualified), written in
// prefix form through class templates the check file defines
// (__gt_ptr<T >::t is T*, ...), so that no declarator has to be built
// inside out.

var tyn_ok: bool = true;

// The check file's helpers (C++98: no alias or variadic templates).
fn gt_defs(o: u8[>..]&) {
    o.append("template<class __T> struct __gt_ptr { typedef __T *t; };\n");
    o.append("template<class __T> struct __gt_lref { typedef __T &t; };\n");
    if opt_cxx_std >= 11 { o.append("template<class __T> struct __gt_rref { typedef __T &&t; };\n"); }
    o.append("template<class __T, unsigned long __N> struct __gt_arr { typedef __T t[__N]; };\n");
    o.append("template<class __T> struct __gt_uarr { typedef __T t[]; };\n");
    o.append("template<class __T> struct __gt_c { typedef const __T t; };\n");
    o.append("template<class __T> struct __gt_v { typedef volatile __T t; };\n");
    o.append("template<class __T> struct __gt_cv { typedef const volatile __T t; };\n");
    o.append("template<class __C, class __T> struct __gt_mp { typedef __T __C::*t; };\n");
    for n in 13 {
        for kind in 3 {
            // __gt_fnN (plain), __gt_fnvN (variadic), __gt_fncN (const member function)
            o.append("template<class __R");
            for i in n { format(o, ", class __A", i); }
            o.append(if kind == 0 { "> struct __gt_fn" } else if kind == 1 { "> struct __gt_fnv" } else { "> struct __gt_fnc" });
            format(o, n, " { typedef __R t(");
            for i in n { if i > 0 { o.append(", "); } format(o, "__A", i); }
            if kind == 1 { o.append(if n > 0 { ", ..." } else { "..." }); }
            o.append(if kind == 2 { ") const; };\n" } else { "); };\n" });
        }
    }
}

recursive fn cx_tyname(out: u8[>..]&, t: u32) {
    let k = kind_of(t);
    let q = quals(t) & (Q_CONST | Q_VOLATILE);
    if q != 0 && k != TY_ARRAY {
        out.append(if q == Q_CONST { "__gt_c< " } else if q == Q_VOLATILE { "__gt_v< " } else { "__gt_cv< " });
        cx_tyname(out, t & ~((Q_CONST | Q_VOLATILE) as! u32));
        out.append(" >::t");
        return;
    }
    if k == TY_POINTER || k == TY_LREF || k == TY_RREF {
        out.append(if k == TY_LREF { "__gt_lref< " } else if k == TY_RREF { "__gt_rref< " } else { "__gt_ptr< " });
        cx_tyname(out, tbase(t));
        out.append(" >::t");
        return;
    }
    if k == TY_MEMPTR {
        out.append("__gt_mp< ");
        cx_tyname(out, types[t >> 4].extra);
        out.append(", ");
        cx_tyname(out, tbase(t));
        out.append(" >::t");
        return;
    }
    if k == TY_ARRAY {
        let n = types[t >> 4].n;
        if n >= 0 { out.append("__gt_arr< "); } else { out.append("__gt_uarr< "); }
        cx_tyname(out, tbase(t));
        if n >= 0 { format(out, ", ", n); }
        out.append(" >::t");
        return;
    }
    if k == TY_FUNC {
        let f = types[t >> 4];
        if (f.flags as i64) & (TF_MVOLATILE | TF_MLREF | TF_MRREF) != 0 || f.n > 12 { tyn_ok = false; }
        if (f.flags as i64) & TF_MCONST != 0 && f.flags & TF_VARIADIC != 0 { tyn_ok = false; }
        out.append(if (f.flags as i64) & TF_MCONST != 0 { "__gt_fnc" } else if f.flags & TF_VARIADIC != 0 { "__gt_fnv" } else { "__gt_fn" });
        format(out, f.n, "< ");
        cx_tyname(out, f.base);
        for i in f.n {
            out.append(", ");
            cx_tyname(out, tparams[f.extra + i]);
        }
        out.append(" >::t");
        return;
    }
    base_tyname(out, t);
}

fn base_tyname(out: u8[>..]&, t: u32) {
    let k = kind_of(t);
    let u = unqual(t);
    if u == t_wchar_cxx { out.append("wchar_t"); return; }
    if u == t_char16 { out.append("char16_t"); return; }
    if u == t_char32 { out.append("char32_t"); return; }
    if u == t_char8 { out.append("unsigned char"); return; }
    if k == TY_STRUCT || k == TY_UNION || k == TY_ENUM {
        let sc = type_scope(t);
        if sc < 0 || !nameable(sc) { tyn_ok = false; out.append("int"); return; }
        out.append(if k == TY_ENUM { "enum " } else if k == TY_UNION { "union " } else { "struct " });
        scope_qname(out, sc);
        return;
    }
    if k == TY_BOOL { out.append("bool"); return; }
    if k == TY_NULLPTR { out.append("decltype(nullptr)"); return; }
    if k == TY_COMPLEX || k == TY_VECTOR || k == TY_EXTVECTOR || is_opaque(t) { tyn_ok = false; out.append("int"); return; }
    out.append(match k {
        TY_VOID => "void", TY_CHAR => "char", TY_SCHAR => "signed char", TY_UCHAR => "unsigned char", TY_SHORT => "short",
        TY_USHORT => "unsigned short", TY_INT => "int", TY_UINT => "unsigned int", TY_LONG => "long",
        TY_ULONG => "unsigned long", TY_LLONG => "long long", TY_ULLONG => "unsigned long long", TY_INT128 => "__int128",
        TY_UINT128 => "unsigned __int128", TY_FLOAT => "float", TY_DOUBLE => "double", TY_LDOUBLE => "long double",
        TY_FLOAT128 => "__float128", TY_FLOAT16 => "_Float16", TY_BF16 => "__bf16", _ => "int",
    });
    if k > TY_EXTVECTOR || k == 0 { tyn_ok = false; }
}

// ---------------------------------------------------------------------------
// The layout check.

fn ck_assert(expr_: const u8[:], value: i64, what: const u8[:]) {
    ck.append("_Static_assert(");
    ck.append(expr_);
    format(ck, " == ", value, ", \"goosecc layout: ");
    for c in what { if c == '"' || c == '\\' { ck.push('\\'); } ck.push(c); }
    ck.append("\");\n");
    ck_count++;
}

fn ck_same(expr_: const u8[:], t: u32, what: const u8[:]) {
    tyn_ok = true;
    var tn: u8[>..] = [];
    cx_tyname(tn, t);
    if !tyn_ok { return; }
    ck.append("_Static_assert(__is_same(__typeof__(");
    ck.append(expr_);
    ck.append("), ");
    ck.append(tn);
    ck.append("), \"goosecc type: ");
    for c in what { if c == '"' || c == '\\' { ck.push('\\'); } ck.push(c); }
    ck.append("\");\n");
    ck_count++;
}

fn write_cxx_layout_check(input: const u8[:], out_path: const u8[:]) -> bool {
    ck.append("/* goosecc --layout-check (C++): generated */\n#include \"");
    ck.append(input);
    ck.append("\"\n");
    gt_defs(ck);
    var ex: u8[>..] = [];
    for rec, r in records {
        if r == 0 || r >= crecs.len { continue; }
        if rec.flags & RF_COMPLETE == 0 || rec.size < 0 { continue; }
        let cr = crecs[r];
        if cr.flags & CR_PATTERN != 0 || cr.scope < 0 { continue; }
        let sc = cr.scope as i64;
        if !nameable(sc) { continue; }
        ck_name.clear();
        ck_name.append(if rec.flags & RF_UNION != 0 { "union " } else { "struct " });
        scope_qname(ck_name, sc);
        ex.clear();
        format(ex, "sizeof(", ck_name, ")");
        ck_assert(ex, rec.size, ck_name);
        ex.clear();
        format(ex, "__alignof__(", ck_name, ")");
        ck_assert(ex, rec.align as i64, ck_name);
        ex.clear();
        format(ex, "__is_polymorphic(", ck_name, ")");
        ck_assert(ex, if cr.flags & CR_POLY != 0 { 1 } else { 0 }, ck_name);
        ex.clear();
        format(ex, "__is_empty(", ck_name, ")");
        ck_assert(ex, if cr.flags & CR_EMPTY != 0 { 1 } else { 0 }, ck_name);
        // the fields
        for i in rec.first..rec.first + rec.count {
            let f = fields[i];
            if f.name == 0 || f.width >= 0 || f.flags & FF_ANON != 0 || is_ref(f.ty) { continue; }
            ex.clear();
            format(ex, "__builtin_offsetof(", ck_name, ", ", ident_text(f.name as i64), ")");
            ck_assert(ex, f.offset, ex);
            ex.clear();
            format(ex, "((", ck_name, "*)0)->", ident_text(f.name as i64));
            if !is_opaque(f.ty) { ck_same(ex, f.ty, ex); }
        }
        // the fields of the bases, through this class (base offsets)
        for b in cr.nbases {
            let bb = cbases[cr.bases + b];
            if bb.flags & BF_VIRTUAL != 0 || !is_record(bb.ty) { continue; }
            let br = records[rec_of(bb.ty)];
            for i in br.first..br.first + br.count {
                let f = fields[i];
                if f.name == 0 || f.width >= 0 || f.flags & FF_ANON != 0 || is_ref(f.ty) { continue; }
                if base_member_hidden(r, f.name) { continue; }
                ex.clear();
                format(ex, "__builtin_offsetof(", ck_name, ", ", ident_text(f.name as i64), ")");
                ck_assert(ex, bb.offset + f.offset, ex);
                break;
            }
        }
    }
    // the declared types of namespace-scope variables of the main file
    for s0, s in syms {
        if s0.kind as i64 != SK_VAR || s >= cxs.len { continue; }
        if cxs[s].flags & (CF_PATTERN | CF_TPARAM) != 0 || s0.scope > 0 || s0.name == 0 { continue; }
        let sc = cxs[s].dscope as i64;
        if sc < 0 || !nameable(sc) || !in_main_file(s0.loc) { continue; }
        if is_opaque(s0.ty) || has_auto_t(s0.ty) { continue; }
        ex.clear();
        scope_qname(ex, sc);
        ex.append("::");
        ex.append(ident_text(s0.name as i64));
        ck_same(ex, s0.ty, ex);
    }
    format(ck, "/* ", ck_count, " assertions */\n");
    return write_file(out_path, ck);
}

recursive fn has_auto_t(t: u32) -> bool {
    let k = kind_of(t);
    if k == TY_AUTO { return true; }
    if k == TY_POINTER || k == TY_LREF || k == TY_RREF || k == TY_ARRAY { return has_auto_t(tbase(t)); }
    return false;
}

// Is a member named `name` of class r's own (or of a nearer base) hiding a
// base's field of that name, or is the name ambiguous?
fn base_member_hidden(r: i64, name: u32) -> bool {
    let rec = records[r];
    for i in rec.first..rec.first + rec.count { if fields[i].name == name { return true; } }
    return false;
}
