// goosecc D1: Itanium C++ ABI name mangling (clang's ItaniumMangleContext
// for what D1 declares): functions (members, constructors C1/C2,
// destructors D0/D1/D2, operators, conversion functions), variables in
// namespaces and static data members, with nested names, substitutions
// (S_, S0_, ...), the std:: abbreviations (St, Sa, Sb, Ss, Si, So, Sd),
// cv- and ref-qualified member functions, template arguments of
// specializations, and the C linkage of extern "C" names and globals.

namespace cx;

import std;
import dictionary;
import .common;
import .types;
import .ast;
import .sema;
import .cx_core;
import .cx_names;

var mg: u8[>..] = [];
var msubs: u64[>..<] = [];
var mg_fail: bool = false;

let MK_TYPE: u64 = 1099511627776;      // 1 << 40: a type (the qtype below)
let MK_SCOPE: u64 = 2199023255552;     // 2 << 40: a namespace or class prefix (scope id)
let MK_TMPL: u64 = 3298534883328;      // 3 << 40: a template prefix (template symbol)

fn sub_find(key: u64) -> i64 {
    for k, i in msubs { if k == key { return i; } }
    return -1;
}

fn sub_emit(i: i64) {
    if i == 0 { mg.append("S_"); return; }
    mg.push('S');
    base36(i - 1);
    mg.push('_');
}

recursive fn base36(v: i64) {
    if v >= 36 { base36(v / 36); }
    let d = v % 36;
    mg.push(if d < 10 { ('0' as i64 + d) as! u8 } else { ('A' as i64 + d - 10) as! u8 });
}

fn source_name(s: const u8[:]) {
    format(mg, s.len);
    mg.append(s);
}

// Is scope sc the namespace ::std?
fn is_std_ns(sc: i64) -> bool {
    return sc > 0 && scopes[sc].kind as i64 == CS_NS && scopes[sc].parent == 0 && scopes[sc].name == id_std;
}

// The mangled name of symbol s (a function or variable) into mg; false
// when D1 cannot mangle it (a dependent or unknown type).
fn mangle_sym(s: i64) -> bool {
    mg.clear();
    msubs.clear();
    mg_fail = false;
    let k = syms[s].kind as i64;
    let sc = cxs[s].dscope as i64;
    let fl = cxs[s].flags;
    // C names: main, extern "C", and variables of the global namespace
    if syms[s].name == id_main && sc == 0 && k == SK_FUNC { mg.append(ident_text(syms[s].name as i64)); return true; }
    // extern "C" names (an internal one is not extern C: clang's FunctionDecl::isExternC)
    if fl & CF_EXTERN_C != 0 && fl & CF_MEMBER == 0 && syms[s].sc as i64 != SC_STATIC { mg.append(ident_text(syms[s].name as i64)); return true; }
    if k == SK_VAR && (sc == 0 || sc < 0) && fl & CF_MEMBER == 0 && !internal_linkage(s) && !type_has_tags(syms[s].ty) {
        mg.append(ident_text(syms[s].name as i64));
        return true;
    }
    mg.append("_Z");
    mg_tags.clear();
    mangle_name(s);
    let name_end = mg_name_end;
    if k == SK_FUNC {
        let ft = syms[s].ty;
        let f = types[ft >> 4];
        if f.n == 0 && f.flags & TF_VARIADIC == 0 { mg.push('v'); }
        for i in f.n { mangle_type(tparams[f.extra + i]); }
        if f.flags & TF_VARIADIC != 0 { mg.push('z'); }
    }
    // implicit ABI tags: those of the return type (variables: of their
    // type) that the name and the parameters do not already carry
    let used = mg_tags.len;
    if (k == SK_FUNC && fl & (CF_CTOR | CF_DTOR | CF_CONV) == 0) || k == SK_VAR {
        let rt = if k == SK_FUNC { types[syms[s].ty >> 4].base } else { syms[s].ty };
        let keep = mg.len;
        let nsubs = msubs.len;
        let fail0 = mg_fail;
        mangle_type(rt);
        mg_fail = fail0;
        mg.resize(keep);
        msubs.resize(nsubs);
        if mg_tags.len > used {
            mg_tail.clear();
            mg_tail.append(mg[name_end..]);
            mg.resize(name_end);
            for j in used..mg_tags.len {
                let tt = tag_text(mg_tags[j]);
                format(mg, "B", tt.len);
                mg.append(tt);
            }
            mg.append(mg_tail);
        }
    }
    return !mg_fail;
}
var mg_name_end: i64 = 0;

// Does mangling t meet an ABI tag (a global variable of such a type is
// mangled, to carry it)?
fn type_has_tags(t: u32) -> bool {
    mg_tags.clear();
    let keep = mg.len;
    let nsubs = msubs.len;
    let fail0 = mg_fail;
    mangle_type(t);
    mg.resize(keep);
    msubs.resize(nsubs);
    mg_fail = fail0;
    let r = mg_tags.len > 0;
    mg_tags.clear();
    return r;
}
var mg_debug: bool = false;
var mg_tail: u8[>..] = [];

// <name> of a declaration.
fn mangle_name(s: i64) {
    let sc = cxs[s].dscope as i64;
    let k = syms[s].kind as i64;
    let member_fn = k == SK_FUNC && cxs[s].flags & CF_MEMBER != 0 && cxs[s].flags & CF_STATIC == 0;
    if sc <= 0 || (is_std_ns(sc) && !member_fn) {
        if is_std_ns(sc) { mg.append("St"); }
        if internal_linkage(s) { mg.push('L'); }
        unqualified(s);
        mg_name_end = mg.len;
        return;
    }
    mg.push('N');
    if member_fn {
        let f = types[syms[s].ty >> 4].flags as i64;
        if f & TF_MVOLATILE != 0 { mg.push('V'); }
        if f & TF_MCONST != 0 { mg.push('K'); }
        if f & TF_MLREF != 0 { mg.push('R'); }
        if f & TF_MRREF != 0 { mg.push('O'); }
    }
    mangle_prefix(sc);
    if internal_linkage(s) { mg.push('L'); }
    unqualified(s);
    mg_name_end = mg.len;
    mg.push('E');
}

// Internal linkage of a namespace member (C++ [basic.link]p3): static
// functions and variables, and const variables that are not extern or
// inline (members of an unnamed namespace are internal too, but they are
// mangled through the namespace, without the L).
fn internal_linkage(s: i64) -> bool {
    if cxs[s].flags & CF_MEMBER != 0 { return false; }
    let sc = cxs[s].dscope as i64;
    if sc > 0 && in_anon_ns(sc) { return false; }
    if syms[s].sc as i64 == SC_STATIC { return true; }
    if syms[s].kind as i64 == SK_VAR && quals(base_elem_q(syms[s].ty)) & Q_CONST != 0 && quals(base_elem_q(syms[s].ty)) & Q_VOLATILE == 0 &&
       syms[s].sc as i64 != SC_EXTERN && syms[s].flags & SF_INLINE == 0 { return true; }
    return false;
}

fn base_elem_q(t: u32) -> u32 {
    var x = t;
    while kind_of(x) == TY_ARRAY { x = tbase(x); }
    return x;
}

fn in_anon_ns(sc0: i64) -> bool {
    var sc = sc0;
    while sc > 0 {
        if scopes[sc].flags & SCF_ANON != 0 { return true; }
        sc = scopes[sc].parent as i64;
    }
    return false;
}

// <prefix> for scope sc (its enclosing scopes first), registering each
// component as a substitution candidate.
recursive fn mangle_prefix(sc: i64) {
    if sc <= 0 { return; }
    if is_std_ns(sc) { mg.append("St"); return; }
    let i = sub_find(MK_SCOPE | (sc as u64));
    if i >= 0 { sub_emit(i); return; }
    let k = scopes[sc].kind as i64;
    if k == CS_CLASS && scopes[sc].rec >= 0 {
        // a class: an explicit specialization is <template-prefix> <template-args>
        let r = scopes[sc].rec as i64;
        let cs = crecs[r].sym as i64;
        if cs >= 0 && cxs[cs].flags & CF_SPEC != 0 && cxs[cs].tmpl >= 0 {
            let t = cxs[cs].tmpl as i64;
            mangle_tmpl_prefix(tmpls[t].sym as i64, scopes[sc].parent as i64);
            mangle_targs(cxs[cs].targs as i64);
            msubs.push(MK_SCOPE | (sc as u64));
            return;
        }
    }
    mangle_prefix(scopes[sc].parent as i64);
    if k == CS_NS && scopes[sc].flags & SCF_ANON != 0 {
        mg.append("12_GLOBAL__N_1");
    } else if scopes[sc].name == 0 {
        mg_fail = true;
    } else {
        source_name(ident_text(scopes[sc].name as i64));
    }
    msubs.push(MK_SCOPE | (sc as u64));
}

// <template-prefix>: the template's scope, then its name.
recursive fn mangle_tmpl_prefix(tsym: i64, parent: i64) {
    let i = sub_find(MK_TMPL | (tsym as u64));
    if i >= 0 { sub_emit(i); return; }
    mangle_prefix(parent);
    source_name(ident_text(syms[tsym].name as i64));
    msubs.push(MK_TMPL | (tsym as u64));
}

fn unqualified(s: i64) {
    let fl = cxs[s].flags;
    if fl & CF_CTOR != 0 { mg.append("C1"); return; }
    if fl & CF_DTOR != 0 { mg.append("D1"); return; }
    if fl & CF_CONV != 0 {
        mg.append("cv");
        mangle_type(types[syms[s].ty >> 4].base);
        return;
    }
    if fl & CF_OPERATOR != 0 {
        // unary + - * &: a member with no parameter, a non-member with one
        let np = types[syms[s].ty >> 4].n;
        let unary = if fl & CF_MEMBER != 0 && fl & CF_STATIC == 0 { np == 0 } else { np == 1 };
        mg.append(if unary { op_code_unary(cxs[s].op as i64) } else { op_code(cxs[s].op as i64) });
        return;
    }
    let nm = ident_text(syms[s].name as i64);
    if nm.len == 0 { mg_fail = true; return; }
    source_name(nm);
}

fn op_code(op: i64) -> const u8[:] {
    return match op {
        OP_NEW => "nw", OP_NEW_ARR => "na", OP_DELETE => "dl", OP_DELETE_ARR => "da", OP_PLUS => "pl", OP_MINUS => "mi",
        OP_STAR => "ml", OP_SLASH => "dv", OP_PERCENT => "rm", OP_CARET => "eo", OP_AMP => "an", OP_PIPE => "or",
        OP_TILDE => "co", OP_EXCLAIM => "nt", OP_EQUAL => "aS", OP_LESS => "lt", OP_GREATER => "gt", OP_PLUSEQ => "pL",
        OP_MINUSEQ => "mI", OP_STAREQ => "mL", OP_SLASHEQ => "dV", OP_PERCENTEQ => "rM", OP_CARETEQ => "eO",
        OP_AMPEQ => "aN", OP_PIPEEQ => "oR", OP_LSHIFT => "ls", OP_RSHIFT => "rs", OP_RSHIFTEQ => "rS", OP_LSHIFTEQ => "lS",
        OP_EQEQ => "eq", OP_NE => "ne", OP_LE => "le", OP_GE => "ge", OP_SPACESHIP => "ss", OP_AMPAMP => "aa",
        OP_PIPEPIPE => "oo", OP_PLUSPLUS => "pp", OP_MINUSMINUS => "mm", OP_COMMA => "cm", OP_ARROWSTAR => "pm",
        OP_ARROW => "pt", OP_CALL => "cl", OP_SUBSCRIPT => "ix", _ => "aw",
    };
}

// The unary operators (+x, -x, *p, &x) have their own codes.
fn op_code_unary(op: i64) -> const u8[:] {
    return match op { OP_PLUS => "ps", OP_MINUS => "ng", OP_STAR => "de", OP_AMP => "ad", _ => op_code(op) };
}

fn builtin_code(t: u32) -> const u8[:] {
    let u = unqual(t);
    if u == t_wchar_cxx { return "w"; }
    if u == t_char16 { return "Ds"; }
    if u == t_char32 { return "Di"; }
    if u == t_char8 { return "Du"; }
    return match kind_of(t) {
        TY_VOID => "v", TY_BOOL => "b", TY_CHAR => "c", TY_SCHAR => "a", TY_UCHAR => "h", TY_SHORT => "s",
        TY_USHORT => "t", TY_INT => "i", TY_UINT => "j", TY_LONG => "l", TY_ULONG => "m", TY_LLONG => "x",
        TY_ULLONG => "y", TY_INT128 => "n", TY_UINT128 => "o", TY_FLOAT => "f", TY_DOUBLE => "d",
        TY_LDOUBLE => "e", TY_FLOAT128 => "g", TY_FLOAT16 => "DF16_", TY_BF16 => "DF16b", TY_NULLPTR => "Dn",
        _ => "",
    };
}

recursive fn mangle_type(t: u32) {
    let k = kind_of(t);
    let q = quals(t);
    let bc = builtin_code(t);
    if q & (Q_CONST | Q_VOLATILE | Q_RESTRICT) != 0 && k != TY_FUNC {
        let i = sub_find(MK_TYPE | (t as u64));
        if i >= 0 { sub_emit(i); return; }
        if q & Q_RESTRICT != 0 { mg.push('r'); }
        if q & Q_VOLATILE != 0 { mg.push('V'); }
        if q & Q_CONST != 0 { mg.push('K'); }
        mangle_type(t & ~((Q_CONST | Q_VOLATILE | Q_RESTRICT) as! u32));
        msubs.push(MK_TYPE | (t as u64));
        return;
    }
    if bc.len > 0 && k != TY_ENUM { mg.append(bc); return; }
    let i = sub_find(MK_TYPE | (unqual(t) as u64));
    if i >= 0 { sub_emit(i); return; }
    if k == TY_POINTER { mg.push('P'); mangle_type(tbase(t)); }
    else if k == TY_LREF { mg.push('R'); mangle_type(tbase(t)); }
    else if k == TY_RREF { mg.push('O'); mangle_type(tbase(t)); }
    else if k == TY_ARRAY {
        mg.push('A');
        let n = types[t >> 4].n;
        if n >= 0 { format(mg, n); }
        mg.push('_');
        mangle_type(tbase(t));
    } else if k == TY_FUNC {
        mangle_fn_type(t);
    } else if k == TY_MEMPTR {
        mg.push('M');
        mangle_type(types[t >> 4].extra);
        let mt = tbase(t);
        if kind_of(mt) == TY_FUNC {
            let f = types[mt >> 4].flags as i64;
            if f & TF_MVOLATILE != 0 { mg.push('V'); }
            if f & TF_MCONST != 0 { mg.push('K'); }
        }
        mangle_type(mt);
    } else if k == TY_STRUCT || k == TY_UNION {
        let r = rec_of(t);
        if r < crecs.len && crecs[r].scope >= 0 {
            note_tags(scopes[crecs[r].scope].parent as i64);
            mangle_class_name(crecs[r].scope as i64);
        } else { mg_fail = true; }
        // the class's name was registered as its scope; the type is the same entity
        return;
    } else if k == TY_ENUM {
        let e = types[t >> 4].extra as i64;
        let es = enum_scope(e);
        if es >= 0 { mangle_class_name(es); } else { mg_fail = true; }
        return;
    } else if k == TY_COMPLEX {
        mg.push('C');
        mangle_type(tbase(t));
    } else if k == TY_VECTOR || k == TY_EXTVECTOR {
        format(mg, "Dv", types[t >> 4].n, "_");
        mangle_type(tbase(t));
    } else if k == TY_DEPSPEC {
        // an uninstantiated specialization with concrete arguments
        let ts = types[t >> 4].extra as i64;
        let args = types[t >> 4].n;
        if mg_debug { write_stderr(str("depspec ts=", ts, " args=", args, " dep=", args_dependent(args as i32), " dsc=", cxs[ts].dscope, "\n")); }
        if args_dependent(args as i32) { mg_fail = true; return; }
        let dsc = cxs[ts].dscope as i64;
        note_tags(dsc);
        if dsc <= 0 || is_std_ns(dsc) {
            if is_std_ns(dsc) && std_abbrev(ts, args, t) { return; }
            let j = sub_find(MK_TMPL | (ts as u64));
            if j >= 0 { sub_emit(j); } else {
                if is_std_ns(dsc) { mg.append("St"); }
                source_name(ident_text(syms[ts].name as i64));
                msubs.push(MK_TMPL | (ts as u64));
            }
            mangle_targs(args);
        } else {
            mg.push('N');
            mangle_tmpl_prefix(ts, dsc);
            mangle_targs(args);
            mg.push('E');
        }
    } else {
        mg_fail = true;
        return;
    }
    msubs.push(MK_TYPE | (unqual(t) as u64));
}

// A class or enum type's name (the scope that names it): unscoped or nested.
recursive fn mangle_class_name(sc: i64) {
    let i = sub_find(MK_SCOPE | (sc as u64));
    if i >= 0 { sub_emit(i); return; }
    let parent = scopes[sc].parent as i64;
    if parent <= 0 || is_std_ns(parent) {
        // unscoped (::X or ::std::X): a template specialization is <unscoped-template-name> <template-args>
        let r = scopes[sc].rec as i64;
        if r >= 0 {
            let cs = crecs[r].sym as i64;
            if cs >= 0 && cxs[cs].flags & CF_SPEC != 0 && cxs[cs].tmpl >= 0 {
                let ts = tmpls[cxs[cs].tmpl].sym as i64;
                if is_std_ns(parent) { mg.append("St"); }
                let j = sub_find(MK_TMPL | (ts as u64));
                if j >= 0 { sub_emit(j); } else {
                    source_name(ident_text(syms[ts].name as i64));
                    msubs.push(MK_TMPL | (ts as u64));
                }
                mangle_targs(cxs[cs].targs as i64);
                msubs.push(MK_SCOPE | (sc as u64));
                return;
            }
        }
        if is_std_ns(parent) {
            mg.append("St");
        }
        if scopes[sc].name == 0 { mg_fail = true; return; }
        source_name(ident_text(scopes[sc].name as i64));
        msubs.push(MK_SCOPE | (sc as u64));
        return;
    }
    mg.push('N');
    mangle_prefix(sc);
    mg.push('E');
}

// The std:: abbreviations: Sa (allocator), Sb (basic_string) as template
// names, and Si/So/Sd for basic_istream/ostream/iostream<char,
// char_traits<char>> (Ss is the old ABI's string, which libstdc++'s
// __cxx11 namespace does not use).
recursive fn std_abbrev(ts: i64, args: i64, t: u32) -> bool {
    let nm = ident_text(syms[ts].name as i64);
    if (nm == "basic_istream" || nm == "basic_ostream" || nm == "basic_iostream") && char_traits_char(args) {
        mg.append(if nm == "basic_istream" { "Si" } else if nm == "basic_ostream" { "So" } else { "Sd" });
        return true;
    }
    if nm == "allocator" || nm == "basic_string" {
        let j = sub_find(MK_TMPL | (ts as u64));
        if j >= 0 { sub_emit(j); } else { mg.append(if nm == "allocator" { "Sa" } else { "Sb" }); }
        mangle_targs(args);
        msubs.push(MK_TYPE | (unqual(t) as u64));
        return true;
    }
    return false;
}

// Is the argument list (char, std::char_traits<char>)?
fn char_traits_char(args: i64) -> bool {
    if tl_count(args) != 2 { return false; }
    let a = tl_arg(args, 0);
    let b = tl_arg(args, 1);
    if a.kind as i64 != TA_TYPE || a.ty != t_char || b.kind as i64 != TA_TYPE { return false; }
    let k = kind_of(b.ty);
    var tsym: i64 = -1;
    var targs: i64 = -1;
    if k == TY_STRUCT {
        let r = rec_of(b.ty);
        let cs = crecs[r].sym as i64;
        if cs < 0 || cxs[cs].flags & CF_SPEC == 0 { return false; }
        tsym = tmpls[cxs[cs].tmpl].sym as i64;
        targs = cxs[cs].targs as i64;
    } else if k == TY_DEPSPEC {
        tsym = types[b.ty >> 4].extra as i64;
        targs = types[b.ty >> 4].n;
    } else { return false; }
    if ident_text(syms[tsym].name as i64) != "char_traits" || !is_std_ns(cxs[tsym].dscope as i64) { return false; }
    return tl_count(targs) == 1 && tl_arg(targs, 0).kind as i64 == TA_TYPE && tl_arg(targs, 0).ty == t_char;
}

// ---------------------------------------------------------------------------
// ABI tags (abi_tag on namespaces: libstdc++'s inline namespace __cxx11).

var ns_abi_tag = dictionary<u64, u64> {};    // scope -> (strbytes offset << 32 | length)
var mg_tags: u64[>..<] = [];                 // the tags met while mangling

fn note_tags(sc0: i64) {
    var sc = sc0;
    while sc > 0 {
        let g = ns_abi_tag.get(sc as u64);
        if g {
            var seen = false;
            for x in mg_tags { if x == g { seen = true; } }
            if !seen { mg_tags.push(g); }
        }
        sc = scopes[sc].parent as i64;
    }
}

fn tag_text(g: u64) -> const u8[:] {
    let o = (g >> 32) as i64;
    let l = (g & 0xFFFFFFFF) as i64;
    return strbytes[o..o + l];
}

recursive fn mangle_fn_type(t: u32) {
    let f = types[t >> 4];
    mg.push('F');
    mangle_type(f.base);
    if f.n == 0 && f.flags & TF_VARIADIC == 0 { mg.push('v'); }
    for i in f.n { mangle_type(tparams[f.extra + i]); }
    if f.flags & TF_VARIADIC != 0 { mg.push('z'); }
    if (f.flags as i64) & TF_MLREF != 0 { mg.push('R'); }
    if (f.flags as i64) & TF_MRREF != 0 { mg.push('O'); }
    mg.push('E');
}

recursive fn mangle_targs(l: i64) {
    mg.push('I');
    let n = tl_count(l);
    for i in n {
        let a = tl_arg(l, i);
        let ak = a.kind as i64;
        if ak == TA_TYPE { mangle_type(a.ty); }
        else if ak == TA_VALUE {
            if a.ty == 0 || is_opaque(a.ty) { mg_fail = true; continue; }
            mg.push('L');
            mangle_type(a.ty);
            if kind_of(a.ty) == TY_BOOL { format(mg, a.v); }
            else if a.v < 0 { mg.push('n'); format(mg, 0 - a.v); }
            else { format(mg, a.v); }
            mg.push('E');
        } else {
            mg_fail = true;
        }
    }
    mg.push('E');
}
