// goosecc D2: implicit conversion sequences (C++ [over.best.ics]) and
// their ranking ([over.ics.rank]), for overload resolution.
//
// An Ics describes how an argument expression converts to a parameter
// type: a standard conversion sequence (with its rank and what the ranking
// rules look at: identity, qualification adjustment, derived-to-base,
// conversion to bool, reference binding), a user-defined conversion (the
// constructor or conversion function, then a second standard conversion),
// the ellipsis, or none (not viable). The user-defined conversion is
// chosen here too ([over.match.copy], [over.match.conv], [over.match.ref]).

namespace cx;

import std;
import dictionary;
import .common;
import .types;
import .ast;
import .sema;
import .expr;
import .cx_core;
import .cx_names;
import .cx_decl;
import .cx_tmpl;
import .cx_inst;

let ICS_BAD = 0;
let ICS_STD = 1;
let ICS_USER = 2;
let ICS_ELLIPSIS = 3;
let ICS_AMBIG = 4;          // more than one user-defined conversion: viable, ranks as a user-defined one

let IF_IDENT = 1;           // no conversion besides an lvalue transformation
let IF_QUAL = 2;            // a qualification adjustment (or a reference adding cv)
let IF_BOOL = 4;            // pointer, member pointer or nullptr to bool
let IF_REF = 8;             // binds a reference
let IF_RVREF = 16;          // binds an rvalue reference
let IF_D2B = 32;            // derived-to-base (class, pointer, reference)
let IF_LVT = 64;            // array / function decay
let IF_PTRVOID = 128;       // pointer to void*
let IF_TEMP = 256;          // a reference bound to a temporary
let IF_UNKNOWN = 512;       // involves what is not computed: viable, rank unknown
let IF_FNREF = 1024;        // binds a reference to a function lvalue
let IF_IMPLOBJ = 2048;      // the implicit object parameter
let IF_LIST = 4096;         // a list-initialization sequence
let IF_NARROW = 8192;       // a narrowing list conversion
let IF_NOREFQ = 16384;      // the implicit object parameter of a member function without ref-qualifier

struct Ics {
    kind: u8,
    rank: u8,           // RK_EXACT, RK_PROMO, RK_CONV (the second standard conversion of a user-defined one)
    flags: u16,
    user: i32,          // ICS_USER: the constructor or conversion function
    from: u32,          // the standard conversion's source type (D2B ranking)
    to: u32,            // and its target type
}

fn ics_bad() -> Ics { Ics { kind: ICS_BAD as! u8, rank: RK_NONE as! u8, flags: 0, user: -1, from: 0, to: 0 } }
fn ics_std(rank: i64, flags: i64, from: u32, to: u32) -> Ics {
    Ics { kind: ICS_STD as! u8, rank: rank as! u8, flags: flags as! u16, user: -1, from: from, to: to }
}
fn ics_unknown() -> Ics { Ics { kind: ICS_STD as! u8, rank: RK_CONV as! u8, flags: IF_UNKNOWN as! u16, user: -1, from: 0, to: 0 } }

// ---------------------------------------------------------------------------
// Type relations.

// The promoted type of an integral (or unscoped enum, bool, character)
// type t ([conv.prom]), or 0 when it has none.
recursive fn int_promotion(t: u32) -> u32 {
    let u = unqual(t);
    if u == t_char16 { return t_int; }
    if u == t_char32 { return t_uint; }
    if u == t_char8 { return t_int; }
    if u == t_wchar_cxx { return 0; }       // int-sized already
    let k = kind_of(u);
    if k == TY_ENUM {
        if is_scoped_enum(u) { return 0; }
        let ut = enum_underlying(u);
        let p = int_promotion(ut);
        return if p != 0 { p } else { unqual(ut) };
    }
    if k == TY_BOOL || k == TY_CHAR || k == TY_SCHAR || k == TY_UCHAR || k == TY_SHORT || k == TY_USHORT { return t_int; }
    return 0;
}

fn is_cxx_integral(t: u32) -> bool {
    let k = kind_of(t);
    return (k >= TY_BOOL && k <= TY_UINT128);
}
fn is_cxx_arith(t: u32) -> bool { is_cxx_integral(t) || is_real_float(t) }

// Is class b a base of class d (same class excluded)? (complete d)
fn is_base_of(b: u32, d: u32) -> bool {
    if !is_record(b) || !is_record(d) || unqual(b) == unqual(d) { return false; }
    need_complete(d);
    return base_offset(unqual(d), unqual(b)) != -1;
}

// Reference-related: T1 is T2 or a base of it (cv ignored).
fn ref_related(t1: u32, t2: u32) -> bool {
    if unqual(t1) == unqual(t2) { return true; }
    return is_record(t1) && is_record(t2) && is_base_of(t1, t2);
}

// Reference-compatible: related and cv1 is at least cv2.
fn ref_compatible(t1: u32, t2: u32) -> bool {
    if !ref_related(t1, t2) { return false; }
    let q1 = quals(t1) & (Q_CONST | Q_VOLATILE);
    let q2 = quals(t2) & (Q_CONST | Q_VOLATILE);
    if q2 & ~q1 != 0 { return false; }
    // a function pointer conversion (noexcept) is reference-compatible too (D2: types without noexcept)
    return true;
}

// Can a pointer to `from` convert to a pointer to `to` by a qualification
// conversion (C++ [conv.qual], multi-level), types otherwise the same?
recursive fn qual_convertible(from: u32, to: u32, level: i64, all_const: bool) -> bool {
    let qf = quals(from) & (Q_CONST | Q_VOLATILE);
    let qt0 = quals(to) & (Q_CONST | Q_VOLATILE);
    if qf & ~qt0 != 0 { return false; }
    // adding cv below the first level needs const at every level above
    if level > 0 && qf != qt0 && !all_const { return false; }
    let uf = unqual(from);
    let ut = unqual(to);
    if uf == ut { return true; }
    if is_pointer(uf) && is_pointer(ut) {
        return qual_convertible(tbase(uf), tbase(ut), level + 1, all_const && qt0 & Q_CONST != 0);
    }
    return false;
}

// ---------------------------------------------------------------------------
// Standard conversions (C++ [conv]).

// The standard conversion of expression e (its type and value category) to
// the non-reference, non-class type `to` (or a class type: same class or a
// derived class), flags: the identity / lvalue transformation found so far.
recursive fn std_conv(e: u32, to0: u32, copy_init: bool) -> Ics {
    let to = unqual(to0);
    var from = unqual(nodes[e].ty);
    var lvt = 0;
    if is_opaque(from) || is_opaque(to) { return ics_unknown(); }
    if is_array(from) { from = mk_ptr(tbase(nodes[e].ty)); lvt = IF_LVT; }
    else if is_func(from) { from = mk_ptr(from); lvt = IF_LVT; }
    let kf = kind_of(from);
    let kt = kind_of(to);
    if from == to { return ics_std(RK_EXACT, IF_IDENT | lvt, from, to); }
    if is_record(to) {
        if is_record(from) && is_base_of(to, from) { return ics_std(RK_CONV, IF_D2B, from, to); }
        return ics_bad();
    }
    if is_record(from) { return ics_bad(); }
    // null pointer constants
    if (kt == TY_POINTER || kt == TY_MEMPTR) && (kf == TY_NULLPTR || (is_cxx_integral(from) && is_null_const(e))) {
        return ics_std(RK_CONV, 0, from, to);
    }
    if kt == TY_NULLPTR { return if kf == TY_NULLPTR { ics_std(RK_EXACT, IF_IDENT, from, to) } else { ics_bad() }; }
    // integral and floating promotions
    if is_cxx_integral(to) || kt == TY_ENUM {
        if kt == TY_ENUM { return ics_bad(); }         // nothing converts implicitly to an enum
        if kt == TY_BOOL {
            if is_cxx_arith(from) || (kf == TY_ENUM && !is_scoped_enum(from)) { return ics_std(RK_CONV, 0, from, to); }
            if kf == TY_POINTER || kf == TY_MEMPTR { return ics_std(RK_CONV, IF_BOOL, from, to); }
            if kf == TY_NULLPTR && !copy_init { return ics_std(RK_CONV, IF_BOOL, from, to); }
            return ics_bad();
        }
        if is_cxx_integral(from) || (kf == TY_ENUM && !is_scoped_enum(from)) {
            let p = int_promotion(from);
            if p != 0 && p == to { return ics_std(RK_PROMO, 0, from, to); }
            return ics_std(RK_CONV, 0, from, to);
        }
        if is_real_float(from) { return ics_std(RK_CONV, 0, from, to); }
        return ics_bad();
    }
    if is_real_float(to) {
        if kf == TY_FLOAT && kt == TY_DOUBLE { return ics_std(RK_PROMO, 0, from, to); }
        if is_real_float(from) || is_cxx_integral(from) || (kf == TY_ENUM && !is_scoped_enum(from)) { return ics_std(RK_CONV, 0, from, to); }
        return ics_bad();
    }
    if kt == TY_COMPLEX {
        if kf == TY_COMPLEX || is_cxx_arith(from) { return ics_std(RK_CONV, 0, from, to); }
        return ics_bad();
    }
    if kt == TY_VECTOR || kt == TY_EXTVECTOR {
        if kf == kt && type_size(from) == type_size(to) { return ics_std(RK_CONV, 0, from, to); }
        return ics_bad();
    }
    if kt == TY_POINTER {
        if kf != TY_POINTER { return ics_bad(); }
        let a = tbase(from);
        let b = tbase(to);
        if qual_convertible(a, b, 0, true) { return ics_std(RK_EXACT, IF_QUAL | lvt, from, to); }
        let qa = quals(a) & (Q_CONST | Q_VOLATILE);
        let qb = quals(b) & (Q_CONST | Q_VOLATILE);
        if qa & ~qb != 0 { return ics_bad(); }
        if kind_of(b) == TY_VOID && !is_func(a) { return ics_std(RK_CONV, IF_PTRVOID | (if qa != qb { IF_QUAL } else { 0 }), from, to); }
        if is_record(a) && is_record(b) && is_base_of(b, a) { return ics_std(RK_CONV, IF_D2B | (if qa != qb { IF_QUAL } else { 0 }), from, to); }
        if is_func(a) && is_func(b) && fn_types_same_but_noexcept(a, b) { return ics_std(RK_EXACT, 0, from, to); }
        return ics_bad();
    }
    if kt == TY_MEMPTR {
        if kf != TY_MEMPTR { return ics_bad(); }
        if tbase(from) != tbase(to) { return ics_bad(); }
        let cf = types[from >> 4].extra;
        let ct = types[to >> 4].extra;
        if unqual(cf) == unqual(ct) { return ics_std(RK_EXACT, IF_QUAL, from, to); }
        if is_base_of(cf, ct) { return ics_std(RK_CONV, IF_D2B, from, to); }
        return ics_bad();
    }
    return ics_bad();
}

fn fn_types_same_but_noexcept(a: u32, b: u32) -> bool { unqual(a) == unqual(b) }

// ---------------------------------------------------------------------------
// The implicit conversion sequence of expression e to parameter type p.

let CV_COPY = 1;            // copy-initialization (explicit constructors and conversion functions excluded)
let CV_NOUSER = 2;          // no user-defined conversion ([over.best.ics]p4)
let CV_BOOL_CTX = 4;        // contextual conversion to bool (explicit conversion functions allowed)

recursive fn ics_of(e: u32, p: u32, fl: i64) -> Ics {
    let ek = nodes[e].kind as i64;
    if ek == N_INITBRACE { return ics_list(e, p, fl); }
    if ek == N_FUNCREF { return ics_overload_set(e, p, fl); }
    if is_opq(e) || is_opaque(p) { return ics_unknown(); }
    if is_ref(p) { return ics_ref(e, p, fl); }
    let pt = unqual(p);
    let at = nodes[e].ty;
    if is_record(pt) {
        need_complete(pt);
        if is_record(at) && (unqual(at) == pt || is_base_of(pt, at)) {
            // [over.best.ics]p6: the class itself (identity) or a derived class (derived-to-base)
            if unqual(at) == pt { return ics_std(RK_EXACT, IF_IDENT, unqual(at), pt); }
            return ics_std(RK_CONV, IF_D2B, unqual(at), pt);
        }
        if fl & CV_NOUSER != 0 { return ics_bad(); }
        return ics_user(e, pt, fl, false, false);
    }
    if is_record(at) {
        if fl & CV_NOUSER != 0 { return ics_bad(); }
        need_complete(at);
        return ics_user(e, pt, fl, false, false);
    }
    return std_conv(e, pt, fl & CV_COPY != 0);
}

// Reference binding (C++ [dcl.init.ref], [over.ics.ref]).
recursive fn ics_ref(e: u32, p: u32, fl: i64) -> Ics {
    let t1 = tbase(p);
    let t2 = nodes[e].ty;
    let rv_ref = kind_of(p) == TY_RREF;
    let is_fn = is_func(t2);
    let lv = is_lvalue(e) && nodes[e].flags & NF_XVALUE == 0;
    if is_record(t1) { need_complete(t1); }
    if is_record(t2) { need_complete(t2); }
    let q1 = quals(t1) & (Q_CONST | Q_VOLATILE);
    let q2 = quals(t2) & (Q_CONST | Q_VOLATILE);
    let addq = if q1 != q2 { IF_QUAL } else { 0 };
    let d2b = if unqual(t1) != unqual(t2) { IF_D2B } else { 0 };
    let rank = if d2b != 0 { RK_CONV } else { RK_EXACT };
    let fnf = if is_fn { IF_FNREF } else { 0 };
    let compatible = ref_compatible(t1, t2);
    let related = ref_related(t1, t2);
    // an lvalue (or a function) bound directly
    if !rv_ref && lv && compatible {
        return ics_std(rank, IF_REF | addq | d2b | fnf | (if d2b == 0 && addq == 0 { IF_IDENT } else { 0 }), unqual(t2), t1);
    }
    if rv_ref && is_fn && compatible { return ics_std(RK_EXACT, IF_REF | IF_RVREF | fnf, unqual(t2), t1); }
    // a conversion function giving an lvalue (an lvalue reference), [over.match.ref]
    if !rv_ref && is_record(t2) && !related && fl & CV_NOUSER == 0 {
        let u = ics_user(e, p, fl, true, true);
        if u.kind != ICS_BAD { return u; }
    }
    // a non-const lvalue reference binds only lvalues
    if !rv_ref && (q1 & Q_CONST == 0 || q1 & Q_VOLATILE != 0) { return ics_bad(); }
    // an rvalue of a related type (an xvalue, a class or array prvalue) bound directly
    if !lv && compatible && (is_record(t2) || is_array(t2) || nodes[e].flags & NF_XVALUE != 0) {
        return ics_std(rank, IF_REF | addq | d2b | (if rv_ref { IF_RVREF } else { 0 }) | (if d2b == 0 && addq == 0 { IF_IDENT } else { 0 }), unqual(t2), t1);
    }
    if rv_ref && lv && related { return ics_bad(); }
    // a conversion function giving an rvalue
    if is_record(t2) && !related && fl & CV_NOUSER == 0 {
        let u = ics_user(e, p, fl, true, false);
        if u.kind != ICS_BAD { return u; }
    }
    if related && !compatible { return ics_bad(); }
    // a temporary of the referred type, copy-initialized from e
    var c = ics_of(e, unqual(t1), fl | CV_COPY);
    if c.kind == ICS_BAD { return c; }
    c.flags = c.flags | (IF_REF | IF_TEMP | (if rv_ref { IF_RVREF } else { 0 })) as! u16;
    c.to = t1;
    return c;
}

// An overload set (&f, or f where a function pointer is expected): the one
// function matching the target type exactly is an identity conversion.
recursive fn ics_overload_set(e: u32, p: u32, fl: i64) -> Ics {
    var t = nonref(p);
    if is_pointer(t) { t = tbase(t); }
    if kind_of(t) == TY_MEMPTR || is_opaque(t) || is_dep(t) { return ics_unknown(); }
    if !is_func(t) {
        // not a function target: the set's single non-template function
        // decays to a pointer (to bool, void * ...)
        var s = nodes[e].a as i64;
        var f: i64 = -1;
        var n = 0;
        while s >= 0 {
            let x = resolve(s);
            if x >= 0 && visible(s) && (syms[x].kind as i64 == SK_FUNC || syms[x].kind as i64 == SK_TEMPLATE) { f = x; n++; }
            s = cxs[s].nnext as i64;
        }
        if n != 1 || syms[f].kind as i64 != SK_FUNC || nodes[e].b != 0 || nodes[e].c != 0 {
            if is_record(nonref(p)) && fl & CV_NOUSER == 0 {
                // a converting constructor taking the set
                need_complete(unqual(nonref(p)));
                return ics_user(e, unqual(nonref(p)), CV_COPY, false, false);
            }
            return ics_bad();
        }
        if cxs[f].flags & CF_MEMBER != 0 && cxs[f].flags & CF_STATIC == 0 { return ics_unknown(); }
        let a = node(N_CXX, 0, mk_ptr(syms[f].ty), 0, 0, 0, nodes[e].loc);
        return ics_of(a, p, CV_COPY);
    }
    let f = overload_for_target(e, t);
    if f >= 0 { return ics_std(RK_EXACT, IF_IDENT, 0, 0); }
    if f == -2 { return ics_unknown(); }
    return ics_bad();
}

// A braced-init-list (C++ [over.ics.list]).
recursive fn ics_list(e: u32, p: u32, fl: i64) -> Ics {
    let n = nodes[e].c as i64;
    let t = unqual(nonref(p));
    if is_opaque(t) { return ics_unknown(); }
    if is_record(t) {
        need_complete(t);
        // std::initializer_list<X>: every element converts to X
        let el = initlist_elem(t);
        if el != 0 {
            var worst = ics_std(RK_EXACT, IF_IDENT | IF_LIST, 0, 0);
            for i in n {
                let x = nlist[nodes[e].v + i];
                let c = ics_of(x, el, CV_COPY);
                if c.kind == ICS_BAD { return c; }
                if c.flags & IF_UNKNOWN != 0 { return ics_unknown(); }
                if ics_compare(c, worst) < 0 { worst = c; }
            }
            worst.flags = worst.flags | IF_LIST as! u16;
            return worst;
        }
        // a user-defined conversion (a constructor, or aggregate initialization)
        let u = Ics { kind: ICS_USER as! u8, rank: RK_EXACT as! u8, flags: (IF_LIST | IF_UNKNOWN) as! u16, user: -1, from: 0, to: t };
        if n == 1 && fl & CV_NOUSER == 0 {
            let x = nlist[nodes[e].v];
            if is_record(nodes[x].ty) && (unqual(nodes[x].ty) == t || is_base_of(t, nodes[x].ty)) { return ics_of(x, p, fl); }
        }
        return u;
    }
    if n == 0 { return ics_std(RK_EXACT, IF_IDENT | IF_LIST, 0, t); }
    if n == 1 && !is_array(t) {
        let x = nlist[nodes[e].v];
        if nodes[x].kind as i64 == N_INITBRACE { return ics_unknown(); }
        var c = ics_of(x, p, fl);
        c.flags = c.flags | IF_LIST as! u16;
        return c;
    }
    return ics_unknown();
}

// The element type of std::initializer_list<X>, or 0.
fn initlist_elem(t: u32) -> u32 {
    if !is_record(t) { return 0; }
    let cs = crecs[rec_of(t)].sym as i64;
    if cs < 0 || cxs[cs].flags & CF_SPEC == 0 || cxs[cs].tmpl < 0 { return 0; }
    let ts = tmpls[cxs[cs].tmpl].sym as i64;
    if ts < 0 || ident_text(syms[ts].name as i64) != "initializer_list" || !is_std_ns(cxs[ts].dscope as i64) { return 0; }
    let a = cxs[cs].targs as i64;
    if tl_count(a) != 1 || tl_arg(a, 0).kind as i64 != TA_TYPE { return 0; }
    return tl_arg(a, 0).ty;
}

// ---------------------------------------------------------------------------
// User-defined conversions.

var uc_best: i64 = -1;      // the conversion function or constructor ics_user chose (-1)

// The best user-defined conversion of e to type t (a class: its converting
// constructors; e of class type: its conversion functions). ref: binding a
// reference of type t (t is the reference type), lvref_only: the result
// must be an lvalue ([over.match.ref]).
recursive fn ics_user(e: u32, t: u32, fl: i64, ref: bool, lvref_only: bool) -> Ics {
    let target = if ref { nonref(t) } else { t };
    var best: i64 = -1;
    var best1 = ics_bad();      // the conversion into the candidate
    var best2 = ics_bad();      // the conversion of its result to t
    var ambig = false;
    var unknown = false;
    let explicit_ok = fl & CV_COPY == 0 || fl & CV_BOOL_CTX != 0;
    // converting constructors of the target class
    if is_record(target) && !ref {
        let sc = type_scope(target);
        if sc >= 0 {
            var s = scope_find(sc, id_ctor);
            while s >= 0 {
                var f = resolve(s);
                s = cxs[s].nnext as i64;
                if f < 0 { continue; }
                if syms[f].kind as i64 == SK_TEMPLATE {
                    // a constructor template: deduced from e
                    let mk = nscratch.len;
                    nscratch.push(e);
                    let sp = deduce_call(cxs[f].tmpl as i64, -1, mk, 1);
                    nscratch.resize(mk);
                    if sp == -2 { unknown = true; continue; }
                    if sp < 0 { continue; }
                    f = sp;
                }
                if syms[f].kind as i64 != SK_FUNC || cxs[f].flags & (CF_PATTERN | CF_DELETED) != 0 { continue; }
                if cxs[f].flags & CF_EXPLICIT != 0 && fl & CV_COPY != 0 { continue; }
                let ft = types[syms[f].ty >> 4];
                if ft.n < 1 && ft.flags & TF_VARIADIC == 0 { continue; }
                if ft.n > 1 && !defaults_from(f, 1) { continue; }
                let c1 = if ft.n >= 1 { ics_of(e, tparams[ft.extra], CV_COPY | CV_NOUSER) } else { Ics { kind: ICS_ELLIPSIS as! u8, rank: RK_ELLIPSIS as! u8, flags: 0, user: -1, from: 0, to: 0 } };
                if c1.kind == ICS_BAD { continue; }
                if c1.flags & IF_UNKNOWN != 0 { unknown = true; }
                let c2 = ics_std(RK_EXACT, IF_IDENT, target, target);
                let cmp = if best < 0 { 1 } else { user_cand_compare(c1, c2, best1, best2, f, best) };
                if cmp > 0 { best = f; best1 = c1; best2 = c2; ambig = false; }
                else if cmp == 0 { ambig = true; }
            }
        }
    }
    // conversion functions of the source's class (and its bases)
    let src = nodes[e].ty;
    if is_record(src) {
        let mark = conv_fns.len;
        collect_conv_fns(unqual(src), 0);
        for i in mark..conv_fns.len {
            var f = conv_fns[i] as i64;
            if syms[f].kind as i64 == SK_TEMPLATE {
                let sp = deduce_conv_template(cxs[f].tmpl as i64, target);
                if sp == -2 { unknown = true; continue; }
                if sp < 0 { continue; }
                f = sp;
            }
            if cxs[f].flags & CF_EXPLICIT != 0 && !explicit_ok { continue; }
            let rt = types[syms[f].ty >> 4].base;
            // the implied object argument
            let c1 = ics_object(e, f);
            if c1.kind == ICS_BAD { continue; }
            // the result converted to t
            let rlv = kind_of(rt) == TY_LREF;
            var c2 = ics_bad();
            if ref {
                if lvref_only && !rlv { continue; }
                let rn = nonref(rt);
                if ref_compatible(nonref(t), rn) {
                    c2 = ics_std(if unqual(rn) != unqual(nonref(t)) { RK_CONV } else { RK_EXACT }, IF_REF, unqual(rn), unqual(nonref(t)));
                } else if !lvref_only && !ref_related(nonref(t), rn) {
                    // a prvalue converted (a temporary bound)
                    let probe = typed_probe(rt);
                    c2 = std_conv(probe, unqual(nonref(t)), true);
                    if c2.kind == ICS_BAD { continue; }
                } else { continue; }
            } else {
                let probe = typed_probe(rt);
                if is_record(target) {
                    let rn = unqual(nonref(rt));
                    if rn == unqual(target) { c2 = ics_std(RK_EXACT, IF_IDENT, rn, rn); }
                    else if is_base_of(target, rn) { c2 = ics_std(RK_CONV, IF_D2B, rn, unqual(target)); }
                    else { continue; }
                } else {
                    c2 = std_conv(probe, target, fl & CV_COPY != 0);
                }
            }
            if c2.kind == ICS_BAD { continue; }
            if c2.flags & IF_UNKNOWN != 0 { unknown = true; }
            let cmp = if best < 0 { 1 } else { user_cand_compare(c1, c2, best1, best2, f, best) };
            if cmp > 0 { best = f; best1 = c1; best2 = c2; ambig = false; }
            else if cmp == 0 { ambig = true; }
        }
        conv_fns.resize(mark);
    }
    if best < 0 {
        if unknown { return ics_unknown(); }
        return ics_bad();
    }
    uc_best = best;
    if unknown { return ics_unknown(); }
    var r = Ics { kind: (if ambig { ICS_AMBIG } else { ICS_USER }) as! u8, rank: best2.rank, flags: best2.flags, user: best as! i32,
        from: best2.from, to: best2.to };
    if ref { r.flags = r.flags | IF_REF as! u16; if kind_of(t) == TY_RREF { r.flags = r.flags | IF_RVREF as! u16; } }
    return r;
}

// Between two user-defined conversion candidates: the conversions into
// them, then (a tie) the conversions of their results ([over.match.best]p2.2).
recursive fn user_cand_compare(a1: Ics, a2: Ics, b1: Ics, b2: Ics, fa: i64, fb: i64) -> i64 {
    let c = ics_compare(a1, b1);
    if c != 0 { return c; }
    let ta = cxs[fa].flags2 & CF2_FSPEC != 0;
    let tb = cxs[fb].flags2 & CF2_FSPEC != 0;
    if !ta && tb { return 1; }
    if ta && !tb { return -1; }
    return ics_compare(a2, b2);
}

// A typed rvalue node of type t (the value category of a call returning t).
fn typed_probe(t: u32) -> u32 {
    let n = node(N_CXX, 0, nonref(t), 0, 0, 0, 0);
    if is_ref(t) { nodes[n].flags = (NF_LVALUE | (if kind_of(t) == TY_RREF { NF_XVALUE } else { 0 })) as! u16; }
    return n;
}

// The conversion functions of class t and its bases (a derived class's
// hiding the bases' of the same converted type), pushed to conv_fns.
var conv_fns: u32[>..<] = [];
recursive fn collect_conv_fns(t: u32, depth: i64) {
    if depth > 32 { return; }
    let sc = type_scope(t);
    if sc < 0 { return; }
    var s = scope_find(sc, id_conv);
    while s >= 0 {
        let f = resolve(s);
        s = cxs[s].nnext as i64;
        if f < 0 { continue; }
        let k = syms[f].kind as i64;
        if k == SK_FUNC && cxs[f].flags & (CF_PATTERN | CF_DELETED) == 0 {
            let rt = types[syms[f].ty >> 4].base;
            var hidden = false;
            for x in conv_fns {
                if syms[x].kind as i64 == SK_FUNC && types[syms[x].ty >> 4].base == rt { hidden = true; }
            }
            if !hidden { conv_fns.push(f as! u32); }
        } else if k == SK_TEMPLATE {
            conv_fns.push(f as! u32);
        }
    }
    let r = rec_of(t);
    if r >= crecs.len { return; }
    let cr = crecs[r];
    for i in cr.nbases {
        let bt = cbases[cr.bases + i].ty;
        if is_record(bt) { collect_conv_fns(bt, depth + 1); }
    }
}

// The implicit object parameter of non-static member function f for the
// object expression obj (0: the implicit *this) (C++ [over.match.funcs]).
recursive fn ics_object(obj: u32, f: i64) -> Ics {
    if cxs[f].flags & CF_STATIC != 0 || cxs[f].flags & CF_MEMBER == 0 || cxs[f].flags & CF_CTOR != 0 {
        return ics_std(RK_EXACT, IF_IDENT | IF_IMPLOBJ, 0, 0);
    }
    let cls = scope_class_type(cxs[f].dscope as i64);
    if cls == 0 { return ics_unknown(); }
    let ff = types[syms[f].ty >> 4].flags as i64;
    var q: i64 = 0;
    if ff & TF_MCONST != 0 { q = q | Q_CONST; }
    if ff & TF_MVOLATILE != 0 { q = q | Q_VOLATILE; }
    var ot: u32 = 0;
    var lv = true;
    var xv = false;
    if obj == 0 {
        if this_type == 0 || is_opaque(this_type) { return ics_unknown(); }
        ot = tbase(this_type);
    } else {
        if is_opq(obj) { return ics_unknown(); }
        ot = nodes[obj].ty;
        lv = is_lvalue(obj) && nodes[obj].flags & NF_XVALUE == 0;
        xv = nodes[obj].flags & NF_XVALUE != 0;
    }
    if !is_record(ot) { return ics_bad(); }
    let p = with_q(cls, q);
    if !ref_compatible(p, ot) { return ics_bad(); }
    // ref-qualifiers: & needs an lvalue, && an rvalue
    if ff & TF_MLREF != 0 && !lv { if q & Q_CONST == 0 || q & Q_VOLATILE != 0 { return ics_bad(); } }
    if ff & TF_MRREF != 0 && lv { return ics_bad(); }
    let d2b = if unqual(ot) != unqual(cls) { IF_D2B } else { 0 };
    let addq = if quals(ot) & (Q_CONST | Q_VOLATILE) != q { IF_QUAL } else { 0 };
    var fl = IF_REF | IF_IMPLOBJ | d2b | addq;
    if d2b == 0 && addq == 0 { fl = fl | IF_IDENT; }
    if ff & TF_MRREF != 0 { fl = fl | IF_RVREF; }
    if ff & (TF_MLREF | TF_MRREF) == 0 { fl = fl | IF_NOREFQ; }
    let r = ics_std(if d2b != 0 { RK_CONV } else { RK_EXACT }, fl, unqual(ot), p);
    return r;
}

// ---------------------------------------------------------------------------
// Ranking (C++ [over.ics.rank]): 1 if a is better than b, -1 worse, 0 neither.

recursive fn ics_compare(a: Ics, b: Ics) -> i64 {
    if a.flags & IF_UNKNOWN != 0 || b.flags & IF_UNKNOWN != 0 { return 0; }
    let ka = if a.kind as i64 == ICS_AMBIG { ICS_USER } else { a.kind as i64 };
    let kb = if b.kind as i64 == ICS_AMBIG { ICS_USER } else { b.kind as i64 };
    if ka != kb { return if ka < kb { 1 } else { -1 }; }
    if ka == ICS_ELLIPSIS { return 0; }
    if ka == ICS_USER {
        if a.kind as i64 == ICS_AMBIG || b.kind as i64 == ICS_AMBIG || a.user != b.user { return 0; }
    }
    return std_compare(a, b);
}

recursive fn std_compare(a: Ics, b: Ics) -> i64 {
    let fa = a.flags as i64;
    let fb = b.flags as i64;
    // a proper subsequence (identity against a qualification adjustment of the same rank)
    if a.rank == b.rank && a.rank as i64 == RK_EXACT && fa & (IF_REF | IF_IMPLOBJ) == 0 && fb & (IF_REF | IF_IMPLOBJ) == 0 {
        if fa & IF_IDENT != 0 && fb & IF_IDENT == 0 && fb & IF_QUAL != 0 { return 1; }
        if fb & IF_IDENT != 0 && fa & IF_IDENT == 0 && fa & IF_QUAL != 0 { return -1; }
    }
    if a.rank != b.rank { return if a.rank < b.rank { 1 } else { -1 }; }
    // not a conversion to bool beats one
    if fa & IF_BOOL == 0 && fb & IF_BOOL != 0 { return 1; }
    if fa & IF_BOOL != 0 && fb & IF_BOOL == 0 { return -1; }
    // derived-to-base: to the nearer base, from the more derived class
    if fa & (IF_D2B | IF_PTRVOID) != 0 && fb & (IF_D2B | IF_PTRVOID) != 0 {
        let c = d2b_compare(a, b);
        if c != 0 { return c; }
    }
    if fa & IF_PTRVOID == 0 && fa & IF_D2B != 0 && fb & IF_PTRVOID != 0 && unqual(a.from) == unqual(b.from) { return 1; }
    if fb & IF_PTRVOID == 0 && fb & IF_D2B != 0 && fa & IF_PTRVOID != 0 && unqual(a.from) == unqual(b.from) { return -1; }
    // reference bindings
    if fa & IF_REF != 0 && fb & IF_REF != 0 {
        // not for the implicit object parameter of a member function without ref-qualifier
        let noq = fa & IF_NOREFQ != 0 || fb & IF_NOREFQ != 0;
        if !noq && fa & IF_FNREF == 0 && fb & IF_FNREF == 0 {
            // an rvalue reference (to an rvalue) beats an lvalue reference
            if fa & IF_RVREF != 0 && fb & IF_RVREF == 0 { return 1; }
            if fb & IF_RVREF != 0 && fa & IF_RVREF == 0 { return -1; }
        }
        // an lvalue reference to a function beats an rvalue reference to one
        if fa & IF_FNREF != 0 && fb & IF_FNREF != 0 {
            if fa & IF_RVREF == 0 && fb & IF_RVREF != 0 { return 1; }
            if fb & IF_RVREF == 0 && fa & IF_RVREF != 0 { return -1; }
        }
        // the referred types differ in cv only: the less qualified one
        if unqual(a.to) == unqual(b.to) && quals(a.to) != quals(b.to) && a.to != 0 {
            let qa = quals(a.to) & (Q_CONST | Q_VOLATILE);
            let qb = quals(b.to) & (Q_CONST | Q_VOLATILE);
            if qa & ~qb == 0 { return 1; }
            if qb & ~qa == 0 { return -1; }
        }
    }
    // qualification conversions to similar types: the less qualified result
    // (D* -> B* a proper subsequence of D* -> const B*)
    if (fa | fb) & IF_QUAL != 0 && fa & IF_REF == 0 && fb & IF_REF == 0 && is_pointer(a.to) && is_pointer(b.to) &&
       unqual(tbase(a.to)) == unqual(tbase(b.to)) {
        let qa = quals(tbase(a.to)) & (Q_CONST | Q_VOLATILE);
        let qb = quals(tbase(b.to)) & (Q_CONST | Q_VOLATILE);
        if qa != qb {
            if qa & ~qb == 0 { return 1; }
            if qb & ~qa == 0 { return -1; }
        }
    }
    return 0;
}

// Two derived-to-base conversions (or to void*) from or to the same class.
fn d2b_compare(a: Ics, b: Ics) -> i64 {
    var fa = a.from;
    var ta = a.to;
    var fb = b.from;
    var tb = b.to;
    if is_pointer(fa) { fa = tbase(fa); ta = tbase(ta); }
    if is_pointer(fb) { fb = tbase(fb); tb = tbase(tb); }
    fa = unqual(fa); ta = unqual(ta); fb = unqual(fb); tb = unqual(tb);
    if a.flags & IF_PTRVOID != 0 || b.flags & IF_PTRVOID != 0 {
        // B* -> void* is better than D* -> void* (D derived from B)
        if a.flags & IF_PTRVOID != 0 && b.flags & IF_PTRVOID != 0 {
            if is_base_of(fa, fb) { return 1; }
            if is_base_of(fb, fa) { return -1; }
        }
        return 0;
    }
    if fa == fb && ta != tb {
        // C -> B better than C -> A when B derives from A
        if is_base_of(tb, ta) { return 1; }
        if is_base_of(ta, tb) { return -1; }
    }
    if ta == tb && fa != fb {
        // B -> A better than C -> A when C derives from B
        if is_base_of(fa, fb) { return 1; }
        if is_base_of(fb, fa) { return -1; }
    }
    return 0;
}

// A conversion function template converting to type t ([temp.deduct.conv]):
// its specialization, -1 none, -2 not known.
recursive fn deduce_conv_template(tt: i64, t: u32) -> i64 {
    let pf = tmpls[tt].pattern as i64;
    if pf < 0 { return -2; }
    var p = types[syms[pf].ty >> 4].base;
    var a = t;
    if is_ref(p) { p = tbase(p); }
    else {
        if is_array(a) { a = mk_ptr(tbase(a)); } else if is_func(a) { a = mk_ptr(a); }
        a = unqual(a);
        p = unqual(p);
    }
    if is_opaque(a) { return -2; }
    let sv = ded_begin(tt);
    let ok = deduce_type(p, a);
    var res: i64 = -1;
    if ok {
        let full, binds = ded_complete(tt);
        ded_end(sv);
        if !full { return -1; }
        return fspec_decl(tt, binds);
    }
    ded_end(sv);
    return res;
}
