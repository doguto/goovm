// goosecc D1: calls, overload resolution, conversions involving classes,
// constructors and initialization.
//
// D1 resolves a call when the candidates are non-template functions and
// the arguments' types are known (C++ [over.match], with implicit
// conversion sequences ranked as exact match, promotion, conversion,
// user-defined conversion, ellipsis); a call that needs template argument
// deduction is opaque (stage D2).

namespace cx;

import std;
import dictionary;
import .common;
import .types;
import .ast;
import .sema;
import .pp;
import .expr;
import .parse;
import .init;
import .builtins;
import .cx_core;
import .cx_names;
import .cx_decl;
import .cx_class;
import .cx_tmpl;
import .cx_decl2;
import .cx_expr;
import .cx_sema;

let CK_DERIVED2BASE = 30;   // a derived class glvalue / pointer to a base (cast offset in the node's v)
let CK_BASE2DERIVED = 31;
let CK_USERCONV = 32;       // a user-defined conversion (b = the conversion function or constructor)

// Is class `base` (a record type) a base of class `der`? The offset of the
// base subobject (-1: not a base, -2: virtual or ambiguous).
recursive fn base_offset(der: u32, base: u32) -> i64 {
    if unqual(der) == unqual(base) { return 0; }
    let r = rec_of(der);
    if r >= crecs.len { return -1; }
    let cr = crecs[r];
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if !is_record(b.ty) { continue; }
        let o = base_offset(b.ty, base);
        if o >= 0 {
            if b.flags & BF_VIRTUAL != 0 { return -2; }
            return b.offset + o;
        }
        if o == -2 { return -2; }
    }
    return -1;
}

// A derived-class glvalue converted to its base `to` (an lvalue), or 0.
fn derived_to_base_lv(e: u32, to: u32, loc: u32) -> u32 {
    let from = nodes[e].ty;
    if !is_record(from) || !is_record(to) { return 0; }
    let o = base_offset(unqual(from), unqual(to));
    if o < 0 { return 0; }
    let n = node_v(N_ICAST, CK_DERIVED2BASE, with_q(unqual(to), quals(from)), e as i64, 0, 0, loc, o);
    nodes[n].flags = nodes[e].flags & (NF_LVALUE | NF_XVALUE);
    return n;
}

// ---------------------------------------------------------------------------
// Candidates and conversion sequences.

let RK_EXACT = 1;
let RK_PROMO = 2;
let RK_CONV = 3;
let RK_USER = 4;
let RK_ELLIPSIS = 5;
let RK_NONE = 99;

// The rank of converting expression e to parameter type p (0: not viable).
fn conv_rank(e: u32, p: u32) -> i64 {
    if is_opq(e) || is_opaque(p) { return RK_CONV; }
    var t = nodes[e].ty;
    let pt = nonref(p);
    if nodes[e].kind as i64 == N_INITBRACE { return RK_USER; }
    if nodes[e].kind as i64 == N_FUNCREF { return if is_pointer(pt) || is_func(pt) || is_ref(p) { RK_EXACT } else { RK_NONE }; }
    if is_ref(p) {
        // reference binding: same type (cv can be added), or a base
        let lv = is_lvalue(e) && nodes[e].flags & NF_XVALUE == 0;
        if kind_of(p) == TY_LREF && quals(pt) & Q_CONST == 0 && !lv { return RK_NONE; }
        if kind_of(p) == TY_RREF && lv { return RK_NONE; }
        if unqual(t) == unqual(pt) {
            if quals(t) & ~quals(pt) != 0 { return RK_NONE; }
            return RK_EXACT;
        }
        if is_record(t) && is_record(pt) && base_offset(unqual(t), unqual(pt)) >= 0 { return RK_CONV; }
        if kind_of(p) == TY_LREF && quals(pt) & Q_CONST == 0 { return RK_NONE; }
        // binds to a temporary of the converted value
        return conv_rank_val(e, unqual(pt));
    }
    return conv_rank_val(e, unqual(pt));
}

fn conv_rank_val(e: u32, p: u32) -> i64 {
    var t = unqual(nodes[e].ty);
    if is_array(t) { t = mk_ptr(tbase(t)); }
    else if is_func(t) { t = mk_ptr(t); }
    if t == p { return RK_EXACT; }
    let kt = kind_of(t);
    let kp = kind_of(p);
    if is_record(p) || is_record(t) {
        if is_record(p) && is_record(t) && base_offset(t, p) >= 0 { return RK_CONV; }
        return RK_USER;     // a constructor or a conversion function may apply
    }
    if is_arith(t) || kt == TY_ENUM {
        if !(is_arith(p) || kp == TY_ENUM) {
            if kp == TY_BOOL { return RK_CONV; }
            if is_pointer(p) && is_null_const(e) { return RK_CONV; }
            return RK_NONE;
        }
        if kp == TY_ENUM { return RK_NONE; }     // no implicit conversion to an enum
        if kt == TY_ENUM && is_scoped_enum(t) { return RK_NONE; }
        // promotions: to int from smaller integers, to double from float
        if kp == TY_INT && (kt == TY_BOOL || kt == TY_CHAR || kt == TY_SCHAR || kt == TY_UCHAR || kt == TY_SHORT || kt == TY_USHORT) { return RK_PROMO; }
        if kp == TY_DOUBLE && kt == TY_FLOAT { return RK_PROMO; }
        if kt == TY_ENUM && p == promoted_type_of(enum_underlying(t)) { return RK_PROMO; }
        return RK_CONV;
    }
    if kt == TY_POINTER {
        if kp == TY_BOOL { return RK_CONV; }
        if kp != TY_POINTER { return RK_NONE; }
        let a = tbase(t);
        let b = tbase(p);
        if unqual(a) == unqual(b) && quals(a) & ~quals(b) == 0 { return RK_EXACT; }   // qualification adjustment
        if is_void(b) && quals(a) & ~quals(b) == 0 { return RK_CONV; }
        if is_record(a) && is_record(b) && base_offset(unqual(a), unqual(b)) >= 0 { return RK_CONV; }
        return RK_NONE;
    }
    if kt == TY_NULLPTR {
        if kp == TY_POINTER || kp == TY_MEMPTR || kp == TY_NULLPTR { return RK_CONV; }
        if kp == TY_BOOL { return RK_CONV; }
        return RK_NONE;
    }
    if kt == TY_MEMPTR { return if kp == TY_BOOL { RK_CONV } else if t == p { RK_EXACT } else { RK_NONE }; }
    return RK_NONE;
}

// The candidates of a call: viable functions of the chain s0 for the
// arguments nscratch[mark..]. The best one, or -1 when there is none or
// the choice needs what D1 does not do (templates, ties).
var cand_ranks: i64[>..<] = [];
fn best_candidate(s0: i64, mark: i64, has_obj: bool) -> i64 {
    let nargs = nscratch.len - mark;
    var best: i64 = -1;
    var best_rank0: i64 = 0;
    let rmark = cand_ranks.len;
    var tie = false;
    var s = s0;
    var any_tmpl = false;
    while s >= 0 {
        let f = resolve(s);
        if f >= 0 && visible(s) && syms[f].kind as i64 == SK_TEMPLATE { any_tmpl = true; }
        // (a function met again through a using-declaration is the same candidate)
        if f >= 0 && f != best && visible(s) && syms[f].kind as i64 == SK_FUNC && cxs[f].flags & (CF_PATTERN | CF_DELETED) == 0 {
            let ft = types[syms[f].ty >> 4];
            let np = ft.n;
            let variadic = ft.flags & TF_VARIADIC != 0;
            var ok = nargs == np || (variadic && nargs >= np);
            if !ok && nargs < np { ok = defaults_from(f, nargs); }
            if ok {
                // the ranks of the arguments
                let cm = cand_ranks.len;
                var viable = true;
                for i in nargs {
                    var r = RK_ELLIPSIS;
                    if i < np { r = conv_rank(nscratch[mark + i], tparams[ft.extra + i]); }
                    if r == RK_NONE { viable = false; break; }
                    cand_ranks.push(r);
                }
                if viable {
                    if best < 0 {
                        best = f;
                        // keep the best's ranks at rmark
                        move_ranks(rmark, cm, nargs);
                    } else {
                        let c = compare_ranks(cm, rmark, nargs);
                        if c > 0 { best = f; move_ranks(rmark, cm, nargs); tie = false; }
                        else if c == 0 { tie = true; }
                    }
                }
                cand_ranks.resize(rmark + (if best >= 0 { nargs } else { 0 }));
            }
        }
        s = cxs[s].nnext as i64;
    }
    var exact = best >= 0 && !tie;
    if exact && any_tmpl {
        // a non-template function whose parameters (not references) all
        // match exactly: no function template specialization is better
        let ft = types[syms[best].ty >> 4];
        for i in nargs {
            if cand_ranks[rmark + i] != RK_EXACT { exact = false; }
            if i < ft.n && is_ref(tparams[ft.extra + i]) { exact = false; }
        }
        if ft.n != nargs { exact = false; }
    }
    cand_ranks.resize(rmark);
    if any_tmpl && exact { return best; }
    if tie || any_tmpl { return -1; }
    return best;
}

fn move_ranks(dst: i64, src0: i64, n: i64) {
    if dst == src0 { return; }
    for i in n { cand_ranks[dst + i] = cand_ranks[src0 + i]; }
}

// 1 if the ranks at a are better than at b, -1 worse, 0 neither.
fn compare_ranks(a: i64, b: i64, n: i64) -> i64 {
    var better = false;
    var worse = false;
    for i in n {
        if cand_ranks[a + i] < cand_ranks[b + i] { better = true; }
        if cand_ranks[a + i] > cand_ranks[b + i] { worse = true; }
    }
    if better && !worse { return 1; }
    if worse && !better { return -1; }
    return 0;
}

// Do the parameters of f from index i on all have default arguments?
fn defaults_from(f: i64, i: i64) -> bool {
    let st, n = fn_param_list(f);
    if st < 0 { return false; }
    for j in i..n {
        if cxs[nlist[st + j]].body == 0 { return false; }
    }
    return true;
}

// ---------------------------------------------------------------------------
// Calls.

recursive fn mk_call_cx(callee: u32, mark: i64, loc: u32) -> u32 {
    for i in mark..nscratch.len { if is_opq(nscratch[i]) && nodes[nscratch[i]].kind as i64 != N_FUNCREF { return opaque_node(loc); } }
    let ck = nodes[callee].kind as i64;
    if ck == N_FUNCREF {
        let obj = nodes[callee].b;
        if nodes[callee].c != 0 { return opaque_node(loc); }     // explicit template arguments
        let f = best_candidate(nodes[callee].a as i64, mark, obj != 0);
        if f < 0 { return opaque_node(loc); }
        return build_call(f, obj, mark, loc, nodes[callee].op != 0);
    }
    if is_opq(callee) { return opaque_node(loc); }
    let t = nodes[callee].ty;
    if is_record(t) {
        // operator()
        let sc = type_scope(t);
        if sc < 0 { return opaque_node(loc); }
        let s = class_lookup(sc, op_ids[OP_CALL]);
        if s < 0 { return opaque_node(loc); }
        let f = best_candidate(s, mark, true);
        if f < 0 { return opaque_node(loc); }
        return build_call(f, callee, mark, loc, false);
    }
    if (is_pointer(t) && is_func(tbase(t))) || is_func(t) {
        let ft = if is_func(t) { t } else { tbase(t) };
        if !cish_call(ft, mark) {
            return typed_result(types[ft >> 4].base, loc);
        }
        return mk_call(callee, mark, loc);
    }
    return opaque_node(loc);
}

// Are the parameter, argument and return types all C's (so that C's
// mk_call converts them)?
fn cish_call(ft: u32, mark: i64) -> bool {
    let f = types[ft >> 4];
    if !cish(f.base) && !is_void(f.base) { return false; }
    for i in f.n { if !cish(tparams[f.extra + i]) { return false; } }
    for i in mark..nscratch.len {
        let a = nscratch[i];
        if !cish_node(a) || kind_of(nodes[a].ty) == TY_NULLPTR { return false; }
    }
    return true;
}

// An expression of a call's result type that D1 does not lower yet.
fn typed_result(ret: u32, loc: u32) -> u32 {
    let n = node(N_CXX, 0, nonref(ret), 0, 0, 0, loc);
    if is_ref(ret) { nodes[n].flags = (NF_LVALUE | (if kind_of(ret) == TY_RREF { NF_XVALUE } else { 0 })) as! u16; }
    if is_opaque(ret) { nodes[n].flags = nodes[n].flags | NF_DEP; }
    return n;
}

// A call of the chosen function f (obj: the object for a member function,
// 0 none).
recursive fn build_call(f: i64, obj: u32, mark: i64, loc: u32, qualified: bool) -> u32 {
    if cg_on { return cg_call(f, obj, mark, loc, qualified); }
    let ft = syms[f].ty;
    let member = cxs[f].flags & CF_MEMBER != 0 && cxs[f].flags & CF_STATIC == 0;
    if !member && cish_call(ft, mark) && !has_defaults_needed(f, mark) {
        let r = node(N_DECLREF, 0, ft, f, 0, 0, loc);
        syms[f].flags = syms[f].flags | SF_USED;
        return mk_call(r, mark, loc);
    }
    return typed_result(types[ft >> 4].base, loc);
}

fn has_defaults_needed(f: i64, mark: i64) -> bool { (nscratch.len - mark) < types[syms[f].ty >> 4].n }

// &f for an overload set: the single function, or opaque.
fn funcref_addr(e: u32, loc: u32) -> u32 {
    var s = nodes[e].a as i64;
    var found: i64 = -1;
    var n = 0;
    while s >= 0 {
        let f = resolve(s);
        if f >= 0 && (syms[f].kind as i64 == SK_FUNC || syms[f].kind as i64 == SK_TEMPLATE) { found = f; n++; }
        s = cxs[s].nnext as i64;
    }
    if n != 1 || syms[found].kind as i64 != SK_FUNC || cxs[found].flags & CF_MEMBER != 0 { return dep_node(t_unknown, loc); }
    let r = node(N_DECLREF, 0, syms[found].ty, found, 0, 0, loc);
    syms[found].flags = syms[found].flags | SF_USED;
    return node(N_UNARY, U_ADDR, mk_ptr(syms[found].ty), r as i64, 0, 0, loc);
}

// ---------------------------------------------------------------------------
// Operators on classes (D1: opaque unless a non-template candidate is
// found and selected; see build_call).

recursive fn overloaded_binop(op: i64, l: u32, r: u32, loc: u32) -> u32 {
    if cg_on { return cg_operator(op, l, r, loc, false); }
    return 0;
}
recursive fn overloaded_assign(op: i64, l: u32, r: u32, loc: u32, tok: i64) -> u32 {
    if cg_on { return cg_assign(op, l, r, loc, tok); }
    return 0;
}
recursive fn overloaded_unop(op: i64, e: u32, loc: u32, post: bool) -> u32 {
    if cg_on { return cg_operator(op, e, 0, loc, post); }
    return 0;
}
recursive fn overloaded_subscript(b: u32, i: u32, loc: u32) -> u32 {
    if cg_on { return cg_operator(OP_SUBSCRIPT, b, i, loc, false); }
    return 0;
}
recursive fn overloaded_arrow(b: u32, loc: u32) -> u32 {
    if cg_on { return cg_operator(OP_ARROW, b, 0, loc, false); }
    return 0;
}
recursive fn conv_to_bool(e: u32) -> u32 {
    if cg_on && !is_opq(e) {
        let c = user_conv(e, t_bool, nodes[e].loc);
        if c != 0 && !is_opq(c) { return to_bool(c); }
    }
    return dep_node(t_bool, nodes[e].loc);
}
recursive fn cast_to_class(t: u32, e: u32, loc: u32) -> u32 { return 0; }

// T(args) / T{args} of class type: a prvalue of T.
recursive fn construct_class(t: u32, mark: i64, loc: u32, braces: bool) -> u32 {
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    return node_v(N_CTOR, 0, unqual(t), 0, 0, count, loc, start);
}

// T x(args).
recursive fn mk_construct_init(t: u32, mark: i64, loc: u32) -> u32 {
    if is_opaque(t) { return dep_node(t, loc); }
    for i in mark..nscratch.len { if is_opq(nscratch[i]) { return dep_node(t, loc); } }
    if is_record(t) { return construct_class(t, mark, loc, false); }
    if nscratch.len - mark == 1 { return nscratch[mark]; }
    return dep_node(t, loc);
}

// The initializer of variable s converted to its type (form: 1 =, 2 (),
// 3 {}).
recursive fn init_convert(s: i64, init: u32, form: i64, loc: u32) -> u32 {
    let t = syms[s].ty;
    if is_opaque(t) { return init; }
    if is_opq(init) && nodes[init].kind as i64 != N_INITBRACE { return init; }
    if is_array(t) && nodes[init].kind as i64 == N_STRING {
        // char a[] = "..."
        let st = nodes[init].ty;
        if types[t >> 4].n < 0 { syms[s].ty = with_q(mk_array(tbase(t), types[st >> 4].n), quals(t)); }
        nodes[init].ty = unqual(syms[s].ty);
        nodes[init].flags = nodes[init].flags | NF_STRINIT;
        return init;
    }
    if is_array(t) {
        if types[t >> 4].n < 0 && nodes[init].kind as i64 == N_INITBRACE {
            // T a[] = { ... }: the bound is the number of elements (an element
            // of aggregate type needs its own braces here)
            let et = tbase(t);
            let n = nodes[init].c as i64;
            var ok = true;
            if is_aggregate(et) || is_record(et) {
                for i in n {
                    let el = nlist[nodes[init].v + i];
                    // a braced element, or an expression of the element's class (no brace elision)
                    if nodes[el].kind as i64 != N_INITBRACE && !(is_record(et) && unqual(nodes[el].ty) == unqual(et)) { ok = false; }
                }
            }
            if ok { syms[s].ty = with_q(mk_array(et, n), quals(t)); }
        }
        return init;
    }
    if nodes[init].kind as i64 == N_INITBRACE || is_record(t) || is_ref(t) || !cish(t) || !cish_node(init) { return init; }
    if kind_of(nodes[init].ty) == TY_NULLPTR {
        if is_pointer(t) { return icast(init, CK_NULL2PTR, unqual(t)); }
        return init;
    }
    return assign_convert(rv(init), t, loc, 1);
}

fn default_init(s: i64, loc: u32) -> u32 { return 0; }
