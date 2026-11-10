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
import .cx_conv;

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
recursive fn derived_to_base_lv(e: u32, to: u32, loc: u32) -> u32 {
    let from = nodes[e].ty;
    if !is_record(from) || !is_record(to) { return 0; }
    let o = base_offset(unqual(from), unqual(to));
    if o == -2 && cg_on { return cg_vbase_lv(e, to, loc); }
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
        if is_record(t) && is_record(pt) && base_offset(unqual(t), unqual(pt)) != -1 { return RK_CONV; }
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
        if is_record(p) && is_record(t) && base_offset(t, p) != -1 { return RK_CONV; }
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
        if is_record(a) && is_record(b) && base_offset(unqual(a), unqual(b)) != -1 { return RK_CONV; }
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

// The candidates of a call: the functions of the chain s0 and the
// specializations of its function templates deduced from the arguments
// nscratch[mark..] (C++ [over.match]), ranked by their implicit conversion
// sequences (cx_conv.goose). The best viable one, or -1 when there is
// none (cand_nviable 0), the choice is ambiguous (cand_ambiguous), the
// best is deleted (cand_deleted), or it depends on what is not known yet
// (cand_unknown: a deduction, a substitution or a conversion D2 cannot
// complete). Arguments needing a user-defined conversion are converted in
// place (the conversion function called, or a temporary constructed).
var cand_syms: u32[>..<] = [];
var cand_explicit: i32 = -1;        // the call's explicit template arguments (-1 none)
var cand_unknown: bool = false;
var cand_obj: u32 = 0;              // the object expression of a member call (0: the implicit *this)
var cand_oper: bool = false;        // an operator: a member candidate's object is the first operand
var cand_deleted: bool = false;
var cand_ambiguous: bool = false;
var cand_nviable: i64 = 0;
var cand_ics: Ics[>..<] = [];
var cand_viable: u32[>..<] = [];

recursive fn best_candidate(s0: i64, mark: i64, has_obj: bool) -> i64 {
    let mc = cand_syms.len;
    var unknown = false;
    let explicit = cand_explicit;
    let oper = cand_oper;
    let nargs = nscratch.len - mark;
    var s = s0;
    while s >= 0 {
        let f = resolve(s);
        if f >= 0 && visible(s) && cxs[s].flags & CF_FRIEND == 0 {
            if !add_candidate(mc, f, explicit, mark, nargs, oper) { unknown = true; }
        }
        s = cxs[s].nnext as i64;
    }
    return best_of_candidates(mc, mark, has_obj, unknown);
}

// The best of the candidates cand_syms[mc..] (popped), as best_candidate.
recursive fn best_of_candidates(mc: i64, mark: i64, has_obj: bool, unknown0: bool) -> i64 {
    let obj = cand_obj;
    let oper = cand_oper;
    cand_obj = 0;
    cand_oper = false;
    cand_explicit = -1;
    cand_deleted = false;
    cand_ambiguous = false;
    cand_unknown = false;
    let nargs = nscratch.len - mark;
    let best = pick_best(mc, mark, nargs, obj, has_obj, oper);
    cand_syms.resize(mc);
    if unknown0 { cand_unknown = true; }
    if cand_unknown { return -1; }
    return best;
}

// Adds function (or function template) f to the candidates from mc: false
// when its deduction could not be decided.
recursive fn add_candidate(mc: i64, f: i64, explicit: i32, mark: i64, nargs: i64, oper: bool) -> bool {
    let k = syms[f].kind as i64;
    if k == SK_FUNC && cxs[f].flags & CF_PATTERN == 0 {
        if explicit < 0 { add_cand(mc, f); }
        return true;
    }
    if k == SK_TEMPLATE && tmpl_kind(f) == TT_FUNC {
        let t = cxs[f].tmpl as i64;
        // an operator's member template deduces from the operands after the object
        let pf = tmpls[t].pattern as i64;
        let skip = if oper && pf >= 0 && cxs[pf].flags & CF_MEMBER != 0 { 1 } else { 0 };
        let sp = deduce_call(t, explicit, mark + skip, nargs - skip);
        if sp >= 0 { add_cand(mc, sp); }
        else if sp == -2 { return false; }
    }
    return true;
}

fn add_cand(cm0: i64, f: i64) {
    for i in cm0..cand_syms.len { if cand_syms[i] as i64 == f { return; } }
    cand_syms.push(f as! u32);
}

let IF_IGNORE = 32768;      // a slot that is neither better nor worse (a static member's object)

// The best viable candidate of cand_syms[cm0..]: per candidate, 1 + nargs
// conversion sequences (slot 0: the implicit object of a member call;
// slot 1 + j: operand j).
recursive fn pick_best(cm0: i64, mark: i64, nargs: i64, obj: u32, has_obj: bool, oper: bool) -> i64 {
    let im = cand_ics.len;
    let vm = cand_viable.len;
    var any_unknown = false;
    let ignore = Ics { kind: ICS_STD as! u8, rank: RK_EXACT as! u8, flags: (IF_IDENT | IF_IGNORE) as! u16, user: -1, from: 0, to: 0 };
    for c in cm0..cand_syms.len {
        let f = cand_syms[c] as i64;
        let ft = types[syms[f].ty >> 4];
        let np = ft.n;
        let member = cxs[f].flags & CF_MEMBER != 0 && cxs[f].flags & CF_CTOR == 0;
        let a0 = if oper && member { 1 } else { 0 };
        let na = nargs - a0;
        let variadic = ft.flags & TF_VARIADIC != 0;
        var ok = na == np || (variadic && na >= np);
        if !ok && na < np { ok = defaults_from(f, na); }
        if !ok { continue; }
        let st = cand_ics.len;
        var viable = true;
        var unk = false;
        // slot 0: the implicit object parameter
        if member && !oper && cxs[f].flags & CF_STATIC == 0 && (has_obj || obj != 0 || this_type != 0) {
            let c0 = ics_object(obj, f);
            if c0.kind as i64 == ICS_BAD { viable = false; }
            cand_ics.push(c0);
        } else {
            cand_ics.push(ignore);
        }
        // the operands
        if a0 == 1 {
            let c0 = if cxs[f].flags & CF_STATIC != 0 { ignore } else { ics_object(nscratch[mark], f) };
            if c0.kind as i64 == ICS_BAD { viable = false; }
            cand_ics.push(c0);
        }
        var i = 0;
        while i < na && viable {
            let e = nscratch[mark + a0 + i];
            var c1 = Ics { kind: ICS_ELLIPSIS as! u8, rank: RK_ELLIPSIS as! u8, flags: 0, user: -1, from: 0, to: 0 };
            if i < np { c1 = ics_of(e, tparams[ft.extra + i], CV_COPY); }
            else if nodes[e].kind as i64 == N_INITBRACE { c1 = ics_unknown(); }
            if c1.kind as i64 == ICS_BAD { viable = false; }
            if c1.kind as i64 == ICS_AMBIG { unk = true; }
            cand_ics.push(c1);
            i++;
        }
        if !viable { cand_ics.resize(st); continue; }
        for j in st..cand_ics.len { if cand_ics[j].flags & IF_UNKNOWN != 0 { unk = true; } }
        if unk { any_unknown = true; }
        cand_viable.push(c as! u32);
        cand_viable.push(st as! u32);
    }
    let nv = (cand_viable.len - vm) / 2;
    cand_nviable = nv;
    if inst_debug() {
        var o: u8[>..] = [];
        o.append(str("pick_best ncand=", cand_syms.len - cm0, " nviable=", nv, " unknown=", any_unknown, " :"));
        for v in nv {
            let f = cand_syms[cand_viable[vm + 2 * v]] as i64;
            o.append(str(" ", ident_text(syms[f].name as i64), "#", f, "["));
            let st = cand_viable[vm + 2 * v + 1] as i64;
            for k in nargs + 1 { let c = cand_ics[st + k]; o.append(str(c.kind, "/", c.rank, "/", c.flags, " ")); }
            o.append("]");
        }
        o.push('\n');
        write_stderr(o);
    }
    var best: i64 = -1;
    if nv == 1 && any_unknown {
        // the only candidate that may be viable
        best = cand_syms[cand_viable[vm]] as i64;
        if cxs[best].flags & CF_DELETED != 0 { cand_deleted = true; best = -1; }
        else { apply_user_convs(best, cand_viable[vm + 1] as i64, mark, nargs, oper); }
    } else if nv > 1 && any_unknown {
        cand_unknown = true;
    } else if nv > 0 {
        // a tournament, then the winner must beat every other one
        var w = 0;
        for i in 1..nv {
            if cand_better(vm, i, w, nargs) > 0 { w = i; }
        }
        var ok = true;
        for i in nv {
            if i == w { continue; }
            if cand_better(vm, w, i, nargs) <= 0 { ok = false; break; }
        }
        if !ok { cand_ambiguous = true; }
        else {
            best = cand_syms[cand_viable[vm + 2 * w]] as i64;
            if any_unknown { cand_unknown = true; best = -1; }
            else if cxs[best].flags & CF_DELETED != 0 { cand_deleted = true; best = -1; }
            else { apply_user_convs(best, cand_viable[vm + 2 * w + 1] as i64, mark, nargs, oper); }
        }
    }
    cand_viable.resize(vm);
    cand_ics.resize(im);
    return best;
}

// 1 if viable candidate i is better than j ([over.match.best]), -1 worse, 0 neither.
recursive fn cand_better(vm: i64, i: i64, j: i64, nargs: i64) -> i64 {
    let fi = cand_syms[cand_viable[vm + 2 * i]] as i64;
    let fj = cand_syms[cand_viable[vm + 2 * j]] as i64;
    let si = cand_viable[vm + 2 * i + 1] as i64;
    let sj = cand_viable[vm + 2 * j + 1] as i64;
    var better = false;
    var worse = false;
    for k in nargs + 1 {
        let a = cand_ics[si + k];
        let b = cand_ics[sj + k];
        if a.flags & IF_IGNORE != 0 || b.flags & IF_IGNORE != 0 { continue; }
        let c = ics_compare(a, b);
        if c > 0 { better = true; }
        if c < 0 { worse = true; }
    }
    if better && !worse { return 1; }
    if worse && !better { return -1; }
    if better && worse { return 0; }
    let ti = cxs[fi].flags2 & CF2_FSPEC != 0;
    let tj = cxs[fj].flags2 & CF2_FSPEC != 0;
    if !ti && tj { return 1; }
    if ti && !tj { return -1; }
    if ti && tj {
        let a = fn_at_least(cxs[fi].tmpl as i64, cxs[fj].tmpl as i64, nargs);
        let b = fn_at_least(cxs[fj].tmpl as i64, cxs[fi].tmpl as i64, nargs);
        if a && !b { return 1; }
        if b && !a { return -1; }
    }
    return 0;
}

// The chosen candidate's user-defined conversions applied to the arguments.
recursive fn apply_user_convs(f: i64, st: i64, mark: i64, nargs: i64, oper: bool) {
    let ft = types[syms[f].ty >> 4];
    let member = cxs[f].flags & CF_MEMBER != 0 && cxs[f].flags & CF_CTOR == 0;
    let a0 = if oper && member { 1 } else { 0 };
    for k in a0..nargs {
        let c = cand_ics[st + 1 + k];
        if c.kind as i64 != ICS_USER || c.user < 0 || c.flags & IF_LIST != 0 { continue; }
        let i = k - a0;
        if i >= ft.n { continue; }
        let e = nscratch[mark + k];
        let x = apply_user_conv(e, c.user as i64, tparams[ft.extra + i]);
        if x != 0 { nscratch[mark + k] = x; }
    }
}

// e converted by the user-defined conversion uf (a converting constructor
// or a conversion function) toward parameter type p: the converted
// expression (the constructor's class prvalue, the conversion function's
// result), or 0.
recursive fn apply_user_conv(e: u32, uf: i64, p: u32) -> u32 {
    let loc = nodes[e].loc;
    inst_use(uf);
    if cxs[uf].flags & CF_CTOR != 0 {
        let t = scope_class_type(cxs[uf].dscope as i64);
        if t == 0 { return 0; }
        let mark = nscratch.len;
        nscratch.push(e);
        let r = construct_class(t, mark, loc, false);
        nscratch.resize(mark);
        return r;
    }
    let rt = types[syms[uf].ty >> 4].base;
    resolved_fn = uf;
    if cg_on {
        resolved_fn = -1;
        var o = e;
        if !is_lvalue(o) { o = materialize(o, loc); }
        let mark = nscratch.len;
        return lower_call(uf, o, mark, loc, true);
    }
    return typed_result(rt, loc);
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
        let explicit = if nodes[callee].c != 0 { (nodes[callee].c - 1) as! i32 } else { -1 };
        let s0 = nodes[callee].a as i64;
        let nargs = nscratch.len - mark;
        let mc = cand_syms.len;
        var ok = true;
        var s = s0;
        while s >= 0 {
            let f = resolve(s);
            if f >= 0 && visible(s) && cxs[s].flags & CF_FRIEND == 0 {
                if !add_candidate(mc, f, explicit, mark, nargs, false) { ok = false; }
            }
            s = cxs[s].nnext as i64;
        }
        // argument-dependent lookup for an unqualified call of a namespace-scope function
        if obj == 0 && nodes[callee].op == 0 && adl_applies(s0) {
            if !adl_candidates(mc, syms[s0].name, mark, explicit, false) { ok = false; }
        }
        cand_obj = obj;
        let f = best_of_candidates(mc, mark, obj != 0, !ok);
        if f < 0 { return opaque_node(loc); }
        return build_call(f, obj, mark, loc, nodes[callee].op != 0);
    }
    if cg_on && ck == N_CXX && nodes[callee].op == 5 { return cg_memfn_call(callee, mark, loc); }
    if cg_on && ck == N_CXX && nodes[callee].op == 9 { return cg_dtor_call(callee, mark, loc); }
    if is_opq(callee) { return opaque_node(loc); }
    let t = nodes[callee].ty;
    if is_record(t) {
        // operator()
        let sc = type_scope(t);
        if sc < 0 { return opaque_node(loc); }
        let s = class_lookup(sc, op_ids[OP_CALL]);
        if s < 0 { return opaque_node(loc); }
        cand_obj = callee;
        let f = best_candidate(s, mark, true);
        if f < 0 { return opaque_node(loc); }
        return build_call(f, callee, mark, loc, false);
    }
    if (is_pointer(t) && is_func(tbase(t))) || is_func(t) {
        let ft = if is_func(t) { t } else { tbase(t) };
        if !cish_call(ft, mark) {
            // code generation: C++ parameter and result types (references,
            // classes by invisible reference)
            if cg_on { return cg_call_ptr(callee, ft, mark, loc); }
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
    let n = node(N_CXX, 0, nonref(ret), if resolved_fn >= 0 { resolved_fn } else { 0 }, 0, 0, loc);
    if resolved_fn >= 0 { nodes[n].op = 7; }      // a resolved call: a = the function
    resolved_fn = -1;
    if is_ref(ret) { nodes[n].flags = (NF_LVALUE | (if kind_of(ret) == TY_RREF { NF_XVALUE } else { 0 })) as! u16; }
    if is_opaque(ret) { nodes[n].flags = nodes[n].flags | NF_DEP; }
    return n;
}

// A call of the chosen function f (obj: the object for a member function,
// 0 none).
var resolved_fn: i64 = -1;     // typed_result: the function its call node is a call of
recursive fn build_call(f: i64, obj: u32, mark: i64, loc: u32, qualified: bool) -> u32 {
    inst_use(f);
    resolved_fn = f;
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
recursive fn funcref_addr(e: u32, loc: u32) -> u32 {
    var s = nodes[e].a as i64;
    var found: i64 = -1;
    var n = 0;
    while s >= 0 {
        let f = resolve(s);
        if f >= 0 && (syms[f].kind as i64 == SK_FUNC || syms[f].kind as i64 == SK_TEMPLATE) { found = f; n++; }
        s = cxs[s].nnext as i64;
    }
    if n == 1 && syms[found].kind as i64 == SK_TEMPLATE && nodes[e].c != 0 && tmpl_kind(found) == TT_FUNC && !dependent_ctx() {
        // f<args>: the specialization the explicit arguments name
        let sp = deduce_addr(cxs[found].tmpl as i64, (nodes[e].c - 1) as! i32, 0);
        if sp >= 0 { found = sp; }
    }
    if n != 1 || syms[found].kind as i64 != SK_FUNC || cxs[found].flags & CF_MEMBER != 0 { return dep_node(t_unknown, loc); }
    let r = node(N_DECLREF, 0, syms[found].ty, found, 0, 0, loc);
    syms[found].flags = syms[found].flags | SF_USED;
    inst_use(found);
    return node(N_UNARY, U_ADDR, mk_ptr(syms[found].ty), r as i64, 0, 0, loc);
}

// ---------------------------------------------------------------------------
// Operators on classes (D1: opaque unless a non-template candidate is
// found and selected; see build_call).

recursive fn overloaded_binop(op: i64, l: u32, r: u32, loc: u32) -> u32 {
    let x = resolve_oper(op, l, r, false, loc);
    if x != 0 { return x; }
    if cg_on { return cg_operator(op, l, r, loc, false); }
    return 0;
}
recursive fn overloaded_assign(op: i64, l: u32, r: u32, loc: u32, tok: i64) -> u32 {
    let x = resolve_oper(tok_op(tok), l, r, false, loc);
    if x != 0 { return x; }
    if cg_on { return cg_assign(op, l, r, loc, tok); }
    return 0;
}
recursive fn overloaded_unop(op: i64, e: u32, loc: u32, post: bool) -> u32 {
    let x = resolve_oper(op, e, 0, post, loc);
    if x != 0 { return x; }
    if cg_on { return cg_operator(op, e, 0, loc, post); }
    return 0;
}
recursive fn overloaded_subscript(b: u32, i: u32, loc: u32) -> u32 {
    let x = resolve_oper(OP_SUBSCRIPT, b, i, false, loc);
    if x != 0 { return x; }
    if cg_on { return cg_operator(OP_SUBSCRIPT, b, i, loc, false); }
    return 0;
}
recursive fn overloaded_arrow(b: u32, loc: u32) -> u32 {
    let x = resolve_oper(OP_ARROW, b, 0, false, loc);
    if x != 0 { return x; }
    if cg_on { return cg_operator(OP_ARROW, b, 0, loc, false); }
    return 0;
}

// Does argument-dependent lookup apply to an unqualified call whose name
// ordinary lookup found as the chain s0 (C++ [basic.lookup.argdep]p3: not
// for a class member, a block-scope function declaration, or a name that
// is not a function)?
fn adl_applies(s0: i64) -> bool {
    var s = s0;
    while s >= 0 {
        let f = resolve(s);
        if f >= 0 && visible(s) {
            let k = syms[f].kind as i64;
            if k != SK_FUNC && k != SK_TEMPLATE { return false; }
            if cxs[f].flags & CF_MEMBER != 0 { return false; }
            if k == SK_TEMPLATE && tmpls[cxs[f].tmpl].pattern >= 0 && cxs[tmpls[cxs[f].tmpl].pattern].flags & CF_MEMBER != 0 { return false; }
            if syms[s].scope > 0 && cxs[s].dscope < 0 { return false; }
        }
        s = cxs[s].nnext as i64;
    }
    return true;
}
recursive fn conv_to_bool(e: u32) -> u32 {
    if !is_opq(e) {
        // a contextual conversion: explicit conversion functions count
        let c = ics_user(e, t_bool, CV_COPY | CV_BOOL_CTX, false, false);
        if c.kind as i64 == ICS_USER && c.user >= 0 {
            let x = apply_user_conv(e, c.user as i64, t_bool);
            if x != 0 && !is_opq(x) { return to_bool(x); }
        }
    }
    return dep_node(t_bool, nodes[e].loc);
}

// A class operand of a built-in operator converted by its conversion
// function (C++ [over.built]: the one non-explicit conversion function to
// an arithmetic, enumeration or pointer type; `want` preferred), or 0.
recursive fn builtin_conv_operand(e: u32, want: u32) -> u32 {
    if is_opq(e) || !is_record(nodes[e].ty) { return 0; }
    need_complete(nodes[e].ty);
    if want != 0 {
        let c = ics_user(e, want, CV_COPY | (if want == t_bool { CV_BOOL_CTX } else { 0 }), false, false);
        if c.kind as i64 == ICS_USER && c.user >= 0 { return apply_user_conv(e, c.user as i64, want); }
    }
    let mark = conv_fns.len;
    collect_conv_fns(unqual(nodes[e].ty), 0);
    var found: i64 = -1;
    var n = 0;
    for i in mark..conv_fns.len {
        let f = conv_fns[i] as i64;
        if syms[f].kind as i64 != SK_FUNC || cxs[f].flags & CF_EXPLICIT != 0 { continue; }
        let rt = nonref(types[syms[f].ty >> 4].base);
        let k = kind_of(rt);
        if is_arith(rt) || k == TY_BOOL || k == TY_ENUM || k == TY_POINTER || k == TY_NULLPTR { found = f; n++; }
    }
    conv_fns.resize(mark);
    if n != 1 { return 0; }
    let ob = ics_object(e, found);
    if ob.kind as i64 == ICS_BAD { return 0; }
    return apply_user_conv(e, found, types[syms[found].ty >> 4].base);
}
recursive fn cast_to_class(t: u32, e: u32, loc: u32) -> u32 { return 0; }

// T(args) / T{args} of class type: a prvalue of T.
recursive fn construct_class(t: u32, mark: i64, loc: u32, braces: bool) -> u32 {
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    // code generation: T{args} of an aggregate is aggregate initialization (op 2)
    let op = if cg_on && braces && is_complete(t) && is_aggregate_class(rec_of(t)) { 2 } else { 0 };
    return node_v(N_CTOR, op, unqual(t), 0, 0, count, loc, start);
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
    if nodes[init].kind as i64 == N_INITBRACE || is_record(t) || is_ref(t) || !cish(t) || !cish_node(init) || kind_of(t) == TY_MEMPTR { return init; }
    if kind_of(nodes[init].ty) == TY_NULLPTR {
        if is_pointer(t) { return icast(init, CK_NULL2PTR, unqual(t)); }
        return init;
    }
    return assign_convert(rv(init), t, loc, 1);
}

fn default_init(s: i64, loc: u32) -> u32 { return 0; }

// An unqualified call whose name ordinary lookup does not find: the
// functions argument-dependent lookup finds (C++ [basic.lookup.argdep]).
// 0 when it finds none; an opaque node when the choice is not known.
recursive fn adl_only_call(name: u32, mark: i64, explicit: i32, loc: u32) -> u32 {
    let mc = cand_syms.len;
    let n0 = adl_seen;
    let ok = adl_candidates(mc, name, mark, explicit, false);
    if adl_seen == n0 && ok { cand_syms.resize(mc); return 0; }
    cand_obj = 0;
    let f = best_of_candidates(mc, mark, false, !ok);
    if f < 0 { return opaque_node(loc); }
    return build_call(f, 0, mark, loc, false);
}

// The function of overload set e whose type matches the target type t (a
// pointer or reference to function, or a function type) [over.over]:
// non-template functions are preferred, then the most specialized
// template's specialization. -1 none (or ambiguous), -2 not known.
recursive fn overload_for_target(e: u32, t: u32) -> i64 {
    var ft = nonref(t);
    if is_pointer(ft) { ft = tbase(ft); }
    if is_opaque(ft) || !is_func(ft) { return -2; }
    ft = unqual(ft);
    if nodes[e].b != 0 { return -2; }
    let explicit = if nodes[e].c != 0 { (nodes[e].c - 1) as! i32 } else { -1 };
    var nt: i64 = -1;
    var nnt = 0;
    var unknown = false;
    let mc = cand_syms.len;
    var s = nodes[e].a as i64;
    while s >= 0 {
        let f = resolve(s);
        let vis = visible(s);
        s = cxs[s].nnext as i64;
        if f < 0 || !vis { continue; }
        let k = syms[f].kind as i64;
        if k == SK_FUNC && cxs[f].flags & CF_PATTERN == 0 {
            if cxs[f].flags & CF_MEMBER != 0 && cxs[f].flags & CF_STATIC == 0 { unknown = true; continue; }
            if explicit < 0 && unqual(syms[f].ty) == ft && f != nt { nt = f; nnt++; }
        } else if k == SK_TEMPLATE && tmpl_kind(f) == TT_FUNC {
            let sp = deduce_addr(cxs[f].tmpl as i64, explicit, ft);
            if sp >= 0 { add_cand(mc, sp); }
            else if sp == -2 { unknown = true; }
        }
    }
    if nnt == 1 { cand_syms.resize(mc); return nt; }
    if nnt > 1 { cand_syms.resize(mc); return -1; }
    let n = cand_syms.len - mc;
    if n == 0 { return if unknown { -2 } else { -1 }; }
    var best = cand_syms[mc] as i64;
    if n > 1 {
        // the most specialized template
        for i in mc + 1..cand_syms.len {
            let c = cand_syms[i] as i64;
            let a = fn_at_least(cxs[c].tmpl as i64, cxs[best].tmpl as i64, tmpl_np(c));
            let b = fn_at_least(cxs[best].tmpl as i64, cxs[c].tmpl as i64, tmpl_np(c));
            if a && !b { best = c; }
        }
        for i in mc..cand_syms.len {
            let c = cand_syms[i] as i64;
            if c == best { continue; }
            let a = fn_at_least(cxs[best].tmpl as i64, cxs[c].tmpl as i64, tmpl_np(c));
            let b = fn_at_least(cxs[c].tmpl as i64, cxs[best].tmpl as i64, tmpl_np(c));
            if !a || b { best = -1; break; }
        }
    }
    cand_syms.resize(mc);
    if best < 0 { return if unknown { -2 } else { -1 }; }
    if unknown { return -2; }
    return best;
}

// &f for the function of overload set e that target type t selects (the
// function itself for a reference or function target); the single
// function's address when the set has one.
recursive fn funcref_addr_to(e: u32, t: u32, loc: u32) -> u32 {
    let f = overload_for_target(e, t);
    if f < 0 { return funcref_addr(e, loc); }
    let r = node(N_DECLREF, 0, syms[f].ty, f, 0, 0, loc);
    nodes[r].flags = NF_LVALUE;
    syms[f].flags = syms[f].flags | SF_USED;
    inst_use(f);
    if is_ref(t) || is_func(t) { return r; }
    return node(N_UNARY, U_ADDR, mk_ptr(syms[f].ty), r as i64, 0, 0, loc);
}

// The number of function parameters of specialization f's template.
fn tmpl_np(f: i64) -> i64 {
    let t = cxs[f].tmpl as i64;
    if t < 0 || tmpls[t].pattern < 0 { return 0; }
    return types[syms[tmpls[t].pattern].ty >> 4].n as i64;
}
