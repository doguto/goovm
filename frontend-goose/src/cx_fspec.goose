// goosecc D2: function templates. Argument deduction from a call (C++
// [temp.deduct.call]), the specialization's declaration (the template's
// declaration parsed again with the deduced arguments bound: a
// substitution failure there removes the candidate, SFINAE), its body on
// use (the definition parsed again for that symbol), and partial ordering
// ([temp.func.order]) for overload resolution.

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
import .cx_core;
import .cx_names;
import .cx_decl;
import .cx_class;
import .cx_tmpl;
import .cx_inst;

var inst_spec_tmpl: i64 = -1;   // declare_function: make the specialization of this template
var inst_spec_binds: i32 = -1;
var inst_spec_result: i64 = -1;
var inst_spec_decl: bool = false;   // function_body: skip the body (a specialization's declaration)
var inst_body_now: bool = false;    // function_body: parse the body now (an instantiated definition)
var fspec_map = dictionary<u64, i32> {};    // (template << 32 | bindings) -> specialization + 1, or -1 failure, -2 uncertain

// ---------------------------------------------------------------------------
// The specialization's declaration.

// The specialization of function template t for `binds` (one argument per
// parameter): its symbol, -1 on a substitution failure, -2 when the result
// is not known.
recursive fn fspec_decl(t: i64, binds: i32) -> i64 {
    let key = ((t as u64) << 32) | (binds as u64);
    let g = fspec_map.get(key);
    if g { return if g > 0 { (g - 1) as i64 } else { g as i64 }; }
    if inst_depth > 400 || tmpls[t].t1 == 0 { return -2; }
    fspec_map.insert(key, -2);
    let sc = tmpls[t].scope as i64;
    let mark = nscratch.len;
    inst_what = tmpls[t].sym as i64;
    let st = inst_enter();
    let e0 = diag_inst_errors;
    bind_header(t, binds);
    if sc >= 0 && scopes[sc].kind as i64 == CS_CLASS {
        cur_scope = sc;
        cur_class = sc;
        cur_access = AC_PUBLIC;
    } else {
        cur_scope = if sc >= 0 { sc } else { 0 };
    }
    pc = tmpls[t].t0 as i64;
    inst_spec_tmpl = t;
    inst_spec_binds = binds;
    inst_spec_result = -1;
    inst_spec_decl = true;
    let ctx = if cur_class >= 0 { if decl_is_friend_ahead() { DC_FRIEND } else { DC_CLASS } } else { DC_NS };
    parse_simple_decl(ctx);
    inst_spec_decl = false;
    inst_spec_tmpl = -1;
    let s = inst_spec_result;
    inst_spec_result = -1;
    let errs = diag_inst_errors - e0;
    let bad = inst_leave(st);
    nscratch.resize(mark);
    var res: i64 = -2;
    if s >= 0 && !bad && errs == 0 {
        res = s;
        if fn_type_opaque(syms[s].ty) { res = -2; }
    } else if s >= 0 && (bad || errs > 0) {
        res = if sfinae_certain(s) { -1 } else { -2 };
    } else if s < 0 && (bad || errs > 0) {
        res = -1;
    }
    fspec_map.insert(key, if res >= 0 { (res + 1) as! i32 } else { res as! i32 });
    if inst_debug() {
        var o: u8[>..] = [];
        o.append(str("fspec_decl ", ident_text(syms[tmpls[t].sym].name as i64), " t=", t, " -> ", res, " errs=", errs, " <"));
        for i in tl_count(binds as i64) {
            let a = tl_arg(binds as i64, i);
            if a.kind as i64 == TA_TYPE { o.append(tname(a.ty)); } else { o.append(str("#", a.v)); }
            o.append(", ");
        }
        o.append(">\n");
        write_stderr(o);
    }
    return res;
}

fn decl_is_friend_ahead() -> bool {
    let sv = save();
    var a = Attrs { .. };
    cx_attrs(a);
    let f = at_kw(KW_FRIEND);
    restore(sv);
    return f;
}

// Does the function type involve a type not computed?
recursive fn fn_type_opaque(ft: u32) -> bool {
    if kind_of(ft) != TY_FUNC { return is_opaque(ft); }
    let f = types[ft >> 4];
    if is_opaque(f.base) && kind_of(f.base) != TY_AUTO { return true; }
    for i in f.n { if is_opaque(tparams[f.extra + i]) { return true; } }
    return false;
}

// A substitution produced errors: is that a certain failure (the
// candidate goes) rather than something D2 does not compute? (Until the
// semantic analysis is complete, only a declaration whose types are all
// known is trusted.)
fn sfinae_certain(s: i64) -> bool { true }

// Called by declare_function in specialization mode.
fn make_fspec(d: CD&, ds: CDS&, key: u32, ft: u32, ctor: bool, is_member: bool, loc: u32) -> i64 {
    let t = inst_spec_tmpl;
    inst_spec_tmpl = -1;
    pending_tmpl = -1;
    let s = csym(SK_FUNC, key, ft, loc);
    let fs = tmpls[t].scope as i64;
    cxs[s].dscope = fs as! i32;
    set_fn_flags(s, d, ds, ctor, is_member);
    cxs[s].flags = cxs[s].flags | CF_SPEC;
    cxs[s].tmpl = t as! i32;
    cxs[s].targs = inst_spec_binds;
    cxs[s].flags2 = CF2_FSPEC | CF2_LAZY_BODY;
    syms[s].flags = syms[s].flags | SF_INLINE;
    let pf = tmpls[t].pattern as i64;
    if pf >= 0 { cxs[s].access = cxs[pf].access; }
    note_params(s, d);
    inst_spec_result = s;
    return s;
}

// ---------------------------------------------------------------------------
// The body.

// The template whose definition holds t's body, and the header binding the
// enclosing class template's parameters (-1 none) with their arguments.
recursive fn fspec_def_source(t: i64) -> i64, i32 {
    if tmpls[t].def_t >= 0 { return tmpls[t].def_t as i64, -1; }
    // a member template of an instantiated class: the pattern's member template
    let sc = tmpls[t].scope as i64;
    if sc >= 0 && scopes[sc].kind as i64 == CS_CLASS && scopes[sc].flags & SCF_INST != 0 {
        let tp = pattern_tmpl(t);
        if tp >= 0 && tmpls[tp].def_t >= 0 {
            let pat, pargs = inst_args_of(sc);
            return tmpls[tp].def_t as i64, pargs;
        }
    }
    return t, -1;
}

// The member template of the pattern that member template t of an
// instantiated class was made from, -1.
recursive fn pattern_tmpl(t: i64) -> i64 {
    if tmpls[t].pat_t != -1 { return if tmpls[t].pat_t >= 0 { tmpls[t].pat_t as i64 } else { -1 }; }
    tmpls[t].pat_t = -2;
    let ps = pattern_scope(tmpls[t].scope as i64);
    if ps < 0 || tmpls[t].sym < 0 { return -1; }
    var x = scope_find(ps, syms[tmpls[t].sym].name);
    while x >= 0 {
        if syms[x].kind as i64 == SK_TEMPLATE && cxs[x].tmpl >= 0 && tmpls[cxs[x].tmpl].pos == tmpls[t].pos {
            tmpls[t].pat_t = cxs[x].tmpl;
            return cxs[x].tmpl as i64;
        }
        x = cxs[x].nnext as i64;
    }
    return -1;
}

recursive fn inst_fspec_body(f: i64) {
    let t = cxs[f].tmpl as i64;
    let binds = cxs[f].targs;
    let dt, outer = fspec_def_source(t);
    if tmpls[dt].t1 == 0 { return; }
    let mark = nscratch.len;
    inst_what = f;
    let st = inst_enter();
    if outer >= 0 && tmpls[dt].hdr_outer >= 0 { bind_header(tmpls[dt].hdr_outer as i64, outer); }
    bind_header(dt, binds);
    let sc = tmpls[dt].scope as i64;
    var ctx = DC_NS;
    if sc >= 0 && scopes[sc].kind as i64 == CS_CLASS {
        cur_scope = sc;
        cur_class = sc;
        cur_access = AC_PUBLIC;
        ctx = if decl_is_friend_ahead_at(tmpls[dt].t0 as i64) { DC_FRIEND } else { DC_CLASS };
    } else {
        cur_scope = if sc >= 0 { sc } else { 0 };
    }
    pc = tmpls[dt].t0 as i64;
    inst_def_target = f;
    inst_body_now = true;
    parse_simple_decl(ctx);
    inst_def_target = -1;
    inst_body_now = false;
    let bad = inst_leave(st);
    if bad { cxs[f].flags2 = cxs[f].flags2 | CF2_DIRTY; }
    take_defs(mark);
}

fn decl_is_friend_ahead_at(p: i64) -> bool {
    let sv = save();
    pc = p;
    gt_pos = -1;
    let f = decl_is_friend_ahead();
    restore(sv);
    return f;
}

// ---------------------------------------------------------------------------
// Deduction from a call.

// Deduces template t's arguments from the call arguments nscratch[mark..]
// (explicit: the explicit template arguments, -1 none) and makes the
// specialization: its symbol, -1 when t is not a candidate, -2 unknown.
recursive fn deduce_call(t: i64, explicit: i32, mark: i64, nargs: i64) -> i64 {
    let pf = tmpls[t].pattern as i64;
    if pf < 0 || kind_of(syms[pf].ty) != TY_FUNC { return -2; }
    let ft = types[syms[pf].ty >> 4];
    let sv = ded_begin(t);
    var res: i64 = -1;
    var unknown = false;
    // explicit arguments
    let ne = tl_count(explicit as i64);
    var ok = true;
    var i = 0;
    while i < ne && ok {
        if i >= ded_n { ok = false; break; }
        let p = tps[tmpls[t].params as i64 + i];
        let a = tl_arg(explicit as i64, i);
        if a.kind as i64 == TA_TYPE && (a.ty == 0 || is_opaque(a.ty)) { unknown = true; }
        if p.pack {
            // the rest of the explicit arguments start the pack
            let m2 = targ_scratch.len;
            var j = i;
            while j < ne { targ_scratch.push(tl_arg(explicit as i64, j)); j++; }
            let pl = targ_intern(m2);
            ded_args[ded_base + i] = TArg { kind: TA_PACK as! u8, rsv: 0, rsv2: 0, ty: 0, v: pl as i64 };
            break;
        }
        if (p.kind as i64 == TPK_TYPE && a.kind as i64 != TA_TYPE) || (p.kind as i64 == TPK_VALUE && a.kind as i64 != TA_VALUE) ||
           (p.kind as i64 == TPK_TEMPLATE && a.kind as i64 != TA_TEMPLATE) { ok = false; break; }
        var a2 = a;
        a2.rsv = 1;
        ded_args[ded_base + i] = a2;
        i++;
    }
    // the function parameters against the arguments
    let np = ft.n;
    var k = 0;
    while ok && k < nargs {
        let e = nscratch[mark + k];
        if k >= np {
            if ft.flags & TF_VARIADIC != 0 { k++; continue; }
            ok = false;
            break;
        }
        let p = tparams[ft.extra + k];
        if kind_of(p) == TY_PACKEXP {
            // a function parameter pack: every remaining argument against its pattern
            if k != np - 1 { unknown = true; break; }
            let r = deduce_pack_args(tbase(p), mark, k, nargs);
            if r == 0 { ok = false; } else if r < 0 { unknown = true; }
            k = nargs;
            break;
        }
        let r = deduce_one(p, e);
        if r == 0 { ok = false; break; }
        if r < 0 { unknown = true; }
        k++;
    }
    if ok && nargs < np {
        // the remaining parameters need default arguments (or are an empty pack)
        if kind_of(tparams[ft.extra + np - 1]) == TY_PACKEXP && nargs == np - 1 {
            let idx = ded_param(tbase(tparams[ft.extra + np - 1]));
            if idx >= 0 && ded_args[ded_base + idx].kind == 0 {
                let m2 = targ_scratch.len;
                let pl = targ_intern(m2);
                ded_args[ded_base + idx] = TArg { kind: TA_PACK as! u8, rsv: 0, rsv2: 0, ty: 0, v: pl as i64 };
            }
        } else if !defaults_from(pf, nargs) { ok = false; }
    }
    if ok && !unknown {
        // default template arguments for what was not deduced
        let full, binds = ded_complete(t);
        if !full { ok = false; }
        else {
            ded_end(sv);
            return fspec_decl(t, binds);
        }
    }
    ded_end(sv);
    if !ok { return -1; }
    return -2;
}

// Deduction from a function parameter pack P... against the arguments from k.
recursive fn deduce_pack_args(pat: u32, mark: i64, k0: i64, nargs: i64) -> i64 {
    let pq = nonref(pat);
    let idx = ded_param(if is_ref(pat) { tbase(pat) } else { pat });
    if idx < 0 {
        // a pattern X<T>...: each argument against it
        var k = k0;
        while k < nargs {
            let r = deduce_one(pat, nscratch[mark + k]);
            if r <= 0 { return r; }
            k++;
        }
        return 1;
    }
    // T... / T&... / T&&... : the pack binds the deduced types
    let m2 = targ_scratch.len;
    var k = k0;
    var unknown = false;
    while k < nargs {
        let saved = ded_args[ded_base + idx];
        ded_args[ded_base + idx] = TArg { kind: 0, rsv: 0, rsv2: 0, ty: 0, v: 0 };
        let r = deduce_one(pat, nscratch[mark + k]);
        let got = ded_args[ded_base + idx];
        ded_args[ded_base + idx] = saved;
        if r == 0 { targ_scratch.resize(m2); return 0; }
        if r < 0 || got.kind == 0 { unknown = true; targ_scratch.push(TArg { kind: TA_TYPE as! u8, rsv: 0, rsv2: 0, ty: t_unknown, v: 0 }); }
        else { targ_scratch.push(got); }
        k++;
    }
    let pl = targ_intern(m2);
    let cur = ded_args[ded_base + idx];
    if cur.kind as i64 == TA_PACK {
        // explicitly given elements first: they must agree
        let ex = cur.v;
        let n1 = tl_count(ex);
        let n2 = tl_count(pl as i64);
        for j in n1 {
            if j >= n2 { break; }
            let a = tl_arg(ex, j);
            let b = tl_arg(pl as i64, j);
            if a.ty != b.ty { unknown = true; }
        }
        if n1 > n2 { return 0; }
    }
    ded_args[ded_base + idx] = TArg { kind: TA_PACK as! u8, rsv: 0, rsv2: 0, ty: 0, v: pl as i64 };
    if unknown { return -1; }
    return 1;
}

// Deduction from one argument e against parameter type p: 1 ok, 0 fails, -1 unknown.
recursive fn deduce_one(p0: u32, e: u32) -> i64 {
    if !is_dep(p0) { return 1; }                  // a non-dependent parameter: checked as a conversion later
    if is_opq(e) && nodes[e].kind as i64 != N_FUNCREF && nodes[e].kind as i64 != N_INITBRACE { return -1; }
    let ek = nodes[e].kind as i64;
    if ek == N_INITBRACE { return -1; }           // std::initializer_list<T> deduction: not yet
    if ek == N_FUNCREF { return -1; }             // an overload set: not yet
    var p = p0;
    var a = nodes[e].ty;
    let lv = is_lvalue(e) && nodes[e].flags & NF_XVALUE == 0;
    if is_ref(p) {
        let rt = tbase(p);
        // a forwarding reference: T&& with T a parameter of this template
        if kind_of(p) == TY_RREF && quals(rt) == 0 && ded_param(rt) >= 0 && lv {
            a = mk_lref(a);
            p = rt;
        } else {
            p = rt;
            // the referred type may be more cv-qualified than the argument
            a = with_q(a, quals(p) & ~quals(a));
        }
    } else {
        // decay, and top-level cv dropped
        if is_array(a) { a = mk_ptr(tbase(a)); }
        else if is_func(a) { a = mk_ptr(a); }
        else { a = unqual(a); }
        p = unqual(p);
    }
    if is_opaque(a) { return -1; }
    if deduce_try(p, a) { return 1; }
    // (D3) every template parameter of P explicitly specified: no
    // deduction, the argument is converted ([temp.arg.explicit]p6)
    if all_explicit(p0, 0) { return 1; }
    // a pointer: a qualification conversion of the argument
    if is_pointer(p) && is_pointer(a) {
        let pa = tbase(a);
        let pp = tbase(p);
        if deduce_try(p, mk_ptr(with_q(pa, quals(pp) & ~quals(pa)))) { return 1; }
    }
    // a class template-id: a base class of the argument's class
    var cls = a;
    var pc0 = p;
    if is_pointer(p) && is_pointer(a) { cls = tbase(a); pc0 = tbase(p); }
    if kind_of(unqual(pc0)) == TY_DEPSPEC && is_record(cls) {
        need_complete(cls);
        if deduce_from_bases(pc0, cls, 0) { return 1; }
    }
    return 0;
}

// Are all template parameters (of the template being deduced) in type t
// explicitly specified arguments?
recursive fn all_explicit(t: u32, depth: i64) -> bool {
    if depth > 16 { return false; }
    let k = kind_of(t);
    if k == TY_TPARAM {
        let idx = ded_param(t);
        if idx < 0 { return true; }
        let a = ded_args[ded_base + idx];
        return a.kind != 0 && a.rsv == 1;
    }
    if k == TY_POINTER || k == TY_LREF || k == TY_RREF || k == TY_ARRAY { return all_explicit(tbase(t), depth + 1); }
    if k == TY_MEMPTR { return all_explicit(types[t >> 4].extra, depth + 1) && all_explicit(tbase(t), depth + 1); }
    if k == TY_FUNC {
        let f = types[t >> 4];
        if !all_explicit(f.base, depth + 1) { return false; }
        for i in f.n { if !all_explicit(tparams[f.extra + i], depth + 1) { return false; } }
        return true;
    }
    if k == TY_DEPSPEC || k == TY_DEPNAME || k == TY_DEPEXPR || k == TY_PACKEXP { return false; }
    return true;
}

// Deduction that leaves the bindings unchanged when it fails.
recursive fn deduce_try(p: u32, a: u32) -> bool {
    let m = ded_args.len;
    for i in ded_n { ded_args.push(ded_args[ded_base + i]); }
    let ok = deduce_type(p, a);
    if !ok { for i in ded_n { ded_args[ded_base + i] = ded_args[m + i]; } }
    ded_args.resize(m);
    return ok;
}

recursive fn deduce_from_bases(p: u32, cls: u32, depth: i64) -> bool {
    if depth > 16 { return false; }
    let r = rec_of(cls);
    if r >= crecs.len { return false; }
    let cr = crecs[r];
    for i in cr.nbases {
        let bt = cbases[cr.bases + i].ty;
        if !is_record(bt) { continue; }
        if deduce_try(p, with_q(bt, quals(p))) { return true; }
        if deduce_from_bases(p, bt, depth + 1) { return true; }
    }
    return false;
}

// The deduced arguments completed with default template arguments.
recursive fn ded_complete(t: i64) -> bool, i32 {
    var i = 0;
    while i < ded_n {
        if ded_args[ded_base + i].kind == 0 {
            let p = tps[tmpls[t].params as i64 + i];
            if p.pack {
                let m2 = targ_scratch.len;
                let pl = targ_intern(m2);
                ded_args[ded_base + i] = TArg { kind: TA_PACK as! u8, rsv: 0, rsv2: 0, ty: 0, v: pl as i64 };
            } else if p.def0 != 0 {
                // the bindings so far (a default argument may use them)
                let mark = targ_scratch.len;
                for j in i { targ_scratch.push(ded_args[ded_base + j]); }
                let prev = targ_intern(mark);
                if p.kind as i64 == TPK_TYPE {
                    let ty = subst_parse(t, prev, p.def0 as i64, 0, i);
                    if ty == 0 || is_opaque(ty) { return false, -1; }
                    ded_args[ded_base + i] = TArg { kind: TA_TYPE as! u8, rsv: 0, rsv2: 0, ty: ty, v: 0 };
                } else if p.kind as i64 == TPK_VALUE {
                    let ty = subst_parse(t, prev, p.def0 as i64, 1, i);
                    if !subst_ok { return false, -1; }
                    ded_args[ded_base + i] = TArg { kind: TA_VALUE as! u8, rsv: 0, rsv2: 0, ty: unqual(nonref(ty)), v: subst_val };
                } else {
                    return false, -1;
                }
            } else {
                return false, -1;
            }
        }
        i++;
    }
    // explicit markers off
    for j in ded_n { ded_args[ded_base + j].rsv = 0; }
    return ded_list(t);
}

// ---------------------------------------------------------------------------
// Partial ordering of function templates (C++ [temp.func.order]), for a
// call with nargs arguments: is template a at least as specialized as b?

recursive fn fn_at_least(a: i64, b: i64, nargs: i64) -> bool {
    let pa = tmpls[a].pattern as i64;
    let pb = tmpls[b].pattern as i64;
    if pa < 0 || pb < 0 { return false; }
    let fa = types[syms[pa].ty >> 4];
    let fb = types[syms[pb].ty >> 4];
    let sv = ded_begin(b);
    var ok = true;
    var i = 0;
    while i < nargs && ok {
        if i >= fb.n { break; }
        var pt = tparams[fb.extra + i];
        if i >= fa.n {
            ok = kind_of(pt) == TY_PACKEXP;
            break;
        }
        var at = retag(tparams[fa.extra + i], tmpls[a].depth as i64, 250);
        if kind_of(pt) == TY_PACKEXP {
            if kind_of(at) != TY_PACKEXP { at = at; }
            pt = tbase(pt);
            if kind_of(at) == TY_PACKEXP { at = tbase(at); }
        } else if kind_of(at) == TY_PACKEXP { ok = false; break; }
        pt = unqual(nonref(pt));
        at = unqual(nonref(at));
        if !deduce_type(pt, at) { ok = false; }
        i++;
    }
    ded_end(sv);
    return ok;
}
