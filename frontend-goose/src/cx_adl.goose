// goosecc D2: argument-dependent lookup (C++ [basic.lookup.argdep]) and
// overloaded operators ([over.match.oper]).
//
// The associated namespaces and classes of the argument types are
// collected (classes, their bases and enclosing classes, the template
// arguments of specializations, enums, pointees, function types); the
// functions named in those namespaces join the candidates, including the
// friends declared in the associated classes, whatever the two-phase
// visibility of the call's position (lookup at the point of instantiation).

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
import .cx_conv;

var adl_ns: i32[>..<] = [];     // associated namespaces (scopes)
var adl_cls: i32[>..<] = [];    // associated classes (scopes)
var friend_class = dictionary<u64, u32> {};    // a function first declared as a friend -> the befriending class scope

recursive fn adl_add_ns(sc: i64, nm: i64) {
    if sc < 0 { return; }
    for i in nm..adl_ns.len { if adl_ns[i] as i64 == sc { return; } }
    adl_ns.push(sc as! i32);
    // an inline namespace's enclosing namespace; the inline namespaces it contains
    if scopes[sc].flags & SCF_INLINE != 0 && scopes[sc].parent >= 0 { adl_add_ns(scopes[sc].parent as i64, nm); }
    var l = scopes[sc].inl;
    while l >= 0 {
        adl_add_ns(ulinks[l].v as i64, nm);
        l = ulinks[l].next;
    }
}

// The associated classes and namespaces of type t (C++ [basic.lookup.argdep]p3).
recursive fn adl_type(t0: u32, nm: i64, cm: i64, depth: i64) {
    if t0 == 0 || depth > 16 { return; }
    var t = nonref(t0);
    let k = kind_of(t);
    if k == TY_POINTER || k == TY_ARRAY || k == TY_COMPLEX || k == TY_VECTOR { adl_type(tbase(t), nm, cm, depth + 1); return; }
    if k == TY_FUNC {
        let f = types[t >> 4];
        adl_type(f.base, nm, cm, depth + 1);
        for i in f.n { adl_type(tparams[f.extra + i], nm, cm, depth + 1); }
        return;
    }
    if k == TY_MEMPTR {
        adl_type(types[t >> 4].extra, nm, cm, depth + 1);
        adl_type(tbase(t), nm, cm, depth + 1);
        return;
    }
    if k == TY_ENUM {
        let es = enum_scope(types[t >> 4].extra as i64);
        if es >= 0 {
            let p = scopes[es].parent as i64;
            if p >= 0 && scopes[p].kind as i64 == CS_CLASS { adl_add_cls(p, nm, cm, depth); }
            adl_add_ns(enclosing_ns(es), nm);
        }
        return;
    }
    if k == TY_STRUCT || k == TY_UNION {
        need_complete(t);
        let sc = type_scope(t);
        if sc < 0 { return; }
        adl_add_cls(sc, nm, cm, depth);
        // a specialization: its template arguments
        let r = rec_of(t);
        let cs = crecs[r].sym as i64;
        if cs >= 0 && cxs[cs].flags & CF_SPEC != 0 && cxs[cs].targs >= 0 {
            let l = cxs[cs].targs as i64;
            for i in tl_count(l) {
                let a = tl_arg(l, i);
                if a.kind as i64 == TA_TYPE { adl_type(a.ty, nm, cm, depth + 1); }
                else if a.kind as i64 == TA_TEMPLATE && a.v >= 0 {
                    let ts = resolve(a.v);
                    if ts >= 0 && cxs[ts].dscope >= 0 {
                        let ds = cxs[ts].dscope as i64;
                        if scopes[ds].kind as i64 == CS_CLASS { adl_add_cls(ds, nm, cm, depth); }
                        adl_add_ns(enclosing_ns(ds), nm);
                    }
                }
            }
        }
    }
}

// Class scope sc, its enclosing class and namespace, and its bases.
recursive fn adl_add_cls(sc: i64, nm: i64, cm: i64, depth: i64) {
    for i in cm..adl_cls.len { if adl_cls[i] as i64 == sc { return; } }
    adl_cls.push(sc as! i32);
    let p = scopes[sc].parent as i64;
    if p >= 0 && scopes[p].kind as i64 == CS_CLASS { adl_add_cls(p, nm, cm, depth + 1); }
    adl_add_ns(enclosing_ns(sc), nm);
    let r = scopes[sc].rec as i64;
    if r < 0 || r >= crecs.len { return; }
    let cr = crecs[r];
    for i in cr.nbases {
        let bt = cbases[cr.bases + i].ty;
        if is_record(bt) && !is_opaque(bt) {
            let bs = type_scope(bt);
            if bs >= 0 { adl_add_cls(bs, nm, cm, depth + 1); }
        }
    }
}

// Adds the functions named `name` that argument-dependent lookup finds for
// the arguments nscratch[mark..] to the candidates from mc; false when a
// deduction could not be decided.
recursive fn adl_candidates(mc: i64, name: u32, mark: i64, explicit: i32, oper: bool) -> bool {
    let nm = adl_ns.len;
    let cm = adl_cls.len;
    let nargs = nscratch.len - mark;
    for i in mark..nscratch.len {
        let e = nscratch[i];
        if nodes[e].kind as i64 == N_FUNCREF { continue; }
        adl_type(nodes[e].ty, nm, cm, 0);
    }
    var ok = true;
    let sv = vis_limit;
    vis_limit = 0x7FFFFFFF;
    for i in nm..adl_ns.len {
        var s = scope_find(adl_ns[i] as i64, name);
        while s >= 0 {
            let f = resolve(s);
            if f >= 0 {
                var take = true;
                if cxs[s].flags & CF_FRIEND != 0 {
                    // a friend is found through its class only
                    take = false;
                    let g = friend_class.get(s as u64);
                    if g { for j in cm..adl_cls.len { if adl_cls[j] as u32 == g { take = true; } } }
                }
                let k = syms[f].kind as i64;
                if take && (k == SK_FUNC || k == SK_TEMPLATE) && cxs[f].flags & CF_MEMBER == 0 {
                    if !add_candidate(mc, f, explicit, mark, nargs, oper) { ok = false; }
                }
            }
            s = cxs[s].nnext as i64;
        }
    }
    vis_limit = sv;
    adl_ns.resize(nm);
    adl_cls.resize(cm);
    return ok;
}

// ---------------------------------------------------------------------------
// Overloaded operators.

// An operator applied to operands l (and r; post: a postfix ++/--) with a
// class or enum operand: the call of the selected operator function, 0
// when the built-in operator applies (no candidate is viable), or an
// opaque node when the choice is not known.
recursive fn resolve_oper(op: i64, l: u32, r: u32, post: bool, loc: u32) -> u32 {
    if is_opq(l) || (r != 0 && is_opq(r) && nodes[r].kind as i64 != N_INITBRACE) { return 0; }
    let lt = nodes[l].ty;
    let lcls = is_record(lt);
    let rcls = r != 0 && nodes[r].kind as i64 != N_INITBRACE && is_record(nodes[r].ty);
    let lenum = kind_of(lt) == TY_ENUM;
    let renum = r != 0 && kind_of(nodes[r].ty) == TY_ENUM;
    if !lcls && !rcls && !lenum && !renum { return 0; }
    let name = op_ids[op];
    let mark = nscratch.len;
    nscratch.push(l);
    if r != 0 { nscratch.push(r); }
    if post { nscratch.push(int_node(0, t_int, loc)); }
    let nargs = nscratch.len - mark;
    let mc = cand_syms.len;
    var ok = true;
    if lcls {
        let sc = type_scope(lt);
        if sc >= 0 {
            var s = class_lookup(sc, name);
            while s >= 0 {
                let f = resolve(s);
                if f >= 0 && (syms[f].kind as i64 == SK_FUNC || syms[f].kind as i64 == SK_TEMPLATE) {
                    if !add_candidate(mc, f, -1, mark, nargs, true) { ok = false; }
                }
                s = cxs[s].nnext as i64;
            }
        }
    }
    if op != OP_EQUAL && op != OP_CALL && op != OP_SUBSCRIPT && op != OP_ARROW {
        // non-members: unqualified lookup (members ignored), then ADL
        var s = unqual_lookup_nonmember(name);
        while s >= 0 {
            let f = resolve(s);
            if f >= 0 && visible(s) && cxs[s].flags & CF_FRIEND == 0 && (syms[f].kind as i64 == SK_FUNC || syms[f].kind as i64 == SK_TEMPLATE) &&
               cxs[f].flags & CF_MEMBER == 0 {
                if !add_candidate(mc, f, -1, mark, nargs, true) { ok = false; }
            }
            s = cxs[s].nnext as i64;
        }
        if !adl_candidates(mc, name, mark, -1, true) { ok = false; }
    }
    if cand_syms.len == mc && ok {
        nscratch.resize(mark);
        return 0;
    }
    cand_oper = true;
    let f = best_of_candidates(mc, mark, true, !ok);
    if f < 0 {
        let unk = cand_unknown;
        let nv = cand_nviable;
        nscratch.resize(mark);
        if !unk && nv == 0 { return 0; }        // the built-in operator
        return opaque_node(loc);
    }
    inst_use(f);
    let member = cxs[f].flags & CF_MEMBER != 0;
    if cg_on {
        if member {
            // the object is the first operand; the arguments follow it
            let obj = nscratch[mark];
            let m2 = nscratch.len;
            for i in mark + 1..m2 { nscratch.push(nscratch[i]); }
            let c = cg_call(f, obj, m2, loc, false);
            nscratch.resize(mark);
            return c;
        }
        let c = lower_call(f, 0, mark, loc, false);
        nscratch.resize(mark);
        return c;
    }
    nscratch.resize(mark);
    resolved_fn = f;
    return typed_result(types[syms[f].ty >> 4].base, loc);
}

// Unqualified lookup of `name` skipping class scopes (non-member operator
// candidates, C++ [over.match.oper]p3.2).
recursive fn unqual_lookup_nonmember(name: u32) -> i64 {
    let l = local_lookup(name);
    if l >= 0 { return l; }
    var sc = cur_scope;
    while sc >= 0 {
        let k = scopes[sc].kind as i64;
        if k == CS_NS {
            let s = ns_lookup(sc, name, false);
            if s >= 0 { return s; }
        }
        sc = scopes[sc].parent as i64;
    }
    return -1;
}
