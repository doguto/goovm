// goosecc D3: run-time type information in code generation: typeid and
// dynamic_cast, as clang does (CGExprCXX.cpp, ItaniumCXXABI.cpp):
//
//   typeid(T), typeid(e) of a non-polymorphic type   *(const std::type_info *)&_ZTI<T>
//   typeid(glvalue of polymorphic class)              the vtable's entry -1
//                                                     (typeid(*p): __cxa_bad_typeid() when p is null)
//   dynamic_cast to a base                            the derived-to-base conversion
//   dynamic_cast<cv void *>(p)                        p + offset-to-top (vtable entry -2)
//   dynamic_cast<D *>(p)                              p ? __dynamic_cast(p, &_ZTI<S>, &_ZTI<D>, hint) : 0
//   dynamic_cast<D &>(l)                              the same, __cxa_bad_cast() on a null result
//
// The hint is clang's computeOffsetHint (Itanium 2.9.7).

namespace cx;

import std;
import dictionary;
import .common;
import .types;
import .ast;
import .sema;
import .parse;
import .cx_core;
import .cx_names;
import .cx_expr;
import .cx_sema;
import .cx_over;
import .cx_layout;
import .cx_mangle;
import .cx_gen_defs;
import .cx_gen_eh;
import .cx_gen_vt;

// std::type_info (0 when <typeinfo> was not included).
var ti_type_cache: u32 = 0;
var ti_type_done = false;
fn std_type_info() -> u32 {
    if ti_type_done { return ti_type_cache; }
    let st = ns_lookup(0, id_std, true);
    if st < 0 { return 0; }
    let ns = sym_scope(st);
    if ns < 0 { return 0; }
    let s = resolve(ns_lookup(ns, intern("type_info"), false));
    if s < 0 || syms[s].kind as i64 != SK_TAG || !is_record(syms[s].ty) || !is_complete(syms[s].ty) { return 0; }
    ti_type_done = true;
    ti_type_cache = unqual(syms[s].ty);
    return ti_type_cache;
}

fn rt_fn4(name: const u8[:], ret: u32, p0: u32, p1: u32, p2: u32, p3: u32, nothrow: bool) -> i64 {
    let id = intern(name);
    let g = rt_syms.get(id as u64);
    if g { return g as i64; }
    fn_scratch.clear();
    fn_scratch.push(p0);
    fn_scratch.push(p1);
    fn_scratch.push(p2);
    fn_scratch.push(p3);
    let ft = qt(mk_type(TY_FUNC, 0, ret, 0, 0, 0) as i64, 0);
    let s = csym(SK_FUNC, id, ft, 0);
    syms[s].sc = SC_EXTERN as! u8;
    syms[s].flags = SF_FILESCOPE;
    cxs[s].flags = CF_EXTERN_C;
    rt_syms.insert(id as u64, s as! u32);
    if nothrow { rt_nothrow.push(s as! u32); }
    return s;
}

fn rt_dynamic_cast() -> i64 {
    let cv = mk_ptr(with_q(t_void, Q_CONST));
    return rt_fn4("__dynamic_cast", t_voidptr, cv, cv, cv, t_long, true);
}
fn rt_bad_cast() -> i64 { rt_fn("__cxa_bad_cast", t_void, 0, 0, 0, 0, false, true) }
fn rt_bad_typeid() -> i64 { rt_fn("__cxa_bad_typeid", t_void, 0, 0, 0, 0, false, true) }

// The pointer operand of a glvalue that is *p (through parentheses and
// no-op casts), or 0 (clang's isGLValueFromPointerDeref, simplified).
fn deref_operand(e0: u32) -> u32 {
    var e = e0;
    while (nodes[e].kind as i64 == N_ICAST || nodes[e].kind as i64 == N_CAST) && nodes[e].op as i64 == CK_NOOP { e = nodes[e].a; }
    if nodes[e].kind as i64 == N_UNARY && nodes[e].op as i64 == U_DEREF { return nodes[e].a; }
    return 0;
}

// The vtable entry k (-1: type_info, -2: offset to top) of the object at
// pointer p (a pointer to a dynamic class), as a value of type et.
fn vtable_entry(p: u32, k: i64, et: u32, loc: u32) -> u32 {
    let pet = mk_ptr(et);
    let vptr = rv(n_deref(node(N_ICAST, CK_BITCAST, mk_ptr(pet), p as i64, 0, 0, loc), loc));
    let at = node(N_BINARY, B_PTRADD, pet, vptr as i64, int_node(k, t_long, loc) as i64, 0, loc);
    return rv(n_deref(at, loc));
}

// typeid(t) (e == 0) or typeid(e).
recursive fn cg_typeid(t0: u32, e: u32, loc: u32) -> u32 {
    let ti = std_type_info();
    if ti == 0 { return opaque_node(loc); }
    let cti = with_q(ti, Q_CONST);
    let pti = mk_ptr(cti);
    var t = t0;
    if e != 0 {
        if is_opq(e) { return opaque_node(loc); }
        t = nodes[e].ty;
        if is_record(t) && is_lvalue(e) && is_complete(t) && crecs[rec_of(t)].flags & CR_POLY != 0 {
            // the dynamic type: through the vtable
            let p = deref_operand(e);
            if p != 0 {
                let pt = unqual(nodes[p].ty);
                let s = csym(SK_VAR, intern("__typeid_tmp"), pt, loc);
                syms[s].scope = 1;
                let mark = nscratch.len;
                nscratch.push(node(N_DECL, 0, pt, s, rv(p) as i64, loc as i64, loc));
                let bm = nscratch.len;
                let bad = n_expr_stmt(rt_call(rt_bad_typeid(), bm, loc));
                let isnull = node(N_UNARY, U_NOT, t_int, icast(rv(n_var(s, loc)), CK_PTR2BOOL, t_bool) as i64, 0, 0, loc);
                nscratch.push(node(N_IF, 0, 0, isnull as i64, bad as i64, 0, loc));
                nscratch.push(n_expr_stmt(vtable_entry(rv(n_var(s, loc)), -1, pti, loc)));
                let body = n_block(mark, loc);
                return n_deref(node(N_STMTEXPR, 0, pti, body as i64, 0, 0, loc), loc);
            }
            return n_deref(vtable_entry(n_addr(e, loc), -1, pti, loc), loc);
        }
    }
    t = unqual(nonref(t));
    if is_opaque(t) { return opaque_node(loc); }
    if is_record(t) && !is_complete(t) { return opaque_node(loc); }
    let v = typeinfo_var(t);
    if v < 0 { return opaque_node(loc); }
    return n_deref(node(N_ICAST, CK_BITCAST, pti, void_addr_of_any(v, loc) as i64, 0, 0, loc), loc);
}

// computeOffsetHint: the offset of Src in Dst when Src is a unique public
// non-virtual base, -1 (a virtual base on a public path), -2 (not a public
// base), -3 (a public base more than once, never virtual).
var hint_npub: i64 = 0;
var hint_off: i64 = 0;
var hint_virtual = false;
var hint_vis: u32[>..<] = [];

fn offset_hint(src: i64, dst: i64) -> i64 {
    hint_npub = 0;
    hint_off = 0;
    hint_virtual = false;
    hint_vis.clear();
    hint_walk(dst, src, 0, true, false);
    if hint_virtual { return -1; }
    if hint_npub == 0 { return -2; }
    if hint_npub > 1 { return -3; }
    return hint_off;
}

// CXXBasePaths' lookup: a virtual base is entered once, every path to src
// recorded in order.
recursive fn hint_walk(d: i64, src: i64, off: i64, pub: bool, virt: bool) {
    for i in vt_nbases(d) {
        let b = cbases[crecs[d].bases + i];
        if !is_record(b.ty) { continue; }
        let br = rec_of(b.ty);
        let bv = b.flags & BF_VIRTUAL != 0;
        var visit = true;
        if bv {
            for x in hint_vis { if x as i64 == br { visit = false; } }
            if visit { hint_vis.push(br as! u32); }
        }
        let p = pub && b.access as i64 == 0;
        let v = virt || bv;
        let o = if bv { 0 } else { off + b.offset };
        if br == src {
            if p {
                hint_npub++;
                if v { hint_virtual = true; }
                else if hint_npub == 1 { hint_off = o; }
            }
        } else if visit {
            hint_walk(br, src, o, p, v);
        }
    }
}

// dynamic_cast<t>(e).
recursive fn cg_dynamic_cast(t: u32, e: u32, loc: u32) -> u32 {
    if is_opq(e) || is_opaque(t) { return opaque_node(loc); }
    if is_ref(t) {
        let to = tbase(t);
        if !is_record(to) || !is_record(nodes[e].ty) || !is_lvalue(e) { return opaque_node(loc); }
        let xv = if kind_of(t) == TY_RREF { NF_XVALUE } else { 0 };
        if unqual(nodes[e].ty) == unqual(to) {
            let n = node(N_CAST, CK_NOOP, to, e as i64, 0, 0, loc);
            nodes[n].flags = (NF_LVALUE | xv) as! u16;
            return n;
        }
        let up = derived_to_base_lv(e, to, loc);
        if up != 0 { nodes[up].flags = (nodes[up].flags | xv) as! u16; return up; }
        let st = unqual(nodes[e].ty);
        let c = dyn_call(n_addr(e, loc), st, unqual(to), loc);
        if c == 0 { return opaque_node(loc); }
        // ({ void *r = __dynamic_cast(...); if (!r) __cxa_bad_cast(); (T *)r; })
        let s = csym(SK_VAR, intern("__dyncast_tmp"), t_voidptr, loc);
        syms[s].scope = 1;
        let mark = nscratch.len;
        nscratch.push(node(N_DECL, 0, t_voidptr, s, c as i64, loc as i64, loc));
        let bm = nscratch.len;
        let bad = n_expr_stmt(rt_call(rt_bad_cast(), bm, loc));
        let isnull = node(N_UNARY, U_NOT, t_int, icast(rv(n_var(s, loc)), CK_PTR2BOOL, t_bool) as i64, 0, 0, loc);
        nscratch.push(node(N_IF, 0, 0, isnull as i64, bad as i64, 0, loc));
        nscratch.push(n_expr_stmt(node(N_ICAST, CK_BITCAST, mk_ptr(to), rv(n_var(s, loc)) as i64, 0, 0, loc)));
        let body = n_block(mark, loc);
        let r = n_deref(node(N_STMTEXPR, 0, mk_ptr(to), body as i64, 0, 0, loc), loc);
        nodes[r].flags = (NF_LVALUE | xv) as! u16;
        return r;
    }
    if !is_pointer(t) { return opaque_node(loc); }
    let pv = rv(e);
    let ft = unqual(nodes[pv].ty);
    if kind_of(ft) == TY_NULLPTR { return icast(pv, CK_NULL2PTR, unqual(t)); }
    if !is_pointer(ft) || !is_record(tbase(ft)) { return opaque_node(loc); }
    let st = unqual(tbase(ft));
    let dt = tbase(t);
    if !is_void(dt) {
        if !is_record(dt) { return opaque_node(loc); }
        if unqual(dt) == st { return node(N_ICAST, CK_NOOP, unqual(t), pv as i64, 0, 0, loc); }
        let up = cg_ptr_conv(pv, unqual(t), loc);
        if up != 0 { return up; }
    }
    if !is_complete(st) || crecs[rec_of(st)].flags & CR_POLY == 0 { return opaque_node(loc); }
    // ({ S *tmp = p; tmp ? <cast> : 0; })
    let s = csym(SK_VAR, intern("__dyncast_tmp"), ft, loc);
    syms[s].scope = 1;
    let mark = nscratch.len;
    nscratch.push(node(N_DECL, 0, ft, s, pv as i64, loc as i64, loc));
    var r: u32 = 0;
    if is_void(dt) {
        // the most derived object: p + offset to top
        let cp = node(N_ICAST, CK_BITCAST, mk_ptr(t_char), rv(n_var(s, loc)) as i64, 0, 0, loc);
        let ot = vtable_entry(rv(n_var(s, loc)), -2, t_long, loc);
        r = node(N_BINARY, B_PTRADD, mk_ptr(t_char), cp as i64, ot as i64, 0, loc);
    } else {
        r = dyn_call(rv(n_var(s, loc)), st, unqual(dt), loc);
        if r == 0 { nscratch.resize(mark); return opaque_node(loc); }
    }
    let cv = node(N_ICAST, CK_BITCAST, unqual(t), r as i64, 0, 0, loc);
    let z = node(N_ICAST, CK_NULL2PTR, unqual(t), int_node(0, t_int, loc) as i64, 0, 0, loc);
    let c = node(N_COND, 0, unqual(t), icast(rv(n_var(s, loc)), CK_PTR2BOOL, t_bool) as i64, cv as i64, z as i64, loc);
    nscratch.push(n_expr_stmt(c));
    let body = n_block(mark, loc);
    return node(N_STMTEXPR, 0, unqual(t), body as i64, 0, 0, loc);
}

// __dynamic_cast(p, &_ZTI<src>, &_ZTI<dst>, hint), or 0.
fn dyn_call(p: u32, src: u32, dst: u32, loc: u32) -> u32 {
    if !is_complete(src) || !is_complete(dst) { return 0; }
    let sr = rec_of(src);
    let dr = rec_of(dst);
    if crecs[sr].flags & CR_POLY == 0 { return 0; }
    let sti = typeinfo_sym(sr);
    let dti = typeinfo_sym(dr);
    if sti < 0 || dti < 0 { return 0; }
    let cv = mk_ptr(with_q(t_void, Q_CONST));
    let mark = nscratch.len;
    nscratch.push(node(N_ICAST, CK_BITCAST, cv, p as i64, 0, 0, loc));
    nscratch.push(node(N_ICAST, CK_BITCAST, cv, void_addr_of_any(sti, loc) as i64, 0, 0, loc));
    nscratch.push(node(N_ICAST, CK_BITCAST, cv, void_addr_of_any(dti, loc) as i64, 0, 0, loc));
    nscratch.push(int_node(offset_hint(sr, dr), t_long, loc));
    return rt_call(rt_dynamic_cast(), mark, loc);
}
