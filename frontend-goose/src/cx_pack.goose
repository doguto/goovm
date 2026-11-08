// goosecc D2: variadic templates. A template parameter pack bound to a
// list (a TA_PACK binding) is one symbol with CF2_PACKBIND; a function
// parameter pack of an instantiated declaration is likewise one symbol
// (SK_VAR) over the parameters it expanded to. A pack expansion `P...` in
// a list (template arguments, call arguments, braced lists, parameters,
// bases, mem-initializers) is handled where the list is parsed: the
// element P is parsed once, noting the bound packs it names (pk_refs:
// resolve() records them and gives the pack itself, whose type is
// unknown); at the `...` the element's tokens are parsed again once per
// element of those packs, with each pack naming its i-th element
// (pk_active), and the results replace the first parse's. sizeof...
// counts, fold-expressions expand into the operator chain.

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
import .cx_inst;

var pk_refs: u32[>..<] = [];        // bound packs named since an element began
var pk_active: u64[>..<] = [];      // (pack << 20 | index): packs being expanded
var pk_elems: u32[>..] = [];        // function parameter packs: their parameters
var pk_elem_cache = dictionary<u64, u32> {};   // (pack << 20 | index) -> element symbol
var plist_packs = dictionary<u64, u32> {};     // a parameter list (nlist start) -> the packs after it

// A use of pack symbol x: its element while it is expanded, else x (noted).
fn pk_use(x: i64) -> i64 {
    var j = pk_active.len - 1;
    while j >= 0 {
        let e = pk_active[j];
        if (e >> 20) as i64 == x { return pk_elem(x, (e & 0xFFFFF) as i64); }
        j--;
    }
    pk_refs.push(x as! u32);
    return x;
}

// The number of elements of a bound pack, -1 unknown.
fn pk_len(x: i64) -> i64 {
    let k = syms[x].kind as i64;
    if k == SK_VAR { return syms[x].v & 0xFFFFF; }
    if syms[x].v < 0 { return -1; }
    return tl_count(syms[x].v);
}

// Element i of bound pack x (a symbol).
fn pk_elem(x: i64, i: i64) -> i64 {
    let k = syms[x].kind as i64;
    if k == SK_VAR {
        let st = syms[x].v >> 20;
        return pk_elems[st + i] as i64;
    }
    let key = ((x as u64) << 20) | (i as u64);
    let g = pk_elem_cache.get(key);
    if g { return g as i64; }
    let a = tl_arg(syms[x].v, i);
    var s: i64 = -1;
    if a.kind as i64 == TA_VALUE {
        s = csym(SK_NTTP, syms[x].name, a.ty, 0);
        syms[s].v = a.v;
        cxs[s].flags = CF_TPARAM | CF_SUBST;
    } else if a.kind as i64 == TA_TEMPLATE {
        s = csym(SK_USING, syms[x].name, 0, 0);
        cxs[s].target = a.v as! i32;
    } else {
        s = csym(SK_TYPEDEF, syms[x].name, a.ty, 0);
        syms[s].sc = SC_TYPEDEF;
    }
    syms[s].scope = 0;
    cxs[s].pos = 0;
    pk_elem_cache.insert(key, s as! u32);
    return s;
}

// After an element whose bound packs were noted from `mark`: the number
// of times to expand it (false when it names no bound pack of known
// length, or packs of different lengths).
fn pk_count(mark: i64) -> bool, i64 {
    var n: i64 = -1;
    for i in mark..pk_refs.len {
        let x = pk_refs[i] as i64;
        let l = pk_len(x);
        if l < 0 { return false, 0; }
        if n >= 0 && l != n { return false, 0; }
        n = l;
    }
    if n < 0 { return false, 0; }
    return true, n;
}

// Expansion i: the packs noted from mark name their i-th elements.
fn pk_activate(mark: i64, i: i64) -> i64 {
    let am = pk_active.len;
    for j in mark..pk_refs.len {
        let x = pk_refs[j] as i64;
        var seen = false;
        for k in am..pk_active.len { if (pk_active[k] >> 20) as i64 == x { seen = true; } }
        if !seen { pk_active.push(((x as u64) << 20) | (i as u64)); }
    }
    return am;
}

// A function parameter pack over the parameters nscratch[from..to).
fn pk_param_pack(name: u32, from: i64, to: i64, loc: u32) -> i64 {
    let st = pk_elems.len;
    for i in from..to {
        pk_elems.push(nscratch[i]);
        cxs[nscratch[i]].flags2 = cxs[nscratch[i]].flags2 | CF2_PACKELEM;
    }
    let s = csym(SK_VAR, name, t_unknown, loc);
    syms[s].flags = SF_PARAM;
    syms[s].v = ((st as i64) << 20) | (to - from);
    cxs[s].flags2 = CF2_PACKBIND;
    return s;
}
let CF2_PACKELEM = 64;      // a parameter a function parameter pack expanded to

// Binds a function's parameters (and the parameter packs after them).
fn bind_params(start: i64, count: i64) {
    for i in count {
        let p = nlist[start + i] as i64;
        if syms[p].name != 0 { bind_sym(p, false); }
    }
    let g = plist_packs.get(start as u64);
    if g {
        for i in g as i64 {
            let p = nlist[start + count + i] as i64;
            bind_sym(p, false);
        }
    }
}

// ---------------------------------------------------------------------------
// Fold-expressions (C++ [expr.prim.fold]) over bound packs.

// The packs noted from mark, kept (pk_saved from the returned mark) for
// the expansions of one construct; pk_refs back to mark.
var pk_saved: u32[>..<] = [];
fn pk_save(mark: i64) -> i64 {
    let sm = pk_saved.len;
    for j in mark..pk_refs.len { pk_saved.push(pk_refs[j]); }
    pk_refs.resize(mark);
    return sm;
}
// Expansion i of the packs saved from sm.
fn pk_activate_saved(sm: i64, i: i64) -> i64 {
    let am = pk_active.len;
    for j in sm..pk_saved.len {
        let x = pk_saved[j] as i64;
        var seen = false;
        for k in am..pk_active.len { if (pk_active[k] >> 20) as i64 == x { seen = true; } }
        if !seen { pk_active.push(((x as u64) << 20) | (i as u64)); }
    }
    return am;
}

// l op r for a fold's operator token k.
recursive fn fold_combine(k: i64, l: u32, r: u32, loc: u32) -> u32 {
    let aop = assign_op(k);
    if k == TK_EQUAL || aop != 0 { return mk_assign_cx(if k == TK_EQUAL { 0 } else { aop }, l, r, loc, k); }
    if k == TK_COMMA { return mk_binop(OP_COMMA, B_COMMA, l, r, loc); }
    return mk_binop(tok_op(k), bin_op(k), l, r, loc);
}

// A fold over an empty pack: && true, || false, `,` void().
fn fold_empty(k: i64, loc: u32) -> u32 {
    if k == TK_AMPAMP { return int_node(1, t_bool, loc); }
    if k == TK_PIPEPIPE { return int_node(0, t_bool, loc); }
    if k == TK_COMMA { return node(N_ZEROINIT, 0, t_void, 0, 0, 0, loc); }
    err_at(loc, "unary fold expression has empty expansion for operator");
    return opaque_node(loc);
}

// The operands of a fold: the cast-expression at p0 once per element of
// the packs saved from sm, pushed to nscratch.
recursive fn fold_operands(p0: i64, sm: i64, n: i64) {
    for i in n {
        pc = p0;
        gt_pos = -1;
        let am = pk_activate_saved(sm, i);
        let x = parse_cast_cx();
        pk_active.resize(am);
        nscratch.push(x);
    }
}

// After `( first` with pc at `op ...`: the rest of a fold-expression, up
// to and including ')'. first began at p0, pm marks the packs it named.
recursive fn parse_fold_rest(first: u32, p0: i64, pm: i64, loc: u32) -> u32 {
    let k = tk();
    let ok, n = pk_count(pm);
    adv();      // op
    adv();      // ...
    if ok {
        // ( E op ... ) or ( E op ... op I ): a right fold
        let sm = pk_save(pm);
        var init: u32 = 0;
        var has_init = false;
        if tk() == k {
            adv();
            init = parse_cast_cx();
            has_init = true;
        }
        let p1 = pc;
        let mark = nscratch.len;
        fold_operands(p0, sm, n);
        pk_saved.resize(sm);
        pc = p1;
        gt_pos = -1;
        expect(TK_R_PAREN, "')'");
        if n == 0 { nscratch.resize(mark); if has_init { return init; } return fold_empty(k, loc); }
        var acc: u32 = if has_init { init } else { nscratch[mark + n - 1] };
        var j = if has_init { n - 1 } else { n - 2 };
        while j >= 0 {
            acc = fold_combine(k, nscratch[mark + j], acc, loc);
            j--;
        }
        nscratch.resize(mark);
        return acc;
    }
    pk_refs.resize(pm);
    // ( I op ... op E ): a left fold with an initializer
    if tk() == k {
        adv();
        let q0 = pc;
        let qm = pk_refs.len;
        let e = parse_cast_cx();
        let ok2, n2 = pk_count(qm);
        if ok2 {
            let sm = pk_save(qm);
            let p1 = pc;
            let mark = nscratch.len;
            fold_operands(q0, sm, n2);
            pk_saved.resize(sm);
            var acc = first;
            for i in n2 { acc = fold_combine(k, acc, nscratch[mark + i], loc); }
            nscratch.resize(mark);
            pc = p1;
            gt_pos = -1;
            expect(TK_R_PAREN, "')'");
            return acc;
        }
        pk_refs.resize(qm);
    }
    skip_to(TK_R_PAREN);
    expect(TK_R_PAREN, "')'");
    return dep_node(t_unknown, loc);
}

// After `( ...` (pc at the operator): ( ... op E ), a left fold.
recursive fn parse_fold_left(loc: u32) -> u32 {
    let k = tk();
    adv();      // op
    let p0 = pc;
    let pm = pk_refs.len;
    let e = parse_cast_cx();
    let ok, n = pk_count(pm);
    if !ok {
        pk_refs.resize(pm);
        skip_to(TK_R_PAREN);
        expect(TK_R_PAREN, "')'");
        return dep_node(t_unknown, loc);
    }
    let sm = pk_save(pm);
    let p1 = pc;
    let mark = nscratch.len;
    fold_operands(p0, sm, n);
    pk_saved.resize(sm);
    pc = p1;
    gt_pos = -1;
    expect(TK_R_PAREN, "')'");
    if n == 0 { nscratch.resize(mark); return fold_empty(k, loc); }
    var acc = nscratch[mark];
    for i in 1..n { acc = fold_combine(k, acc, nscratch[mark + i], loc); }
    nscratch.resize(mark);
    return acc;
}

// sizeof...(name): the length of a bound pack, -1 (not one).
fn pack_size_of(name: u32) -> i64 {
    let s = unqual_lookup(name);
    if s < 0 || cxs[s].flags2 & CF2_PACKBIND == 0 { return -1; }
    return pk_len(s);
}
