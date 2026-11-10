// goosecc D2: the C++ constant evaluator (C++ [expr.const]).
//
// Evaluates the semantic analysis's trees (the ones -fsyntax-only builds:
// C nodes for what C has, N_CXX op 7 calls with their function, object and
// arguments, N_CTOR constructions, N_THIS) over an abstract machine:
//
//  - objects live in byte memories laid out as the target lays them out
//    (type_size, field offsets): ce_mem for the evaluation's locals and
//    temporaries (reset when a top-level evaluation ends), ce_g for the
//    objects that outlive it (string literals, constexpr variables);
//  - an address is an offset in ce_mem (from 16), CE_G + an offset in
//    ce_g, or CE_FN + a function symbol; 0 is the null pointer;
//  - calls run the functions' bodies, parsed again for the evaluation in
//    semantic-analysis mode (ce_body), parameters and locals in frames.
//
// Anything not modelled makes the evaluation fail (not a constant): never
// a wrong value. Evaluation is bounded (steps, depth).

namespace cx;

import std;
import dictionary;
import .common;
import .types;
import .ast;
import .sema;
import .expr;
import .parse;
import .cx_core;
import .cx_names;

struct CeV { k: u8, ty: u32, i: i64, f: f64 }
let CE_FAIL = 0;
let CE_INT = 1;
let CE_FLT = 2;
let CE_PTR = 3;
let CE_OBJ = 4;     // an object of class or array type at address i
let CE_VOID = 5;

let CE_G = 1099511627776;       // 1 << 40: the global memory
let CE_FN = 2199023255552;      // 2 << 40: functions

var ce_mem: u8[>..<] = [];
var ce_g: u8[>..<] = [];
var ce_steps: i64 = 0;
var ce_depth: i64 = 0;
var ce_active: i64 = 0;         // > 0 while evaluating (__builtin_is_constant_evaluated)
var ce_locals: i64[>..<] = [];  // (symbol, address) pairs of the frames
var ce_frame: i64 = 0;          // the current frame's first pair
var ce_this: i64 = 0;           // the current member function's object
var ce_rv_val: CeV = CeV { k: 0, ty: 0, i: 0, f: 0.0 };     // a return statement's value
var ce_ret_addr: i64 = 0;       // the return slot of a function returning a class
var ce_gvars = dictionary<u64, u64> {};     // variable -> its object in ce_g (+1)
var ce_gbusy = dictionary<u64, u32> {};     // variables being initialized (recursion)
var ce_strs = dictionary<u64, u64> {};      // string literal -> its array in ce_g
var ce_var_init = dictionary<u64, u32> {};  // constexpr / const variable -> its initializer (analysis tree)
var ce_why: i64 = 0;            // debugging: the node an evaluation failed at

fn ce_fail() -> CeV { CeV { k: CE_FAIL as! u8, ty: 0, i: 0, f: 0.0 } }
fn ce_int(v: i64, t: u32) -> CeV { CeV { k: CE_INT as! u8, ty: t, i: v, f: 0.0 } }
fn ce_flt(v: f64, t: u32) -> CeV { CeV { k: CE_FLT as! u8, ty: t, i: 0, f: v } }
fn ce_ptr(a: i64, t: u32) -> CeV { CeV { k: CE_PTR as! u8, ty: t, i: a, f: 0.0 } }
fn ce_obj(a: i64, t: u32) -> CeV { CeV { k: CE_OBJ as! u8, ty: t, i: a, f: 0.0 } }
fn ce_void() -> CeV { CeV { k: CE_VOID as! u8, ty: 0, i: 0, f: 0.0 } }

fn ce_debug() -> bool {
    if ce_dbg_mode < 0 {
        var v: u8[>..] = [];
        ce_dbg_mode = if env("GOOSECC_DEBUG_CE", v) && v.len > 0 && v[0] == '1' { 1 } else { 0 };
    }
    return ce_dbg_mode == 1;
}
var ce_dbg_mode: i64 = -1;
fn ce_bad(n: u32) -> CeV {
    if ce_why == 0 { ce_why = n as i64; }
    if ce_debug() {
        var o: u8[>..] = [];
        loc_prefix(o, nodes[n].loc as i64);
        o.append(str("ce: cannot evaluate node kind ", nodes[n].kind, " op ", nodes[n].op, "\n"));
        write_stderr(o);
    }
    return ce_fail();
}

// ---------------------------------------------------------------------------
// Memory.

fn ce_alloc(size0: i64, align0: i64, global: bool) -> i64 {
    let size = if size0 <= 0 { 1 } else { size0 };
    let al = if align0 <= 0 { 1 } else { align0 };
    if global {
        if ce_g.len < 16 { while ce_g.len < 16 { ce_g.push(0); } }
        while ce_g.len % al != 0 { ce_g.push(0); }
        let a = ce_g.len;
        for i in size { ce_g.push(0); }
        return CE_G + a;
    }
    if ce_mem.len < 16 { while ce_mem.len < 16 { ce_mem.push(0); } }
    while ce_mem.len % al != 0 { ce_mem.push(0); }
    let a = ce_mem.len;
    if a + size > 268435456 { return -1; }
    for i in size { ce_mem.push(0); }
    return a;
}

fn ce_valid(a: i64, n: i64) -> bool {
    if a >= CE_FN || a < 16 { return false; }
    if a >= CE_G { return a - CE_G + n <= ce_g.len; }
    return a + n <= ce_mem.len;
}

fn ce_ld(a: i64, n: i64) -> i64 {
    var v: i64 = 0;
    if a >= CE_G {
        let o = a - CE_G;
        var i = n - 1;
        while i >= 0 { v = (v << 8) | (ce_g[o + i] as i64); i--; }
        return v;
    }
    var i = n - 1;
    while i >= 0 { v = (v << 8) | (ce_mem[a + i] as i64); i--; }
    return v;
}

fn ce_st(a: i64, n: i64, v: i64) {
    var x = v;
    if a >= CE_G {
        let o = a - CE_G;
        for i in n { ce_g[o + i] = (x & 255) as! u8; x = x >> 8; }
        return;
    }
    for i in n { ce_mem[a + i] = (x & 255) as! u8; x = x >> 8; }
}

fn ce_copy(dst: i64, src: i64, n: i64) {
    for i in n { ce_st(dst + i, 1, ce_ld(src + i, 1)); }
}

fn ce_zero(dst: i64, n: i64) { for i in n { ce_st(dst + i, 1, 0); } }

extern fn ce_f32_bits(v: f64) -> i64 = "goosecc_f32_bits";
extern fn ce_bits_f32(v: i64) -> f64 = "goosecc_bits_f32";

// The value of the object of type t at a.
fn ce_load(a: i64, t0: u32) -> CeV {
    let t = unqual(t0);
    let k = kind_of(t);
    if is_record(t) || is_array(t) { return ce_obj(a, t); }
    if is_ref(t) {
        if !ce_valid(a, 8) { return ce_fail(); }
        return ce_ptr(ce_ld(a, 8), mk_ptr(tbase(t)));
    }
    let sz = type_size(t);
    if sz <= 0 || !ce_valid(a, if sz > 8 { 8 } else { sz }) { return ce_fail(); }
    if k == TY_FLOAT { return ce_flt(ce_bits_f32(ce_ld(a, 4)), t); }
    if k == TY_DOUBLE || k == TY_LDOUBLE || k == TY_FLOAT128 { return ce_flt(reinterpret_f64(ce_ld(a, 8)), t); }
    if is_pointer(t) || k == TY_NULLPTR { return ce_ptr(ce_ld(a, 8), t); }
    if is_integer(t) || k == TY_BOOL || k == TY_ENUM {
        if sz > 8 { return ce_fail(); }
        return ce_int(trunc_to(ce_ld(a, sz), t), t);
    }
    return ce_fail();
}

// Stores scalar v (already of type t) at a.
fn ce_store(a: i64, t0: u32, v: CeV) -> bool {
    let t = unqual(t0);
    let k = kind_of(t);
    if v.k == CE_OBJ as! u8 {
        let n = type_size(t);
        if n <= 0 || !ce_valid(a, n) || !ce_valid(v.i, n) { return false; }
        ce_copy(a, v.i, n);
        return true;
    }
    if is_ref(t) || is_pointer(t) || k == TY_NULLPTR {
        if v.k != CE_PTR as! u8 || !ce_valid(a, 8) { return false; }
        ce_st(a, 8, v.i);
        return true;
    }
    let sz = type_size(t);
    if sz <= 0 || sz > 16 || !ce_valid(a, if sz > 8 { 8 } else { sz }) { return false; }
    if k == TY_FLOAT { if v.k != CE_FLT as! u8 { return false; } ce_st(a, 4, ce_f32_bits(v.f)); return true; }
    if k == TY_DOUBLE || k == TY_LDOUBLE || k == TY_FLOAT128 { if v.k != CE_FLT as! u8 { return false; } ce_st(a, 8, reinterpret_i64(v.f)); return true; }
    if v.k != CE_INT as! u8 || sz > 8 { return false; }
    ce_st(a, sz, v.i);
    return true;
}

// ---------------------------------------------------------------------------
// Conversions.

fn ce_conv(v: CeV, to0: u32) -> CeV {
    if v.k == CE_FAIL as! u8 { return v; }
    let to = unqual(nonref(to0));
    let k = kind_of(to);
    if k == TY_VOID { return ce_void(); }
    if k == TY_BOOL {
        if v.k == CE_INT as! u8 { return ce_int(if v.i != 0 { 1 } else { 0 }, to); }
        if v.k == CE_FLT as! u8 { return ce_int(if v.f != 0.0 { 1 } else { 0 }, to); }
        if v.k == CE_PTR as! u8 {
            // a pointer to an object or function is never null
            return ce_int(if v.i != 0 { 1 } else { 0 }, to);
        }
        return ce_fail();
    }
    if is_integer(to) || k == TY_ENUM {
        if v.k == CE_INT as! u8 { return ce_int(trunc_to(v.i, to), to); }
        if v.k == CE_FLT as! u8 {
            if v.f != v.f { return ce_fail(); }
            return ce_int(trunc_to(float_to_int(v.f, to), to), to);
        }
        return ce_fail();
    }
    if k == TY_FLOAT || k == TY_DOUBLE || k == TY_LDOUBLE || k == TY_FLOAT128 {
        var f: f64 = 0.0;
        if v.k == CE_INT as! u8 {
            if v.ty != 0 && !is_signed(v.ty) && v.i < 0 { f = (v.i as! u64) as! f64; } else { f = v.i as! f64; }
        } else if v.k == CE_FLT as! u8 { f = v.f; }
        else { return ce_fail(); }
        if k == TY_FLOAT { f = round_f32(f); }
        return ce_flt(f, to);
    }
    if is_pointer(to) || k == TY_NULLPTR {
        if v.k == CE_PTR as! u8 { return ce_ptr(v.i, to); }
        if v.k == CE_INT as! u8 && v.i == 0 { return ce_ptr(0, to); }
        return ce_fail();
    }
    if is_record(to) || is_array(to) {
        if v.k == CE_OBJ as! u8 { return v; }
        return ce_fail();
    }
    return ce_fail();
}

// ---------------------------------------------------------------------------
// Lvalues: the address of the object e designates.

recursive fn ce_lv(e: u32) -> bool, i64 {
    let nd = nodes[e];
    let k = nd.kind as i64;
    ce_steps++;
    if k == N_DECLREF {
        let s = nd.a as i64;
        if syms[s].kind as i64 != SK_VAR { if syms[s].kind as i64 == SK_FUNC { return true, CE_FN + s; } return false, 0; }
        let a = ce_var_addr(s);
        if a <= 0 { return false, 0; }
        if is_ref(syms[s].ty) {
            if !ce_valid(a, 8) { return false, 0; }
            return true, ce_ld(a, 8);
        }
        return true, a;
    }
    if k == N_UNARY && nd.op as i64 == U_DEREF {
        let p = ce_rv(nd.a);
        if p.k != CE_PTR as! u8 || p.i == 0 { return false, 0; }
        return true, p.i;
    }
    if k == N_UNARY && nd.op as i64 == U_EXTENSION { return ce_lv(nd.a); }
    if k == N_UNARY && (nd.op as i64 == U_PREINC || nd.op as i64 == U_PREDEC) {
        let v = ce_rv(e);
        if v.k == CE_FAIL as! u8 { return false, 0; }
        return ce_lv(nd.a);
    }
    if k == N_ASSIGN {
        let v = ce_rv(e);
        if v.k == CE_FAIL as! u8 { return false, 0; }
        return ce_lv(nd.a);
    }
    if k == N_MEMBER {
        var base: i64 = 0;
        if nd.op == 1 {
            let p = ce_rv(nd.a);
            if p.k != CE_PTR as! u8 || p.i == 0 { return false, 0; }
            base = p.i;
        } else {
            let ok, b = ce_lv(nd.a);
            if !ok { return false, 0; }
            base = b;
        }
        let fi = nd.b as i64;
        if fi < 0 || fi >= fields.len || fields[fi].width >= 0 { return false, 0; }
        return true, base + fields[fi].offset;
    }
    if k == N_INDEX {
        let p = ce_rv(nd.a);
        let i = ce_rv(nd.b);
        if p.k != CE_PTR as! u8 || i.k != CE_INT as! u8 || p.i == 0 { return false, 0; }
        let el = type_size(nodes[e].ty);
        if el <= 0 { return false, 0; }
        return true, p.i + i.i * el;
    }
    if k == N_STRING {
        let a = ce_string(e);
        return a > 0, a;
    }
    if k == N_COND {
        let c = ce_rv(nd.a);
        if c.k != CE_INT as! u8 { return false, 0; }
        return ce_lv(if c.i != 0 { nd.b } else { nd.c });
    }
    if k == N_BINARY && nd.op as i64 == B_COMMA {
        let l = ce_rv(nd.a);
        if l.k == CE_FAIL as! u8 { return false, 0; }
        return ce_lv(nd.b);
    }
    if (k == N_ICAST || k == N_CAST) && (nd.op as i64 == CK_NOOP || nd.op as i64 == CK_DERIVED2BASE) {
        let ok, a = ce_lv(nd.a);
        if !ok { return false, 0; }
        if nd.op as i64 == CK_DERIVED2BASE { return true, a + nd.v; }
        return true, a;
    }
    if k == N_CXX && nd.op == 7 && nd.a != 0 {
        // a call returning a reference
        let f = nd.a as i64;
        let rt = types[syms[f].ty >> 4].base;
        if !is_ref(rt) { return ce_lv_temp(e); }
        let v = ce_call_node(e);
        if v.k != CE_PTR as! u8 || v.i == 0 { return false, 0; }
        return true, v.i;
    }
    if k == N_THIS { return false, 0; }
    // a prvalue of class or array type: materialized
    return ce_lv_temp(e);
}

// A prvalue materialized as a temporary object: its address.
recursive fn ce_lv_temp(e: u32) -> bool, i64 {
    let t = unqual(nodes[e].ty);
    if is_void(t) || is_opaque(t) || is_func(t) { return false, 0; }
    let a = ce_alloc(type_size(t), type_align(t), false);
    if a < 0 { return false, 0; }
    if !ce_init(a, t, e) { return false, 0; }
    return true, a;
}

// A string literal's array (in the global memory).
fn ce_string(e: u32) -> i64 {
    let si = nodes[e].a as i64;
    let g = ce_strs.get(si as u64);
    if g { return g as i64; }
    let sl = strs[si];
    let t = nodes[e].ty;
    let a = ce_alloc(sl.len as i64, 8, true);
    for i in sl.len as i64 { ce_st(a + i, 1, strbytes[sl.start as i64 + i] as i64); }
    ce_strs.insert(si as u64, a as u64);
    return a;
}

// The object of variable s: a local of the evaluation, or a constexpr /
// const variable initialized once (0: none).
recursive fn ce_var_addr(s: i64) -> i64 {
    var i = ce_locals.len - 2;
    while i >= ce_frame {
        if ce_locals[i] == s { return ce_locals[i + 1]; }
        i -= 2;
    }
    let g = ce_gvars.get(s as u64);
    if g { return (g - 1) as i64; }
    // a variable usable in constant expressions: constexpr, or a const
    // non-volatile integral / enumeration one, with its initializer
    let t = syms[s].ty;
    let q = quals(nonref(t));
    let cx = cxs[s].flags & CF_CONSTEXPR != 0;
    if !cx && !(q & Q_CONST != 0 && q & Q_VOLATILE == 0 && (is_integer(t) || kind_of(t) == TY_ENUM || kind_of(t) == TY_BOOL)) &&
       !(is_ref(t) && cx) {
        return 0;
    }
    var init: u32 = 0;
    let ig = ce_var_init.get(s as u64);
    if ig { init = ig; }
    if init == 0 { return 0; }
    if ce_gbusy.contains(s as u64) { return 0; }
    ce_gbusy.insert(s as u64, 1);
    let st = nonref(t);
    let sz = if is_ref(t) { 8 } else { type_size(st) };
    let al = if is_ref(t) { 8 } else { type_align(st) };
    let a = ce_alloc(sz, al, true);
    // the initializer's temporaries outlive it: evaluated in the global memory? (locals are fine:
    // only scalar and class values are copied in)
    let sf = ce_frame;
    let sl = ce_locals.len;
    ce_frame = ce_locals.len;
    let sth = ce_this;
    ce_this = 0;
    var ok = false;
    if is_ref(t) {
        let lok, la = ce_lv(init);
        if lok && la >= CE_G { ce_st(a, 8, la); ok = true; }
    } else {
        ok = ce_init(a, st, init);
    }
    ce_this = sth;
    ce_locals.resize(sl);
    ce_frame = sf;
    ce_gbusy.remove(s as u64);
    if !ok { return 0; }
    ce_gvars.insert(s as u64, (a + 1) as u64);
    return a;
}

// ---------------------------------------------------------------------------
// Rvalues.

recursive fn ce_rv(e: u32) -> CeV {
    ce_steps++;
    if ce_steps > 2000000 { return ce_fail(); }
    let nd = nodes[e];
    let k = nd.kind as i64;
    let t = nd.ty;
    if k == N_INT { return ce_int(trunc_to(nd.v, t), unqual(t)); }
    if k == N_FLOAT { return ce_flt(reinterpret_f64(nd.v), unqual(t)); }
    if k == N_SIZEOF || k == N_OFFSETOF {
        if nd.v < 0 { return ce_bad(e); }
        return ce_int(nd.v, unqual(t));
    }
    if k == N_DECLREF {
        let s = nd.a as i64;
        let sk = syms[s].kind as i64;
        if sk == SK_ENUMC { return ce_int(syms[s].v, unqual(t)); }
        if sk == SK_FUNC { return ce_ptr(CE_FN + s, mk_ptr(syms[s].ty)); }
        let ok, a = ce_lv(e);
        if !ok { return ce_bad(e); }
        return ce_load(a, t);
    }
    if k == N_ICAST || k == N_CAST { return ce_cast(e); }
    if k == N_UNARY { return ce_unary(e); }
    if k == N_BINARY { return ce_binary(e); }
    if k == N_ASSIGN { return ce_assign(e); }
    if k == N_COND {
        let c = ce_rv(nd.a);
        if nd.b == 0 {
            if c.k == CE_FAIL as! u8 { return c; }
            if ce_truth(c) != 0 { return c; }
            return ce_rv(nd.c);
        }
        let b = ce_truth(c);
        if b < 0 { return ce_bad(e); }
        return ce_rv(if b != 0 { nd.b } else { nd.c });
    }
    if k == N_MEMBER || k == N_INDEX {
        let ok, a = ce_lv(e);
        if !ok { return ce_bad(e); }
        return ce_load(a, t);
    }
    if k == N_CALL { return ce_ccall(e); }
    if k == N_CXX && nd.op == 7 && nd.a != 0 {
        let f = nd.a as i64;
        let rt = types[syms[f].ty >> 4].base;
        if is_ref(rt) {
            let v = ce_call_node(e);
            if v.k != CE_PTR as! u8 || v.i == 0 { return ce_bad(e); }
            return ce_load(v.i, nonref(rt));
        }
        if is_record(rt) {
            let ok, a = ce_lv_temp(e);
            if !ok { return ce_bad(e); }
            return ce_obj(a, unqual(rt));
        }
        return ce_call_node(e);
    }
    if k == N_THIS {
        if ce_this == 0 { return ce_bad(e); }
        return ce_ptr(ce_this, t);
    }
    if k == N_CTOR || k == N_INITLIST || k == N_INITBRACE || k == N_COMPLIT || k == N_ZEROINIT {
        if is_record(t) || is_array(t) {
            let ok, a = ce_lv_temp(e);
            if !ok { return ce_bad(e); }
            return ce_obj(a, unqual(t));
        }
        if k == N_ZEROINIT { return ce_conv(ce_int(0, t_int), t); }
        if (k == N_INITBRACE || k == N_INITLIST) && nd.c == 1 { return ce_conv(ce_rv(nlist[nd.v]), t); }
        if (k == N_INITBRACE || k == N_INITLIST) && nd.c == 0 { return ce_conv(ce_int(0, t_int), t); }
        if k == N_CTOR && nd.c == 0 { return ce_conv(ce_int(0, t_int), t); }
        if k == N_CTOR && nd.c == 1 { return ce_conv(ce_rv(nlist[nd.v]), t); }
        return ce_bad(e);
    }
    if k == N_STRING {
        let a = ce_string(e);
        if a <= 0 { return ce_bad(e); }
        return ce_obj(a, unqual(t));
    }
    if k == N_BUILTIN { return ce_builtin(e); }
    if k == N_TEMP { return ce_rv(nd.a); }
    return ce_bad(e);
}

// 1 / 0 for a scalar's truth value, -1 unknown.
fn ce_truth(v: CeV) -> i64 {
    if v.k == CE_INT as! u8 { return if v.i != 0 { 1 } else { 0 }; }
    if v.k == CE_FLT as! u8 { return if v.f != 0.0 { 1 } else { 0 }; }
    if v.k == CE_PTR as! u8 { return if v.i != 0 { 1 } else { 0 }; }
    return -1;
}

recursive fn ce_cast(e: u32) -> CeV {
    let nd = nodes[e];
    let op = nd.op as i64;
    let t = nd.ty;
    if op == CK_LVAL2RVAL {
        let ok, a = ce_lv(nd.a);
        if !ok { return ce_bad(e); }
        return ce_load(a, t);
    }
    if op == CK_ARRAY2PTR {
        let ok, a = ce_lv(nd.a);
        if !ok { return ce_bad(e); }
        return ce_ptr(a, t);
    }
    if op == CK_FUNC2PTR {
        let x = nodes[nd.a];
        if x.kind as i64 == N_DECLREF && syms[x.a].kind as i64 == SK_FUNC { return ce_ptr(CE_FN + x.a as i64, t); }
        return ce_bad(e);
    }
    if op == CK_NULL2PTR { return ce_ptr(0, t); }
    if op == CK_TOVOID {
        let v = ce_rv(nd.a);
        if v.k == CE_FAIL as! u8 { return v; }
        return ce_void();
    }
    if op == CK_DERIVED2BASE {
        if is_pointer(t) {
            let p = ce_rv(nd.a);
            if p.k != CE_PTR as! u8 { return ce_bad(e); }
            if p.i == 0 { return ce_ptr(0, t); }
            return ce_ptr(p.i + nd.v, t);
        }
        let ok, a = ce_lv(e);
        if !ok { return ce_bad(e); }
        return ce_load(a, t);
    }
    if op == CK_NOOP {
        if is_record(t) || is_array(t) {
            let ok, a = ce_lv(nd.a);
            if !ok { return ce_bad(e); }
            return ce_obj(a, unqual(t));
        }
        if is_lvalue(nd.a) && (is_integer(t) || is_pointer(t) || is_real_float(t) || kind_of(t) == TY_BOOL || kind_of(t) == TY_ENUM) &&
           nodes[nd.a].kind as i64 != N_ICAST && nodes[nd.a].kind as i64 != N_CAST {
            let v = ce_rv(nd.a);
            return ce_conv(v, t);
        }
        return ce_conv(ce_rv(nd.a), t);
    }
    if op == CK_INTEGRAL || op == CK_INT2BOOL || op == CK_INT2FLOAT || op == CK_FLOAT2INT || op == CK_FLOAT2BOOL ||
       op == CK_FLOATCAST || op == CK_PTR2BOOL {
        return ce_conv(ce_rv(nd.a), t);
    }
    if op == CK_BITCAST {
        // pointer to pointer: only to the same object type (cv) or void
        let p = ce_rv(nd.a);
        if p.k != CE_PTR as! u8 { return ce_bad(e); }
        let from = nodes[nd.a].ty;
        if is_pointer(from) && is_pointer(t) && unqual(tbase(from)) != unqual(tbase(t)) && !is_void(tbase(t)) && !is_void(tbase(from)) { return ce_bad(e); }
        return ce_ptr(p.i, t);
    }
    return ce_bad(e);
}

recursive fn ce_unary(e: u32) -> CeV {
    let nd = nodes[e];
    let op = nd.op as i64;
    let t = unqual(nd.ty);
    if op == U_ADDR {
        let x = nodes[nd.a];
        if x.kind as i64 == N_DECLREF && syms[x.a].kind as i64 == SK_FUNC { return ce_ptr(CE_FN + x.a as i64, t); }
        let ok, a = ce_lv(nd.a);
        if !ok { return ce_bad(e); }
        return ce_ptr(a, t);
    }
    if op == U_DEREF {
        let ok, a = ce_lv(e);
        if !ok { return ce_bad(e); }
        return ce_load(a, nd.ty);
    }
    if op == U_EXTENSION || op == U_PLUS { return ce_conv(ce_rv(nd.a), t); }
    if op == U_NEG {
        let v = ce_rv(nd.a);
        if v.k == CE_INT as! u8 {
            if is_signed(t) && type_size(t) == 8 && v.i == -9223372036854775807 - 1 { return ce_bad(e); }
            let r = 0 - v.i;
            if is_signed(t) && trunc_to(r, t) != r { return ce_bad(e); }
            return ce_int(trunc_to(r, t), t);
        }
        if v.k == CE_FLT as! u8 { return ce_flt(0.0 - v.f, t); }
        return ce_bad(e);
    }
    if op == U_NOT {
        let v = ce_rv(nd.a);
        let b = ce_truth(v);
        if b < 0 { return ce_bad(e); }
        return ce_int(if b != 0 { 0 } else { 1 }, t);
    }
    if op == U_BITNOT {
        let v = ce_rv(nd.a);
        if v.k != CE_INT as! u8 { return ce_bad(e); }
        return ce_int(trunc_to(~v.i, t), t);
    }
    if op == U_PREINC || op == U_PREDEC || op == U_POSTINC || op == U_POSTDEC {
        let ok, a = ce_lv(nd.a);
        if !ok { return ce_bad(e); }
        let ot = nodes[nd.a].ty;
        let old = ce_load(a, ot);
        if old.k == CE_FAIL as! u8 { return ce_bad(e); }
        let inc = op == U_PREINC || op == U_POSTINC;
        var nv = old;
        if old.k == CE_INT as! u8 {
            let r = if inc { old.i + 1 } else { old.i - 1 };
            if is_signed(ot) && trunc_to(r, ot) != r && kind_of(ot) != TY_BOOL { return ce_bad(e); }
            nv = ce_int(trunc_to(r, ot), unqual(ot));
        } else if old.k == CE_FLT as! u8 {
            nv = ce_flt(if inc { old.f + 1.0 } else { old.f - 1.0 }, unqual(ot));
        } else if old.k == CE_PTR as! u8 {
            let el = type_size(tbase(ot));
            if el <= 0 || old.i == 0 { return ce_bad(e); }
            nv = ce_ptr(if inc { old.i + el } else { old.i - el }, unqual(ot));
        } else { return ce_bad(e); }
        if !ce_store(a, ot, nv) { return ce_bad(e); }
        return if op == U_PREINC || op == U_PREDEC { nv } else { old };
    }
    return ce_bad(e);
}

fn ce_arith_int(op: i64, a: i64, b: i64, t: u32) -> bool, i64 {
    let sg = is_signed(t);
    let sz = type_size(t);
    var r: i64 = 0;
    if op == B_ADD { r = a + b; }
    else if op == B_SUB { r = a - b; }
    else if op == B_MUL {
        if sg && sz == 8 && a != 0 && b != 0 {
            // overflow check for 64-bit signed
            let p = a * b;
            if p / b != a || (a == -1 && b == -9223372036854775807 - 1) || (b == -1 && a == -9223372036854775807 - 1) { return false, 0; }
            return true, p;
        }
        r = a * b;
    } else if op == B_DIV || op == B_REM {
        if b == 0 { return false, 0; }
        if sg {
            if sz == 8 && a == -9223372036854775807 - 1 && b == -1 { return false, 0; }
            r = if op == B_DIV { a / b } else { a % b };
        } else {
            let ua = if sz >= 8 { a as! u64 } else { (a & ((1 << (sz * 8)) - 1)) as! u64 };
            let ub = if sz >= 8 { b as! u64 } else { (b & ((1 << (sz * 8)) - 1)) as! u64 };
            r = (if op == B_DIV { ua / ub } else { ua % ub }) as! i64;
        }
    } else if op == B_SHL || op == B_SHR {
        if b < 0 || b >= sz * 8 { return false, 0; }
        if op == B_SHL {
            if sg && a < 0 && opt_cxx_std < 20 { return false, 0; }
            r = a << b;
            if sg && opt_cxx_std < 20 && sz < 8 && (r >> (sz * 8 - 1)) > 1 { return false, 0; }
        } else if sg { r = a >> b; }
        else {
            let ua = if sz >= 8 { a as! u64 } else { (a & ((1 << (sz * 8)) - 1)) as! u64 };
            r = (ua >> (b as! u64)) as! i64;
        }
    } else if op == B_AND { r = a & b; }
    else if op == B_XOR { r = a ^ b; }
    else if op == B_OR { r = a | b; }
    else { return false, 0; }
    if sg && sz < 8 && trunc_to(r, t) != r && op != B_SHL { return false, 0; }
    if sg && sz == 8 && (op == B_ADD || op == B_SUB) {
        // 64-bit signed overflow
        if op == B_ADD && ((a >= 0 && b >= 0 && r < 0) || (a < 0 && b < 0 && r >= 0)) { return false, 0; }
        if op == B_SUB && ((a >= 0 && b < 0 && r < 0) || (a < 0 && b >= 0 && r >= 0)) { return false, 0; }
    }
    return true, trunc_to(r, t);
}

fn ce_cmp_int(op: i64, a: i64, b: i64, t: u32) -> i64 {
    var lt = false;
    var eq = a == b;
    if is_signed(t) || type_size(t) < 8 { lt = a < b; } else { lt = (a as! u64) < (b as! u64); }
    if op == B_LT { return if lt { 1 } else { 0 }; }
    if op == B_GT { return if !lt && !eq { 1 } else { 0 }; }
    if op == B_LE { return if lt || eq { 1 } else { 0 }; }
    if op == B_GE { return if !lt { 1 } else { 0 }; }
    if op == B_EQ { return if eq { 1 } else { 0 }; }
    return if eq { 0 } else { 1 };
}

recursive fn ce_binary(e: u32) -> CeV {
    let nd = nodes[e];
    let op = nd.op as i64;
    let t = unqual(nd.ty);
    if op == B_LAND || op == B_LOR {
        let l = ce_truth(ce_rv(nd.a));
        if l < 0 { return ce_bad(e); }
        if op == B_LAND && l == 0 { return ce_int(0, t); }
        if op == B_LOR && l == 1 { return ce_int(1, t); }
        let r = ce_truth(ce_rv(nd.b));
        if r < 0 { return ce_bad(e); }
        return ce_int(r, t);
    }
    if op == B_COMMA {
        let l = ce_rv(nd.a);
        if l.k == CE_FAIL as! u8 { return l; }
        return ce_rv(nd.b);
    }
    let l = ce_rv(nd.a);
    let r = ce_rv(nd.b);
    if l.k == CE_FAIL as! u8 || r.k == CE_FAIL as! u8 { return ce_bad(e); }
    if op == B_PTRADD || op == B_PTRSUB {
        if l.k != CE_PTR as! u8 || r.k != CE_INT as! u8 { return ce_bad(e); }
        let el = type_size(tbase(t));
        if el <= 0 { return ce_bad(e); }
        if l.i == 0 { if r.i == 0 { return ce_ptr(0, t); } return ce_bad(e); }
        return ce_ptr(if op == B_PTRADD { l.i + r.i * el } else { l.i - r.i * el }, t);
    }
    if op == B_PTRDIFF {
        if l.k != CE_PTR as! u8 || r.k != CE_PTR as! u8 { return ce_bad(e); }
        let el = type_size(tbase(nodes[nd.a].ty));
        if el <= 0 { return ce_bad(e); }
        if (l.i >= CE_G) != (r.i >= CE_G) { return ce_bad(e); }
        return ce_int((l.i - r.i) / el, t);
    }
    if op >= B_LT && op <= B_NE {
        if l.k == CE_PTR as! u8 && r.k == CE_PTR as! u8 {
            if op != B_EQ && op != B_NE && ((l.i >= CE_G) != (r.i >= CE_G) || l.i == 0 || r.i == 0) { return ce_bad(e); }
            return ce_int(ce_cmp_int(op, l.i, r.i, t_ulong), t);
        }
        if l.k == CE_FLT as! u8 || r.k == CE_FLT as! u8 {
            let a = ce_conv(l, t_double);
            let b = ce_conv(r, t_double);
            if a.k != CE_FLT as! u8 || b.k != CE_FLT as! u8 { return ce_bad(e); }
            let x = a.f;
            let y = b.f;
            let res = if op == B_LT { x < y } else if op == B_GT { x > y } else if op == B_LE { x <= y } else if op == B_GE { x >= y } else if op == B_EQ { x == y } else { x != y };
            return ce_int(if res { 1 } else { 0 }, t);
        }
        if l.k == CE_INT as! u8 && r.k == CE_INT as! u8 {
            let ot = unqual(nodes[nd.a].ty);
            return ce_int(ce_cmp_int(op, l.i, r.i, if is_integer(ot) || kind_of(ot) == TY_ENUM { ot } else { t_long }), t);
        }
        return ce_bad(e);
    }
    if l.k == CE_FLT as! u8 || r.k == CE_FLT as! u8 {
        let a = ce_conv(l, t);
        let b = ce_conv(r, t);
        if a.k != CE_FLT as! u8 || b.k != CE_FLT as! u8 { return ce_bad(e); }
        var f: f64 = 0.0;
        if op == B_ADD { f = a.f + b.f; }
        else if op == B_SUB { f = a.f - b.f; }
        else if op == B_MUL { f = a.f * b.f; }
        else if op == B_DIV { if b.f == 0.0 { return ce_bad(e); } f = a.f / b.f; }
        else { return ce_bad(e); }
        if kind_of(t) == TY_FLOAT { f = round_f32(f); }
        return ce_flt(f, t);
    }
    if l.k == CE_INT as! u8 && r.k == CE_INT as! u8 {
        let ok, v = ce_arith_int(op, l.i, r.i, if op == B_SHL || op == B_SHR { t } else { t });
        if !ok { return ce_bad(e); }
        return ce_int(v, t);
    }
    return ce_bad(e);
}

recursive fn ce_assign(e: u32) -> CeV {
    let nd = nodes[e];
    let ok, a = ce_lv(nd.a);
    if !ok { return ce_bad(e); }
    let lt = nodes[nd.a].ty;
    if nd.op == 0 {
        if is_record(lt) {
            let v = ce_rv(nd.b);
            if v.k != CE_OBJ as! u8 { return ce_bad(e); }
            if !ce_store(a, lt, v) { return ce_bad(e); }
            return ce_obj(a, unqual(lt));
        }
        let v = ce_conv(ce_rv(nd.b), lt);
        if v.k == CE_FAIL as! u8 || !ce_store(a, lt, v) { return ce_bad(e); }
        return v;
    }
    // compound: in the computation type (c), converted back
    let old = ce_load(a, lt);
    let r = ce_rv(nd.b);
    if old.k == CE_FAIL as! u8 || r.k == CE_FAIL as! u8 { return ce_bad(e); }
    let op = nd.op as i64;
    var nv = ce_fail();
    if old.k == CE_PTR as! u8 && (op == B_ADD || op == B_SUB || op == B_PTRADD || op == B_PTRSUB) {
        if r.k != CE_INT as! u8 { return ce_bad(e); }
        let el = type_size(tbase(lt));
        if el <= 0 || old.i == 0 { return ce_bad(e); }
        nv = ce_ptr(if op == B_ADD || op == B_PTRADD { old.i + r.i * el } else { old.i - r.i * el }, unqual(lt));
    } else {
        let ct = if nd.c != 0 { nd.c as u32 } else { unqual(lt) };
        let x = ce_conv(old, ct);
        let y = ce_conv(r, if op == B_SHL || op == B_SHR { r.ty } else { ct });
        if x.k == CE_FLT as! u8 {
            let b = ce_conv(y, ct);
            var f: f64 = 0.0;
            if op == B_ADD { f = x.f + b.f; } else if op == B_SUB { f = x.f - b.f; } else if op == B_MUL { f = x.f * b.f; }
            else if op == B_DIV { if b.f == 0.0 { return ce_bad(e); } f = x.f / b.f; } else { return ce_bad(e); }
            nv = ce_conv(ce_flt(f, ct), lt);
        } else if x.k == CE_INT as! u8 && y.k == CE_INT as! u8 {
            let ok2, v = ce_arith_int(op, x.i, y.i, ct);
            if !ok2 { return ce_bad(e); }
            nv = ce_conv(ce_int(v, ct), lt);
        } else { return ce_bad(e); }
    }
    if nv.k == CE_FAIL as! u8 || !ce_store(a, lt, nv) { return ce_bad(e); }
    return nv;
}

// ---------------------------------------------------------------------------
// Initialization of the object of type t at a from e.

recursive fn ce_init(a: i64, t0: u32, e: u32) -> bool {
    let t = unqual(t0);
    let nd = nodes[e];
    let k = nd.kind as i64;
    ce_steps++;
    if is_array(t) {
        let el = tbase(t);
        let n = types[t >> 4].n;
        let es = type_size(el);
        if es <= 0 || n < 0 { return false; }
        if k == N_STRING {
            let s = ce_string(e);
            let sl = strs[nd.a];
            let m = if (sl.len as i64) < n * es { sl.len as i64 } else { n * es };
            ce_zero(a, n * es);
            ce_copy(a, s, m);
            return true;
        }
        if k == N_INITLIST || k == N_INITBRACE {
            ce_zero(a, n * es);
            let c = nd.c as i64;
            if c > n { return false; }
            for i in c {
                if !ce_init(a + i * es, el, nlist[nd.v + i]) { return false; }
            }
            if nd.b != 0 && c < n {
                for i in c..n { if !ce_init(a + i * es, el, nd.b) { return false; } }
            } else if c < n && is_record(el) {
                for i in c..n { if !ce_value_init(a + i * es, el) { return false; } }
            }
            return true;
        }
        if k == N_ZEROINIT { ce_zero(a, n * es); return true; }
        let v = ce_rv(e);
        if v.k != CE_OBJ as! u8 { return false; }
        ce_copy(a, v.i, n * es);
        return true;
    }
    if is_record(t) {
        need_complete(t);
        if is_opaque(t) || records[rec_of(t)].flags & RF_COMPLETE == 0 { return false; }
        if k == N_ZEROINIT { ce_zero(a, type_size(t)); return ce_value_init(a, t); }
        if k == N_INITLIST || k == N_INITBRACE {
            if ce_has_user_ctor(t) || (k == N_INITBRACE && nd.c == 1 && is_record(nodes[nlist[nd.v]].ty) && unqual(nodes[nlist[nd.v]].ty) == t) {
                return ce_construct(a, t, nd.v as i64, nd.c as i64, e);
            }
            return ce_agg_init(a, t, nd.v as i64, nd.c as i64);
        }
        if k == N_CTOR {
            if nd.op == 2 { return ce_agg_init(a, t, nd.v as i64, nd.c as i64); }
            return ce_construct(a, t, nd.v as i64, nd.c as i64, e);
        }
        if k == N_CXX && nd.op == 7 && nd.a != 0 {
            let f = nd.a as i64;
            let rt = types[syms[f].ty >> 4].base;
            if is_record(rt) && !is_ref(rt) {
                let sv = ce_ret_addr;
                ce_ret_addr = a;
                let v = ce_call_node(e);
                ce_ret_addr = sv;
                return v.k != CE_FAIL as! u8;
            }
        }
        let v = ce_rv(e);
        if v.k != CE_OBJ as! u8 { return false; }
        if unqual(v.ty) != t {
            // a derived class object: its base subobject
            let off = base_offset(unqual(v.ty), t);
            if off < 0 { return false; }
            ce_copy(a, v.i + off, type_size(t));
            return true;
        }
        if ce_has_user_copy(t) { return false; }
        ce_copy(a, v.i, type_size(t));
        return true;
    }
    if is_ref(t0) {
        let ok, la = ce_lv(e);
        if !ok { return false; }
        ce_st(a, 8, la);
        return true;
    }
    var x = e;
    if (k == N_INITBRACE || k == N_INITLIST) && nd.c == 1 { x = nlist[nd.v]; }
    else if (k == N_INITBRACE || k == N_INITLIST) && nd.c == 0 { return ce_store(a, t, ce_conv(ce_int(0, t_int), t)); }
    let v = ce_conv(ce_rv(x), t);
    if v.k == CE_FAIL as! u8 { return false; }
    return ce_store(a, t, v);
}

// T{} / T() of a class: zero, then a default constructor if it has a user one.
recursive fn ce_value_init(a: i64, t: u32) -> bool {
    ce_zero(a, type_size(t));
    if ce_has_user_ctor(t) { return ce_construct(a, t, 0, 0, 0); }
    return ce_agg_default(a, t);
}

// Default member initializers and default-initialized members of an aggregate.
recursive fn ce_agg_default(a: i64, t: u32) -> bool {
    let r = rec_of(t);
    let rec = records[r];
    let sc = crecs[r].scope as i64;
    for i in rec.first..rec.first + rec.count {
        let f = fields[i];
        if f.width >= 0 { continue; }
        let ft = f.ty;
        if f.name != 0 {
            let ns = field_nsdmi_ce(sc, f.name);
            if ns != 0 {
                let init = ce_nsdmi(ns);
                if init == 0 { return false; }
                if !ce_init(a + f.offset, ft, init) { return false; }
                continue;
            }
        }
        if is_record(ft) && !ce_value_init(a + f.offset, ft) { return false; }
    }
    return true;
}

// Aggregate initialization from the elements nlist[v..v+c).
recursive fn ce_agg_init(a: i64, t: u32, v: i64, c: i64) -> bool {
    let r = rec_of(t);
    let rec = records[r];
    let cr = crecs[r];
    ce_zero(a, type_size(t));
    var j: i64 = 0;
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if b.flags & BF_VIRTUAL != 0 { return false; }
        if j < c { if !ce_init(a + b.offset, b.ty, nlist[v + j]) { return false; } j++; }
        else if !ce_value_init(a + b.offset, b.ty) { return false; }
    }
    let sc = cr.scope as i64;
    for i in rec.first..rec.first + rec.count {
        let f = fields[i];
        if f.width >= 0 { if j < c { return false; } continue; }
        if f.name == 0 && is_record(f.ty) && records[rec_of(f.ty)].name == 0 {
            // an anonymous struct/union member: not modelled
            if j < c { return false; }
            continue;
        }
        if j < c {
            if !ce_init(a + f.offset, f.ty, nlist[v + j]) { return false; }
            j++;
            if kind_of(t) == TY_UNION { return j == c; }
            continue;
        }
        if kind_of(t) == TY_UNION { break; }
        let ns = if f.name != 0 { field_nsdmi_ce(sc, f.name) } else { 0 };
        if ns != 0 {
            let init = ce_nsdmi(ns);
            if init == 0 { return false; }
            if !ce_init(a + f.offset, f.ty, init) { return false; }
        } else if is_record(f.ty) {
            if !ce_value_init(a + f.offset, f.ty) { return false; }
        } else if is_array(f.ty) && is_record(base_elem_t(f.ty)) {
            return false;
        }
    }
    return j == c;
}

fn field_nsdmi_ce(sc: i64, name: u32) -> i64 {
    var s = scope_find(sc, name);
    while s >= 0 {
        if syms[s].kind as i64 == SK_FIELD && cxs[s].body != 0 { return s; }
        s = cxs[s].nnext as i64;
    }
    return 0;
}

// A default member initializer parsed for the evaluation (its tokens at
// cxs[s].body), cached.
var ce_nsdmis = dictionary<u64, u32> {};
recursive fn ce_nsdmi(s: i64) -> u32 {
    let g = ce_nsdmis.get(s as u64);
    if g { return if g == 4294967295 { 0 } else { g }; }
    ce_nsdmis.insert(s as u64, 4294967295);
    let n = ce_parse_nsdmi(s);
    if n != 0 { ce_nsdmis.insert(s as u64, n); }
    return n;
}

fn ce_has_user_ctor(t: u32) -> bool {
    let sc = type_scope(t);
    if sc < 0 { return false; }
    var s = scope_find(sc, id_ctor);
    while s >= 0 {
        let f = resolve(s);
        if f >= 0 && (syms[f].kind as i64 == SK_FUNC || syms[f].kind as i64 == SK_TEMPLATE) && cxs[f].flags & CF_IMPLICIT == 0 &&
           cxs[f].flags & CF_DEFAULTED == 0 { return true; }
        s = cxs[s].nnext as i64;
    }
    return false;
}

fn ce_has_user_copy(t: u32) -> bool {
    let sc = type_scope(t);
    if sc < 0 { return false; }
    let cls = unqual(t);
    var s = scope_find(sc, id_ctor);
    while s >= 0 {
        let f = resolve(s);
        if f >= 0 && syms[f].kind as i64 == SK_FUNC && cxs[f].flags & (CF_IMPLICIT | CF_DEFAULTED) == 0 {
            let ft = types[syms[f].ty >> 4];
            if ft.n >= 1 && is_ref(tparams[ft.extra]) && unqual(tbase(tparams[ft.extra])) == cls { return true; }
        }
        s = cxs[s].nnext as i64;
    }
    return false;
}

// T(args) / T{args} with a constructor: overload resolution among T's
// constructors, then the call.
recursive fn ce_construct(a: i64, t: u32, v: i64, c: i64, e: u32) -> bool {
    let sc = type_scope(t);
    if sc < 0 { return false; }
    let s = scope_find(sc, id_ctor);
    if s < 0 {
        if c == 0 { return ce_agg_default(a, t); }
        return false;
    }
    let mark = nscratch.len;
    for i in c { nscratch.push(nlist[v + i]); }
    cand_obj = 0;
    let f = best_candidate(s, mark, true);
    nscratch.resize(mark);
    if f < 0 {
        // the implicit copy / move constructor
        if c == 1 {
            let x = ce_rv(nlist[v]);
            if x.k != CE_OBJ as! u8 { return false; }
            if unqual(x.ty) != unqual(t) {
                let off = base_offset(unqual(x.ty), unqual(t));
                if off < 0 { return false; }
                ce_copy(a, x.i + off, type_size(t));
                return true;
            }
            ce_copy(a, x.i, type_size(t));
            return true;
        }
        if c == 0 { return ce_agg_default(a, t); }
        return false;
    }
    let r = ce_call(f, a, v, c, 0);
    return r.k != CE_FAIL as! u8;
}

// ---------------------------------------------------------------------------
// Calls.

// An N_CXX op 7 call: a = the function, b = the object (0 none), v/c = the
// arguments as written.
recursive fn ce_call_node(e: u32) -> CeV {
    let nd = nodes[e];
    let f = nd.a as i64;
    var obj: i64 = 0;
    let member = cxs[f].flags & CF_MEMBER != 0 && cxs[f].flags & CF_STATIC == 0 && cxs[f].flags & CF_CTOR == 0;
    var v = nd.v;
    var c = nd.c as i64;
    if member {
        let ob = nd.b;
        if ob == 0 {
            if ce_this == 0 { return ce_bad(e); }
            obj = ce_this;
        } else {
            let ok, oa = ce_obj_addr(ob);
            if !ok { return ce_bad(e); }
            obj = oa;
        }
    }
    return ce_call(f, obj, v, c, e);
}

// The object an object expression designates (a pointer for ->).
recursive fn ce_obj_addr(ob: u32) -> bool, i64 {
    if is_pointer(nodes[ob].ty) {
        let p = ce_rv(ob);
        if p.k != CE_PTR as! u8 || p.i == 0 { return false, 0; }
        return true, p.i;
    }
    return ce_lv(ob);
}

// A C call node (the callee a function designator, arguments converted).
recursive fn ce_ccall(e: u32) -> CeV {
    let nd = nodes[e];
    var c = nodes[nd.a];
    while (c.kind as i64 == N_ICAST || c.kind as i64 == N_CAST) && (c.op as i64 == CK_FUNC2PTR || c.op as i64 == CK_NOOP) { c = nodes[c.a]; }
    var f: i64 = -1;
    if c.kind as i64 == N_DECLREF && syms[c.a].kind as i64 == SK_FUNC { f = c.a as i64; }
    else {
        let p = ce_rv(nd.a);
        if p.k == CE_PTR as! u8 && p.i >= CE_FN { f = p.i - CE_FN; }
    }
    if f < 0 { return ce_bad(e); }
    if syms[f].kind as i64 == SK_BUILTIN { return ce_builtin_call(f, nd.v, nd.c as i64, e); }
    return ce_call(f, 0, nd.v, nd.c as i64, e);
}

// Calls f (obj: its object for a member function, or the object a
// constructor initializes) with the arguments nlist[v..v+c).
recursive fn ce_call(f: i64, obj: i64, v: i64, c: i64, e: u32) -> CeV {
    if f < 0 || f >= cxs.len { return ce_fail(); }
    let fl = cxs[f].flags;
    if fl & CF_CONSTEXPR == 0 && fl & CF_IMPLICIT == 0 && !(fl & CF_DEFAULTED != 0) {
        if ce_debug() { write_stderr(str("ce: call of non-constexpr ", ident_text(syms[f].name as i64), "\n")); }
        return ce_fail();
    }
    if fl & CF_DELETED != 0 { return ce_fail(); }
    if ce_depth > 512 { return ce_fail(); }
    let ft = types[syms[f].ty >> 4];
    let is_ctor = fl & CF_CTOR != 0;
    let def = ce_body(f);
    if def == 0 {
        if is_ctor && (fl & (CF_IMPLICIT | CF_DEFAULTED)) != 0 { return ce_default_ctor(f, obj, v, c); }
        if ce_debug() { write_stderr(str("ce: no body for ", ident_text(syms[f].name as i64), "\n")); }
        return ce_fail();
    }
    let pst = nodes[def].v;
    let np = nodes[def].c as i64;
    // the arguments, in the caller's frame
    let lm = ce_locals.len;
    var i: i64 = 0;
    while i < np {
        let p = nlist[pst + i] as i64;
        let pt = syms[p].ty;
        let sz = if is_ref(pt) { 8 } else { type_size(nonref(pt)) };
        let al = if is_ref(pt) { 8 } else { type_align(nonref(pt)) };
        let pa = ce_alloc(sz, al, false);
        if pa < 0 { ce_locals.resize(lm); return ce_fail(); }
        var ok = false;
        if i < c { ok = ce_init(pa, pt, nlist[v + i]); }
        else if cxs[p].body != 0 {
            let d = ce_default_arg(f, p);
            ok = d != 0 && ce_init(pa, pt, d);
        }
        if !ok { ce_locals.resize(lm); return ce_fail(); }
        ce_locals.push(p);
        ce_locals.push(pa);
        i++;
    }
    let sf = ce_frame;
    let sth = ce_this;
    let srv = ce_rv_val;
    ce_frame = lm;
    ce_this = obj;
    ce_depth++;
    ce_fn_stack.push(f);
    var ok = true;
    if is_ctor { ok = ce_ctor_inits(f, obj); }
    ce_rv_val = ce_void();
    var st: i64 = 0;
    if ok { st = ce_exec(nodes[def].b); }
    ce_depth--;
    ce_fn_stack.pop();
    let res = ce_rv_val;
    ce_rv_val = srv;
    ce_this = sth;
    ce_frame = sf;
    ce_locals.resize(lm);
    if !ok || st == CS_FAIL { return ce_fail(); }
    if is_ctor || is_void(ft.base) { return ce_void(); }
    if st != CS_RETURN { return ce_fail(); }
    return res;
}

// A defaulted / implicit default constructor: the members' initializers.
recursive fn ce_default_ctor(f: i64, obj: i64, v: i64, c: i64) -> CeV {
    let t = scope_class_type(cxs[f].dscope as i64);
    if t == 0 { return ce_fail(); }
    if c == 0 { if ce_agg_default(obj, t) { return ce_void(); } return ce_fail(); }
    if c == 1 {
        let x = ce_rv(nlist[v]);
        if x.k != CE_OBJ as! u8 { return ce_fail(); }
        ce_copy(obj, x.i, type_size(t));
        return ce_void();
    }
    return ce_fail();
}

// The base and member initializers of constructor f for the object obj.
recursive fn ce_ctor_inits(f: i64, obj: i64) -> bool {
    let t = scope_class_type(cxs[f].dscope as i64);
    if t == 0 { return false; }
    let r = rec_of(t);
    let cr = crecs[r];
    let inits = ce_inits_of(f);
    // bases
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if b.flags & BF_VIRTUAL != 0 { return false; }
        let x = ce_find_init(inits, -1, b.ty);
        if x != 0 {
            if !ce_init_from_args(obj + b.offset, b.ty, x) { return false; }
        } else if !ce_value_init_default(obj + b.offset, b.ty) { return false; }
    }
    let rec = records[r];
    let sc = cr.scope as i64;
    for i in rec.first..rec.first + rec.count {
        let fd = fields[i];
        if fd.width >= 0 { continue; }
        var ms: i64 = -1;
        if fd.name != 0 {
            var s = scope_find(sc, fd.name);
            while s >= 0 && syms[s].kind as i64 != SK_FIELD { s = cxs[s].nnext as i64; }
            ms = s;
        }
        let x = if ms >= 0 { ce_find_init(inits, ms, 0) } else { 0 };
        if x != 0 {
            if !ce_init_from_args(obj + fd.offset, fd.ty, x) { return false; }
            continue;
        }
        let ns = if fd.name != 0 { field_nsdmi_ce(sc, fd.name) } else { 0 };
        if ns != 0 {
            let init = ce_nsdmi(ns);
            if init == 0 || !ce_init(obj + fd.offset, fd.ty, init) { return false; }
        } else if is_record(fd.ty) {
            if !ce_value_init_default(obj + fd.offset, fd.ty) { return false; }
        }
        // scalars without an initializer stay as they are (zero here)
    }
    return true;
}

recursive fn ce_value_init_default(a: i64, t: u32) -> bool {
    if ce_has_user_ctor(t) { return ce_construct(a, t, 0, 0, 0); }
    return ce_agg_default(a, t);
}

// The mem-initializer (an N_CXX op 1 node) for member ms or base type bt.
fn ce_find_init(inits: u32, ms: i64, bt: u32) -> u32 {
    if inits == 0 { return 0; }
    let nd = nodes[inits];
    for i in nd.c as i64 {
        let x = nlist[nd.v + i];
        let xn = nodes[x];
        if ms >= 0 && xn.a as i64 == ms { return x; }
        if bt != 0 && xn.ty != 0 && unqual(xn.ty) == unqual(bt) { return x; }
    }
    return 0;
}

// A member or base initialized from a mem-initializer's arguments.
recursive fn ce_init_from_args(a: i64, t: u32, x: u32) -> bool {
    let args = nodes[x].b;
    if args == 0 { return false; }
    let an = nodes[args];
    if is_record(t) {
        if an.op == 1 { return ce_construct(a, t, an.v as i64, an.c as i64, args); }
        if ce_has_user_ctor(t) { return ce_construct(a, t, an.v as i64, an.c as i64, args); }
        if an.c == 1 && is_record(nodes[nlist[an.v]].ty) { return ce_init(a, t, nlist[an.v]); }
        return ce_agg_init(a, t, an.v as i64, an.c as i64);
    }
    if is_array(t) { return ce_init(a, t, args); }
    if an.c == 0 { ce_zero(a, if is_ref(t) { 8 } else { type_size(t) }); return true; }
    if an.c != 1 { return false; }
    return ce_init(a, t, nlist[an.v]);
}

// ---------------------------------------------------------------------------
// Statements.

let CS_NORMAL = 0;
let CS_BREAK = 1;
let CS_CONTINUE = 2;
let CS_RETURN = 3;
let CS_FAIL = 4;

recursive fn ce_exec(s: u32) -> i64 {
    if s == 0 { return CS_NORMAL; }
    ce_steps++;
    if ce_steps > 2000000 { return CS_FAIL; }
    let nd = nodes[s];
    let k = nd.kind as i64;
    if k == N_COMPOUND {
        let lm = ce_locals.len;
        for i in nd.c as i64 {
            let r = ce_exec(nlist[nd.v + i]);
            if r != CS_NORMAL { ce_locals.resize(lm); return r; }
        }
        ce_locals.resize(lm);
        return CS_NORMAL;
    }
    if k == N_NULL || k == N_TYPEDEF || k == N_TAGDEF || k == N_STATICASSERT { return CS_NORMAL; }
    if k == N_EXPR {
        let v = ce_rv(nd.a);
        return if v.k == CE_FAIL as! u8 { CS_FAIL } else { CS_NORMAL };
    }
    if k == N_DECL {
        let sy = nd.a as i64;
        let t = syms[sy].ty;
        if syms[sy].kind as i64 != SK_VAR { return CS_NORMAL; }
        if syms[sy].sc as i64 == SC_STATIC || syms[sy].sc as i64 == SC_EXTERN { return CS_FAIL; }
        let sz = if is_ref(t) { 8 } else { type_size(t) };
        let al = if is_ref(t) { 8 } else { type_align(t) };
        let a = ce_alloc(sz, al, false);
        if a < 0 { return CS_FAIL; }
        ce_zero(a, sz);
        ce_locals.push(sy);
        ce_locals.push(a);
        if nd.b != 0 {
            if !ce_init(a, t, nd.b) { return CS_FAIL; }
        } else if is_record(t) {
            if !ce_value_init_default(a, t) { return CS_FAIL; }
        }
        return CS_NORMAL;
    }
    if k == N_RETURN {
        if nd.a == 0 { ce_rv_val = ce_void(); return CS_RETURN; }
        let f = cur_ce_fn();
        let rt = if f >= 0 { types[syms[f].ty >> 4].base } else { nodes[nd.a].ty };
        if is_ref(rt) {
            let ok, a = ce_lv(nd.a);
            if !ok { return CS_FAIL; }
            ce_rv_val = ce_ptr(a, mk_ptr(tbase(rt)));
            return CS_RETURN;
        }
        if is_record(rt) {
            var ra = ce_ret_addr;
            if ra == 0 {
                ra = ce_alloc(type_size(rt), type_align(rt), false);
                if ra < 0 { return CS_FAIL; }
            }
            let sv = ce_ret_addr;
            ce_ret_addr = 0;
            let ok = ce_init(ra, rt, nd.a);
            ce_ret_addr = sv;
            if !ok { return CS_FAIL; }
            ce_rv_val = ce_obj(ra, unqual(rt));
            return CS_RETURN;
        }
        let v = ce_conv(ce_rv(nd.a), rt);
        if v.k == CE_FAIL as! u8 { return CS_FAIL; }
        ce_rv_val = v;
        return CS_RETURN;
    }
    if k == N_IF {
        let lm = ce_locals.len;
        let c = ce_truth(ce_rv(nd.a));
        if c < 0 { return CS_FAIL; }
        let r = ce_exec(if c != 0 { nd.b } else { nd.c });
        ce_locals.resize(lm);
        return r;
    }
    if k == N_WHILE {
        let lm = ce_locals.len;
        loop {
            ce_locals.resize(lm);
            let c = ce_truth(ce_rv(nd.a));
            if c < 0 { return CS_FAIL; }
            if c == 0 { break; }
            let r = ce_exec(nd.b);
            if r == CS_BREAK { break; }
            if r == CS_RETURN || r == CS_FAIL { ce_locals.resize(lm); return r; }
        }
        ce_locals.resize(lm);
        return CS_NORMAL;
    }
    if k == N_DO {
        loop {
            let r = ce_exec(nd.a);
            if r == CS_BREAK { break; }
            if r == CS_RETURN || r == CS_FAIL { return r; }
            let c = ce_truth(ce_rv(nd.b));
            if c < 0 { return CS_FAIL; }
            if c == 0 { break; }
        }
        return CS_NORMAL;
    }
    if k == N_FOR {
        let lm = ce_locals.len;
        if nd.a != 0 {
            let r0 = ce_exec_or_expr(nd.a);
            if r0 != CS_NORMAL { ce_locals.resize(lm); return CS_FAIL; }
        }
        let lm2 = ce_locals.len;
        loop {
            ce_locals.resize(lm2);
            if nd.b != 0 {
                let c = ce_truth(ce_rv(nd.b));
                if c < 0 { ce_locals.resize(lm); return CS_FAIL; }
                if c == 0 { break; }
            }
            let r = ce_exec(nd.v as u32);
            if r == CS_BREAK { break; }
            if r == CS_RETURN || r == CS_FAIL { ce_locals.resize(lm); return r; }
            if nd.c != 0 {
                let x = ce_rv(nd.c);
                if x.k == CE_FAIL as! u8 { ce_locals.resize(lm); return CS_FAIL; }
            }
        }
        ce_locals.resize(lm);
        return CS_NORMAL;
    }
    if k == N_SWITCH { return ce_switch(s); }
    if k == N_BREAK { return CS_BREAK; }
    if k == N_CONTINUE { return CS_CONTINUE; }
    if k == N_CASE || k == N_DEFAULT { return ce_exec(nd.a); }
    if k == N_LABEL { return ce_exec(nd.b); }
    return CS_FAIL;
}

recursive fn ce_exec_or_expr(n: u32) -> i64 {
    let k = nodes[n].kind as i64;
    if k >= N_COMPOUND && k <= N_NULL { return ce_exec(n); }
    let v = ce_rv(n);
    return if v.k == CE_FAIL as! u8 { CS_FAIL } else { CS_NORMAL };
}

// switch: the statements from the matching case (flattened bodies: the
// case labels are found in the body's compound statement).
recursive fn ce_switch(s: u32) -> i64 {
    let nd = nodes[s];
    let c = ce_rv(nd.a);
    if c.k != CE_INT as! u8 { return CS_FAIL; }
    let body = nd.b;
    if nodes[body].kind as i64 != N_COMPOUND { return CS_FAIL; }
    let bn = nodes[body];
    // the first statement to run
    var start: i64 = -1;
    var deflt: i64 = -1;
    for i in bn.c as i64 {
        let x = nodes[nlist[bn.v + i]];
        if x.kind as i64 == N_CASE {
            let hi = if x.c != 0 { nodes[x.c].v } else { x.v };
            if c.i >= x.v && c.i <= hi && start < 0 { start = i; }
        } else if x.kind as i64 == N_DEFAULT { deflt = i; }
    }
    if start < 0 { start = deflt; }
    if start < 0 { return CS_NORMAL; }
    let lm = ce_locals.len;
    var i = start;
    while i < bn.c as i64 {
        let r = ce_exec(nlist[bn.v + i]);
        if r == CS_BREAK { break; }
        if r != CS_NORMAL { ce_locals.resize(lm); return r; }
        i++;
    }
    ce_locals.resize(lm);
    return CS_NORMAL;
}

// The function whose body runs (for return statements): the innermost call.
var ce_fn_stack: i64[>..<] = [];
fn cur_ce_fn() -> i64 { if ce_fn_stack.len == 0 { return -1; } return ce_fn_stack[ce_fn_stack.len - 1]; }

// ---------------------------------------------------------------------------
// Builtins.

recursive fn ce_builtin(e: u32) -> CeV { return ce_bad(e); }

recursive fn ce_builtin_call(f: i64, v: i64, c: i64, e: u32) -> CeV {
    let nm = ident_text(syms[f].name as i64);
    if nm == "__builtin_is_constant_evaluated" { return ce_int(1, t_bool); }
    if nm == "__builtin_expect" && c >= 1 { return ce_rv(nlist[v]); }
    if (nm == "__builtin_strlen" || nm == "__builtin_wcslen") && c == 1 {
        let p = ce_rv(nlist[v]);
        if p.k != CE_PTR as! u8 || p.i == 0 { return ce_bad(e); }
        let es = if nm == "__builtin_strlen" { 1 } else { 4 };
        var n: i64 = 0;
        loop {
            if !ce_valid(p.i + n * es, es) { return ce_bad(e); }
            if ce_ld(p.i + n * es, es) == 0 { break; }
            n++;
        }
        return ce_int(n, t_ulong);
    }
    if nm == "__builtin_unreachable" || nm == "__builtin_trap" || nm == "__builtin_abort" { return ce_fail(); }
    return ce_bad(e);
}

// ---------------------------------------------------------------------------
// Entry points.

// The integer value of constant expression e (an integral or enumeration
// type), when the evaluator can compute it.
recursive fn ce_eval_int(e: u32) -> bool, i64 {
    if e == 0 || is_opq(e) { return false, 0; }
    let t = nodes[e].ty;
    if !(is_integer(t) || kind_of(t) == TY_BOOL || kind_of(t) == TY_ENUM) && !is_pointer(t) { return false, 0; }
    let v = ce_top(e);
    if v.k == CE_INT as! u8 { return true, v.i; }
    return false, 0;
}

// The value of e evaluated as a full constant expression.
recursive fn ce_top(e: u32) -> CeV {
    let mm = ce_mem.len;
    let lm = ce_locals.len;
    let sf = ce_frame;
    let sth = ce_this;
    let fm = ce_fn_stack.len;
    if ce_active == 0 { ce_steps = 0; ce_why = 0; }
    ce_active++;
    ce_frame = ce_locals.len;
    ce_this = 0;
    let v = ce_rv(e);
    ce_active--;
    ce_this = sth;
    ce_frame = sf;
    ce_locals.resize(lm);
    ce_fn_stack.resize(fm);
    var r = v;
    if v.k == CE_OBJ as! u8 { r = ce_fail(); }      // (a class value: not returned to the caller)
    if v.k == CE_PTR as! u8 && v.i > 0 && v.i < CE_G { r = ce_fail(); }    // a pointer to a temporary
    if ce_active == 0 { ce_mem.resize(mm); }
    return r;
}

// ---------------------------------------------------------------------------
// Function bodies for the evaluation: parsed again in semantic-analysis
// mode (cg_on off), with the instantiation machinery for templates; the
// function's definition node, its mem-initializers and flags are left as
// they were.

var ce_capturing: bool = false;
var ce_bodies = dictionary<u64, u32> {};    // function -> its N_FUNCDEF for the evaluation (max: none)
var ce_inits = dictionary<u64, u32> {};     // constructor -> its mem-initializers for the evaluation
var ce_btok = dictionary<u64, u64> {};      // constexpr function -> (scope << 32 | body token)

fn ce_note_body(s: i64, tok: i64, sc: i64) {
    ce_btok.insert(s as u64, ((sc as u64) << 32) | (tok as u64));
}

recursive fn ce_inits_of(f: i64) -> u32 {
    let g = ce_inits.get(f as u64);
    if g { return g; }
    return 0;
}

recursive fn ce_body(f: i64) -> u32 {
    let g = ce_bodies.get(f as u64);
    if g { return if g == 4294967295 { 0 } else { g }; }
    ce_bodies.insert(f as u64, 4294967295);
    let d0 = syms[f].def;
    var ci0: u32 = 0;
    let cg_ = ctor_inits.get(f as u64);
    if cg_ { ci0 = cg_; }
    let fl0 = cxs[f].flags;
    let fl20 = cxs[f].flags2;
    let sfl0 = syms[f].flags;
    let cg0 = cg_on;
    let cap0 = ce_capturing;
    let mark = nscratch.len;
    // in semantic-analysis mode, a definition already parsed is used as it is
    if !cg0 && d0 >= 0 && nodes[d0].kind as i64 == N_FUNCDEF && nodes[d0].b != 0 {
        ce_bodies.insert(f as u64, d0 as u32);
        ce_inits.insert(f as u64, ci0);
        return d0 as u32;
    }
    cg_on = false;
    ce_capturing = true;
    syms[f].def = -1;
    var tried = true;
    if cxs[f].flags2 & CF2_FSPEC != 0 {
        inst_fspec_body(f);
    } else if cxs[f].body != 0 && cxs[f].flags & (CF_HAS_BODY_LATER | CF_DEFINED_IN_CLASS) != 0 {
        let fsg = friend_scope.get(f as u64);
        let sc = if fsg { fsg as i64 } else { cxs[f].dscope as i64 };
        let st = inst_enter(true);
        parse_member_body(f, sc);
        let bad = inst_leave(st);
    } else if cxs[f].flags2 & CF2_LAZY_BODY != 0 {
        let p = pattern_member(f);
        if p >= 0 && cxs[p].odef >= 0 {
            let hdr = cxs[p].odef as i64;
            let pat, pargs = inst_args_of(cxs[f].dscope as i64);
            if pat >= 0 {
                let st = inst_enter(true);
                bind_header(hdr, pargs);
                cur_scope = tmpls[hdr].scope as i64;
                pc = tmpls[hdr].t0 as i64;
                inst_def_target = f;
                parse_simple_decl(DC_NS);
                inst_def_target = -1;
                let bad = inst_leave(st);
            }
        }
    } else {
        let bt = ce_btok.get(f as u64);
        if bt {
            let st = inst_enter(true);
            cur_scope = (bt >> 32) as i64;
            pc = (bt & 0xFFFFFFFF) as i64;
            let ps, pn = fn_param_list(f);
            let n = parse_function_body(f, if ps < 0 { 0 } else { ps }, if ps < 0 { 0 } else { pn });
            let bad = inst_leave(st);
        } else { tried = false; }
    }
    nscratch.resize(mark);
    let d = syms[f].def;
    var ci: u32 = 0;
    let cg2 = ctor_inits.get(f as u64);
    if cg2 { ci = cg2; }
    // restored
    syms[f].def = d0;
    if ci0 != 0 { ctor_inits.insert(f as u64, ci0); } else { ctor_inits.remove(f as u64); }
    cxs[f].flags = fl0;
    cxs[f].flags2 = fl20;
    syms[f].flags = sfl0;
    cg_on = cg0;
    ce_capturing = cap0;
    if !tried || d < 0 || nodes[d].kind as i64 != N_FUNCDEF || nodes[d].b == 0 { return 0; }
    ce_bodies.insert(f as u64, d as u32);
    ce_inits.insert(f as u64, ci);
    return d as u32;
}

// The default argument of parameter p of f, parsed for the evaluation.
recursive fn ce_default_arg(f: i64, p: i64) -> u32 {
    let cg0 = cg_on;
    cg_on = false;
    let e = default_arg(f, p);
    cg_on = cg0;
    return e;
}

// A default member initializer (tokens at cxs[s].body) for the evaluation.
recursive fn ce_parse_nsdmi(s: i64) -> u32 {
    let cg0 = cg_on;
    cg_on = false;
    let sv = save();
    let s_scope = cur_scope;
    let s_tt = this_type;
    let sc = cxs[s].dscope as i64;
    let ct = scope_class_type(sc);
    cur_scope = sc;
    this_type = if ct != 0 { mk_ptr(ct) } else { 0 };
    pc = cxs[s].body as i64;
    gt_pos = -1;
    if at(TK_EQUAL) { adv(); }
    var e: u32 = 0;
    if at(TK_L_BRACE) { e = parse_braced(); } else { e = parse_assign_cx(); }
    cur_scope = s_scope;
    this_type = s_tt;
    restore(sv);
    cg_on = cg0;
    if is_opq(e) && nodes[e].kind as i64 != N_INITBRACE { return 0; }
    return e;
}
