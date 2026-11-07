// goosecc B2: expressions. The AST of DESIGN.md section 6 is lowered as
// clang's CodeGen does at -O0: every object lives in memory (allocas for
// locals), scalar expressions become GIR values, complex values are pairs
// of values, and aggregates are evaluated into a destination address.
//
//   ex_val(n)        a scalar rvalue (NONE for void)
//   ex_cplx(n)       a complex rvalue as (real, imaginary)
//   ex_agg(n, dst)   an aggregate rvalue stored at dst (NONE: discarded)
//   ex_lv(n)         an lvalue: address, bit-field, volatility
//   ex_cond(n, t, f) branch on a scalar condition
//   ex_ignore(n)     evaluate for the side effects

namespace gen;

import std;
import .common;
import .types;
import .ast;
import .sema;
import .builtins;
import .dtype;

struct LV {
    addr: u32,      // the address (for a bit-field: of the record holding it)
    fld: i32,       // bit-field: index in fields, else -1
    vol: bool,
    q: u32,         // the C type of the object
}

fn lv_plain(addr: u32, q: u32) -> LV { LV { addr: addr, fld: -1, vol: quals(q) & Q_VOLATILE != 0, q: q } }

fn nkind(n: u32) -> i64 { nodes[n].kind as i64 }

// ------------------------------------------------------------ per-function state

// Per symbol: the address of a local (alloca, byval arg, VLA), its GIR
// global (NONE until needed), the initializer node of a file-scope
// object, the N_DECL that defines it, the initializer of a const local
// (for folding); one array, sized by ensure_sym_gen.
struct SymGen { addr: u32, glob: u32, init: u32, decl: u32, linit: u32 }
var sym_gen: SymGen[>..] = [];
fn ensure_sym_gen() { while sym_gen.len < syms.len { sym_gen.push(SymGen { addr: NONE, glob: NONE, init: 0, decl: 0, linit: 0 }); } }
var vla_size: u32[>..] = [];     // per VLA type index: the value of its element count, NONE
var f_sym: i64 = -1;
var f_ret: Abi = Abi { kind: AK_IGNORE, ext: 0, n: 0, tmp: 0, t0: 0, t1: 0, off0: 0, off1: 0, size: 0, align: 1 };
var f_sret: u32 = NONE;
var f_ret_q: u32 = 0;
var f_flags: u32 = 0;

fn ensure_sym_tables() {
    ensure_sym_gen();
}

fn ensure_vla_table() {
    while vla_size.len < types.len { vla_size.push(NONE); }
}

// ------------------------------------------------------------ VLA sizes

// The size in bytes of type q as a value (VLA-aware).
recursive fn size_val(q: u32) -> u32 {
    let k = kind_of(q);
    if k == TY_VLA {
        ensure_vla_table();
        let ti = q >> 4;
        var n = vla_size[ti];
        if n == NONE { n = eval_vla(q); }
        let es = size_val(tbase(q));
        return ins_bin(GIR_MUL, GIR_T_I64, n, es);
    }
    if k == TY_ARRAY && is_vm(tbase(q)) {
        let es = size_val(tbase(q));
        return ins_bin(GIR_MUL, GIR_T_I64, c_i64(types[q >> 4].n), es);
    }
    var s = type_size(q);
    if s < 0 { s = 1; }
    if k == TY_VOID || k == TY_FUNC { s = 1; }
    return c_i64(s);
}

recursive fn is_vm(q: u32) -> bool {
    let k = kind_of(q);
    if k == TY_VLA { return true; }
    if k == TY_ARRAY { return is_vm(tbase(q)); }
    return false;
}

// Evaluates the size expressions of a variably modified type (at its declaration).
recursive fn eval_vm_type(q: u32) {
    let k = kind_of(q);
    if k == TY_VLA {
        eval_vla(q);
        eval_vm_type(tbase(q));
    } else if k == TY_ARRAY || k == TY_POINTER {
        eval_vm_type(tbase(q));
    } else if k == TY_FUNC {
        eval_vm_type(tbase(q));
    }
}

recursive fn eval_vla(q: u32) -> u32 {
    ensure_vla_table();
    let ti = q >> 4;
    let e = types[ti].n as! u32;
    let v = ex_val(e);
    let r = conv(v, nty(e), t_ulong);
    vla_size[ti] = r;
    return r;
}

// Element size of a pointer's pointee as (constant, or value if VLA).
recursive fn elem_size(pt: u32) -> bool, i64, u32 {
    if is_vm(pt) { return false, 0, size_val(pt); }
    let k = kind_of(pt);
    if k == TY_VOID || k == TY_FUNC { return true, 1, NONE; }
    let s = type_size(pt);
    return true, if s < 0 { 1 } else { s }, NONE;
}

// p + i * sizeof(*p); i is an integer value of C type iq.
recursive fn ptr_add(p: u32, pt: u32, i: u32, iq: u32, neg: bool) -> u32 {
    var idx = i;
    let it = vtype(idx);
    if tcls(it) == C_INT2 { idx = int_cast(idx, it, GIR_T_I64, false); }
    else if tbits(it) < 64 { idx = int_cast(idx, it, GIR_T_I64, kind_of(iq) != TY_BOOL && is_signed(iq)); }
    if neg { idx = ins_bin(GIR_SUB, GIR_T_I64, c_i64(0), idx); }
    let ok, es, ev = elem_size(pt);
    if !ok {
        let off = ins_bin(GIR_MUL, GIR_T_I64, idx, ev);
        return gep_idx(p, 0, off, 1);
    }
    return gep_idx(p, 0, idx, es);
}

// ------------------------------------------------------------ lvalues

recursive fn ex_lv(n: u32) -> LV {
    if !dbg_on() { return ex_lv1(n); }
    let saved = push_loc(visit_loc(n));
    let l = ex_lv1(n);
    pop_loc(saved);
    return l;
}

recursive fn ex_lv1(n: u32) -> LV {
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_DECLREF {
        let s = nd.a as i64;
        if syms[s].kind == SK_FUNC || syms[s].kind == SK_BUILTIN { return lv_plain(gref(func_global(s)), nd.ty); }
        return lv_plain(var_addr(s), nd.ty);
    }
    if k == N_UNARY {
        if nd.op == U_DEREF { return lv_plain(ex_val(nd.a), nd.ty); }
        if nd.op == U_REAL || nd.op == U_IMAG {
            let l = ex_lv(nd.a);
            if nd.op == U_REAL { return lv_plain(l.addr, nd.ty); }
            return lv_plain(gep(l.addr, type_size(nd.ty)), nd.ty);
        }
        if nd.op == U_EXTENSION { return ex_lv(nd.a); }
    }
    if k == N_INDEX {
        if nd.op == 1 {
            // vector element
            let base = agg_addr_any(nd.a);
            let i = ex_val(nd.b);
            return lv_plain(ptr_add(base, nd.ty, i, nty(nd.b), false), nd.ty);
        }
        let p = ex_val(nd.a);
        let i = ex_val(nd.b);
        return lv_plain(ptr_add(p, nd.ty, i, nty(nd.b), false), nd.ty);
    }
    if k == N_MEMBER {
        var base: u32 = 0;
        if nd.op == 1 { base = ex_val(nd.a); } else { base = agg_addr(nd.a); }
        let f = fields[nd.b];
        if f.width >= 0 {
            return LV { addr: base, fld: nd.b as! i32, vol: quals(nd.ty) & Q_VOLATILE != 0, q: nd.ty };
        }
        return lv_plain(gep(base, f.offset), nd.ty);
    }
    if k == N_STRING {
        let g = string_global(nd.a);
        dbg_string(n, g);
        return lv_plain(gref(g), nd.ty);
    }
    if k == N_COMPLIT { return lv_plain(ex_complit(n), nd.ty); }
    if k == N_SWIZZLE {
        var base: u32 = 0;
        if nd.op == 1 { base = ex_val(nd.a); } else { base = agg_addr_any(nd.a); }
        let lane = (nd.v & 15) as i64;
        let vt = if nd.op == 1 { tbase(nty(nd.a)) } else { nty(nd.a) };
        return lv_plain(gep(base, lane * type_size(tbase(vt))), nd.ty);
    }
    if (k == N_ICAST || k == N_CAST) && (nd.op == CK_NOOP || nd.op == CK_ATOMIC || nd.op == CK_LVAL2RVAL) && is_lvalue(nd.a) {
        let l = ex_lv(nd.a);
        return LV { addr: l.addr, fld: l.fld, vol: l.vol, q: nd.ty };
    }
    // an rvalue used as an object (member of a call result, ...)
    let tmp = alloca(type_size(nd.ty), type_align(nd.ty));
    store_any(nd.ty, n, tmp);
    return lv_plain(tmp, nd.ty);
}

// Evaluates n (of any value kind) and stores it at p.
recursive fn store_any(q: u32, n: u32, p: u32) {
    let vk = vkind(q);
    if vk == VK_AGG { ex_agg(n, p); return; }
    if vk == VK_COMPLEX {
        let re, im = ex_cplx(n);
        store_cplx(q, re, im, p, false);
        return;
    }
    if vk == VK_VOID { ex_ignore(n); return; }
    let v = ex_val(n);
    store_c(q, v, p, false);
}

// The address of an aggregate (lvalue or temporary).
recursive fn agg_addr(n: u32) -> u32 {
    if is_lvalue(n) { return ex_lv(n).addr; }
    let q = nty(n);
    let tmp = alloca(type_size(q), type_align(q));
    ex_agg(n, tmp);
    return tmp;
}

// The address of a value of any kind (spilled if needed).
recursive fn agg_addr_any(n: u32) -> u32 {
    if is_lvalue(n) { return ex_lv(n).addr; }
    let q = nty(n);
    let tmp = alloca(type_size(q), type_align(q));
    store_any(q, n, tmp);
    return tmp;
}

// ------------------------------------------------------------ bit-fields

fn bf_mask(bits: u32, w: i64, t: u32) -> u32 {
    // (1 << w) - 1 in type t
    if bits > 64 {
        if w >= 64 { return c_wide(0xFFFFFFFFFFFFFFFF, mask_of((w - 64) as! u32), t); }
        return c_wide(mask_of(w as! u32), 0, t);
    }
    return c_int(mask_of(w as! u32), t);
}

fn shift_const(t: u32, s: i64) -> u32 {
    if tcls(t) == C_INT2 { return c_wide(s as! u64, 0, t); }
    return c_int(s as! u64, t);
}

fn bf_load(l: LV) -> u32 {
    let f = fields[l.fld];
    let w = f.width as i64;
    let bp = f.bitpos;
    let b0 = bp / 8;
    let bit = bp % 8;
    let nbytes = (bit + w + 7) / 8;
    let nb = (nbytes * 8) as! u32;
    let it = ty_int(nb);
    let p = gep(l.addr, b0);
    var x = ins_load(it, p, l.vol);
    let ft = f.ty;
    let vt = vty(ft);
    let signed = kind_of(ft) != TY_BOOL && is_signed(ft);
    if signed {
        let up = nb as i64 - w - bit;
        if up > 0 { x = ins_bin(GIR_SHL, it, x, shift_const(it, up)); }
        if nb as i64 - w > 0 { x = ins_bin(GIR_ASHR, it, x, shift_const(it, nb as i64 - w)); }
    } else {
        if bit > 0 { x = ins_bin(GIR_LSHR, it, x, shift_const(it, bit)); }
        if w < nb as i64 { x = ins_bin(GIR_AND, it, x, bf_mask(nb, w, it)); }
    }
    if vt == GIR_T_I1 { return int_cast(x, it, GIR_T_I1, false); }
    return int_cast(x, it, vt, signed);
}

// Stores v (of the field's value type) into the bit-field; returns the value
// as read back (truncated to the width, sign-extended if signed).
fn bf_store(l: LV, v: u32) -> u32 {
    let f = fields[l.fld];
    let w = f.width as i64;
    let bp = f.bitpos;
    let b0 = bp / 8;
    let bit = bp % 8;
    let nbytes = (bit + w + 7) / 8;
    let nb = (nbytes * 8) as! u32;
    let it = ty_int(nb);
    let p = gep(l.addr, b0);
    let vt = vtype(v);
    var x = int_cast(v, vt, it, false);
    if w < nb as i64 { x = ins_bin(GIR_AND, it, x, bf_mask(nb, w, it)); }
    if bit > 0 { x = ins_bin(GIR_SHL, it, x, shift_const(it, bit)); }
    if w < nb as i64 {
        let old = ins_load(it, p, l.vol);
        // keep the bits outside [bit, bit + w)
        var keep = bf_mask(nb, w, it);
        if bit > 0 { keep = ins_bin(GIR_SHL, it, keep, shift_const(it, bit)); }
        let all = if tcls(it) == C_INT2 { c_wide(0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, it) } else { c_int(0xFFFFFFFFFFFFFFFF, it) };
        keep = ins_bin(GIR_XOR, it, keep, all);
        let o2 = ins_bin(GIR_AND, it, old, keep);
        x = ins_bin(GIR_OR, it, o2, x);
    }
    ins_store(it, x, p, l.vol);
    // the value of the assignment
    let ft = f.ty;
    let signed = kind_of(ft) != TY_BOOL && is_signed(ft);
    if vt == GIR_T_I1 { return v; }
    let fb = tbits(vt) as i64;
    if w >= fb { return v; }
    if signed {
        let s1 = ins_bin(GIR_SHL, vt, v, shift_const(vt, fb - w));
        return ins_bin(GIR_ASHR, vt, s1, shift_const(vt, fb - w));
    }
    return ins_bin(GIR_AND, vt, v, bf_mask(tbits(vt), w, vt));
}

fn lv_load(l: LV) -> u32 {
    if l.fld >= 0 { return bf_load(l); }
    return load_c(l.q, l.addr, l.vol);
}

// Stores a scalar; returns the stored value.
fn lv_store(l: LV, v: u32) -> u32 {
    if l.fld >= 0 { return bf_store(l, v); }
    store_c(l.q, v, l.addr, l.vol);
    return v;
}

// ------------------------------------------------------------ complex

fn cplx_elem(q: u32) -> u32 { unqual(tbase(q)) }

fn load_cplx(q: u32, p: u32, vol: bool) -> u32, u32 {
    let et = cplx_elem(q);
    let re = load_c(et, p, vol);
    let im = load_c(et, gep(p, type_size(et)), vol);
    return re, im;
}

fn store_cplx(q: u32, re: u32, im: u32, p: u32, vol: bool) {
    let et = cplx_elem(q);
    store_c(et, re, p, vol);
    store_c(et, im, gep(p, type_size(et)), vol);
}

// ------------------------------------------------------------ scalars

recursive fn ex_ignore(n: u32) {
    let vk = vkind(nty(n));
    if vk == VK_AGG {
        // an lvalue of aggregate type: nothing to do (clang does not load it)
        if is_lvalue(n) {
            let k = nkind(n);
            if k == N_DECLREF || k == N_STRING { return; }
            ex_lv(n);
            return;
        }
        ex_agg(n, NONE);
        return;
    }
    if vk == VK_COMPLEX {
        if is_lvalue(n) { ex_lv(n); return; }
        ex_cplx(n);
        return;
    }
    if is_lvalue(n) {
        // a discarded lvalue that was not converted (void, or a bit-field read)
        let l = ex_lv(n);
        if l.vol && !is_void(nty(n)) && vk == VK_SCALAR { lv_load(l); }
        return;
    }
    ex_val(n);
}

recursive fn ex_val(n: u32) -> u32 {
    if !dbg_on() { return ex_val1(n); }
    let saved = push_loc(visit_loc(n));
    let k = nkind(n);
    if k == N_INT { dbg_enumc(n); }
    else if k == N_CAST && !dbg_no_enum { dev(EV_CAST, node_written(n), 0); }
    let v = ex_val1(n);
    pop_loc(saved);
    return v;
}

recursive fn ex_val1(n: u32) -> u32 {
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_INT {
        let t = vty(nd.ty);
        if tcls(t) == C_INT2 { return c_wide(nd.v as! u64, if nd.v < 0 { 0xFFFFFFFFFFFFFFFF } else { 0 as u64 }, t); }
        if t == GIR_T_I1 { return c_int(if nd.v != 0 { 1 } else { 0 }, t); }
        if t == GIR_T_VOID { return NONE; }
        return c_int(nd.v as! u64, t);
    }
    if k == N_FLOAT { return float_const(n); }
    if k == N_ICAST || k == N_CAST { return ex_cast(n); }
    if k == N_UNARY { return ex_unary(n); }
    if k == N_BINARY { return ex_binary(n); }
    if k == N_ASSIGN { return ex_assign(n); }
    if k == N_COND { return ex_condexpr(n, NONE); }
    if k == N_CALL { return ex_call(n, NONE); }
    if k == N_SIZEOF {
        if nd.v >= 0 { return c_int(nd.v as! u64, vty(nd.ty)); }
        // a variably modified type: evaluate the expression's VLA sizes
        var tq = nd.b;
        if nd.a != 0 && is_vm(nty(nd.a)) { tq = nty(nd.a); }
        if nd.op == 1 { return c_int(type_align(tq) as! u64, vty(nd.ty)); }
        if nd.a == 0 { eval_vm_type(tq); }
        return conv(size_val(tq), t_ulong, nd.ty);
    }
    if k == N_OFFSETOF { return c_int(nd.v as! u64, vty(nd.ty)); }
    if k == N_STMTEXPR { return ex_stmtexpr(n, NONE); }
    if k == N_VAARG {
        let p = va_arg_addr(n);
        let q = nd.ty;
        return load_c(q, p, false);
    }
    if k == N_LABELADDR {
        add_addr_label(nd.a as i64);
        return emit(GIR_BLOCKADDR, GIR_T_PTR, 0, 0, 0, f_global, label_block(nd.a as i64), 0);
    }
    if k == N_BUILTIN { return ex_builtin(n, NONE); }
    if k == N_DECLREF {
        let s = nd.a as i64;
        if syms[s].kind == SK_FUNC || syms[s].kind == SK_BUILTIN { return gref(func_global(s)); }
        return lv_load(ex_lv(n));
    }
    if k == N_SWIZZLE { return ex_swizzle(n); }
    if k == N_INDEX && nd.op == 1 && !is_lvalue(n) {
        let v = ex_val(nd.a);
        let i = ex_val(nd.b);
        return emit(GIR_EXTRACTELT, mty(nd.ty), 0, 0, vtype(v), v, i, 0);
    }
    if k == N_INITLIST {
        if is_vector(nd.ty) { return vec_init_val(n); }
        // a scalar in braces: { x }
        if nd.c > 0 { return ex_val(nlist[nd.v]); }
        return c_zero(vty(nd.ty));
    }
    if k == N_ZEROINIT { return c_zero(vty(nd.ty)); }
    if is_lvalue(n) || k == N_MEMBER || k == N_INDEX { return lv_load(ex_lv(n)); }
    if k == N_ERROR { return c_zero(GIR_T_I32); }
    bug("ex_val", n);
    return c_zero(GIR_T_I32);
}

// A vector from an initializer list (elements or smaller vectors).
recursive fn vec_init_val(n: u32) -> u32 {
    let nd = nodes[n];
    let vt = vty(nd.ty);
    let et = tbase(nd.ty);
    let lanes = m_types[vt].n;
    var v = c_zero(vt);
    var lane: u32 = 0;
    for i in nd.c {
        let child = nlist[nd.v + i];
        let ct = nty(child);
        let x = ex_val(child);
        if is_vector(ct) {
            let cn = m_types[vtype(x)].n;
            for j in 0..cn {
                if lane >= lanes { break; }
                let e = emit(GIR_EXTRACTELT, mty(tbase(ct)), 0, 0, vtype(x), x, c_i32(j as i64), 0);
                v = emit(GIR_INSERTELT, vt, 0, 0, 0, v, e, c_i32(lane as i64));
                lane++;
            }
        } else {
            if lane >= lanes { break; }
            let e = conv(x, ct, et);
            let em = if kind_of(et) == TY_BOOL { int_cast(e, GIR_T_I1, GIR_T_I8, false) } else { e };
            v = emit(GIR_INSERTELT, vt, 0, 0, 0, v, em, c_i32(lane as i64));
            lane++;
        }
    }
    return v;
}

fn bug(what: const u8[:], n: u32) {
    write_stderr(str("goosecc: internal error: ", what, " cannot lower node kind ", nodes[n].kind, " op ", nodes[n].op, "\n"));
    var err_out: u8[>..] = [];
    loc_prefix(err_out, nodes[n].loc as i64);
    n_errors++;
}

fn float_const(n: u32) -> u32 {
    let nd = nodes[n];
    let t = vty(nd.ty);
    let d = reinterpret_f64(nd.v);
    if nd.c > 0 {
        // the literal's spelling, converted exactly to its type
        let text = src[nd.b..nd.b + nd.c];
        if t == GIR_T_F80 {
            let x = strtold(text);
            return c_fp(x.lo, x.hi, t);
        }
        if t == GIR_T_F64 { return c_fp(strtod_bits(text, 1), 0, t); }
        if t == GIR_T_F32 { return c_fp(strtod_bits(text, 0), 0, t); }
        if t == GIR_T_F16 { return c_fp(strtod_bits(text, 3), 0, t); }
    }
    if t == GIR_T_F80 {
        let x = f64_to_f80(d);
        return c_fp(x.lo, x.hi, t);
    }
    return c_double(d, t);
}

recursive fn ex_swizzle(n: u32) -> u32 {
    let nd = nodes[n];
    var vec: u32 = 0;
    if nd.op == 1 {
        let p = ex_val(nd.a);
        let vt = tbase(nty(nd.a));
        vec = ins_load(vty(vt), p, false);
    } else {
        vec = ex_val(nd.a);
    }
    let cnt = nd.c as i64;
    if cnt == 1 {
        return emit(GIR_EXTRACTELT, mty(nd.ty), 0, 0, vtype(vec), vec, c_i32(nd.v & 15), 0);
    }
    let rt = vty(nd.ty);
    let s = m_opnds.len as! u32;
    let nl = m_types[rt].n as i64;
    for i in nl {
        if i < cnt { op_imm(((nd.v >> (4 * i)) & 15) as! u32); } else { op_imm(NONE); }
    }
    return emit(GIR_SHUFFLE, rt, 0, 0, vtype(vec), vec, vec, s);
}

recursive fn ex_cast(n: u32) -> u32 {
    let nd = nodes[n];
    let ck = nd.op as i64;
    let a = nd.a;
    if ck == CK_LVAL2RVAL {
        let l = ex_lv(a);
        if quals(nd.ty) & Q_ATOMIC != 0 || quals(nty(a)) & Q_ATOMIC != 0 { return atomic_load_lv(l, unqual(nd.ty)); }
        return lv_load(LV { addr: l.addr, fld: l.fld, vol: l.vol, q: nd.ty });
    }
    if ck == CK_ARRAY2PTR {
        if nkind(a) == N_STRING {
            let g = string_global(nodes[a].a);
            dbg_string(a, g);
            return gref(g);
        }
        return ex_lv(a).addr;
    }
    if ck == CK_FUNC2PTR || ck == CK_BUILTIN2PTR { return ex_lv(a).addr; }
    if ck == CK_NULL2PTR {
        if nkind(a) != N_INT && has_side_effects(a) {
            // clang does not visit the operand of a null pointer conversion
            // (its casts and enumerators make no debug types)
            let q0 = dbg_no_enum;
            dbg_no_enum = true;
            ex_ignore(a);
            dbg_no_enum = q0;
        }
        return c_null();
    }
    if ck == CK_TOVOID { ex_ignore(a); return NONE; }
    if ck == CK_INT2BOOL || ck == CK_FLOAT2BOOL || ck == CK_PTR2BOOL {
        let v = ex_val(a);
        return to_bool(v, nty(a));
    }
    if ck == CK_COMPLEX2REAL {
        let re, im = ex_cplx(a);
        return conv(re, cplx_elem(nty(a)), nd.ty);
    }
    if ck == CK_VECSPLAT {
        let s = ex_val(a);
        let vt = vty(nd.ty);
        let et = tbase(nd.ty);
        let sv = conv(s, nty(a), et);
        var v = c_zero(vt);
        let lanes = m_types[vt].n;
        for i in 0..lanes { v = emit(GIR_INSERTELT, vt, 0, 0, 0, v, sv, c_i32(i as i64)); }
        return v;
    }
    if vkind(nd.ty) != VK_SCALAR {
        bug("ex_cast (non-scalar)", n);
        return c_zero(GIR_T_I32);
    }
    let v = ex_val(a);
    if ck == CK_NOOP || ck == CK_ATOMIC {
        let t = vty(nd.ty);
        if t != vtype(v) && v != NONE && t != GIR_T_VOID { return conv(v, nty(a), nd.ty); }
        return v;
    }
    if ck == CK_BITCAST {
        let t = vty(nd.ty);
        if t != vtype(v) { return ins_bitcast(v, t); }
        return v;
    }
    return conv(v, nty(a), nd.ty);
}

fn has_side_effects(n: u32) -> bool {
    let k = nkind(n);
    return !(k == N_INT || k == N_FLOAT || k == N_DECLREF || k == N_SIZEOF || k == N_OFFSETOF || k == N_STRING);
}

// ------------------------------------------------------------ unary

recursive fn ex_unary(n: u32) -> u32 {
    let nd = nodes[n];
    let op = nd.op as i64;
    let a = nd.a;
    if op == U_ADDR {
        let an = nodes[a];
        if an.kind == N_DECLREF && (syms[an.a].kind == SK_FUNC || syms[an.a].kind == SK_BUILTIN) { return gref(func_global(an.a as i64)); }
        return ex_lv(a).addr;
    }
    if op == U_DEREF {
        // *p of a function or void pointer used as a value
        let l = ex_lv(n);
        if is_func(nd.ty) { return l.addr; }
        if is_void(nd.ty) { return NONE; }
        return lv_load(l);
    }
    if op == U_EXTENSION || op == U_PLUS { return ex_val(a); }
    if op == U_NEG {
        let v = ex_val(a);
        let t = vtype(v);
        if tcls(t) == C_FP || tcls(t) == C_X87 { return ins_fneg(v); }
        if tkind(t) == TK_VECTOR {
            let et = m_types[t].elems;
            if tcls(et) == C_FP { return emit(GIR_FNEG, t, 0, 0, t, v, 0, 0); }
        }
        return ins_bin(GIR_SUB, t, c_zero(t), v);
    }
    if op == U_BITNOT {
        let v = ex_val(a);
        let t = vtype(v);
        if tkind(t) == TK_VECTOR {
            let et = m_types[t].elems;
            var allones = c_zero(t);
            // build an all-ones vector constant
            let s = m_data.len as! u32;
            for i in 0..tsize(t) { m_data.push(255); }
            allones = c_new(0, 0, t, s);
            return emit(GIR_XOR, t, 0, 0, 0, v, allones, 0);
        }
        if tcls(t) == C_INT2 { return ins_bin(GIR_XOR, t, v, c_wide(0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, t)); }
        return ins_bin(GIR_XOR, t, v, c_int(0xFFFFFFFFFFFFFFFF, t));
    }
    if op == U_NOT {
        let b = ex_bool(a);
        let nb = ins_bin(GIR_XOR, GIR_T_I1, b, c_true());
        return int_cast(nb, GIR_T_I1, vty(nd.ty), false);
    }
    if op == U_PREINC || op == U_PREDEC || op == U_POSTINC || op == U_POSTDEC { return ex_incdec(n); }
    if op == U_REAL || op == U_IMAG {
        let at = nty(a);
        if is_complex(at) {
            if is_lvalue(a) {
                let l = ex_lv(n);
                return load_c(nd.ty, l.addr, l.vol);
            }
            let re, im = ex_cplx(a);
            return if op == U_REAL { re } else { im };
        }
        // __real / __imag of a real value
        let v = ex_val(a);
        if op == U_REAL { return v; }
        return c_zero(vtype(v));
    }
    bug("ex_unary", n);
    return c_zero(GIR_T_I32);
}

recursive fn ex_incdec(n: u32) -> u32 {
    let nd = nodes[n];
    let op = nd.op as i64;
    let inc = op == U_PREINC || op == U_POSTINC;
    let post = op == U_POSTINC || op == U_POSTDEC;
    let q = unqual(nd.ty);
    let l = ex_lv(nd.a);
    let lq = nty(nd.a);
    if quals(lq) & Q_ATOMIC != 0 { return atomic_incdec(l, q, inc, post); }
    if is_complex(q) {
        let re, im = load_cplx(q, l.addr, l.vol);
        let et = cplx_elem(q);
        let one = conv(c_i32(1), t_int, et);
        let nr = arith(if inc { B_ADD } else { B_SUB }, et, re, one);
        store_cplx(q, nr, im, l.addr, l.vol);
        return NONE;
    }
    let old = lv_load(l);
    var nv: u32 = 0;
    let k = kind_of(q);
    if k == TY_BOOL {
        nv = if inc { c_true() } else { ins_bin(GIR_XOR, GIR_T_I1, old, c_true()) };
    } else if k == TY_POINTER {
        nv = ptr_add(old, tbase(q), c_i64(if inc { 1 } else { -1 }), t_long, false);
    } else {
        let t = vtype(old);
        if tcls(t) == C_FP || tcls(t) == C_X87 {
            nv = ins_fbin(if inc { GIR_FADD } else { GIR_FSUB }, t, old, c_double(1.0, t));
        } else if tkind(t) == TK_VECTOR {
            let one = splat_const(t, 1);
            let et = m_types[t].elems;
            let fp = tcls(et) == C_FP;
            nv = emit(if fp { if inc { GIR_FADD } else { GIR_FSUB } } else { if inc { GIR_ADD } else { GIR_SUB } }, t, 0, 0, 0, old, one, 0);
        } else if tcls(t) == C_INT2 {
            nv = ins_bin(if inc { GIR_ADD } else { GIR_SUB }, t, old, c_wide(1, 0, t));
        } else {
            nv = ins_bin(if inc { GIR_ADD } else { GIR_SUB }, t, old, c_int(1, t));
        }
    }
    let stored = lv_store(l, nv);
    return if post { old } else { stored };
}

fn splat_const(t: u32, x: i64) -> u32 {
    let et = m_types[t].elems;
    let n = m_types[t].n;
    let s = m_data.len as! u32;
    for i in 0..n {
        if et == GIR_T_F32 {
            let b = f32_bits(x as f64);
            for k in 0..4 { m_data.push(((b >> ((8 * k) as! u64)) & 255) as! u8); }
        } else if et == GIR_T_F64 {
            let b = reinterpret_i64(x as f64) as! u64;
            for k in 0..8 { m_data.push(((b >> ((8 * k) as! u64)) & 255) as! u8); }
        } else {
            let sz = tsize(et);
            let b = x as! u64;
            for k in 0..sz { m_data.push(((b >> ((8 * k) as! u64)) & 255) as! u8); }
        }
    }
    while m_data.len < s as i64 + tsize(t) as i64 { m_data.push(0); }
    return c_new(0, 0, t, s);
}

// ------------------------------------------------------------ binary

// The GIR op for a C arithmetic operator on values of C type q.
fn arith(op: i64, q: u32, a: u32, b: u32) -> u32 {
    let t = vtype(a);
    var fp = tcls(t) == C_FP || tcls(t) == C_X87;
    var vec_fp = false;
    if tkind(t) == TK_VECTOR {
        let et = m_types[t].elems;
        vec_fp = tcls(et) == C_FP;
        fp = vec_fp;
    }
    var signed = true;
    if is_vector(q) { signed = is_signed(tbase(q)); } else if !fp { signed = kind_of(q) != TY_POINTER && is_signed(q); }
    if fp {
        let gop = match op { B_ADD => GIR_FADD, B_SUB => GIR_FSUB, B_MUL => GIR_FMUL, B_DIV => GIR_FDIV, _ => 0 };
        if op == B_REM {
            // fmod (GNU vector or never for scalars)
            return libcall2(if t == GIR_T_F32 { "fmodf" } else if t == GIR_T_F80 { "fmodl" } else { "fmod" }, t, a, b);
        }
        if tkind(t) == TK_VECTOR { return emit(gop, t, 0, 0, 0, a, b, 0); }
        return ins_fbin(gop, t, a, b);
    }
    var bb = b;
    if op == B_SHL || op == B_SHR {
        let bt = vtype(b);
        if bt != t {
            if tkind(t) == TK_VECTOR {
                // vector shifted by a scalar: splat
                if tkind(bt) != TK_VECTOR {
                    let et = m_types[t].elems;
                    let sv = int_cast(b, bt, et, false);
                    var v = c_zero(t);
                    for i in 0..m_types[t].n { v = emit(GIR_INSERTELT, t, 0, 0, 0, v, sv, c_i32(i as i64)); }
                    bb = v;
                }
            } else {
                bb = int_cast(b, bt, t, false);
            }
        }
    }
    let gop = match op {
        B_ADD => GIR_ADD, B_SUB => GIR_SUB, B_MUL => GIR_MUL,
        B_DIV => if signed { GIR_SDIV } else { GIR_UDIV },
        B_REM => if signed { GIR_SREM } else { GIR_UREM },
        B_SHL => GIR_SHL, B_SHR => if signed { GIR_ASHR } else { GIR_LSHR },
        B_AND => GIR_AND, B_XOR => GIR_XOR, _ => GIR_OR,
    };
    if tcls(t) == C_INT2 && (gop == GIR_SDIV || gop == GIR_UDIV || gop == GIR_SREM || gop == GIR_UREM) {
        let nm = match gop { GIR_SDIV => "__divti3", GIR_UDIV => "__udivti3", GIR_SREM => "__modti3", _ => "__umodti3" };
        let wa = int_cast(a, t, GIR_T_I128, signed);
        let wb = int_cast(bb, t, GIR_T_I128, signed);
        let r = libcall2(nm, GIR_T_I128, wa, wb);
        return int_cast(r, GIR_T_I128, t, false);
    }
    if tkind(t) == TK_VECTOR { return emit(gop, t, 0, 0, 0, a, bb, 0); }
    return ins_bin(gop, t, a, bb);
}

// A comparison of two scalars of C type q; i1 result (vectors: a lane mask).
fn compare(op: i64, q: u32, a: u32, b: u32) -> u32 {
    let t = vtype(a);
    let fp = tcls(t) == C_FP || tcls(t) == C_X87;
    if fp {
        let p = match op { B_LT => F_OLT, B_GT => F_OGT, B_LE => F_OLE, B_GE => F_OGE, B_EQ => F_OEQ, _ => F_UNE };
        return ins_fcmp(p, t, a, b);
    }
    let signed = kind_of(q) != TY_POINTER && kind_of(q) != TY_BOOL && is_integer(q) && is_signed(q);
    let p = match op {
        B_LT => if signed { GIR_SLT } else { GIR_ULT }, B_GT => if signed { GIR_SGT } else { GIR_UGT },
        B_LE => if signed { GIR_SLE } else { GIR_ULE }, B_GE => if signed { GIR_SGE } else { GIR_UGE },
        B_EQ => GIR_EQ, _ => GIR_NE,
    };
    return ins_icmp(p, t, a, b);
}

fn is_cmp_op(op: i64) -> bool { op >= B_LT && op <= B_NE }

recursive fn ex_binary(n: u32) -> u32 {
    let nd = nodes[n];
    let op = nd.op as i64;
    if op == B_COMMA {
        ex_ignore(nd.a);
        return ex_val(nd.b);
    }
    if op == B_LAND || op == B_LOR {
        let b = ex_bool(n);
        return int_cast(b, GIR_T_I1, vty(nd.ty), false);
    }
    let at = nty(nd.a);
    if is_cmp_op(op) {
        if is_vector(at) { return vec_compare(n); }
        if is_complex(at) || is_complex(nty(nd.b)) {
            let b = cplx_compare(n);
            return int_cast(b, GIR_T_I1, vty(nd.ty), false);
        }
        let x = ex_val(nd.a);
        let y = ex_val(nd.b);
        let c = compare(op, at, x, y);
        return int_cast(c, GIR_T_I1, vty(nd.ty), false);
    }
    if op == B_PTRADD || op == B_PTRSUB {
        let p = ex_val(nd.a);
        let i = ex_val(nd.b);
        return ptr_add(p, tbase(at), i, nty(nd.b), op == B_PTRSUB);
    }
    if op == B_PTRDIFF {
        let p = ex_val(nd.a);
        let r = ex_val(nd.b);
        let pi = ins_ptrtoint(p, GIR_T_I64);
        let ri = ins_ptrtoint(r, GIR_T_I64);
        let d = ins_bin(GIR_SUB, GIR_T_I64, pi, ri);
        let ok, es, ev = elem_size(tbase(at));
        var res = d;
        if !ok { res = ins_bin(GIR_SDIV, GIR_T_I64, d, ev); }
        else if es != 1 { res = ins_bin(GIR_SDIV, GIR_T_I64, d, c_i64(es)); }
        return conv(res, t_long, nd.ty);
    }
    let x = ex_val(nd.a);
    let y = ex_val(nd.b);
    return arith(op, nd.ty, x, y);
}

recursive fn vec_compare(n: u32) -> u32 {
    let nd = nodes[n];
    let x = ex_val(nd.a);
    let y = ex_val(nd.b);
    let t = vtype(x);
    let lanes = m_types[t].n;
    let et = m_types[t].elems;
    let mt = ty_vec(lanes, GIR_T_I1);
    let fp = tcls(et) == C_FP;
    let op = nd.op as i64;
    let q = nty(nd.a);
    var c: u32 = 0;
    if fp {
        let p = match op { B_LT => F_OLT, B_GT => F_OGT, B_LE => F_OLE, B_GE => F_OGE, B_EQ => F_OEQ, _ => F_UNE };
        c = emit(GIR_FCMP, mt, p, 0, t, x, y, 0);
    } else {
        let signed = is_signed(tbase(q));
        let p = match op {
            B_LT => if signed { GIR_SLT } else { GIR_ULT }, B_GT => if signed { GIR_SGT } else { GIR_UGT },
            B_LE => if signed { GIR_SLE } else { GIR_ULE }, B_GE => if signed { GIR_SGE } else { GIR_UGE },
            B_EQ => GIR_EQ, _ => GIR_NE,
        };
        c = emit(GIR_ICMP, mt, p, 0, t, x, y, 0);
    }
    // sext <n x i1> to the result vector type
    let rt = vty(nd.ty);
    return emit(GIR_SEXT, rt, 0, 0, mt, c, 0, 0);
}

// == / != on complex values.
recursive fn cplx_compare(n: u32) -> u32 {
    let nd = nodes[n];
    let ar, ai = cplx_or_real(nd.a);
    let xr, xi = cplx_or_real(nd.b);
    let q = nty(nd.a);
    let et = if is_complex(q) { cplx_elem(q) } else { unqual(q) };
    let r = compare(nd.op as i64, et, ar, xr);
    let i = compare(nd.op as i64, et, ai, xi);
    if nd.op == B_EQ { return ins_bin(GIR_AND, GIR_T_I1, r, i); }
    return ins_bin(GIR_OR, GIR_T_I1, r, i);
}

recursive fn cplx_or_real(n: u32) -> u32, u32 {
    if is_complex(nty(n)) { return ex_cplx(n); }
    let v = ex_val(n);
    return v, c_zero(vtype(v));
}

// ------------------------------------------------------------ conditions

// The value of a scalar condition as i1.
recursive fn ex_bool(n: u32) -> u32 {
    if !dbg_on() { return ex_bool1(n); }
    if dbg_loopcond {
        // the top of a loop condition: a comparison is at its operator, the
        // conversion of any other scalar at the loop
        dbg_loopcond = false;
        let nd = nodes[n];
        let own = (nd.kind == N_BINARY && (is_cmp_op(nd.op as i64) || nd.op == B_LAND || nd.op == B_LOR)) ||
                  (nd.kind == N_UNARY && nd.op == U_NOT);
        var v: u32 = 0;
        if own {
            let s0 = push_loc(expr_loc(n));
            v = ex_bool1(n);
            pop_loc(s0);
        } else {
            v = ex_bool1(n);
        }
        dbg_loopcond = true;
        return v;
    }
    let saved = push_loc(expr_loc(n));
    let v = ex_bool1(n);
    pop_loc(saved);
    return v;
}

recursive fn ex_bool1(n: u32) -> u32 {
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_BINARY && (nd.op == B_LAND || nd.op == B_LOR) {
        let land = nd.op == B_LAND;
        let ok, cv = const_bool(nd.a);
        if ok {
            // constant left operand
            if land && !cv { return c_false(); }
            if !land && cv { return c_true(); }
            return ex_bool(nd.b);
        }
        let rhs = new_block();
        let end = new_block();
        let l = ex_bool(nd.a);
        let pl = cur_blk;
        if land { condbr(l, rhs, end); } else { condbr(l, end, rhs); }
        start_block(rhs);
        let r = ex_bool(nd.b);
        let pr = cur_blk;
        if cur_blk >= 0 { br(end); }
        start_block(end);
        if pl < 0 && pr < 0 { return c_false(); }
        let s = m_opnds.len as! u32;
        var np: u32 = 0;
        if pl >= 0 { op_ref(if land { c_false() } else { c_true() }); op_blk(pl as! u32); np++; }
        if pr >= 0 { op_ref(r); op_blk(pr as! u32); np++; }
        return emit(GIR_PHI, GIR_T_I1, 0, 0, 0, 0, s, np);
    }
    if k == N_UNARY && nd.op == U_NOT {
        let b = ex_bool(nd.a);
        return ins_bin(GIR_XOR, GIR_T_I1, b, c_true());
    }
    if k == N_BINARY && is_cmp_op(nd.op as i64) && !is_vector(nty(nd.a)) {
        if is_complex(nty(nd.a)) || is_complex(nty(nd.b)) { return cplx_compare(n); }
        let x = ex_val(nd.a);
        let y = ex_val(nd.b);
        return compare(nd.op as i64, nty(nd.a), x, y);
    }
    if is_complex(nd.ty) {
        let re, im = ex_cplx(n);
        let et = cplx_elem(nd.ty);
        let a = to_bool(re, et);
        let b = to_bool(im, et);
        return ins_bin(GIR_OR, GIR_T_I1, a, b);
    }
    let v = ex_val(n);
    return to_bool(v, nd.ty);
}

fn has_label_or_side(n: u32) -> bool { has_side_effects(n) && nkind(n) != N_INT }

// Branch to t if n (a scalar) is nonzero, else to f.
recursive fn ex_cond(n: u32, t: u32, f: u32) {
    let nd = nodes[n];
    let k = nd.kind as i64;
    let ok, cv = const_bool(n);
    if ok {
        br(if cv { t } else { f });
        return;
    }
    if k == N_BINARY && (nd.op == B_LAND || nd.op == B_LOR) {
        // in a loop condition (a value for clang) the branches are at the
        // operator; in an if, at the whole condition (already current)
        let lc = dbg_loopcond;
        let saved = if dbg_on() && lc { push_loc(nd.loc) } else { 0 };
        dbg_loopcond = false;
        let mid = new_block();
        if nd.op == B_LAND { ex_cond(nd.a, mid, f); } else { ex_cond(nd.a, t, mid); }
        start_block(mid);
        ex_cond(nd.b, t, f);
        dbg_loopcond = lc;
        if dbg_on() && lc { pop_loc(saved); }
        return;
    }
    if k == N_UNARY && nd.op == U_NOT {
        ex_cond(nd.a, f, t);
        return;
    }
    if k == N_ICAST && (nd.op == CK_INTEGRAL || nd.op == CK_INT2BOOL) && is_integer(nty(nd.a)) && nkind(nd.a) == N_BINARY &&
       (nodes[nd.a].op == B_LAND || nodes[nd.a].op == B_LOR || is_cmp_op(nodes[nd.a].op as i64)) {
        ex_cond(nd.a, t, f);
        return;
    }
    let b = ex_bool(n);
    if is_const(b) {
        br(if c_lo(b) != 0 { t } else { f });
        return;
    }
    if cur_blk < 0 { return; }
    condbr(b, t, f);
}

// The value of a condition that is a constant without side effects.
fn const_bool(n: u32) -> bool, bool {
    if !pure_const(n) { return false, false; }
    return fold_bool(n);
}

// A constant without side effects (fold_int / fold_float accepted it).
recursive fn pure_const(n: u32) -> bool {
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_INT || k == N_FLOAT || k == N_SIZEOF || k == N_OFFSETOF { return true; }
    if k == N_ICAST || k == N_CAST || k == N_UNARY { return pure_const(nd.a); }
    if k == N_BINARY {
        if nd.op == B_COMMA { return false; }
        return pure_const(nd.a) && pure_const(nd.b);
    }
    if k == N_COND { return pure_const(nd.a) && (nd.b == 0 || pure_const(nd.b)) && pure_const(nd.c); }
    return false;
}

// ------------------------------------------------------------ ?:

recursive fn ex_condexpr(n: u32, dst: u32) -> u32 {
    let nd = nodes[n];
    let q = nd.ty;
    let vk = vkind(q);
    if nd.b == 0 {
        // GNU a ?: c
        let v = ex_val(nd.a);
        let tb = new_block();
        let fb = new_block();
        let end = new_block();
        let c = to_bool(v, nty(nd.a));
        let cv = conv(v, nty(nd.a), q);
        condbr(c, tb, fb);
        start_block(tb);
        let pt = cur_blk;
        br(end);
        start_block(fb);
        let w = ex_val(nd.c);
        let pf = cur_blk;
        if cur_blk >= 0 { br(end); }
        start_block(end);
        if vk == VK_VOID { return NONE; }
        return phi2(vtype(cv), cv, pt, w, pf);
    }
    let ok, cv = const_bool(nd.a);
    if ok && !contains_label(nd.b) && !contains_label(nd.c) {
        let arm = if cv { nd.b } else { nd.c };
        if vk == VK_AGG { ex_agg(arm, dst); return NONE; }
        if vk == VK_VOID { ex_ignore(arm); return NONE; }
        return ex_val(arm);
    }
    let tb = new_block();
    let fb = new_block();
    let end = new_block();
    ex_cond(nd.a, tb, fb);
    start_block(tb);
    var x: u32 = NONE;
    if vk == VK_AGG { ex_agg(nd.b, dst); } else if vk == VK_VOID { ex_ignore(nd.b); } else { x = ex_val(nd.b); }
    let pt = cur_blk;
    if cur_blk >= 0 { br(end); }
    start_block(fb);
    var y: u32 = NONE;
    if vk == VK_AGG { ex_agg(nd.c, dst); } else if vk == VK_VOID { ex_ignore(nd.c); } else { y = ex_val(nd.c); }
    let pf = cur_blk;
    if cur_blk >= 0 { br(end); }
    start_block(end);
    if vk != VK_SCALAR { return NONE; }
    let t = if x != NONE { vtype(x) } else if y != NONE { vtype(y) } else { vty(q) };
    return phi2(t, x, pt, y, pf);
}

fn phi2(t: u32, x: u32, px: i64, y: u32, py: i64) -> u32 {
    if px < 0 && py < 0 { return c_zero(t); }
    if px < 0 { return y; }
    if py < 0 { return x; }
    let s = m_opnds.len as! u32;
    op_ref(x);
    op_blk(px as! u32);
    op_ref(y);
    op_blk(py as! u32);
    return emit(GIR_PHI, t, 0, 0, 0, 0, s, 2);
}

// ------------------------------------------------------------ assignment

recursive fn ex_assign(n: u32) -> u32 {
    let nd = nodes[n];
    let lq = nty(nd.a);
    let vk = vkind(lq);
    if vk == VK_AGG {
        let l = ex_lv(nd.a);
        assign_agg(l.addr, lq, nd.b);
        return NONE;
    }
    if vk == VK_COMPLEX {
        let r, i = assign_cplx(n);
        return NONE;
    }
    if nd.op == 0 {
        if quals(lq) & Q_ATOMIC != 0 {
            let v = ex_val(nd.b);
            let l = ex_lv(nd.a);
            atomic_store_lv(l, unqual(lq), v);
            return v;
        }
        // clang evaluates the right side first for scalars
        let v = ex_val(nd.b);
        let l = ex_lv(nd.a);
        return lv_store(l, v);
    }
    // compound assignment: load, convert to the computation type, op, convert back
    let ct = nd.c;
    let op = nd.op as i64;
    if is_complex(ct) { return assign_cplx_to_real(n); }
    if quals(lq) & Q_ATOMIC != 0 { return atomic_compound(n); }
    let rhs = ex_val(nd.b);
    let l = ex_lv(nd.a);
    let old = lv_load(l);
    var r: u32 = 0;
    if op == B_PTRADD || op == B_PTRSUB {
        r = ptr_add(old, tbase(unqual(lq)), rhs, nty(nd.b), op == B_PTRSUB);
    } else {
        let ov = conv(old, unqual(lq), ct);
        r = arith(op, ct, ov, rhs);
        r = conv(r, ct, unqual(lq));
    }
    return lv_store(l, r);
}

// dst = value of aggregate expression b (type q).
recursive fn assign_agg(dst: u32, q: u32, b: u32) {
    let k = nkind(b);
    if k == N_CALL || k == N_STMTEXPR || k == N_COND || k == N_VAARG {
        // the call may read the destination: through a temporary
        let tmp = alloca(type_size(q), type_align(q));
        ex_agg(b, tmp);
        mem_copy(dst, tmp, type_size(q), quals(q) & Q_VOLATILE != 0);
        return;
    }
    ex_agg(b, dst);
}

// Complex assignment; returns the stored value.
recursive fn assign_cplx(n: u32) -> u32, u32 {
    let nd = nodes[n];
    let lq = unqual(nty(nd.a));
    if nd.op == 0 {
        let re, im = ex_cplx(nd.b);
        let l = ex_lv(nd.a);
        store_cplx(lq, re, im, l.addr, l.vol);
        return re, im;
    }
    let ct = nd.c;
    let xr, xi = cplx_or_real(nd.b);
    let l = ex_lv(nd.a);
    let ar, ai = load_cplx(lq, l.addr, l.vol);
    let cr = conv(ar, cplx_elem(lq), cplx_elem(ct));
    let ci = conv(ai, cplx_elem(lq), cplx_elem(ct));
    let rr, ri = cplx_arith(nd.op as i64, ct, cr, ci, true, xr, xi, is_complex(nty(nd.b)));
    let sr = conv(rr, cplx_elem(ct), cplx_elem(lq));
    let si = conv(ri, cplx_elem(ct), cplx_elem(lq));
    store_cplx(lq, sr, si, l.addr, l.vol);
    return sr, si;
}

// real op= complex: computed in the complex type, the real part stored.
recursive fn assign_cplx_to_real(n: u32) -> u32 {
    let nd = nodes[n];
    let lq = unqual(nty(nd.a));
    let ct = nd.c;
    let xr, xi = ex_cplx(nd.b);
    let l = ex_lv(nd.a);
    let old = lv_load(l);
    let ar = conv(old, lq, cplx_elem(ct));
    let rr, ri = cplx_arith(nd.op as i64, ct, ar, c_zero(vtype(ar)), false, xr, xi, true);
    return lv_store(l, conv(rr, cplx_elem(ct), lq));
}

// ------------------------------------------------------------ complex values

recursive fn ex_cplx(n: u32) -> u32, u32 {
    if !dbg_on() { return ex_cplx1(n); }
    let saved = push_loc(visit_loc(n));
    let re, im = ex_cplx1(n);
    pop_loc(saved);
    return re, im;
}

recursive fn ex_cplx1(n: u32) -> u32, u32 {
    let nd = nodes[n];
    let k = nd.kind as i64;
    let q = nd.ty;
    if k == N_ICAST || k == N_CAST {
        let ck = nd.op as i64;
        if ck == CK_LVAL2RVAL {
            let l = ex_lv(nd.a);
            return load_cplx(q, l.addr, l.vol);
        }
        if ck == CK_REAL2COMPLEX {
            let v = ex_val(nd.a);
            let et = cplx_elem(q);
            let r = conv(v, nty(nd.a), et);
            return r, c_zero(vty(et));
        }
        if ck == CK_COMPLEXCAST {
            let re, im = ex_cplx(nd.a);
            let fe = cplx_elem(nty(nd.a));
            let te = cplx_elem(q);
            return conv(re, fe, te), conv(im, fe, te);
        }
        if ck == CK_NOOP || ck == CK_ATOMIC || ck == CK_BITCAST { return ex_cplx(nd.a); }
    }
    if k == N_BUILTIN && nd.op == BI_IMAG_CONST {
        let v = ex_val(nd.a);
        let et = cplx_elem(q);
        let iv = conv(v, nty(nd.a), et);
        return c_zero(vty(et)), iv;
    }
    if k == N_BINARY {
        let op = nd.op as i64;
        if op == B_COMMA {
            ex_ignore(nd.a);
            return ex_cplx(nd.b);
        }
        let ac = is_complex(nty(nd.a));
        let bc = is_complex(nty(nd.b));
        let ar, ai = cplx_or_real(nd.a);
        let xr, xi = cplx_or_real(nd.b);
        return cplx_arith(op, q, ar, ai, ac, xr, xi, bc);
    }
    if k == N_UNARY {
        let op = nd.op as i64;
        if op == U_PLUS || op == U_EXTENSION { return ex_cplx(nd.a); }
        if op == U_NEG {
            let re, im = ex_cplx(nd.a);
            return neg_any(re), neg_any(im);
        }
        if op == U_BITNOT {
            let re, im = ex_cplx(nd.a);
            return re, neg_any(im);
        }
        if op == U_PREINC || op == U_PREDEC || op == U_POSTINC || op == U_POSTDEC {
            let l = ex_lv(nd.a);
            let re, im = load_cplx(q, l.addr, l.vol);
            let et = cplx_elem(q);
            let one = conv(c_i32(1), t_int, et);
            let inc = op == U_PREINC || op == U_POSTINC;
            let nr = arith(if inc { B_ADD } else { B_SUB }, et, re, one);
            store_cplx(q, nr, im, l.addr, l.vol);
            if op == U_POSTINC || op == U_POSTDEC { return re, im; }
            return nr, im;
        }
    }
    if k == N_ASSIGN { return assign_cplx(n); }
    if k == N_COND {
        let tb = new_block();
        let fb = new_block();
        let end = new_block();
        if nd.b == 0 {
            // GNU a ?: c on complex
            let tmp = alloca(type_size(q), type_align(q));
            let ar, ai = ex_cplx(nd.a);
            store_cplx(q, ar, ai, tmp, false);
            let et = cplx_elem(q);
            let c = ins_bin(GIR_OR, GIR_T_I1, to_bool(ar, et), to_bool(ai, et));
            condbr(c, end, fb);
            start_block(fb);
            let cr, ci = ex_cplx(nd.c);
            store_cplx(q, cr, ci, tmp, false);
            start_block(end);
            br(tb);
            start_block(tb);
            return load_cplx(q, tmp, false);
        }
        ex_cond(nd.a, tb, fb);
        start_block(tb);
        let xr, xi = ex_cplx(nd.b);
        let pt = cur_blk;
        if cur_blk >= 0 { br(end); }
        start_block(fb);
        let yr, yi = ex_cplx(nd.c);
        let pf = cur_blk;
        if cur_blk >= 0 { br(end); }
        start_block(end);
        let et = vty(cplx_elem(q));
        let r = phi2(et, xr, pt, yr, pf);
        let i = phi2(et, xi, pt, yi, pf);
        return r, i;
    }
    if k == N_CALL || k == N_STMTEXPR || k == N_VAARG || (k == N_BUILTIN && nd.op == BI_CALL) || k == N_INITLIST || k == N_ZEROINIT {
        if k == N_INITLIST && nd.c == 2 {
            let et = cplx_elem(q);
            let r = conv(ex_val(nlist[nd.v]), nty(nlist[nd.v]), et);
            let i = conv(ex_val(nlist[nd.v + 1]), nty(nlist[nd.v + 1]), et);
            return r, i;
        }
        if k == N_ZEROINIT {
            let et = vty(cplx_elem(q));
            return c_zero(et), c_zero(et);
        }
        let tmp = alloca(type_size(q), type_align(q));
        if k == N_CALL { ex_call(n, tmp); }
        else if k == N_STMTEXPR { ex_stmtexpr(n, tmp); }
        else if k == N_BUILTIN { ex_builtin(n, tmp); }
        else if k == N_INITLIST { ex_agg(n, tmp); }
        else { mem_copy(tmp, va_arg_addr(n), type_size(q), false); }
        return load_cplx(q, tmp, false);
    }
    if is_lvalue(n) || k == N_MEMBER || k == N_INDEX {
        let l = ex_lv(n);
        return load_cplx(q, l.addr, l.vol);
    }
    bug("ex_cplx", n);
    return c_zero(GIR_T_F64), c_zero(GIR_T_F64);
}

fn neg_any(v: u32) -> u32 {
    let t = vtype(v);
    if tcls(t) == C_FP || tcls(t) == C_X87 { return ins_fneg(v); }
    return ins_bin(GIR_SUB, t, c_zero(t), v);
}

fn cplx_lib_suffix(t: u32) -> const u8[:] { if t == GIR_T_F32 { "sc3" } else if t == GIR_T_F64 { "dc3" } else { "xc3" } }

// A call of __mul?c3 / __div?c3: returns the complex result as two values.
fn cplx_libcall(div: bool, t: u32, a: u32, b: u32, c: u32, d: u32) -> u32, u32 {
    var nm: u8[>..] = [];
    nm.append(if div { "__div" } else { "__mul" });
    nm.append(cplx_lib_suffix(t));
    var rt: u32 = 0;
    if t == GIR_T_F32 { rt = GIR_T_F64; }
    else if t == GIR_T_F64 { rt = ty_pair(GIR_T_F64, GIR_T_F64, 8); }
    else { rt = ty_pair(GIR_T_F80, GIR_T_F80, 16); }
    let r = libcall4(nm, rt, a, b, c, d);
    if t == GIR_T_F32 {
        let v = ins_bitcast(r, ty_vec(2, GIR_T_F32));
        let x = emit(GIR_EXTRACTELT, GIR_T_F32, 0, 0, vtype(v), v, c_i32(0), 0);
        let y = emit(GIR_EXTRACTELT, GIR_T_F32, 0, 0, vtype(v), v, c_i32(1), 0);
        return x, y;
    }
    let x = emit(GIR_EXTRACTVALUE, t, 0, 0, 0, r, 0, 0);
    let y = emit(GIR_EXTRACTVALUE, t, 0, 0, 0, r, if t == GIR_T_F64 { 8 } else { 16 }, 0);
    return x, y;
}

// Complex arithmetic (clang's ComplexExprEmitter): operands may be real
// (ac / bc false: imaginary part zero, not used).
fn cplx_arith(op: i64, q: u32, ar: u32, ai: u32, ac: bool, yr: u32, yi: u32, bc: bool) -> u32, u32 {
    let et = cplx_elem(q);
    let t = vty(et);
    let fp = tcls(t) == C_FP || tcls(t) == C_X87;
    if op == B_ADD || op == B_SUB {
        let r = arith(op, et, ar, yr);
        var i: u32 = 0;
        if ac && bc { i = arith(op, et, ai, yi); }
        else if ac { i = ai; }
        else if op == B_ADD { i = yi; }
        else { i = neg_any(yi); }
        return r, i;
    }
    if op == B_MUL {
        if ac && bc {
            let ac_ = arith(B_MUL, et, ar, yr);
            let bd = arith(B_MUL, et, ai, yi);
            let ad = arith(B_MUL, et, ar, yi);
            let bcv = arith(B_MUL, et, ai, yr);
            let r = arith(B_SUB, et, ac_, bd);
            let i = arith(B_ADD, et, ad, bcv);
            if !fp || t == GIR_T_F16 { return r, i; }
            // NaN check, then the library call
            let cont = new_block();
            let inan = new_block();
            let lib = new_block();
            let isr = ins_fcmp(F_UNO, t, r, r);
            let b0 = cur_blk;
            condbr(isr, inan, cont);
            start_block(inan);
            let isi = ins_fcmp(F_UNO, t, i, i);
            let b1 = cur_blk;
            condbr(isi, lib, cont);
            start_block(lib);
            let lr, li = cplx_libcall(false, t, ar, ai, yr, yi);
            let b2 = cur_blk;
            br(cont);
            start_block(cont);
            let s = m_opnds.len as! u32;
            op_ref(r); op_blk(b0 as! u32); op_ref(r); op_blk(b1 as! u32); op_ref(lr); op_blk(b2 as! u32);
            let pr = emit(GIR_PHI, t, 0, 0, 0, 0, s, 3);
            let s2 = m_opnds.len as! u32;
            op_ref(i); op_blk(b0 as! u32); op_ref(i); op_blk(b1 as! u32); op_ref(li); op_blk(b2 as! u32);
            let pi = emit(GIR_PHI, t, 0, 0, 0, 0, s2, 3);
            return pr, pi;
        }
        if ac { return arith(B_MUL, et, ar, yr), arith(B_MUL, et, ai, yr); }
        return arith(B_MUL, et, ar, yr), arith(B_MUL, et, ar, yi);
    }
    if op == B_DIV {
        if !bc {
            if ac { return arith(B_DIV, et, ar, yr), arith(B_DIV, et, ai, yr); }
            return arith(B_DIV, et, ar, yr), c_zero(t);
        }
        if fp && t != GIR_T_F16 {
            let xi = if ac { ai } else { c_zero(t) };
            return cplx_libcall(true, t, ar, xi, yr, yi);
        }
        // integer complex division: (a+yi)/(c+di) = ((ac+bd) + (bc-ad)i) / (cc+dd)
        let xi = if ac { ai } else { c_zero(t) };
        let cc = arith(B_MUL, et, yr, yr);
        let dd = arith(B_MUL, et, yi, yi);
        let den = arith(B_ADD, et, cc, dd);
        let acv = arith(B_MUL, et, ar, yr);
        let bdv = arith(B_MUL, et, xi, yi);
        let bcv = arith(B_MUL, et, xi, yr);
        let adv = arith(B_MUL, et, ar, yi);
        let rn = arith(B_ADD, et, acv, bdv);
        let inn = arith(B_SUB, et, bcv, adv);
        return arith(B_DIV, et, rn, den), arith(B_DIV, et, inn, den);
    }
    return ar, ai;
}

// ------------------------------------------------------------ aggregates

recursive fn ex_agg(n: u32, dst: u32) {
    if !dbg_on() { ex_agg1(n, dst); return; }
    let saved = push_loc(visit_loc(n));
    ex_agg1(n, dst);
    pop_loc(saved);
}

recursive fn ex_agg1(n: u32, dst: u32) {
    let nd = nodes[n];
    let k = nd.kind as i64;
    let q = nd.ty;
    if k == N_ICAST || k == N_CAST {
        let ck = nd.op as i64;
        if ck == CK_LVAL2RVAL {
            let l = ex_lv(nd.a);
            if dst != NONE { mem_copy(dst, l.addr, type_size(q), l.vol); }
            return;
        }
        if ck == CK_NOOP || ck == CK_ATOMIC || ck == CK_BITCAST {
            if vkind(nty(nd.a)) == VK_AGG { ex_agg(nd.a, dst); return; }
            if dst == NONE { ex_ignore(nd.a); return; }
            store_any(nty(nd.a), nd.a, dst);
            return;
        }
        if ck == CK_TOUNION {
            if dst == NONE { ex_ignore(nd.a); return; }
            store_any(nty(nd.a), nd.a, dst);
            return;
        }
        if ck == CK_TOVOID { ex_ignore(nd.a); return; }
    }
    if k == N_CALL { ex_call(n, dst); return; }
    if k == N_ASSIGN {
        let l = ex_lv(nd.a);
        assign_agg(l.addr, nty(nd.a), nd.b);
        if dst != NONE { mem_copy(dst, l.addr, type_size(q), false); }
        return;
    }
    if k == N_COND { ex_condexpr(n, dst); return; }
    if k == N_BINARY && nd.op == B_COMMA {
        ex_ignore(nd.a);
        ex_agg(nd.b, dst);
        return;
    }
    if k == N_STMTEXPR { ex_stmtexpr(n, dst); return; }
    if k == N_COMPLIT {
        let p = ex_complit(n);
        if dst != NONE { mem_copy(dst, p, type_size(q), false); }
        return;
    }
    if k == N_INITLIST {
        if dst == NONE {
            let tmp = alloca(type_size(q), type_align(q));
            init_local(tmp, q, n);
            return;
        }
        init_local(dst, q, n);
        return;
    }
    if k == N_ZEROINIT {
        if dst != NONE { mem_set(dst, c_i8(0), type_size(q), false); }
        return;
    }
    if k == N_STRING {
        if dst != NONE { init_local(dst, q, n); }
        return;
    }
    if k == N_VAARG {
        let p = va_arg_addr(n);
        if dst != NONE { mem_copy(dst, p, type_size(q), false); }
        return;
    }
    if k == N_BUILTIN { ex_builtin(n, dst); return; }
    if is_lvalue(n) || k == N_MEMBER || k == N_INDEX {
        let l = ex_lv(n);
        if dst != NONE { mem_copy(dst, l.addr, type_size(q), l.vol); }
        return;
    }
    bug("ex_agg", n);
}

// ------------------------------------------------------------ compound literals

recursive fn ex_complit(n: u32) -> u32 {
    let nd = nodes[n];
    let s = nd.b as i64;
    if syms[s].flags & SF_FILESCOPE != 0 || syms[s].sc == SC_STATIC || f_sym < 0 {
        return gref(complit_global(n));
    }
    var p = sym_gen[s].addr;
    let q = syms[s].ty;
    if p == NONE {
        p = alloca(type_size(q), local_align(s, q));
        sym_gen[s].addr = p;
    }
    init_object(p, q, nd.a);
    return p;
}

// Stores the initializer `init` (of an object of type q) at p.
recursive fn init_object(p: u32, q: u32, init: u32) {
    let vk = vkind(q);
    if vk == VK_AGG { init_local(p, q, init); return; }
    if vk == VK_COMPLEX {
        let re, im = ex_cplx(init);
        store_cplx(q, re, im, p, false);
        return;
    }
    let v = ex_val(init);
    if quals(q) & Q_ATOMIC != 0 { store_c(unqual(q), v, p, false); return; }
    store_c(q, v, p, false);
}

// ------------------------------------------------------------ statement expressions

recursive fn ex_stmtexpr(n: u32, dst: u32) -> u32 {
    let nd = nodes[n];
    let body = nd.a;
    let bn = nodes[body];
    let cnt = bn.c as i64;
    let q = nd.ty;
    var res: u32 = NONE;
    push_cleanup_scope();
    // the compound statement is a scope (clang's LexicalScope)
    scope_enter(body);
    for i in cnt {
        let s = nlist[bn.v + i];
        if i == cnt - 1 && !is_void(q) {
            // the value: the last statement (under labels) is an expression
            var e = s;
            while nkind(e) == N_LABEL {
                gen_label(nodes[e].a as i64);
                if dbg_on() { dbg_label(nodes[e].a as i64, label_block(nodes[e].a as i64), nodes[e].loc); }
                e = nodes[e].b;
            }
            if nkind(e) == N_EXPR {
                let x = nodes[e].a;
                let vk = vkind(q);
                if vk == VK_AGG { ex_agg(x, dst); }
                else if vk == VK_COMPLEX {
                    let re, im = ex_cplx(x);
                    if dst != NONE { store_cplx(q, re, im, dst, false); }
                } else {
                    res = ex_val(x);
                }
            } else {
                gen_stmt(e);
            }
        } else {
            gen_stmt(s);
        }
    }
    scope_leave();
    pop_cleanup_scope(true);
    if res == NONE && vkind(q) == VK_SCALAR { return c_zero(vty(q)); }
    return res;
}
