// goosecc B2: instruction helpers. Operations on constants are folded as
// LLVM's IRBuilder (ConstantFolder) folds them for clang at -O0; C scalar
// conversions; loads, stores, address arithmetic and block copies.

namespace gen;

import std;
import .common;
import .types;
import .ast;
import .sema;

fn mask_of(bits: u32) -> u64 {
    if bits >= 64 { return 0xFFFFFFFFFFFFFFFF; }
    return ((1 as u64) << (bits as! u64)) - 1;
}

fn sext_of(v: u64, bits: u32) -> i64 {
    if bits >= 64 { return v as! i64; }
    let sh = (64 - bits) as! u64;
    return ((v << sh) as! i64) >> sh;
}

// ------------------------------------------------------- integer ops

fn ins_bin(op: i64, t: u32, a: u32, b: u32) -> u32 {
    if is_const(a) && is_const(b) && tcls(t) == C_INT && t != GIR_T_PTR {
        let bits = tbits(t);
        let x = c_lo(a);
        let y = c_lo(b);
        let m = mask_of(bits);
        var ok = true;
        var r: u64 = 0;
        if op == GIR_ADD { r = x + y; }
        else if op == GIR_SUB { r = x - y; }
        else if op == GIR_MUL { r = x * y; }
        else if op == GIR_AND { r = x & y; }
        else if op == GIR_OR { r = x | y; }
        else if op == GIR_XOR { r = x ^ y; }
        else if op == GIR_SHL { if y < bits as u64 { r = x << y; } else { ok = false; } }
        else if op == GIR_LSHR { if y < bits as u64 { r = (x & m) >> y; } else { ok = false; } }
        else if op == GIR_ASHR { if y < bits as u64 { r = (sext_of(x, bits) >> y) as! u64; } else { ok = false; } }
        else if op == GIR_UDIV || op == GIR_UREM {
            if (y & m) == 0 { ok = false; }
            else if op == GIR_UDIV { r = (x & m) / (y & m); } else { r = (x & m) % (y & m); }
        } else if op == GIR_SDIV || op == GIR_SREM {
            let sx = sext_of(x, bits);
            let sy = sext_of(y, bits);
            if sy == 0 || (sy == -1 && sx == sext_of((1 as u64) << ((bits - 1) as! u64), bits)) { ok = false; }
            else if op == GIR_SDIV { r = (sx / sy) as! u64; } else { r = rem(sx, sy) as! u64; }
        } else { ok = false; }
        if ok { return c_int(r & m, t); }
    }
    return emit(op, t, 0, 0, 0, a, b, 0);
}

fn ins_icmp(pred: i64, t: u32, a: u32, b: u32) -> u32 {
    if is_const(a) && is_const(b) && tcls(t) == C_INT {
        let bits = tbits(t);
        let m = mask_of(bits);
        let x = c_lo(a) & m;
        let y = c_lo(b) & m;
        let sx = sext_of(x, bits);
        let sy = sext_of(y, bits);
        let r = match pred {
            GIR_EQ => x == y, GIR_NE => x != y, GIR_UGT => x > y, GIR_UGE => x >= y, GIR_ULT => x < y,
            GIR_ULE => x <= y, GIR_SGT => sx > sy, GIR_SGE => sx >= sy, GIR_SLT => sx < sy, _ => sx <= sy,
        };
        return c_int(if r { 1 } else { 0 }, GIR_T_I1);
    }
    return emit(GIR_ICMP, GIR_T_I1, pred, 0, t, a, b, 0);
}

fn ins_select(c: u32, a: u32, b: u32) -> u32 {
    if is_const(c) { return if c_lo(c) != 0 { a } else { b }; }
    return emit(GIR_SELECT, vtype(a), 0, 0, 0, c, a, b);
}

// Integer resize: zext/sext/trunc from type f to type t.
fn int_cast(v: u32, f: u32, t: u32, signed: bool) -> u32 {
    if f == t { return v; }
    let fb = tbits(f);
    let tb = tbits(t);
    if is_const(v) {
        let c = m_consts[cidx(v)];
        if tcls(t) == C_INT && tcls(f) == C_INT {
            var x = c.lo & mask_of(fb);
            if signed && tb > fb { x = sext_of(x, fb) as! u64; }
            return c_int(x, t);
        }
        if tcls(t) == C_INT2 && tcls(f) == C_INT {
            var lo = c.lo & mask_of(fb);
            var hi: u64 = 0;
            if signed && sext_of(lo, fb) < 0 { lo = sext_of(lo, fb) as! u64; hi = 0xFFFFFFFFFFFFFFFF; }
            return c_wide(lo, hi, t);
        }
        if tcls(t) == C_INT && tcls(f) == C_INT2 { return c_int(c.lo, t); }
    }
    if tb > fb { return emit(if signed { GIR_SEXT } else { GIR_ZEXT }, t, 0, 0, f, v, 0, 0); }
    if tb < fb { return emit(GIR_TRUNC, t, 0, 0, f, v, 0, 0); }
    return v;
}

fn ins_zext(v: u32, t: u32) -> u32 { int_cast(v, vtype(v), t, false) }

fn ins_ptrtoint(v: u32, t: u32) -> u32 {
    if is_const(v) { return c_int(c_lo(v), t); }
    return emit(GIR_PTRTOINT, t, 0, 0, GIR_T_PTR, v, 0, 0);
}
fn ins_inttoptr(v: u32) -> u32 {
    let f = vtype(v);
    if is_const(v) && tcls(f) == C_INT { return c_int(c_lo(v), GIR_T_PTR); }
    return emit(GIR_INTTOPTR, GIR_T_PTR, 0, 0, f, v, 0, 0);
}

fn ins_bitcast(v: u32, t: u32) -> u32 {
    let f = vtype(v);
    if f == t { return v; }
    return emit(GIR_BITCAST, t, 0, 0, f, v, 0, 0);
}

// ------------------------------------------------------- floating point

fn f32_bits(d: f64) -> u64 { f64_to_f32bits(d) as u64 }

extern fn f64_to_f32bits(d: f64) -> u32 = "goosecc_f64_to_f32bits";
extern fn f32bits_to_f64(b: u32) -> f64 = "goosecc_f32bits_to_f64";
extern fn f64_to_f16bits(d: f64) -> u32 = "goosecc_f64_to_f16bits";
extern fn f16bits_to_f64(b: u32) -> f64 = "goosecc_f16bits_to_f64";

// An FP constant of type t with value d (f80: the exact extension).
fn c_double(d: f64, t: u32) -> u32 {
    if t == GIR_T_F64 { return c_fp(reinterpret_i64(d) as! u64, 0, t); }
    if t == GIR_T_F32 { return c_fp(f32_bits(d), 0, t); }
    if t == GIR_T_F16 { return c_fp(f64_to_f16bits(d) as u64, 0, t); }
    let x = f64_to_f80(d);
    return c_fp(x.lo, x.hi, t);
}

// The value of an f32/f64/f16 constant as a double (ok = false for f80).
fn c_as_double(v: u32) -> bool, f64 {
    let c = m_consts[cidx(v)];
    if c.ty == GIR_T_F64 { return true, reinterpret_f64(c.lo as! i64); }
    if c.ty == GIR_T_F32 { return true, f32bits_to_f64(c.lo as! u32); }
    return false, 0.0;
}

recursive fn ins_fbin(op: i64, t: u32, a: u32, b: u32) -> u32 {
    if t == GIR_T_F16 {
        let x = half_to_float(a);
        let y = half_to_float(b);
        return float_to_half(ins_fbin(op, GIR_T_F32, x, y));
    }
    if is_const(a) && is_const(b) && (t == GIR_T_F64 || t == GIR_T_F32) {
        let ok1, x = c_as_double(a);
        let ok2, y = c_as_double(b);
        if ok1 && ok2 {
            var r = 0.0;
            if op == GIR_FADD { r = x + y; } else if op == GIR_FSUB { r = x - y; } else if op == GIR_FMUL { r = x * y; } else { r = x / y; }
            return c_double(if t == GIR_T_F32 { round_f32(r) } else { r }, t);
        }
    }
    return emit(op, t, 0, 0, 0, a, b, 0);
}

fn ins_fneg(v: u32) -> u32 {
    let t = vtype(v);
    if t == GIR_T_F16 {
        let i = ins_bitcast(v, GIR_T_I16);
        let x = ins_bin(GIR_XOR, GIR_T_I16, i, c_int(0x8000, GIR_T_I16));
        return ins_bitcast(x, GIR_T_F16);
    }
    if is_const(v) {
        let c = m_consts[cidx(v)];
        if t == GIR_T_F64 { return c_fp(c.lo ^ 0x8000000000000000, 0, t); }
        if t == GIR_T_F32 { return c_fp(c.lo ^ 0x80000000, 0, t); }
        if t == GIR_T_F80 { return c_fp(c.lo, c.hi ^ 0x8000, t); }
    }
    return emit(GIR_FNEG, t, 0, 0, t, v, 0, 0);
}

recursive fn ins_fcmp(pred: i64, t: u32, a: u32, b: u32) -> u32 {
    if t == GIR_T_F16 { return ins_fcmp(pred, GIR_T_F32, half_to_float(a), half_to_float(b)); }
    if is_const(a) && is_const(b) && (t == GIR_T_F64 || t == GIR_T_F32) {
        let ok1, x = c_as_double(a);
        let ok2, y = c_as_double(b);
        if ok1 && ok2 {
            let uno = x != x || y != y;
            let r = match pred {
                F_FALSE => false, F_OEQ => !uno && x == y, F_OGT => !uno && x > y, F_OGE => !uno && x >= y,
                F_OLT => !uno && x < y, F_OLE => !uno && x <= y, F_ONE => !uno && x != y, F_ORD => !uno,
                F_UNO => uno, F_UEQ => uno || x == y, F_UGT => uno || x > y, F_UGE => uno || x >= y,
                F_ULT => uno || x < y, F_ULE => uno || x <= y, F_UNE => uno || x != y, _ => true,
            };
            return c_int(if r { 1 } else { 0 }, GIR_T_I1);
        }
    }
    return emit(GIR_FCMP, GIR_T_I1, pred, 0, t, a, b, 0);
}

fn half_to_float(v: u32) -> u32 {
    if is_const(v) { return c_double(f16bits_to_f64(c_lo(v) as! u32), GIR_T_F32); }
    return libcall1("__extendhfsf2", GIR_T_F32, v);
}
fn float_to_half(v: u32) -> u32 {
    if is_const(v) {
        let ok, d = c_as_double(v);
        if ok { return c_double(d, GIR_T_F16); }
    }
    let t = vtype(v);
    let nm = if t == GIR_T_F32 { "__truncsfhf2" } else if t == GIR_T_F64 { "__truncdfhf2" } else { "__truncxfhf2" };
    return libcall1(nm, GIR_T_F16, v);
}

// FP -> FP.
recursive fn fp_cast(v: u32, f: u32, t: u32) -> u32 {
    if f == t { return v; }
    if f == GIR_T_F16 {
        let x = half_to_float(v);
        return fp_cast(x, GIR_T_F32, t);
    }
    if t == GIR_T_F16 { return float_to_half(v); }
    if is_const(v) {
        let ok, d = c_as_double(v);
        if ok {
            if t == GIR_T_F32 { return c_double(round_f32(d), t); }
            return c_double(d, t);
        }
        if f == GIR_T_F80 {
            let c = m_consts[cidx(v)];
            let d2 = f80_to_f64(F80 { lo: c.lo, hi: c.hi });
            if t == GIR_T_F64 { return c_double(d2, t); }
            if t == GIR_T_F32 { return c_double(f80_to_f32_d(F80 { lo: c.lo, hi: c.hi }), t); }
        }
    }
    let rank_f = if f == GIR_T_F32 { 1 } else if f == GIR_T_F64 { 2 } else { 3 };
    let rank_t = if t == GIR_T_F32 { 1 } else if t == GIR_T_F64 { 2 } else { 3 };
    return emit(if rank_t > rank_f { GIR_FPEXT } else { GIR_FPTRUNC }, t, 0, 0, f, v, 0, 0);
}

fn fp_suffix_part(t: u32) -> const u8[:] { if t == GIR_T_F32 { "sf" } else if t == GIR_T_F64 { "df" } else { "xf" } }

// INT -> FP
recursive fn int_to_fp(v: u32, f: u32, t: u32, signed: bool) -> u32 {
    if t == GIR_T_F16 { return float_to_half(int_to_fp(v, f, GIR_T_F32, signed)); }
    if tcls(f) == C_INT2 {
        let w = int_cast(v, f, GIR_T_I128, signed);
        var nm: u8[>..] = [];
        nm.append(if signed { "__floatti" } else { "__floatunti" });
        nm.append(fp_suffix_part(t));
        return libcall1(nm, t, w);
    }
    if is_const(v) && t != GIR_T_F80 {
        let x = c_lo(v) & mask_of(tbits(f));
        var d = 0.0;
        if signed { d = sext_of(x, tbits(f)) as f64; } else { d = u64_to_f64(x); }
        if t == GIR_T_F32 {
            // rounding a u64/i64 to float directly (not through double)
            if signed { return c_fp(i64_to_f32bits(sext_of(x, tbits(f))) as u64, 0, t); }
            return c_fp(u64_to_f32bits(x) as u64, 0, t);
        }
        return c_double(d, t);
    }
    return emit(if signed { GIR_SITOFP } else { GIR_UITOFP }, t, 0, 0, f, v, 0, 0);
}

extern fn u64_to_f64(x: u64) -> f64 = "goosecc_u64_to_f64";
extern fn u64_to_f32bits(x: u64) -> u32 = "goosecc_u64_to_f32bits";
extern fn i64_to_f32bits(x: i64) -> u32 = "goosecc_i64_to_f32bits";

// FP -> INT
recursive fn fp_to_int(v: u32, f: u32, t: u32, signed: bool) -> u32 {
    if f == GIR_T_F16 { return fp_to_int(half_to_float(v), GIR_T_F32, t, signed); }
    if tcls(t) == C_INT2 {
        var nm: u8[>..] = [];
        nm.append(if signed { "__fix" } else { "__fixuns" });
        nm.append(fp_suffix_part(f));
        nm.append("ti");
        let r = libcall1(nm, GIR_T_I128, v);
        return int_cast(r, GIR_T_I128, t, false);
    }
    return emit(if signed { GIR_FPTOSI } else { GIR_FPTOUI }, t, 0, 0, f, v, 0, 0);
}

// ------------------------------------------------------- C conversions

fn is_fp_kind(k: i64) -> bool { k == TY_FLOAT || k == TY_DOUBLE || k == TY_LDOUBLE || k == TY_FLOAT16 || k == TY_FLOAT128 }
fn is_int_like(k: i64) -> bool { is_integer_kind(k) }

// x != 0 as i1 for a scalar of C type q.
fn to_bool(v: u32, q: u32) -> u32 {
    let t = vtype(v);
    if t == GIR_T_I1 { return v; }
    let k = kind_of(q);
    if tcls(t) == C_FP || tcls(t) == C_X87 { return ins_fcmp(F_UNE, t, v, c_zero(t)); }
    if k == TY_POINTER || t == GIR_T_PTR { return ins_icmp(GIR_NE, GIR_T_PTR, v, c_null()); }
    return ins_icmp(GIR_NE, t, v, c_zero(t));
}

// Converts scalar v of C type `from` to C type `to` (C11 6.3).
fn conv(v: u32, from: u32, to: u32) -> u32 {
    let kt = kind_of(to);
    if kt == TY_VOID { return NONE; }
    let kf = kind_of(from);
    if kt == TY_BOOL { return to_bool(v, from); }
    let ft = vtype(v);
    let tt = vty(to);
    if ft == tt && kf != TY_BOOL { return v; }
    let ff = tcls(ft) == C_FP || tcls(ft) == C_X87;
    let tf = tcls(tt) == C_FP || tcls(tt) == C_X87;
    if tkind(tt) == TK_VECTOR || tkind(ft) == TK_VECTOR {
        if tsize(tt) == tsize(ft) { return ins_bitcast(v, tt); }
        return v;
    }
    if ff && tf { return fp_cast(v, ft, tt); }
    if ff { return fp_to_int(v, ft, tt, is_signed(to) || kt == TY_POINTER); }
    if tf { return int_to_fp(v, ft, tt, kf != TY_BOOL && kf != TY_POINTER && is_signed(from)); }
    if tt == GIR_T_PTR {
        if ft == GIR_T_PTR { return v; }
        let w = int_cast(v, ft, GIR_T_I64, kf != TY_BOOL && is_signed(from));
        return ins_inttoptr(w);
    }
    if ft == GIR_T_PTR {
        let w = ins_ptrtoint(v, GIR_T_I64);
        return int_cast(w, GIR_T_I64, tt, false);
    }
    return int_cast(v, ft, tt, kf != TY_BOOL && is_signed(from));
}

// ------------------------------------------------------- memory

fn ins_load(t: u32, p: u32, vol: bool) -> u32 {
    return emit(GIR_LOAD, t, 0, if vol { IF_VOLATILE } else { 0 }, 0, p, 0, 0);
}
fn ins_store(t: u32, v: u32, p: u32, vol: bool) {
    emit(GIR_STORE, GIR_T_VOID, 0, if vol { IF_VOLATILE } else { 0 }, t, v, p, 0);
}

// Loads a C scalar of type q from p: bool is a byte holding 0 or 1.
fn load_c(q: u32, p: u32, vol: bool) -> u32 {
    if kind_of(q) == TY_BOOL {
        let b = ins_load(GIR_T_I8, p, vol);
        return emit(GIR_TRUNC, GIR_T_I1, 0, 0, GIR_T_I8, b, 0, 0);
    }
    return ins_load(mty(q), p, vol);
}
fn store_c(q: u32, v: u32, p: u32, vol: bool) {
    if kind_of(q) == TY_BOOL {
        let b = int_cast(v, vtype(v), GIR_T_I8, false);
        ins_store(GIR_T_I8, b, p, vol);
        return;
    }
    ins_store(mty(q), v, p, vol);
}

// p + off (+ idx * scale): GEP.
fn gep(p: u32, off: i64) -> u32 {
    if off == 0 { return p; }
    if is_const(p) {
        // a constant address (an integer cast to a pointer)
        return c_int(c_lo(p) + (off as! u64), GIR_T_PTR);
    }
    let s = m_opnds.len as! u32;
    op_imm(((off as! u64) & 0xFFFFFFFF) as! u32);
    op_imm(((off as! u64) >> 32) as! u32);
    return emit(GIR_GEP, GIR_T_PTR, 0, 0, 0, p, s, 0);
}

fn gep_idx(p: u32, off: i64, idx: u32, scale: i64) -> u32 {
    if is_const(idx) {
        let it = vtype(idx);
        let iv = sext_of(c_lo(idx), tbits(it));
        return gep(p, off + iv * scale);
    }
    if scale == 0 { return gep(p, off); }
    var ix = idx;
    var sc = scale;
    if scale > 0xFFFFFFFF || scale < 0 {
        ix = ins_bin(GIR_MUL, GIR_T_I64, int_cast(idx, vtype(idx), GIR_T_I64, true), c_i64(scale));
        sc = 1;
    }
    let s = m_opnds.len as! u32;
    op_imm(((off as! u64) & 0xFFFFFFFF) as! u32);
    op_imm(((off as! u64) >> 32) as! u32);
    op_ref(ix);
    op_imm(sc as! u32);
    return emit(GIR_GEP, GIR_T_PTR, 0, 0, 0, p, s, 1);
}

// Block copy / fill of n bytes (inline up to 256, else libc).
fn mem_copy(dst: u32, src: u32, n: i64, vol: bool) {
    if n <= 0 { return; }
    if n <= 256 {
        emit(GIR_MEMCPY, GIR_T_VOID, 0, if vol { IF_VOLATILE } else { 0 }, 0, dst, src, n as! u32);
        return;
    }
    libcall3("memcpy", GIR_T_PTR, dst, src, c_i64(n));
}

fn mem_set(dst: u32, byte: u32, n: i64, vol: bool) {
    if n <= 0 { return; }
    if n <= 256 {
        emit(GIR_MEMSET, GIR_T_VOID, 0, if vol { IF_VOLATILE } else { 0 }, 0, dst, byte, n as! u32);
        return;
    }
    libcall3("memset", GIR_T_PTR, dst, ins_zext(byte, GIR_T_I32), c_i64(n));
}

fn mem_copy_dyn(dst: u32, src: u32, n: u32) {
    libcall3("memcpy", GIR_T_PTR, dst, src, n);
}

// ------------------------------------------------------- library calls


fn libfn(name: const u8[:]) -> u32 {
    let id = intern(name);
    let r = gmap.get(gk(GM_LIBFN, id));
    if r { return r; }
    let g = global_by_name(id, true);
    gmap.insert(gk(GM_LIBFN, id), g);
    return g;
}

fn libcall_emit(name: const u8[:], rt: u32, s: u32, n: u32) -> u32 {
    let g = libfn(name);
    return emit(GIR_CALL, rt, 0, 0, 0, gref(g), s, n);
}

fn libcall1(name: const u8[:], rt: u32, a: u32) -> u32 {
    let g = libfn(name);
    let s = m_opnds.len as! u32;
    op_ref(a);
    op_imm(0);
    return emit(GIR_CALL, rt, 0, 0, 0, gref(g), s, 1);
}
fn libcall2(name: const u8[:], rt: u32, a: u32, b: u32) -> u32 {
    let g = libfn(name);
    let s = m_opnds.len as! u32;
    op_ref(a);
    op_imm(0);
    op_ref(b);
    op_imm(0);
    return emit(GIR_CALL, rt, 0, 0, 0, gref(g), s, 2);
}
fn libcall3(name: const u8[:], rt: u32, a: u32, b: u32, c: u32) -> u32 {
    let g = libfn(name);
    let s = m_opnds.len as! u32;
    op_ref(a);
    op_imm(0);
    op_ref(b);
    op_imm(0);
    op_ref(c);
    op_imm(0);
    return emit(GIR_CALL, rt, 0, 0, 0, gref(g), s, 3);
}
fn libcall4(name: const u8[:], rt: u32, a: u32, b: u32, c: u32, d: u32) -> u32 {
    let g = libfn(name);
    let s = m_opnds.len as! u32;
    op_ref(a);
    op_imm(0);
    op_ref(b);
    op_imm(0);
    op_ref(c);
    op_imm(0);
    op_ref(d);
    op_imm(0);
    return emit(GIR_CALL, rt, 0, 0, 0, gref(g), s, 4);
}
