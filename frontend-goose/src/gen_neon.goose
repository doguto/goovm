// goosecc F1: arm_neon.h on AArch64. The header's functions call
// __builtin_neon_* builtins with their operands reinterpreted as int8x8_t /
// int8x16_t and, for the polymorphic ones (`..._v`), a NEON type code as the
// last argument (bits 0-3 the element type: 0 i8, 1 i16, 2 i32, 3 i64,
// 4 p8, 5 p16, 6 p64, 7 p128, 8 f16, 9 f32, 10 f64, 11 bf16; 16 unsigned;
// 32 a 128-bit vector). They are lowered as clang's CodeGen lowers them
// (EmitAArch64BuiltinExpr, EmitCommonNeonBuiltinExpr): into GIR_A64
// operations (the instructions LLVM's llvm.aarch64.neon.* intrinsics are)
// and generic vector operations, with the operands bitcast to the vector
// type of the code and the result bitcast back to the builtin's type.
// The scalar (SISD) builtins (vqaddb_s8, vcvtd_s64_f64, vaddvq_u32 ...)
// take their C types. Not covered: fp16 and bf16 arithmetic (+fullfp16,
// +bf16), the FP8, SVE, SM3/SM4/SHA-3/SHA-512 and i8mm extensions.

namespace gen;

import std;
import .common;
import .types;
import .ast;
import .sema;

// ---------------------------------------------------------------- types

fn nn_elt(code: i64) -> u32 {
    let e = code & 15;
    if e == 0 || e == 4 { return GIR_T_I8; }
    if e == 1 || e == 5 || e == 11 { return GIR_T_I16; }
    if e == 2 { return GIR_T_I32; }
    if e == 3 || e == 6 { return GIR_T_I64; }
    if e == 7 { return GIR_T_I128; }
    if e == 8 { return GIR_T_F16; }
    if e == 9 { return GIR_T_F32; }
    return GIR_T_F64;
}
fn nn_quad(code: i64) -> bool { code & 32 != 0 }
fn nn_uns(code: i64) -> bool { code & 16 != 0 }
fn nn_fp(code: i64) -> bool { let e = code & 15; e >= 8 && e <= 10 }
fn nn_poly(code: i64) -> bool { let e = code & 15; e >= 4 && e <= 7 }
fn elt_bits(t: u32) -> u32 { if tkind(t) == TK_VECTOR { tsize(m_types[t].elems) * 8 } else { tsize(t) * 8 } }
fn lanes(t: u32) -> u32 { m_types[t].n }
fn elt_of(t: u32) -> u32 { m_types[t].elems }
// <lanes x elt> of `bits` total bits.
fn vt_bits(elt: u32, bits: u32) -> u32 { ty_vec(bits / (tsize(elt) * 8), elt) }
fn nn_vt(code: i64) -> u32 { vt_bits(nn_elt(code), if nn_quad(code) { 128 } else { 64 }) }
// the same lane count with elements of half / double the width (integers)
fn vt_half(t: u32) -> u32 { ty_vec(lanes(t), ty_int(elt_bits(t) / 2)) }
fn vt_dbl(t: u32) -> u32 { ty_vec(lanes(t), ty_int(elt_bits(t) * 2)) }
// the integer vector of t's shape, and the FP vector of an integer vector's shape
fn vt_int(t: u32) -> u32 { ty_vec(lanes(t), ty_int(elt_bits(t))) }
fn vt_fp(t: u32) -> u32 { ty_vec(lanes(t), if elt_bits(t) == 64 { GIR_T_F64 } else if elt_bits(t) == 32 { GIR_T_F32 } else { GIR_T_F16 }) }
fn vt_mask(t: u32) -> u32 { ty_vec(lanes(t), GIR_T_I1) }

// ---------------------------------------------------------------- operands

fn nb_imm(n: u32, i: i64) -> i64 {
    let ok, v = fold_int(barg(n, i));
    return v;
}
fn bc(v: u32, t: u32) -> u32 { ins_bitcast(v, t) }
fn op3(k: i64, t: u32, at: u32, a: u32, b: u32, c: u32) -> u32 { emit(GIR_A64, t, k, 0, at, a, b, c) }
fn op2(k: i64, t: u32, a: u32, b: u32) -> u32 { emit(GIR_A64, t, k, 0, vtype(a), a, b, c_i32(0)) }
fn op1(k: i64, t: u32, a: u32) -> u32 { emit(GIR_A64, t, k, 0, vtype(a), a, c_i32(0), c_i32(0)) }
fn vbin(op: i64, a: u32, b: u32) -> u32 { emit(op, vtype(a), 0, 0, 0, a, b, 0) }
fn vcast(op: i64, t: u32, v: u32) -> u32 { emit(op, t, 0, 0, vtype(v), v, 0, 0) }
fn splat_v(t: u32, x: u32) -> u32 {
    var v = c_zero(t);
    for i in 0..lanes(t) { v = emit(GIR_INSERTELT, t, 0, 0, 0, v, x, c_i32(i as i64)); }
    return v;
}
fn splat_imm(t: u32, x: i64) -> u32 { splat_const(t, x) }
fn shuf(t: u32, a: u32, b: u32, idx: const i64[:]) -> u32 {
    let s = m_opnds.len as! u32;
    for x in idx { if x < 0 { op_imm(NONE); } else { op_imm(x as! u32); } }
    return emit(GIR_SHUFFLE, t, 0, 0, vtype(a), a, b, s);
}
var nn_idx: i64[>..] = [];
// a with b's lanes after it (b of a's type)
fn concat(a: u32, b: u32) -> u32 {
    let t = vtype(a);
    nn_idx.clear();
    for i in 0..2 * lanes(t) { nn_idx.push(i as i64); }
    return shuf(ty_vec(2 * lanes(t), elt_of(t)), a, b, nn_idx[..]);
}
fn splat_lane(t: u32, v: u32, lane: i64) -> u32 {
    nn_idx.clear();
    for i in 0..lanes(t) { nn_idx.push(lane); }
    return shuf(t, v, v, nn_idx[..]);
}
// lane-wise compare (GIR predicate; fp: an F_ predicate), sign-extended to the integer vector
fn vcmp(fp: bool, pred: i64, a: u32, b: u32) -> u32 {
    let t = vtype(a);
    let c = emit(if fp { GIR_FCMP } else { GIR_ICMP }, vt_mask(t), pred, 0, t, a, b, 0);
    return emit(GIR_SEXT, vt_int(t), 0, 0, vt_mask(t), c, 0, 0);
}
// The operand's type before the header's reinterpreting cast (clang's
// EmitAArch64CompareBuiltinExpr looks through the bitcast the same way).
fn orig_type(a: u32) -> u32 {
    var m = a;
    loop {
        let nd = nodes[m];
        if (nd.kind == N_ICAST || nd.kind == N_CAST) && is_vector(nty(nd.a)) && type_size(nty(nd.a)) == type_size(nd.ty) {
            m = nd.a;
            continue;
        }
        break;
    }
    return vty(unqual(nty(m)));
}
fn nout(v: u32, rq: u32) -> u32 {
    if v == NONE || is_void(rq) { return NONE; }
    let t = vty(rq);
    if vtype(v) == t { return v; }
    if tkind(t) == TK_VECTOR || tkind(vtype(v)) == TK_VECTOR { return bc(v, t); }
    if tcls(t) == C_INT && tcls(vtype(v)) == C_INT { return int_cast(v, vtype(v), t, false); }
    return v;
}

// the GIR_A64 operation of a signed / unsigned / FP family member
fn sufk(fp: bool, uns: bool, kf: i64, ks: i64, ku: i64) -> i64 { if fp { kf } else if uns { ku } else { ks } }

// ---------------------------------------------------------------- loads and stores

// the address of element k of type et at p
fn eaddr(p: u32, et: u32, k: i64) -> u32 { gep(p, k * tsize(et) as i64) }

// vldN (dup 0: interleaved, 1: replicate; lane >= 0: one lane into the vectors vs) into *dst
fn ld_n(dst: u32, p: u32, t: u32, nv: i64, dup: bool, lane: i64, vs: const u32[:]) {
    let et = elt_of(t);
    let nl = lanes(t) as i64;
    for k in 0..nv {
        var v: u32 = 0;
        if dup {
            v = splat_v(t, ins_load(et, eaddr(p, et, k), false));
        } else if lane >= 0 {
            v = emit(GIR_INSERTELT, t, 0, 0, 0, bc(vs[k], t), ins_load(et, eaddr(p, et, k), false), c_i32(lane));
        } else {
            v = c_zero(t);
            for j in 0..nl {
                let x = ins_load(et, eaddr(p, et, j * nv + k), false);
                v = emit(GIR_INSERTELT, t, 0, 0, 0, v, x, c_i32(j));
            }
        }
        ins_store(t, v, gep(dst, k * tsize(t) as i64), false);
    }
}
fn st_n(p: u32, t: u32, vs: const u32[:], lane: i64) {
    let et = elt_of(t);
    let nv = vs.len;
    let nl = lanes(t) as i64;
    for k in 0..nv {
        let v = bc(vs[k], t);
        if lane >= 0 {
            ins_store(et, emit(GIR_EXTRACTELT, et, 0, 0, t, v, c_i32(lane), 0), eaddr(p, et, k), false);
            continue;
        }
        for j in 0..nl {
            ins_store(et, emit(GIR_EXTRACTELT, et, 0, 0, t, v, c_i32(j), 0), eaddr(p, et, j * nv + k), false);
        }
    }
}

// ---------------------------------------------------------------- tables

// vtbl / vtbx on 64-bit tables (clang's packTBLDVectorList: pairs of d registers
// as q registers, an odd one with zeros)
fn tbl_d(tabs: const u32[:], idx: u32, tbx: bool, fb: u32) -> u32 {
    let t8 = ty_vec(8, GIR_T_I8);
    let t16 = ty_vec(16, GIR_T_I8);
    var qs: u32[>..] = [];
    var k = 0;
    while k < tabs.len {
        let a = bc(tabs[k], t8);
        let b = if k + 1 < tabs.len { bc(tabs[k + 1], t8) } else { c_zero(t8) };
        qs.push(concat(a, b));
        k += 2;
    }
    let ix = bc(idx, t8);
    let n = tabs.len;
    if tbx && (n == 2 || n == 4) {
        // the fallback is the instruction's own (no index out of range is in the table)
        return tbl_q(qs[..], ix, true, bc(fb, t8), t8);
    }
    let r = tbl_q(qs[..], ix, false, 0, t8);
    if !tbx { return r; }
    // vtbx1 / vtbx3: the lanes whose index is past the table keep the fallback
    let lim = splat_imm(t8, (8 * n) as i64);
    let m = vcmp(false, GIR_UGE, ix, lim);
    let keep = vbin(GIR_AND, m, bc(fb, t8));
    let notm = vbin(GIR_XOR, m, splat_imm(t8, -1));
    let fromt = vbin(GIR_AND, notm, r);
    return vbin(GIR_OR, keep, fromt);
}
// tbl / tbx on 128-bit tables qs, indices ix (result of ix's type)
fn tbl_q(qs: const u32[:], ix: u32, tbx: bool, fb: u32, rt: u32) -> u32 {
    let t16 = ty_vec(16, GIR_T_I8);
    var tab = bc(qs[0], t16);
    let n = qs.len;
    if n > 1 {
        let c01 = concat(bc(qs[0], t16), bc(qs[1], t16));
        if n == 2 { tab = c01; }
        else {
            let c23 = concat(bc(qs[2], t16), if n == 4 { bc(qs[3], t16) } else { bc(qs[2], t16) });
            nn_idx.clear();
            for i in 0..16 * n { nn_idx.push(i as i64); }
            tab = shuf(ty_vec((16 * n) as! u32, GIR_T_I8), c01, c23, nn_idx[..]);
        }
    }
    return op3(if tbx { GIR_A64_TBX } else { GIR_A64_TBL }, rt, t16, tab, ix, if tbx { fb } else { c_i32(0) });
}

// ---------------------------------------------------------------- the builtins

// arm_neon.h's builtin `name` (without __builtin_neon_), or KEEP_CALL when it is not one goosecc knows.
recursive fn neon_builtin(full: const u8[:], n: u32, dst: u32) -> u32 {
    let nd = nodes[n];
    let nargs = nd.c as i64;
    let rq = unqual(nd.ty);
    // the operands first, in order (as clang's EmitAArch64BuiltinExpr); an operand may itself be a NEON builtin
    var ops: u32[12] = [0; 12];
    for i in 0..nargs {
        if i < 12 { ops[i] = ex_val(barg(n, i)); }
    }
    let o = ops[..if nargs < 12 { nargs } else { 12 }];
    if ends_with(full, "_v") && nargs >= 1 {
        let r = neon_poly(full[..full.len - 2], n, rq, o);
        if r != KEEP_CALL { return nout(r, rq); }
    }
    let r = neon_mono(full, n, rq, o);
    if r != KEEP_CALL { return nout(r, rq); }
    return KEEP_CALL;
}

var nn_fam: u8[>..] = [];
var vals: u32[>..] = [];

// the family of a polymorphic builtin: its name without the q of the 128-bit form
fn neon_family(b: const u8[:], out: u8[>..]&) {
    out.clear();
    var u = find(b, "_");
    if u < 0 { u = b.len; }
    var i = 0;
    while i < b.len {
        if !(i == u - 1 && b[i] == 'q' && u > 2) { out.push(b[i]); }
        i++;
    }
}

fn neon_poly(base: const u8[:], n: u32, rq: u32, o: const u32[:]) -> u32 {
    let nargs = nodes[n].c as i64;
    let code = nb_imm(n, nargs - 1);
    neon_family(base, nn_fam);
    let f = nn_fam[..];
    var T = nn_vt(code);
    let qf = nn_fam.len < base.len;   // the 128-bit form (by the name)
    if find(f, "_lane") >= 0 && !starts_with(f, "splat") && !starts_with(f, "vld") && !starts_with(f, "vst") {
        // the by-element forms: the result's width by the name, the lane vector's by `lane` / `laneq`
        T = vt_bits(nn_elt(code), if qf { 128 } else { 64 });
    }
    let fp = nn_fp(code);
    let u = nn_uns(code);
    let z = c_i32(0);
    // same-type binary operations
    var k: i64 = -1;
    if f == "vabd" { k = sufk(fp, u, GIR_A64_FABD, GIR_A64_SABD, GIR_A64_UABD); }
    else if f == "vhadd" { k = sufk(fp, u, -1, GIR_A64_SHADD, GIR_A64_UHADD); }
    else if f == "vhsub" { k = sufk(fp, u, -1, GIR_A64_SHSUB, GIR_A64_UHSUB); }
    else if f == "vrhadd" { k = sufk(fp, u, -1, GIR_A64_SRHADD, GIR_A64_URHADD); }
    else if f == "vmax" { k = sufk(fp, u, GIR_A64_FMAX, GIR_A64_SMAX, GIR_A64_UMAX); }
    else if f == "vmin" { k = sufk(fp, u, GIR_A64_FMIN, GIR_A64_SMIN, GIR_A64_UMIN); }
    else if f == "vmaxnm" { k = GIR_A64_FMAXNM; }
    else if f == "vminnm" { k = GIR_A64_FMINNM; }
    else if f == "vpadd" { k = if fp { GIR_A64_FADDP } else { GIR_A64_ADDP }; }
    else if f == "vpmax" { k = sufk(fp, u, GIR_A64_FMAXP, GIR_A64_SMAXP, GIR_A64_UMAXP); }
    else if f == "vpmin" { k = sufk(fp, u, GIR_A64_FMINP, GIR_A64_SMINP, GIR_A64_UMINP); }
    else if f == "vpmaxnm" { k = GIR_A64_FMAXNMP; }
    else if f == "vpminnm" { k = GIR_A64_FMINNMP; }
    else if f == "vqadd" { k = sufk(false, u, -1, GIR_A64_SQADD, GIR_A64_UQADD); }
    else if f == "vqsub" { k = sufk(false, u, -1, GIR_A64_SQSUB, GIR_A64_UQSUB); }
    else if f == "vqdmulh" { k = GIR_A64_SQDMULH; }
    else if f == "vqrdmulh" { k = GIR_A64_SQRDMULH; }
    else if f == "vshl" { k = sufk(false, u, -1, GIR_A64_SSHL, GIR_A64_USHL); }
    else if f == "vqshl" { k = sufk(false, u, -1, GIR_A64_SQSHL, GIR_A64_UQSHL); }
    else if f == "vrshl" { k = sufk(false, u, -1, GIR_A64_SRSHL, GIR_A64_URSHL); }
    else if f == "vqrshl" { k = sufk(false, u, -1, GIR_A64_SQRSHL, GIR_A64_UQRSHL); }
    else if f == "vmul" { k = GIR_A64_PMUL; }
    else if f == "vmulx" { k = GIR_A64_FMULX; }
    else if f == "vrecps" { k = GIR_A64_FRECPS; }
    else if f == "vrsqrts" { k = GIR_A64_FRSQRTS; }
    else if f == "vsqadd" { k = GIR_A64_USQADD; }
    else if f == "vuqadd" { k = GIR_A64_SUQADD; }
    if k >= 0 && nargs == 3 {
        return op2(k, T, bc(o[0], T), bc(o[1], T));
    }
    // absolute compares: the operands are FP vectors of the result's shape
    if f == "vcage" || f == "vcagt" || f == "vcale" || f == "vcalt" {
        let ft = vt_fp(T);
        let a = bc(o[0], ft);
        let b = bc(o[1], ft);
        let ge = f == "vcage" || f == "vcale";
        let swap = f == "vcale" || f == "vcalt";
        let kk = if ge { GIR_A64_FACGE } else { GIR_A64_FACGT };
        return if swap { op2(kk, T, b, a) } else { op2(kk, T, a, b) };
    }
    // unary operations of one type
    k = -1;
    if f == "vqabs" { k = GIR_A64_SQABS; }
    else if f == "vqneg" { k = GIR_A64_SQNEG; }
    else if f == "vcls" { k = GIR_A64_CLS; }
    else if f == "vclz" { k = GIR_A64_CLZ; }
    else if f == "vcnt" { k = GIR_A64_CNT; }
    else if f == "vrbit" { k = GIR_A64_RBIT; }
    else if f == "vrecpe" { k = if fp { GIR_A64_FRECPE } else { GIR_A64_URECPE }; }
    else if f == "vrsqrte" { k = if fp { GIR_A64_FRSQRTE } else { GIR_A64_URSQRTE }; }
    else if f == "vrnd" { k = GIR_A64_FRINTZ; }
    else if f == "vrnda" { k = GIR_A64_FRINTA; }
    else if f == "vrndi" { k = GIR_A64_FRINTI; }
    else if f == "vrndm" { k = GIR_A64_FRINTM; }
    else if f == "vrndn" { k = GIR_A64_FRINTN; }
    else if f == "vrndp" { k = GIR_A64_FRINTP; }
    else if f == "vrndx" { k = GIR_A64_FRINTX; }
    else if f == "vabs" && !fp { k = GIR_A64_ABS; }
    if k >= 0 && nargs == 2 { return op1(k, T, bc(o[0], T)); }
    if f == "vabs" { return emit(GIR_FABS, T, 0, 0, T, bc(o[0], T), 0, 0); }
    if f == "vsqrt" { return emit(GIR_FSQRT, T, 0, 0, T, bc(o[0], T), 0, 0); }
    // conversions (the code is the integer type)
    if f == "vcvt_s32" || f == "vcvt_s64" || f == "vcvt_u32" || f == "vcvt_u64" || starts_with(f, "vcvta_") ||
       starts_with(f, "vcvtm_") || starts_with(f, "vcvtn_") || starts_with(f, "vcvtp_") {
        let us = find(f, "_u") >= 0;
        let c = f[4];
        let kk = if c == 'a' { if us { GIR_A64_FCVTAU } else { GIR_A64_FCVTAS } }
                 else if c == 'm' { if us { GIR_A64_FCVTMU } else { GIR_A64_FCVTMS } }
                 else if c == 'n' { if us { GIR_A64_FCVTNU } else { GIR_A64_FCVTNS } }
                 else if c == 'p' { if us { GIR_A64_FCVTPU } else { GIR_A64_FCVTPS } }
                 else { if us { GIR_A64_FCVTZU } else { GIR_A64_FCVTZS } };
        return op1(kk, T, bc(o[0], vt_fp(T)));
    }
    if f == "vcvt_f32" || f == "vcvt_f64" || f == "vcvt_f16" {
        let src = bc(o[0], vt_int(T));
        return vcast(if u { GIR_UITOFP } else { GIR_SITOFP }, vt_fp(T), src);
    }
    if f == "vcvt_n_f32" || f == "vcvt_n_f64" {
        let src = bc(o[0], vt_int(T));
        return op2(if u { GIR_A64_UCVTF_FX } else { GIR_A64_SCVTF_FX }, vt_fp(T), src, c_i32(nb_imm(n, 1)));
    }
    if f == "vcvt_n_s32" || f == "vcvt_n_s64" || f == "vcvt_n_u32" || f == "vcvt_n_u64" {
        let src = bc(o[0], vt_fp(T));
        return op2(if find(f, "_u") >= 0 { GIR_A64_FCVTZU_FX } else { GIR_A64_FCVTZS_FX }, T, src, c_i32(nb_imm(n, 1)));
    }
    if f == "vcvtx_f32" {
        return op1(GIR_A64_FCVTXN, ty_vec(2, GIR_T_F32), bc(o[0], ty_vec(2, GIR_T_F64)));
    }
    if f == "vcvt_f32_f64" || f == "vcvt_f64_f32" {
        // (no q form) f64x2 -> f32x2 / f32x2 -> f64x2
        if f == "vcvt_f32_f64" { return vcast(GIR_FPTRUNC, ty_vec(2, GIR_T_F32), bc(o[0], ty_vec(2, GIR_T_F64))); }
        return vcast(GIR_FPEXT, ty_vec(2, GIR_T_F64), bc(o[0], ty_vec(2, GIR_T_F32)));
    }
    // widening and narrowing (the code is the result)
    if f == "vmovl" { return vcast(if u { GIR_ZEXT } else { GIR_SEXT }, T, bc(o[0], vt_half(T))); }
    if f == "vmovn" { return vcast(GIR_TRUNC, T, bc(o[0], vt_dbl(T))); }
    if f == "vqmovn" { return op1(if u { GIR_A64_UQXTN } else { GIR_A64_SQXTN }, T, bc(o[0], vt_dbl(T))); }
    if f == "vqmovun" { return op1(GIR_A64_SQXTUN, T, bc(o[0], vt_dbl(T))); }
    if f == "vaddhn" || f == "vsubhn" {
        let W = vt_dbl(T);
        let s = vbin(if f == "vaddhn" { GIR_ADD } else { GIR_SUB }, bc(o[0], W), bc(o[1], W));
        let sh = vbin(GIR_LSHR, s, splat_imm(W, elt_bits(T) as i64));
        return vcast(GIR_TRUNC, T, sh);
    }
    if f == "vraddhn" || f == "vrsubhn" {
        let W = vt_dbl(T);
        return op2(if f == "vraddhn" { GIR_A64_RADDHN } else { GIR_A64_RSUBHN }, T, bc(o[0], W), bc(o[1], W));
    }
    if f == "vpaddl" || f == "vpadal" {
        let src_t = vt_bits(ty_int(elt_bits(T) / 2), if nn_quad(code) { 128 } else { 64 });
        let x = o[if f == "vpadal" { 1 } else { 0 }];
        let p = op1(if u { GIR_A64_UADDLP } else { GIR_A64_SADDLP }, T, bc(x, src_t));
        if f == "vpaddl" { return p; }
        return vbin(GIR_ADD, p, bc(o[0], T));
    }
    if f == "vmull" {
        let H = vt_half(T);
        let kk = if nn_poly(code) { GIR_A64_PMULL } else if u { GIR_A64_UMULL } else { GIR_A64_SMULL };
        return op2(kk, T, bc(o[0], H), bc(o[1], H));
    }
    if f == "vqdmull" {
        let H = vt_half(T);
        return op2(GIR_A64_SQDMULL, T, bc(o[0], H), bc(o[1], H));
    }
    if f == "vqdmlal" || f == "vqdmlsl" {
        let H = vt_half(T);
        let acc = bc(o[0], T);
        let m = op2(GIR_A64_SQDMULL, T, bc(o[1], H), bc(o[2], H));
        return op2(if f == "vqdmlal" { GIR_A64_SQADD } else { GIR_A64_SQSUB }, T, acc, m);
    }
    // shifts by an immediate
    if f == "vshl_n" { return vbin(GIR_SHL, bc(o[0], T), splat_imm(T, nb_imm(n, 1))); }
    if f == "vshr_n" || f == "vsra_n" {
        let src = if f == "vsra_n" { 1 } else { 0 };
        let sh = nb_imm(n, src + 1);
        let v = bc(o[src], T);
        var r: u32 = 0;
        if sh == elt_bits(T) as i64 && u { r = c_zero(T); }
        else {
            let s2 = if sh == elt_bits(T) as i64 { sh - 1 } else { sh };
            r = vbin(if u { GIR_LSHR } else { GIR_ASHR }, v, splat_imm(T, s2));
        }
        if f == "vshr_n" { return r; }
        return vbin(GIR_ADD, bc(o[0], T), r);
    }
    if f == "vrshr_n" || f == "vrsra_n" {
        let src = if f == "vrsra_n" { 1 } else { 0 };
        let r = op2(if u { GIR_A64_URSHL } else { GIR_A64_SRSHL }, T, bc(o[src], T), splat_imm(vt_int(T), -nb_imm(n, src + 1)));
        if f == "vrshr_n" { return r; }
        return vbin(GIR_ADD, bc(o[0], T), r);
    }
    if f == "vqshl_n" {
        return op2(if u { GIR_A64_UQSHL } else { GIR_A64_SQSHL }, T, bc(o[0], T), splat_imm(T, nb_imm(n, 1)));
    }
    if f == "vqshlu_n" { return op2(GIR_A64_SQSHLU, T, bc(o[0], T), splat_imm(T, nb_imm(n, 1))); }
    if f == "vshrn_n" {
        let W = vt_dbl(T);
        let s = vbin(if u { GIR_LSHR } else { GIR_ASHR }, bc(o[0], W), splat_imm(W, nb_imm(n, 1)));
        return vcast(GIR_TRUNC, T, s);
    }
    k = -1;
    if f == "vrshrn_n" { k = GIR_A64_RSHRN; }
    else if f == "vqshrn_n" { k = if u { GIR_A64_UQSHRN } else { GIR_A64_SQSHRN }; }
    else if f == "vqrshrn_n" { k = if u { GIR_A64_UQRSHRN } else { GIR_A64_SQRSHRN }; }
    else if f == "vqshrun_n" { k = GIR_A64_SQSHRUN; }
    else if f == "vqrshrun_n" { k = GIR_A64_SQRSHRUN; }
    if k >= 0 { return op2(k, T, bc(o[0], vt_dbl(T)), c_i32(nb_imm(n, 1))); }
    if f == "vshll_n" {
        let w = vcast(if u { GIR_ZEXT } else { GIR_SEXT }, T, bc(o[0], vt_half(T)));
        return vbin(GIR_SHL, w, splat_imm(T, nb_imm(n, 1)));
    }
    if f == "vsli_n" || f == "vsri_n" {
        return op3(if f == "vsli_n" { GIR_A64_SLI } else { GIR_A64_SRI }, T, T, bc(o[0], T), bc(o[1], T),
                   c_i32(nb_imm(n, 2)));
    }
    // permutations, selection, compares
    if f == "vext" {
        let sh = nb_imm(n, 2);
        let a = bc(o[0], T);
        let b = bc(o[1], T);
        nn_idx.clear();
        for i in 0..lanes(T) { nn_idx.push(i as i64 + sh); }
        return shuf(T, a, b, nn_idx[..]);
    }
    if f == "vbsl" {
        let I = vt_int(T);
        let m = bc(o[0], I);
        let a = bc(o[1], I);
        let b = bc(o[2], I);
        let x = vbin(GIR_AND, m, a);
        let y = vbin(GIR_AND, vbin(GIR_XOR, m, splat_imm(I, -1)), b);
        return bc(vbin(GIR_OR, x, y), T);
    }
    if f == "vtst" {
        let a = bc(o[0], T);
        let b = bc(o[1], T);
        return vcmp(false, GIR_NE, vbin(GIR_AND, a, b), c_zero(T));
    }
    if f == "vceqz" || f == "vcgez" || f == "vcgtz" || f == "vclez" || f == "vcltz" {
        let ot = orig_type(barg(n, 0));
        let ofp = tkind(ot) == TK_VECTOR && tcls(elt_of(ot)) == C_FP;
        let a = bc(o[0], if ofp { ot } else { T });
        let c = f[2];
        let c2 = f[3];
        var p: i64 = 0;
        if ofp {
            p = if c == 'e' { F_OEQ } else if c == 'g' && c2 == 'e' { F_OGE } else if c == 'g' { F_OGT } else if c2 == 'e' { F_OLE } else { F_OLT };
        } else {
            p = if c == 'e' { GIR_EQ } else if c == 'g' && c2 == 'e' { GIR_SGE } else if c == 'g' { GIR_SGT } else if c2 == 'e' { GIR_SLE } else { GIR_SLT };
        }
        return vcmp(ofp, p, a, c_zero(vtype(a)));
    }
    // fused multiply-add: a + b * c (clang: llvm.fma(b, c, a))
    if f == "vfma" { return emit(GIR_FMA, T, 0, 0, T, bc(o[1], T), bc(o[2], T), bc(o[0], T)); }
    if f == "vfma_lane" || f == "vfma_laneq" {
        let lt = vt_bits(elt_of(T), if f == "vfma_laneq" { 128 } else { 64 });
        let c = splat_lane(T, bc(o[2], lt), nb_imm(n, 3));
        return emit(GIR_FMA, T, 0, 0, T, bc(o[1], T), c, bc(o[0], T));
    }
    if f == "vmul_lane" || f == "vmul_laneq" {
        let lt = vt_bits(elt_of(T), if f == "vmul_laneq" { 128 } else { 64 });
        let c = splat_lane(T, bc(o[1], lt), nb_imm(n, 2));
        return emit(GIR_FMUL, T, 0, 0, 0, bc(o[0], T), c, 0);
    }
    if f == "vqdmulh_lane" || f == "vqdmulh_laneq" || f == "vqrdmulh_lane" || f == "vqrdmulh_laneq" {
        let lt = vt_bits(elt_of(T), if ends_with(f, "laneq") { 128 } else { 64 });
        let kk = if starts_with(f, "vqdmulh") { GIR_A64_SQDMULH_LANE } else { GIR_A64_SQRDMULH_LANE };
        return op3(kk, T, T, bc(o[0], T), bc(o[1], lt), c_i32(nb_imm(n, 2)));
    }
    if f == "splat_lane" || f == "splatq_lane" || f == "splat_laneq" || f == "splatq_laneq" {
        // the code is the source vector's; the result is 64 or 128 bits by the name
        let src = bc(o[0], T);
        let rt = vt_bits(elt_of(T), if starts_with(base, "splatq") { 128 } else { 64 });
        let lane = nb_imm(n, 1);
        nn_idx.clear();
        for i in 0..lanes(rt) { nn_idx.push(lane); }
        return shuf(rt, src, src, nn_idx[..]);
    }
    if f == "vdot" {
        let bt = vt_bits(GIR_T_I8, if nn_quad(code) { 128 } else { 64 });
        return op3(if u { GIR_A64_UDOT } else { GIR_A64_SDOT }, T, T, bc(o[0], T), bc(o[1], bt), bc(o[2], bt));
    }
    // tables
    if f == "vtbl1" || f == "vtbl2" || f == "vtbl3" || f == "vtbl4" || f == "vtbx1" || f == "vtbx2" || f == "vtbx3" || f == "vtbx4" {
        let tbx = f[3] == 'x';
        let nt = (f[4] - '0') as i64;
        let first = if tbx { 1 } else { 0 };
        vals.clear();
        for i in 0..nt { vals.push(o[first + i]); }
        let idx = o[first + nt];
        let fb = if tbx { o[0] } else { 0 };
        return tbl_d(vals[..], idx, tbx, fb);
    }
    if starts_with(f, "vqtbl") || starts_with(f, "vqtbx") {
        let tbx = f[4] == 'x';
        let nt = (f[5] - '0') as i64;
        let first = if tbx { 1 } else { 0 };
        vals.clear();
        for i in 0..nt { vals.push(o[first + i]); }
        let rt = vt_bits(GIR_T_I8, if nn_quad(code) { 128 } else { 64 });
        let idx = bc(o[first + nt], rt);
        let fb = if tbx { bc(o[0], rt) } else { 0 };
        return tbl_q(vals[..], idx, tbx, fb, rt);
    }
    // loads and stores
    if f == "vld1" { return ins_load(T, o[0], false); }
    if f == "vld1_dup" { return splat_v(T, ins_load(elt_of(T), o[0], false)); }
    if f == "vld1_lane" {
        let v = bc(o[1], T);
        return emit(GIR_INSERTELT, T, 0, 0, 0, v, ins_load(elt_of(T), o[0], false), c_i32(nb_imm(n, 2)));
    }
    if f == "vst1" {
        ins_store(T, bc(o[1], T), o[0], false);
        return NONE;
    }
    if f == "vst1_lane" {
        let v = bc(o[1], T);
        ins_store(elt_of(T), emit(GIR_EXTRACTELT, elt_of(T), 0, 0, T, v, c_i32(nb_imm(n, 2)), 0), o[0], false);
        return NONE;
    }
    if starts_with(f, "vld1_x") {
        let cnt = (f[6] - '0') as i64;
        let d = o[0];
        let p = o[1];
        for i in 0..cnt {
            ins_store(T, ins_load(T, gep(p, i * tsize(T) as i64), false), gep(d, i * tsize(T) as i64), false);
        }
        return NONE;
    }
    if starts_with(f, "vst1_x") {
        let cnt = (f[6] - '0') as i64;
        let p = o[0];
        for i in 0..cnt { ins_store(T, bc(o[1 + i], T), gep(p, i * tsize(T) as i64), false); }
        return NONE;
    }
    if (starts_with(f, "vld2") || starts_with(f, "vld3") || starts_with(f, "vld4")) && f.len >= 4 {
        let cnt = (f[3] - '0') as i64;
        let d = o[0];
        let p = o[1];
        if f.len == 4 { ld_n(d, p, T, cnt, false, -1, vals[..0]); return NONE; }
        if ends_with(f, "_dup") { ld_n(d, p, T, cnt, true, -1, vals[..0]); return NONE; }
        if ends_with(f, "_lane") {
            vals.clear();
            for i in 0..cnt { vals.push(o[2 + i]); }
            ld_n(d, p, T, cnt, false, nb_imm(n, 2 + cnt), vals[..]);
            return NONE;
        }
    }
    if (starts_with(f, "vst2") || starts_with(f, "vst3") || starts_with(f, "vst4")) && f.len >= 4 {
        let cnt = (f[3] - '0') as i64;
        let p = o[0];
        vals.clear();
        for i in 0..cnt { vals.push(o[1 + i]); }
        if f.len == 4 { st_n(p, T, vals[..], -1); return NONE; }
        if ends_with(f, "_lane") { st_n(p, T, vals[..], nb_imm(n, 1 + cnt)); return NONE; }
    }
    if f == "vzip" || f == "vuzp" || f == "vtrn" {
        let d = o[0];
        let a = bc(o[1], T);
        let b = bc(o[2], T);
        let nl = lanes(T) as i64;
        for v in 0..2 {
            nn_idx.clear();
            for i in 0..nl {
                var x: i64 = 0;
                if f == "vzip" { x = (i >> 1) + (if i & 1 != 0 { nl } else { 0 }) + v * (nl >> 1); }
                else if f == "vuzp" { x = 2 * i + v; }
                else { x = (i & ~1) + v + (if i & 1 != 0 { nl } else { 0 }); }
                nn_idx.push(x);
            }
            ins_store(T, shuf(T, a, b, nn_idx[..]), gep(d, v * tsize(T) as i64), false);
        }
        return NONE;
    }
    // the cryptographic extension (fixed codes)
    if f == "vaese" || f == "vaesd" { return op2(if f == "vaese" { GIR_A64_AESE } else { GIR_A64_AESD }, T, bc(o[0], T), bc(o[1], T)); }
    if f == "vaesmc" || f == "vaesimc" { return op1(if f == "vaesmc" { GIR_A64_AESMC } else { GIR_A64_AESIMC }, T, bc(o[0], T)); }
    return KEEP_CALL;
}

// The builtins with concrete C types.
fn neon_mono(name: const u8[:], n: u32, rq: u32, o: const u32[:]) -> u32 {
    let nargs = nodes[n].c as i64;
    let z = c_i32(0);
    // crypto and dot products whose names carry the type
    if name == "vaeseq_u8" || name == "vaesdq_u8" || name == "vaesmcq_u8" || name == "vaesimcq_u8" {
        return neon_poly(name[..name.len - 3], n, rq, o);
    }
    if name == "vsha1cq_u32" || name == "vsha1pq_u32" || name == "vsha1mq_u32" {
        let k = if name[5] == 'c' { GIR_A64_SHA1C } else if name[5] == 'p' { GIR_A64_SHA1P } else { GIR_A64_SHA1M };
        let t = ty_vec(4, GIR_T_I32);
        return op3(k, t, t, bc(o[0], t), o[1], bc(o[2], t));
    }
    if name == "vsha1h_u32" { return op1(GIR_A64_SHA1H, GIR_T_I32, o[0]); }
    if name == "vsha1su0q_u32" || name == "vsha256hq_u32" || name == "vsha256h2q_u32" || name == "vsha256su1q_u32" {
        let k = if name == "vsha1su0q_u32" { GIR_A64_SHA1SU0 } else if name == "vsha256hq_u32" { GIR_A64_SHA256H }
                else if name == "vsha256h2q_u32" { GIR_A64_SHA256H2 } else { GIR_A64_SHA256SU1 };
        let t = ty_vec(4, GIR_T_I32);
        return op3(k, t, t, bc(o[0], t), bc(o[1], t), bc(o[2], t));
    }
    if name == "vsha1su1q_u32" || name == "vsha256su0q_u32" {
        let t = ty_vec(4, GIR_T_I32);
        return op2(if name == "vsha1su1q_u32" { GIR_A64_SHA1SU1 } else { GIR_A64_SHA256SU0 }, t, bc(o[0], t), bc(o[1], t));
    }
    if starts_with(name, "vdot") && nargs == 4 {
        let code = nb_imm(n, 3);
        let T = nn_vt(code);
        let bt = vt_bits(GIR_T_I8, if nn_quad(code) { 128 } else { 64 });
        return op3(if nn_uns(code) { GIR_A64_UDOT } else { GIR_A64_SDOT }, T, T, bc(o[0], T), bc(o[1], bt), bc(o[2], bt));
    }
    if starts_with(name, "vcvt_f32_f64") || starts_with(name, "vcvt_f64_f32") {
        if starts_with(name, "vcvt_f32_f64") { return vcast(GIR_FPTRUNC, ty_vec(2, GIR_T_F32), bc(o[0], ty_vec(2, GIR_T_F64))); }
        return vcast(GIR_FPEXT, ty_vec(2, GIR_T_F64), bc(o[0], ty_vec(2, GIR_T_F32)));
    }
    // scalar fused multiply-add by element: a + b * v[lane]
    if (starts_with(name, "vfmas_lane") || starts_with(name, "vfmad_lane")) && nargs == 4 {
        let v = o[2];
        let e = emit(GIR_EXTRACTELT, elt_of(vtype(v)), 0, 0, vtype(v), v, c_i32(nb_imm(n, 3)), 0);
        let t = vtype(o[0]);
        return emit(GIR_FMA, t, 0, 0, t, o[1], e, o[0]);
    }
    // saturating doubling multiply-accumulate long (scalar): sqdmull, then sqadd / sqsub
    if starts_with(name, "vqdmlal") || starts_with(name, "vqdmlsl") {
        var b = o[2];
        if find(name, "_lane") >= 0 && nargs == 4 {
            b = emit(GIR_EXTRACTELT, elt_of(vtype(b)), 0, 0, vtype(b), b, c_i32(nb_imm(n, 3)), 0);
        }
        let t = vtype(o[0]);
        let m = op2(GIR_A64_SQDMULL, t, o[1], b);
        return op2(if name[5] == 'a' { GIR_A64_SQADD } else { GIR_A64_SQSUB }, t, o[0], m);
    }
    // lanes
    if starts_with(name, "vget_lane_") || starts_with(name, "vgetq_lane_") || starts_with(name, "vdupb_lane") ||
       starts_with(name, "vduph_lane") || starts_with(name, "vdups_lane") || starts_with(name, "vdupd_lane") {
        let v = o[0];
        let t = vtype(v);
        return emit(GIR_EXTRACTELT, elt_of(t), 0, 0, t, v, c_i32(nb_imm(n, 1)), 0);
    }
    if starts_with(name, "vset_lane_") || starts_with(name, "vsetq_lane_") {
        let x = o[0];
        let v = o[1];
        let t = vtype(v);
        var xx = x;
        if vtype(x) != elt_of(t) {
            if tcls(elt_of(t)) == C_INT && tcls(vtype(x)) == C_INT { xx = int_cast(x, vtype(x), elt_of(t), false); }
            else { xx = bc(x, elt_of(t)); }
        }
        return emit(GIR_INSERTELT, t, 0, 0, 0, v, xx, c_i32(nb_imm(n, 2)));
    }
    // across lanes
    if (starts_with(name, "vaddv") || starts_with(name, "vmaxv") || starts_with(name, "vminv") || starts_with(name, "vaddlv") ||
        starts_with(name, "vmaxnmv") || starts_with(name, "vminnmv")) && nargs == 1 {
        let v = o[0];
        let t = vtype(v);
        let et = elt_of(t);
        let fp = tcls(et) == C_FP;
        let u = find(name, "_u") >= 0;
        let long = starts_with(name, "vaddlv");
        var k: i64 = 0;
        if starts_with(name, "vaddv") { k = if fp { GIR_A64_FADDV } else { GIR_A64_ADDV }; }
        else if long { k = if u { GIR_A64_UADDLV } else { GIR_A64_SADDLV }; }
        else if starts_with(name, "vmaxnmv") { k = GIR_A64_FMAXNMV; }
        else if starts_with(name, "vminnmv") { k = GIR_A64_FMINNMV; }
        else if starts_with(name, "vmaxv") { k = if fp { GIR_A64_FMAXV } else if u { GIR_A64_UMAXV } else { GIR_A64_SMAXV }; }
        else { k = if fp { GIR_A64_FMINV } else if u { GIR_A64_UMINV } else { GIR_A64_SMINV }; }
        if fp { return op1(k, et, v); }
        // (an i32 result, an i64 one for 64-bit lanes and long sums of 32-bit lanes, as clang's intrinsics)
        let rt: u32 = if elt_bits(t) == 64 || long && elt_bits(t) == 32 { GIR_T_I64 } else { GIR_T_I32 };
        return op1(k, rt, v);
    }
    // pairwise to a scalar (two lanes)
    if (starts_with(name, "vpaddd") || starts_with(name, "vpadds") || starts_with(name, "vpmax") || starts_with(name, "vpmin")) && nargs == 1 {
        let v = o[0];
        let et = elt_of(vtype(v));
        let fp = tcls(et) == C_FP;
        var k = GIR_A64_ADDV;
        if starts_with(name, "vpadd") { k = if fp { GIR_A64_FADDV } else { GIR_A64_ADDV }; }
        else if starts_with(name, "vpmaxnm") { k = GIR_A64_FMAXNMV; }
        else if starts_with(name, "vpminnm") { k = GIR_A64_FMINNMV; }
        else if starts_with(name, "vpmax") { k = GIR_A64_FMAXV; }
        else { k = GIR_A64_FMINV; }
        return op1(k, et, v);
    }
    // SISD: <op><b|h|s|d>[_n]_<type>
    let u = find(name, "_u") >= 0;
    let fp = find(name, "_f") >= 0;
    var k2: i64 = -1;
    var arity: i64 = 2;
    if starts_with(name, "vqadd") { k2 = if u { GIR_A64_UQADD } else { GIR_A64_SQADD }; }
    else if starts_with(name, "vqsub") { k2 = if u { GIR_A64_UQSUB } else { GIR_A64_SQSUB }; }
    else if starts_with(name, "vqdmulh") && find(name, "lane") < 0 { k2 = GIR_A64_SQDMULH; }
    else if starts_with(name, "vqrdmulh") && find(name, "lane") < 0 { k2 = GIR_A64_SQRDMULH; }
    else if starts_with(name, "vqrshl") { k2 = if u { GIR_A64_UQRSHL } else { GIR_A64_SQRSHL }; }
    else if starts_with(name, "vqshl") && find(name, "_n_") < 0 { k2 = if u { GIR_A64_UQSHL } else { GIR_A64_SQSHL }; }
    else if starts_with(name, "vrshl") { k2 = if u { GIR_A64_URSHL } else { GIR_A64_SRSHL }; }
    else if starts_with(name, "vshld") && find(name, "_n_") < 0 { k2 = if u { GIR_A64_USHL } else { GIR_A64_SSHL }; }
    else if starts_with(name, "vuqadd") { k2 = GIR_A64_SUQADD; }
    else if starts_with(name, "vsqadd") { k2 = GIR_A64_USQADD; }
    else if starts_with(name, "vabd") && fp { k2 = GIR_A64_FABD; }
    else if starts_with(name, "vmulx") && find(name, "lane") < 0 { k2 = GIR_A64_FMULX; }
    else if starts_with(name, "vrecps") && fp { k2 = GIR_A64_FRECPS; }
    else if starts_with(name, "vrsqrts") && fp { k2 = GIR_A64_FRSQRTS; }
    else if starts_with(name, "vqdmull") && find(name, "lane") < 0 { k2 = GIR_A64_SQDMULL; }
    else if starts_with(name, "vqabs") { k2 = GIR_A64_SQABS; arity = 1; }
    else if starts_with(name, "vqneg") { k2 = GIR_A64_SQNEG; arity = 1; }
    else if starts_with(name, "vabsd") { k2 = GIR_A64_ABS; arity = 1; }
    else if starts_with(name, "vqmovun") { k2 = GIR_A64_SQXTUN; arity = 1; }
    else if starts_with(name, "vqmovn") { k2 = if u { GIR_A64_UQXTN } else { GIR_A64_SQXTN }; arity = 1; }
    else if starts_with(name, "vrecpe") && fp { k2 = GIR_A64_FRECPE; arity = 1; }
    else if starts_with(name, "vrsqrte") && fp { k2 = GIR_A64_FRSQRTE; arity = 1; }
    else if starts_with(name, "vrndn") && fp { k2 = GIR_A64_FRINTN; arity = 1; }
    else if starts_with(name, "vcvtxd") { k2 = GIR_A64_FCVTXN; arity = 1; }
    if k2 >= 0 && nargs == arity {
        let a = o[0];
        if arity == 1 { return op1(k2, vty(rq), a); }
        var b = o[1];
        // the shift and accumulate operands are of the first operand's type
        if vtype(b) != vtype(a) && tcls(vtype(b)) == C_INT && k2 != GIR_A64_SQDMULL { b = int_cast(b, vtype(b), vtype(a), true); }
        return op2(k2, vty(rq), a, b);
    }
    // SISD conversions
    if starts_with(name, "vcvt") && !starts_with(name, "vcvt_") && find(name, "_n_") < 0 && nargs == 1 {
        // vcvt[a|m|n|p]<s|d>_<to>_<from>
        let to_int = name[name.len - 3] == 'f';
        let a = o[0];
        if to_int {
            let c = name[4];
            let us = find(name, "_u") >= 0;
            let k = if c == 'a' { if us { GIR_A64_FCVTAU } else { GIR_A64_FCVTAS } }
                    else if c == 'm' { if us { GIR_A64_FCVTMU } else { GIR_A64_FCVTMS } }
                    else if c == 'n' { if us { GIR_A64_FCVTNU } else { GIR_A64_FCVTNS } }
                    else if c == 'p' { if us { GIR_A64_FCVTPU } else { GIR_A64_FCVTPS } }
                    else { if us { GIR_A64_FCVTZU } else { GIR_A64_FCVTZS } };
            return op1(k, vty(rq), a);
        }
        // integer -> FP: plain conversions
        let us = name[name.len - 3] == 'u';
        return emit(if us { GIR_UITOFP } else { GIR_SITOFP }, vty(rq), 0, 0, vtype(a), a, 0, 0);
    }
    if starts_with(name, "vcvt") && find(name, "_n_") >= 0 && nargs == 2 {
        let a = o[0];
        let fb = nb_imm(n, 1);
        let to_int = name[name.len - 3] == 'f';
        if to_int {
            let us = find(name, "_n_u") >= 0;
            return op2(if us { GIR_A64_FCVTZU_FX } else { GIR_A64_FCVTZS_FX }, vty(rq), a, c_i32(fb));
        }
        let us = name[name.len - 3] == 'u';
        return op2(if us { GIR_A64_UCVTF_FX } else { GIR_A64_SCVTF_FX }, vty(rq), a, c_i32(fb));
    }
    // SISD shifts by an immediate
    if find(name, "_n_") >= 0 && (nargs == 2 || nargs == 3) {
        let a = o[0];
        let t = vtype(a);
        let bits = tsize(t) as i64 * 8;
        if starts_with(name, "vshld_n") { return ins_bin(GIR_SHL, t, a, c_int(nb_imm(n, 1) as! u64, t)); }
        if starts_with(name, "vshrd_n") || starts_with(name, "vsrad_n") {
            let src = if nargs == 3 { 1 } else { 0 };
            let x = o[src];
            let sh = nb_imm(n, src + 1);
            var r: u32 = 0;
            if sh >= bits && u { r = c_zero(t); }
            else { r = ins_bin(if u { GIR_LSHR } else { GIR_ASHR }, t, x, c_int((if sh >= bits { bits - 1 } else { sh }) as! u64, t)); }
            if nargs == 2 { return r; }
            return ins_bin(GIR_ADD, t, a, r);
        }
        if starts_with(name, "vrshrd_n") || starts_with(name, "vrsrad_n") {
            let src = if nargs == 3 { 1 } else { 0 };
            let r = op2(if u { GIR_A64_URSHL } else { GIR_A64_SRSHL }, t, o[src], c_int((-nb_imm(n, src + 1)) as! u64, t));
            if nargs == 2 { return r; }
            return ins_bin(GIR_ADD, t, a, r);
        }
        if starts_with(name, "vqshl") && find(name, "vqshlu") < 0 {
            return op2(if u { GIR_A64_UQSHL } else { GIR_A64_SQSHL }, t, a, c_int(nb_imm(n, 1) as! u64, t));
        }
        if starts_with(name, "vqshlu") {
            return op2(GIR_A64_SQSHLU, t, a, c_int(nb_imm(n, 1) as! u64, t));
        }
        if starts_with(name, "vslid_n") || starts_with(name, "vsrid_n") {
            return op3(if name[2] == 'l' { GIR_A64_SLI } else { GIR_A64_SRI }, t, t, a, o[1], c_i32(nb_imm(n, 2)));
        }
        var k: i64 = -1;
        if starts_with(name, "vqshrn") { k = if u { GIR_A64_UQSHRN } else { GIR_A64_SQSHRN }; }
        else if starts_with(name, "vqrshrn") { k = if u { GIR_A64_UQRSHRN } else { GIR_A64_SQRSHRN }; }
        else if starts_with(name, "vqshrun") { k = GIR_A64_SQSHRUN; }
        else if starts_with(name, "vqrshrun") { k = GIR_A64_SQRSHRUN; }
        if k >= 0 { return op2(k, vty(rq), a, c_i32(nb_imm(n, 1))); }
    }
    // scalar compares (all ones / zero)
    if (starts_with(name, "vceq") || starts_with(name, "vcge") || starts_with(name, "vcgt") || starts_with(name, "vcle") ||
        starts_with(name, "vclt") || starts_with(name, "vtst") || starts_with(name, "vcage") || starts_with(name, "vcagt") ||
        starts_with(name, "vcale") || starts_with(name, "vcalt")) && (nargs == 1 || nargs == 2) && !is_vector(rq) {
        let a = o[0];
        let t = vtype(a);
        let isfp = tcls(t) == C_FP;
        let zero = nargs == 1;
        var b = if zero { c_zero(t) } else { o[1] };
        var x = a;
        let rt = vty(rq);
        var c: u32 = 0;
        if starts_with(name, "vca") {
            x = emit(GIR_FABS, t, 0, 0, t, a, 0, 0);
            b = emit(GIR_FABS, t, 0, 0, t, b, 0, 0);
        }
        let s2 = if starts_with(name, "vca") { name[3] } else { name[2] };
        let s3 = if starts_with(name, "vca") { name[4] } else { name[3] };
        if starts_with(name, "vtst") {
            c = ins_icmp(GIR_NE, t, ins_bin(GIR_AND, t, a, b), c_zero(t));
        } else if isfp {
            let p = if s2 == 'e' { F_OEQ } else if s2 == 'g' && s3 == 'e' { F_OGE } else if s2 == 'g' { F_OGT }
                    else if s3 == 'e' { F_OLE } else { F_OLT };
            c = ins_fcmp(p, t, x, b);
        } else {
            let uu = find(name, "_u") >= 0;
            let p = if s2 == 'e' { GIR_EQ } else if s2 == 'g' && s3 == 'e' { if uu { GIR_UGE } else { GIR_SGE } }
                    else if s2 == 'g' { if uu { GIR_UGT } else { GIR_SGT } } else if s3 == 'e' { if uu { GIR_ULE } else { GIR_SLE } }
                    else { if uu { GIR_ULT } else { GIR_SLT } };
            c = ins_icmp(p, t, x, b);
        }
        return int_cast(c, GIR_T_I1, rt, true);
    }
    // scalar arithmetic in the SIMD&FP registers that is generic IR
    if (starts_with(name, "vaddd_") || starts_with(name, "vsubd_")) && nargs == 2 {
        let a = o[0];
        return ins_bin(if name[1] == 'a' { GIR_ADD } else { GIR_SUB }, vtype(a), a, o[1]);
    }
    if starts_with(name, "vmul_n_f64") {
        let a = o[0];
        let s = o[1];
        return emit(GIR_FMUL, vtype(a), 0, 0, 0, a, bc(s, vtype(a)), 0);
    }
    return KEEP_CALL;
}
