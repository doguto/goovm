// AArch64 NEON and ACLE operations (GIR_A64, milestone F1; gir.h GirA64):
// each the instruction of that name, in its vector arrangement (from the
// type: lanes, 64 or 128 bits) or its scalar (SISD) form for scalar types and
// one-lane 64-bit vectors. Lowered in the memory tier (a64mem.goose): the
// operands go to v0, v1, v2 (scalars in GPRs through x0), the result comes
// back from v0 (or x0); table registers are v16..v19.

// Arrangement of type t: q (16 bytes), size (lane size log2), fp lanes, lanes,
// scalar (a scalar type or one 64-bit lane: the SISD encodings).
struct NArr { q: bool, size: u32, fp: bool, n: u32, scalar: bool }
fn n_arr(t: u32) -> NArr {
    let T = M.types[t];
    if T.kind == TK_VECTOR {
        let L = M.types[T.elems];
        let s = a_log2(L.size);
        return NArr { q: T.store == 16, size: s, fp: L.cls == C_FP, n: T.n, scalar: T.n == 1 };
    }
    return NArr { q: false, size: a_log2(T.store), fp: T.cls == C_FP, n: 1, scalar: true };
}
// The scalar / vector 3-same, 2-misc and shift-by-immediate bases.
checkfree fn n_s3(u: u32, size: u32, opc: u32, vd: u32, vn: u32, vm: u32) {
    a4(0x5E200400 | (u << 29) | (size << 22) | ((vm & 31) << 16) | (opc << 11) | ((vn & 31) << 5) | (vd & 31));
}
checkfree fn n_s2(u: u32, size: u32, opc: u32, vd: u32, vn: u32) {
    a4(0x5E200800 | (u << 29) | (size << 22) | (opc << 12) | ((vn & 31) << 5) | (vd & 31));
}
checkfree fn n_ssh(u: u32, immhb: u32, opc: u32, vd: u32, vn: u32) {
    a4(0x5F000400 | (u << 29) | (immhb << 16) | (opc << 11) | ((vn & 31) << 5) | (vd & 31));
}
checkfree fn n_v3d(q: bool, u: u32, size: u32, opc: u32, vd: u32, vn: u32, vm: u32) {
    a4(0x0E200000 | (if q { 0x40000000 as u32 } else { 0 }) | (u << 29) | (size << 22) | ((vm & 31) << 16) | (opc << 12)
       | ((vn & 31) << 5) | (vd & 31));
}
// The constant value of operand v (an INT constant, or lane 0 of a vector constant).
fn n_imm(v: u32) -> u64 {
    if gir_kind(v) != GIR_V_CONST { return 0; }
    return a_const_bits(gir_idx(v));
}
// Operand v of type t into V register r (a GPR scalar through x0).
fn n_in(v: u32, r: u32) {
    let t = type_of(v);
    if arc(t) == ARC_GPR {
        b_gpr(v, AX0);
        a_fmov_from_gp(M.types[t].store == 8, r, AX0);
        return;
    }
    if a_inv(arc(t)) {
        b_vr(v, r);
        return;
    }
    let b, o = a_val_mem(v, AX16);
    if is_val(v) { a_note(vid(v)); }
    a_ls(LS_FLDR, a_log2(M.types[t].store), r, b, o);
}
// The result in v0 to instruction j of type t (a GPR result from lane 0, sign- or
// zero-extended from `lb` bytes).
fn n_out(j: u32, t: u32, lb: u32, sgn: bool) {
    if arc(t) == ARC_GPR {
        let s = a_log2(lb);
        let w64 = M.types[t].store == 8;
        if s == 3 { a_fmov_to_gp(true, AX0, AV0); }
        else if s == 2 && (!sgn || !w64) { a_fmov_to_gp(false, AX0, AV0); }
        else if sgn { a_smov(w64, s, AX0, AV0, 0); }
        else { a_umov(s, AX0, AV0, 0); }
        if !exact_width(bits_of(t)) { a_zext(AX0, bits_of(t)); }
        b_set(j, AX0, false);
        return;
    }
    if a_inv(arc(t)) {
        b_set(j, AV0, false);
        return;
    }
    let ro = b_res(j);
    a_ls(LS_FSTR, a_log2(M.types[t].store), AV0, AFP, ro);
}

// Integer 3-same: (U, opcode) per GirA64 id.
fn n_int3(k: u32) -> u32, u32 {
    if k == GIR_A64_SQADD { return 0, 0x01; }
    if k == GIR_A64_UQADD { return 1, 0x01; }
    if k == GIR_A64_SQSUB { return 0, 0x05; }
    if k == GIR_A64_UQSUB { return 1, 0x05; }
    if k == GIR_A64_SHADD { return 0, 0x00; }
    if k == GIR_A64_UHADD { return 1, 0x00; }
    if k == GIR_A64_SRHADD { return 0, 0x02; }
    if k == GIR_A64_URHADD { return 1, 0x02; }
    if k == GIR_A64_SHSUB { return 0, 0x04; }
    if k == GIR_A64_UHSUB { return 1, 0x04; }
    if k == GIR_A64_SMAX { return 0, 0x0C; }
    if k == GIR_A64_UMAX { return 1, 0x0C; }
    if k == GIR_A64_SMIN { return 0, 0x0D; }
    if k == GIR_A64_UMIN { return 1, 0x0D; }
    if k == GIR_A64_SABD { return 0, 0x0E; }
    if k == GIR_A64_UABD { return 1, 0x0E; }
    if k == GIR_A64_SSHL { return 0, 0x08; }
    if k == GIR_A64_USHL { return 1, 0x08; }
    if k == GIR_A64_SQSHL { return 0, 0x09; }
    if k == GIR_A64_UQSHL { return 1, 0x09; }
    if k == GIR_A64_SRSHL { return 0, 0x0A; }
    if k == GIR_A64_URSHL { return 1, 0x0A; }
    if k == GIR_A64_SQRSHL { return 0, 0x0B; }
    if k == GIR_A64_UQRSHL { return 1, 0x0B; }
    if k == GIR_A64_ADDP { return 0, 0x17; }
    if k == GIR_A64_SMAXP { return 0, 0x14; }
    if k == GIR_A64_UMAXP { return 1, 0x14; }
    if k == GIR_A64_SMINP { return 0, 0x15; }
    if k == GIR_A64_UMINP { return 1, 0x15; }
    if k == GIR_A64_SQDMULH { return 0, 0x16; }
    if k == GIR_A64_SQRDMULH { return 1, 0x16; }
    return 1, 0x13;   // PMUL
}
// FP 3-same: (U, high size bit, opcode).
fn n_fp3(k: u32) -> u32, u32, u32 {
    if k == GIR_A64_FMAX { return 0, 0, 0x1E; }
    if k == GIR_A64_FMIN { return 0, 1, 0x1E; }
    if k == GIR_A64_FMAXNM { return 0, 0, 0x18; }
    if k == GIR_A64_FMINNM { return 0, 1, 0x18; }
    if k == GIR_A64_FABD { return 1, 1, 0x1A; }
    if k == GIR_A64_FMULX { return 0, 0, 0x1B; }
    if k == GIR_A64_FRECPS { return 0, 0, 0x1F; }
    if k == GIR_A64_FRSQRTS { return 0, 1, 0x1F; }
    if k == GIR_A64_FACGE { return 1, 0, 0x1D; }
    if k == GIR_A64_FACGT { return 1, 1, 0x1D; }
    if k == GIR_A64_FADDP { return 1, 0, 0x1A; }
    if k == GIR_A64_FMAXP { return 1, 0, 0x1E; }
    if k == GIR_A64_FMINP { return 1, 1, 0x1E; }
    if k == GIR_A64_FMAXNMP { return 1, 0, 0x18; }
    return 1, 1, 0x18;   // FMINNMP
}
// 2-misc: (U, high size bit for FP, opcode, FP)
fn n_misc(k: u32) -> u32, u32, u32, bool {
    if k == GIR_A64_SQABS { return 0, 0, 0x07, false; }
    if k == GIR_A64_SQNEG { return 1, 0, 0x07, false; }
    if k == GIR_A64_ABS { return 0, 0, 0x0B, false; }
    if k == GIR_A64_CLS { return 0, 0, 0x04, false; }
    if k == GIR_A64_CLZ { return 1, 0, 0x04, false; }
    if k == GIR_A64_CNT { return 0, 0, 0x05, false; }
    if k == GIR_A64_RBIT { return 1, 0, 0x05, false; }
    if k == GIR_A64_SADDLP { return 0, 0, 0x02, false; }
    if k == GIR_A64_UADDLP { return 1, 0, 0x02, false; }
    if k == GIR_A64_SQXTN { return 0, 0, 0x14, false; }
    if k == GIR_A64_UQXTN { return 1, 0, 0x14, false; }
    if k == GIR_A64_SQXTUN { return 1, 0, 0x12, false; }
    if k == GIR_A64_URECPE { return 0, 1, 0x1C, true; }
    if k == GIR_A64_URSQRTE { return 1, 1, 0x1C, true; }
    if k == GIR_A64_FRECPE { return 0, 1, 0x1D, true; }
    if k == GIR_A64_FRSQRTE { return 1, 1, 0x1D, true; }
    if k == GIR_A64_FCVTZS { return 0, 1, 0x1B, true; }
    if k == GIR_A64_FCVTZU { return 1, 1, 0x1B, true; }
    if k == GIR_A64_FCVTNS { return 0, 0, 0x1A, true; }
    if k == GIR_A64_FCVTNU { return 1, 0, 0x1A, true; }
    if k == GIR_A64_FCVTMS { return 0, 0, 0x1B, true; }
    if k == GIR_A64_FCVTMU { return 1, 0, 0x1B, true; }
    if k == GIR_A64_FCVTPS { return 0, 1, 0x1A, true; }
    if k == GIR_A64_FCVTPU { return 1, 1, 0x1A, true; }
    if k == GIR_A64_FCVTAS { return 0, 0, 0x1C, true; }
    if k == GIR_A64_FCVTAU { return 1, 0, 0x1C, true; }
    if k == GIR_A64_FCVTXN { return 1, 0, 0x16, true; }
    if k == GIR_A64_FRINTN { return 0, 0, 0x18, true; }
    if k == GIR_A64_FRINTM { return 0, 0, 0x19, true; }
    if k == GIR_A64_FRINTP { return 0, 1, 0x18, true; }
    if k == GIR_A64_FRINTZ { return 0, 1, 0x19, true; }
    if k == GIR_A64_FRINTA { return 1, 0, 0x18, true; }
    if k == GIR_A64_FRINTX { return 1, 0, 0x19, true; }
    return 1, 1, 0x19, true;   // FRINTI
}
// The fp <-> gpr conversion opcode (rmode:opcode) of a scalar fcvt*.
fn n_fcvt_gp(k: u32) -> u32 {
    if k == GIR_A64_FCVTZS { return AFC_FCVTZS; }
    if k == GIR_A64_FCVTZU { return AFC_FCVTZU; }
    if k == GIR_A64_FCVTNS { return 0x00; }
    if k == GIR_A64_FCVTNU { return 0x01; }
    if k == GIR_A64_FCVTMS { return 0x10; }
    if k == GIR_A64_FCVTMU { return 0x11; }
    if k == GIR_A64_FCVTPS { return 0x08; }
    if k == GIR_A64_FCVTPU { return 0x09; }
    if k == GIR_A64_FCVTAS { return 0x04; }
    return 0x05;
}

fn b_lower_a64(I: Inst, j: u32) {
    let k: u32 = I.sub;
    let rt: u32 = I.ty;
    if k == GIR_A64_DMB || k == GIR_A64_DSB || k == GIR_A64_ISB {
        let crm: u32 = (n_imm(I.a) & 15) as! u32;
        let base: u32 = if k == GIR_A64_DMB { 0xD50330BF } else if k == GIR_A64_DSB { 0xD503309F } else { 0xD50330DF };
        a4(base | (crm << 8));
        return;
    }
    if k == GIR_A64_HINT {
        a4(0xD503201F | (((n_imm(I.a) & 127) as! u32) << 5));
        return;
    }
    if k == GIR_A64_THREAD_POINTER {
        a_mrs_tpidr(AX0);
        b_set(j, AX0, false);
        return;
    }
    let at = type_of(I.a);
    let A = n_arr(at);
    let R = n_arr(rt);
    if k == GIR_A64_CLS && arc(at) == ARC_GPR {
        // cls on a GPR (ACLE __cls / __clsll)
        b_gpr(I.a, AX0);
        a4(0x5AC01400 | (if M.types[at].store == 8 { 0x80000000 as u32 } else { 0 }) | (AX0 << 5) | AX0);
        b_set(j, AX0, true);
        return;
    }
    // same-type integer operations
    if k <= GIR_A64_PMUL {
        if A.fp {
            // (fmax / fmin / ... are FP ids below; an integer op on an FP type does not occur)
            a_brk(1);
            return;
        }
        n_in(I.a, AV0);
        n_in(I.b, AV0 + 1);
        let u, opc = n_int3(k);
        if A.scalar { n_s3(u, A.size, opc, AV0, AV0, AV0 + 1); }
        else { a_v3(A.q, u, A.size, opc, AV0, AV0, AV0 + 1); }
        n_out(j, rt, 1 << R.size, false);
        return;
    }
    if k <= GIR_A64_FMINNMP {
        n_in(I.a, AV0);
        n_in(I.b, AV0 + 1);
        let u, hi, opc = n_fp3(k);
        let sz: u32 = if A.size == 3 { 1 } else { 0 };
        if A.scalar && (k == GIR_A64_FMAX || k == GIR_A64_FMIN || k == GIR_A64_FMAXNM || k == GIR_A64_FMINNM) {
            let kk: u32 = if k == GIR_A64_FMAX { AF2_FMAX } else if k == GIR_A64_FMIN { AF2_FMIN }
                          else if k == GIR_A64_FMAXNM { AF2_FMAXNM } else { AF2_FMINNM };
            a_fp2(sz, kk, AV0, AV0, AV0 + 1);
        } else if A.scalar {
            n_s3(u, (hi << 1) | sz, opc, AV0, AV0, AV0 + 1);
        } else {
            a_v3(A.q, u, (hi << 1) | sz, opc, AV0, AV0, AV0 + 1);
        }
        n_out(j, rt, 1 << R.size, false);
        return;
    }
    if k == GIR_A64_SUQADD || k == GIR_A64_USQADD {
        n_in(I.a, AV0);
        n_in(I.b, AV0 + 1);
        let u: u32 = if k == GIR_A64_USQADD { 1 } else { 0 };
        if A.scalar { n_s2(u, A.size, 0x03, AV0, AV0 + 1); } else { a_v2(A.q, u, A.size, 0x03, AV0, AV0 + 1); }
        n_out(j, rt, 1 << R.size, false);
        return;
    }
    if k <= GIR_A64_RBIT {
        // unary
        let u, hi, opc, fpk = n_misc(k);
        let isfp_src = A.fp;
        if A.scalar && isfp_src && arc(rt) == ARC_GPR && k >= GIR_A64_FCVTZS && k <= GIR_A64_FCVTAU {
            // fp -> integer scalar: the conversion into a GPR
            n_in(I.a, AV0);
            a_fcvt_gp(M.types[rt].store == 8, if A.size == 3 { 1 } else { 0 }, n_fcvt_gp(k), AX0, AV0);
            b_set(j, AX0, false);
            return;
        }
        if A.scalar && isfp_src && k >= GIR_A64_FRINTN && k <= GIR_A64_FRINTI {
            n_in(I.a, AV0);
            let f1: u32 = if k == GIR_A64_FRINTN { AF1_FRINTN } else if k == GIR_A64_FRINTP { AF1_FRINTP }
                          else if k == GIR_A64_FRINTM { AF1_FRINTM } else if k == GIR_A64_FRINTZ { AF1_FRINTZ }
                          else if k == GIR_A64_FRINTA { AF1_FRINTA } else if k == GIR_A64_FRINTX { AF1_FRINTX } else { AF1_FRINTI };
            a_fp1(if A.size == 3 { 1 } else { 0 }, f1, AV0, AV0);
            n_out(j, rt, 1 << R.size, false);
            return;
        }
        n_in(I.a, AV0);
        var size: u32 = A.size;
        var q = A.q;
        if fpk {
            let sz: u32 = if k == GIR_A64_FCVTXN { 1 } else if A.size == 3 { 1 } else { 0 };
            size = (hi << 1) | sz;
        }
        if k == GIR_A64_RBIT { size = 1; }      // (rbit is size 01 of the NOT encoding)
        if k == GIR_A64_SQXTN || k == GIR_A64_UQXTN || k == GIR_A64_SQXTUN || k == GIR_A64_FCVTXN {
            // narrow: the destination's lane size, the low half
            if !fpk { size = R.size; }
            q = false;
        }
        if A.scalar && !(k == GIR_A64_SQXTN || k == GIR_A64_UQXTN || k == GIR_A64_SQXTUN || k == GIR_A64_FCVTXN) {
            n_s2(u, size, opc, AV0, AV0);
        } else if A.scalar || R.scalar && (k == GIR_A64_SQXTN || k == GIR_A64_UQXTN || k == GIR_A64_SQXTUN || k == GIR_A64_FCVTXN) {
            n_s2(u, if fpk { size } else { R.size }, opc, AV0, AV0);
        } else {
            a_v2(q, u, size, opc, AV0, AV0);
        }
        n_out(j, rt, 1 << R.size, false);
        return;
    }
    if k <= GIR_A64_FADDV {
        n_in(I.a, AV0);
        let sgn = k == GIR_A64_SMAXV || k == GIR_A64_SMINV || k == GIR_A64_SADDLV;
        if A.fp {
            let sz: u32 = if A.size == 3 { 1 } else { 0 };
            let mn: u32 = if k == GIR_A64_FMINV || k == GIR_A64_FMINNMV { 1 } else { 0 };
            let nm = k == GIR_A64_FMAXNMV || k == GIR_A64_FMINNMV;
            if k == GIR_A64_FADDV {
                if A.q && A.size == 2 { a_v3(true, 1, 0, 0x1A, AV0, AV0, AV0); }   // faddp v.4s
                a4(0x7E30D800 | (sz << 22));                                        // faddp s0/d0, v0.2s/2d
            } else if A.q && A.size == 2 {
                // fmaxv / fminv / fmaxnmv / fminnmv s0, v0.4s
                a_vacross(true, 1, mn << 1, if nm { 0x0C } else { 0x0F }, AV0, AV0);
            } else {
                // two lanes: the pairwise scalar form
                a4((if nm { 0x7E30C800 as u32 } else { 0x7E30F800 }) | (mn << 23) | (sz << 22));
            }
            n_out(j, rt, 1 << A.size, false);
            return;
        }
        let long = k == GIR_A64_SADDLV || k == GIR_A64_UADDLV;
        let u: u32 = if k == GIR_A64_UMAXV || k == GIR_A64_UMINV || k == GIR_A64_UADDLV { 1 } else { 0 };
        if A.n == 2 {
            // 2 x 32 / 2 x 64 lanes: the pairwise operations
            if long {
                a_v2(A.q, u, A.size, 0x02, AV0, AV0);          // [su]addlp v0.1d, v0.2s
            } else if k == GIR_A64_ADDV {
                if A.size == 3 { a4(0x5EF1B800); } else { a_v3(false, 0, A.size, 0x17, AV0, AV0, AV0); }
            } else {
                let opc: u32 = if k == GIR_A64_SMAXV || k == GIR_A64_UMAXV { 0x14 } else { 0x15 };
                a_v3(false, u, A.size, opc, AV0, AV0, AV0);
            }
        } else {
            let opc: u32 = if k == GIR_A64_ADDV { 0x1B } else if k == GIR_A64_SMAXV || k == GIR_A64_UMAXV { 0x0A }
                           else if long { 0x03 } else { 0x1A };
            a_vacross(A.q, u, A.size, opc, AV0, AV0);
        }
        let lb: u32 = if long { 2 << A.size } else { 1 << A.size };
        n_out(j, rt, lb, sgn);
        return;
    }
    if k <= GIR_A64_RSUBHN {
        n_in(I.a, AV0);
        n_in(I.b, AV0 + 1);
        if A.scalar {
            // sqdmull s/d scalar
            a4(0x5E200000 | (A.size << 22) | (1 << 16) | (0x0D << 12) | 0);
            n_out(j, rt, 1 << R.size, false);
            return;
        }
        let u: u32 = if k == GIR_A64_UMULL || k == GIR_A64_RADDHN || k == GIR_A64_RSUBHN { 1 } else { 0 };
        let opc: u32 = if k == GIR_A64_SMULL || k == GIR_A64_UMULL { 0x0C } else if k == GIR_A64_SQDMULL { 0x0D }
                       else if k == GIR_A64_PMULL { 0x0E } else if k == GIR_A64_RADDHN { 0x04 } else { 0x06 };
        let narrow = k == GIR_A64_RADDHN || k == GIR_A64_RSUBHN;
        n_v3d(false, u, if narrow { R.size } else { A.size }, opc, AV0, AV0, AV0 + 1);
        n_out(j, rt, 1 << R.size, false);
        return;
    }
    if k <= GIR_A64_FCVTZU_FX {
        // shifts by immediate
        n_in(I.a, AV0);
        var amt: u64 = 0;
        if k == GIR_A64_SLI || k == GIR_A64_SRI {
            n_in(I.b, AV0 + 1);
            amt = n_imm(I.c);
        } else {
            amt = n_imm(I.b);
        }
        let narrow = k >= GIR_A64_RSHRN && k <= GIR_A64_SQRSHRUN;
        let es: u32 = 8 << (if narrow { R.size } else { A.size });
        var u: u32 = 0;
        var opc: u32 = 0;
        var left = false;
        if k == GIR_A64_SQSHLU { u = 1; opc = 0x0C; left = true; }
        else if k == GIR_A64_RSHRN { u = 0; opc = 0x11; }
        else if k == GIR_A64_SQSHRN { u = 0; opc = 0x12; }
        else if k == GIR_A64_UQSHRN { u = 1; opc = 0x12; }
        else if k == GIR_A64_SQRSHRN { u = 0; opc = 0x13; }
        else if k == GIR_A64_UQRSHRN { u = 1; opc = 0x13; }
        else if k == GIR_A64_SQSHRUN { u = 1; opc = 0x10; }
        else if k == GIR_A64_SQRSHRUN { u = 1; opc = 0x11; }
        else if k == GIR_A64_SLI { u = 1; opc = 0x0A; left = true; }
        else if k == GIR_A64_SRI { u = 1; opc = 0x08; }
        else if k == GIR_A64_SCVTF_FX { u = 0; opc = 0x1C; }
        else if k == GIR_A64_UCVTF_FX { u = 1; opc = 0x1C; }
        else if k == GIR_A64_FCVTZS_FX { u = 0; opc = 0x1F; }
        else { u = 1; opc = 0x1F; }
        let sh: u32 = (amt & 127) as! u32;
        let immhb: u32 = if left { es + sh } else { 2 * es - sh };
        if (k >= GIR_A64_SCVTF_FX) && A.scalar && arc(at) == ARC_GPR || (k >= GIR_A64_FCVTZS_FX) && A.scalar && arc(rt) == ARC_GPR {
            // fixed-point conversions with a general register
            let fx64 = M.types[if k >= GIR_A64_FCVTZS_FX { rt } else { at }].store == 8;
            let ft: u32 = if M.types[if k >= GIR_A64_FCVTZS_FX { at } else { rt }].store == 8 { 1 } else { 0 };
            let base: u32 = if k == GIR_A64_SCVTF_FX { 0x1E020000 } else if k == GIR_A64_UCVTF_FX { 0x1E030000 }
                            else if k == GIR_A64_FCVTZS_FX { 0x1E180000 } else { 0x1E190000 };
            if k >= GIR_A64_FCVTZS_FX {
                a4(base | sfb(fx64) | (ft << 22) | ((64 - sh) << 10) | ((AV0 & 31) << 5) | AX0);
                b_set(j, AX0, false);
            } else {
                b_gpr(I.a, AX0);
                a4(base | sfb(fx64) | (ft << 22) | ((64 - sh) << 10) | (AX0 << 5) | (AV0 & 31));
                n_out(j, rt, 1 << R.size, false);
            }
            return;
        }
        let src: u32 = if k == GIR_A64_SLI || k == GIR_A64_SRI { AV0 + 1 } else { AV0 };
        if A.scalar && !narrow { n_ssh(u, immhb, opc, AV0, src); }
        else if A.scalar || narrow && R.scalar { n_ssh(u, immhb, opc, AV0, src); }
        else { a_vsh(if narrow { false } else { A.q }, u, immhb, opc, AV0, src); }
        n_out(j, rt, 1 << R.size, false);
        return;
    }
    if k == GIR_A64_SQDMULH_LANE || k == GIR_A64_SQRDMULH_LANE {
        n_in(I.a, AV0);
        n_in(I.b, AV0 + 1);
        let lane: u32 = (n_imm(I.c) & 15) as! u32;
        let opc: u32 = if k == GIR_A64_SQDMULH_LANE { 0xC000 } else { 0xD000 };
        var h: u32 = 0;
        var l: u32 = 0;
        var m: u32 = 0;
        if A.size == 1 {
            h = (lane >> 2) & 1;
            l = (lane >> 1) & 1;
            m = lane & 1;
        } else {
            h = (lane >> 1) & 1;
            l = lane & 1;
        }
        let base: u32 = if A.scalar { 0x5F000000 } else { 0x0F000000 | (if A.q { 0x40000000 as u32 } else { 0 }) };
        a4(base | opc | (A.size << 22) | (l << 21) | (m << 20) | (1 << 16) | (h << 11) | 0);
        n_out(j, rt, 1 << R.size, false);
        return;
    }
    if k == GIR_A64_TBL || k == GIR_A64_TBX {
        // the table in v16.., the indices in v1, the result (TBX: the kept lanes) in v0
        let tt = type_of(I.a);
        let nt = M.types[tt].store / 16;
        if a_inv(arc(tt)) { b_vr(I.a, AV0 + 16); }
        else {
            let b, o = a_val_mem(I.a, AX16);
            if is_val(I.a) { a_note(vid(I.a)); }
            for q in 0..nt { a_ls(LS_FLDR, 4, AV0 + 16 + q, b, o + 16 * q as i64); }
        }
        n_in(I.b, AV0 + 1);
        if k == GIR_A64_TBX { n_in(I.c, AV0); }
        a4(0x0E000000 | (if R.q { 0x40000000 as u32 } else { 0 }) | (1 << 16) | ((nt - 1) << 13)
           | (if k == GIR_A64_TBX { 0x1000 as u32 } else { 0 }) | (16 << 5) | 0);
        n_out(j, rt, 1, false);
        return;
    }
    if k == GIR_A64_MRS {
        let sr: u32 = (n_imm(I.a) & 0xFFFF) as! u32;
        a4(0xD5200000 | (sr << 5) | AX0);
        b_set(j, AX0, false);
        return;
    }
    if k == GIR_A64_MSR {
        let sr: u32 = (n_imm(I.a) & 0xFFFF) as! u32;
        b_gpr(I.b, AX0);
        a4(0xD5000000 | (sr << 5) | AX0);
        return;
    }
    if k >= GIR_A64_CRC32B && k <= GIR_A64_CRC32CX {
        let sz: u32 = (k - GIR_A64_CRC32B) & 3;
        let c: u32 = if k >= GIR_A64_CRC32CB { 1 } else { 0 };
        b_gpr(I.a, AX0);
        b_gpr(I.b, AX1);
        a4(0x1AC04000 | (if sz == 3 { 0x80000000 as u32 } else { 0 }) | (AX1 << 16) | (c << 12) | (sz << 10) | (AX0 << 5) | AX0);
        b_set(j, AX0, true);
        return;
    }
    if k == GIR_A64_LDXR || k == GIR_A64_LDAXR {
        let sz = a_log2(M.types[I.aux].store);
        b_gpr(I.a, AX1);
        if k == GIR_A64_LDXR { a_ldxr(sz, AX0, AX1); } else { a_ldaxr(sz, AX0, AX1); }
        b_set(j, AX0, true);
        return;
    }
    if k == GIR_A64_STXR || k == GIR_A64_STLXR {
        let sz = a_log2(M.types[I.aux].store);
        b_gpr(I.a, AX2);
        b_gpr(I.b, AX1);
        if k == GIR_A64_STXR { a_stxr(sz, AX0, AX2, AX1); } else { a_stlxr(sz, AX0, AX2, AX1); }
        b_set(j, AX0, true);
        return;
    }
    if k == GIR_A64_CLREX {
        a4(0xD5033F5F);
        return;
    }
    if k >= GIR_A64_AESE && k <= GIR_A64_AESIMC {
        // aese / aesd: v0 = data, v1 = key; aesmc / aesimc: v0
        n_in(I.a, AV0);
        if k <= GIR_A64_AESD {
            n_in(I.b, AV0 + 1);
            a4((if k == GIR_A64_AESE { 0x4E284800 as u32 } else { 0x4E285800 }) | (1 << 5));
        } else {
            a4(if k == GIR_A64_AESMC { 0x4E286800 as u32 } else { 0x4E287800 });
        }
        n_out(j, rt, 16, false);
        return;
    }
    if k == GIR_A64_SHA1H || k == GIR_A64_SHA1SU1 || k == GIR_A64_SHA256SU0 {
        n_in(I.a, AV0);
        if k == GIR_A64_SHA1H { a4(0x5E280800); }
        else {
            n_in(I.b, AV0 + 1);
            a4((if k == GIR_A64_SHA1SU1 { 0x5E281800 as u32 } else { 0x5E282800 }) | (1 << 5));
        }
        n_out(j, rt, if k == GIR_A64_SHA1H { 4 as u32 } else { 16 }, false);
        return;
    }
    if k >= GIR_A64_SHA1C && k <= GIR_A64_SHA256SU1 {
        // three registers: (v0, v1 (sha1c/p/m: s1), v2)
        n_in(I.a, AV0);
        n_in(I.b, AV0 + 1);
        n_in(I.c, AV0 + 2);
        let base: u32 = if k == GIR_A64_SHA1C { 0x5E000000 } else if k == GIR_A64_SHA1P { 0x5E001000 }
                        else if k == GIR_A64_SHA1M { 0x5E002000 } else if k == GIR_A64_SHA1SU0 { 0x5E003000 }
                        else if k == GIR_A64_SHA256H { 0x5E004000 } else if k == GIR_A64_SHA256H2 { 0x5E005000 }
                        else { 0x5E006000 };
        a4(base | (2 << 16) | (1 << 5));
        n_out(j, rt, 16, false);
        return;
    }
    if k == GIR_A64_SDOT || k == GIR_A64_UDOT {
        n_in(I.a, AV0);
        n_in(I.b, AV0 + 1);
        n_in(I.c, AV0 + 2);
        a4(0x0E809400 | (if R.q { 0x40000000 as u32 } else { 0 }) | (if k == GIR_A64_UDOT { 0x20000000 as u32 } else { 0 })
           | (2 << 16) | (1 << 5));
        n_out(j, rt, 4, false);
        return;
    }
    a_brk(1);
}
