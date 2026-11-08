// AArch64 instruction selection for values in registers (milestone F1):
// integer and pointer arithmetic, compares fused with their branch or
// select, casts, loads and stores with folded addresses, GEP, scalar
// floating point, FMA, bit operations, small copies and fills, the stack
// pointer operations. The memory-class operations (INT2, aggregates, vectors
// that do not fit a register, lane-by-lane vector code), fp128 arithmetic
// (library calls), atomics, TLS and inline assembly are in a64mem.goose.

// ------------------------------------------------------------ integers

// Whether value v is an INT constant; its value (zero-extended from its width).
fn a_cint(v: u32) -> bool, u64 {
    if gir_kind(v) != GIR_V_CONST { return false, 0; }
    let c = M.consts[gir_idx(v)];
    if cls_of(c.ty) != C_INT { return false, 0; }
    return true, c.lo;
}
// The constant sign-extended from `bits`.
checkfree fn a_sx(x: u64, bits: u32) -> i64 {
    if bits >= 64 { return x as! i64; }
    let s: u32 = 64 - bits;
    return ((x << s) as! i64) >> s;
}

// v in a register, sign- or zero-extended to 32 bits (bits < 32) or as is.
// Returns the register (a temp when an extension was needed).
fn a_gpr_ext(v: u32, sgn: bool, bits: u32) -> u32 {
    if bits >= 32 && bits != 32 && bits < 64 {
        // odd widths above 32: kept zero-extended; signed uses need the sign
        let r = a_gpr(v, true);
        if !sgn { return r; }
        let t = a_temp();
        a_sext(t, r, bits);
        return t;
    }
    if bits >= 32 { return a_gpr(v, false); }
    let isc, c = a_cint(v);
    if isc {
        let t = a_temp();
        let x: u64 = if sgn { a_sx(c, bits) as! u64 } else { c };
        a_mov_imm(t, x, false);
        return t;
    }
    let r = a_gpr(v, false);
    let id = vid(v);
    if !sgn && vi[id].st & ST_EXT == 0 { return r; }
    let t = a_temp();
    if sgn { a_bfm(ABF_SBFM, false, t, r, 0, bits - 1); }
    else { a_bfm(ABF_UBFM, false, t, r, 0, bits - 1); }
    return t;
}

// add/sub immediate forms: (ok, imm12, shifted, negated)
fn a_addimm(x: i64) -> bool, u32, bool, bool {
    var v = x;
    var neg = false;
    if v < 0 {
        v = -v;
        neg = true;
    }
    if v < 4096 { return true, v as! u32, false, neg; }
    if v & 0xFFF == 0 && v < (1 << 24) { return true, (v >> 12) as! u32, true, neg; }
    return false, 0, false, false;
}

fn a_lower_binop(I: Inst, j: u32) {
    let t: u32 = I.ty;
    let bits = bits_of(t);
    let w64 = bits > 32;
    let op: u32 = I.op;
    let ex = exact_width(bits);
    var ext = bits < 32;     // the result may have garbage above its width
    let isc, c = a_cint(I.b);
    if op == GIR_ADD || op == GIR_SUB {
        let a = a_gpr(I.a, false);
        var done = false;
        var rd: u32 = 0;
        if isc {
            let k: i64 = if bits >= 64 { c as! i64 } else if w64 { a_sx(c, bits) } else { a_sx(c, if bits < 32 { bits } else { 32 }) };
            let ok, imm, sh, neg = a_addimm(if op == GIR_SUB { -k } else { k });
            if ok {
                rd = a_def(j);
                a_addsub_imm(if neg { AI_SUB } else { AI_ADD }, w64, rd, a, imm, sh);
                done = true;
            }
        }
        if !done {
            let b = a_gpr_z(I.b, false);
            rd = a_def(j);
            a_addsub_rr(if op == GIR_ADD { AR_ADD } else { AR_SUB }, w64, rd, a, b, 0, 0);
        }
        if !ex { a_zext(rd, bits); ext = false; }
        a_set(j, rd, ext);
        return;
    }
    if op == GIR_AND || op == GIR_OR || op == GIR_XOR {
        let a = a_gpr(I.a, false);
        var rd: u32 = 0;
        var done = false;
        if isc {
            let enc = a_bitmask(c, w64);
            if enc != 0xFFFFFFFF {
                rd = a_def(j);
                let base: u32 = if op == GIR_AND { ALI_AND } else if op == GIR_OR { ALI_ORR } else { ALI_EOR };
                a_logic_imm(base, w64, rd, a, enc);
                done = true;
            }
        }
        if !done {
            let b = a_gpr_z(I.b, false);
            rd = a_def(j);
            let base: u32 = if op == GIR_AND { AL_AND } else if op == GIR_OR { AL_ORR } else { AL_EOR };
            a_logic_rr(base, w64, rd, a, b, 0, 0);
        }
        // and/or/xor of clean values is clean; odd widths stay clean (constants are zero-extended)
        if !ex { ext = false; }
        a_set(j, rd, ext);
        return;
    }
    if op == GIR_MUL {
        let a = a_gpr(I.a, false);
        let b = a_gpr(I.b, false);
        let rd = a_def(j);
        a_mul(w64, rd, a, b);
        if !ex { a_zext(rd, bits); ext = false; }
        a_set(j, rd, ext);
        return;
    }
    if op == GIR_SHL {
        let a = a_gpr(I.a, false);
        let rd = a_def(j);
        if isc && c < bits as u64 {
            a_lsl_imm(w64, rd, a, c as! u32);
        } else {
            let b = a_gpr(I.b, false);
            a_dp2(w64, A2_LSL, rd, a, b);
        }
        if !ex { a_zext(rd, bits); ext = false; }
        a_set(j, rd, ext);
        return;
    }
    if op == GIR_LSHR || op == GIR_ASHR {
        let sgn = op == GIR_ASHR;
        if isc && c < bits as u64 {
            let a = a_gpr(I.a, false);
            let rd = a_def(j);
            let sh: u32 = c as! u32;
            // ubfx/sbfx take the bits [sh, bits) whatever is above them
            if bits == 64 || bits == 32 {
                if sgn { a_asr_imm(w64, rd, a, sh); } else { a_lsr_imm(w64, rd, a, sh); }
            } else if sgn {
                a_sbfx(w64, rd, a, sh, bits - sh);
                if !ex { a_zext(rd, bits); }
            } else {
                a_ubfx(w64, rd, a, sh, bits - sh);
            }
            a_set(j, rd, sgn && ex && bits < 32);
            return;
        }
        let a = a_gpr_ext(I.a, sgn, bits);
        let b = a_gpr(I.b, false);
        let rd = a_def(j);
        a_dp2(w64 || (bits > 32), if sgn { A2_ASR } else { A2_LSR }, rd, a, b);
        if !ex { a_zext(rd, bits); }
        a_set(j, rd, sgn && ex && bits < 32);
        return;
    }
    // division and remainder
    let sgn = op == GIR_SDIV || op == GIR_SREM;
    let a = a_gpr_ext(I.a, sgn, bits);
    let b = a_gpr_ext(I.b, sgn, bits);
    let rd = a_def(j);
    if op == GIR_SDIV || op == GIR_UDIV {
        a_dp2(w64, if sgn { A2_SDIV } else { A2_UDIV }, rd, a, b);
    } else {
        let q = a_temp();
        a_dp2(w64, if sgn { A2_SDIV } else { A2_UDIV }, q, a, b);
        a_msub(w64, rd, q, b, a);
    }
    if !ex || sgn && bits < 32 { a_zext(rd, bits); }
    a_set(j, rd, false);
}

// The condition code of an integer predicate.
checkfree fn a_icc(p: u32) -> u32 {
    if p == GIR_EQ { return AC_EQ; }
    if p == GIR_NE { return AC_NE; }
    if p == GIR_UGT { return AC_HI; }
    if p == GIR_UGE { return AC_HS; }
    if p == GIR_ULT { return AC_LO; }
    if p == GIR_ULE { return AC_LS; }
    if p == GIR_SGT { return AC_GT; }
    if p == GIR_SGE { return AC_GE; }
    if p == GIR_SLT { return AC_LT; }
    return AC_LE;
}
checkfree fn a_signed_pred(p: u32) -> bool { p >= GIR_SGT }
// Whether instruction j's only use is the next instruction, a CONDBR or a
// scalar SELECT on it (the flags then go straight there).
fn a_fusible(j: u32) -> bool {
    if vi[j].nuse != 1 || vi[j].st & ST_GLOB != 0 || j + 1 >= f_nins { return false; }
    let N = M.insts[f_first_inst + j + 1];
    let r = (GIR_V_INST << 30) | (f_first_inst + j);
    if N.op == GIR_CONDBR && N.a == r { return true; }
    if N.op == GIR_SELECT && N.a == r && N.b != r && N.c != r {
        let c = arc(N.ty);
        return c == ARC_GPR || c == ARC_FPR;
    }
    return false;
}
// cmp of a and b (INT, `bits` wide) for predicate p: sets the flags.
fn a_cmp_vals(p: u32, bits: u32, va: u32, vb: u32) {
    let sgn = a_signed_pred(p);
    let w64 = bits > 32;
    let a = a_gpr_ext(va, sgn, bits);
    let isc, c = a_cint(vb);
    if isc {
        let k: i64 = if sgn { a_sx(c, bits) } else { c as! i64 };
        let ok, imm, sh, neg = a_addimm(k);
        if ok && (bits >= 32 || !neg) {
            a_addsub_imm(if neg { AI_ADDS } else { AI_SUBS }, w64, AZR, a, imm, sh);
            return;
        }
    }
    let b = if isc && c == 0 { AZR } else { a_gpr_ext(vb, sgn, bits) };
    a_cmp_rr(w64, a, b);
}
fn a_lower_icmp(I: Inst, j: u32) {
    let t: u32 = I.aux;
    let bits = bits_of(t);
    let p: u32 = I.sub;
    a_cmp_vals(p, bits, I.a, I.b);
    if a_fusible(j) {
        a_flags_id = j;
        a_fcc = a_icc(p);
        a_fcomb = 0;
        return;
    }
    let rd = a_def(j);
    a_cset(rd, a_icc(p));
    a_set(j, rd, false);
}

// fcmp predicate -> condition(s): (cc, cc2, comb) with comb 0 = cc, 2 = cc || cc2.
fn a_fcc_of(p: u32) -> u32, u32, u32 {
    if p == F_OEQ { return AC_EQ, 0, 0; }
    if p == F_OGT { return AC_GT, 0, 0; }
    if p == F_OGE { return AC_GE, 0, 0; }
    if p == F_OLT { return AC_MI, 0, 0; }
    if p == F_OLE { return AC_LS, 0, 0; }
    if p == F_ONE { return AC_MI, AC_GT, 2; }
    if p == F_ORD { return AC_VC, 0, 0; }
    if p == F_UNO { return AC_VS, 0, 0; }
    if p == F_UEQ { return AC_EQ, AC_VS, 2; }
    if p == F_UGT { return AC_HI, 0, 0; }
    if p == F_UGE { return AC_PL, 0, 0; }
    if p == F_ULT { return AC_LT, 0, 0; }
    if p == F_ULE { return AC_LE, 0, 0; }
    if p == F_UNE { return AC_NE, 0, 0; }
    if p == F_TRUE { return AC_AL, 0, 0; }
    return AC_AL, 0, 3;   // false: comb 3
}
fn a_lower_fcmp(I: Inst, j: u32) {
    let t: u32 = I.aux;
    let p: u32 = I.sub;
    let cc, cc2, comb = a_fcc_of(p);
    if p != F_FALSE && p != F_TRUE {
        let a = a_vr(I.a);
        let isz = gir_kind(I.b) == GIR_V_CONST && M.consts[gir_idx(I.b)].lo == 0;
        if isz { a_fcmp0(a_ft(t), a); }
        else {
            let b = a_vr(I.b);
            a_fcmp(a_ft(t), a, b);
        }
    }
    if comb != 3 && a_fusible(j) {
        a_flags_id = j;
        a_fcc = cc;
        a_fcc2 = cc2;
        a_fcomb = comb;
        return;
    }
    let rd = a_def(j);
    if comb == 3 { a_movz(false, rd, 0, 0); }
    else if cc == AC_AL { a_movz(false, rd, 1, 0); }
    else if comb == 0 { a_cset(rd, cc); }
    else {
        a_cset(rd, cc);
        a_csel_k(false, 1, rd, rd, AZR, cc2 ^ 1);   // rd = cc2 ? 1 : rd  (csinc rd, rd, zr, !cc2)
        // csinc gives zr + 1 = 1 when !(!cc2), i.e. cc2: rd = cc2 ? 1 : rd
    }
    a_set(j, rd, false);
}

// ------------------------------------------------------------ select

fn a_lower_select(I: Inst, j: u32) {
    let t: u32 = I.ty;
    let c = arc(t);
    let fused = a_flags_id != RV_NONE && I.a == inst_ref(a_flags_id);
    var cc: u32 = AC_NE;
    var comb: u32 = 0;
    var cc2: u32 = 0;
    if fused {
        cc = a_fcc;
        comb = a_fcomb;
        cc2 = a_fcc2;
        a_flags_id = RV_NONE;
    }
    if c == ARC_GPR {
        let w64 = bits_of(t) > 32;
        let b = a_gpr_z(I.b, false);
        let cv = a_gpr_z(I.c, false);
        if !fused {
            let r = a_gpr(I.a, false);
            a_logic_imm(ALI_ANDS, false, AZR, r, a_bitmask(1, false));
        }
        let rd = a_def(j);
        if comb == 2 {
            a_csel(w64, rd, b, cv, cc);
            a_csel(w64, rd, b, rd, cc2);
        } else {
            a_csel(w64, rd, b, cv, cc);
        }
        var ext = bits_of(t) < 64;
        if gir_kind(I.b) == GIR_V_INST && gir_kind(I.c) == GIR_V_INST {
            ext = vi[vid(I.b)].st & ST_EXT != 0 || vi[vid(I.c)].st & ST_EXT != 0;
        }
        if !exact_width(bits_of(t)) { ext = false; }
        a_set(j, rd, ext && bits_of(t) < 64);
        return;
    }
    if c == ARC_FPR {
        let b = a_vr(I.b);
        let cv = a_vr(I.c);
        if !fused {
            let r = a_gpr(I.a, false);
            a_logic_imm(ALI_ANDS, false, AZR, r, a_bitmask(1, false));
        }
        let rd = a_def(j);
        let ft = a_ft(t);
        if ft == 3 {
            // half: fcsel on h needs FEAT_FP16; select the 32-bit containers
            a_fcsel(0, rd, b, cv, cc);
            if comb == 2 { a_fcsel(0, rd, b, rd, cc2); }
        } else {
            a_fcsel(ft, rd, b, cv, cc);
            if comb == 2 { a_fcsel(ft, rd, b, rd, cc2); }
        }
        a_set(j, rd, false);
        return;
    }
    // vectors in a register, f128: a branch around a copy
    let cr = a_gpr(I.a, false);
    let b = a_vr(I.b);
    let cv = a_vr(I.c);
    let rd = a_def(j);
    a_vmov(true, rd, cv);
    a_tbz_raw(false, cr, 0);
    let p = here() - 4;
    a_vmov(true, rd, b);
    a_patch_branch(p, here(), AF_B14);
    a_set(j, rd, false);
}

// ------------------------------------------------------------ casts

fn a_lower_cast(I: Inst, j: u32) {
    let op: u32 = I.op;
    let dt: u32 = I.ty;
    let st: u32 = I.aux;
    let dc = arc(dt);
    let sc = arc(st);
    if dc == ARC_GPR && sc == ARC_GPR {
        let sb = bits_of(st);
        let db = bits_of(dt);
        if op == GIR_SEXT {
            let a = a_gpr(I.a, false);
            let rd = a_def(j);
            if sb >= 64 { a_mov_rr(true, rd, a); }
            else { a_bfm(ABF_SBFM, db > 32, rd, a, 0, sb - 1); }
            if !exact_width(db) { a_zext(rd, db); }
            a_set(j, rd, db < 32 && exact_width(db));
            return;
        }
        if op == GIR_ZEXT {
            let a = a_gpr(I.a, false);
            let rd = a_def(j);
            let id: u32 = if is_val(I.a) { vid(I.a) } else { RV_NONE };
            let dirty = id != RV_NONE && vi[id].st & ST_EXT != 0 || !is_val(I.a);
            if dirty && sb < 64 {
                if sb == 32 { a_mov_rr(false, rd, a); }
                else { a_bfm(ABF_UBFM, sb > 32, rd, a, 0, sb - 1); }
            } else {
                a_mov_rr(true, rd, a);
            }
            a_set(j, rd, false);
            return;
        }
        // trunc, ptrtoint, inttoptr, bitcast between integers
        let a = a_gpr(I.a, false);
        let rd = a_def(j);
        if db < sb && !exact_width(db) {
            a_mov_rr(true, rd, a);
            a_zext(rd, db);
            a_set(j, rd, false);
            return;
        }
        a_mov_rr(true, rd, a);
        var ext = db < sb && db < 64;
        if is_val(I.a) && vi[vid(I.a)].st & ST_EXT != 0 && db < 64 { ext = true; }
        a_set(j, rd, ext);
        return;
    }
    if op == GIR_BITCAST {
        if a_inv(dc) && a_inv(sc) {
            let a = a_vr(I.a);
            let rd = a_def(j);
            a_vmov(true, rd, a);
            a_set(j, rd, false);
            return;
        }
        if dc == ARC_GPR {
            // FP or 8-byte vector bits into a GPR
            let a = a_vr(I.a);
            let rd = a_def(j);
            let n = M.types[st].store;
            if n == 8 { a_fmov_to_gp(true, rd, a); }
            else if n == 4 { a_fmov_to_gp(false, rd, a); }
            else { a_umov(1, rd, a, 0); }
            a_set(j, rd, false);
            return;
        }
        // GPR bits into an FP / vector register
        let a = a_gpr(I.a, false);
        let rd = a_def(j);
        let n = M.types[dt].store;
        a_fmov_from_gp(n == 8, rd, a);
        a_set(j, rd, false);
        return;
    }
    if op == GIR_FPEXT || op == GIR_FPTRUNC {
        let a = a_vr(I.a);
        let rd = a_def(j);
        let to: u32 = if dt == GIR_T_F64 { AF1_CVT_D } else if dt == GIR_T_F32 { AF1_CVT_S } else { AF1_CVT_H };
        a_fp1(a_ft(st), to, rd, a);
        a_set(j, rd, false);
        return;
    }
    if op == GIR_FPTOSI || op == GIR_FPTOUI {
        let a = a_vr(I.a);
        let rd = a_def(j);
        let db = bits_of(dt);
        let w64 = db > 32;
        if op == GIR_FPTOSI || db > 32 || db == 32 {
            a_fcvt_gp(w64, a_ft(st), if op == GIR_FPTOSI { AFC_FCVTZS } else { AFC_FCVTZU }, rd, a);
        } else {
            // a narrow unsigned result: the signed conversion covers its range (and LLVM's)
            a_fcvt_gp(false, a_ft(st), AFC_FCVTZS, rd, a);
        }
        if !exact_width(db) { a_zext(rd, db); }
        a_set(j, rd, db < 32 && exact_width(db));
        return;
    }
    // sitofp / uitofp
    let sb = bits_of(st);
    let sgn = op == GIR_SITOFP;
    let a = a_gpr_ext(I.a, sgn, sb);
    let rd = a_def(j);
    var w64 = sb > 32;
    if sb == 32 && !sgn {
        // a 32-bit unsigned value in w: ucvtf from w
        w64 = false;
    }
    if sb < 32 { w64 = false; }
    if sb > 32 && sb < 64 && sgn {
        // (a_gpr_ext sign-extended it to 64 bits)
        w64 = true;
    }
    a_fcvt_gp(w64, a_ft(dt), if sgn { AFC_SCVTF } else { AFC_UCVTF }, rd, a);
    a_set(j, rd, false);
}

// ------------------------------------------------------------ floating point

fn a_lower_fbin(I: Inst, j: u32) {
    let t: u32 = I.ty;
    let a = a_vr(I.a);
    let b = a_vr(I.b);
    let rd = a_def(j);
    let op: u32 = I.op;
    let k: u32 = if op == GIR_FADD { AF2_FADD } else if op == GIR_FSUB { AF2_FSUB } else if op == GIR_FMUL { AF2_FMUL } else { AF2_FDIV };
    a_fp2(a_ft(t), k, rd, a, b);
    a_set(j, rd, false);
}
fn a_lower_fma(I: Inst, j: u32) {
    let t: u32 = I.ty;
    let a = a_vr(I.a);
    let b = a_vr(I.b);
    let c = a_vr(I.c);
    let rd = a_def(j);
    if arc(t) == ARC_VR {
        // fmla vd, vn, vm accumulates into vd: rd = c, then fmla rd, a, b
        let q = M.types[t].store == 16;
        let sz: u32 = if M.types[t].elems == GIR_T_F64 { 1 } else { 0 };
        if rd != c { a_vmov(true, rd, c); }
        if rd == a || rd == b {
            a_vmov(true, AV31, c);
            a_v3(q, 0, sz, 0x19, AV31, a, b);
            a_vmov(true, rd, AV31);
        } else {
            a_v3(q, 0, sz, 0x19, rd, a, b);
        }
        a_set(j, rd, false);
        return;
    }
    a_fma3(a_ft(t), 0, rd, a, b, c);
    a_set(j, rd, false);
}
fn a_lower_funary(I: Inst, j: u32) {
    let t: u32 = I.ty;
    let op: u32 = I.op;
    let ft = a_ft(t);
    if op == GIR_COPYSIGN {
        // rd = a with b's sign: bit-insert under the sign mask (-0.0 = fneg of +0.0)
        let a = a_vr(I.a);
        let b = a_vr(I.b);
        let rd = a_def(j);
        let sz: u32 = if t == GIR_T_F64 { 1 } else { 0 };
        a_vzero(true, AV31);
        a_v2(true, 1, 2 | sz, 0x0F, AV31, AV31);     // fneg v31.(4s|2d)
        if rd != a { a_vmov(true, rd, a); }
        a_v3(false, 1, 2, 0x03, rd, b, AV31);       // bit rd.8b, b.8b, v31.8b
        a_set(j, rd, false);
        return;
    }
    let a = a_vr(I.a);
    let rd = a_def(j);
    let k: u32 = if op == GIR_FNEG { AF1_FNEG } else if op == GIR_FABS { AF1_FABS } else { AF1_FSQRT };
    a_fp1(ft, k, rd, a);
    a_set(j, rd, false);
}

// ------------------------------------------------------------ memory

// An address operand: base register + offset, or base + index register
// (extended by opt: 3 lsl/uxtx, 6 sxtw, 2 uxtw, shifted by the access size if sh).
struct AMem { base: u32, idx: u32, off: i64, opt: u32, sh: u32 }
let ANOIDX = 64;

// The address in v (a pointer value), as an AMem.
fn a_addr(v: u32) -> AMem {
    if is_val(v) {
        let id = vid(v);
        if vi[id].home == H_ALLOCA && vi[id].reg >= 64 {
            a_note(id);
            return AMem { base: AFP, idx: ANOIDX, off: vi[id].off as i64, opt: 0, sh: 0 };
        }
        if a_paddr_id != RV_NONE && id == a_paddr_id {
            a_paddr_id = RV_NONE;
            return a_paddr_m;
        }
    }
    let r = a_gpr(v, false);
    return AMem { base: r, idx: ANOIDX, off: 0, opt: 0, sh: 0 };
}
var a_paddr_m: AMem = AMem { base: 0, idx: 64, off: 0, opt: 0, sh: 0 };

// A load or store of 2^s bytes (kind k) at m.
fn a_ls_m(k: u32, s: u32, rt: u32, m: AMem) {
    if m.idx == ANOIDX {
        a_ls(k, s, rt, m.base, m.off);
        return;
    }
    if m.off == 0 && (m.sh == 0 || m.sh == s) {
        a_ls_reg(k, s, rt, m.base, m.idx, m.opt, m.sh != 0);
        return;
    }
    // base + index into x16, then the offset
    a_addsub_ext(AR_ADD, true, AX16, m.base, m.idx, m.opt, m.sh);
    a_ls(k, s, rt, AX16, m.off);
}

fn a_lower_load(I: Inst, j: u32) {
    let t: u32 = I.ty;
    let c = arc(t);
    let ord = (I.flags & IF_ORD_MASK) >> IF_ORD_SHIFT;
    let n = a_vbytes(t);
    if ord >= 4 && ord != 5 {
        // acquire / seq_cst: ldar (no offset)
        let m = a_addr(I.a);
        var ar = m.base;
        if m.idx != ANOIDX || m.off != 0 {
            ar = AX16;
            if m.idx != ANOIDX { a_addsub_ext(AR_ADD, true, AX16, m.base, m.idx, m.opt, m.sh); a_add_off(AX16, AX16, m.off); }
            else { a_add_off(AX16, m.base, m.off); }
        }
        let rd = a_def(j);
        if c == ARC_GPR {
            a_ldar(a_log2(n), rd, ar);
        } else {
            a_ldar(a_log2(n), AX17, ar);
            a_fmov_from_gp(n == 8, rd, AX17);
        }
        a_set(j, rd, false);
        return;
    }
    let m = a_addr(I.a);
    let rd = a_def(j);
    if c == ARC_GPR {
        a_ls_m(LS_LDR, a_log2(n), rd, m);
        a_set(j, rd, false);
        return;
    }
    a_ls_m(LS_FLDR, a_log2(n), rd, m);
    a_set(j, rd, false);
}
fn a_lower_store(I: Inst) {
    let t: u32 = I.aux;
    let c = arc(t);
    let n = a_vbytes(t);
    let ord = (I.flags & IF_ORD_MASK) >> IF_ORD_SHIFT;
    if c == ARC_GPR {
        let r = a_gpr_z(I.a, false);
        let m = a_addr(I.b);
        if ord >= 5 {
            var ar = m.base;
            if m.idx != ANOIDX || m.off != 0 {
                ar = AX16;
                if m.idx != ANOIDX { a_addsub_ext(AR_ADD, true, AX16, m.base, m.idx, m.opt, m.sh); a_add_off(AX16, AX16, m.off); }
                else { a_add_off(AX16, m.base, m.off); }
            }
            a_stlr(a_log2(n), r, ar);
            return;
        }
        a_ls_m(LS_STR, a_log2(n), r, m);
        return;
    }
    let r = a_vr(I.a);
    let m = a_addr(I.b);
    if ord >= 5 {
        var ar = m.base;
        if m.idx != ANOIDX || m.off != 0 {
            ar = AX16;
            if m.idx != ANOIDX { a_addsub_ext(AR_ADD, true, AX16, m.base, m.idx, m.opt, m.sh); a_add_off(AX16, AX16, m.off); }
            else { a_add_off(AX16, m.base, m.off); }
        }
        if n == 8 { a_fmov_to_gp(true, AX17, r); } else { a_fmov_to_gp(false, AX17, r); }
        a_stlr(a_log2(n), AX17, ar);
        return;
    }
    a_ls_m(LS_FSTR, a_log2(n), r, m);
}

// Whether GEP j can be folded into the next instruction (a load or store of a
// register-class value through it, its only use).
fn a_gep_foldable(I: Inst, j: u32) -> bool {
    if vi[j].nuse != 1 || vi[j].st & ST_GLOB != 0 || j + 1 >= f_nins { return false; }
    let N = M.insts[f_first_inst + j + 1];
    let r = (GIR_V_INST << 30) | (f_first_inst + j);
    if N.flags & IF_ORD_MASK != 0 { return false; }
    if N.op == GIR_LOAD && N.a == r { return arc(N.ty) != ARC_MEM && exact_width_t(N.ty); }
    if N.op == GIR_STORE && N.b == r && N.a != r { return arc(N.aux) != ARC_MEM && exact_width_t(N.aux); }
    return false;
}
fn exact_width_t(t: u32) -> bool { arc(t) != ARC_GPR || exact_width(bits_of(t)) }

// GEP: base + offset + sum(sext(index) * scale).
fn a_lower_gep(I: Inst, j: u32) {
    let off: i64 = (M.opnds[I.b] as u64 | (M.opnds[I.b + 1] as u64 << 32)) as! i64;
    let n = I.c;
    let fold = a_gep_foldable(I, j);
    // the access size of the user (for a scaled index)
    var us: u32 = 0;
    if fold {
        let N = M.insts[f_first_inst + j + 1];
        let ut: u32 = if N.op == GIR_LOAD { N.ty } else { N.aux };
        us = a_log2(a_vbytes(ut));
    }
    // base
    var base: u32 = 64;
    var boff: i64 = off;
    if is_val(I.a) && vi[vid(I.a)].home == H_ALLOCA && vi[vid(I.a)].reg >= 64 {
        base = AFP;
        boff = off + vi[vid(I.a)].off as i64;
        a_note(vid(I.a));
    } else {
        base = a_gpr(I.a, false);
    }
    if fold && n == 0 {
        a_carry = true;
        a_paddr_id = j;
        a_paddr_m = AMem { base: base, idx: ANOIDX, off: boff, opt: 0, sh: 0 };
        vi[j].reg = PADDR;
        return;
    }
    if fold && n == 1 {
        let iv = M.opnds[I.b + 2];
        let sc = M.opnds[I.b + 3];
        let ib = bits_of(type_of(iv));
        if (sc == 1 || sc == (1 as u32) << us) && (ib == 32 || ib == 64) && gir_kind(iv) != GIR_V_CONST {
            let x = a_gpr(iv, false);
            if boff != 0 {
                let t = a_temp();
                a_add_off(t, base, boff);
                base = t;
            }
            a_carry = true;
            a_paddr_id = j;
            a_paddr_m = AMem { base: base, idx: x, off: 0, opt: if ib == 32 { 6 } else { 3 }, sh: if sc == 1 { 0 } else { us } };
            vi[j].reg = PADDR;
            return;
        }
    }
    let rd = a_def(j);
    var cur = base;
    var pend_off: i64 = boff;
    for k in 0..n {
        let iv = M.opnds[I.b + 2 + 2 * k];
        let sc: u32 = M.opnds[I.b + 3 + 2 * k];
        let ib = bits_of(type_of(iv));
        let isc, cv = a_cint(iv);
        if isc {
            pend_off += a_sx(cv, ib) * sc as i64;
            continue;
        }
        let x = a_gpr(iv, false);
        var sh: u32 = 64;
        if sc != 0 && sc & (sc - 1) == 0 { sh = ctz(sc as u64) as! u32; }
        if sh <= 4 && ib <= 32 && (ib == 8 || ib == 16 || ib == 32) {
            let opt: u32 = if ib == 8 { 4 } else if ib == 16 { 5 } else { 6 };
            a_addsub_ext(AR_ADD, true, rd, cur, x, opt, sh);
        } else if sh < 64 && ib == 64 {
            if cur == ASP { a_addsub_ext(AR_ADD, true, rd, cur, x, 3, sh); }
            else { a_addsub_rr(AR_ADD, true, rd, cur, x, 0, sh); }
        } else {
            // any width, any scale: x16 = sext(x); then madd
            a_sext(AX16, x, ib);
            if sh < 64 {
                a_addsub_rr(AR_ADD, true, rd, cur, AX16, 0, sh);
            } else {
                a_mov_imm(AX17, sc as u64, true);
                if cur == AFP || cur == ASP {
                    a_mov_sp(rd, cur);
                    a_madd(true, rd, AX16, AX17, rd);
                } else {
                    a_madd(true, rd, AX16, AX17, cur);
                }
            }
        }
        cur = rd;
    }
    if cur != rd {
        a_add_off(rd, cur, pend_off);
    } else if pend_off != 0 {
        a_add_off(rd, rd, pend_off);
    }
    a_set(j, rd, false);
}

// memcpy / memset of a constant size (<= 4096 bytes) inline.
fn a_lower_memcpy(I: Inst) {
    let n: u32 = I.c;
    let d = a_gpr(I.a, false);
    if I.op == GIR_MEMCPY {
        let s = a_gpr(I.b, false);
        a_copy(d, 0, s, 0, n);
        return;
    }
    // memset: the byte replicated in x17, stored 8 bytes at a time
    let isc, c = a_cint(I.b);
    if isc {
        let b: u64 = c & 0xFF;
        a_mov_imm(AX17, b * 0x0101010101010101, true);
    } else {
        let r = a_gpr(I.b, false);
        a_bfm(ABF_UBFM, false, AX17, r, 0, 7);
        a_mov_imm(AX16, 0x0101010101010101, true);
        a_mul(true, AX17, AX17, AX16);
    }
    var p: u32 = 0;
    while p < n {
        let rest = n - p;
        let cc: u32 = if rest >= 8 { 8 } else if rest >= 4 { 4 } else if rest >= 2 { 2 } else { 1 };
        if !a_ls_ok(a_log2(cc), p as i64) {
            a_add_off(AX16, d, p as i64);
            a_ls(LS_STR, a_log2(cc), AX17, AX16, 0);
        } else {
            a_ls(LS_STR, a_log2(cc), AX17, d, p as i64);
        }
        p += cc;
    }
}

// ------------------------------------------------------------ bit operations

fn a_lower_bitop(I: Inst, j: u32) {
    let t: u32 = I.ty;
    let bits = bits_of(t);
    let w64 = bits > 32;
    let op: u32 = I.op;
    let wb: u32 = if w64 { 64 } else { 32 };
    let a = a_gpr(I.a, true);
    let rd = a_def(j);
    if op == GIR_CTLZ {
        a_dp1(w64, 4, rd, a);
        if bits != wb { a_addsub_imm(AI_SUB, false, rd, rd, wb - bits, false); }
    } else if op == GIR_CTTZ {
        // rbit, clz; a zero input gives the width: set a bit just above the value first
        if bits != wb {
            a_logic_imm(ALI_ORR, w64, AX16, a, a_bitmask((1 as u64) << bits, w64));
            a_dp1(w64, 0, rd, AX16);
        } else {
            a_dp1(w64, 0, rd, a);
        }
        a_dp1(w64, 4, rd, rd);
    } else if op == GIR_CTPOP {
        a_fmov_from_gp(true, AV31, a);
        a_v2(false, 0, 0, 0x05, AV31, AV31);       // cnt v31.8b, v31.8b
        a_vacross(false, 0, 0, 0x1B, AV31, AV31);  // addv b31, v31.8b
        a_fmov_to_gp(false, rd, AV31);
    } else if op == GIR_BSWAP {
        if bits == 16 {
            a_dp1(false, 1, rd, a);   // rev16
        } else if bits == 32 {
            a_dp1(false, 2, rd, a);
        } else if bits == 64 {
            a_dp1(true, 3, rd, a);
        } else {
            // (other byte counts: rev of the containing width, shifted down)
            a_dp1(true, 3, rd, a);
            a_lsr_imm(true, rd, rd, 64 - bits);
        }
    } else {
        // bitreverse
        a_dp1(w64, 0, rd, a);
        if bits != wb { a_lsr_imm(w64, rd, rd, wb - bits); }
    }
    a_set(j, rd, false);
}
// fshl(a, b, c) = (a << c) | (b >> (w - c)), c mod w; fshr(a, b, c) = (a << (w - c)) | (b >> c)
fn a_lower_funnel(I: Inst, j: u32) {
    let t: u32 = I.ty;
    let bits = bits_of(t);
    let w64 = bits > 32;
    let isc, c = a_cint(I.c);
    if (bits == 32 || bits == 64) && isc {
        let a = a_gpr(I.a, false);
        let b = a_gpr(I.b, false);
        let rd = a_def(j);
        var sh: u32 = (c % bits as u64) as! u32;
        if sh == 0 {
            a_mov_rr(w64, rd, if I.op == GIR_FSHL { a } else { b });
        } else {
            // extr rd, a, b, #lsb: (a:b) >> lsb
            let lsb: u32 = if I.op == GIR_FSHL { bits - sh } else { sh };
            a_extr(w64, rd, a, b, lsb);
        }
        a_set(j, rd, false);
        return;
    }
    // general case on clean 64-bit registers: x16 = c mod bits
    let a = a_gpr(I.a, true);
    let b = a_gpr(I.b, true);
    let cr = a_gpr(I.c, true);
    let rd = a_def(j);
    let t2 = a_temp();
    if bits & (bits - 1) == 0 {
        a_logic_imm(ALI_AND, true, AX16, cr, a_bitmask((bits - 1) as u64, true));
    } else {
        a_mov_imm(AX17, bits as u64, true);
        a_dp2(true, A2_UDIV, AX16, cr, AX17);
        a_msub(true, AX16, AX16, AX17, cr);       // x16 = c % bits
    }
    let first: u32 = if I.op == GIR_FSHL { a } else { b };
    let second: u32 = if I.op == GIR_FSHL { b } else { a };
    // t2 = first shifted by s (left for fshl, right for fshr)
    a_dp2(true, if I.op == GIR_FSHL { A2_LSL } else { A2_LSR }, t2, first, AX16);
    // x17 = second shifted the other way by bits - s, nothing when s = 0
    a_mov_imm(AX17, bits as u64, true);
    a_addsub_rr(AR_SUB, true, AX17, AX17, AX16, 0, 0);
    a_dp2(true, if I.op == GIR_FSHL { A2_LSR } else { A2_LSL }, AX17, second, AX17);
    a_addsub_imm(AI_SUBS, true, AZR, AX16, 0, false);
    a_csel(true, AX17, AZR, AX17, AC_EQ);
    a_logic_rr(AL_ORR, true, rd, t2, AX17, 0, 0);
    if bits < 64 { a_zext(rd, bits); }
    a_set(j, rd, false);
}
// scmp/ucmp: -1, 0, 1
fn a_lower_scmp(I: Inst, j: u32) {
    let t: u32 = I.aux;
    let bits = bits_of(t);
    let p: u32 = if I.op == GIR_SCMP { GIR_SLT } else { GIR_ULT };
    a_cmp_vals(p, bits, I.a, I.b);
    let rd = a_def(j);
    let w64 = bits_of(I.ty) > 32;
    let lt: u32 = if I.op == GIR_SCMP { AC_LT } else { AC_LO };
    a_cset(rd, AC_NE);                      // 1 if different
    a_csel_k(w64, 2, rd, rd, AZR, lt ^ 1);  // csinv rd, rd, zr, !lt: lt -> ~0 = -1
    if !exact_width(bits_of(I.ty)) { a_zext(rd, bits_of(I.ty)); }
    a_set(j, rd, bits_of(I.ty) < 64 && exact_width(bits_of(I.ty)));
}

// ------------------------------------------------------------ stack

fn a_lower_dynalloca(I: Inst, j: u32) {
    let n = a_gpr(I.a, false);
    var al: u64 = I.b;
    if al < 16 { al = 16; }
    // sp = (sp - n) & ~(al - 1), rounding n up to 16
    a_addsub_imm(AI_ADD, true, AX16, n, 15, false);
    a_logic_imm(ALI_AND, true, AX16, AX16, a_bitmask(~(15 as u64), true));
    a_mov_sp(AX17, ASP);
    a_addsub_rr(AR_SUB, true, AX17, AX17, AX16, 0, 0);
    if al > 16 { a_logic_imm(ALI_AND, true, AX17, AX17, a_bitmask(~(al - 1), true)); }
    a_mov_sp(ASP, AX17);
    let rd = a_def(j);
    a_mov_sp(rd, ASP);
    a_set(j, rd, false);
}
fn a_lower_frameaddr(I: Inst, j: u32) {
    let rd = a_def(j);
    if I.op == GIR_FRAMEADDR {
        a_mov_rr(true, rd, AFP);
        for k in 0..I.a { a_ls(LS_LDR, 3, rd, rd, 0); }
    } else {
        if I.a == 0 {
            a_ls(LS_LDR, 3, rd, AFP, 8);
        } else {
            a_mov_rr(true, rd, AFP);
            for k in 0..I.a { a_ls(LS_LDR, 3, rd, rd, 0); }
            a_ls(LS_LDR, 3, rd, rd, 8);
        }
    }
    a_set(j, rd, false);
}
fn a_lower_fence(I: Inst) {
    if I.flags & IF_SINGLETHREAD != 0 { return; }
    let ord = (I.flags & IF_ORD_MASK) >> IF_ORD_SHIFT;
    if ord == 4 { a_dmb(9); } else { a_dmb(11); }   // acquire: ishld; else ish
}
