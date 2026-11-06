// Allocator-aware instruction lowering (milestone A2): integer and pointer
// arithmetic, compares (fused with the branch or select that uses them),
// selects, casts, loads and stores (with deferred loads folded into the
// user and GEPs folded into the address), floating point, memcpy/memset.
// Operands come from ra_gpr / ra_xmm / ra_mem_opnd, results go to ra_set.
//
// Integer operations use the operand size of the type: 32-bit instructions
// for i32 (whose results are zero-extended for free), 64-bit ones for i64
// and pointers; i8/i16 results computed with 32-bit instructions carry
// garbage above their width (ST_EXT) until a user needs them clean.

inline fn inst_ref(j: u32) -> u32 { f_first_inst + j }
fn is_const(v: u32) -> bool { gir_kind(v) == GIR_V_CONST }

// The constant v as a sign-extended imm32 usable with an operation on
// `bits`-wide values (only the low `bits` bits of the result matter, except
// for compares, see cmp_imm).
fn alu_imm(v: u32, bits: u32) -> bool, i32 {
    if !is_const(v) { return false, 0; }
    let c = M.consts[gir_idx(v)];
    if cls_of(c.ty) != C_INT { return false, 0; }
    if bits <= 32 { return true, (c.lo as! u32) as! i32; }
    if bits == 64 && fits32(c.lo as! i64) { return true, c.lo as! i32; }
    return false, 0;
}
// The constant v as an imm32 for a compare with a `bits`-wide value that is
// zero-extended (sgn = false) or sign-extended (sgn = true) to 64 bits.
fn cmp_imm(v: u32, bits: u32, sgn: bool) -> bool, i32 {
    if !is_const(v) { return false, 0; }
    let c = M.consts[gir_idx(v)];
    if cls_of(c.ty) != C_INT { return false, 0; }
    var x: i64 = c.lo as! i64;
    if sgn && bits < 64 { x = (x << (64 - bits)) >> (64 - bits); }
    if fits32(x) { return true, x as! i32; }
    return false, 0;
}
// Whether operand v of the current instruction carries garbage above its width.
fn v_ext(v: u32) -> bool {
    if !is_val(v) { return false; }
    let id = vid(v);
    return v_reg[id] < 32 && v_st[id] & ST_EXT != 0;
}
// The result register for j, taking over the register of operand a if a dies
// here (else a copy of ra): the two-address form "rd = ra; rd op= ...".
fn def_from(j: u32, a: u32, ra: u32) -> u32 {
    let r = ra_reuse(a);
    if r == ra { return r; }
    let rd = ra_def(j);
    mov_rr64(rd, ra);
    return rd;
}

// ------------------------------------------------------ integer binops

fn lower_binop_a(I: Inst, j: u32) {
    let bits = bits_of(I.ty);
    let op: u32 = I.op;
    let w = wq(bits);
    let exact = exact_width(bits);
    if op == GIR_SDIV || op == GIR_UDIV || op == GIR_SREM || op == GIR_UREM {
        lower_divrem_a(I, j, bits);
        return;
    }
    if op == GIR_SHL || op == GIR_LSHR || op == GIR_ASHR {
        lower_shift_a(I, j, bits);
        return;
    }
    let ok, imm = alu_imm(I.b, bits);
    if ok && op != GIR_MUL {
        let ra = ra_gpr(I.a, !exact);
        var rd: u32 = 32;
        if op == GIR_ADD || op == GIR_SUB {
            rd = ra_reuse(I.a);
            let k: i64 = if op == GIR_ADD { imm } else { 0 - (imm as i64) };
            if rd != ra && fits32(k) {
                rd = ra_def(j);
                if w != 0 { lea64(rd, m_reg(ra, k as! i32)); } else { lea32(rd, m_reg(ra, k as! i32)); }
                lower_int_done(j, rd, bits, true);
                return;
            }
            if rd != ra { rd = def_from(j, I.a, ra); }
        } else {
            rd = def_from(j, I.a, ra);
        }
        let ext: u32 = match op { GIR_ADD => G1_ADD, GIR_SUB => G1_SUB, GIR_AND => G1_AND, GIR_OR => G1_OR, _ => G1_XOR };
        grp1_ri(w, ext, rd, imm);
        lower_int_done(j, rd, bits, op == GIR_ADD || op == GIR_SUB || op != GIR_AND && v_ext(I.a));
        return;
    }
    if ok && op == GIR_MUL {
        let ra = ra_gpr(I.a, !exact);
        var rd = ra_reuse(I.a);
        if rd != ra { rd = ra_def(j); }
        imul_rri(w, rd, ra, imm);
        lower_int_done(j, rd, bits, true);
        return;
    }
    // register (or memory) second operand
    var a = I.a;
    var b = I.b;
    let comm = op == GIR_ADD || op == GIR_MUL || op == GIR_AND || op == GIR_OR || op == GIR_XOR;
    if comm && ra_reuse(a) == 32 && ra_reuse(b) != 32 {
        a = I.b;
        b = I.a;
    }
    let ra = ra_gpr(a, !exact);
    let n = int_bytes(bits);
    var okm = false;
    var mb = Mem { M_REG, 0, 0, 0, 0 };
    if exact && n >= 4 {
        let o, m2 = ra_mem_opnd(b, n);
        okm = o;
        mb = m2;
    }
    var rb: u32 = 32;
    if !okm { rb = ra_gpr(b, !exact); }
    let rd = def_from(j, a, ra);
    let aop: u32 = match op { GIR_ADD => ALU_ADD, GIR_SUB => ALU_SUB, GIR_AND => ALU_AND, GIR_OR => ALU_OR,
                              GIR_XOR => ALU_XOR, _ => 0 };
    if op == GIR_MUL {
        if okm { imul_rm(w, rd, mb); } else { imul_rr(w, rd, rb); }
    } else if okm {
        alu_rm(w, aop, rd, mb);
    } else {
        alu_rr(w, aop, rd, rb);
    }
    let ext = op == GIR_ADD || op == GIR_SUB || op == GIR_MUL || v_ext(a) || v_ext(b);
    lower_int_done(j, rd, bits, ext);
}
// The INT result of j is in rd; `dirty`: the operation may have set bits
// above the width (only possible below 32 bits, or for odd widths).
fn lower_int_done(j: u32, rd: u32, bits: u32, dirty: bool) {
    if bits == 32 || bits == 64 {
        ra_set(j, rd, false);
    } else if exact_width(bits) {
        ra_set(j, rd, dirty);
    } else {
        if dirty { zext_reg(rd, bits); }
        ra_set(j, rd, false);
    }
}

fn lower_shift_a(I: Inst, j: u32, bits: u32) {
    let op: u32 = I.op;
    let w = wq(bits);
    let sh: u32 = if op == GIR_SHL { SH_SHL } else if op == GIR_LSHR { SH_SHR } else { SH_SAR };
    // right shifts need the bits above the width: zero (lshr) or the sign (ashr)
    let need_clean = op == GIR_LSHR && bits != 32 && bits != 64;
    if is_const(I.b) {
        let n = (M.consts[gir_idx(I.b)].lo & 63) as! u32;
        let ra = ra_gpr(I.a, need_clean);
        var rd: u32 = 32;
        if op == GIR_ASHR && bits != 32 && bits != 64 {
            rd = ra_reuse(I.a);
            if rd != ra { rd = ra_def(j); }
            sign_ext_into(rd, ra, bits);
            shift_imm(1, sh, rd, n);
            lower_int_done(j, rd, bits, true);
            return;
        }
        if op == GIR_SHL && n == 1 && ra_reuse(I.a) != ra {
            // shl by 1 without a copy: lea rd, [ra + ra]
            rd = ra_def(j);
            op_mem(0, w, 0x8D, rd, m_sib(ra, ra, 0, 0), false);
            lower_int_done(j, rd, bits, true);
            return;
        }
        rd = def_from(j, I.a, ra);
        if n != 0 { shift_imm(if bits == 32 { 0 } else { 1 }, sh, rd, n); }
        lower_int_done(j, rd, bits, op == GIR_SHL);
        return;
    }
    // count in cl
    ra_gpr_into(I.b, RCX, false);
    let ra = ra_gpr(I.a, need_clean);
    var rd = ra_reuse(I.a);
    if rd != ra { rd = ra_def(j); }
    if op == GIR_ASHR && bits != 32 && bits != 64 { sign_ext_into(rd, ra, bits); }
    else if rd != ra { mov_rr64(rd, ra); }
    shift_cl(if bits == 32 { 0 } else { 1 }, sh, rd);
    lower_int_done(j, rd, bits, op != GIR_LSHR);
}
// rd = sign extension of the `bits`-wide value in rs to 64 bits.
fn sign_ext_into(rd: u32, rs: u32, bits: u32) {
    if bits == 8 { movsx8(1, rd, rs); }
    else if bits == 16 { movsx16(1, rd, rs); }
    else if bits == 32 { movsxd(rd, rs); }
    else if bits >= 64 { if rd != rs { mov_rr64(rd, rs); } }
    else {
        if rd != rs { mov_rr64(rd, rs); }
        sext_reg(rd, bits);
    }
}

// Division: dividend in rax (edx:eax), quotient in rax, remainder in rdx.
fn lower_divrem_a(I: Inst, j: u32, bits: u32) {
    let op: u32 = I.op;
    let sgn = op == GIR_SDIV || op == GIR_SREM;
    let rem = op == GIR_SREM || op == GIR_UREM;
    // unsigned division by a power of two: a shift or a mask
    if !sgn && is_const(I.b) {
        let c = M.consts[gir_idx(I.b)].lo;
        if c != 0 && c & (c - 1) == 0 && (bits == 32 || bits == 64) {
            var sh: u32 = 0;
            while ((1 as u64) << sh) < c { sh++; }
            let ra = ra_gpr(I.a, false);
            let rd = def_from(j, I.a, ra);
            let w = wq(bits);
            if rem {
                if c - 1 <= 0x7FFFFFFF { grp1_ri(w, G1_AND, rd, (c - 1) as! i32); }
                else {
                    let t = ra_temp();
                    mov_ri(t, c - 1);
                    alu_rr(w, ALU_AND, rd, t);
                }
            } else if sh != 0 {
                shift_imm(w, SH_SHR, rd, sh);
            }
            ra_set(j, rd, false);
            return;
        }
    }
    let w: u32 = if bits > 32 { 1 } else { 0 };
    let small = bits < 32;
    ra_gpr_into(I.a, RAX, !sgn);
    ra_clobber(RDX);
    // the divisor: a register other than rax/rdx, or memory
    let n = int_bytes(bits);
    var okm = false;
    var mb = Mem { M_REG, 0, 0, 0, 0 };
    if !small && exact_width(bits) {
        let o, m2 = ra_mem_opnd(I.b, n);
        okm = o;
        mb = m2;
    }
    var rb: u32 = 32;
    if !okm {
        rb = ra_gpr(I.b, !sgn);
        if rb == RAX || rb == RDX {
            let t = ra_temp();
            mov_rr64(t, rb);
            rb = t;
        }
    }
    if sgn && bits != 32 && bits != 64 {
        // extend both operands to the operation width
        sign_ext_into(RAX, RAX, bits);
        let t = ra_temp();
        sign_ext_into(t, rb, bits);
        rb = t;
    }
    let ow: u32 = if bits == 32 || small { 0 } else { 1 };
    if sgn {
        if ow != 0 { cqo(); } else { cdq(); }
    } else {
        zero_r(RDX);
    }
    if okm { div_m(ow, if sgn { 7 } else { 6 }, mb); } else { div_r(ow, if sgn { 7 } else { 6 }, rb); }
    let rr: u32 = if rem { RDX } else { RAX };
    if bits == 32 || bits == 64 { ra_set(j, rr, false); }
    else {
        zext_reg(rr, bits);
        ra_set(j, rr, false);
    }
}

// ------------------------------------------------------------ compares

checkfree fn icmp_cc(p: u32) -> u32 {
    match p {
        GIR_EQ => CC_E,
        GIR_NE => CC_NE,
        GIR_UGT => CC_A,
        GIR_UGE => CC_AE,
        GIR_ULT => CC_B,
        GIR_ULE => CC_BE,
        GIR_SGT => CC_G,
        GIR_SGE => CC_GE,
        GIR_SLT => CC_L,
        _ => CC_LE,
    }
}
checkfree fn swap_pred(p: u32) -> u32 {
    match p {
        GIR_UGT => GIR_ULT,
        GIR_UGE => GIR_ULE,
        GIR_ULT => GIR_UGT,
        GIR_ULE => GIR_UGE,
        GIR_SGT => GIR_SLT,
        GIR_SGE => GIR_SLE,
        GIR_SLT => GIR_SGT,
        GIR_SLE => GIR_SGE,
        _ => p,
    }
}
// cmp of two registers at a width of n bytes (1, 2, 4, 8)
fn cmp_rr_n(n: u32, a: u32, b: u32) {
    if n == 1 { alu_rr8(ALU_CMP, a, b); }
    else if n == 2 { alu_rr16(ALU_CMP, a, b); }
    else { alu_rr(if n == 8 { 1 } else { 0 }, ALU_CMP, a, b); }
}
fn cmp_ri_n(n: u32, a: u32, imm: i32) {
    if imm == 0 {
        if n == 1 { test_rr8(a, a); }
        else if n == 2 { test_rr16(a, a); }
        else { test_rr(if n == 8 { 1 } else { 0 }, a, a); }
        return;
    }
    if n == 1 { cmp8_ri(a, (imm as! u32) & 0xFF); }
    else if n == 2 { cmp16_ri(a, (imm as! u32) & 0xFFFF); }
    else { grp1_ri(if n == 8 { 1 } else { 0 }, G1_CMP, a, imm); }
}
// cmp r, [m] (n bytes)
fn cmp_rm_n(n: u32, a: u32, m: Mem) {
    if n == 1 { op_mem(0, 0, 0x3A, a, m, true); }
    else if n == 2 { op_mem(P_66, 0, 0x3B, a, m, false); }
    else { alu_rm(if n == 8 { 1 } else { 0 }, ALU_CMP, a, m); }
}
// cmp [m], r (n bytes)
fn cmp_mr_n(n: u32, m: Mem, b: u32) {
    if n == 1 { alu_mr8(ALU_CMP, m, b); }
    else if n == 2 { alu_mr16(ALU_CMP, m, b); }
    else { alu_mr(if n == 8 { 1 } else { 0 }, ALU_CMP, m, b); }
}

// Emits the compare of a and b (bits wide) for predicate pred; returns the
// condition code that is true when the predicate holds.
fn emit_icmp(pred: u32, bits: u32, a0: u32, b0: u32) -> u32 {
    var p = pred;
    var a = a0;
    var b = b0;
    if is_const(a) && !is_const(b) {
        a = b0;
        b = a0;
        p = swap_pred(pred);
    }
    let sgn = p >= GIR_SGT;
    if !exact_width(bits) {
        // odd widths are zero-extended: unsigned compares at 32/64 bits; signed
        // ones on sign-extended copies
        let n: u32 = if bits <= 32 { 4 } else { 8 };
        if !sgn {
            let ok, imm = cmp_imm(b, bits, false);
            let ra = ra_gpr(a, true);
            if ok { cmp_ri_n(n, ra, imm); } else { cmp_rr_n(n, ra, ra_gpr(b, true)); }
            return icmp_cc(p);
        }
        let ra = ra_gpr(a, true);
        let ta = ra_temp();
        sign_ext_into(ta, ra, bits);
        let ok, imm = cmp_imm(b, bits, true);
        if ok { cmp_ri_n(8, ta, imm); }
        else {
            let rb = ra_gpr(b, true);
            let tb = ra_temp();
            sign_ext_into(tb, rb, bits);
            cmp_rr_n(8, ta, tb);
        }
        return icmp_cc(p);
    }
    let n = bits / 8;
    let ok, imm = cmp_imm(b, bits, sgn);
    var okb = ok;
    var immb = imm;
    if !ok && is_const(b) && n <= 4 {
        // any constant fits a compare of 32 bits or less
        okb = true;
        immb = (M.consts[gir_idx(b)].lo as! u32) as! i32;
    }
    if okb {
        let okm, ma = ra_mem_opnd(a, n);
        if okm {
            grp1_mi(n, G1_CMP, ma, immb);
            return icmp_cc(p);
        }
        let ra = ra_gpr(a, false);
        cmp_ri_n(n, ra, immb);
        return icmp_cc(p);
    }
    let okma, ma = ra_mem_opnd(a, n);
    if okma {
        let rb = ra_gpr(b, false);
        cmp_mr_n(n, ma, rb);
        return icmp_cc(p);
    }
    let ra = ra_gpr(a, false);
    let okmb, mb = ra_mem_opnd(b, n);
    if okmb { cmp_rm_n(n, ra, mb); }
    else { cmp_rr_n(n, ra, ra_gpr(b, false)); }
    return icmp_cc(p);
}

// Whether the compare j only feeds the next instruction's condition (a
// CONDBR, or a SELECT on registers), so the flags can be used directly.
fn fuse_flags(j: u32) -> bool {
    if v_nuse[j] != 1 || v_st[j] & ST_GLOB != 0 || v_last[j] != j + 1 { return false; }
    let N = M.insts[f_first_inst + j + 1];
    let r = inst_ref(j);
    if N.op == GIR_CONDBR { return N.a == r; }
    if N.op == GIR_SELECT { return N.a == r && N.b != r && N.c != r && inst_kind(N) == K_A; }
    return false;
}
// Materializes a condition code as the 0/1 result of j.
fn set_cc_result(j: u32, cc: u32) {
    let rd = ra_def(j);
    setcc(cc, rd);
    movzx8(rd, rd);
    ra_set(j, rd, false);
}

fn lower_icmp_a(I: Inst, j: u32) {
    let cc = emit_icmp(I.sub, bits_of(I.aux), I.a, I.b);
    if fuse_flags(j) {
        flags_id = j;
        flags_cc = cc;
        flags_comb = 0;
        return;
    }
    set_cc_result(j, cc);
}

// How an FCMP predicate is computed from ucomis(x, y) flags: compare (a, b)
// or swapped (b, a), then cc1 [combined with cc2 by and/or]. Packed as
// swap | cc1 << 8 | cc2 << 16 | comb << 24 (comb: 1 = and, 2 = or).
fn fcmp_plan_packed(p: u32) -> u32 {
    match p {
        F_OEQ => CC_E << 8 | CC_NP << 16 | 1 << 24,
        F_UNE => CC_NE << 8 | CC_P << 16 | 2 << 24,
        F_OGT => CC_A << 8,
        F_OGE => CC_AE << 8,
        F_OLT => 1 | CC_A << 8,
        F_OLE => 1 | CC_AE << 8,
        F_ONE => CC_NE << 8,
        F_ORD => CC_NP << 8,
        F_UNO => CC_P << 8,
        F_UEQ => CC_E << 8,
        F_UGT => 1 | CC_B << 8,
        F_UGE => 1 | CC_BE << 8,
        F_ULT => CC_B << 8,
        _ => CC_BE << 8,
    }
}
fn fcmp_plan(p: u32) -> bool, u32, u32, u32 {
    let x = fcmp_plan_packed(p);
    return x & 1 != 0, (x >> 8) & 0xFF, (x >> 16) & 0xFF, x >> 24;
}
// ucomis of FP values a, b (b may be read from memory).
fn emit_ucomis(dbl: bool, a: u32, b: u32) {
    let xa = ra_xmm(a);
    let okm, mb = ra_mem_opnd(b, 0);
    if okm { ucomis_m(dbl, xa, mb); return; }
    if is_const(b) {
        ucomis_m(dbl, xa, const_mem(gir_idx(b)));
        return;
    }
    ucomis(dbl, xa, ra_xmm(b));
}
fn lower_fcmp_a(I: Inst, j: u32) {
    let t: u32 = I.aux;
    let dbl = t == GIR_T_F64;
    let p: u32 = I.sub;
    if p == F_FALSE || p == F_TRUE {
        let rd = ra_def(j);
        mov_ri(rd, if p == F_TRUE { 1 } else { 0 });
        ra_set(j, rd, false);
        return;
    }
    let swap, cc1, cc2, comb = fcmp_plan(p);
    if swap { emit_ucomis(dbl, I.b, I.a); } else { emit_ucomis(dbl, I.a, I.b); }
    if fuse_flags(j) && (comb == 0 || M.insts[f_first_inst + j + 1].op == GIR_CONDBR) {
        flags_id = j;
        flags_cc = cc1;
        flags_cc2 = cc2;
        flags_comb = comb;
        return;
    }
    let rd = ra_def(j);
    setcc(cc1, rd);
    if comb != 0 {
        let t2 = ra_temp();
        setcc(cc2, t2);
        alu_rr8(if comb == 1 { ALU_AND } else { ALU_OR }, rd, t2);
    }
    movzx8(rd, rd);
    ra_set(j, rd, false);
}

// ------------------------------------------------------------- select

fn lower_select_a(I: Inst, j: u32) {
    var cc: u32 = CC_NE;
    let fused = flags_id != RV_NONE && I.a == inst_ref(flags_id);
    if fused { cc = flags_cc; }
    else {
        let rc = ra_gpr(I.a, true);
        test_rr32(rc, rc);
    }
    flags_id = RV_NONE;
    if rc_of(I.ty) == RC_GPR {
        let ext = v_ext(I.b) || v_ext(I.c);
        let rb = ra_gpr(I.b, false);
        let rcv = ra_gpr(I.c, false);
        let rd = def_from(j, I.c, rcv);
        cmov64(cc, rd, rb);
        ra_set(j, rd, ext);
        return;
    }
    // xmm: rd = b; if !cc: rd = c
    let xb = ra_xmm(I.b);
    let xc = ra_xmm(I.c);
    let xd = ra_xdef(j);
    movaps_rr(xd, xb);
    let p = jcc_fwd8(cc);
    movaps_rr(xd, xc);
    patch_here8(p);
    ra_xset(j, xd);
}

// -------------------------------------------------------------- casts

fn lower_cast_a(I: Inst, j: u32) {
    let op: u32 = I.op;
    let dt = I.ty;
    let st: u32 = I.aux;
    let dc = rc_of(dt);
    let sc = rc_of(st);
    if dc == RC_GPR && sc == RC_GPR {
        lower_icast_a(I, j, op, bits_of(st), bits_of(dt));
        return;
    }
    if dc == RC_XMM && sc == RC_XMM {
        // fpext / fptrunc
        let okm, m = ra_mem_opnd(I.a, 0);
        let xd = if okm { ra_xdef(j) } else { 0 };
        if okm {
            if op == GIR_FPEXT { cvtss2sd_m(xd, m); } else { cvtsd2ss_m(xd, m); }
            ra_xset(j, xd);
            return;
        }
        let xs = ra_xmm(I.a);
        var x = ra_xreuse(I.a);
        if x == 32 { x = ra_xdef(j); }
        if op == GIR_FPEXT { cvtss2sd(x, xs); } else if op == GIR_FPTRUNC { cvtsd2ss(x, xs); } else if x != xs { movaps_rr(x, xs); }
        ra_xset(j, x);
        return;
    }
    let dbl = if dc == RC_XMM { dt == GIR_T_F64 } else { st == GIR_T_F64 };
    if dc == RC_XMM {
        // INT -> FP: bitcast, sitofp, uitofp
        let sb = bits_of(st);
        if op == GIR_BITCAST {
            let okm, m = ra_mem_opnd(I.a, int_bytes(sb));
            let xd = ra_xdef(j);
            if okm {
                if dbl { movsd_load(xd, m); } else { movss_load(xd, m); }
            } else {
                let rs = ra_gpr(I.a, false);
                if dbl { movq_xr(xd, rs); } else { movd_xr(xd, rs); }
            }
            ra_xset(j, xd);
            return;
        }
        let sgn = op == GIR_SITOFP;
        if sb == 32 && sgn || sb == 64 && sgn {
            let okm, m = ra_mem_opnd(I.a, sb / 8);
            let xd = ra_xdef(j);
            if okm { cvtsi2s_m(dbl, wq(sb), xd, m); }
            else { cvtsi2s(dbl, wq(sb), xd, ra_gpr(I.a, false)); }
            ra_xset(j, xd);
            return;
        }
        if sb < 64 {
            // extend into a 64-bit temp, then a 64-bit conversion (exact for < 64 bits)
            let rs = ra_gpr(I.a, !sgn);
            let t = ra_temp();
            if sgn { sign_ext_into(t, rs, sb); } else { mov_rr64(t, rs); }
            let xd = ra_xdef(j);
            cvtsi2s(dbl, 1, xd, t);
            ra_xset(j, xd);
            return;
        }
        // unsigned 64-bit
        let rs = ra_gpr(I.a, false);
        let t = ra_temp();
        let t2 = ra_temp();
        let xd = ra_xdef(j);
        test_rr64(rs, rs);
        let neg = jcc_fwd8(CC_S);
        cvtsi2s(dbl, 1, xd, rs);
        let done = jmp_fwd8();
        patch_here8(neg);
        mov_rr64(t, rs);
        shift_imm64(SH_SHR, t, 1);
        mov_rr32(t2, rs);
        and_ri32(t2, 1);
        alu_rr64(ALU_OR, t, t2);
        cvtsi2s(dbl, 1, xd, t);
        sse_arith(0x58, dbl, xd, xd);
        patch_here8(done);
        ra_xset(j, xd);
        return;
    }
    // FP -> INT: bitcast, fptosi, fptoui
    let db = bits_of(dt);
    if op == GIR_BITCAST {
        let okm, m = ra_mem_opnd(I.a, 0);
        let rd = ra_def(j);
        if okm { load_int(rd, m, db); }
        else {
            let xs = ra_xmm(I.a);
            if dbl { movq_rx(rd, xs); } else { movd_rx(rd, xs); }
        }
        ra_set(j, rd, false);
        return;
    }
    let sgn = op == GIR_FPTOSI;
    if sgn || db < 64 {
        // signed (any width), or unsigned narrower than 64 bits (a 64-bit signed conversion)
        let w: u32 = if sgn && db <= 32 { 0 } else { 1 };
        let okm, m = ra_mem_opnd(I.a, 0);
        let rd = ra_def(j);
        if okm { cvtts2si_m(dbl, w, rd, m); } else { cvtts2si(dbl, w, rd, ra_xmm(I.a)); }
        lower_int_done(j, rd, db, !(sgn && db == 32));
        return;
    }
    // unsigned 64-bit: values >= 2^63 are converted after subtracting 2^63
    let xs = ra_xmm(I.a);
    let xt = ra_xtemp();
    let xc = ra_xtemp();
    let rd = ra_def(j);
    let t = ra_temp();
    if dbl {
        mov_ri(t, 0x43E0000000000000);
        movq_xr(xc, t);
    } else {
        mov_ri(t, 0x5F000000);
        movd_xr(xc, t);
    }
    ucomis(dbl, xs, xc);
    let big = jcc_fwd8(CC_AE);
    cvtts2si(dbl, 1, rd, xs);
    let done = jmp_fwd8();
    patch_here8(big);
    movaps_rr(xt, xs);
    sse_arith(0x5C, dbl, xt, xc);
    cvtts2si(dbl, 1, rd, xt);
    bt_ri64(7, rd, 63);
    patch_here8(done);
    ra_set(j, rd, false);
}

// Integer casts (zext, sext, trunc, ptrtoint, inttoptr, bitcast) from sb to db bits.
fn lower_icast_a(I: Inst, j: u32, op: u32, sb: u32, db: u32) {
    if op == GIR_SEXT {
        var okm = false;
        var m = Mem { M_REG, 0, 0, 0, 0 };
        if exact_width(sb) && sb < 64 {
            let o, m2 = ra_mem_opnd(I.a, sb / 8);
            okm = o;
            m = m2;
        }
        let w: u32 = if db > 32 { 1 } else { 0 };
        if okm {
            let rd = ra_def(j);
            if sb == 8 { load8s(w, rd, m); } else if sb == 16 { load16s(w, rd, m); } else { load32s(rd, m); }
            lower_int_done(j, rd, db, true);
            return;
        }
        let rs = ra_gpr(I.a, !exact_width(sb));
        var rd = ra_reuse(I.a);
        if rd != rs { rd = ra_def(j); }
        if sb == 8 { movsx8(w, rd, rs); }
        else if sb == 16 { movsx16(w, rd, rs); }
        else if sb == 32 { movsxd(rd, rs); }
        else { sign_ext_into(rd, rs, sb); }
        lower_int_done(j, rd, db, true);
        return;
    }
    if op == GIR_ZEXT || op == GIR_INTTOPTR || op == GIR_PTRTOINT || op == GIR_TRUNC || op == GIR_BITCAST {
        let widen = db > sb;
        // a deferred load: load just the bytes the result needs
        let lb: u32 = if widen { sb } else { db };
        if exact_width(lb) {
            let okm, m = ra_mem_opnd(I.a, if widen { int_bytes(sb) } else { int_bytes(sb) });
            if okm {
                let rd = ra_def(j);
                load_int(rd, m, lb);
                lower_int_done(j, rd, db, false);
                return;
            }
        }
        let ext = v_ext(I.a);
        let rs = ra_gpr(I.a, false);
        var rd = ra_reuse(I.a);
        if widen && ext {
            // zero-extend the garbage away
            if rd != rs { rd = ra_def(j); }
            if sb == 8 { movzx8(rd, rs); }
            else if sb == 16 { movzx16(rd, rs); }
            else { mov_rr32(rd, rs); }
            ra_set(j, rd, false);
            return;
        }
        if rd != rs {
            rd = ra_def(j);
            mov_rr64(rd, rs);
        }
        if widen { ra_set(j, rd, false); }
        else { lower_int_done(j, rd, db, ext || db < sb); }
        return;
    }
    assert(false);
}

// --------------------------------------------------------- loads and stores

// Whether pointer v can be addressed without registers (frame or rip-relative).
fn addr_is_static(v: u32) -> bool {
    let k = gir_kind(v);
    if k == GIR_V_GLOBAL { return is_local_ref(gir_idx(v)); }
    if k > GIR_V_ARG { return false; }
    let id = vid(v);
    let h = v_home[id];
    if h == H_ALLOCA || h == H_BYVAL { return true; }
    return v_reg[id] == PADDR && m_regs(paddr_m) == 0;
}
// Memory operand for pointer value v.
fn ra_addr(v: u32) -> Mem {
    let k = gir_kind(v);
    let i = gir_idx(v);
    if k <= GIR_V_ARG {
        let id = vid(v);
        let r = v_reg[id];
        if r == PADDR {
            v_reg[id] = NOREG;
            return paddr_m;
        }
        let h = v_home[id];
        if h == H_ALLOCA || h == H_BYVAL { return m_rbp(v_off[id]); }
    }
    if k == GIR_V_GLOBAL && is_local_ref(i) { return m_sym(g_sym[i], R_X86_64_PC32, 0); }
    return m_reg(ra_gpr(v, false), 0);
}

fn lower_load_a(I: Inst, j: u32) {
    let t: u32 = I.ty;
    if I.flags & (IF_VOLATILE | IF_ORD_MASK) == 0 && v_nuse[j] == 1
       && v_st[j] & (ST_GLOB | ST_NODEF) == 0 && v_last[j] > j && addr_is_static(I.a) {
        ra_pend_add(j, ra_addr(I.a));
        return;
    }
    let m = ra_addr(I.a);
    if rc_of(t) == RC_XMM {
        let xd = ra_xdef(j);
        if t == GIR_T_F32 { movss_load(xd, m); } else { movsd_load(xd, m); }
        ra_xset(j, xd);
        return;
    }
    // the pointer's register may hold the result
    var rd: u32 = 32;
    if m.kind == M_REG && m.reg != RBP {
        let r: u32 = m.reg;
        if ra_reuse(I.a) == r { rd = r; }
    }
    if rd == 32 { rd = ra_def(j); }
    load_int(rd, m, bits_of(t));
    if t == GIR_T_I1 { and_ri32(rd, 1); }
    ra_set(j, rd, false);
}

// Stores the INT constant c (n bytes) at m; false if it needs a register.
fn store_const(m: Mem, c: u64, n: u32) -> bool {
    if n == 1 { store_imm8(m, (c & 0xFF) as! u32); return true; }
    if n == 2 { store_imm16(m, (c & 0xFFFF) as! u32); return true; }
    if n == 4 { store_imm32(m, c as! u32); return true; }
    if fits32(c as! i64) { store_imm64(m, c as! i32); return true; }
    return false;
}

fn lower_store_a(I: Inst) {
    let t: u32 = I.aux;
    let v = I.a;
    let seq = (I.flags & IF_ORD_MASK) >> IF_ORD_SHIFT == ORD_SEQ_CST;
    let m = ra_addr(I.b);
    let c = rc_of(t);
    if c == RC_GPR {
        let n = int_bytes(bits_of(t));
        if seq {
            let r = ra_temp();
            let rs = ra_gpr(v, false);
            mov_rr64(r, rs);
            atomic_rm(false, n, 0x86, 0x87, r, m);
            return;
        }
        if is_const(v) && cls_of(M.consts[gir_idx(v)].ty) == C_INT {
            if store_const(m, M.consts[gir_idx(v)].lo, n) { return; }
        }
        store_int(m, ra_gpr(v, false), bits_of(t));
        return;
    }
    // f32 / f64
    if seq {
        let r = ra_temp();
        let x = ra_xmm(v);
        if t == GIR_T_F32 { movd_rx(r, x); } else { movq_rx(r, x); }
        atomic_rm(false, store_of(t), 0x86, 0x87, r, m);
        return;
    }
    if is_const(v) {
        let k = M.consts[gir_idx(v)];
        if store_const(m, k.lo, store_of(t)) { return; }
    }
    let x = ra_xmm(v);
    if t == GIR_T_F32 { movss_store(m, x); } else { movsd_store(m, x); }
}

// ------------------------------------------------------------------ GEP

// The address computed by GEP I as a memory operand (registers locked).
fn gep_mem(I: Inst) -> Mem {
    var off = (M.opnds[I.b] | M.opnds[I.b + 1] as u64 << 32) as! i64;
    // the variable terms; constant indices fold into the offset
    var nv: u32 = 0;
    var last: u32 = GIR_NONE;
    for k in 0..I.c {
        let idx = M.opnds[I.b + 2 + 2 * k];
        let sc = M.opnds[I.b + 3 + 2 * k];
        if sc == 0 { continue; }
        if is_const(idx) {
            let ct = M.consts[gir_idx(idx)].ty;
            var x: i64 = M.consts[gir_idx(idx)].lo as! i64;
            let b = bits_of(ct);
            if b < 64 { x = (x << (64 - b)) >> (64 - b); }
            off = off + x * sc;
            continue;
        }
        nv++;
        last = k;
    }
    // base: frame address, rip address (no index), or a register
    let a = I.a;
    var base: u32 = 32;
    var disp: i64 = 0;
    let ka = gir_kind(a);
    if ka <= GIR_V_ARG && (v_home[vid(a)] == H_ALLOCA || v_home[vid(a)] == H_BYVAL) {
        base = RBP;
        disp = v_off[vid(a)];
    } else if ka == GIR_V_GLOBAL && is_local_ref(gir_idx(a)) && nv == 0 && fits32(off) {
        return m_sym(g_sym[gir_idx(a)], R_X86_64_PC32, off as! i32);
    } else {
        base = ra_gpr(a, false);
    }
    if nv == 0 {
        if fits32(disp + off) { return m_reg(base, (disp + off) as! i32); }
        let t = ra_temp();
        if base == RBP { lea64(t, m_rbp(disp as! i32)); } else { mov_rr64(t, base); }
        let t2 = ra_temp();
        mov_ri(t2, off as! u64);
        alu_rr64(ALU_ADD, t, t2);
        return m_reg(t, 0);
    }
    // all variable terms but the last are added to a copy of the base
    var b = base;
    if nv > 1 || !fits32(disp + off) {
        let t = ra_temp();
        if b == RBP { lea64(t, m_rbp(disp as! i32)); } else { mov_rr64(t, b); }
        disp = 0;
        b = t;
        if !fits32(off) {
            let t2 = ra_temp();
            mov_ri(t2, off as! u64);
            alu_rr64(ALU_ADD, b, t2);
            off = 0;
        }
        for k in 0..I.c {
            let idx = M.opnds[I.b + 2 + 2 * k];
            let sc = M.opnds[I.b + 3 + 2 * k];
            if sc == 0 || is_const(idx) || k == last { continue; }
            let x = gep_index(idx, sc, true);
            alu_rr64(ALU_ADD, b, x);
        }
    }
    let idx = M.opnds[I.b + 2 + 2 * last];
    let sc = M.opnds[I.b + 3 + 2 * last];
    var sh: u32 = 4;
    if sc == 1 { sh = 0; } else if sc == 2 { sh = 1; } else if sc == 4 { sh = 2; } else if sc == 8 { sh = 3; }
    if sh == 4 {
        let x = gep_index(idx, sc, false);
        return m_sib(b, x, 0, (disp + off) as! i32);
    }
    let x = gep_index(idx, 1, false);
    return m_sib(b, x, sh, (disp + off) as! i32);
}
// A register holding sext64(idx) * sc (a scratch copy if it had to change;
// `own`: always a scratch register).
fn gep_index(idx: u32, sc: u32, own: bool) -> u32 {
    let bits = bits_of(type_of(idx));
    let r = ra_gpr(idx, false);
    var x = r;
    if bits < 64 || sc != 1 || own {
        x = ra_temp();
        sign_ext_into(x, r, bits);
    }
    if sc != 1 {
        if sc & (sc - 1) == 0 {
            var sh: u32 = 0;
            while ((1 as u32) << sh) < sc { sh++; }
            shift_imm64(SH_SHL, x, sh);
        } else if sc <= 0x7FFFFFFF {
            imul_rri(1, x, x, sc as! i32);
        } else {
            let t = ra_temp();
            mov_ri(t, sc);
            imul_rr64(x, t);
        }
    }
    return x;
}

fn lower_gep_a(I: Inst, j: u32) {
    let m = gep_mem(I);
    // folded into the next load or store when that is its only use
    if v_nuse[j] == 1 && v_st[j] & ST_GLOB == 0 && v_last[j] == j + 1 {
        let N = M.insts[f_first_inst + j + 1];
        let r = inst_ref(j);
        if (N.op == GIR_LOAD && N.a == r || N.op == GIR_STORE && N.b == r && N.a != r) && inst_kind(N) == K_A {
            v_reg[j] = PADDR;
            paddr_m = m;
            ra_carry = true;
            return;
        }
    }
    if m.kind == M_REG && m.disp == 0 {
        // a plain copy of the base
        let rb: u32 = m.reg;
        if rb != RBP {
            let rd = def_from(j, I.a, rb);
            ra_set(j, rd, false);
            return;
        }
    }
    var rd: u32 = 32;
    if m.kind != M_RIP {
        let rb: u32 = m.reg;
        if ra_reuse(I.a) == rb { rd = rb; }
    }
    if rd == 32 { rd = ra_def(j); }
    lea64(rd, m);
    ra_set(j, rd, false);
}

// ------------------------------------------------------- floating point

checkfree fn sse_op(op: u32) -> u32 {
    match op {
        GIR_FADD => 0x58,
        GIR_FMUL => 0x59,
        GIR_FSUB => 0x5C,
        _ => 0x5E,
    }
}
fn lower_fbin_a(I: Inst, j: u32) {
    let dbl = I.ty == GIR_T_F64;
    let op: u32 = I.op;
    var a = I.a;
    var b = I.b;
    if (op == GIR_FADD || op == GIR_FMUL) && ra_xreuse(a) == 32 && ra_xreuse(b) != 32 {
        a = I.b;
        b = I.a;
    }
    let xa = ra_xmm(a);
    let okm, mb = ra_mem_opnd(b, 0);
    var xb: u32 = 32;
    var cm = false;
    if !okm {
        if is_const(b) { cm = true; } else { xb = ra_xmm(b); }
    }
    var xd = ra_xreuse(a);
    if xd != xa {
        xd = ra_xdef(j);
        movaps_rr(xd, xa);
    }
    if okm { sse_arith_m(sse_op(op), dbl, xd, mb); }
    else if cm { sse_arith_m(sse_op(op), dbl, xd, const_mem(gir_idx(b))); }
    else { sse_arith(sse_op(op), dbl, xd, xb); }
    ra_xset(j, xd);
}
// fneg, fabs, fsqrt on f32 / f64.
fn lower_funary_a(I: Inst, j: u32) {
    let dbl = I.ty == GIR_T_F64;
    let op: u32 = I.op;
    if op == GIR_FSQRT {
        let okm, m = ra_mem_opnd(I.a, 0);
        let xd = if okm { ra_xdef(j) } else { 32 };
        if okm {
            sse_arith_m(0x51, dbl, xd, m);
            ra_xset(j, xd);
            return;
        }
        let xs = ra_xmm(I.a);
        var x = ra_xreuse(I.a);
        if x == 32 { x = ra_xdef(j); }
        sse_arith(0x51, dbl, x, xs);
        ra_xset(j, x);
        return;
    }
    let xs = ra_xmm(I.a);
    var x = ra_xreuse(I.a);
    if x != xs {
        x = ra_xdef(j);
        movaps_rr(x, xs);
    }
    var k: u32 = 0;
    if op != GIR_FNEG { k = 2; }
    if dbl { k += 1; }
    sse_packed_m(if op == GIR_FNEG { 0x57 } else { 0x54 }, false, x, mask_mem(k));
    ra_xset(j, x);
}

// ---------------------------------------------------------- memcpy, memset

fn lower_memcpy_a(I: Inst) {
    let n = I.c;
    if I.op == GIR_MEMSET {
        if n > 64 {
            ra_gpr_into(I.a, RDI, false);
            ra_gpr_into(I.b, RAX, false);
            ra_clobber(RCX);
            mov_ri(RCX, n);
            rep_stosb();
            return;
        }
        let m = ra_addr(I.a);
        let t = ra_temp();
        if is_const(I.b) {
            let c = M.consts[gir_idx(I.b)].lo & 0xFF;
            if c == 0 { zero_r(t); } else { mov_ri(t, c * 0x0101010101010101); }
        } else {
            let rv = ra_gpr(I.b, false);
            movzx8(t, rv);
            let t2 = ra_temp();
            mov_ri(t2, 0x0101010101010101);
            imul_rr64(t, t2);
        }
        var k: u32 = 0;
        while k + 8 <= n {
            store64(m_add(m, k), t);
            k += 8;
        }
        while k < n {
            let r = n - k;
            let w: u32 = if r >= 4 { 4 } else if r >= 2 { 2 } else { 1 };
            store_n(m_add(m, k), t, w);
            k += w;
        }
        return;
    }
    if n > 64 {
        ra_gpr_into(I.a, RDI, false);
        ra_gpr_into(I.b, RSI, false);
        ra_clobber(RCX);
        mov_ri(RCX, n);
        rep_movsb();
        return;
    }
    let dst = ra_addr(I.a);
    let src = ra_addr(I.b);
    var k: u32 = 0;
    if n >= 16 {
        let x = ra_xtemp();
        while k + 16 <= n {
            movups_load(x, m_add(src, k));
            movups_store(m_add(dst, k), x);
            k += 16;
        }
    }
    if k < n {
        let t = ra_temp();
        copy_mem_t(m_add(dst, k), m_add(src, k), n - k, 8, t);
    }
}
