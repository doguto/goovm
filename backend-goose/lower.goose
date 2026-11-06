// Instruction lowering: one GIR instruction at a time, through the
// value-location interface of loc.goose. Scalar integer work uses RAX (first
// operand and result), RCX (second operand / shift count) and RDX; FP work
// XMM0/XMM1; x87 work the x87 stack (empty between instructions); vectors are
// processed lane by lane in memory.

fn local_of(v: u32) -> u32 { gir_idx(v) - f_first_inst }
// ------------------------------------------------------ integer core ops

// RAX = RAX op RCX for `bits`-wide zero-extended values; result normalized.
fn int_binop(op: u32, bits: u32) {
    match op {
        GIR_ADD => { alu_rr64(ALU_ADD, RAX, RCX); zext_reg(RAX, bits); },
        GIR_SUB => { alu_rr64(ALU_SUB, RAX, RCX); zext_reg(RAX, bits); },
        GIR_MUL => { imul_rr64(RAX, RCX); zext_reg(RAX, bits); },
        GIR_AND => alu_rr64(ALU_AND, RAX, RCX),
        GIR_OR => alu_rr64(ALU_OR, RAX, RCX),
        GIR_XOR => alu_rr64(ALU_XOR, RAX, RCX),
        GIR_SHL => { shift_cl64(SH_SHL, RAX); zext_reg(RAX, bits); },
        GIR_LSHR => shift_cl64(SH_SHR, RAX),
        GIR_ASHR => {
            sext_reg(RAX, bits);
            shift_cl64(SH_SAR, RAX);
            zext_reg(RAX, bits);
        },
        GIR_SDIV, GIR_SREM => {
            sext_reg(RAX, bits);
            sext_reg(RCX, bits);
            b1(0x48);  // cqo
            b1(0x99);
            div64(7, RCX);
            if op == GIR_SREM { mov_rr64(RAX, RDX); }
            zext_reg(RAX, bits);
        },
        _ => {  // UDIV, UREM
            op_rr(0, ALU_XOR, RDX, RDX, false);  // xor edx, edx
            div64(6, RCX);
            if op == GIR_UREM { mov_rr64(RAX, RDX); }
        },
    }
}
// Loads a, b of a `bits`-wide integer compare (RAX, and RCX or an
// immediate), compares, and leaves 0/1 in EAX.
fn int_cmp_vals(pred: u32, bits: u32, a: u32, b: u32) {
    let sgn = pred >= GIR_SGT && bits < 64;
    use_fixed(a, RAX);
    if sgn { sext_reg(RAX, bits); }
    let ok, imm = cmp_imm(b, bits, pred >= GIR_SGT);
    if ok {
        grp1_ri64(G1_CMP, RAX, imm);
    } else {
        use_fixed(b, RCX);
        if sgn { sext_reg(RCX, bits); }
        alu_rr64(ALU_CMP, RAX, RCX);
    }
    setcc(icmp_cc(pred), RAX);
    movzx8(RAX, RAX);
}
// Same with both operands already in RAX and RCX (zero-extended).
fn int_cmp_rr(pred: u32, bits: u32) {
    if pred >= GIR_SGT && bits < 64 {
        sext_reg(RAX, bits);
        sext_reg(RCX, bits);
    }
    alu_rr64(ALU_CMP, RAX, RCX);
    setcc(icmp_cc(pred), RAX);
    movzx8(RAX, RAX);
}

// ---------------------------------------------------- floating-point core

fn fcmp_result(cc1: u32, cc2: u32, comb: u32) {
    setcc(cc1, RAX);
    if comb != 0 {
        setcc(cc2, RCX);
        alu_rr8(if comb == 1 { ALU_AND } else { ALU_OR }, RAX, RCX);
    }
    movzx8(RAX, RAX);
}
// a in XMM0, b in XMM1 -> 0/1 in EAX.
fn fcmp_xmm(p: u32, dbl: bool) {
    if p == F_FALSE || p == F_TRUE {
        mov_ri(RAX, if p == F_TRUE { 1 } else { 0 });
        return;
    }
    let swap, cc1, cc2, comb = fcmp_plan(p);
    if swap { ucomis(dbl, XMM1, XMM0); } else { ucomis(dbl, XMM0, XMM1); }
    fcmp_result(cc1, cc2, comb);
}
// f80 operands in memory -> 0/1 in EAX.
fn fcmp_x87(p: u32, a: Mem, b: Mem) {
    if p == F_FALSE || p == F_TRUE {
        mov_ri(RAX, if p == F_TRUE { 1 } else { 0 });
        return;
    }
    let swap, cc1, cc2, comb = fcmp_plan(p);
    if swap {
        fld_m(10, a);
        fld_m(10, b);
    } else {
        fld_m(10, b);
        fld_m(10, a);
    }
    fucomip();
    fstp_st0();
    fcmp_result(cc1, cc2, comb);
}
fn x87_op(op: u32) -> u32 {
    match op {
        GIR_FADD => X87_FADDP,
        GIR_FMUL => X87_FMULP,
        GIR_FSUB => X87_FSUBP,
        _ => X87_FDIVP,
    }
}

// Sets the x87 rounding mode to truncation around a fistp; the saved
// control word lives in the scratch area (scratch+0, +2).
fn x87_trunc_on() {
    fnstcw(m_rbp(scr()));
    load16z(RAX, m_rbp(scr()));
    grp1_ri32(G1_OR, RAX, 0x0C00);
    store16(m_rbp(scr() + 2), RAX);
    fldcw(m_rbp(scr() + 2));
}
fn x87_trunc_off() { fldcw(m_rbp(scr())); }

// st0 (f80) -> RAX as a signed (sgn) or unsigned 64-bit integer; pops st0.
fn x87_to_int(sgn: bool) {
    x87_trunc_on();
    let tmp = m_rbp(scr() + 8);
    if sgn {
        fistp_m(8, tmp);
        load64(RAX, tmp);
    } else {
        // st0 = a. Compare with 2^63; subtract it first if a >= 2^63.
        store_imm32(m_rbp(scr() + 16), 0x5F000000);  // 2^63 as f32
        fld_m(4, m_rbp(scr() + 16));                 // st0 = 2^63, st1 = a
        fxch();                                            // st0 = a, st1 = 2^63
        x87_2(0xDB, 0xE9);                                 // fucomi st0, st1
        let small = jcc_fwd(CC_B);
        x87_2(0xD8, 0xE1);                                 // fsub st0, st1
        fistp_m(8, tmp);
        load64(RAX, tmp);
        bt_ri64(7, RAX, 63);                               // btc rax, 63
        let done = jmp_fwd();
        patch_here(small);
        fistp_m(8, tmp);
        load64(RAX, tmp);
        patch_here(done);
        fstp_st0();                                        // pop 2^63
    }
    x87_trunc_off();
}
// XMM0 (f32/f64) -> RAX, truncated; unsigned 64-bit needs the 2^63 split.
fn fp_to_int(dbl: bool, sgn: bool, bits: u32) {
    if sgn || bits < 64 {
        cvtts2si(dbl, 1, RAX, XMM0);
        zext_reg(RAX, bits);
        return;
    }
    if dbl {
        mov_ri(RCX, 0x43E0000000000000);
        movq_xr(XMM1, RCX);
    } else {
        mov_ri(RCX, 0x5F000000);
        movd_xr(XMM1, RCX);
    }
    ucomis(dbl, XMM0, XMM1);
    let big = jcc_fwd(CC_AE);
    cvtts2si(dbl, 1, RAX, XMM0);
    let done = jmp_fwd();
    patch_here(big);
    sse_arith(0x5C, dbl, XMM0, XMM1);
    cvtts2si(dbl, 1, RAX, XMM0);
    bt_ri64(7, RAX, 63);
    patch_here(done);
}
// RAX (zero-extended `bits` integer) -> XMM0 (f32/f64).
fn int_to_fp(dbl: bool, sgn: bool, bits: u32) {
    if sgn { sext_reg(RAX, bits); }
    if sgn || bits < 64 {
        cvtsi2s(dbl, 1, XMM0, RAX);
        return;
    }
    test_rr64(RAX, RAX);
    let neg = jcc_fwd(CC_S);
    cvtsi2s(dbl, 1, XMM0, RAX);
    let done = jmp_fwd();
    patch_here(neg);
    mov_rr64(RCX, RAX);
    shift_imm64(SH_SHR, RCX, 1);
    and_ri32(RAX, 1);
    alu_rr64(ALU_OR, RCX, RAX);
    cvtsi2s(dbl, 1, XMM0, RCX);
    sse_arith(0x58, dbl, XMM0, XMM0);
    patch_here(done);
}
// RAX (zero-extended `bits` integer) -> st0 (f80).
fn int_to_x87(sgn: bool, bits: u32) {
    if sgn { sext_reg(RAX, bits); }
    let tmp = m_rbp(scr() + 8);
    store64(tmp, RAX);
    fild_m(8, tmp);
    if !sgn && bits == 64 {
        test_rr64(RAX, RAX);
        let ok = jcc_fwd(CC_NS);
        store_imm32(m_rbp(scr() + 16), 0x5F800000);  // 2^64 as f32
        fadd_m32(m_rbp(scr() + 16));
        patch_here(ok);
    }
}

// ------------------------------------------------------------- lanes

fn lane_type(t: u32) -> u32 { M.types[t].elems }
fn lane_size(t: u32) -> u32 { M.types[M.types[t].elems].size }
// Loads lane k of vector v: INT lanes into RAX (zero-extended), FP lanes
// into xmm x.
fn load_lane(v: u32, k: u32, r: u32, x: u32) {
    let t = type_of(v);
    let lt = lane_type(t);
    let ls = lane_size(t);
    let m = m_add(val_mem(v), (k * ls));
    if cls_of(lt) == C_FP {
        if lt == GIR_T_F32 { movss_load(x, m); } else { movsd_load(x, m); }
    } else {
        load_n(r, m, ls);
    }
}
fn store_lane_gpr(j: u32, t: u32, k: u32, r: u32) {
    let ls = lane_size(t);
    store_n(m_add(res_mem(j), (k * ls)), r, ls);
}
fn store_lane_xmm(j: u32, t: u32, k: u32, x: u32) {
    let lt = lane_type(t);
    let m = m_add(res_mem(j), (k * lane_size(t)));
    if lt == GIR_T_F32 { movss_store(m, x); } else { movsd_store(m, x); }
}

fn vec_binop(I: Inst, j: u32) {
    let t = I.ty;
    let lt = lane_type(t);
    let n = M.types[t].n;
    let fp = I.op >= GIR_FADD && I.op <= GIR_FDIV;
    for k in 0..n {
        if fp {
            load_lane(I.a, k, RAX, XMM0);
            load_lane(I.b, k, RCX, XMM1);
            sse_arith(sse_op(I.op), lt == GIR_T_F64, XMM0, XMM1);
            store_lane_xmm(j, t, k, XMM0);
        } else {
            load_lane(I.a, k, RAX, XMM0);
            load_lane(I.b, k, RCX, XMM1);
            int_binop(I.op, bits_of(lt));
            store_lane_gpr(j, t, k, RAX);
        }
    }
}
fn vec_cmp(I: Inst, j: u32) {
    let at = I.aux;
    let lt = lane_type(at);
    let n = M.types[at].n;
    for k in 0..n {
        load_lane(I.a, k, RAX, XMM0);
        load_lane(I.b, k, RCX, XMM1);
        if I.op == GIR_FCMP { fcmp_xmm(I.sub, lt == GIR_T_F64); }
        else { int_cmp_rr(I.sub, bits_of(lt)); }
        store8(m_add(res_mem(j), k), RAX);
    }
}
// Lane-wise casts and unary FP operations.
fn vec_unary(I: Inst, j: u32) {
    let t = I.ty;
    let st = type_of(I.a);
    let dl = lane_type(t);
    let sl = lane_type(st);
    let n = M.types[t].n;
    for k in 0..n {
        load_lane(I.a, k, RAX, XMM0);
        let op = I.op;
        if op == GIR_ZEXT || op == GIR_TRUNC { zext_reg(RAX, bits_of(dl)); }
        else if op == GIR_SEXT {
            sext_reg(RAX, bits_of(sl));
            zext_reg(RAX, bits_of(dl));
        } else if op == GIR_FPEXT { cvtss2sd(XMM0, XMM0); }
        else if op == GIR_FPTRUNC { cvtsd2ss(XMM0, XMM0); }
        else if op == GIR_SITOFP || op == GIR_UITOFP { int_to_fp(dl == GIR_T_F64, op == GIR_SITOFP, bits_of(sl)); }
        else if op == GIR_FPTOSI || op == GIR_FPTOUI { fp_to_int(sl == GIR_T_F64, op == GIR_FPTOSI, bits_of(dl)); }
        else if op == GIR_FNEG || op == GIR_FABS {
            if dl == GIR_T_F64 { movq_rx(RAX, XMM0); } else { movd_rx(RAX, XMM0); }
            fp_sign_op(op, dl == GIR_T_F64);
            if dl == GIR_T_F64 { movq_xr(XMM0, RAX); } else { movd_xr(XMM0, RAX); }
        } else if op == GIR_FSQRT { sse_arith(0x51, dl == GIR_T_F64, XMM0, XMM0); }
        if cls_of(dl) == C_FP && !(op == GIR_FPTOSI || op == GIR_FPTOUI) { store_lane_xmm(j, t, k, XMM0); }
        else if cls_of(dl) == C_FP { store_lane_xmm(j, t, k, XMM0); }
        else { store_lane_gpr(j, t, k, RAX); }
    }
}
// Sign-bit operations on the bits of an f32/f64 in RAX.
fn fp_sign_op(op: u32, dbl: bool) {
    if op == GIR_FNEG {
        if dbl { bt_ri64(7, RAX, 63); } else { grp1_ri32(G1_XOR, RAX, 0x80000000); }
    } else {
        if dbl { bt_ri64(6, RAX, 63); } else { grp1_ri32(G1_AND, RAX, 0x7FFFFFFF); }
    }
}

// ------------------------------------------------------- INT2 (i65..i128)

fn int2_norm_hi(r: u32, bits: u32) { if bits < 128 { zext_reg(r, bits - 64); } }
// Sign-extends a (lo, hi) pair from `bits` to 128.
fn int2_sext(hi: u32, bits: u32) { if bits < 128 { sext_reg(hi, bits - 64); } }

fn int2_binop(I: Inst, j: u32) {
    let bits = bits_of(I.ty);
    let op = I.op;
    if op == GIR_SHL || op == GIR_LSHR || op == GIR_ASHR {
        use_gpr2(I.a, RAX, RDX);
        if gir_kind(I.b) == GIR_V_CONST { mov_ri(RCX, M.consts[gir_idx(I.b)].lo); }
        else { use_gpr2(I.b, RCX, RSI); }
        if op == GIR_ASHR { int2_sext(RDX, bits); }
        if op == GIR_SHL {
            shld_cl64(RDX, RAX);
            shift_cl64(SH_SHL, RAX);
        } else {
            shrd_cl64(RAX, RDX);
            shift_cl64(if op == GIR_LSHR { SH_SHR } else { SH_SAR }, RDX);
        }
        op_rr(0, 0xF6, 0, RCX, false);  // test cl, 64
        b1(64);
        let skip = jcc_fwd(CC_E);
        if op == GIR_SHL {
            mov_rr64(RDX, RAX);
            op_rr(0, ALU_XOR, RAX, RAX, false);
        } else {
            mov_rr64(RAX, RDX);
            if op == GIR_LSHR { op_rr(0, ALU_XOR, RDX, RDX, false); } else { shift_imm64(SH_SAR, RDX, 63); }
        }
        patch_here(skip);
        int2_norm_hi(RDX, bits);
        put_gpr2(j, RAX, RDX);
        return;
    }
    use_gpr2(I.a, RAX, RDI);
    use_gpr2(I.b, RCX, RSI);
    if op == GIR_ADD {
        alu_rr64(ALU_ADD, RAX, RCX);
        alu_rr64(ALU_ADC, RDI, RSI);
    } else if op == GIR_SUB {
        alu_rr64(ALU_SUB, RAX, RCX);
        alu_rr64(ALU_SBB, RDI, RSI);
    } else if op == GIR_AND {
        alu_rr64(ALU_AND, RAX, RCX);
        alu_rr64(ALU_AND, RDI, RSI);
    } else if op == GIR_OR {
        alu_rr64(ALU_OR, RAX, RCX);
        alu_rr64(ALU_OR, RDI, RSI);
    } else if op == GIR_XOR {
        alu_rr64(ALU_XOR, RAX, RCX);
        alu_rr64(ALU_XOR, RDI, RSI);
    } else {  // MUL: lo = a.lo * b.lo; hi = high(a.lo * b.lo) + a.hi * b.lo + a.lo * b.hi
        mov_rr64(R8, RDI);
        imul_rr64(R8, RCX);
        mov_rr64(R9, RSI);
        imul_rr64(R9, RAX);
        div64(4, RCX);  // mul rcx: rdx:rax = rax * rcx
        alu_rr64(ALU_ADD, RDX, R8);
        alu_rr64(ALU_ADD, RDX, R9);
        mov_rr64(RDI, RDX);
    }
    int2_norm_hi(RDI, bits);
    put_gpr2(j, RAX, RDI);
}
// INT2 compare -> 0/1 in EAX.
fn int2_cmp(pred: u32, bits: u32, a: u32, b: u32) {
    use_gpr2(a, RAX, RDX);
    use_gpr2(b, RCX, RSI);
    if pred == GIR_EQ || pred == GIR_NE {
        alu_rr64(ALU_XOR, RAX, RCX);
        alu_rr64(ALU_XOR, RDX, RSI);
        alu_rr64(ALU_OR, RAX, RDX);
        setcc(if pred == GIR_EQ { CC_E } else { CC_NE }, RAX);
        movzx8(RAX, RAX);
        return;
    }
    let sgn = pred >= GIR_SGT;
    if sgn {
        int2_sext(RDX, bits);
        int2_sext(RSI, bits);
    }
    // x < y  <=>  borrow of (x - y); compute with sub/sbb on copies.
    let swap = pred == GIR_UGT || pred == GIR_ULE || pred == GIR_SGT || pred == GIR_SLE;
    if swap {
        // compute b - a
        alu_rr64(ALU_CMP, RCX, RAX);
        alu_rr64(ALU_SBB, RSI, RDX);
    } else {
        alu_rr64(ALU_CMP, RAX, RCX);
        alu_rr64(ALU_SBB, RDX, RSI);
    }
    // flags now describe (x < y) for x, y = (a, b) or (b, a)
    var cc: u32 = 0;
    if pred == GIR_ULT || pred == GIR_UGT { cc = CC_B; }
    else if pred == GIR_UGE || pred == GIR_ULE { cc = CC_AE; }
    else if pred == GIR_SLT || pred == GIR_SGT { cc = CC_L; }
    else { cc = CC_GE; }
    setcc(cc, RAX);
    movzx8(RAX, RAX);
}

// ------------------------------------------------------ bit operations

fn lower_bitop(I: Inst, j: u32) {
    let bits = bits_of(I.ty);
    use_fixed(I.a, RAX);
    let op = I.op;
    if op == GIR_CTLZ {
        mov_ri(RCX, 0xFFFFFFFFFFFFFFFF);
        bsr64(RAX, RAX);
        cmov64(CC_E, RAX, RCX);
        neg64(RAX);
        grp1_ri64(G1_ADD, RAX, (bits - 1) as! i32);
    } else if op == GIR_CTTZ {
        mov_ri(RCX, bits);
        bsf64(RAX, RAX);
        cmov64(CC_E, RAX, RCX);
    } else if op == GIR_CTPOP {
        mov_rr64(RCX, RAX);
        shift_imm64(SH_SHR, RCX, 1);
        mov_ri(RDX, 0x5555555555555555);
        alu_rr64(ALU_AND, RCX, RDX);
        alu_rr64(ALU_SUB, RAX, RCX);
        mov_ri(RDX, 0x3333333333333333);
        mov_rr64(RCX, RAX);
        alu_rr64(ALU_AND, RAX, RDX);
        shift_imm64(SH_SHR, RCX, 2);
        alu_rr64(ALU_AND, RCX, RDX);
        alu_rr64(ALU_ADD, RAX, RCX);
        mov_rr64(RCX, RAX);
        shift_imm64(SH_SHR, RCX, 4);
        alu_rr64(ALU_ADD, RAX, RCX);
        mov_ri(RDX, 0x0F0F0F0F0F0F0F0F);
        alu_rr64(ALU_AND, RAX, RDX);
        mov_ri(RDX, 0x0101010101010101);
        imul_rr64(RAX, RDX);
        shift_imm64(SH_SHR, RAX, 56);
    } else if op == GIR_BSWAP {
        bswap64(RAX);
        if bits < 64 { shift_imm64(SH_SHR, RAX, 64 - bits); }
    } else {  // BITREVERSE: swap bits, pairs, nibbles, then bytes
        bit_swap(1, 0x5555555555555555);
        bit_swap(2, 0x3333333333333333);
        bit_swap(4, 0x0F0F0F0F0F0F0F0F);
        bswap64(RAX);
        if bits < 64 { shift_imm64(SH_SHR, RAX, 64 - bits); }
    }
    put_gpr(j, RAX);
}
// rax = ((rax >> s) & m) | ((rax & m) << s)
fn bit_swap(s: u32, m: u64) {
    mov_ri(RDX, m);
    mov_rr64(RCX, RAX);
    shift_imm64(SH_SHR, RCX, s);
    alu_rr64(ALU_AND, RCX, RDX);
    alu_rr64(ALU_AND, RAX, RDX);
    shift_imm64(SH_SHL, RAX, s);
    alu_rr64(ALU_OR, RAX, RCX);
}
// fshl/fshr for widths 1..64.
fn lower_funnel(I: Inst, j: u32) {
    let bits = bits_of(I.ty);
    let left = I.op == GIR_FSHL;
    use_fixed(I.a, RAX);
    use_fixed(I.b, RDX);
    use_fixed(I.c, RCX);
    if bits == 64 || bits == 32 {
        if left { op_rr(if bits == 64 { 1 } else { 0 }, 0x0FA5, RDX, RAX, false); }   // shld rax, rdx, cl
        else {
            op_rr(if bits == 64 { 1 } else { 0 }, 0x0FAD, RAX, RDX, false);           // shrd rdx, rax, cl
            mov_rr64(RAX, RDX);
        }
        if bits == 32 { mov_rr32(RAX, RAX); }
        put_gpr(j, RAX);
        return;
    }
    // s = c % bits in RCX
    mov_rr64(R8, RAX);
    mov_rr64(RAX, RCX);
    mov_ri(RCX, bits);
    op_rr(0, ALU_XOR, R9, R9, false);
    mov_rr64(R10, RDX);
    op_rr(0, ALU_XOR, RDX, RDX, false);
    div64(6, RCX);           // rdx = c % bits
    mov_rr64(RCX, RDX);      // s
    // fshl: (a << s) | (b >> (bits - s)); fshr: (b >> s) | (a << (bits - s)); s == 0 -> a (fshl) or b (fshr)
    mov_rr64(RAX, if left { R8 } else { R10 });
    test_rr32(RCX, RCX);
    let zero = jcc_fwd(CC_E);
    if left {
        shift_cl64(SH_SHL, R8);
        mov_rr64(R9, RCX);
        mov_ri(RCX, bits);
        alu_rr64(ALU_SUB, RCX, R9);
        shift_cl64(SH_SHR, R10);
    } else {
        shift_cl64(SH_SHR, R10);
        mov_rr64(R9, RCX);
        mov_ri(RCX, bits);
        alu_rr64(ALU_SUB, RCX, R9);
        shift_cl64(SH_SHL, R8);
    }
    mov_rr64(RAX, R8);
    alu_rr64(ALU_OR, RAX, R10);
    zext_reg(RAX, bits);
    patch_here(zero);
    put_gpr(j, RAX);
}

fn lower_ovf(I: Inst, j: u32) {
    let vt: u32 = I.aux;
    let bits = bits_of(vt);
    let k: u32 = I.sub;
    use_fixed(I.a, RAX);
    use_fixed(I.b, RCX);
    if k == OVF_SADD || k == OVF_SSUB || k == OVF_SMUL {
        sext_reg(RAX, bits);
        sext_reg(RCX, bits);
        if k == OVF_SADD { alu_rr64(ALU_ADD, RAX, RCX); }
        else if k == OVF_SSUB { alu_rr64(ALU_SUB, RAX, RCX); }
        else { imul_rr64(RAX, RCX); }
        setcc(CC_O, R8);
        if bits < 64 {
            mov_rr64(RDX, RAX);
            sext_reg(RDX, bits);
            alu_rr64(ALU_CMP, RDX, RAX);
            setcc(CC_NE, RDX);
            alu_rr8(ALU_OR, RDX, R8);
        } else {
            mov_rr64(RDX, R8);
        }
    } else if k == OVF_UADD {
        alu_rr64(ALU_ADD, RAX, RCX);
        if bits < 64 {
            mov_rr64(RDX, RAX);
            shift_imm64(SH_SHR, RDX, bits);
            test_rr64(RDX, RDX);
            setcc(CC_NE, RDX);
        } else {
            setcc(CC_B, RDX);
        }
    } else if k == OVF_USUB {
        alu_rr64(ALU_CMP, RAX, RCX);
        setcc(CC_B, R8);
        alu_rr64(ALU_SUB, RAX, RCX);
        mov_rr64(RDX, R8);
    } else {  // UMUL
        div64(4, RCX);  // mul rcx: rdx:rax
        setcc(CC_O, R8);
        if bits < 64 {
            mov_rr64(RDX, RAX);
            shift_imm64(SH_SHR, RDX, bits);
            test_rr64(RDX, RDX);
            setcc(CC_NE, RDX);
            alu_rr8(ALU_OR, RDX, R8);
        } else {
            mov_rr64(RDX, R8);
        }
    }
    zext_reg(RAX, bits);
    let m = res_mem(j);
    let d = M.types[I.ty];
    store_n(m, RAX, store_of(vt));
    store8(m_add(m, M.opnds[d.elems + 3]), RDX);
}

// x86 SSE intrinsics on 16-byte vectors.
fn lower_x86(I: Inst, j: u32) {
    movups_load(XMM0, val_mem(I.a));
    let k: u32 = I.sub;
    if k == X86_MOVMSKPS {
        sse_rr(P_NONE, 0, 0x0F50, RAX, XMM0);
        put_gpr(j, RAX);
        return;
    }
    if k == X86_MAXPS || k == X86_MINPS || k == X86_PACKSSDW {
        movups_load(XMM1, val_mem(I.b));
        if k == X86_MAXPS { sse_rr(P_NONE, 0, 0x0F5F, XMM0, XMM1); }
        else if k == X86_MINPS { sse_rr(P_NONE, 0, 0x0F5D, XMM0, XMM1); }
        else { sse_rr(P_66, 0, 0x0F6B, XMM0, XMM1); }
    } else {
        use_fixed(I.b, RAX);
        mov_rr32(RAX, RAX);
        movq_xr(XMM1, RAX);
        let op: u32 = match k {
            X86_PSLLIW => 0x0FF1,
            X86_PSRLIW => 0x0FD1,
            X86_PSRAIW => 0x0FE1,
            X86_PSLLID => 0x0FF2,
            X86_PSRLID => 0x0FD2,
            _ => 0x0FE2,
        };
        sse_rr(P_66, 0, op, XMM0, XMM1);
    }
    movups_store(res_mem(j), XMM0);
}

// ----------------------------------------------------------- is.fpclass

// Class bit (LLVM FPClassTest) of an f32/f64 whose bits are in RAX, into
// ECX; then EAX = (ECX & mask) != 0.
fn lower_isfpclass(I: Inst, j: u32) {
    let t: u32 = I.aux;
    let mask = I.b;
    var fix: u32[8] = [0; 8];
    var nf: u32 = 0;
    if t == GIR_T_F80 {
        let m = val_mem(I.a);
        load64(RAX, m);
        load16z(RDX, m_add(m, 8));
        mov_rr32(RCX, RDX);
        grp1_ri32(G1_AND, RCX, 0x7FFF);
        grp1_ri32(G1_CMP, RCX, 0x7FFF);
        let special = jcc_fwd(CC_E);
        test_rr32(RCX, RCX);
        let denz = jcc_fwd(CC_E);
        // normal exponent: integer bit set -> normal, else invalid (NaN)
        bt_ri64(4, RAX, 63);
        let unnormal = jcc_fwd(CC_AE);
        mov_ri(RCX, 256);
        mov_ri(R8, 8);
        fix[nf] = jmp_fwd(); nf++;
        patch_here(denz);
        test_rr64(RAX, RAX);
        let nonzero = jcc_fwd(CC_NE);
        mov_ri(RCX, 64);
        mov_ri(R8, 32);
        fix[nf] = jmp_fwd(); nf++;
        patch_here(nonzero);
        bt_ri64(4, RAX, 63);
        let pseudo = jcc_fwd(CC_B);
        mov_ri(RCX, 128);
        mov_ri(R8, 16);
        fix[nf] = jmp_fwd(); nf++;
        patch_here(special);
        bt_ri64(4, RAX, 63);
        let invalid = jcc_fwd(CC_AE);
        mov_rr64(R9, RAX);
        bt_ri64(6, R9, 63);  // btr: clear the integer bit
        test_rr64(R9, R9);
        let nan = jcc_fwd(CC_NE);
        mov_ri(RCX, 512);
        mov_ri(R8, 4);
        fix[nf] = jmp_fwd(); nf++;
        patch_here(nan);
        bt_ri64(4, RAX, 62);
        mov_ri(RCX, 1);
        mov_ri(R8, 2);
        cmov64(CC_B, RCX, R8);
        let done1 = jmp_fwd();
        patch_here(unnormal);
        patch_here(pseudo);
        patch_here(invalid);
        mov_ri(RCX, 2);
        let done2 = jmp_fwd();
        // sign select for the signed classes
        for f in 0..nf { patch_here(fix[f]); }
        bt_ri64(4, RDX, 15);
        cmov64(CC_B, RCX, R8);
        patch_here(done1);
        patch_here(done2);
    } else {
        let dbl = t == GIR_T_F64;
        use_fixed(I.a, RAX);
        if !dbl { mov_rr32(RAX, RAX); }
        mov_rr64(RDX, RAX);
        if dbl { bt_ri64(6, RDX, 63); } else { grp1_ri32(G1_AND, RDX, 0x7FFFFFFF); }
        mov_ri(R9, if dbl { 0x7FF0000000000000 } else { 0x7F800000 });
        alu_rr64(ALU_CMP, RDX, R9);
        let nan = jcc_fwd(CC_A);
        let inf = jcc_fwd(CC_E);
        mov_ri(R9, if dbl { 0x0010000000000000 } else { 0x00800000 });
        alu_rr64(ALU_CMP, RDX, R9);
        let norm = jcc_fwd(CC_AE);
        test_rr64(RDX, RDX);
        let sub = jcc_fwd(CC_NE);
        mov_ri(RCX, 64);
        mov_ri(R8, 32);
        fix[nf] = jmp_fwd(); nf++;
        patch_here(sub);
        mov_ri(RCX, 128);
        mov_ri(R8, 16);
        fix[nf] = jmp_fwd(); nf++;
        patch_here(norm);
        mov_ri(RCX, 256);
        mov_ri(R8, 8);
        fix[nf] = jmp_fwd(); nf++;
        patch_here(inf);
        mov_ri(RCX, 512);
        mov_ri(R8, 4);
        fix[nf] = jmp_fwd(); nf++;
        patch_here(nan);
        mov_ri(R9, if dbl { 0x0008000000000000 } else { 0x00400000 });
        mov_ri(RCX, 1);
        mov_ri(R8, 2);
        test_rr64(RDX, R9);
        cmov64(CC_NE, RCX, R8);
        let done = jmp_fwd();
        for f in 0..nf { patch_here(fix[f]); }
        if dbl { test_rr64(RAX, RAX); } else { test_rr32(RAX, RAX); }
        cmov64(CC_S, RCX, R8);
        patch_here(done);
    }
    grp1_ri32(G1_AND, RCX, mask);
    setcc(CC_NE, RAX);
    movzx8(RAX, RAX);
    put_gpr(j, RAX);
}

// -------------------------------------------------------------- atomics

// lock-prefixed or plain op [m], r of size n (1, 2, 4, 8): opcode op8 for
// bytes, op for the rest.
fn atomic_rm(lock: bool, n: u32, op8: u32, op: u32, r: u32, m: Mem) {
    if lock { b1(0xF0); }
    if n == 1 { op_mem(0, 0, op8, r, m, true); }
    else if n == 2 { op_mem(P_66, 0, op, r, m, false); }
    else { op_mem(0, if n == 8 { 1 } else { 0 }, op, r, m, false); }
}
fn lower_cmpxchg(I: Inst, j: u32) {
    let vt: u32 = I.aux;
    let n = store_of(vt);
    let bits = bits_of(vt);
    use_fixed(I.b, RAX);
    use_fixed(I.c, RDX);
    let m = addr_of(I.a, RCX);
    atomic_rm(true, n, 0x0FB0, 0x0FB1, RDX, m);
    setcc(CC_E, RCX);
    zext_reg(RAX, bits);
    let r = res_mem(j);
    store_n(r, RAX, n);
    store8(m_add(r, M.opnds[M.types[I.ty].elems + 3]), RCX);
}
fn lower_atomicrmw(I: Inst, j: u32) {
    let t = I.ty;
    let n = store_of(t);
    let bits = bits_of(t);
    let k: u32 = I.sub;
    if k == RMW_FADD || k == RMW_FSUB {
        let dbl = t == GIR_T_F64;
        use_xmm(I.b, XMM1);
        let m = addr_of(I.a, RSI);
        load_n(RAX, m, n);
        let top = here();
        if dbl { movq_xr(XMM0, RAX); } else { movd_xr(XMM0, RAX); }
        sse_arith(if k == RMW_FADD { 0x58 } else { 0x5C }, dbl, XMM0, XMM1);
        if dbl { movq_rx(RCX, XMM0); } else { movd_rx(RCX, XMM0); }
        atomic_rm(true, n, 0x0FB0, 0x0FB1, RCX, m);
        jcc_back(CC_NE, top);
        store_n(res_mem(j), RAX, n);
        return;
    }
    use_fixed(I.b, RDX);
    let m = addr_of(I.a, RSI);
    if k == RMW_XCHG || k == RMW_ADD || k == RMW_SUB {
        mov_rr64(RAX, RDX);
        if k == RMW_SUB { neg64(RAX); }
        if k == RMW_XCHG { atomic_rm(false, n, 0x86, 0x87, RAX, m); }
        else { atomic_rm(true, n, 0x0FC0, 0x0FC1, RAX, m); }
        zext_reg(RAX, bits);
        put_gpr(j, RAX);
        return;
    }
    // cmpxchg loop: rax = old, rcx = new
    load_n(RAX, m, n);
    let top = here();
    mov_rr64(RCX, RAX);
    if k == RMW_AND { alu_rr64(ALU_AND, RCX, RDX); }
    else if k == RMW_OR { alu_rr64(ALU_OR, RCX, RDX); }
    else if k == RMW_XOR { alu_rr64(ALU_XOR, RCX, RDX); }
    else if k == RMW_NAND {
        alu_rr64(ALU_AND, RCX, RDX);
        not64(RCX);
    } else {
        // min/max: rcx = cond(old, val) ? old : val
        mov_rr64(R8, RAX);
        mov_rr64(R9, RDX);
        let sgn = k == RMW_MAX || k == RMW_MIN;
        if sgn {
            sext_reg(R8, bits);
            sext_reg(R9, bits);
        }
        alu_rr64(ALU_CMP, R8, R9);
        let cc: u32 = if k == RMW_MAX { CC_G } else if k == RMW_MIN { CC_L } else if k == RMW_UMAX { CC_A } else { CC_B };
        mov_rr64(RCX, RDX);
        cmov64(cc, RCX, RAX);
    }
    atomic_rm(true, n, 0x0FB0, 0x0FB1, RCX, m);
    jcc_back(CC_NE, top);
    zext_reg(RAX, bits);
    put_gpr(j, RAX);
}

// ---------------------------------------------------------------- TLS

fn lower_tlsaddr(I: Inst, j: u32) {
    let g = I.a;
    let G = M.globals[g];
    let pie = M.header[0].flags & MF_PIE != 0;
    let sym = g_sym[g];
    if pie {
        // mov rax, fs:[0]
        b1(0x64); b1(0x48); b1(0x8B); b1(0x04); b1(0x25); b4(0);
        if G.flags & GF_DEFINED != 0 {
            // local exec: lea rax, [rax + sym@tpoff]
            b1(0x48); b1(0x8D); b1(0x80);
            rela(here(), sym, R_X86_64_TPOFF32, 0);
            b4(0);
        } else {
            // initial exec: add rax, [rip + sym@gottpoff]
            b1(0x48); b1(0x03); b1(0x05);
            rela(here(), sym, R_X86_64_GOTTPOFF, -4);
            b4(0);
        }
    } else {
        // general dynamic: data16 lea rdi, [rip + sym@tlsgd]; data16 data16 rex.w call __tls_get_addr@plt
        b1(0x66); b1(0x48); b1(0x8D); b1(0x3D);
        rela(here(), sym, R_X86_64_TLSGD, -4);
        b4(0);
        b1(0x66); b1(0x66); b1(0x48); b1(0xE8);
        rela(here(), g_sym[M.header[0].tls_get_addr], R_X86_64_PLT32, -4);
        b4(0);
    }
    put_gpr(j, RAX);
}

// ---------------------------------------------------------- aggregates

// Loads a value of type t at m into the result of j (any class).
fn load_to_result(j: u32, t: u32, m: Mem) {
    let d = M.types[t];
    let c: u32 = d.cls;
    if c == C_INT {
        load_n(RAX, m, d.store);
        let b: u32 = d.bits;
        if b < 64 && b != d.store * 8 { zext_reg(RAX, b); }
        put_gpr(j, RAX);
    } else if c == C_INT2 {
        load64(RAX, m);
        load_n(RDX, m_add(m, 8), store_of(t) - 8);
        int2_norm_hi(RDX, bits_of(t));
        put_gpr2(j, RAX, RDX);
    } else {
        copy_mem_g(res_mem(j), m, store_of(t), gran_of(t));
    }
}
// Stores value v of type t at m (any class). m's base must not be RAX, RSI,
// RDI (or RDX for INT2).
fn store_value(m: Mem, v: u32, t: u32) {
    let c = cls_of(t);
    if c == C_INT {
        use_fixed(v, RAX);
        store_n(m, RAX, store_of(t));
    } else if c == C_INT2 {
        use_gpr2(v, RAX, RDX);
        store64(m, RAX);
        store_n(m_add(m, 8), RDX, store_of(t) - 8);
    } else {
        copy_mem_g(m, val_mem(v), store_of(t), gran_of(t));
    }
}

// Address of lane `idx` (value) of a vector at base, clamped into range:
// [RDX + RCX * lane size]. Returns the memory operand.
fn lane_addr(base: Mem, idx: u32, n: u32, ls: u32) -> Mem {
    lea64(RDX, base);
    use_fixed(idx, RCX);
    if n & (n - 1) == 0 { grp1_ri64(G1_AND, RCX, (n - 1) as! i32); }
    else {
        mov_ri(R8, 0);
        grp1_ri64(G1_CMP, RCX, n as! i32);
        cmov64(CC_AE, RCX, R8);
    }
    if ls > 1 {
        var sh: u32 = 0;
        while ((1 as u32) << sh) < ls { sh++; }
        shift_imm64(SH_SHL, RCX, sh);
    }
    alu_rr64(ALU_ADD, RDX, RCX);
    return m_reg(RDX, 0);
}

fn lower_extractelt(I: Inst, j: u32) {
    let vt: u32 = I.aux;
    let ls = lane_size(vt);
    let n = M.types[vt].n;
    if is_const(I.b) {
        let k = M.consts[gir_idx(I.b)].lo;
        let kk: u32 = if k < n { k as! u32 } else { 0 };
        load_to_result(j, I.ty, m_add(val_mem(I.a), (kk * ls)));
        return;
    }
    let m = lane_addr(val_mem(I.a), I.b, n, ls);
    load_to_result(j, I.ty, m);
}
fn lower_insertelt(I: Inst, j: u32) {
    let t = I.ty;
    let ls = lane_size(t);
    let n = M.types[t].n;
    let lt = lane_type(t);
    copy_val(res_mem(j), I.a, M.types[t].size);
    if is_const(I.c) {
        let k = M.consts[gir_idx(I.c)].lo;
        if k >= n { return; }
        store_value(m_add(res_mem(j), (k as! u32 * ls)), I.b, lt);
        return;
    }
    let m = lane_addr(res_mem(j), I.c, n, ls);
    // RDX is the base; store through RCX-free registers.
    if cls_of(lt) == C_INT {
        use_fixed(I.b, RAX);
        store_n(m, RAX, ls);
    } else {
        copy_mem(m, val_mem(I.b), ls);
    }
}
fn lower_shuffle(I: Inst, j: u32) {
    let t = I.ty;
    let at: u32 = I.aux;
    let na = M.types[at].n;
    let ls = lane_size(t);
    let n = M.types[t].n;
    for k in 0..n {
        let mk = M.opnds[I.c + k];
        let dst = m_add(res_mem(j), (k * ls));
        if mk == GIR_NONE { continue; }
        let src = if mk < na { m_add(val_mem(I.a), (mk * ls)) } else { m_add(val_mem(I.b), ((mk - na) * ls)) };
        copy_mem(dst, src, ls);
    }
}

// ------------------------------------------------------------- casts

fn lower_cast(I: Inst, j: u32) {
    let op: u32 = I.op;
    let dt = I.ty;
    let st: u32 = I.aux;
    let dc = cls_of(dt);
    let sc = cls_of(st);
    if dc == C_VEC && op != GIR_BITCAST {
        vec_unary(I, j);
        return;
    }
    if op == GIR_BITCAST {
        if dc == C_INT && sc == C_INT {
            use_fixed(I.a, RAX);
            put_gpr(j, RAX);
        } else if dc == C_INT {
            load_n(RAX, val_mem(I.a), store_of(dt));
            put_gpr(j, RAX);
        } else if sc == C_INT {
            use_fixed(I.a, RAX);
            store_n(res_mem(j), RAX, store_of(dt));
        } else {
            copy_val(res_mem(j), I.a, store_of(dt));
            if dc == C_INT2 && bits_of(dt) < 128 {
                load64(RDX, m_add(res_mem(j), 8));
                int2_norm_hi(RDX, bits_of(dt));
                store64(m_add(res_mem(j), 8), RDX);
            }
        }
        return;
    }
    if dc == C_INT2 || sc == C_INT2 {
        // integer casts involving i65..i128
        if sc == C_INT2 && dc == C_INT2 {
            use_gpr2(I.a, RAX, RDX);
            if op == GIR_SEXT { int2_sext(RDX, bits_of(st)); }
            int2_norm_hi(RDX, bits_of(dt));
            put_gpr2(j, RAX, RDX);
        } else if sc == C_INT2 {  // TRUNC to <= 64 bits
            use_gpr2(I.a, RAX, RDX);
            zext_reg(RAX, bits_of(dt));
            put_gpr(j, RAX);
        } else {  // ZEXT/SEXT from <= 64 bits
            use_fixed(I.a, RAX);
            if op == GIR_SEXT {
                sext_reg(RAX, bits_of(st));
                mov_rr64(RDX, RAX);
                shift_imm64(SH_SAR, RDX, 63);
            } else {
                op_rr(0, ALU_XOR, RDX, RDX, false);
            }
            int2_norm_hi(RDX, bits_of(dt));
            put_gpr2(j, RAX, RDX);
        }
        return;
    }
    match op {
        GIR_ZEXT, GIR_INTTOPTR => {
            use_fixed(I.a, RAX);
            put_gpr(j, RAX);
        },
        GIR_TRUNC, GIR_PTRTOINT => {
            use_fixed(I.a, RAX);
            zext_reg(RAX, bits_of(dt));
            put_gpr(j, RAX);
        },
        GIR_SEXT => {
            use_fixed(I.a, RAX);
            sext_reg(RAX, bits_of(st));
            zext_reg(RAX, bits_of(dt));
            put_gpr(j, RAX);
        },
        GIR_FPEXT, GIR_FPTRUNC => {
            if dc == C_X87 {
                fld_m(store_of(st), val_mem(I.a));
                fstp_m(10, res_mem(j));
            } else if sc == C_X87 {
                fld_m(10, val_mem(I.a));
                fstp_m(store_of(dt), res_mem(j));
            } else {
                use_xmm(I.a, XMM0);
                if op == GIR_FPEXT { cvtss2sd(XMM0, XMM0); } else { cvtsd2ss(XMM0, XMM0); }
                put_xmm(j, XMM0, dt);
            }
        },
        GIR_FPTOSI, GIR_FPTOUI => {
            if sc == C_X87 {
                fld_m(10, val_mem(I.a));
                x87_to_int(op == GIR_FPTOSI);
                zext_reg(RAX, bits_of(dt));
            } else {
                use_xmm(I.a, XMM0);
                fp_to_int(st == GIR_T_F64, op == GIR_FPTOSI, bits_of(dt));
            }
            put_gpr(j, RAX);
        },
        _ => {  // SITOFP, UITOFP
            use_fixed(I.a, RAX);
            if dc == C_X87 {
                int_to_x87(op == GIR_SITOFP, bits_of(st));
                fstp_m(10, res_mem(j));
            } else {
                int_to_fp(dt == GIR_T_F64, op == GIR_SITOFP, bits_of(st));
                put_xmm(j, XMM0, dt);
            }
        },
    }
}

// ---------------------------------------------------------- FP unary

fn lower_fp_unary(I: Inst, j: u32) {
    let t = I.ty;
    let c = cls_of(t);
    let op: u32 = I.op;
    if c == C_VEC {
        vec_unary(I, j);
        return;
    }
    if c == C_X87 {
        if op == GIR_COPYSIGN {
            let a = val_mem(I.a);
            let b = val_mem(I.b);
            let r = res_mem(j);
            load64(RAX, a);
            store64(r, RAX);
            load16z(RAX, m_add(a, 8));
            grp1_ri32(G1_AND, RAX, 0x7FFF);
            load16z(RCX, m_add(b, 8));
            grp1_ri32(G1_AND, RCX, 0x8000);
            alu_rr32(ALU_OR, RAX, RCX);
            store16(m_add(r, 8), RAX);
            return;
        }
        fld_m(10, val_mem(I.a));
        if op == GIR_FNEG { fchs(); } else if op == GIR_FABS { fabs_(); } else { fsqrt(); }
        fstp_m(10, res_mem(j));
        return;
    }
    let dbl = t == GIR_T_F64;
    if op == GIR_FSQRT {
        use_xmm(I.a, XMM0);
        sse_arith(0x51, dbl, XMM0, XMM0);
        put_xmm(j, XMM0, t);
        return;
    }
    use_fixed(I.a, RAX);
    if op == GIR_COPYSIGN {
        use_fixed(I.b, RCX);
        if dbl {
            bt_ri64(6, RAX, 63);
            shift_imm64(SH_SHR, RCX, 63);
            shift_imm64(SH_SHL, RCX, 63);
            alu_rr64(ALU_OR, RAX, RCX);
        } else {
            grp1_ri32(G1_AND, RAX, 0x7FFFFFFF);
            grp1_ri32(G1_AND, RCX, 0x80000000);
            alu_rr32(ALU_OR, RAX, RCX);
        }
    } else {
        fp_sign_op(op, dbl);
    }
    put_gpr(j, RAX);
}

// ---------------------------------------------------------------- misc

fn copy_slot(dst: Mem, src: Mem, t: u32) {
    copy_mem_g(dst, src, slot_size(t) as! u32, gran_of(t));
}

fn lower_select(I: Inst, j: u32) {
    let t = I.ty;
    let c = cls_of(t);
    let ct = type_of(I.a);
    if cls_of(ct) == C_VEC {
        // vector condition: lane by lane
        let n = M.types[t].n;
        let ls = lane_size(t);
        for k in 0..n {
            load8z(RDX, m_add(val_mem(I.a), k));
            load_n(RAX, m_add(val_mem(I.b), (k * ls)), ls);
            load_n(RCX, m_add(val_mem(I.c), (k * ls)), ls);
            test_rr32(RDX, RDX);
            cmov64(CC_E, RAX, RCX);
            store_n(m_add(res_mem(j), (k * ls)), RAX, ls);
        }
        return;
    }
    if c == C_INT {
        use_fixed(I.a, RAX);
        use_fixed(I.b, RCX);
        use_fixed(I.c, RDX);
        test_rr32(RAX, RAX);
        cmov64(CC_E, RCX, RDX);
        put_gpr(j, RCX);
        return;
    }
    if c == C_FP {
        use_fixed(I.a, RAX);
        load64(RCX, val_mem(I.b));
        load64(RDX, val_mem(I.c));
        test_rr32(RAX, RAX);
        cmov64(CC_E, RCX, RDX);
        put_gpr(j, RCX);
        return;
    }
    let n = slot_size(t) as! u32;
    use_fixed(I.a, RDX);
    test_rr32(RDX, RDX);
    let other = jcc_fwd(CC_E);
    copy_val(res_mem(j), I.b, n);
    let done = jmp_fwd();
    patch_here(other);
    copy_val(res_mem(j), I.c, n);
    patch_here(done);
}

// Zero-extending load / store of a predefined integer type (i1..i64, ptr).
checkfree fn load_small(r: u32, m: Mem, t: u32) {
    if t == GIR_T_I1 || t == GIR_T_I8 { load8z(r, m); }
    else if t == GIR_T_I16 { load16z(r, m); }
    else if t == GIR_T_I32 { load32(r, m); }
    else { load64(r, m); }
}
checkfree fn store_small(m: Mem, r: u32, t: u32) {
    if t == GIR_T_I1 || t == GIR_T_I8 { store8(m, r); }
    else if t == GIR_T_I16 { store16(m, r); }
    else if t == GIR_T_I32 { store32(m, r); }
    else { store64(m, r); }
}
fn lower_load(I: Inst, j: u32) {
    let m = addr_of(I.a, RCX);
    let t: u32 = I.ty;
    if t >= GIR_T_I1 && t <= GIR_T_PTR {  // the common case, without the type table
        load_small(RAX, m, t);
        if t == GIR_T_I1 { and_ri32(RAX, 1); }
        put_gpr(j, RAX);
        return;
    }
    load_to_result(j, t, m);
}
fn lower_store(I: Inst) {
    let t: u32 = I.aux;
    if t >= GIR_T_I1 && t <= GIR_T_PTR && I.flags & IF_ORD_MASK != ORD_SEQ_CST << IF_ORD_SHIFT {
        use_fixed(I.a, RAX);
        store_small(addr_of(I.b, RCX), RAX, t);
        return;
    }
    let d = M.types[t];
    let c: u32 = d.cls;
    let seq = (I.flags & IF_ORD_MASK) >> IF_ORD_SHIFT == ORD_SEQ_CST;
    if c == C_INT {
        use_fixed(I.a, RAX);
        let m = addr_of(I.b, RCX);
        let n = d.store;
        if seq && (n == 1 || n == 2 || n == 4 || n == 8) { atomic_rm(false, n, 0x86, 0x87, RAX, m); }
        else { store_n(m, RAX, n); }
        return;
    }
    if c == C_FP && seq {
        load_n(RAX, val_mem(I.a), store_of(t));
        let m = addr_of(I.b, RCX);
        atomic_rm(false, store_of(t), 0x86, 0x87, RAX, m);
        return;
    }
    let m = addr_of(I.b, RCX);
    store_value(m, I.a, t);
}

fn lower_dynalloca(I: Inst, j: u32) {
    use_fixed(I.a, RAX);
    grp1_ri64(G1_ADD, RAX, 15);
    grp1_ri64(G1_AND, RAX, -16);
    alu_rr64(ALU_SUB, RSP, RAX);
    let al = I.b;
    if al > 16 { grp1_ri64(G1_AND, RSP, (0 - al as! i64) as! i32); }
    mov_rr64(RAX, RSP);
    put_gpr(j, RAX);
}

fn lower_setjmp(I: Inst, j: u32) {
    use_fixed(I.a, RDX);
    // lea rax, [rip + resume]
    b1(0x48); b1(0x8D); b1(0x05);
    let p = here();
    b4(0);
    store64(m_reg(RDX, 8), RAX);
    store_imm64(res_mem(j), 0);
    let done = jmp_fwd();
    patch_here(p);  // resume point: after a longjmp, rbp and rsp are this frame's again
    store_imm64(res_mem(j), 1);
    patch_here(done);
}
fn lower_longjmp(I: Inst) {
    use_fixed(I.a, RDX);
    load64(RBP, m_reg(RDX, 0));
    load64(RCX, m_reg(RDX, 8));
    load64(RSP, m_reg(RDX, 16));
    jmp_r(RCX);
}

fn lower_frameaddr(I: Inst, j: u32) {
    mov_rr64(RAX, RBP);
    for k in 0..I.a { load64(RAX, m_reg(RAX, 0)); }
    if I.op == GIR_RETADDR { load64(RAX, m_reg(RAX, 8)); }
    put_gpr(j, RAX);
}

fn lower_blockaddr(I: Inst, j: u32) {
    let fi = M.globals[I.a].func;
    let gb = M.funcs[fi].first_block + I.b;
    b1(0x48); b1(0x8D); b1(0x05);  // lea rax, [rip + block]
    baddr.push(Fixup { pos: here(), blk: gb });
    b4(0);
    put_gpr(j, RAX);
}

fn lower_scmp(I: Inst, j: u32) {
    let at: u32 = I.aux;
    let bits = bits_of(at);
    use_fixed(I.a, RAX);
    use_fixed(I.b, RCX);
    let sgn = I.op == GIR_SCMP;
    if sgn {
        sext_reg(RAX, bits);
        sext_reg(RCX, bits);
    }
    alu_rr64(ALU_CMP, RAX, RCX);
    setcc(if sgn { CC_G } else { CC_A }, RAX);
    setcc(if sgn { CC_L } else { CC_B }, RCX);
    alu_rr8(ALU_SUB, RAX, RCX);
    movsx8_64(RAX, RAX);
    zext_reg(RAX, bits_of(I.ty));
    put_gpr(j, RAX);
}

// Inline assembly: inputs into their registers (x87 ones pushed deepest
// first), the assembled code, then the outputs out of theirs.
fn lower_asm(I: Inst, j: u32) {
    let A = M.asms[I.a];
    let ins = A.ops;
    // x87 inputs, deepest first
    var k: i64 = A.n_in as i64 - 1;  // (u32 - 1 would wrap before widening)
    while k >= 0 {
        let v = M.opnds[ins + 2 * k as! u32];
        let r = M.opnds[ins + 2 * k as! u32 + 1];
        if r >= ASMREG_ST0 {
            let t = type_of(v);
            fld_m(store_of(t), val_mem(v));
        }
        k--;
    }
    for q in 0..A.n_in {
        let v = M.opnds[ins + 2 * q];
        let r = M.opnds[ins + 2 * q + 1];
        if r >= ASMREG_XMM0 && r < ASMREG_ST0 {
            let t = type_of(v);
            if cls_of(t) == C_FP { use_xmm(v, r - ASMREG_XMM0); }
            else { xmm_load_n(r - ASMREG_XMM0, val_mem(v), store_of(t)); }
        }
    }
    for q in 0..A.n_in {
        let v = M.opnds[ins + 2 * q];
        let r = M.opnds[ins + 2 * q + 1];
        if r < ASMREG_XMM0 { use_fixed(v, r); }
    }
    code.append(M.data[A.code..A.code + A.code_len]);
    if I.ty == GIR_T_VOID { return; }
    let outs = ins + 2 * A.n_in;
    let res = res_mem(j);
    let single = A.n_out == 1 && cls_of(I.ty) != C_MEM;
    // GPR and xmm outputs first, then the x87 ones (st0 first).
    for q in 0..A.n_out {
        let r = M.opnds[outs + 2 * q];
        let off = M.opnds[outs + 2 * q + 1];
        let ft = if single { I.ty } else { M.opnds[M.types[I.ty].elems + 2 * q] };
        let m = m_add(res, off);
        if r < ASMREG_XMM0 {
            if single && cls_of(ft) == C_INT {
                zext_reg(r, bits_of(ft));
                store64(m, r);
            } else {
                store_n(m, r, store_of(ft));
            }
        } else if r < ASMREG_ST0 {
            xmm_store_n(m, r - ASMREG_XMM0, store_of(ft));
        }
    }
    for q in 0..A.n_out {
        let r = M.opnds[outs + 2 * q];
        let off = M.opnds[outs + 2 * q + 1];
        let ft = if single { I.ty } else { M.opnds[M.types[I.ty].elems + 2 * q] };
        if r >= ASMREG_ST0 { fstp_m(store_of(ft), m_add(res, off)); }
    }
    for q in 0..A.x87_pop { fstp_st0(); }
}
