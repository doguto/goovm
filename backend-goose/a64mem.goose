// AArch64 lowerings in memory (milestone F1): the operations whose values do
// not live in one register (INT2, aggregates, vectors that are not 8 or 16
// bytes of i8..i64/f32/f64 lanes, i1 vectors), the lane-by-lane vector code,
// odd-width integer loads and stores, overflow intrinsics, fp128 arithmetic
// by soft-float calls, atomics (outline-atomics helpers as clang's default,
// and LL/SC loops), TLS, setjmp/longjmp, inline assembly, landing pads.
//
// Like the x86-64 back-end's legacy lowerings (DESIGN.md §4), they run with
// every caller-saved register free (b_begin spills their values to their
// homes; callee-saved registers keep theirs and are not touched), read
// their operands from memory into fixed registers (b_gpr, b_vr, b_addr) and
// write results to their home (b_res) or hand back a register (b_set).
// Scratch: x0..x17, v0..v7, v16..v31.

fn b_begin(all: bool) {
    a_flush(if all { A_GP_ALL | A_V_ALL } else { A_GP_CALLER | A_V_CALLER });
    a_flags_id = RV_NONE;
}
// INT value v into register r.
fn b_gpr(v: u32, r: u32) {
    if is_val(v) {
        let id = vid(v);
        a_note(id);
        let vr: u32 = vi[id].reg;
        if vr < 32 {
            a_mov_rr(true, r, vr);
            if vi[id].st & ST_EXT != 0 { a_zext(r, bits_of(vtype(id))); }
            return;
        }
    }
    a_mat_gpr(v, r);
}
// FP / vector value v into V register r.
fn b_vr(v: u32, r: u32) {
    if is_val(v) {
        let id = vid(v);
        a_note(id);
        let vr: u32 = vi[id].reg;
        if vr < 64 && vr >= 32 {
            a_vmov(true, r, vr);
            return;
        }
    }
    a_mat_v(v, r);
}
// The address of v's memory in register r (any class).
fn b_addr(v: u32, r: u32) {
    if is_val(v) { a_note(vid(v)); }
    a_val_addr(v, r);
}
// The result of j goes to its home: the home's offset from x29.
fn b_res(j: u32) -> i64 {
    vi[j].st |= ST_MEM;
    vi[j].reg = NOREG;
    return a_home_off(j) as i64;
}
// The result of j is in register r (a scratch register of the lowering).
fn b_set(j: u32, r: u32, ext: bool) {
    a_set(j, r, ext);
}
// The result of j, of a register class, at x29 + off: loaded into its register class.
fn b_res_done(j: u32) {
    vi[j].st |= ST_MEM;
}

// ------------------------------------------------------------ INT2

// lo/hi of INT2 value v into r0/r1 (zero-extended above its width).
fn b_int2(v: u32, r0: u32, r1: u32) {
    let t = type_of(v);
    if gir_kind(v) == GIR_V_CONST {
        let c = M.consts[gir_idx(v)];
        a_mov_imm(r0, c.lo, true);
        a_mov_imm(r1, c.hi, true);
        return;
    }
    b_addr(v, AX16);
    a_ldstp(true, 0, r0, r1, AX16, 0);
    if bits_of(t) < 128 { a_zext(r1, bits_of(t) - 64); }
}
// r0/r1 into the result j (INT2 of `bits`), normalized.
fn b_set_int2(j: u32, r0: u32, r1: u32, bits: u32) {
    if bits < 128 { a_zext(r1, bits - 64); }
    let off = b_res(j);
    a_ldstp(false, 0, r0, r1, AFP, off);
}
// x1:x0 sign-extended from bits (for signed operations)
fn b_int2_sext(hi: u32, bits: u32) {
    if bits < 128 { a_bfm(ABF_SBFM, true, hi, hi, 0, bits - 65); }
}

fn b_int2_binop(I: Inst, j: u32) {
    let t: u32 = I.ty;
    let bits = bits_of(t);
    let op: u32 = I.op;
    b_int2(I.a, AX0, AX1);
    b_int2(I.b, AX2, AX3);
    if op == GIR_ADD {
        a_addsub_rr(AR_ADDS, true, AX0, AX0, AX2, 0, 0);
        a_adc(true, AX1, AX1, AX3);
    } else if op == GIR_SUB {
        a_addsub_rr(AR_SUBS, true, AX0, AX0, AX2, 0, 0);
        a_sbc(true, AX1, AX1, AX3);
    } else if op == GIR_AND {
        a_logic_rr(AL_AND, true, AX0, AX0, AX2, 0, 0);
        a_logic_rr(AL_AND, true, AX1, AX1, AX3, 0, 0);
    } else if op == GIR_OR {
        a_logic_rr(AL_ORR, true, AX0, AX0, AX2, 0, 0);
        a_logic_rr(AL_ORR, true, AX1, AX1, AX3, 0, 0);
    } else if op == GIR_XOR {
        a_logic_rr(AL_EOR, true, AX0, AX0, AX2, 0, 0);
        a_logic_rr(AL_EOR, true, AX1, AX1, AX3, 0, 0);
    } else if op == GIR_MUL {
        // lo = a0*b0; hi = umulh(a0, b0) + a0*b1 + a1*b0
        a_umulh(AX4, AX0, AX2);
        a_madd(true, AX4, AX0, AX3, AX4);
        a_madd(true, AX4, AX1, AX2, AX4);
        a_mul(true, AX0, AX0, AX2);
        a_mov_rr(true, AX1, AX4);
    } else if op == GIR_SHL || op == GIR_LSHR || op == GIR_ASHR {
        if op == GIR_ASHR { b_int2_sext(AX1, bits); }
        b_int2_shift(op, AX2);
    } else {
        // division: the exporter makes them library calls; anything else traps
        a_brk(1);
    }
    b_set_int2(j, AX0, AX1, bits);
}
// x1:x0 shifted by the amount in register s (0..127); clobbers x2..x6.
fn b_int2_shift(op: u32, s: u32) {
    // n = s & 63; big = s >= 64
    a_logic_imm(ALI_AND, true, AX5, s, a_bitmask(63, true));
    a_mov_imm(AX6, 64, true);
    a_addsub_rr(AR_SUB, true, AX6, AX6, AX5, 0, 0);       // 64 - n
    if op == GIR_SHL {
        // small: hi = hi << n | lo >> (64 - n) (n = 0: hi), lo = lo << n
        a_dp2(true, A2_LSL, AX4, AX1, AX5);
        a_dp2(true, A2_LSR, AX3, AX0, AX6);
        a_addsub_imm(AI_SUBS, true, AZR, AX5, 0, false);
        a_csel(true, AX3, AZR, AX3, AC_EQ);
        a_logic_rr(AL_ORR, true, AX4, AX4, AX3, 0, 0);
        a_dp2(true, A2_LSL, AX3, AX0, AX5);
        // big: hi = lo << n, lo = 0
        a_logic_imm(ALI_ANDS, true, AZR, s, a_bitmask(64, true));
        a_csel(true, AX1, AX4, AX3, AC_EQ);
        a_csel(true, AX0, AX3, AZR, AC_EQ);
        return;
    }
    let sh: u32 = if op == GIR_LSHR { A2_LSR } else { A2_ASR };
    // small: lo = lo >> n | hi << (64 - n) (n = 0: lo), hi = hi >> n
    a_dp2(true, A2_LSR, AX4, AX0, AX5);
    a_dp2(true, A2_LSL, AX3, AX1, AX6);
    a_addsub_imm(AI_SUBS, true, AZR, AX5, 0, false);
    a_csel(true, AX3, AZR, AX3, AC_EQ);
    a_logic_rr(AL_ORR, true, AX4, AX4, AX3, 0, 0);
    a_dp2(true, sh, AX3, AX1, AX5);
    // big: lo = hi >> n, hi = 0 or the sign
    if op == GIR_LSHR { a_mov_rr(true, AX6, AZR); } else { a_asr_imm(true, AX6, AX1, 63); }
    a_logic_imm(ALI_ANDS, true, AZR, s, a_bitmask(64, true));
    a_csel(true, AX0, AX4, AX3, AC_EQ);
    a_csel(true, AX1, AX3, AX6, AC_EQ);
}
// INT2 compare: x0 = 0/1.
fn b_int2_cmp(p: u32, bits: u32, va: u32, vb: u32) {
    b_int2(va, AX2, AX3);
    b_int2(vb, AX4, AX5);
    let sgn = a_signed_pred(p);
    if sgn {
        b_int2_sext(AX3, bits);
        b_int2_sext(AX5, bits);
    }
    if p == GIR_EQ || p == GIR_NE {
        a_logic_rr(AL_EOR, true, AX2, AX2, AX4, 0, 0);
        a_logic_rr(AL_EOR, true, AX3, AX3, AX5, 0, 0);
        a_logic_rr(AL_ORR, true, AX2, AX2, AX3, 0, 0);
        a_addsub_imm(AI_SUBS, true, AZR, AX2, 0, false);
        a_cset(AX0, if p == GIR_EQ { AC_EQ } else { AC_NE });
        return;
    }
    // a < b: cmp lo; sbcs hi -> lt / lo. gt, le: swapped operands.
    var swap = false;
    var cc: u32 = 0;
    if p == GIR_SLT { cc = AC_LT; } else if p == GIR_SGE { cc = AC_GE; }
    else if p == GIR_ULT { cc = AC_LO; } else if p == GIR_UGE { cc = AC_HS; }
    else if p == GIR_SGT { cc = AC_LT; swap = true; } else if p == GIR_SLE { cc = AC_GE; swap = true; }
    else if p == GIR_UGT { cc = AC_LO; swap = true; } else { cc = AC_HS; swap = true; }
    if swap {
        a_cmp_rr(true, AX4, AX2);
        a_sbcs(true, AZR, AX5, AX3);
    } else {
        a_cmp_rr(true, AX2, AX4);
        a_sbcs(true, AZR, AX3, AX5);
    }
    a_cset(AX0, cc);
}

// ------------------------------------------------------------ memory values

// Loads a value of type t at [base + off] into the result of j (any class).
fn b_load_to(j: u32, t: u32, base: u32, off: i64) {
    let d = M.types[t];
    let c = arc(t);
    if c == ARC_GPR {
        a_load_n(AX0, base, off, d.store);
        let b: u32 = d.bits;
        if b < 64 && b != d.store * 8 { a_zext(AX0, b); }
        b_set(j, AX0, false);
        return;
    }
    if a_inv(c) {
        a_ls(LS_FLDR, a_log2(d.store), AV0, base, off);
        b_set(j, AV0, false);
        return;
    }
    if d.cls == C_INT2 {
        a_ls(LS_LDR, 3, AX0, base, off);
        a_load_n(AX1, base, off + 8, d.store - 8);
        b_set_int2(j, AX0, AX1, d.bits);
        return;
    }
    let ro = b_res(j);
    a_copy(AFP, ro, base, off, d.store);
}
// Stores value v of type t at [base + off] (base is not x0..x3, x16, x17).
fn b_store_val(base: u32, off: i64, v: u32, t: u32) {
    let d = M.types[t];
    let c = arc(t);
    if c == ARC_GPR {
        b_gpr(v, AX0);
        a_store_n(AX0, base, off, d.store);
        return;
    }
    if a_inv(c) {
        b_vr(v, AV0);
        a_ls(LS_FSTR, a_log2(d.store), AV0, base, off);
        return;
    }
    if d.cls == C_INT2 {
        b_int2(v, AX0, AX1);
        a_ls(LS_STR, 3, AX0, base, off);
        a_store_n(AX1, base, off + 8, d.store - 8);
        return;
    }
    let sb, so = a_val_mem(v, AX2);
    if is_val(v) { a_note(vid(v)); }
    a_copy(base, off, sb, so, d.store);
}
fn b_lower_load(I: Inst, j: u32) {
    let ord = (I.flags & IF_ORD_MASK) >> IF_ORD_SHIFT;
    b_gpr(I.a, AX9);
    if ord != 0 && M.types[I.ty].store == 16 {
        // a 16-byte atomic load: ldxp + stxp of the same value until it succeeds
        let acq = ord >= 4;
        let top = here();
        if acq { a_ldaxp(AX0, AX1, AX9); } else { a_ldxp(AX0, AX1, AX9); }
        if ord == 7 { a_stlxp(AX2, AX0, AX1, AX9); } else { a_stxp(AX2, AX0, AX1, AX9); }
        a_cbz_raw(false, true, AX2);
        a_patch_branch(here() - 4, top, AF_B19);
        if arc(I.ty) == ARC_VR {
            a_fmov_from_gp(true, AV0, AX0);
            a_fmov_hi_from_gp(AV0, AX1);
            b_set(j, AV0, false);
        } else {
            b_set_int2(j, AX0, AX1, bits_of(I.ty));
        }
        return;
    }
    b_load_to(j, I.ty, AX9, 0);
    if ord >= 4 && ord != 5 { a_dmb(9); }
}
fn b_lower_store(I: Inst) {
    let ord = (I.flags & IF_ORD_MASK) >> IF_ORD_SHIFT;
    let t: u32 = I.aux;
    b_gpr(I.b, AX9);
    if ord != 0 && M.types[t].store == 16 {
        if arc(t) == ARC_VR {
            b_vr(I.a, AV0);
            a_fmov_to_gp(true, AX2, AV0);
            a_fmov_hi_to_gp(AX3, AV0);
        } else {
            b_int2(I.a, AX2, AX3);
        }
        let top = here();
        if ord >= 4 && ord != 5 { a_ldaxp(AX0, AX1, AX9); } else { a_ldxp(AX0, AX1, AX9); }
        if ord >= 5 { a_stlxp(AX4, AX2, AX3, AX9); } else { a_stxp(AX4, AX2, AX3, AX9); }
        a_cbz_raw(false, true, AX4);
        a_patch_branch(here() - 4, top, AF_B19);
        return;
    }
    if ord >= 5 { a_dmb(11); }
    b_store_val(AX9, 0, I.a, t);
    if ord == 7 { a_dmb(11); }
}
fn b_lower_extractvalue(I: Inst, j: u32) {
    let sb, so = a_val_mem(I.a, AX9);
    if is_val(I.a) { a_note(vid(I.a)); }
    b_load_to(j, I.ty, sb, so + I.b as i64);
}
fn b_lower_insertvalue(I: Inst, j: u32) {
    let t: u32 = I.ty;
    let ro = b_res(j);
    let sb, so = a_val_mem(I.a, AX9);
    if is_val(I.a) { a_note(vid(I.a)); }
    a_copy(AFP, ro, sb, so, M.types[t].size);
    a_add_off(AX9, AFP, ro + I.c as i64);
    b_store_val(AX9, 0, I.b, type_of(I.b));
}

// ------------------------------------------------------------ casts in memory

fn b_lower_cast(I: Inst, j: u32) {
    let op: u32 = I.op;
    let dt: u32 = I.ty;
    let st: u32 = I.aux;
    let dcl = cls_of(dt);
    let scl = cls_of(st);
    if dcl == C_VEC || scl == C_VEC && op != GIR_BITCAST {
        b_vec_cast(I, j);
        return;
    }
    if op == GIR_BITCAST || op == GIR_PTRTOINT || op == GIR_INTTOPTR {
        // same size: the bytes
        let sb, so = a_val_mem(I.a, AX9);
        if is_val(I.a) { a_note(vid(I.a)); }
        b_load_to(j, dt, sb, so);
        return;
    }
    if dcl == C_INT2 && scl == C_INT2 {
        // zext / sext / trunc between INT2 widths
        b_int2(I.a, AX0, AX1);
        if op == GIR_SEXT { b_int2_sext(AX1, bits_of(st)); }
        b_set_int2(j, AX0, AX1, bits_of(dt));
        return;
    }
    if dcl == C_INT2 {
        // zext / sext of an INT
        b_gpr(I.a, AX0);
        let sb = bits_of(st);
        if op == GIR_SEXT {
            a_sext(AX0, AX0, sb);
            a_asr_imm(true, AX1, AX0, 63);
        } else {
            a_zext(AX0, sb);
            a_mov_rr(true, AX1, AZR);
        }
        b_set_int2(j, AX0, AX1, bits_of(dt));
        return;
    }
    if scl == C_INT2 && dcl == C_INT {
        b_int2(I.a, AX0, AX1);
        let db = bits_of(dt);
        if db < 64 { a_zext(AX0, db); }
        b_set(j, AX0, false);
        return;
    }
    // fp128 and the conversions with no register path
    b_f128_cast(I, j);
}

// ------------------------------------------------------------ fp128 (soft float)

// The library routine of an fp128 binary operation.
fn b_f128_bin(I: Inst, j: u32) {
    b_vr(I.a, AV0);
    b_vr(I.b, AV0 + 1);
    let op: u32 = I.op;
    a_call_lib(if op == GIR_FADD { "__addtf3" } else if op == GIR_FSUB { "__subtf3" } else if op == GIR_FMUL { "__multf3" } else { "__divtf3" });
    a_after_call();
    b_set(j, AV0, false);
}
// fcmp on fp128: the comparison routine's int result against 0.
fn b_f128_cmp(I: Inst, j: u32) {
    let p: u32 = I.sub;
    if p == F_FALSE || p == F_TRUE {
        a_movz(false, AX0, if p == F_TRUE { 1 } else { 0 }, 0);
        b_set(j, AX0, false);
        return;
    }
    // ord / uno: __unordtf2 != 0; the others: one routine and a compare
    // (routine k: 0 eq, 1 ne, 2 gt, 3 ge, 4 lt, 5 le, 6 unord)
    var fk: u32 = 0;
    var cc: u32 = AC_EQ;
    if p == F_OEQ { fk = 0; cc = AC_EQ; }
    else if p == F_UNE { fk = 1; cc = AC_NE; }
    else if p == F_OGT { fk = 2; cc = AC_GT; }
    else if p == F_OGE { fk = 3; cc = AC_GE; }
    else if p == F_OLT { fk = 4; cc = AC_LT; }
    else if p == F_OLE { fk = 5; cc = AC_LE; }
    else if p == F_UNO { fk = 6; cc = AC_NE; }
    else if p == F_ORD { fk = 6; cc = AC_EQ; }
    else if p == F_UGT { fk = 5; cc = AC_GT; }
    else if p == F_UGE { fk = 4; cc = AC_GE; }
    else if p == F_ULT { fk = 3; cc = AC_LT; }
    else if p == F_ULE { fk = 2; cc = AC_LE; }
    let two = p == F_ONE || p == F_UEQ;
    if two {
        // one = olt || ogt (as LLVM: __eqtf2 != 0 && __unordtf2 == 0); ueq = !one
        b_vr(I.a, AV0);
        b_vr(I.b, AV0 + 1);
        a_ls(LS_FSTR, 4, AV0, AFP, b_scratch(32));
        a_ls(LS_FSTR, 4, AV0 + 1, AFP, b_scratch(32) + 16);
        a_call_lib("__eqtf2");
        a_ls(LS_STR, 2, AX0, AFP, b_scratch(32) + 32);
        a_ls(LS_FLDR, 4, AV0, AFP, b_scratch(32));
        a_ls(LS_FLDR, 4, AV0 + 1, AFP, b_scratch(32) + 16);
        a_call_lib("__unordtf2");
        a_ls(LS_LDR, 2, AX1, AFP, b_scratch(32) + 32);
        a_addsub_imm(AI_SUBS, false, AZR, AX0, 0, false);
        a_cset(AX0, AC_EQ);                                  // ordered
        a_addsub_imm(AI_SUBS, false, AZR, AX1, 0, false);
        a_cset(AX1, AC_NE);                                  // not equal
        a_logic_rr(AL_AND, false, AX0, AX0, AX1, 0, 0);
        if p == F_UEQ { a_logic_imm(ALI_EOR, false, AX0, AX0, a_bitmask(1, false)); }
        a_after_call();
        b_set(j, AX0, false);
        return;
    }
    b_vr(I.a, AV0);
    b_vr(I.b, AV0 + 1);
    a_call_lib(if fk == 0 { "__eqtf2" } else if fk == 1 { "__netf2" } else if fk == 2 { "__gttf2" } else if fk == 3 { "__getf2" }
               else if fk == 4 { "__lttf2" } else if fk == 5 { "__letf2" } else { "__unordtf2" });
    a_addsub_imm(AI_SUBS, false, AZR, AX0, 0, false);
    a_cset(AX0, cc);
    a_after_call();
    b_set(j, AX0, false);
}
// 48 bytes of per-function scratch in the frame (offset from x29).
var b_scr_off: i64 = 0;
fn b_scratch(n: i64) -> i64 {
    if b_scr_off == 0 { b_scr_off = a_new_slot(48) as i64; }
    return b_scr_off;
}
// Conversions with fp128 on one side (or with no register path).
fn b_f128_cast(I: Inst, j: u32) {
    let op: u32 = I.op;
    let dt: u32 = I.ty;
    let st: u32 = I.aux;
    if op == GIR_FPEXT || op == GIR_FPTRUNC {
        b_vr(I.a, AV0);
        if op == GIR_FPEXT {
            a_call_lib(if st == GIR_T_F32 { "__extendsftf2" } else if st == GIR_T_F16 { "__extendhftf2" } else { "__extenddftf2" });
        } else {
            a_call_lib(if dt == GIR_T_F32 { "__trunctfsf2" } else if dt == GIR_T_F16 { "__trunctfhf2" } else { "__trunctfdf2" });
        }
        a_after_call();
        b_set(j, AV0, false);
        return;
    }
    if op == GIR_FPTOSI || op == GIR_FPTOUI {
        b_vr(I.a, AV0);
        let db = bits_of(dt);
        let sgn = op == GIR_FPTOSI;
        if db <= 32 {
            a_call_lib(if sgn { "__fixtfsi" } else { "__fixunstfsi" });
        } else {
            a_call_lib(if sgn { "__fixtfdi" } else { "__fixunstfdi" });
        }
        a_after_call();
        if db < 64 && !exact_width(db) || db < 32 { a_zext(AX0, db); }
        b_set(j, AX0, false);
        return;
    }
    if op == GIR_SITOFP || op == GIR_UITOFP {
        let sb = bits_of(st);
        let sgn = op == GIR_SITOFP;
        b_gpr(I.a, AX0);
        if sgn { a_sext(AX0, AX0, sb); } else { a_zext(AX0, sb); }
        if sb <= 32 {
            a_call_lib(if sgn { "__floatsitf" } else { "__floatunsitf" });
        } else {
            a_call_lib(if sgn { "__floatditf" } else { "__floatunditf" });
        }
        a_after_call();
        b_set(j, AV0, false);
        return;
    }
    a_brk(1);
}
// fneg / fabs / copysign on fp128: the sign bit (bit 127).
fn b_f128_sign(I: Inst, j: u32) {
    b_vr(I.a, AV0);
    a_fmov_hi_to_gp(AX1, AV0);
    let op: u32 = I.op;
    if op == GIR_FNEG {
        a_logic_imm(ALI_EOR, true, AX1, AX1, a_bitmask(0x8000000000000000, true));
    } else if op == GIR_FABS {
        a_logic_imm(ALI_AND, true, AX1, AX1, a_bitmask(0x7FFFFFFFFFFFFFFF, true));
    } else {
        b_vr(I.b, AV0 + 1);
        a_fmov_hi_to_gp(AX2, AV0 + 1);
        a_logic_imm(ALI_AND, true, AX1, AX1, a_bitmask(0x7FFFFFFFFFFFFFFF, true));
        a_logic_imm(ALI_AND, true, AX2, AX2, a_bitmask(0x8000000000000000, true));
        a_logic_rr(AL_ORR, true, AX1, AX1, AX2, 0, 0);
    }
    a_fmov_hi_from_gp(AV0, AX1);
    b_set(j, AV0, false);
}
fn b_f128_sqrt(I: Inst, j: u32) {
    b_vr(I.a, AV0);
    a_call_lib("sqrtl");
    a_after_call();
    b_set(j, AV0, false);
}

// ------------------------------------------------------------ overflow intrinsics

fn b_lower_ovf(I: Inst, j: u32) {
    let vt: u32 = I.aux;
    let bits = bits_of(vt);
    let k: u32 = I.sub;
    let sgn = k == OVF_SADD || k == OVF_SSUB || k == OVF_SMUL;
    let w64 = bits > 32;
    b_gpr(I.a, AX0);
    b_gpr(I.b, AX1);
    if bits == 32 || bits == 64 {
        if k == OVF_SADD || k == OVF_UADD {
            a_addsub_rr(AR_ADDS, w64, AX2, AX0, AX1, 0, 0);
            a_cset(AX3, if sgn { AC_VS } else { AC_HS });
        } else if k == OVF_SSUB || k == OVF_USUB {
            a_addsub_rr(AR_SUBS, w64, AX2, AX0, AX1, 0, 0);
            a_cset(AX3, if sgn { AC_VS } else { AC_LO });
        } else if bits == 32 {
            if sgn { a_smull(AX2, AX0, AX1); } else { a_umull(AX2, AX0, AX1); }
            if sgn {
                a_addsub_ext(AR_SUBS, true, AZR, AX2, AX2, 6, 0);   // cmp x2, w2, sxtw
            } else {
                a_addsub_rr(AR_SUBS, true, AZR, AZR, AX2, 1, 32);   // cmp xzr, x2, lsr #32
            }
            a_cset(AX3, AC_NE);
        } else {
            if sgn {
                a_smulh(AX3, AX0, AX1);
                a_mul(true, AX2, AX0, AX1);
                a_addsub_rr(AR_SUBS, true, AZR, AX3, AX2, 2, 63);   // cmp hi, lo, asr #63
            } else {
                a_umulh(AX3, AX0, AX1);
                a_mul(true, AX2, AX0, AX1);
                a_addsub_imm(AI_SUBS, true, AZR, AX3, 0, false);
            }
            a_cset(AX3, AC_NE);
        }
    } else {
        // narrow and odd widths: in 64 bits on extended operands; overflow if
        // the result differs from its own extension from `bits`
        if sgn {
            a_sext(AX0, AX0, bits);
            a_sext(AX1, AX1, bits);
        } else {
            a_zext(AX0, bits);
            a_zext(AX1, bits);
        }
        if k == OVF_SADD || k == OVF_UADD { a_addsub_rr(AR_ADD, true, AX2, AX0, AX1, 0, 0); }
        else if k == OVF_SSUB || k == OVF_USUB { a_addsub_rr(AR_SUB, true, AX2, AX0, AX1, 0, 0); }
        else if bits <= 32 { a_mul(true, AX2, AX0, AX1); }
        else {
            // 33..63 bits: the 128-bit product
            if sgn { a_smulh(AX3, AX0, AX1); } else { a_umulh(AX3, AX0, AX1); }
            a_mul(true, AX2, AX0, AX1);
        }
        a_mov_rr(true, AX4, AX2);
        if sgn { a_sext(AX4, AX4, bits); } else { a_zext(AX4, bits); }
        a_cmp_rr(true, AX4, AX2);
        a_cset(AX5, AC_NE);
        if bits > 32 && (k == OVF_SMUL || k == OVF_UMUL) {
            // the high half must be the extension of the low half too
            if sgn { a_asr_imm(true, AX6, AX2, 63); } else { a_mov_rr(true, AX6, AZR); }
            a_cmp_rr(true, AX3, AX6);
            a_cset(AX6, AC_NE);
            a_logic_rr(AL_ORR, false, AX5, AX5, AX6, 0, 0);
        }
        a_zext(AX2, bits);
        a_mov_rr(true, AX3, AX5);
    }
    let ro = b_res(j);
    a_store_n(AX2, AFP, ro, M.types[vt].store);
    let f1 = M.opnds[M.types[I.ty].elems + 3];
    a_ls(LS_STR, 0, AX3, AFP, ro + f1 as i64);
}

// ------------------------------------------------------------ is.fpclass

// llvm.is.fpclass on f16/f32/f64/f128 from the bits: x0 = class mask bit of the value.
fn b_lower_isfpclass(I: Inst, j: u32) {
    let t: u32 = I.aux;
    let mask: u32 = I.b;
    // hi:lo = the value's bits; exponent / mantissa field positions per type
    var ebits: u32 = 8;
    var mbits: u32 = 23;
    if t == GIR_T_F64 { ebits = 11; mbits = 52; }
    else if t == GIR_T_F16 { ebits = 5; mbits = 10; }
    else if t == GIR_T_F128 { ebits = 15; mbits = 112; }
    b_vr(I.a, AV0);
    if t == GIR_T_F128 {
        a_fmov_to_gp(true, AX0, AV0);          // lo
        a_fmov_hi_to_gp(AX1, AV0);             // hi
    } else if t == GIR_T_F64 {
        a_fmov_to_gp(true, AX0, AV0);
        a_mov_rr(true, AX1, AZR);
    } else if t == GIR_T_F32 {
        a_fmov_to_gp(false, AX0, AV0);
        a_mov_rr(true, AX1, AZR);
    } else {
        a_umov(1, AX0, AV0, 0);
        a_mov_rr(true, AX1, AZR);
    }
    // sign -> x2; exponent -> x3; mantissa nonzero -> x4; quiet bit -> x5
    if t == GIR_T_F128 {
        a_lsr_imm(true, AX2, AX1, 63);
        a_ubfx(true, AX3, AX1, 48, 15);
        a_ubfx(true, AX4, AX1, 0, 48);
        a_logic_rr(AL_ORR, true, AX4, AX4, AX0, 0, 0);
        a_ubfx(true, AX5, AX1, 47, 1);
    } else {
        let tb = ebits + mbits + 1;
        a_lsr_imm(true, AX2, AX0, tb - 1);
        a_ubfx(true, AX3, AX0, mbits, ebits);
        a_ubfx(true, AX4, AX0, 0, mbits);
        a_ubfx(true, AX5, AX0, mbits - 1, 1);
    }
    // class bit in x6: LLVM FPClassTest: 1 snan, 2 qnan, 4 -inf, 8 -normal, 16 -subnormal,
    // 32 -zero, 64 +zero, 128 +subnormal, 256 +normal, 512 +inf
    let emax: u64 = ((1 as u64) << ebits) - 1;
    // default: normal
    a_mov_imm(AX6, 8, true);
    a_mov_imm(AX7, 256, true);
    a_addsub_imm(AI_SUBS, true, AZR, AX2, 0, false);
    a_csel(true, AX6, AX6, AX7, AC_NE);      // x6 = sign ? 8 : 256
    // exponent 0: zero or subnormal
    a_mov_imm(AX7, 32, true);
    a_mov_imm(AX8, 64, true);
    a_addsub_imm(AI_SUBS, true, AZR, AX2, 0, false);
    a_csel(true, AX7, AX7, AX8, AC_NE);      // zero class
    a_mov_imm(AX8, 16, true);
    a_mov_imm(AX9, 128, true);
    a_addsub_imm(AI_SUBS, true, AZR, AX2, 0, false);
    a_csel(true, AX8, AX8, AX9, AC_NE);      // subnormal class
    a_addsub_imm(AI_SUBS, true, AZR, AX4, 0, false);
    a_csel(true, AX7, AX7, AX8, AC_EQ);      // x7 = mantissa == 0 ? zero : subnormal
    a_addsub_imm(AI_SUBS, true, AZR, AX3, 0, false);
    a_csel(true, AX6, AX7, AX6, AC_EQ);
    // exponent max: inf or nan
    a_mov_imm(AX7, 4, true);
    a_mov_imm(AX8, 512, true);
    a_addsub_imm(AI_SUBS, true, AZR, AX2, 0, false);
    a_csel(true, AX7, AX7, AX8, AC_NE);      // inf class
    a_mov_imm(AX8, 2, true);
    a_mov_imm(AX9, 1, true);
    a_addsub_imm(AI_SUBS, true, AZR, AX5, 0, false);
    a_csel(true, AX8, AX8, AX9, AC_NE);      // nan class: quiet or signalling
    a_addsub_imm(AI_SUBS, true, AZR, AX4, 0, false);
    a_csel(true, AX7, AX7, AX8, AC_EQ);
    a_mov_imm(AX9, emax, true);
    a_cmp_rr(true, AX3, AX9);
    a_csel(true, AX6, AX7, AX6, AC_EQ);
    a_mov_imm(AX7, mask as u64, true);
    a_tst_rr(true, AX6, AX7);
    a_cset(AX0, AC_NE);
    b_set(j, AX0, false);
}

// ------------------------------------------------------------ vectors, lane by lane

fn b_lane_t(t: u32) -> u32 { M.types[t].elems }
fn b_lane_size(t: u32) -> u32 {
    let L = M.types[M.types[t].elems];
    if L.bits == 1 { return 1; }
    return L.size;
}
// Lane k of vector value at [base + off] into register r (x or v), zero-extended.
fn b_ld_lane(r: u32, base: u32, off: i64, lt: u32, ls: u32) {
    if r >= 32 { a_ls(LS_FLDR, a_log2(ls), r, base, off); }
    else { a_ls(LS_LDR, a_log2(ls), r, base, off); }
}
fn b_st_lane(r: u32, base: u32, off: i64, ls: u32) {
    if r >= 32 { a_ls(LS_FSTR, a_log2(ls), r, base, off); }
    else { a_ls(LS_STR, a_log2(ls), r, base, off); }
}
// The memory of v for lane access: (base register, offset), with base x9/x10/x11 for constants.
fn b_vmem(v: u32, scr: u32) -> u32, i64 {
    let b, o = a_val_mem(v, scr);
    if is_val(v) { a_note(vid(v)); }
    return b, o;
}
// One integer lane operation on clean operands x0, x1 -> x2 (bits = lane width).
fn b_lane_int(op: u32, bits: u32) {
    let w64 = bits > 32;
    if op == GIR_ADD { a_addsub_rr(AR_ADD, w64, AX2, AX0, AX1, 0, 0); }
    else if op == GIR_SUB { a_addsub_rr(AR_SUB, w64, AX2, AX0, AX1, 0, 0); }
    else if op == GIR_MUL { a_mul(w64, AX2, AX0, AX1); }
    else if op == GIR_AND { a_logic_rr(AL_AND, w64, AX2, AX0, AX1, 0, 0); }
    else if op == GIR_OR { a_logic_rr(AL_ORR, w64, AX2, AX0, AX1, 0, 0); }
    else if op == GIR_XOR { a_logic_rr(AL_EOR, w64, AX2, AX0, AX1, 0, 0); }
    else if op == GIR_SHL { a_dp2(w64, A2_LSL, AX2, AX0, AX1); }
    else if op == GIR_LSHR { a_dp2(w64, A2_LSR, AX2, AX0, AX1); }
    else if op == GIR_ASHR {
        a_sext(AX0, AX0, bits);
        a_dp2(true, A2_ASR, AX2, AX0, AX1);
    } else if op == GIR_UDIV { a_dp2(w64, A2_UDIV, AX2, AX0, AX1); }
    else if op == GIR_UREM {
        a_dp2(w64, A2_UDIV, AX2, AX0, AX1);
        a_msub(w64, AX2, AX2, AX1, AX0);
    } else {
        a_sext(AX0, AX0, bits);
        a_sext(AX1, AX1, bits);
        a_dp2(true, A2_SDIV, AX2, AX0, AX1);
        if op == GIR_SREM { a_msub(true, AX2, AX2, AX1, AX0); }
    }
}
fn b_vec_binop(I: Inst, j: u32) {
    let t: u32 = I.ty;
    let n = M.types[t].n;
    let lt = b_lane_t(t);
    let ls = b_lane_size(t);
    let fp = cls_of(lt) == C_FP;
    let ab, ao = b_vmem(I.a, AX9);
    let bb, bo = b_vmem(I.b, AX10);
    let ro = b_res(j);
    let op: u32 = I.op;
    for k in 0..n {
        let o: i64 = (k * ls) as i64;
        if fp {
            a_ls(LS_FLDR, a_log2(ls), AV0, ab, ao + o);
            a_ls(LS_FLDR, a_log2(ls), AV0 + 1, bb, bo + o);
            let kk: u32 = if op == GIR_FADD { AF2_FADD } else if op == GIR_FSUB { AF2_FSUB } else if op == GIR_FMUL { AF2_FMUL } else { AF2_FDIV };
            a_fp2(a_ft(lt), kk, AV0 + 2, AV0, AV0 + 1);
            a_ls(LS_FSTR, a_log2(ls), AV0 + 2, AFP, ro + o);
        } else {
            a_ls(LS_LDR, a_log2(ls), AX0, ab, ao + o);
            a_ls(LS_LDR, a_log2(ls), AX1, bb, bo + o);
            b_lane_int(op, bits_of(lt));
            a_ls(LS_STR, a_log2(ls), AX2, AFP, ro + o);
        }
    }
    b_vec_result(j);
}
// A vector result written to its home: a register-class result is loaded back.
fn b_vec_result(j: u32) {
    let t = M.insts[f_first_inst + j].ty;
    if arc(t) == ARC_VR {
        a_ls(LS_FLDR, a_log2(M.types[t].store), AV0, AFP, a_home_off(j) as i64);
        b_set(j, AV0, false);
        vi[j].st |= ST_MEM;
    }
}
// Unary FP lane ops (fneg, fabs, fsqrt, copysign uses two operands) and FMA.
fn b_vec_unary(I: Inst, j: u32) {
    let t: u32 = I.ty;
    let n = M.types[t].n;
    let lt = b_lane_t(t);
    let ls = b_lane_size(t);
    let ab, ao = b_vmem(I.a, AX9);
    var bb: u32 = 0;
    var bo: i64 = 0;
    var cb: u32 = 0;
    var co: i64 = 0;
    let op: u32 = I.op;
    if op == GIR_COPYSIGN || op == GIR_FMA {
        let x, y = b_vmem(I.b, AX10);
        bb = x;
        bo = y;
    }
    if op == GIR_FMA {
        let x, y = b_vmem(I.c, AX11);
        cb = x;
        co = y;
    }
    let ro = b_res(j);
    let ft = a_ft(lt);
    for k in 0..n {
        let o: i64 = (k * ls) as i64;
        a_ls(LS_FLDR, a_log2(ls), AV0, ab, ao + o);
        if op == GIR_FNEG { a_fp1(ft, AF1_FNEG, AV0, AV0); }
        else if op == GIR_FABS { a_fp1(ft, AF1_FABS, AV0, AV0); }
        else if op == GIR_FSQRT { a_fp1(ft, AF1_FSQRT, AV0, AV0); }
        else if op == GIR_FMA {
            a_ls(LS_FLDR, a_log2(ls), AV0 + 1, bb, bo + o);
            a_ls(LS_FLDR, a_log2(ls), AV0 + 2, cb, co + o);
            a_fma3(ft, 0, AV0, AV0, AV0 + 1, AV0 + 2);
        } else {
            // copysign
            a_ls(LS_LDR, a_log2(ls), AX0, ab, ao + o);
            a_ls(LS_LDR, a_log2(ls), AX1, bb, bo + o);
            let sb: u32 = bits_of(lt) - 1;
            let w64 = ls == 8;
            a_logic_imm(ALI_AND, w64, AX0, AX0, a_bitmask(~((1 as u64) << sb), w64));
            a_logic_imm(ALI_AND, w64, AX1, AX1, a_bitmask((1 as u64) << sb, w64));
            a_logic_rr(AL_ORR, w64, AX0, AX0, AX1, 0, 0);
            a_ls(LS_STR, a_log2(ls), AX0, AFP, ro + o);
            continue;
        }
        a_ls(LS_FSTR, a_log2(ls), AV0, AFP, ro + o);
    }
    b_vec_result(j);
}
// icmp / fcmp lane by lane: i1 lanes (one byte each, 0 or 1).
fn b_vec_cmp(I: Inst, j: u32) {
    let at: u32 = I.aux;
    let n = M.types[at].n;
    let lt = b_lane_t(at);
    let ls = b_lane_size(at);
    let ab, ao = b_vmem(I.a, AX9);
    let bb, bo = b_vmem(I.b, AX10);
    let ro = b_res(j);
    let p: u32 = I.sub;
    let rls = b_lane_size(I.ty);
    for k in 0..n {
        let o: i64 = (k * ls) as i64;
        if I.op == GIR_FCMP {
            a_ls(LS_FLDR, a_log2(ls), AV0, ab, ao + o);
            a_ls(LS_FLDR, a_log2(ls), AV0 + 1, bb, bo + o);
            let cc, cc2, comb = a_fcc_of(p);
            if comb == 3 { a_movz(false, AX2, 0, 0); }
            else if cc == AC_AL { a_movz(false, AX2, 1, 0); }
            else {
                a_fcmp(a_ft(lt), AV0, AV0 + 1);
                a_cset(AX2, cc);
                if comb == 2 { a_csel_k(false, 1, AX2, AX2, AZR, cc2 ^ 1); }
            }
        } else {
            a_ls(LS_LDR, a_log2(ls), AX0, ab, ao + o);
            a_ls(LS_LDR, a_log2(ls), AX1, bb, bo + o);
            let bits = bits_of(lt);
            if a_signed_pred(p) && bits < 64 {
                a_sext(AX0, AX0, bits);
                a_sext(AX1, AX1, bits);
            }
            a_cmp_rr(true, AX0, AX1);
            a_cset(AX2, a_icc(p));
        }
        a_ls(LS_STR, a_log2(rls), AX2, AFP, ro + (k * rls) as i64);
    }
    b_vec_result(j);
}
// select with a vector condition (i1 lanes) or on memory-class values.
fn b_lower_select(I: Inst, j: u32) {
    let t: u32 = I.ty;
    let ct = type_of(I.a);
    let ro = b_res(j);
    let bb, bo = b_vmem(I.b, AX10);
    let cb, co = b_vmem(I.c, AX11);
    if cls_of(ct) == C_VEC {
        let n = M.types[t].n;
        let ls = b_lane_size(t);
        let mb, mo = b_vmem(I.a, AX9);
        for k in 0..n {
            let o: i64 = (k * ls) as i64;
            a_ls(LS_LDR, 0, AX0, mb, mo + k as i64);
            a_ls(LS_LDR, a_log2(ls), AX1, bb, bo + o);
            a_ls(LS_LDR, a_log2(ls), AX2, cb, co + o);
            a_logic_imm(ALI_ANDS, false, AZR, AX0, a_bitmask(1, false));
            a_csel(true, AX1, AX1, AX2, AC_NE);
            a_ls(LS_STR, a_log2(ls), AX1, AFP, ro + o);
        }
        b_vec_result(j);
        return;
    }
    // scalar condition on a memory value: copy one or the other
    b_gpr(I.a, AX0);
    let n = a_slot_size(t) as! u32;
    let st = M.types[t].store;
    let cn: u32 = if st < n { st } else { n };
    a_tbz_raw(false, AX0, 0);
    let p = here() - 4;
    a_copy(AFP, ro, bb, bo, cn);
    let q = a_fwd_b();
    a_patch_branch(p, here(), AF_B14);
    a_copy(AFP, ro, cb, co, cn);
    a_here(q);
    b_vec_result(j);
}
// Vector casts lane by lane (and bitcasts between vectors and other types).
fn b_vec_cast(I: Inst, j: u32) {
    let op: u32 = I.op;
    let dt: u32 = I.ty;
    let st: u32 = I.aux;
    if op == GIR_BITCAST {
        let sb, so = b_vmem(I.a, AX9);
        b_load_to(j, dt, sb, so);
        return;
    }
    let n = M.types[dt].n;
    let dlt = b_lane_t(dt);
    let slt = b_lane_t(st);
    let dls = b_lane_size(dt);
    let sls = b_lane_size(st);
    let ab, ao = b_vmem(I.a, AX9);
    let ro = b_res(j);
    let sfp = cls_of(slt) == C_FP;
    let dfp = cls_of(dlt) == C_FP;
    let sbits = bits_of(slt);
    let dbits = bits_of(dlt);
    for k in 0..n {
        let si: i64 = (k * sls) as i64;
        let di: i64 = (k * dls) as i64;
        if sfp { a_ls(LS_FLDR, a_log2(sls), AV0, ab, ao + si); }
        else { a_ls(LS_LDR, a_log2(sls), AX0, ab, ao + si); }
        if op == GIR_SEXT {
            a_sext(AX0, AX0, sbits);
        } else if op == GIR_ZEXT || op == GIR_TRUNC || op == GIR_PTRTOINT || op == GIR_INTTOPTR {
            // the stored width is the destination's
        } else if op == GIR_FPEXT || op == GIR_FPTRUNC {
            let to: u32 = if dlt == GIR_T_F64 { AF1_CVT_D } else if dlt == GIR_T_F32 { AF1_CVT_S } else { AF1_CVT_H };
            a_fp1(a_ft(slt), to, AV0, AV0);
        } else if op == GIR_FPTOSI || op == GIR_FPTOUI {
            let w64 = dbits > 32;
            let sgn = op == GIR_FPTOSI || dbits < 32;
            a_fcvt_gp(w64, a_ft(slt), if sgn { AFC_FCVTZS } else { AFC_FCVTZU }, AX0, AV0);
        } else {
            let sgn = op == GIR_SITOFP;
            if sgn { a_sext(AX0, AX0, sbits); }
            a_fcvt_gp(sbits > 32 || sgn && sbits < 32, a_ft(dlt), if sgn { AFC_SCVTF } else { AFC_UCVTF }, AV0, AX0);
        }
        if dbits == 1 { a_logic_imm(ALI_AND, false, AX0, AX0, a_bitmask(1, false)); }
        if dfp { a_ls(LS_FSTR, a_log2(dls), AV0, AFP, ro + di); }
        else { a_ls(LS_STR, a_log2(dls), AX0, AFP, ro + di); }
    }
    b_vec_result(j);
}
fn b_lower_extractelt(I: Inst, j: u32) {
    let vt: u32 = I.aux;
    let ls = b_lane_size(vt);
    let vb, vo = b_vmem(I.a, AX9);
    let n = M.types[vt].n;
    let isc, c = a_cint(I.b);
    if isc {
        if c >= n as u64 { a_movz(false, AX0, 0, 0); b_set_any(j, I.ty); return; }
        b_load_to(j, I.ty, vb, vo + (c * ls as u64) as! i64);
        return;
    }
    b_gpr(I.b, AX1);
    // index masked to the lane count's power of two (an out-of-range index is poison)
    a_add_off(AX10, vb, vo);
    a_addsub_rr(AR_ADD, true, AX10, AX10, AX1, 0, a_log2(ls));
    b_load_to(j, I.ty, AX10, 0);
}
fn b_set_any(j: u32, t: u32) {
    if a_inv(arc(t)) {
        a_vzero(true, AV0);
        b_set(j, AV0, false);
    } else if arc(t) == ARC_GPR {
        b_set(j, AX0, false);
    } else {
        b_res(j);
    }
}
fn b_lower_insertelt(I: Inst, j: u32) {
    let vt: u32 = I.ty;
    let ls = b_lane_size(vt);
    let n = M.types[vt].n;
    let ro = b_res(j);
    let vb, vo = b_vmem(I.a, AX9);
    a_copy(AFP, ro, vb, vo, M.types[vt].store);
    let isc, c = a_cint(I.c);
    if isc {
        if c < n as u64 { b_store_val_lane(ro + (c * ls as u64) as! i64, I.b, b_lane_t(vt), ls); }
    } else {
        b_gpr(I.c, AX1);
        a_add_off(AX10, AFP, ro);
        a_addsub_rr(AR_ADD, true, AX10, AX10, AX1, 0, a_log2(ls));
        if cls_of(b_lane_t(vt)) == C_FP {
            b_vr(I.b, AV0);
            a_ls(LS_FSTR, a_log2(ls), AV0, AX10, 0);
        } else {
            b_gpr(I.b, AX0);
            a_ls(LS_STR, a_log2(ls), AX0, AX10, 0);
        }
    }
    b_vec_result(j);
}
fn b_store_val_lane(off: i64, v: u32, lt: u32, ls: u32) {
    if cls_of(lt) == C_FP {
        b_vr(v, AV0);
        a_ls(LS_FSTR, a_log2(ls), AV0, AFP, off);
    } else {
        b_gpr(v, AX0);
        a_ls(LS_STR, a_log2(ls), AX0, AFP, off);
    }
}
fn b_lower_shuffle(I: Inst, j: u32) {
    let t: u32 = I.ty;
    let at: u32 = I.aux;
    let n = M.types[t].n;
    let na = M.types[at].n;
    let ls = b_lane_size(t);
    let ab, ao = b_vmem(I.a, AX9);
    let bb, bo = b_vmem(I.b, AX10);
    let ro = b_res(j);
    for k in 0..n {
        let m = M.opnds[I.c + k];
        if m == GIR_NONE { continue; }
        let o: i64 = (k * ls) as i64;
        if m < na {
            a_ls(LS_LDR, a_log2(ls), AX0, ab, ao + (m * ls) as i64);
        } else {
            a_ls(LS_LDR, a_log2(ls), AX0, bb, bo + ((m - na) * ls) as i64);
        }
        a_ls(LS_STR, a_log2(ls), AX0, AFP, ro + o);
    }
    b_vec_result(j);
}
