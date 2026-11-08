// AArch64 atomics, TLS, setjmp/longjmp, inline assembly and landing pads
// (milestone F1; memory-tier lowerings, see a64mem.goose).
//
// Atomics follow clang's default for aarch64-linux-gnu (+outline-atomics):
// atomicrmw xchg/add/sub/and/or/xor and cmpxchg call libgcc's helpers
// (__aarch64_swp4_acq_rel, __aarch64_ldadd8_relax, __aarch64_cas16_acq, ...),
// which use LSE instructions when the CPU has them and LL/SC loops
// otherwise; the operations without a helper (nand, min, max, umin, umax,
// fadd, fsub, and all 16-byte read-modify-writes) are LL/SC loops here, as
// LLVM expands them. Atomic loads and stores of 1..8 bytes are ldar/stlr
// (a64low.goose); 16-byte ones are ldxp/stxp loops (a64mem.goose).

// The helper suffix of an ordering: relax, acq, rel, acq_rel.
fn b_ord_name(ord: u32) -> const u8[:] {
    if ord <= 2 { return "relax"; }
    if ord == 4 { return "acq"; }
    if ord == 5 { return "rel"; }
    return "acq_rel";
}
// The ordering of a cmpxchg for its helper: the success ordering, with the
// failure ordering's acquire merged in (LLVM's getMergedOrdering).
fn b_merged(succ: u32, fail: u32) -> u32 {
    if succ == 5 && fail >= 4 { return 6; }   // release + acquire failure: acq_rel
    if succ <= 2 && fail >= 4 { return 4; }
    return succ;
}
var b_hname: u8[>..] = [];
fn b_helper(base: const u8[:], n: u32, ord: u32) {
    b_hname.clear();
    b_hname.append("__aarch64_");
    b_hname.append(base);
    format(b_hname, n);
    b_hname.push('_');
    b_hname.append(b_ord_name(ord));
    a_call_lib(b_hname);
}

fn b_lower_cmpxchg(I: Inst, j: u32) {
    let vt: u32 = I.aux;
    let n = M.types[vt].store;
    let bits = bits_of(vt);
    let ord = (I.flags & IF_ORD_MASK) >> IF_ORD_SHIFT;
    let ford: u32 = ((I.flags & 0x0070) >> 4) as u32;
    let mo = b_merged(ord, ford);
    let ro = b_res(j);
    let f1 = M.opnds[M.types[I.ty].elems + 3];
    if n == 16 {
        b_gpr(I.a, AX4);
        b_int2(I.b, AX0, AX1);
        a_ldstp(false, 0, AX0, AX1, AFP, b_scratch(48));
        b_int2(I.c, AX2, AX3);
        b_helper("cas", 16, mo);
        a_ldstp(true, 0, AX2, AX3, AFP, b_scratch(48));
        a_cmp_rr(true, AX0, AX2);
        a_ccmp(true, AX1, AX3, 0, AC_EQ);
        a_cset(AX5, AC_EQ);
        if bits < 128 { a_zext(AX1, bits - 64); }
        a_ldstp(false, 0, AX0, AX1, AFP, ro);
        a_ls(LS_STR, 0, AX5, AFP, ro + f1 as i64);
        a_after_call();
        return;
    }
    b_gpr(I.a, AX2);
    b_gpr(I.b, AX0);
    a_zext(AX0, bits);
    a_ls(LS_STR, 3, AX0, AFP, b_scratch(48));
    b_gpr(I.c, AX1);
    b_helper("cas", n, mo);
    a_ls(LS_LDR, 3, AX1, AFP, b_scratch(48));
    a_zext(AX0, bits);
    a_cmp_rr(true, AX0, AX1);
    a_cset(AX5, AC_EQ);
    a_store_n(AX0, AFP, ro, n);
    a_ls(LS_STR, 0, AX5, AFP, ro + f1 as i64);
    a_after_call();
}

// ld(a)xr / st(l)xr of 2^s bytes for an ordering.
fn b_ldx(ord: u32, s: u32, rt: u32, rn: u32) {
    if ord >= 4 && ord != 5 { a_ldaxr(s, rt, rn); } else { a_ldxr(s, rt, rn); }
}
fn b_stx(ord: u32, s: u32, rs: u32, rt: u32, rn: u32) {
    if ord >= 5 { a_stlxr(s, rs, rt, rn); } else { a_stxr(s, rs, rt, rn); }
}

fn b_lower_atomicrmw(I: Inst, j: u32) {
    let t: u32 = I.ty;
    let n = M.types[t].store;
    let bits = bits_of(t);
    let k: u32 = I.sub;
    let ord = (I.flags & IF_ORD_MASK) >> IF_ORD_SHIFT;
    let w64 = n == 8;
    if n == 16 {
        b_lower_rmw128(I, j);
        return;
    }
    if k == RMW_XCHG || k == RMW_ADD || k == RMW_SUB || k == RMW_AND || k == RMW_OR || k == RMW_XOR {
        if cls_of(t) == C_FP {
            b_vr(I.b, AV0);
            if w64 { a_fmov_to_gp(true, AX0, AV0); } else if n == 4 { a_fmov_to_gp(false, AX0, AV0); } else { a_umov(1, AX0, AV0, 0); }
        } else {
            b_gpr(I.b, AX0);
        }
        b_gpr(I.a, AX1);
        if k == RMW_SUB { a_addsub_rr(AR_SUB, true, AX0, AZR, AX0, 0, 0); }
        if k == RMW_AND { a_logic_rr(AL_ORN, true, AX0, AZR, AX0, 0, 0); }
        let base: const u8[:] = if k == RMW_XCHG { "swp" } else if k == RMW_ADD || k == RMW_SUB { "ldadd" }
                                else if k == RMW_AND { "ldclr" } else if k == RMW_OR { "ldset" } else { "ldeor" };
        b_helper(base, n, ord);
        a_after_call();
        if cls_of(t) == C_FP {
            if w64 { a_fmov_from_gp(true, AV0, AX0); } else { a_fmov_from_gp(false, AV0, AX0); }
            b_set(j, AV0, false);
            return;
        }
        if bits < 32 { a_zext(AX0, bits); }
        b_set(j, AX0, false);
        return;
    }
    // LL/SC loop: x9 = pointer, x1 = operand, x0 = old, x2 = new, w3 = status
    b_gpr(I.a, AX9);
    let fp = cls_of(t) == C_FP;
    if fp { b_vr(I.b, AV0 + 1); } else { b_gpr(I.b, AX1); }
    let s = a_log2(n);
    let top = here();
    b_ldx(ord, s, AX0, AX9);
    if fp {
        let ft = a_ft(t);
        if ft == 3 {
            // half: in float
            a_fmov_from_gp(false, AV0, AX0);
            a_fp1(3, AF1_CVT_S, AV0, AV0);
            a_fp1(3, AF1_CVT_S, AV0 + 2, AV0 + 1);
            a_fp2(0, if k == RMW_FADD { AF2_FADD } else { AF2_FSUB }, AV0, AV0, AV0 + 2);
            a_fp1(0, AF1_CVT_H, AV0, AV0);
            a_umov(1, AX2, AV0, 0);
        } else {
            a_fmov_from_gp(w64, AV0, AX0);
            a_fp2(ft, if k == RMW_FADD { AF2_FADD } else { AF2_FSUB }, AV0, AV0, AV0 + 1);
            a_fmov_to_gp(w64, AX2, AV0);
        }
    } else if k == RMW_NAND {
        a_logic_rr(AL_AND, true, AX2, AX0, AX1, 0, 0);
        a_logic_rr(AL_ORN, true, AX2, AZR, AX2, 0, 0);
    } else {
        // min / max: on extended copies
        let sgn = k == RMW_MAX || k == RMW_MIN;
        if sgn {
            a_sext(AX4, AX0, bits);
            a_sext(AX5, AX1, bits);
        } else {
            a_mov_rr(true, AX4, AX0);
            a_mov_rr(true, AX5, AX1);
            a_zext(AX5, bits);
        }
        a_cmp_rr(true, AX4, AX5);
        let cc: u32 = if k == RMW_MAX { AC_GT } else if k == RMW_MIN { AC_LT } else if k == RMW_UMAX { AC_HI } else { AC_LO };
        a_csel(true, AX2, AX0, AX1, cc);
    }
    b_stx(ord, s, AX3, AX2, AX9);
    a_cbz_raw(false, true, AX3);
    a_patch_branch(here() - 4, top, AF_B19);
    if fp {
        a_fmov_from_gp(w64, AV0, AX0);
        b_set(j, AV0, false);
        return;
    }
    b_set(j, AX0, false);
}
// 16-byte read-modify-write: ldxp/stxp loop on x1:x0 (old) and x5:x4 (new).
fn b_lower_rmw128(I: Inst, j: u32) {
    let t: u32 = I.ty;
    let bits = bits_of(t);
    let k: u32 = I.sub;
    let ord = (I.flags & IF_ORD_MASK) >> IF_ORD_SHIFT;
    b_gpr(I.a, AX9);
    b_int2(I.b, AX2, AX3);
    let top = here();
    if ord >= 4 && ord != 5 { a_ldaxp(AX0, AX1, AX9); } else { a_ldxp(AX0, AX1, AX9); }
    if k == RMW_XCHG {
        a_mov_rr(true, AX4, AX2);
        a_mov_rr(true, AX5, AX3);
    } else if k == RMW_ADD {
        a_addsub_rr(AR_ADDS, true, AX4, AX0, AX2, 0, 0);
        a_adc(true, AX5, AX1, AX3);
    } else if k == RMW_SUB {
        a_addsub_rr(AR_SUBS, true, AX4, AX0, AX2, 0, 0);
        a_sbc(true, AX5, AX1, AX3);
    } else if k == RMW_AND || k == RMW_NAND {
        a_logic_rr(AL_AND, true, AX4, AX0, AX2, 0, 0);
        a_logic_rr(AL_AND, true, AX5, AX1, AX3, 0, 0);
        if k == RMW_NAND {
            a_logic_rr(AL_ORN, true, AX4, AZR, AX4, 0, 0);
            a_logic_rr(AL_ORN, true, AX5, AZR, AX5, 0, 0);
        }
    } else if k == RMW_OR {
        a_logic_rr(AL_ORR, true, AX4, AX0, AX2, 0, 0);
        a_logic_rr(AL_ORR, true, AX5, AX1, AX3, 0, 0);
    } else if k == RMW_XOR {
        a_logic_rr(AL_EOR, true, AX4, AX0, AX2, 0, 0);
        a_logic_rr(AL_EOR, true, AX5, AX1, AX3, 0, 0);
    } else {
        // min / max: old < operand (signed or unsigned) over 128 bits
        a_cmp_rr(true, AX0, AX2);
        a_sbcs(true, AZR, AX1, AX3);
        let sgn = k == RMW_MAX || k == RMW_MIN;
        let lt: u32 = if sgn { AC_LT } else { AC_LO };
        // keep old if (max: !(old < v)) (min: old < v)
        let keep: u32 = if k == RMW_MAX || k == RMW_UMAX { lt ^ 1 } else { lt };
        a_csel(true, AX4, AX0, AX2, keep);
        a_csel(true, AX5, AX1, AX3, keep);
    }
    if bits < 128 { a_zext(AX5, bits - 64); }
    if ord >= 5 { a_stlxp(AX6, AX4, AX5, AX9); } else { a_stxp(AX6, AX4, AX5, AX9); }
    a_cbz_raw(false, true, AX6);
    a_patch_branch(here() - 4, top, AF_B19);
    b_set_int2(j, AX0, AX1, bits);
}

// ------------------------------------------------------------ TLS

// The address of thread-local global g in x0: local exec (an executable's own
// variable), initial exec (another module's, in an executable), or a TLS
// descriptor call (shared objects), as clang emits them.
fn b_lower_tlsaddr(I: Inst, j: u32) {
    let g = I.a;
    let G = M.globals[g];
    let pie = M.header[0].flags & MF_PIE != 0;
    let sym = g_sym[g];
    if pie && G.flags & GF_DEFINED != 0 {
        a_mrs_tpidr(AX0);
        a_rela(sym, R_AARCH64_TLSLE_ADD_TPREL_HI12, 0);
        a_addsub_imm(AI_ADD, true, AX0, AX0, 0, true);
        a_rela(sym, R_AARCH64_TLSLE_ADD_TPREL_LO12_NC, 0);
        a_addsub_imm(AI_ADD, true, AX0, AX0, 0, false);
    } else if pie {
        a_rela(sym, R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21, 0);
        a_adrp_raw(AX0);
        a_rela(sym, R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC, 0);
        a_ls_uimm(LS_LDR, 3, AX0, AX0, 0);
        a_mrs_tpidr(AX1);
        a_addsub_rr(AR_ADD, true, AX0, AX1, AX0, 0, 0);
    } else {
        a_rela(sym, R_AARCH64_TLSDESC_ADR_PAGE21, 0);
        a_adrp_raw(AX0);
        a_rela(sym, R_AARCH64_TLSDESC_LD64_LO12, 0);
        a_ls_uimm(LS_LDR, 3, AX1, AX0, 0);
        a_rela(sym, R_AARCH64_TLSDESC_ADD_LO12, 0);
        a_addsub_imm(AI_ADD, true, AX0, AX0, 0, false);
        a_rela(sym, R_AARCH64_TLSDESC_CALL, 0);
        a_blr(AX1);
        a_mrs_tpidr(AX1);
        a_addsub_rr(AR_ADD, true, AX0, AX1, AX0, 0, 0);
    }
    b_set(j, AX0, false);
}

// ------------------------------------------------------------ setjmp / longjmp

// __builtin_setjmp: word 1 of the buffer gets the resume address (the IR
// stored the frame address in word 0 and the stack pointer in word 2).
fn b_lower_setjmp(I: Inst, j: u32) {
    b_gpr(I.a, AX1);
    let ro = b_res(j);
    let p = here();
    a_adr_raw(AX16);
    a_ls(LS_STR, 3, AX16, AX1, 8);
    a_ls(LS_STR, 2, AZR, AFP, ro);
    let done = a_fwd_b();
    a_patch_branch(p, here(), AF_ADR);
    // resume point: x29 and sp are this frame's again
    a_movz(false, AX16, 1, 0);
    a_ls(LS_STR, 2, AX16, AFP, ro);
    a_here(done);
}
fn b_lower_longjmp(I: Inst) {
    b_gpr(I.a, AX1);
    a_ls(LS_LDR, 3, AFP, AX1, 0);
    a_ls(LS_LDR, 3, AX17, AX1, 8);
    a_ls(LS_LDR, 3, AX16, AX1, 16);
    a_mov_sp(ASP, AX16);
    a_br(AX17);
}

// ------------------------------------------------------------ inline assembly

fn b_lower_asm(I: Inst, j: u32) {
    let A = M.asms[I.a];
    let ins = A.ops;
    for q in 0..A.n_in {
        let v = M.opnds[ins + 2 * q];
        let r = M.opnds[ins + 2 * q + 1];
        if r < ASMREG_V0 { continue; }
        let t = type_of(v);
        if a_inv(arc(t)) { b_vr(v, r); }
        else {
            let b, o = a_val_mem(v, AX16);
            if is_val(v) { a_note(vid(v)); }
            a_ls(LS_FLDR, a_log2(M.types[t].store), r, b, o);
        }
    }
    for q in 0..A.n_in {
        let v = M.opnds[ins + 2 * q];
        let r = M.opnds[ins + 2 * q + 1];
        if r >= ASMREG_V0 { continue; }
        let t = type_of(v);
        if arc(t) == ARC_GPR { b_gpr(v, r); }
        else if a_inv(arc(t)) {
            b_vr(v, AV31);
            if M.types[t].store == 8 { a_fmov_to_gp(true, r, AV31); } else { a_fmov_to_gp(false, r, AV31); }
        } else {
            let b, o = a_val_mem(v, AX16);
            if is_val(v) { a_note(vid(v)); }
            a_load_n(r, b, o, if M.types[t].store > 8 { 8 } else { M.types[t].store });
        }
    }
    code.append(M.data[A.code..A.code + A.code_len]);
    if I.ty == GIR_T_VOID { return; }
    let outs = ins + 2 * A.n_in;
    let single = A.n_out == 1 && cls_of(I.ty) != C_MEM;
    if single {
        let r = M.opnds[outs];
        let c = arc(I.ty);
        if r < ASMREG_V0 && c == ARC_GPR {
            a_zext(r, bits_of(I.ty));
            b_set(j, r, false);
            return;
        }
        if r >= ASMREG_V0 && a_inv(c) {
            b_set(j, r, false);
            return;
        }
    }
    let ro = b_res(j);
    for q in 0..A.n_out {
        let r = M.opnds[outs + 2 * q];
        let off = M.opnds[outs + 2 * q + 1];
        let ft = if single { I.ty } else { M.opnds[M.types[I.ty].elems + 2 * q] };
        let n = M.types[ft].store;
        if r < ASMREG_V0 { a_store_n(r, AFP, ro + off as i64, if n > 8 { 8 } else { n }); }
        else { a_ls(LS_FSTR, a_log2(n), r, AFP, ro + off as i64); }
    }
    b_vec_result(j);
}

// The landing pad's {ptr, i32}: x0 and w1 as the personality routine left them.
fn b_lower_landingpad(I: Inst, j: u32) {
    let ro = b_res(j);
    a_ls(LS_STR, 3, AX0, AFP, ro);
    a_ls(LS_STR, 2, AX1, AFP, ro + 8);
}
