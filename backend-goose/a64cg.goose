// AArch64 code generation (milestone F1): the pre-pass, the dispatch of
// instructions to their lowerings, PHIs, terminators (switch tables in the
// code), the frame, prologue and epilogue (with their CFI), and the
// placement of functions. The structure is the x86-64 back-end's
// (cg.goose, DESIGN.md §2): one pass per function after a liveness
// pre-pass, the prologue generated after the body (when the frame size and
// the callee-saved registers in use are known) and placed before it.
//
// Frame (x29 = sp after the prologue, at the bottom of the fixed frame):
//
//   x29 + F + ...   incoming stack arguments (F = frame size, 16-aligned)
//   x29 + 16 ...    callee-saved registers in use (x19.., d8..), then the va
//                   save areas, allocas, homes, spill slots, PHI temps
//   x29 + 8         saved x30
//   x29             saved x29
//   below x29       dynamic allocas and outgoing argument areas (sp moves)

// ------------------------------------------------------------ pre-pass

// Operand masks (U_*) of opcode op.
fn a_op_uses(op: u32) -> u32 {
    if op < GIR_NOPS { return OP_USES[op]; }
    if op == GIR_FMA { return U_A | U_B | U_C; }
    return U_A | U_B | U_C;
}
// How instruction I is lowered on AArch64: K_A (in registers), K_CALL (a
// call, or a library call: clobbers the caller-saved registers), K_B (in
// memory, a64mem.goose), K_ALL (clobbers every register).
fn a_kind(I: Inst) -> u32 {
    let op: u32 = I.op;
    if op == GIR_CALL { return K_CALL; }
    if op == GIR_ASM || op == GIR_SJLJ_SETJMP { return K_ALL; }
    if op <= GIR_UNREACHABLE || op == GIR_INDIRECTBR || op == GIR_PHI || op == GIR_ALLOCA || op == GIR_GEP { return K_A; }
    if op == GIR_TRAP || op == GIR_DEBUGTRAP || op == GIR_FENCE || op == GIR_FRAMEADDR || op == GIR_RETADDR { return K_A; }
    if op == GIR_DYNALLOCA || op == GIR_STACKSAVE || op == GIR_STACKRESTORE || op == GIR_VASTART || op == GIR_BLOCKADDR { return K_A; }
    if op == GIR_MEMCPY || op == GIR_MEMSET { return K_A; }
    if op == GIR_LANDINGPAD || op == GIR_TLSADDR || op == GIR_SJLJ_LONGJMP || op == GIR_X86 { return K_B; }
    if op == GIR_CMPXCHG || op == GIR_ATOMICRMW { return K_CALL; }
    if op == GIR_OVF || op == GIR_EXTRACTVALUE || op == GIR_INSERTVALUE || op == GIR_SHUFFLE || op == GIR_ISFPCLASS { return K_B; }
    if op == GIR_A64 { return K_B; }
    if op == GIR_EXTRACTELT { return a_kind_ext(I); }
    // the type that decides
    var t: u32 = I.ty;
    if op == GIR_ICMP || op == GIR_FCMP || op == GIR_STORE || op == GIR_EXTRACTELT || op == GIR_SCMP || op == GIR_UCMP { t = I.aux; }
    let c = arc(t);
    if op == GIR_LOAD || op == GIR_STORE {
        if c == ARC_MEM { return K_B; }
        if c == ARC_GPR && !exact_width(bits_of(t)) { return K_B; }
        if I.flags & IF_ORD_MASK != 0 && M.types[t].store == 16 { return K_B; }
        return K_A;
    }
    if t == GIR_T_F128 {
        if op == GIR_FADD || op == GIR_FSUB || op == GIR_FMUL || op == GIR_FDIV || op == GIR_FCMP || op == GIR_FSQRT { return K_CALL; }
        if op >= GIR_FPEXT && op <= GIR_UITOFP { return K_CALL; }
        if op == GIR_SELECT || op == GIR_BITCAST { return K_A; }
        return K_B;
    }
    if op >= GIR_FPEXT && op <= GIR_UITOFP && I.aux == GIR_T_F128 { return K_CALL; }
    if c == ARC_MEM { return K_B; }
    if c == ARC_VR {
        // vectors in a register: the lane-by-lane code for what has no NEON lowering here
        if op == GIR_SELECT && cls_of(type_of(I.a)) == C_VEC { return K_B; }
        if op == GIR_SELECT || op == GIR_LOAD || op == GIR_STORE { return K_A; }
        if op == GIR_BITCAST { return if arc(I.aux) == ARC_MEM { K_B } else { K_A }; }
        if op == GIR_FMA { return K_A; }
        return K_B;
    }
    if op >= GIR_ZEXT && op <= GIR_BITCAST || op >= GIR_FPEXT && op <= GIR_UITOFP {
        let sc = arc(I.aux);
        if sc == ARC_MEM { return K_B; }
        if sc == ARC_VR && I.aux != GIR_T_F128 && op != GIR_BITCAST { return K_B; }
        return K_A;
    }
    if op == GIR_SELECT && cls_of(type_of(I.a)) == C_VEC { return K_B; }
    if op == GIR_INSERTELT { return K_B; }
    return K_A;
}
// extractelement with a constant lane of a vector in a register: K_A.
fn a_kind_ext(I: Inst) -> u32 {
    let isc, c = a_cint(I.b);
    if isc && arc(I.aux) == ARC_VR && c < M.types[I.aux].n as u64 && arc(I.ty) != ARC_MEM { return K_A; }
    return K_B;
}

// Register hints: a value used by a return or as a call argument is
// computed in that register if it is free.
fn a_hint(v: u32, r: u32) {
    if gir_kind(v) != GIR_V_INST { return; }
    let u = gir_idx(v) - f_first_inst;
    if u >= f_nins { return; }
    vi[u].hint = r as! u8;
}
fn a_call_hints(I: Inst) {
    var gp: u32 = 0;
    var fp: u32 = 0;
    for k in 0..I.c {
        let v = M.opnds[I.b + 2 * k];
        if M.opnds[I.b + 2 * k + 1] != 0 { return; }
        let c = arc(type_of(v));
        if c == ARC_GPR {
            if gp == 8 { return; }
            a_hint(v, gp);
            gp++;
        } else if a_inv(c) {
            if fp == 8 { return; }
            a_hint(v, AV0 + fp);
            fp++;
        } else {
            return;
        }
    }
}

var a_ncs_v: u32 = 0;     // values spanning a call that live in V registers
var a_ncs_g: u32 = 0;
fn a_prepass(insts: const Inst[:], blocks: const Block[:]) {
    pp_epoch++;
    pp_ncs = 0;
    a_ncs_v = 0;
    a_ncs_g = 0;
    f_call = false;
    f_rsp = false;
    f_asm = false;
    let nv: i64 = f_nins as i64 + f_nargs;
    assert(vi.len >= nv);
    let z = VInfo { reg: NOREG, st: 0, home: H_NONE, nuse: 0, ncl: 0, kind: 0, hint: NOREG, nev: 0, last: 0, off: 0 };
    for q in 0..nv { vi[q] = z; }
    let E = blocks[0];
    for gi in E.first_inst..E.first_inst + E.n_inst {
        if M.insts[gi].op == GIR_ALLOCA { vi[gi - f_first_inst].home = H_ALLOCA; }
    }
    for B, b in blocks {
        let lo = B.first_inst - f_first_inst;
        let hi = lo + B.n_inst;
        var ncl: u32 = 0;
        var mw: u32 = 0;
        var j = lo;
        while j < hi {
            let I = insts[j];
            let op: u32 = I.op;
            let k2 = a_kind(I);
            let nodef = k2 == K_B || k2 == K_ALL;
            let m: u32 = a_op_uses(op);
            if m & U_A != 0 { pp_use(I.a, j, lo, ncl, mw, nodef); }
            if m & U_B != 0 { pp_use(I.b, j, lo, ncl, mw, nodef); }
            if m & U_C != 0 { pp_use(I.c, j, lo, ncl, mw, nodef); }
            if m >= U_GEP { pp_runs(I, m, j, lo, ncl, mw, nodef); }
            if op == GIR_RET && I.a != GIR_NONE {
                let c = arc(type_of(I.a));
                if c == ARC_GPR { a_hint(I.a, AX0); } else if a_inv(c) { a_hint(I.a, AV0); }
            } else if op == GIR_CALL { a_call_hints(I); }
            if op <= GIR_SWITCH || op == GIR_INDIRECTBR { pp_term(I, op, b as! u32, j, lo, ncl, mw); }
            if op == GIR_STORE || op == GIR_CALL || op == GIR_MEMCPY || op == GIR_MEMSET || k2 != K_A { mw = j + 1; }
            if k2 != K_A {
                ncl++;
                if k2 == K_CALL || k2 == K_B { f_call = true; }
                if k2 == K_ALL { f_asm = true; }
            }
            if op == GIR_DYNALLOCA || op == GIR_STACKRESTORE { f_rsp = true; }
            vi[j].kind = k2 as! u8;
            if I.ty != GIR_T_VOID {
                vi[j].last = j;
                vi[j].ncl = if ncl > 255 { 255 } else { ncl as! u8 };
                if op == GIR_PHI {
                    vi[j].st |= ST_PHI;
                    t_off[j] = 0;
                }
            }
            j++;
        }
    }
    // values spanning a call, by class (the callee-saved budget)
    for q in 0..nv {
        if vi[q].st & (ST_CS | ST_GLOB) != ST_CS { continue; }
        let t = vtype(q as! u32);
        if a_inv(arc(t)) { a_ncs_v++; } else { a_ncs_g++; }
    }
}

// ------------------------------------------------------------ PHIs

fn a_has_phi(b: u32) -> bool {
    let B = M.blocks[f_first_block + b];
    return B.n_inst != 0 && M.insts[B.first_inst].op == GIR_PHI;
}
// The home (or temp slot) offset a PHI's incoming value is written to.
fn a_phi_dst(b: u32, j: u32) -> i64 {
    if b_tag[b] == pp_epoch {
        if t_off[j] == 0 { t_off[j] = a_new_slot(a_slot_size(M.insts[f_first_inst + j].ty)); }
        return t_off[j] as i64;
    }
    return a_home_off(j) as i64;
}
// Writes value v (type t) to [x29 + doff] without changing the register state
// (x16, x17 and v31 only).
fn a_phi_copy(doff: i64, v: u32, t: u32) {
    let c = arc(t);
    if c == ARC_GPR {
        if is_val(v) {
            let r: u32 = vi[vid(v)].reg;
            if r < 32 {
                a_store_t(r, AFP, doff, t);
                return;
            }
        }
        if gir_kind(v) == GIR_V_CONST && a_const_bits(gir_idx(v)) == 0 {
            a_store_t(AZR, AFP, doff, t);
            return;
        }
        a_mat_gpr(v, AX17);
        a_store_t(AX17, AFP, doff, t);
        return;
    }
    if a_inv(c) {
        if is_val(v) {
            let r: u32 = vi[vid(v)].reg;
            if r < 64 && r >= 32 {
                a_store_t(r, AFP, doff, t);
                return;
            }
        }
        a_mat_v(v, AV31);
        a_store_t(AV31, AFP, doff, t);
        return;
    }
    let n = a_slot_size(t) as! u32;
    let st = M.types[t].store;
    let cn: u32 = if gir_kind(v) == GIR_V_CONST && st < n { st } else { n };
    if gir_kind(v) == GIR_V_CONST {
        a_const_addr(AX17, gir_idx(v));
        a_copy(AFP, doff, AX17, 0, cn);
        return;
    }
    let id = vid(v);
    let r: u32 = vi[id].reg;
    if r < 64 && vi[id].st & ST_MEM == 0 { a_store_home(id, r); }
    a_copy(AFP, doff, AFP, a_home_off(id) as i64, cn);
}
// Edge from -> to: each PHI's incoming value.
fn a_phi_moves(from: u32, to: u32) {
    if rg_on {
        a_phi_moves_rg(from, to);
        return;
    }
    let B = M.blocks[f_first_block + to];
    for k in B.first_inst..B.first_inst + B.n_inst {
        let I = M.insts[k];
        if I.op != GIR_PHI { break; }
        let j = k - f_first_inst;
        if vi[j].nuse == 0 { continue; }
        for p in 0..I.c {
            if M.opnds[I.b + 2 * p + 1] != from { continue; }
            a_phi_copy(a_phi_dst(to, j), M.opnds[I.b + 2 * p], I.ty);
            break;
        }
    }
}
fn a_lower_phi(I: Inst, j: u32, b: u32) {
    if vi[j].nuse == 0 || vi[j].st & ST_PIN != 0 { return; }   // (a pinned PHI is in its register)
    let h = a_home_off(j) as i64;
    if b_tag[b] == pp_epoch {
        if t_off[j] == 0 { t_off[j] = a_new_slot(a_slot_size(I.ty)); }
        a_copy(AFP, h, AFP, t_off[j] as i64, a_slot_size(I.ty) as! u32);
    }
    vi[j].st |= ST_MEM;
    vi[j].reg = NOREG;
}

// ------------------------------------------------------------ terminators

// Branches to `target` when the pending flags say `when`.
fn a_bflags(when: bool, target: u32) {
    let cc = a_fcc;
    let cc2 = a_fcc2;
    if a_fcomb == 0 {
        a_bcond_block(if when { cc } else { cc ^ 1 }, target);
    } else {
        // cc || cc2
        if when {
            a_bcond_block(cc, target);
            a_bcond_block(cc2, target);
        } else {
            let p = a_fwd_bcond(cc);
            a_bcond_block(cc2 ^ 1, target);
            a_here(p);
        }
    }
}
// The same as a forward branch inside the code: positions to patch.
fn a_bflags_fwd(when: bool) -> u32, u32 {
    let cc = a_fcc;
    let cc2 = a_fcc2;
    if a_fcomb == 0 { return a_fwd_bcond(if when { cc } else { cc ^ 1 }), GIR_NONE; }
    if when { return a_fwd_bcond(cc), a_fwd_bcond(cc2); }
    let p = a_fwd_bcond(cc);
    let q = a_fwd_bcond(cc2 ^ 1);
    a_here(p);
    return q, GIR_NONE;
}
fn a_lower_condbr(I: Inst, cur: u32, next: u32) {
    let fused = a_flags_id != RV_NONE && I.a == inst_ref(a_flags_id);
    if !fused {
        let r = a_gpr(I.a, false);
        a_logic_imm(ALI_ANDS, false, AZR, r, a_bitmask(1, false));
        a_fcc = AC_NE;
        a_fcomb = 0;
    }
    a_flags_id = RV_NONE;
    let pb = a_edge_phi(cur, I.b);
    let pc = a_edge_phi(cur, I.c);
    if pb != pc {
        if pc {
            a_bflags(true, I.b);
            a_phi_moves(cur, I.c);
            if I.c != next { a_b_block(I.c); }
        } else {
            a_bflags(false, I.c);
            a_phi_moves(cur, I.b);
            if I.b != next { a_b_block(I.b); }
        }
    } else if pb {
        let p, q = a_bflags_fwd(false);
        a_phi_moves(cur, I.b);
        a_b_block(I.b);
        a_here(p);
        if q != GIR_NONE { a_here(q); }
        a_phi_moves(cur, I.c);
        if I.c != next { a_b_block(I.c); }
    } else if I.b == next {
        a_bflags(false, I.c);
    } else {
        a_bflags(true, I.b);
        if I.c != next { a_b_block(I.c); }
    }
}

// Jump tables: entries are 32-bit offsets from the table, which sits in the
// code after the br (between $d and $x mapping symbols).
struct AJt { pos: u32, blk: u32, base: u32 }
var a_jt: AJt[>..] = [];
var a_maps: MapSym[>..] = [];      // the current function's mapping symbols (body-relative)

fn a_switch_table(I: Inst, cur: u32, r: u32, bits: u32) -> bool {
    let nc: u32 = I.c;
    if nc < 4 { return false; }
    var lo: i64 = case_val(I, 0, bits);
    var hi: i64 = lo;
    for k in 1..nc {
        let x = case_val(I, k, bits);
        if x < lo { lo = x; }
        if x > hi { hi = x; }
    }
    let span: u64 = (hi as! u64) - (lo as! u64);
    if span >= 0x40000000 || (span + 1) * 2 > (nc as u64) * 5 { return false; }
    let n: u32 = span as! u32 + 1;
    // x16 = sext(x) - lo
    a_sext(AX16, r, bits);
    if lo != 0 {
        a_mov_imm(AX17, lo as! u64, true);
        a_addsub_rr(AR_SUB, true, AX16, AX16, AX17, 0, 0);
    }
    a_mov_imm(AX17, span, true);
    a_cmp_rr(true, AX16, AX17);
    let d = M.opnds[I.b];
    let dphi = a_has_phi(d);
    var dpos: u32 = GIR_NONE;
    if dphi { dpos = a_fwd_bcond(AC_HI); } else { a_bcond_block(AC_HI, d); }
    let ap = here();
    a_adr_raw(AX17);
    a_ls_reg(LS_LDRSX, 2, AX16, AX17, AX16, 3, true);   // ldrsw x16, [x17, x16, lsl #2]
    a_addsub_rr(AR_ADD, true, AX17, AX17, AX16, 0, 0);
    a_br(AX17);
    let base = here();
    a_patch_branch(ap, base, AF_ADR);
    a_maps.push(MapSym { sec: 0, off: base, data: true });
    if jt_case.len < n { jt_case.resize(n, 0); }
    for e in 0..n { jt_case[e] = 0; }
    for k in 0..nc { jt_case[(case_val(I, k, bits) - lo) as! u32] = k + 1; }
    for e in 0..n { a4(0); }
    a_maps.push(MapSym { sec: 0, off: here(), data: false });
    // stubs for the edges into blocks with PHIs
    jt_stub_blk.clear();
    jt_stub_pos.clear();
    for e in 0..n + 1 {
        var tb = d;
        if e < n && jt_case[e] != 0 { tb = M.opnds[I.b + 2 * jt_case[e]]; }
        if !a_has_phi(tb) { continue; }
        var seen = false;
        for q in jt_stub_blk { if q == tb { seen = true; } }
        if seen { continue; }
        jt_stub_blk.push(tb);
        jt_stub_pos.push(here());
        a_phi_moves(cur, tb);
        a_b_block(tb);
    }
    if dphi { a_patch_branch(dpos, stub_pos(d), AF_B19); }
    for e in 0..n {
        var tb = d;
        if jt_case[e] != 0 { tb = M.opnds[I.b + 2 * jt_case[e]]; }
        let p = base + 4 * e;
        if a_has_phi(tb) { patch4(p, stub_pos(tb) - base); }
        else if tb <= cur_blk { patch4(p, block_off[tb] - base); }
        else { a_jt.push(AJt { pos: p, blk: tb, base: base }); }
    }
    return true;
}
fn a_lower_switch(I: Inst, cur: u32, next: u32) {
    let t: u32 = I.aux;
    let wide = cls_of(t) == C_INT2;
    let bits = bits_of(t);
    var r: u32 = 0;
    var rhi: u32 = 0;
    if wide {
        r = a_temp();
        rhi = a_temp();
        if gir_kind(I.a) == GIR_V_CONST {
            let c = M.consts[gir_idx(I.a)];
            a_mov_imm(r, c.lo, true);
            a_mov_imm(rhi, c.hi, true);
        } else {
            let b, o = a_val_mem(I.a, AX16);
            a_note(vid(I.a));
            a_ls(LS_LDR, 3, r, b, o);
            a_ls(LS_LDR, 3, rhi, b, o + 8);
            if bits < 128 { a_zext(rhi, bits - 64); }
        }
    } else {
        r = a_gpr(I.a, true);
        if a_switch_table(I, cur, r, bits) { return; }
    }
    for k in 0..I.c {
        let c = M.consts[gir_idx(M.opnds[I.b + 1 + 2 * k])];
        let tb = M.opnds[I.b + 2 + 2 * k];
        if wide {
            a_mov_imm(AX16, c.lo, true);
            a_mov_imm(AX17, c.hi, true);
            a_cmp_rr(true, r, AX16);
            a_ccmp(true, rhi, AX17, 0, AC_EQ);
        } else {
            let w64 = bits > 32;
            let ok, imm, sh, neg = a_addimm(c.lo as! i64);
            if ok && !neg {
                a_addsub_imm(AI_SUBS, w64, AZR, r, imm, sh);
            } else {
                a_mov_imm(AX16, c.lo, w64);
                a_cmp_rr(w64, r, AX16);
            }
        }
        if a_has_phi(tb) {
            let p = a_fwd_bcond(AC_NE);
            a_phi_moves(cur, tb);
            a_b_block(tb);
            a_here(p);
        } else {
            a_bcond_block(AC_EQ, tb);
        }
    }
    let d = M.opnds[I.b];
    a_phi_moves(cur, d);
    if d != next { a_b_block(d); }
}
fn a_lower_ret(I: Inst, j: u32) {
    if I.a != GIR_NONE {
        let t = type_of(I.a);
        a_ret_value(I.a, t);
    }
    if j + 1 != f_nins { a_b_block(cur_nblocks); }
}

// ------------------------------------------------------------ instructions

fn a_gen_inst(gi: u32, cur: u32) {
    let I = M.insts[gi];
    let j = gi - f_first_inst;
    let next = cur + 1;
    cur_pos = j;
    let k: u32 = vi[j].kind;
    let op: u32 = I.op;
    let pin = rg_on && vi[j].st & ST_PIN != 0 && op != GIR_PHI;
    if pin { a_rg_def_start(j); }
    a_gen_inst2(I, j, k, op, cur, next);
    if pin { a_rg_def_end(j); }
    a_end_inst();
}
fn a_gen_inst2(I: Inst, j: u32, k: u32, op: u32, cur: u32, next: u32) {
    if k == K_A {
        match op {
            GIR_LOAD => a_lower_load(I, j),
            GIR_STORE => a_lower_store(I),
            GIR_GEP => a_lower_gep(I, j),
            GIR_ICMP => a_lower_icmp(I, j),
            GIR_RET => a_lower_ret(I, j),
            GIR_BR => {
                if a_edge_phi(cur, I.a) { a_phi_moves(cur, I.a); }
                if I.a != next { a_b_block(I.a); }
            },
            GIR_CONDBR => a_lower_condbr(I, cur, next),
            GIR_SWITCH => a_lower_switch(I, cur, next),
            GIR_INDIRECTBR => {
                let r = a_gpr(I.a, false);
                for q in 0..I.c {
                    let tb = M.opnds[I.b + q];
                    var seen = false;
                    for p in 0..q { if M.opnds[I.b + p] == tb { seen = true; } }
                    if !seen { a_phi_moves(cur, tb); }
                }
                a_br(r);
            },
            GIR_UNREACHABLE, GIR_TRAP => a_brk(1),
            GIR_DEBUGTRAP => a_brk(0xF000),
            GIR_ADD, GIR_SUB, GIR_MUL, GIR_SDIV, GIR_UDIV, GIR_SREM, GIR_UREM,
            GIR_AND, GIR_OR, GIR_XOR, GIR_SHL, GIR_LSHR, GIR_ASHR => a_lower_binop(I, j),
            GIR_FCMP => a_lower_fcmp(I, j),
            GIR_FADD, GIR_FSUB, GIR_FMUL, GIR_FDIV => a_lower_fbin(I, j),
            GIR_FMA => a_lower_fma(I, j),
            GIR_FNEG, GIR_FABS, GIR_FSQRT, GIR_COPYSIGN => a_lower_funary(I, j),
            GIR_SELECT => a_lower_select(I, j),
            GIR_ZEXT, GIR_SEXT, GIR_TRUNC, GIR_PTRTOINT, GIR_INTTOPTR, GIR_BITCAST,
            GIR_FPEXT, GIR_FPTRUNC, GIR_FPTOSI, GIR_FPTOUI, GIR_SITOFP, GIR_UITOFP => a_lower_cast(I, j),
            GIR_ALLOCA => {},
            GIR_PHI => a_lower_phi(I, j, cur),
            GIR_MEMCPY, GIR_MEMSET => a_lower_memcpy(I),
            GIR_CTLZ, GIR_CTTZ, GIR_CTPOP, GIR_BSWAP, GIR_BITREVERSE => a_lower_bitop(I, j),
            GIR_FSHL, GIR_FSHR => a_lower_funnel(I, j),
            GIR_SCMP, GIR_UCMP => a_lower_scmp(I, j),
            GIR_EXTRACTELT => a_lower_extractelt(I, j),
            GIR_DYNALLOCA => a_lower_dynalloca(I, j),
            GIR_STACKSAVE => {
                let rd = a_def(j);
                a_mov_sp(rd, ASP);
                a_set(j, rd, false);
            },
            GIR_STACKRESTORE => {
                let r = a_gpr(I.a, false);
                a_mov_sp(ASP, r);
            },
            GIR_FRAMEADDR, GIR_RETADDR => a_lower_frameaddr(I, j),
            GIR_FENCE => a_lower_fence(I),
            GIR_VASTART => a_lower_vastart(I),
            GIR_BLOCKADDR => a_lower_blockaddr(I, j),
            _ => a_brk(1),
        }
        return;
    }
    if k == K_CALL && op == GIR_CALL {
        if I.flags & IF_INVOKE != 0 { call_lp = M.opnds[I.b + 2 * I.c]; }
        a_lower_call(I, j);
        call_lp = GIR_NONE;
        return;
    }
    b_begin(k == K_ALL);
    match op {
        GIR_ADD, GIR_SUB, GIR_MUL, GIR_SDIV, GIR_UDIV, GIR_SREM, GIR_UREM,
        GIR_AND, GIR_OR, GIR_XOR, GIR_SHL, GIR_LSHR, GIR_ASHR => {
            if cls_of(I.ty) == C_INT2 { b_int2_binop(I, j); } else { b_vec_binop(I, j); }
        },
        GIR_ICMP => {
            let t: u32 = I.aux;
            if cls_of(t) == C_VEC { b_vec_cmp(I, j); }
            else {
                b_int2_cmp(I.sub, bits_of(t), I.a, I.b);
                b_set(j, AX0, false);
            }
        },
        GIR_FCMP => {
            if cls_of(I.aux) == C_VEC { b_vec_cmp(I, j); } else { b_f128_cmp(I, j); }
        },
        GIR_FADD, GIR_FSUB, GIR_FMUL, GIR_FDIV => {
            if I.ty == GIR_T_F128 { b_f128_bin(I, j); } else { b_vec_binop(I, j); }
        },
        GIR_FNEG, GIR_FABS, GIR_COPYSIGN => {
            if I.ty == GIR_T_F128 { b_f128_sign(I, j); } else { b_vec_unary(I, j); }
        },
        GIR_FSQRT => {
            if I.ty == GIR_T_F128 { b_f128_sqrt(I, j); } else { b_vec_unary(I, j); }
        },
        GIR_FMA => b_vec_unary(I, j),
        GIR_SELECT => b_lower_select(I, j),
        GIR_ZEXT, GIR_SEXT, GIR_TRUNC, GIR_PTRTOINT, GIR_INTTOPTR, GIR_BITCAST,
        GIR_FPEXT, GIR_FPTRUNC, GIR_FPTOSI, GIR_FPTOUI, GIR_SITOFP, GIR_UITOFP => b_lower_cast(I, j),
        GIR_LOAD => b_lower_load(I, j),
        GIR_STORE => b_lower_store(I),
        GIR_EXTRACTVALUE => b_lower_extractvalue(I, j),
        GIR_INSERTVALUE => b_lower_insertvalue(I, j),
        GIR_EXTRACTELT => b_lower_extractelt(I, j),
        GIR_INSERTELT => b_lower_insertelt(I, j),
        GIR_SHUFFLE => b_lower_shuffle(I, j),
        GIR_OVF => b_lower_ovf(I, j),
        GIR_ISFPCLASS => b_lower_isfpclass(I, j),
        GIR_CMPXCHG => b_lower_cmpxchg(I, j),
        GIR_ATOMICRMW => b_lower_atomicrmw(I, j),
        GIR_TLSADDR => b_lower_tlsaddr(I, j),
        GIR_SJLJ_SETJMP => b_lower_setjmp(I, j),
        GIR_SJLJ_LONGJMP => b_lower_longjmp(I),
        GIR_ASM => b_lower_asm(I, j),
        GIR_LANDINGPAD => b_lower_landingpad(I, j),
        GIR_A64 => b_lower_a64(I, j),
        _ => a_brk(1),
    }
}

// extractelement of a register vector with a constant lane (else the memory path).
fn a_lower_extractelt(I: Inst, j: u32) {
    let vt: u32 = I.aux;
    let isc, c = a_cint(I.b);
    assert(isc && arc(vt) == ARC_VR && c < M.types[vt].n as u64);
    let lt = M.types[vt].elems;
    let s = a_log2(M.types[lt].size);
    let v = a_vr(I.a);
    let rd = a_def(j);
    let idx: u32 = c as! u32;
    if arc(I.ty) == ARC_GPR {
        a_umov(s, rd, v, idx);
    } else {
        // the lane into lane 0 of rd: ins rd.T[0], v.T[idx]
        a_vins_elt(a_imm5(s, 0), idx << s, rd, v);
    }
    a_set(j, rd, false);
}

// blockaddress: adr to a block of this function, else adrp + add against
// the code section (addend patched when that function is placed).
struct ABaddr { rel: u32, gblk: u32, sec: u32 }
var a_baddr: ABaddr[>..] = [];
fn a_lower_blockaddr(I: Inst, j: u32) {
    let rd = a_def(j);
    let fi = M.globals[I.a].func;
    if fi == f_index {
        a_fix.push(AFix { pos: here(), blk: I.b, kind: AF_ADR });
        a_adr_raw(rd);
    } else {
        let sec = global_section(I.a as i64);
        let gb = M.funcs[fi].first_block + I.b;
        a_baddr.push(ABaddr { rel: rela_code.len as! u32, gblk: gb, sec: sec });
        a_rela(sec_sym(sec), R_AARCH64_ADR_PREL_PG_HI21, 0);
        a_adrp_raw(rd);
        a_rela(sec_sym(sec), R_AARCH64_ADD_ABS_LO12_NC, 0);
        a_addsub_imm(AI_ADD, true, rd, rd, 0, false);
    }
    a_set(j, rd, false);
}
fn a_resolve_blockaddrs() {
    for x in a_baddr {
        let a: i64 = blk_code[x.gblk] as i64 - osecs[x.sec].start as i64;
        rela_code[x.rel].addend = a;
        rela_code[x.rel + 1].addend = a;
    }
}

// ------------------------------------------------------------ frame

var a_ncs_save_g: u32 = 0;   // callee-saved GPRs this function may allocate
var a_ncs_save_v: u32 = 0;
var a_cs_off: i64 = 16;      // the save area of the callee-saved registers
var a_epi_frame: i64 = 0;

// The callee-saved registers the prologue saves (in order: x19.., d8..).
fn a_saved_list(out: u32[>..]&) {
    out.clear();
    for r in A_CS_GP { if a_csused & abit(r) != 0 { out.push(r); } }
    for r in A_CS_V { if a_csused & abit(r) != 0 { out.push(r); } }
}
var a_saved: u32[>..] = [];

// Prologue: sub sp / stp x29, x30 / mov x29, sp / callee-saved stores (CFI
// events prologue-relative), then the va save area and argument homes.
fn a_emit_prologue(flags: u32) {
    let base = here();
    let F = a_frame;
    if F <= 504 {
        a_stp_pre(AFP, ALR, ASP, -F);
        a_cfi_pro.push(ACfi { pos: here() - base, kind: AE_CFA_OFF, reg: 0, off: F as! i32 });
    } else {
        if F < 4096 {
            a_addsub_imm(AI_SUB, true, ASP, ASP, F as! u32, false);
        } else if F < (1 << 24) {
            a_addsub_imm(AI_SUB, true, ASP, ASP, (F >> 12) as! u32, true);
            if F & 0xFFF != 0 { a_addsub_imm(AI_SUB, true, ASP, ASP, (F & 0xFFF) as! u32, false); }
        } else {
            a_mov_imm(AX16, F as! u64, true);
            a_addsub_ext(AR_SUB, true, ASP, ASP, AX16, 3, 0);
        }
        a_cfi_pro.push(ACfi { pos: here() - base, kind: AE_CFA_OFF, reg: 0, off: F as! i32 });
        a_ldstp(false, 0, AFP, ALR, ASP, 0);
    }
    let p1 = here() - base;
    a_cfi_pro.push(ACfi { pos: p1, kind: AE_SAVE, reg: AFP, off: (0 - F) as! i32 });
    a_cfi_pro.push(ACfi { pos: p1, kind: AE_SAVE, reg: ALR, off: (8 - F) as! i32 });
    a_mov_sp(AFP, ASP);
    a_cfi_pro.push(ACfi { pos: here() - base, kind: AE_CFA, reg: AFP, off: F as! i32 });
    // callee-saved registers, in pairs
    a_saved_list(a_saved);
    var k: i64 = 0;
    let n = a_saved.len;
    while k < n {
        let r = a_saved[k];
        let off: i64 = a_cs_off + 8 * k;
        if k + 1 < n && (a_saved[k + 1] >= 32) == (r >= 32) {
            let r2 = a_saved[k + 1];
            a_ldstp(false, if r >= 32 { 1 } else { 0 }, r, r2, AFP, off);
            let p = here() - base;
            a_cfi_pro.push(ACfi { pos: p, kind: AE_SAVE, reg: r, off: (off - F) as! i32 });
            a_cfi_pro.push(ACfi { pos: p, kind: AE_SAVE, reg: r2, off: (off + 8 - F) as! i32 });
            k += 2;
        } else {
            if r >= 32 { a_ls(LS_FSTR, 3, r, AFP, off); } else { a_ls(LS_STR, 3, r, AFP, off); }
            a_cfi_pro.push(ACfi { pos: here() - base, kind: AE_SAVE, reg: r, off: (off - F) as! i32 });
            k++;
        }
    }
    if flags & FN_VASTART != 0 {
        pro_va = here() - base;
        a_save_va_regs();
    }
    a_prologue_args();
}
// Epilogue: restore the callee-saved registers, then the frame record, ret.
fn a_emit_epilogue() {
    let F = a_frame;
    a_epi_frame = F;
    if f_rsp { a_mov_sp(ASP, AFP); }
    a_saved_list(a_saved);
    var k: i64 = 0;
    let n = a_saved.len;
    while k < n {
        let r = a_saved[k];
        let off: i64 = a_cs_off + 8 * k;
        if k + 1 < n && (a_saved[k + 1] >= 32) == (r >= 32) {
            let r2 = a_saved[k + 1];
            a_ldstp(true, if r >= 32 { 1 } else { 0 }, r, r2, AFP, off);
            a_cfi_body.push(ACfi { pos: here(), kind: AE_RESTORE, reg: r, off: 0 });
            a_cfi_body.push(ACfi { pos: here(), kind: AE_RESTORE, reg: r2, off: 0 });
            k += 2;
        } else {
            if r >= 32 { a_ls(LS_FLDR, 3, r, AFP, off); } else { a_ls(LS_LDR, 3, r, AFP, off); }
            a_cfi_body.push(ACfi { pos: here(), kind: AE_RESTORE, reg: r, off: 0 });
            k++;
        }
    }
    // the CFA moves to sp (== x29 here) before x29 is reloaded
    a_cfi_body.push(ACfi { pos: here(), kind: AE_CFA, reg: ASP, off: F as! i32 });
    if F <= 504 {
        a_ldp_post(AFP, ALR, ASP, F);
    } else {
        a_ldstp(true, 0, AFP, ALR, ASP, 0);
        a_cfi_body.push(ACfi { pos: here(), kind: AE_RESTORE, reg: AFP, off: 0 });
        a_cfi_body.push(ACfi { pos: here(), kind: AE_RESTORE, reg: ALR, off: 0 });
        a_add_off(ASP, ASP, F);
    }
    a_cfi_body.push(ACfi { pos: here(), kind: AE_CFA_OFF, reg: 0, off: 0 });
    if F <= 504 {
        a_cfi_body.push(ACfi { pos: here(), kind: AE_RESTORE, reg: AFP, off: 0 });
        a_cfi_body.push(ACfi { pos: here(), kind: AE_RESTORE, reg: ALR, off: 0 });
    }
    a_ret();
}

// An upper bound of the function's code size (bytes), to decide whether
// conditional branches may reach (1 MiB) or take the far form.
fn a_size_bound(insts: const Inst[:]) -> u64 {
    var n: u64 = 4096;
    for I in insts {
        let op: u32 = I.op;
        n += 96;
        if op == GIR_MEMCPY || op == GIR_MEMSET { n += 2 * I.c as u64; }
        else if op == GIR_SWITCH || op == GIR_CALL || op == GIR_PHI || op == GIR_INDIRECTBR { n += 64 * I.c as u64; }
        else if op == GIR_ASM { n += M.asms[I.a].code_len as u64 + 64 * (M.asms[I.a].n_in + M.asms[I.a].n_out) as u64; }
        else if op == GIR_SHUFFLE || op == GIR_INSERTVALUE || op == GIR_EXTRACTVALUE || cls_of(I.ty) == C_VEC
                || cls_of(I.ty) == C_MEM {
            n += 32 * M.types[I.ty].size as u64 + 64;
        }
    }
    return n;
}

fn a_gen_function(fi: u32) {
    let f = M.funcs[fi];
    let falign: u32 = (1 as u32) << (f.flags >> FN_ALIGN_SHIFT);
    if falign > osecs[cur_code_sec].align { osecs[cur_code_sec].align = falign; }
    f_first_inst = f.first_inst;
    f_first_block = f.first_block;
    f_args = f.args;
    f_nargs = f.n_args;
    f_index = fi;
    f_sjlj = f.flags & FN_SJLJ != 0;
    f_nins = f.n_inst;
    cur_nblocks = f.n_blocks;
    let insts = M.insts[f.first_inst..f.first_inst + f.n_inst];
    let blocks = M.blocks[f.first_block..f.first_block + f.n_blocks];
    let nv: i64 = f.n_inst as i64 + f.n_args;
    if vi.len < nv {
        vi.resize(nv, VInfo { reg: NOREG, st: 0, home: H_NONE, nuse: 0, ncl: 0, kind: 0, hint: NOREG, nev: 0, last: 0, off: 0 });
    }
    if t_off.len < f.n_inst { t_off.resize(f.n_inst, 0); }
    if b_tag.len < f.n_blocks { b_tag.resize(f.n_blocks, 0); }
    if block_off.len < f.n_blocks + 1 { block_off.resize(f.n_blocks + 1, 0); }
    a_prepass(insts, blocks);
    if dbg_on { dbg_keep_homes(fi); }
    rg_on = false;
    a_nborrow = 0;
    if opt_on && !opt_off("ra") { a_rg_alloc(insts, blocks); }
    f_share = f.flags & (FN_SJLJ | FN_RETURNS_TWICE) == 0;
    // the callee-saved budget: as many as values spanning calls want
    var ng = a_ncs_g;
    var nvr = a_ncs_v;
    if ng > 10 { ng = 10; }
    if nvr > 8 { nvr = 8; }
    if f_sjlj || f_asm {
        ng = 10;
        nvr = 8;
    }
    a_ncs_save_g = ng;
    a_ncs_save_v = nvr;
    var cs: u64 = 0;
    if rg_on {
        // the pinned values' callee-saved registers, then as many more as local values want
        cs = a_rg_cs;
        var tg: i64 = popcount(a_rg_cs & A_GP_CALLEE) + ng;
        var tv: i64 = popcount(a_rg_cs & A_V_CALLEE) + nvr;
        if tg > 10 { tg = 10; }
        if tv > 8 { tv = 8; }
        var q = 0;
        while popcount(cs & A_GP_CALLEE) < tg {
            cs |= abit(A_CS_GP[q]);
            q++;
        }
        q = 0;
        while popcount(cs & A_V_CALLEE) < tv {
            cs |= abit(A_CS_V[q]);
            q++;
        }
        ng = popcount(cs & A_GP_CALLEE) as! u32;
        nvr = popcount(cs & A_V_CALLEE) as! u32;
    } else {
        for q in 0..ng { cs |= abit(A_CS_GP[q]); }
        for q in 0..nvr { cs |= abit(A_CS_V[q]); }
    }
    a_alloc = A_GP_CALLER | A_V_CALLER | cs;
    a_csused = if f_sjlj || f_asm { cs } else { 0 };
    a_func_start();
    eh_func_start();
    a_cfi_pro.clear();
    a_cfi_body.clear();
    b_scr_off = 0;
    a_far = a_size_bound(insts) >= 900000;

    code.clear();
    a_fix.clear();
    a_jt.clear();
    a_maps.clear();
    let rela_start = rela_code.len;
    // the fixed frame: record, callee-saved area, va save areas, allocas
    a_cs_off = 16;
    a_lay = 16 + 8 * (ng + nvr) as i64;
    n_free8 = 0;
    n_free16 = 0;
    if f.flags & FN_VASTART != 0 {
        a_lay = (a_lay + 15) & ~15;
        a_va_gr_off = a_lay;
        a_lay += 64;
        a_va_vr_off = a_lay;
        a_lay += 128;
        a_va_stk_off = a_lay;
        a_lay += 8;
    }
    // allocas: small ones first (they stay in reach of the scaled offsets)
    let E = blocks[0];
    for pass in 2 {
        for gi in E.first_inst..E.first_inst + E.n_inst {
            let I = M.insts[gi];
            if I.op != GIR_ALLOCA { continue; }
            let size: i64 = if I.a != 0 { I.a } else { 1 };
            if (size <= 64) != (pass == 0) { continue; }
            let al: i64 = if I.b != 0 { I.b } else { 1 };
            let j = gi - f_first_inst;
            if al <= 16 {
                a_lay = (a_lay + al - 1) & ~(al - 1);
                vi[j].off = a_lay as! i32;
                vi[j].home = H_ALLOCA;
                a_lay += size;
            } else {
                // over-aligned: aligned at run time from x29 (the frame is 16-aligned only)
                a_lay = (a_lay + 15) & ~15;
                t_off[j] = a_lay as! i32;
                a_lay += size + al;
                a_lay = (a_lay + 7) & ~7;
                vi[j].off = a_lay as! i32;
                vi[j].home = H_PTR;
                vi[j].st |= ST_MEM;
                a_lay += 8;
            }
        }
    }
    a_setup_args();

    for B, b in blocks {
        cur_blk = b as! u32;
        block_off[b] = here();
        if b == 0 { a_entry_state(); } else { a_block_start(); }
        if rg_on {
            a_rg_block_enter(b as! u32);
            if b == 0 { a_rg_entry_moves(); }
        }
        if dbg_on {
            if b == 0 { dbg_func_start(f.dbg); }
            dbg_block_start();
            for k in B.first_inst..B.first_inst + B.n_inst {
                dbg_inst(k);
                a_gen_inst(k, b as! u32);
                dbg_inst_end();
            }
            dbg_block_end();
        } else {
            for k in B.first_inst..B.first_inst + B.n_inst { a_gen_inst(k, b as! u32); }
        }
    }
    a_frame = (a_lay + 15) & ~15;
    cur_blk = f.n_blocks;
    block_off[f.n_blocks] = here();
    if dbg_on { dbg_epilogue(); }
    a_emit_epilogue();
    for x in a_fix {
        let to = block_off[x.blk];
        assert(a_reaches(x.pos, to, x.kind));
        a_patch_branch(x.pos, to, x.kind);
    }
    for x in a_jt { patch4(x.pos, block_off[x.blk] - x.base); }
    let body = here();
    a_emit_prologue(f.flags);
    // over-aligned allocas: their aligned address in their slot
    for I, j in insts {
        if I.op != GIR_ALLOCA || vi[j].home != H_PTR { continue; }
        let al: u64 = I.b;
        a_add_off(AX16, AFP, t_off[j] as i64 + al as i64 - 1);
        a_logic_imm(ALI_AND, true, AX16, AX16, a_bitmask(~(al - 1), true));
        a_ls(LS_STR, 3, AX16, AFP, vi[j].off as i64);
    }
    let pro = here();

    // Place it: prologue, then the body.
    while mcode.len & (falign as i64 - 1) != 0 { mcode.push(0); }
    let start: u32 = mcode.len as! u32;
    mcode.append(code[body..pro]);
    let base: u32 = mcode.len as! u32;
    mcode.append(code[0..body]);
    for k in rela_start..rela_code.len {
        rela_code[k].offset += base;
        rela_code[k].sec = cur_code_sec;
    }
    // (the prologue's own relocations: none; a_emit_prologue emits no relocated code)
    for ms in a_maps {
        map_syms.push(MapSym { sec: cur_code_sec, off: ms.off + base - osecs[cur_code_sec].start as! u32, data: ms.data });
    }
    for B, b in blocks { blk_code[f.first_block + b] = block_off[b] + base; }
    g_value[f.global] = start - osecs[cur_code_sec].start;
    let size: u32 = mcode.len as! u32 - start;
    g_size[f.global] = size;
    if sec_eh != 0 { eh_func_end(fi, start, size, pro - body, cur_code_sec); }
    if dbg_on { dbg_func_end(fi, start, pro - body, size, cur_code_sec); }
}

fn a_gen_functions() {
    let ns = osecs.len;
    for s in 1..ns {
        if osecs[s].buf != BUF_CODE { continue; }
        cur_code_sec = s as! u32;
        while mcode.len % 16 != 0 { mcode.push(0); }
        osecs[s].start = mcode.len as u64;
        var first = true;
        for k in sec_end[s - 1]..sec_end[s] {
            let G = M.globals[g_order[k]];
            if G.kind != G_FUNC || G.func == GIR_NONE { continue; }
            if M.funcs[G.func].flags & (FN_DEAD | FN_AVAILEXT) != 0 { continue; }
            if first {
                map_syms.push(MapSym { sec: s as! u32, off: 0, data: false });
                first = false;
            }
            a_gen_function(G.func);
        }
        osecs[s].size = mcode.len as u64 - osecs[s].start;
    }
}
