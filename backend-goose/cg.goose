// goovm back-end v2 (milestone A2): GIR version 2 tables -> ELF64 x86-64
// relocatable object.
//
// One pass per function after a liveness pre-pass: values live in registers
// (ra.goose), instructions are selected with immediate, memory-operand,
// address-mode and compare-branch folding (lowera.goose), and the less
// common operations keep A1's legacy lowerings (lower.goose) behind a
// spill-everything-caller-saved boundary. backend-goose/DESIGN.md describes
// the architecture.
//
//   goose --standalone --header cg.h -o cg.c backend-goose/cg.goose
//   (backend-goose/CMakeLists.txt does this when goovm-llc is built.)

import std;
import gir;
import x86;
import ra;
import loc;
import elf;
import abi;
import lowera;
import lower;

var M: Module;

// The object file being built; the host reads it until the next call.
var obj: u8[>..] = [];
// The module's code: every function placed (prologue, body) in order.
var mcode: u8[>..] = [];

// Function order (grouped by code section) and the current code section.
var f_order: u32[>..] = [];
var cur_code_sec: u32 = 0;

// ------------------------------------------------------------------- PHIs

fn has_phi(b: u32) -> bool {
    let B = M.blocks[f_first_block + b];
    return B.n_inst != 0 && M.insts[B.first_inst].op == GIR_PHI;
}
// Scratch registers for the PHI moves of a terminator, taken before the
// terminator branches (a move on one path must not evict values: the other
// path would not see the spill).
var phi_t: u32 = 0;
var phi_x: u32 = 0;
fn phi_scratch() {
    phi_t = ra_temp();
    phi_x = ra_xtemp();
}
// The memory a PHI's incoming value is written to: its temp slot (blocks
// whose PHIs need a parallel copy) or its home.
fn phi_dst(b: u32, j: u32) -> Mem {
    if b_tag[b] == pp_epoch {
        if t_off[j] == 0 { t_off[j] = new_slot(val_slot_size(M.insts[f_first_inst + j].ty)); }
        return m_rbp(t_off[j]);
    }
    return ra_home(j);
}
// Writes value v (type t) to dst without changing the register state (only
// phi_t / phi_x are used).
fn phi_copy(dst: Mem, v: u32, t: u32) {
    let c = rc_of(t);
    if c == RC_GPR {
        let bits = bits_of(t);
        if is_const(v) && cls_of(M.consts[gir_idx(v)].ty) == C_INT {
            if store_const(dst, M.consts[gir_idx(v)].lo, int_bytes(bits)) { return; }
        }
        if is_val(v) {
            let id = vid(v);
            let r: u32 = vi[id].reg;
            if r < 16 {
                store_int(dst, r, bits);
                return;
            }
            if r == PEND {
                load_int(phi_t, pend_peek(id), bits);
                store_int(dst, phi_t, bits);
                return;
            }
        }
        ra_mat_gpr(v, phi_t);
        store_int(dst, phi_t, bits);
        return;
    }
    if c == RC_VX {
        if is_val(v) {
            let r: u32 = vi[vid(v)].reg;
            if r >= 16 && r < 32 {
                xmm_store_t(dst, r - 16, t);
                return;
            }
        }
        if is_const(v) { xmm_load_t(phi_x, const_mem(gir_idx(v)), t); }
        else {
            let id = vid(v);
            xmm_load_t(phi_x, if vi[id].home == H_STACK { m_rbp(vi[id].off) } else { ra_home(id) }, t);
        }
        xmm_store_t(dst, phi_x, t);
        return;
    }
    if c == RC_XMM {
        if is_const(v) && store_const(dst, M.consts[gir_idx(v)].lo, store_of(t)) { return; }
        if is_val(v) {
            let id = vid(v);
            let r: u32 = vi[id].reg;
            if r >= 16 && r < 32 {
                if t == GIR_T_F32 { movss_store(dst, r - 16); } else { movsd_store(dst, r - 16); }
                return;
            }
            if r == PEND {
                load_int(phi_t, pend_peek(id), bits_of(t));
                store_int(dst, phi_t, bits_of(t));
                return;
            }
        }
        if is_const(v) { load_n(phi_t, const_mem(gir_idx(v)), store_of(t)); }
        else {
            let id = vid(v);
            load_int(phi_t, if vi[id].home == H_STACK { m_rbp(vi[id].off) } else { ra_home(id) }, bits_of(t));
        }
        store_int(dst, phi_t, bits_of(t));
        return;
    }
    // memory classes
    let n = slot_size(t) as! u32;
    let src = val_mem(v);
    let m: u32 = if is_const(v) && store_of(t) < n { store_of(t) } else { n };
    copy_mem_t(dst, src, m, gran_of(t), phi_t);
}
fn pend_peek(id: u32) -> Mem {
    for k in 0..n_pend { if pend[k].id == id { return pend[k].m; } }
    assert(false);
    return Mem { M_REG, 0, 0, 0, 0 };
}
// Edge from -> to: write each PHI's incoming value.
fn phi_moves(from: u32, to: u32) {
    let B = M.blocks[f_first_block + to];
    for k in B.first_inst..B.first_inst + B.n_inst {
        let I = M.insts[k];
        if I.op != GIR_PHI { break; }
        let j = k - f_first_inst;
        if vi[j].nuse == 0 { continue; }
        for p in 0..I.c {
            if M.opnds[I.b + 2 * p + 1] != from { continue; }
            phi_copy(phi_dst(to, j), M.opnds[I.b + 2 * p], I.ty);
            break;
        }
    }
}
// A PHI at the start of its block: the value is in its home (copied there
// from the temp slot first if the block uses temps).
fn lower_phi(I: Inst, j: u32, b: u32) {
    if vi[j].nuse == 0 { return; }
    if b_tag[b] == pp_epoch {
        if t_off[j] == 0 { t_off[j] = new_slot(val_slot_size(I.ty)); }
        let t = ra_temp();
        copy_mem_t(ra_home(j), m_rbp(t_off[j]), slot_size(I.ty) as! u32, gran_of(I.ty), t);
    } else {
        ra_home(j);
    }
    vi[j].st |= ST_MEM;
    vi[j].reg = NOREG;
}

// ----------------------------------------------------------- terminators

// Jumps to `target` when the pending flags (flags_cc / flags_cc2 /
// flags_comb) say `when`.
fn jcc_flags(when: bool, target: u32) {
    let cc = flags_cc;
    let cc2 = flags_cc2;
    if flags_comb == 0 {
        jcc_block(if when { cc } else { cc ^ 1 }, target);
    } else if flags_comb == 1 {
        // true iff cc && cc2
        if when {
            let p = jcc_fwd8(cc ^ 1);
            jcc_block(cc2, target);
            patch_here8(p);
        } else {
            jcc_block(cc ^ 1, target);
            jcc_block(cc2 ^ 1, target);
        }
    } else {
        // true iff cc || cc2
        if when {
            jcc_block(cc, target);
            jcc_block(cc2, target);
        } else {
            let p = jcc_fwd8(cc);
            jcc_block(cc2 ^ 1, target);
            patch_here8(p);
        }
    }
}
// Same as a forward jump inside the instruction (returns rel32 positions to patch).
fn jcc_flags_fwd(when: bool) -> u32, u32 {
    let cc = flags_cc;
    let cc2 = flags_cc2;
    if flags_comb == 0 { return jcc_fwd(if when { cc } else { cc ^ 1 }), GIR_NONE; }
    if flags_comb == 1 {
        if when {
            let p = jcc_fwd8(cc ^ 1);
            let q = jcc_fwd(cc2);
            patch_here8(p);
            return q, GIR_NONE;
        }
        return jcc_fwd(cc ^ 1), jcc_fwd(cc2 ^ 1);
    }
    if when { return jcc_fwd(cc), jcc_fwd(cc2); }
    let p = jcc_fwd8(cc);
    let q = jcc_fwd(cc2 ^ 1);
    patch_here8(p);
    return q, GIR_NONE;
}

fn lower_condbr(I: Inst, cur: u32, next: u32) {
    let fused = flags_id != RV_NONE && I.a == inst_ref(flags_id);
    if !fused {
        let r = ra_gpr(I.a, true);
        test_rr32(r, r);
        flags_cc = CC_NE;
        flags_comb = 0;
    }
    flags_id = RV_NONE;
    if has_phi(I.b) || has_phi(I.c) {
        phi_scratch();
        let p, q = jcc_flags_fwd(false);
        phi_moves(cur, I.b);
        jmp_block(I.b);
        patch_here(p);
        if q != GIR_NONE { patch_here(q); }
        phi_moves(cur, I.c);
        if I.c != next { jmp_block(I.c); }
    } else if I.b == next {
        jcc_flags(false, I.c);
    } else {
        jcc_flags(true, I.b);
        if I.c != next { jmp_block(I.c); }
    }
}

// Jump tables: entries are rel32 offsets from the table start, which sits in
// the code right after the indirect jump. An entry whose target block is not
// placed yet is patched with the fixups (jt_fix).
struct JtFix { pos: u32, blk: u32, base: u32 }
var jt_fix: JtFix[>..] = [];
var jt_case: u32[>..] = [];     // per table entry: case index + 1 (0: default)
var jt_stub_blk: u32[>..] = []; // PHI edges: target block and its stub's position
var jt_stub_pos: u32[>..] = [];

// The value of case k of SWITCH I, sign-extended from `bits`.
fn case_val(I: Inst, k: u32, bits: u32) -> i64 {
    var x: i64 = M.consts[gir_idx(M.opnds[I.b + 1 + 2 * k])].lo as! i64;
    if bits < 64 { x = (x << (64 - bits)) >> (64 - bits); }
    return x;
}
// A dense switch (at least 4 cases, at least 40% of the range) through a
// table: t = sext(x) - lo; if t > hi - lo goto default; goto table[t].
fn switch_table(I: Inst, cur: u32, r: u32, bits: u32) -> bool {
    let nc: u32 = I.c;
    if nc < 4 { return false; }
    var lo: i64 = case_val(I, 0, bits);
    var hi: i64 = lo;
    for k in 1..nc {
        let x = case_val(I, k, bits);
        if x < lo { lo = x; }
        if x > hi { hi = x; }
    }
    let span: u64 = (hi as! u64) - (lo as! u64);   // entries - 1 (wraps for huge ranges: then too large)
    if span >= 0x40000000 || (span + 1) * 2 > (nc as u64) * 5 || !fits32(lo) { return false; }
    let n: u32 = span as! u32 + 1;
    let t = ra_temp();
    let u = ra_temp();
    sign_ext_into(t, r, bits);
    if lo != 0 { grp1_ri(1, G1_SUB, t, lo as! i32); }
    grp1_ri(1, G1_CMP, t, span as! i32);
    let d = M.opnds[I.b];
    let dphi = has_phi(d);
    var dpos: u32 = 0;
    if dphi { dpos = jcc_fwd(CC_A); } else { jcc_block(CC_A, d); }
    let lp = lea_here(u);
    load32s(t, m_sib(u, t, 2, 0));
    alu_rr64(ALU_ADD, t, u);
    jmp_r(t);
    let base = here();
    patch_here(lp);
    // the table
    if jt_case.len < n { jt_case.resize(n, 0); }
    for e in 0..n { jt_case[e] = 0; }
    for k in 0..nc { jt_case[(case_val(I, k, bits) - lo) as! u32] = k + 1; }
    for e in 0..n { b4(0); }
    // stubs for the edges into blocks with PHIs
    jt_stub_blk.clear();
    jt_stub_pos.clear();
    for e in 0..n + 1 {
        // (entry n: the default's own branch)
        var tb = d;
        if e < n && jt_case[e] != 0 { tb = M.opnds[I.b + 2 * jt_case[e]]; }
        if !has_phi(tb) { continue; }
        var seen = false;
        for q in jt_stub_blk { if q == tb { seen = true; } }
        if seen { continue; }
        jt_stub_blk.push(tb);
        jt_stub_pos.push(here());
        phi_moves(cur, tb);
        jmp_block(tb);
    }
    if dphi { patch4(dpos, stub_pos(d) - (dpos + 4)); }
    for e in 0..n {
        var tb = d;
        if jt_case[e] != 0 { tb = M.opnds[I.b + 2 * jt_case[e]]; }
        let p = base + 4 * e;
        if has_phi(tb) { patch4(p, stub_pos(tb) - base); }
        else if tb <= cur_blk { patch4(p, block_off[tb] - base); }
        else { jt_fix.push(JtFix { pos: p, blk: tb, base: base }); }
    }
    return true;
}
fn stub_pos(b: u32) -> u32 {
    for q, k in jt_stub_blk { if q == b { return jt_stub_pos[k]; } }
    assert(false);
    return 0;
}

fn lower_switch(I: Inst, cur: u32, next: u32) {
    let t: u32 = I.aux;
    let wide = cls_of(t) == C_INT2;
    var phis = has_phi(M.opnds[I.b]);
    for k in 0..I.c { if has_phi(M.opnds[I.b + 2 + 2 * k]) { phis = true; } }
    if phis { phi_scratch(); }
    var r: u32 = 0;
    var rhi: u32 = 0;
    let bits = bits_of(t);
    let ex = exact_width(bits);
    let n: u32 = if !ex { if bits <= 32 { 4 } else { 8 } } else { bits / 8 };
    if wide {
        r = ra_temp();
        rhi = ra_temp();
        use_gpr2(I.a, r, rhi);
    } else {
        r = ra_gpr(I.a, !ex);
        if ex && switch_table(I, cur, r, bits) { return; }
    }
    var tc: u32 = 32;
    for k in 0..I.c {
        let c = M.consts[gir_idx(M.opnds[I.b + 1 + 2 * k])];
        let tb = M.opnds[I.b + 2 + 2 * k];
        var miss: u32 = GIR_NONE;
        if wide {
            if tc == 32 { tc = ra_temp(); }
            mov_ri(tc, c.hi);
            alu_rr64(ALU_CMP, rhi, tc);
            miss = jcc_fwd(CC_NE);
            mov_ri(tc, c.lo);
            alu_rr64(ALU_CMP, r, tc);
        } else if n <= 4 || fits32(c.lo as! i64) {
            cmp_ri_n(n, r, (c.lo as! u32) as! i32);
        } else {
            if tc == 32 { tc = ra_temp(); }
            mov_ri(tc, c.lo);
            alu_rr64(ALU_CMP, r, tc);
        }
        if has_phi(tb) {
            let p = jcc_fwd(CC_NE);
            phi_moves(cur, tb);
            jmp_block(tb);
            patch_here(p);
        } else {
            jcc_block(CC_E, tb);
        }
        if miss != GIR_NONE { patch_here(miss); }
    }
    let d = M.opnds[I.b];
    phi_moves(cur, d);
    if d != next { jmp_block(d); }
}

fn lower_ret(I: Inst, j: u32) {
    if I.a != GIR_NONE {
        let t = type_of(I.a);
        let c = rc_of(t);
        if c == RC_GPR { ra_gpr_into(I.a, RAX, bits_of(t) < 32); }
        else if in_xmm(c) { ra_xmm_into(I.a, XMM0); }
        else {
            ra_tierb_begin(false);
            ret_value(I.a, t);
            tierb = false;
        }
    }
    // the epilogue follows the last block
    if j + 1 != f_nins { jmp_block(cur_nblocks); }
}
var cur_nblocks: u32 = 0;

// ------------------------------------------------------------ instructions

fn gen_inst(gi: u32, cur: u32) {
    let I = M.insts[gi];
    let j = gi - f_first_inst;
    let next = cur + 1;
    cur_pos = j;
    let k: u32 = vi[j].kind;
    if k == K_A || k == K_CALL {
        match I.op {
            GIR_RET => lower_ret(I, j),
            GIR_BR => {
                if has_phi(I.a) {
                    phi_scratch();
                    phi_moves(cur, I.a);
                }
                if I.a != next { jmp_block(I.a); }
            },
            GIR_CONDBR => lower_condbr(I, cur, next),
            GIR_SWITCH => lower_switch(I, cur, next),
            GIR_INDIRECTBR => {
                phi_scratch();
                for q in 0..I.c {
                    let tb = M.opnds[I.b + q];
                    var seen = false;
                    for p in 0..q { if M.opnds[I.b + p] == tb { seen = true; } }
                    if !seen { phi_moves(cur, tb); }
                }
                jmp_r(ra_gpr(I.a, false));
            },
            GIR_UNREACHABLE, GIR_TRAP => ud2(),
            GIR_DEBUGTRAP => b1(0xCC),
            GIR_ADD, GIR_SUB, GIR_MUL, GIR_SDIV, GIR_UDIV, GIR_SREM, GIR_UREM,
            GIR_AND, GIR_OR, GIR_XOR, GIR_SHL, GIR_LSHR, GIR_ASHR => {
                if rc_of(I.ty) == RC_VX { lower_vbin_a(I, j); } else { lower_binop_a(I, j); }
            },
            GIR_ICMP => lower_icmp_a(I, j),
            GIR_FCMP => lower_fcmp_a(I, j),
            GIR_FADD, GIR_FSUB, GIR_FMUL, GIR_FDIV => {
                if rc_of(I.ty) == RC_VX { lower_vbin_a(I, j); } else { lower_fbin_a(I, j); }
            },
            GIR_INSERTELT => lower_vins_a(I, j),
            GIR_EXTRACTELT => lower_vext_a(I, j),
            GIR_FNEG, GIR_FABS, GIR_FSQRT, GIR_COPYSIGN => lower_funary_a(I, j),
            GIR_SELECT => lower_select_a(I, j),
            GIR_ZEXT, GIR_SEXT, GIR_TRUNC, GIR_PTRTOINT, GIR_INTTOPTR, GIR_BITCAST,
            GIR_FPEXT, GIR_FPTRUNC, GIR_FPTOSI, GIR_FPTOUI, GIR_SITOFP, GIR_UITOFP => lower_cast_a(I, j),
            GIR_ALLOCA => {},
            GIR_LOAD => lower_load_a(I, j),
            GIR_STORE => lower_store_a(I),
            GIR_GEP => lower_gep_a(I, j),
            GIR_CALL => lower_call(I, j),
            GIR_PHI => lower_phi(I, j, cur),
            GIR_MEMCPY, GIR_MEMSET => lower_memcpy_a(I),
            _ => ud2(),
        }
        ra_end_inst();
        return;
    }
    ra_tierb_begin(k == K_ALL);
    gen_inst_b(I, j);
    ra_tierb_end();
    ra_end_inst();
}

// Legacy lowerings (A1): every caller-saved register is free when they run.
fn gen_inst_b(I: Inst, j: u32) {
    match I.op {
        GIR_ADD, GIR_SUB, GIR_MUL, GIR_SDIV, GIR_UDIV, GIR_SREM, GIR_UREM,
        GIR_AND, GIR_OR, GIR_XOR, GIR_SHL, GIR_LSHR, GIR_ASHR => {
            if cls_of(I.ty) == C_INT2 { int2_binop(I, j); } else { vec_binop(I, j); }
        },
        GIR_ICMP => {
            let t: u32 = I.aux;
            if cls_of(t) == C_VEC { vec_cmp(I, j); }
            else {
                int2_cmp(I.sub, bits_of(t), I.a, I.b);
                put_gpr(j, RAX);
            }
        },
        GIR_FADD, GIR_FSUB, GIR_FMUL, GIR_FDIV => {
            if cls_of(I.ty) == C_X87 {
                fld_m(10, val_mem(I.a));
                fld_m(10, val_mem(I.b));
                fop_p(x87_op(I.op));
                fstp_m(10, res_mem(j));
            } else if I.ty == GIR_T_F16 {
                use_xmm(I.a, XMM0);
                use_xmm(I.b, XMM1);
                sse_arith(sse_op(I.op), false, XMM0, XMM1);
                put_xmm(j, XMM0, I.ty);
            } else {
                vec_binop(I, j);
            }
        },
        GIR_FNEG, GIR_FABS, GIR_COPYSIGN, GIR_FSQRT => lower_fp_unary(I, j),
        GIR_FCMP => {
            let t: u32 = I.aux;
            let c = cls_of(t);
            if c == C_VEC { vec_cmp(I, j); }
            else {
                if c == C_X87 { fcmp_x87(I.sub, val_mem(I.a), val_mem(I.b)); }
                else {
                    use_xmm(I.a, XMM0);
                    use_xmm(I.b, XMM1);
                    fcmp_xmm(I.sub, t == GIR_T_F64);
                }
                put_gpr(j, RAX);
            }
        },
        GIR_SELECT => lower_select(I, j),
        GIR_ZEXT, GIR_SEXT, GIR_TRUNC, GIR_PTRTOINT, GIR_INTTOPTR, GIR_BITCAST,
        GIR_FPEXT, GIR_FPTRUNC, GIR_FPTOSI, GIR_FPTOUI, GIR_SITOFP, GIR_UITOFP => lower_cast(I, j),
        GIR_LOAD => lower_load(I, j),
        GIR_STORE => lower_store(I),
        GIR_EXTRACTVALUE => load_to_result(j, I.ty, m_add(val_mem(I.a), I.b)),
        GIR_INSERTVALUE => {
            copy_val(res_mem(j), I.a, size_of(I.ty));
            store_value(m_add(res_mem(j), I.c), I.b, type_of(I.b));
        },
        GIR_EXTRACTELT => lower_extractelt(I, j),
        GIR_INSERTELT => lower_insertelt(I, j),
        GIR_SHUFFLE => lower_shuffle(I, j),
        GIR_DYNALLOCA => lower_dynalloca(I, j),
        GIR_STACKSAVE => {
            mov_rr64(RAX, RSP);
            put_gpr(j, RAX);
        },
        GIR_STACKRESTORE => {
            use_fixed(I.a, RAX);
            mov_rr64(RSP, RAX);
        },
        GIR_VASTART => lower_vastart(I),
        GIR_CTLZ, GIR_CTTZ, GIR_CTPOP, GIR_BSWAP, GIR_BITREVERSE => lower_bitop(I, j),
        GIR_FSHL, GIR_FSHR => lower_funnel(I, j),
        GIR_OVF => lower_ovf(I, j),
        GIR_SCMP, GIR_UCMP => lower_scmp(I, j),
        GIR_ISFPCLASS => lower_isfpclass(I, j),
        GIR_CMPXCHG => lower_cmpxchg(I, j),
        GIR_ATOMICRMW => lower_atomicrmw(I, j),
        GIR_FENCE => {
            let ord = (I.flags & IF_ORD_MASK) >> IF_ORD_SHIFT;
            if ord == ORD_SEQ_CST && I.flags & IF_SINGLETHREAD == 0 { mfence(); }
        },
        GIR_TLSADDR => lower_tlsaddr(I, j),
        GIR_FRAMEADDR, GIR_RETADDR => lower_frameaddr(I, j),
        GIR_SJLJ_SETJMP => lower_setjmp(I, j),
        GIR_SJLJ_LONGJMP => lower_longjmp(I),
        GIR_BLOCKADDR => lower_blockaddr(I, j),
        GIR_X86 => lower_x86(I, j),
        GIR_ASM => lower_asm(I, j),
        _ => ud2(),  // unknown opcode: trap
    }
}

// ----------------------------------------------------------- frame layout

// Home of alloca j; true if it is over-aligned (aligned at run time).
fn layout_alloca(I: Inst, j: u32) -> bool {
    let al: i64 = if I.b != 0 { I.b } else { 1 };
    let size: i64 = if I.a != 0 { I.a } else { 1 };
    if al <= 16 {
        lay_off = (lay_off + size + al - 1) & ~(al - 1);  // al is a power of two (no division)
        vi[j].off = (-lay_off) as! i32;
        vi[j].home = H_ALLOCA;
        return false;
    }
    // area of size + al bytes, aligned at run time; the pointer gets a slot
    lay_off = (lay_off + size + al + 15) & ~15;
    t_off[j] = (-lay_off) as! i32;
    lay_off = ((lay_off + 7) & ~7) + 8;
    vi[j].off = (-lay_off) as! i32;
    vi[j].home = H_PTR;
    vi[j].st |= ST_MEM;
    return true;
}

// --------------------------------------------------------------- functions

var f_ncs: u32 = 0;          // callee-saved registers this function may use
var f_overaligned = false;

// push rbp; mov rbp, rsp; saves; frame; argument stores; over-aligned allocas.
fn emit_prologue(insts: const Inst[:], flags: u32) {
    b1(0x55);
    b1(0x48);
    b1(0x89);
    b1(0xE5);
    var nsave: i64 = 0;
    for r in CS_REGS {
        if r_cs_used & bit(r) != 0 {
            push_r(r);
            nsave++;
        }
    }
    let frame: i64 = (lay_off + 15) & ~15;
    let sub = frame - 8 * nsave;
    let leaf = !f_call && !f_rsp && !f_asm && !f_sjlj;
    if sub > 0 && !(leaf && sub <= 128) { grp1_ri64(G1_SUB, RSP, sub as! i32); }
    if flags & FN_VASTART != 0 { save_va_regs(); }
    prologue_args();
    if f_overaligned {
        for I, j in insts {
            if I.op != GIR_ALLOCA || vi[j].home != H_PTR { continue; }
            let al: i64 = I.b;
            lea64(RAX, m_rbp(t_off[j]));
            grp1_ri64(G1_ADD, RAX, (al - 1) as! i32);
            grp1_ri64(G1_AND, RAX, (0 - al) as! i32);
            store64(m_rbp(vi[j].off), RAX);
        }
    }
}
// rsp is not moved below the saved registers (no frame, or a leaf's frame
// in the red zone), so the epilogue can pop rbp directly.
fn frameless() -> bool {
    var nsave: i64 = 0;
    for r in CS_REGS { if r_cs_used & bit(r) != 0 { nsave++; } }
    let sub = ((lay_off + 15) & ~15) - 8 * nsave;
    let leaf = !f_call && !f_rsp && !f_asm && !f_sjlj;
    return sub <= 0 || leaf && sub <= 128;
}
fn emit_epilogue() {
    var nsave: u32 = 0;
    for r in CS_REGS { if r_cs_used & bit(r) != 0 { nsave++; } }
    if nsave == 0 {
        if frameless() && !f_rsp { b1(0x5D); } else { b1(0xC9); }  // pop rbp / leave
        b1(0xC3);  // ret
        return;
    }
    lea64(RSP, m_rbp((0 - 8 * nsave) as! i32));
    var k: i64 = 4;
    while k >= 0 {
        let r = CS_REGS[k];
        if r_cs_used & bit(r) != 0 { pop_r(r); }
        k--;
    }
    b1(0x5D);  // pop rbp
    b1(0xC3);  // ret
}

fn gen_function(fi: u32) {
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
        vi.resize(nv, VInfo { reg: NOREG, st: 0, home: H_NONE, nuse: 0, ncl: 0, kind: 0, hint: NOREG, spare: 0, last: 0, off: 0 });
    }
    if t_off.len < f.n_inst { t_off.resize(f.n_inst, 0); }
    if b_tag.len < f.n_blocks { b_tag.resize(f.n_blocks, 0); }
    if block_off.len < f.n_blocks + 1 { block_off.resize(f.n_blocks + 1, 0); }
    assert(t_off.len >= insts.len && block_off.len > blocks.len);

    ra_prepass(insts, blocks);
    f_share = f.flags & (FN_SJLJ | FN_RETURNS_TWICE) == 0;
    var ncs = pp_ncs;
    if ncs > 5 { ncs = 5; }
    if f_sjlj || f_asm { ncs = 5; }
    f_ncs = ncs;
    var cs: u32 = 0;
    for q in 0..ncs { cs |= bit(CS_REGS[q]); }
    r_alloc = GP_CALLER | XMM_ALL | cs;
    r_cs_used = if f_sjlj || f_asm { cs } else { 0 };
    ra_func_start();

    // Frame: the callee-saved save area, the va register save area, allocas,
    // then homes and spill slots as they are needed.
    code.clear();
    fixups.clear();
    jt_fix.clear();
    let rela_start = rela_code.len;
    let baddr_start = baddr.len;
    lay_off = 8 * ncs as i64;
    n_free8 = 0;
    n_free16 = 0;
    scratch_off = 0;
    if f.flags & FN_VASTART != 0 {
        lay_off = (lay_off + 176 + 15) & ~15;
        rsa_off = (-lay_off) as! i32;
    }
    f_overaligned = false;
    let E = blocks[0];
    for gi in E.first_inst..E.first_inst + E.n_inst {
        let I = M.insts[gi];
        if I.op != GIR_ALLOCA { continue; }
        if layout_alloca(I, gi - f_first_inst) { f_overaligned = true; }
    }
    setup_args();

    for B, b in blocks {
        cur_blk = b as! u32;
        block_off[b] = here();
        if b == 0 { ra_entry_state(); } else { ra_block_start(); }
        for k in B.first_inst..B.first_inst + B.n_inst { gen_inst(k, b as! u32); }
    }
    // epilogue (pseudo block n_blocks), then the prologue
    cur_blk = f.n_blocks;
    block_off[f.n_blocks] = here();
    emit_epilogue();
    for x in fixups {
        patch4(x.pos, block_off[x.blk] - (x.pos + 4));
    }
    for x in jt_fix { patch4(x.pos, block_off[x.blk] - x.base); }
    let body = here();
    emit_prologue(insts, f.flags);
    let pro = here();

    // Place it: prologue, then the body.
    while mcode.len & (falign as i64 - 1) != 0 { mcode.push(0xCC); }
    let start: u32 = mcode.len as! u32;
    mcode.append(code[body..pro]);
    let base: u32 = mcode.len as! u32;
    mcode.append(code[0..body]);
    for k in rela_start..rela_code.len { rela_code[k].offset += base; }
    for k in baddr_start..baddr.len { baddr[k].pos += base; }
    for B, b in blocks { blk_code[f.first_block + b] = block_off[b] + base; }

    g_value[f.global] = start - osecs[cur_code_sec].start;
    g_size[f.global] = mcode.len as u64 - start;
}

// Generates all functions, grouped by code section.
fn gen_functions() {
    let nf = M.funcs.len;
    f_order.clear();
    f_order.resize(nf, 0);
    let ns = osecs.len;
    // functions of each code section, in table order
    var k: i64 = 0;
    for s in 1..ns {
        if osecs[s].buf != BUF_CODE { continue; }
        cur_code_sec = s as! u32;
        while mcode.len % 16 != 0 { mcode.push(0xCC); }
        osecs[s].start = mcode.len as u64;
        for F, fi in M.funcs {
            if g_sec[F.global] != s { continue; }
            gen_function(fi as! u32);
            k++;
        }
        osecs[s].size = mcode.len as u64 - osecs[s].start;
    }
}

// ------------------------------------------------------------------ entry

// Compiles the whole module and returns the bytes of an ELF64 x86-64
// relocatable object (valid until the next call). The module must follow
// the structural rules of gir.h; the back-end does not validate its input
// (an out-of-range index aborts on a bounds check instead of reading
// garbage).
export fn gir_codegen(header: const Header[:], types: const TypeDef[:], funcs: const Func[:],
                      blocks: const Block[:], insts: const Inst[:], opnds: const u32[:], consts: const Const[:],
                      globals: const Global[:], sections: const Section[:], data: const u8[:],
                      drelocs: const DataReloc[:], strtab: const u8[:], dlocs: const DLoc[:],
                      dscopes: const DScope[:], dfiles: const DFile[:], dstr: const u8[:],
                      asms: const Asm[:]) -> const u8[:] {
    M = Module { header: header, types: types, funcs: funcs, blocks: blocks, insts: insts, opnds: opnds,
                 consts: consts, globals: globals, sections: sections, data: data, drelocs: drelocs,
                 strtab: strtab, dlocs: dlocs, dscopes: dscopes, dfiles: dfiles, dstr: dstr, asms: asms };
    code.clear();
    mcode.clear();
    rela_code.clear();
    sdata.clear();
    srodata.clear();
    cst4.clear();
    cst8.clear();
    cst16.clear();
    baddr.clear();
    pool_syms.clear();
    rodata_align = 16;
    c_pool.clear();
    c_pool.resize(consts.len, GIR_NONE);
    for q in 4 { mask_pool[q] = GIR_NONE; }
    blk_code.clear();
    blk_code.resize(blocks.len, 0);
    build_type_rc();
    make_sections();
    layout_globals();
    gen_functions();
    resolve_blockaddrs();
    resolve_aliases();
    write_elf(obj);
    return obj;
}
