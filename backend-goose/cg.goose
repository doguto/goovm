// goovm back-end v1: GIR version 2 tables -> ELF64 x86-64 relocatable object.
//
// One pass per function at -O0 quality behind a value-location interface
// (loc.goose): every value has a frame home, instructions load operands into
// scratch registers and store results back. backend-goose/DESIGN.md
// describes the architecture.
//
//   goose --standalone --header cg.h -o cg.c backend-goose/cg.goose
//   (backend-goose/CMakeLists.txt does this when goovm-llc is built.)

import gir;
import x86;
import loc;
import elf;
import abi;
import lower;

var M: Module;

// The object file being built; the host reads it until the next call.
var obj: u8[>..] = [];

// Function order (grouped by code section) and the current code section.
var f_order: u32[>..] = [];
var cur_code_sec: u32 = 0;

// ------------------------------------------------------------------- PHIs

fn has_phi(b: u32) -> bool {
    let B = M.blocks[f_first_block + b];
    return B.n_inst != 0 && M.insts[B.first_inst].op == GIR_PHI;
}
// Edge from -> to: write each PHI's incoming value into the PHI's temp slot.
fn phi_moves(from: u32, to: u32) {
    let B = M.blocks[f_first_block + to];
    for k in B.first_inst..B.first_inst + B.n_inst {
        let I = M.insts[k];
        if I.op != GIR_PHI { break; }
        for p in 0..I.c {
            if M.opnds[I.b + 2 * p + 1] != from { continue; }
            let v = M.opnds[I.b + 2 * p];
            let tmp = m_rbp(t_off[k - f_first_inst]);
            if cls_of(I.ty) == C_INT {
                use_gpr(v, RAX);
                store64(tmp, RAX);
            } else {
                copy_val(tmp, v, slot_size(I.ty) as! u32);
            }
            break;
        }
    }
}

// ----------------------------------------------------------- terminators

fn epilogue() {
    if f_sjlj {
        load64(RBX, m_rbp(-8));
        load64(R12, m_rbp(-16));
        load64(R13, m_rbp(-24));
        load64(R14, m_rbp(-32));
        load64(R15, m_rbp(-40));
    }
    b1(0xC9);  // leave
    b1(0xC3);  // ret
}

fn lower_switch(I: Inst, cur: u32, next: u32) {
    let t: u32 = I.aux;
    let wide = cls_of(t) == C_INT2;
    if wide { use_gpr2(I.a, RAX, RDX); } else { use_fixed(I.a, RAX); }
    for k in 0..I.c {
        let c = M.consts[gir_idx(M.opnds[I.b + 1 + 2 * k])];
        let tb = M.opnds[I.b + 2 + 2 * k];
        var miss: u32 = GIR_NONE;
        if wide {
            mov_ri(RCX, c.hi);
            alu_rr64(ALU_CMP, RDX, RCX);
            miss = jcc_fwd(CC_NE);
        }
        let v: i64 = c.lo as! i64;
        if fits32(v) {
            grp1_ri64(G1_CMP, RAX, v as! i32);
        } else {
            mov_ri(RCX, c.lo);
            alu_rr64(ALU_CMP, RAX, RCX);
        }
        if has_phi(tb) {
            let p = jcc_fwd(CC_NE);
            phi_moves(cur, tb);
            if wide { use_gpr2(I.a, RAX, RDX); } else { use_fixed(I.a, RAX); }
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

// ------------------------------------------------------------ instructions

fn gen_inst(gi: u32, cur: u32) {
    let I = M.insts[gi];
    let j = gi - f_first_inst;
    let next = cur + 1;
    cur_pos = j;
    match I.op {
        GIR_RET => {
            if I.a != GIR_NONE { ret_value(I.a, type_of(I.a)); }
            epilogue();
        },
        GIR_BR => {
            phi_moves(cur, I.a);
            if I.a != next { jmp_block(I.a); }
        },
        GIR_CONDBR => {
            use_fixed(I.a, RAX);
            test_rr32(RAX, RAX);
            if has_phi(I.b) || has_phi(I.c) {
                let p = jcc_fwd(CC_E);
                phi_moves(cur, I.b);
                jmp_block(I.b);
                patch_here(p);
                phi_moves(cur, I.c);
                if I.c != next { jmp_block(I.c); }
            } else if I.b == next {
                jcc_block(CC_E, I.c);
            } else {
                jcc_block(CC_NE, I.b);
                if I.c != next { jmp_block(I.c); }
            }
        },
        GIR_SWITCH => lower_switch(I, cur, next),
        GIR_INDIRECTBR => {
            for k in 0..I.c {
                let tb = M.opnds[I.b + k];
                var seen = false;
                for q in 0..k { if M.opnds[I.b + q] == tb { seen = true; } }
                if !seen { phi_moves(cur, tb); }
            }
            use_fixed(I.a, RAX);
            jmp_r(RAX);
        },
        GIR_UNREACHABLE, GIR_TRAP => ud2(),
        GIR_DEBUGTRAP => b1(0xCC),
        GIR_ADD, GIR_SUB, GIR_MUL, GIR_SDIV, GIR_UDIV, GIR_SREM, GIR_UREM,
        GIR_AND, GIR_OR, GIR_XOR, GIR_SHL, GIR_LSHR, GIR_ASHR => {
            let d = M.types[I.ty];
            let c: u32 = d.cls;
            if c == C_INT {
                let bits: u32 = d.bits;
                use_fixed(I.a, RAX);
                let op: u32 = I.op;
                let ok, imm = alu_imm(I.b, bits);
                if ok && (op == GIR_ADD || op == GIR_SUB || op == GIR_AND || op == GIR_OR || op == GIR_XOR) {
                    let ext: u32 = match op { GIR_ADD => G1_ADD, GIR_SUB => G1_SUB, GIR_AND => G1_AND,
                                              GIR_OR => G1_OR, _ => G1_XOR };
                    grp1_ri64(ext, RAX, imm);
                    if op != GIR_AND { zext_reg(RAX, bits); }
                } else if is_const(I.b) && (op == GIR_SHL || op == GIR_LSHR || op == GIR_ASHR) {
                    let n = (M.consts[gir_idx(I.b)].lo & 63) as! u32;
                    if op == GIR_ASHR { sext_reg(RAX, bits); }
                    shift_imm64(if op == GIR_SHL { SH_SHL } else if op == GIR_LSHR { SH_SHR } else { SH_SAR }, RAX, n);
                    if op != GIR_LSHR { zext_reg(RAX, bits); }
                } else {
                    use_fixed(I.b, RCX);
                    int_binop(op, bits);
                }
                put_gpr(j, RAX);
            } else if c == C_INT2 {
                int2_binop(I, j);
            } else {
                vec_binop(I, j);
            }
        },
        GIR_ICMP => {
            let t: u32 = I.aux;
            let c = cls_of(t);
            if c == C_VEC { vec_cmp(I, j); }
            else if c == C_INT2 {
                int2_cmp(I.sub, bits_of(t), I.a, I.b);
                put_gpr(j, RAX);
            } else {
                int_cmp_vals(I.sub, bits_of(t), I.a, I.b);
                put_gpr(j, RAX);
            }
        },
        GIR_FADD, GIR_FSUB, GIR_FMUL, GIR_FDIV => {
            let c = cls_of(I.ty);
            if c == C_FP {
                use_xmm(I.a, XMM0);
                use_xmm(I.b, XMM1);
                sse_arith(sse_op(I.op), I.ty == GIR_T_F64, XMM0, XMM1);
                put_xmm(j, XMM0, I.ty);
            } else if c == C_X87 {
                fld_m(10, val_mem(I.a));
                fld_m(10, val_mem(I.b));
                fop_p(x87_op(I.op));
                fstp_m(10, res_mem(j));
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
        GIR_ALLOCA => {},
        GIR_LOAD => lower_load(I, j),
        GIR_STORE => lower_store(I),
        GIR_GEP => lower_gep(I, j),
        GIR_CALL => lower_call(I, j),
        GIR_PHI => {
            let tmp = m_rbp(t_off[j]);
            if cls_of(I.ty) == C_INT {
                load64(RAX, tmp);
                put_gpr(j, RAX);
            } else {
                copy_mem_g(res_mem(j), tmp, slot_size(I.ty) as! u32, gran_of(I.ty));
            }
        },
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
        GIR_MEMCPY, GIR_MEMSET => lower_memcpy(I),
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

// Homes are laid out by one backward pass over the function that also finds
// each value's last use, so that values can share frame slots: one slot per
// value overflowed the stack in consumer-typeset's recursive Manifest (a
// 97 KB frame per call; clang -O0: 2 KB). Scanning backward, the first use
// of a value that is seen is its last one: the value gets its slot there and
// gives it back at its definition. A value whose uses are all in its own
// block ("local") shares 8- and 16-byte slots with other local values; a
// value used in another block keeps its own slot. Local values of different
// blocks are never live at the same time, so no liveness across blocks is
// needed. A use above its definition in layout order (a block that comes
// before the defining one) is detected and the function is laid out again
// with one slot per value, as are functions that call a returns_twice
// function (the second return from setjmp sees the slots as they were).
// The pass costs about as much again as the forward layout it replaces, so
// functions of at most SHARE_MIN_INSTS instructions (value slots of at most
// ~2 KB) keep one slot per value.

let SHARE_MIN_INSTS = 256;

var v_mark: u32[>..] = [];      // per value: lay_epoch + MK_*
var lay_epoch: u32 = 0;         // advances by 4 per function
let MK_SLOT = 0;                // has its slot (a later use was seen)
let MK_DEF = 1;                 // definition passed
let MK_ALLOCA = 2;              // alloca (homed by the entry-block pass)
var lay_off: i64 = 0;           // bytes below rbp so far
var lay_lo: u32 = 0;            // current block [lay_lo, lay_hi) (module indices)
var lay_conflict = false;
var f_end_inst: u32 = 0;
var free8: i32[>..] = [];       // free shared slots (rbp offsets), 8 and 16 bytes
var free16: i32[>..] = [];
var n_free8: i64 = 0;
var n_free16: i64 = 0;

// Value operands per opcode: U_A/U_B/U_C for the fields a, b, c, plus the
// operand runs of GEP, CALL and ASM (PHI incoming values are uses of the
// predecessor's terminator). Immediates are not listed: taking one for a
// value only limits sharing, while a missed use would be a miscompile,
// which live_check turns into an abort.
let U_A = 1;
let U_B = 2;
let U_C = 4;
let U_GEP = 8;
let U_CALL = 16;
let U_ASM = 64;
let OP_USES: u8[83] = [
    1, 0, 1, 1, 0, 3, 3, 3,  // ret br condbr switch unreachable add sub mul
    3, 3, 3, 3, 3, 3, 3, 3,  // sdiv udiv srem urem and or xor shl
    3, 3, 3, 7, 1, 1, 1, 1,  // lshr ashr icmp select zext sext trunc ptrtoint
    1, 1, 0, 1, 3, 9, 17, 0,  // inttoptr bitcast alloca load store gep call phi
    3, 3, 3, 3, 1, 3, 1, 1,  // fadd fsub fmul fdiv fneg fcmp fpext fptrunc
    1, 1, 1, 1, 1, 3, 3, 7,  // fptosi fptoui sitofp uitofp extractvalue insertvalue extractelt insertelt
    3, 1, 0, 1, 1, 3, 3, 1,  // shuffle dynalloca stacksave stackrestore vastart memcpy memset ctlz
    1, 1, 1, 1, 7, 7, 3, 3,  // cttz ctpop bswap bitreverse fshl fshr ovf scmp
    3, 1, 3, 1, 1, 7, 3, 0,  // ucmp fabs copysign fsqrt isfpclass cmpxchg atomicrmw fence
    0, 0, 0, 1, 1, 0, 0, 1,  // tlsaddr frameaddr retaddr sjlj_setjmp sjlj_longjmp trap debugtrap indirectbr
    0, 3, 64,  // blockaddr x86 asm
];

// A fresh slot of sz bytes (16-aligned from 16 bytes on).
inline fn new_slot(sz: i64) -> i32 {
    lay_off += sz;
    if sz >= 16 { lay_off = (lay_off + 15) & ~15; }
    return (-lay_off) as! i32;
}
inline fn val_slot_size(t: u32) -> i64 { if t > GIR_T_F64 { slot_size(t) } else { 8 } }

// Home of alloca j; true if it is over-aligned (aligned at run time).
fn layout_alloca(I: Inst, j: u32) -> bool {
    let al: i64 = if I.b != 0 { I.b } else { 1 };
    let size: i64 = if I.a != 0 { I.a } else { 1 };
    if al <= 16 {
        lay_off = (lay_off + size + al - 1) & ~(al - 1);  // al is a power of two (no division)
        v_off[j] = (-lay_off) as! i32;
        v_home[j] = H_ALLOCA;
        return false;
    }
    // area of size + al bytes, aligned at run time; the pointer gets a slot
    lay_off = (lay_off + size + al + 15) & ~15;
    t_off[j] = (-lay_off) as! i32;
    lay_off = ((lay_off + 7) & ~7) + 8;
    v_off[j] = (-lay_off) as! i32;
    v_home[j] = H_PTR;
    return true;
}

// One slot per value. Returns whether there are over-aligned allocas.
fn layout_unique(insts: const Inst[:]) -> bool {
    var overaligned = false;
    for I, j in insts {
        if I.op == GIR_ALLOCA {
            if layout_alloca(I, j as! u32) { overaligned = true; }
        } else if I.ty != GIR_T_VOID {
            let sz = val_slot_size(I.ty);
            v_off[j] = new_slot(sz);
            v_home[j] = H_SLOT;
            if I.op == GIR_PHI { t_off[j] = new_slot(sz); }
        } else {
            v_home[j] = H_NONE;
        }
    }
    return overaligned;
}

// The last use of value v (module reference) is at local position pos of
// the current block: give v its slot.
inline fn lay_use(v: u32, pos: u32) {
    if v >= f_first_inst && v < f_end_inst {  // an instruction of this function
        let mk = v_mark[v - f_first_inst] - lay_epoch;
        if mk != MK_SLOT && mk != MK_ALLOCA { lay_last_use(v, pos, mk); }
    }
}
// (v has no slot yet: this is its last use)
fn lay_last_use(v: u32, pos: u32, mk: u32) {
    let u = v - f_first_inst;
    if mk == MK_DEF {
        lay_conflict = true;  // used above its definition
        return;
    }
    v_mark[u] = lay_epoch + MK_SLOT;
    let sz = val_slot_size(M.insts[v].ty);
    if v < lay_lo {
        v_span[u] = SPAN_ALL;
        v_off[u] = new_slot(sz);
        return;
    }
    v_span[u] = pos - u;
    if sz == 8 && n_free8 != 0 {
        n_free8--;
        v_off[u] = free8[n_free8];
    } else if sz == 16 && n_free16 != 0 {
        n_free16--;
        v_off[u] = free16[n_free16];
    } else {
        v_off[u] = new_slot(sz);
    }
}

// The definition of local value j: its slot is free above it.
fn lay_free(j: u32, sz: i64) {
    let o = v_off[j];
    if sz == 8 {
        if n_free8 < free8.len { free8[n_free8] = o; } else { free8.push(o); }
        n_free8++;
    } else if sz == 16 {
        if n_free16 < free16.len { free16[n_free16] = o; } else { free16.push(o); }
        n_free16++;
    }
}

// PHI incoming values of successor s for the edge from block `from`: read by
// phi_moves at from's terminator (position pos).
fn lay_phi_uses(s: u32, from: u32, pos: u32) {
    let B = M.blocks[f_first_block + s];
    for k in B.first_inst..B.first_inst + B.n_inst {
        let I = M.insts[k];
        if I.op != GIR_PHI { break; }
        for p in 0..I.c {
            if M.opnds[I.b + 2 * p + 1] == from {
                lay_use(M.opnds[I.b + 2 * p], pos);
                break;
            }
        }
    }
}

fn lay_runs(I: Inst, m: u32, pos: u32) {
    if m & U_GEP != 0 {
        for k in 0..I.c { lay_use(M.opnds[I.b + 2 + 2 * k], pos); }
    } else if m & U_CALL != 0 {
        for k in 0..I.c { lay_use(M.opnds[I.b + 2 * k], pos); }
    } else {
        let A = M.asms[I.a];
        for q in 0..A.n_in { lay_use(M.opnds[A.ops + 2 * q], pos); }
    }
}

// Slot-sharing layout. Returns (ok, overaligned); not ok: a use above its
// definition was found (the caller lays the function out again).
fn layout_shared(insts: const Inst[:], blocks: const Block[:]) -> bool, bool {
    lay_epoch += 4;
    lay_conflict = false;
    n_free8 = 0;
    n_free16 = 0;
    // allocas first (entry block only), so that their uses are ignored
    var overaligned = false;
    let E = blocks[0];
    for gi in E.first_inst..E.first_inst + E.n_inst {
        let I = M.insts[gi];
        if I.op != GIR_ALLOCA { continue; }
        let j = gi - f_first_inst;
        if layout_alloca(I, j) { overaligned = true; }
        v_mark[j] = lay_epoch + MK_ALLOCA;
        v_span[j] = SPAN_ALL;
    }
    var b = blocks.len;
    while b > 0 {
        b--;
        let B = blocks[b];
        lay_lo = B.first_inst;
        var gi = B.first_inst + B.n_inst;
        while gi > B.first_inst {
            gi--;
            let I = M.insts[gi];
            let j = gi - f_first_inst;
            let op: u32 = I.op;
            // uses first: an operand never shares the result's slot
            let m: u32 = if op < 83 { OP_USES[op] } else { U_A | U_B | U_C };
            if m & U_A != 0 { lay_use(I.a, j); }
            if m & U_B != 0 { lay_use(I.b, j); }
            if m & U_C != 0 { lay_use(I.c, j); }
            if m >= U_GEP { lay_runs(I, m, j); }
            if op <= GIR_SWITCH || op == GIR_INDIRECTBR {
                let bu = b as! u32;
                if op == GIR_BR { lay_phi_uses(I.a, bu, j); }
                else if op == GIR_CONDBR {
                    lay_phi_uses(I.b, bu, j);
                    lay_phi_uses(I.c, bu, j);
                } else if op == GIR_SWITCH {
                    lay_phi_uses(M.opnds[I.b], bu, j);
                    for k in 0..I.c { lay_phi_uses(M.opnds[I.b + 2 + 2 * k], bu, j); }
                } else if op == GIR_INDIRECTBR {
                    for k in 0..I.c { lay_phi_uses(M.opnds[I.b + k], bu, j); }
                }
            }
            // the definition
            if op == GIR_ALLOCA {
                if v_mark[j] != lay_epoch + MK_ALLOCA { lay_conflict = true; }  // not in the entry block
            } else if I.ty != GIR_T_VOID {
                let sz = val_slot_size(I.ty);
                if v_mark[j] != lay_epoch + MK_SLOT {
                    // never used: a slot for the store only
                    lay_lo = B.first_inst;
                    lay_use(gi, j);
                }
                if v_span[j] != SPAN_ALL { lay_free(j, sz); }
                v_mark[j] = lay_epoch + MK_DEF;
                v_home[j] = H_SLOT;
                if op == GIR_PHI { t_off[j] = new_slot(sz); }
            } else {
                v_home[j] = H_NONE;
            }
        }
    }
    return !lay_conflict, overaligned;
}

// --------------------------------------------------------------- functions


fn gen_function(fi: u32) {
    let f = M.funcs[fi];
    let falign: u32 = (1 as u32) << (f.flags >> FN_ALIGN_SHIFT);
    if falign > osecs[cur_code_sec].align { osecs[cur_code_sec].align = falign; }
    while code.len & (falign - 1) != 0 { b1(0xCC); }
    let start = here();
    f_first_inst = f.first_inst;
    f_first_block = f.first_block;
    f_args = f.args;
    f_nargs = f.n_args;
    f_index = fi;
    f_sjlj = f.flags & FN_SJLJ != 0;

    let insts = M.insts[f.first_inst..f.first_inst + f.n_inst];
    let blocks = M.blocks[f.first_block..f.first_block + f.n_blocks];

    // Frame layout. `off` counts bytes below rbp: callee-saved registers
    // (sjlj), scratch, the va register save area, argument slots, then one
    // home per instruction result and alloca areas at their alignment.
    var off: i64 = 0;
    if f_sjlj { off = 48; }
    off = (off + 32 + 15) & ~15;
    scratch_off = (-off) as! i32;
    if f.flags & FN_VASTART != 0 {
        off = (off + 176 + 15) & ~15;
        rsa_off = (-off) as! i32;
    }
    if a_off.len < f.n_args {
        a_off.resize(f.n_args, 0);
        a_home.resize(f.n_args, 0);
    }
    for a in 0..f.n_args {
        let t = M.opnds[f.args + 2 * a];
        let al = slot_align(t);
        off = (off + slot_size(t) + al - 1) & ~(al - 1);  // al is a power of two (no division)
        a_off[a] = (-off) as! i32;
        a_home[a] = A_SLOT;
    }
    if v_off.len < f.n_inst {
        v_off.resize(f.n_inst, 0);
        v_home.resize(f.n_inst, 0);
        t_off.resize(f.n_inst, 0);
        v_span.resize(f.n_inst, 0);
        v_mark.resize(f.n_inst, 0);
    }
    assert(v_off.len >= insts.len && v_home.len >= insts.len && t_off.len >= insts.len);
    assert(v_span.len >= insts.len && v_mark.len >= insts.len);
    f_end_inst = f.first_inst + f.n_inst;
    lay_off = off;
    var ok = false;
    var overaligned = false;
    if f.n_inst > SHARE_MIN_INSTS && f.flags & (FN_SJLJ | FN_RETURNS_TWICE) == 0 {
        let ok1, ov1 = layout_shared(insts, blocks);
        ok = ok1;
        overaligned = ov1;
    }
    f_shared = ok;
    if !ok {
        lay_off = off;
        overaligned = layout_unique(insts);
    }
    off = lay_off;
    let frame: i64 = (off + 15) & ~15;
    if frame > 0x7FFFFFF0 { assert(false); }

    // Prologue: push rbp; mov rbp, rsp; sub rsp, frame; save registers; spill arguments.
    b1(0x55);
    b1(0x48);
    b1(0x89);
    b1(0xE5);
    if frame != 0 { grp1_ri64(G1_SUB, RSP, frame as! i32); }
    if f_sjlj {
        store64(m_rbp(-8), RBX);
        store64(m_rbp(-16), R12);
        store64(m_rbp(-24), R13);
        store64(m_rbp(-32), R14);
        store64(m_rbp(-40), R15);
    }
    if f.flags & FN_VASTART != 0 { save_va_regs(); }
    spill_args();
    if overaligned {
        for I, j in insts {
            if I.op != GIR_ALLOCA || v_home[j] != H_PTR { continue; }
            let al: i64 = I.b;
            lea64(RAX, m_rbp(t_off[j]));
            grp1_ri64(G1_ADD, RAX, (al - 1) as! i32);
            grp1_ri64(G1_AND, RAX, (0 - al) as! i32);
            store64(m_rbp(v_off[j]), RAX);
        }
    }

    if block_off.len < f.n_blocks { block_off.resize(f.n_blocks, 0); }
    assert(block_off.len >= blocks.len);
    fixups.clear();
    for B, b in blocks {
        block_off[b] = here();
        blk_code[f.first_block + b] = here();
        for k in B.first_inst..B.first_inst + B.n_inst { gen_inst(k, b as! u32); }
    }
    for x in fixups {
        patch4(x.pos, block_off[x.blk] - (x.pos + 4));
    }

    g_value[f.global] = start - osecs[cur_code_sec].start;
    g_size[f.global] = here() - start;
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
        while code.len % 16 != 0 { b1(0xCC); }
        osecs[s].start = code.len as u64;
        for F, fi in M.funcs {
            if g_sec[F.global] != s { continue; }
            gen_function(fi as! u32);
            k++;
        }
        osecs[s].size = code.len as u64 - osecs[s].start;
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
    blk_code.clear();
    blk_code.resize(blocks.len, 0);
    make_sections();
    layout_globals();
    gen_functions();
    resolve_blockaddrs();
    resolve_aliases();
    write_elf(obj);
    return obj;
}
