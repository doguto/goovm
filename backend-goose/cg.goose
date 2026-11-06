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
            let c = cls_of(I.ty);
            if c == C_INT {
                let bits = bits_of(I.ty);
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
        _ => ud2(),  // unknown opcode: trap
    }
}

// --------------------------------------------------------------- functions

checkfree fn align_down(off: i64, al: i64) -> i64 { off / al * al }

fn gen_function(fi: u32) {
    let f = M.funcs[fi];
    let falign: u32 = (1 as u32) << (f.flags >> FN_ALIGN_SHIFT);
    if falign > osecs[cur_code_sec].align { osecs[cur_code_sec].align = falign; }
    while code.len % falign != 0 { b1(0xCC); }
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
        off = (off + slot_size(t) + al - 1) / al * al;
        a_off[a] = (-off) as! i32;
        a_home[a] = A_SLOT;
    }
    if v_off.len < f.n_inst {
        v_off.resize(f.n_inst, 0);
        v_home.resize(f.n_inst, 0);
        t_off.resize(f.n_inst, 0);
    }
    assert(v_off.len >= insts.len && v_home.len >= insts.len && t_off.len >= insts.len);
    var overaligned = false;
    for I, j in insts {
        if I.op == GIR_ALLOCA {
            let al: i64 = if I.b != 0 { I.b } else { 1 };
            let size: i64 = if I.a != 0 { I.a } else { 1 };
            if al <= 16 {
                off = (off + size + al - 1) / al * al;
                v_off[j] = (-off) as! i32;
                v_home[j] = H_ALLOCA;
            } else {
                // area of size + al bytes, aligned at run time; the pointer gets a slot
                off = (off + size + al + 15) & ~15;
                t_off[j] = (-off) as! i32;
                off = ((off + 7) & ~7) + 8;
                v_off[j] = (-off) as! i32;
                v_home[j] = H_PTR;
                overaligned = true;
            }
        } else if I.ty != GIR_T_VOID {
            let al = slot_align(I.ty);
            off = (off + slot_size(I.ty) + al - 1) / al * al;
            v_off[j] = (-off) as! i32;
            v_home[j] = H_SLOT;
            if I.op == GIR_PHI {
                off = (off + slot_size(I.ty) + al - 1) / al * al;
                t_off[j] = (-off) as! i32;
            }
        } else {
            v_home[j] = H_NONE;
        }
    }
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
                      dscopes: const DScope[:], dfiles: const DFile[:], dstr: const u8[:]) -> const u8[:] {
    M = Module { header: header, types: types, funcs: funcs, blocks: blocks, insts: insts, opnds: opnds,
                 consts: consts, globals: globals, sections: sections, data: data, drelocs: drelocs,
                 strtab: strtab, dlocs: dlocs, dscopes: dscopes, dfiles: dfiles, dstr: dstr };
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
