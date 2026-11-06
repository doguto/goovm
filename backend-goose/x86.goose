// x86-64 machine code: byte output, memory operands and the instruction
// encoder (general registers, SSE2, x87). Everything here appends to
// `code`, the current function's buffer (gen_function copies it into the
// module's code after the prologue), and records relocations of rip-relative
// operands in `rela_code` at function-relative offsets.
// The functions are `checkfree`: the compiler verifies that no bounds check
// is left in them.

// Register numbers (ModRM/REX encoding). XMM registers use the same numbers.
let RAX = 0;
let RCX = 1;
let RDX = 2;
let RBX = 3;
let RSP = 4;
let RBP = 5;
let RSI = 6;
let RDI = 7;
let R8 = 8;
let R9 = 9;
let R10 = 10;
let R11 = 11;
let R12 = 12;
let R13 = 13;
let R14 = 14;
let R15 = 15;
let XMM0 = 0;
let XMM1 = 1;
let XMM2 = 2;
let XMM3 = 3;

// Condition codes: low nibble of Jcc (0F 80+cc), SETcc (0F 90+cc), CMOVcc (0F 40+cc).
let CC_O = 0x0;
let CC_NO = 0x1;
let CC_B = 0x2;
let CC_AE = 0x3;
let CC_E = 0x4;
let CC_NE = 0x5;
let CC_BE = 0x6;
let CC_A = 0x7;
let CC_S = 0x8;
let CC_NS = 0x9;
let CC_P = 0xA;
let CC_NP = 0xB;
let CC_L = 0xC;
let CC_GE = 0xD;
let CC_LE = 0xE;
let CC_G = 0xF;

// ALU opcodes, "op r/m, r" form (+2: "op r, r/m").
let ALU_ADD = 0x01;
let ALU_OR = 0x09;
let ALU_ADC = 0x11;
let ALU_SBB = 0x19;
let ALU_AND = 0x21;
let ALU_SUB = 0x29;
let ALU_XOR = 0x31;
let ALU_CMP = 0x39;
// Group-1 (81 /ext, 83 /ext) and shift (C1/D3 /ext) extensions.
let G1_ADD = 0;
let G1_OR = 1;
let G1_AND = 4;
let G1_SUB = 5;
let G1_XOR = 6;
let G1_CMP = 7;
let SH_ROL = 0;
let SH_ROR = 1;
let SH_SHL = 4;
let SH_SHR = 5;
let SH_SAR = 7;

// SSE prefixes.
let P_NONE = 0;
let P_66 = 0x66;
let P_F2 = 0xF2;
let P_F3 = 0xF3;

// ELF relocation types (x86-64).
let R_X86_64_64 = 1;
let R_X86_64_PC32 = 2;
let R_X86_64_PLT32 = 4;
let R_X86_64_TLSGD = 19;
let R_X86_64_GOTTPOFF = 22;
let R_X86_64_TPOFF32 = 23;
let R_X86_64_REX_GOTPCRELX = 42;

// Memory operand: [reg + disp], [reg + idx * 2^sh + disp] (M_SIB: rtype =
// idx | sh << 8), or [rip + symbol + disp] (relocation of type rtype against
// ELF symbol sym, addend disp - 4 - bytes after the displacement).
let M_REG = 1;
let M_SIB = 2;
let M_RIP = 3;
struct Mem { kind: u8, reg: u8, rtype: u16, disp: i32, sym: u32 }

struct Rela { offset: u64, info: u64, addend: i64, sec: u32 }  // info = (symbol << 32) | type; sec: code section (set when placed)

// rel32 at code[pos] -> start of local block `blk`.
struct Fixup { pos: u32, blk: u32 }

var code: u8[>..] = [];        // the current function's code (prologue last)
var rela_code: Rela[>..] = []; // relocations in code (function-relative until the function is placed)
var fixups: Fixup[>..] = [];   // per function
// Code offset of each local block that has been emitted (and of the epilogue,
// block n_blocks); blocks are emitted in order, so a block b <= cur_blk is
// placed and branches to it can be short.
var block_off: u32[>..] = [];
var cur_blk: u32 = 0;

// ----------------------------------------------------------------- byte output

checkfree fn b1(x: u32) { code.push(x as! u8); }
checkfree fn b2(x: u32) {
    b1(x);
    b1(x >> 8);
}
checkfree fn b4(x: u32) {
    b1(x);
    b1(x >> 8);
    b1(x >> 16);
    b1(x >> 24);
}
checkfree fn b8(x: u64) {
    b4(x as! u32);
    b4((x >> 32) as! u32);
}
fn patch4(pos: u32, x: u32) {
    let p: i64 = pos;
    let w = code[p..p + 4];
    w[0] = x as! u8;
    w[1] = (x >> 8) as! u8;
    w[2] = (x >> 16) as! u8;
    w[3] = (x >> 24) as! u8;
}
fn patch1(pos: u32, x: u32) {
    let p: i64 = pos;
    let w = code[p..p + 1];
    w[0] = x as! u8;
}
checkfree fn here() -> u32 { code.len as! u32 }

checkfree fn fits8(v: i64) -> bool { v >= -128 && v <= 127 }
checkfree fn fits32(v: i64) -> bool { v >= -2147483648 && v <= 2147483647 }

// ------------------------------------------------------------------ encoder

// REX prefix: w = 64-bit operand size, reg = ModRM.reg register, rm = ModRM.rm
// (or base) register. `force` emits a bare REX (0x40), needed to address
// spl/bpl/sil/dil as byte registers.
checkfree fn rex(w: u32, reg: u32, rm: u32, force: bool) {
    let r: u32 = 0x40 | (w << 3) | ((reg >> 3) << 2) | (rm >> 3);
    if r != 0x40 || force { b1(r); }
}
// One- or two-byte opcode (0x0FB6 = 0F B6), or three bytes (0x0F38xx).
checkfree fn opc(op: u32) {
    if op > 0xFFFF { b1(op >> 16); }
    if op > 0xFF { b1((op >> 8) & 0xFF); }
    b1(op & 0xFF);
}
checkfree fn rela(off: u32, sym: u32, typ: u32, addend: i64) {
    rela_code.push(Rela { offset: off, info: (sym as u64 << 32) | typ, addend: addend, sec: 0 });
}
// ModRM (+ SIB + displacement) for `reg` and memory operand x; `tail` is the
// number of immediate bytes that follow (for the rip-relative addend).
checkfree fn modrm_mem(reg: u32, x: Mem, tail: u32) {
    let r: u32 = (reg & 7) << 3;
    if x.kind == M_RIP {
        b1(r | 5);
        rela(here(), x.sym, x.rtype, x.disp as i64 - 4 - tail);
        b4(0);
        return;
    }
    let base: u32 = x.reg & 7;
    var md: u32 = 2;
    if x.disp == 0 && base != 5 { md = 0; }
    else if fits8(x.disp) { md = 1; }
    if x.kind == M_SIB {
        let idx: u32 = x.rtype & 7;
        let sh: u32 = (x.rtype >> 8) & 3;
        b1((md << 6) | r | 4);
        b1((sh << 6) | (idx << 3) | base);
    } else if base == 4 {
        b1((md << 6) | r | 4);
        b1(0x24);
    } else {
        b1((md << 6) | r | base);
    }
    if md == 1 { b1(x.disp as! u32); }
    else if md == 2 { b4(x.disp as! u32); }
}
// [prefix] [REX] opcode ModRM(reg, mem) [tail immediate follows].
// byte_reg: `reg` is an 8-bit register.
checkfree fn op_mem_t(pfx: u32, w: u32, op: u32, reg: u32, x: Mem, byte_reg: bool, tail: u32) {
    if pfx != 0 { b1(pfx); }
    if x.kind == M_REG && x.reg == RBP {
        // Fast path for frame slots, by far the most common operand.
        let rx: u32 = 0x40 | (w << 3) | ((reg >> 3) << 2);
        if rx != 0x40 || (byte_reg && reg >= 4 && reg < 8) { b1(rx); }
        opc(op);
        let r: u32 = (reg & 7) << 3;
        if fits8(x.disp) {
            b1(0x45 | r);
            b1(x.disp as! u32);
        } else {
            b1(0x85 | r);
            b4(x.disp as! u32);
        }
        return;
    }
    var rb: u32 = 0;
    var xb: u32 = 0;
    if x.kind != M_RIP { rb = x.reg; }
    if x.kind == M_SIB { xb = (x.rtype >> 3) & 1; }
    let rx: u32 = 0x40 | (w << 3) | ((reg >> 3) << 2) | (xb << 1) | (rb >> 3);
    if rx != 0x40 || (byte_reg && reg >= 4 && reg < 8) { b1(rx); }
    opc(op);
    modrm_mem(reg, x, tail);
}
checkfree fn op_mem(pfx: u32, w: u32, op: u32, reg: u32, x: Mem, byte_reg: bool) {
    op_mem_t(pfx, w, op, reg, x, byte_reg, 0);
}
// [prefix] [REX] opcode ModRM(11, reg, rm). force: see rex().
checkfree fn op_rr_p(pfx: u32, w: u32, op: u32, reg: u32, rm: u32, force: bool) {
    if pfx != 0 { b1(pfx); }
    rex(w, reg, rm, force);
    opc(op);
    b1(0xC0 | ((reg & 7) << 3) | (rm & 7));
}
checkfree fn op_rr(w: u32, op: u32, reg: u32, rm: u32, force: bool) { op_rr_p(0, w, op, reg, rm, force); }

checkfree fn m_reg(r: u32, disp: i32) -> Mem { Mem { M_REG, r as! u8, 0, disp, 0 } }
checkfree fn m_rbp(disp: i32) -> Mem { Mem { M_REG, RBP, 0, disp, 0 } }
checkfree fn m_rsp(disp: i32) -> Mem { Mem { M_REG, RSP, 0, disp, 0 } }
checkfree fn m_sym(sym: u32, rtype: u32, disp: i32) -> Mem { Mem { M_RIP, 0, rtype as! u16, disp, sym } }
checkfree fn m_sib(base: u32, idx: u32, sh: u32, disp: i32) -> Mem {
    Mem { M_SIB, base as! u8, (idx | (sh << 8)) as! u16, disp, 0 }
}
// x + d bytes.
checkfree fn m_add(x: Mem, d: i64) -> Mem {
    var y = x;
    y.disp = (x.disp + d) as! i32;
    return y;
}
// The registers a memory operand reads (bit mask).
checkfree fn m_regs(x: Mem) -> u32 {
    if x.kind == M_RIP { return 0; }
    var m: u32 = (1 as u32) << (x.reg & 15);
    if x.kind == M_SIB { m |= (1 as u32) << (x.rtype & 15); }
    return m;
}

// --- general-register moves
checkfree fn load64(r: u32, x: Mem) { op_mem(0, 1, 0x8B, r, x, false); }   // mov r64, [m]
checkfree fn store64(x: Mem, r: u32) { op_mem(0, 1, 0x89, r, x, false); }  // mov [m], r64
checkfree fn lea64(r: u32, x: Mem) { op_mem(0, 1, 0x8D, r, x, false); }    // lea r64, [m]
checkfree fn lea32(r: u32, x: Mem) { op_mem(0, 0, 0x8D, r, x, false); }    // lea r32, [m]
checkfree fn load32(r: u32, x: Mem) { op_mem(0, 0, 0x8B, r, x, false); }   // mov r32, [m] (zero-extends)
checkfree fn store32(x: Mem, r: u32) { op_mem(0, 0, 0x89, r, x, false); }
checkfree fn load16z(r: u32, x: Mem) { op_mem(0, 0, 0x0FB7, r, x, false); } // movzx r32, word [m]
checkfree fn load8z(r: u32, x: Mem) { op_mem(0, 0, 0x0FB6, r, x, false); }  // movzx r32, byte [m]
checkfree fn store16(x: Mem, r: u32) { op_mem(P_66, 0, 0x89, r, x, false); }
checkfree fn store8(x: Mem, r: u32) { op_mem(0, 0, 0x88, r, x, true); }
checkfree fn load8s(w: u32, r: u32, x: Mem) { op_mem(0, w, 0x0FBE, r, x, false); }  // movsx r, byte [m]
checkfree fn load16s(w: u32, r: u32, x: Mem) { op_mem(0, w, 0x0FBF, r, x, false); } // movsx r, word [m]
checkfree fn load32s(r: u32, x: Mem) { op_mem(0, 1, 0x63, r, x, false); }          // movsxd r64, dword [m]
// mov qword/dword [m], simm32
checkfree fn store_imm64(x: Mem, v: i32) {
    op_mem_t(0, 1, 0xC7, 0, x, false, 4);
    b4(v as! u32);
}
checkfree fn store_imm32(x: Mem, v: u32) {
    op_mem_t(0, 0, 0xC7, 0, x, false, 4);
    b4(v);
}
checkfree fn store_imm16(x: Mem, v: u32) {
    op_mem_t(P_66, 0, 0xC7, 0, x, false, 2);
    b2(v);
}
checkfree fn store_imm8(x: Mem, v: u32) {
    op_mem_t(0, 0, 0xC6, 0, x, false, 1);
    b1(v);
}
checkfree fn mov_rr64(d: u32, s: u32) { op_rr(1, 0x89, s, d, false); }
checkfree fn mov_rr32(d: u32, s: u32) { op_rr(0, 0x89, s, d, false); }
checkfree fn mov_rr(w: u32, d: u32, s: u32) { op_rr(w, 0x89, s, d, false); }
checkfree fn alu_rr64(op: u32, d: u32, s: u32) { op_rr(1, op, s, d, false); }
checkfree fn alu_rr32(op: u32, d: u32, s: u32) { op_rr(0, op, s, d, false); }
checkfree fn alu_rr(w: u32, op: u32, d: u32, s: u32) { op_rr(w, op, s, d, false); }
checkfree fn alu_rr8(op: u32, d: u32, s: u32) { op_rr(0, op - 1, s, d, s >= 4 && s < 8 || d >= 4 && d < 8); }
checkfree fn alu_rr16(op: u32, d: u32, s: u32) { op_rr_p(P_66, 0, op, s, d, false); }
// op r, [m] and op [m], r (w: 0 = 32-bit, 1 = 64-bit)
checkfree fn alu_rm(w: u32, op: u32, r: u32, x: Mem) { op_mem(0, w, op + 2, r, x, false); }
checkfree fn alu_mr(w: u32, op: u32, x: Mem, r: u32) { op_mem(0, w, op, r, x, false); }
checkfree fn alu_mr8(op: u32, x: Mem, r: u32) { op_mem(0, 0, op - 1, r, x, true); }
checkfree fn alu_mr16(op: u32, x: Mem, r: u32) { op_mem(P_66, 0, op, r, x, false); }
checkfree fn imul_rr64(d: u32, s: u32) { op_rr(1, 0x0FAF, d, s, false); }
checkfree fn imul_rr(w: u32, d: u32, s: u32) { op_rr(w, 0x0FAF, d, s, false); }
checkfree fn imul_rm(w: u32, d: u32, x: Mem) { op_mem(0, w, 0x0FAF, d, x, false); }
checkfree fn imul_rri64(d: u32, s: u32, imm: i32) {
    op_rr(1, 0x69, d, s, false);
    b4(imm as! u32);
}
checkfree fn imul_rmi(w: u32, d: u32, x: Mem, imm: i32) {
    if fits8(imm) {
        op_mem_t(0, w, 0x6B, d, x, false, 1);
        b1(imm as! u32);
    } else {
        op_mem_t(0, w, 0x69, d, x, false, 4);
        b4(imm as! u32);
    }
}
checkfree fn imul_rri(w: u32, d: u32, s: u32, imm: i32) {
    if fits8(imm) {
        op_rr(w, 0x6B, d, s, false);
        b1(imm as! u32);
    } else {
        op_rr(w, 0x69, d, s, false);
        b4(imm as! u32);
    }
}
checkfree fn grp1_ri64(ext: u32, r: u32, imm: i32) {
    if fits8(imm) {
        op_rr(1, 0x83, ext, r, false);
        b1(imm as! u32);
    } else {
        op_rr(1, 0x81, ext, r, false);
        b4(imm as! u32);
    }
}
checkfree fn grp1_ri32(ext: u32, r: u32, imm: u32) {
    if imm < 0x80 || imm >= 0xFFFFFF80 {
        op_rr(0, 0x83, ext, r, false);
        b1(imm);
    } else {
        op_rr(0, 0x81, ext, r, false);
        b4(imm);
    }
}
checkfree fn grp1_ri(w: u32, ext: u32, r: u32, imm: i32) {
    if w != 0 { grp1_ri64(ext, r, imm); } else { grp1_ri32(ext, r, imm as! u32); }
}
// op [m], imm at operand size n bytes (1, 2, 4, 8; 8: simm32)
checkfree fn grp1_mi(n: u32, ext: u32, x: Mem, imm: i32) {
    if n == 1 {
        op_mem_t(0, 0, 0x80, ext, x, false, 1);
        b1(imm as! u32);
        return;
    }
    let w: u32 = if n == 8 { 1 } else { 0 };
    let p: u32 = if n == 2 { P_66 } else { 0 };
    if fits8(imm) {
        op_mem_t(p, w, 0x83, ext, x, false, 1);
        b1(imm as! u32);
    } else if n == 2 {
        op_mem_t(p, w, 0x81, ext, x, false, 2);
        b2(imm as! u32);
    } else {
        op_mem_t(p, w, 0x81, ext, x, false, 4);
        b4(imm as! u32);
    }
}
// cmp r8, imm8 / cmp r16, imm
checkfree fn cmp8_ri(r: u32, imm: u32) {
    op_rr(0, 0x80, 7, r, r >= 4 && r < 8);
    b1(imm);
}
checkfree fn cmp16_ri(r: u32, imm: u32) {
    if imm < 0x80 || (imm >= 0xFF80 && imm <= 0xFFFF) {
        op_rr_p(P_66, 0, 0x83, 7, r, false);
        b1(imm);
    } else {
        op_rr_p(P_66, 0, 0x81, 7, r, false);
        b2(imm);
    }
}
checkfree fn test_rr8(a: u32, b: u32) { op_rr(0, 0x84, b, a, a >= 4 && a < 8 || b >= 4 && b < 8); }
checkfree fn test_rr16(a: u32, b: u32) { op_rr_p(P_66, 0, 0x85, b, a, false); }
checkfree fn shift_cl64(ext: u32, r: u32) { op_rr(1, 0xD3, ext, r, false); }
checkfree fn shift_cl(w: u32, ext: u32, r: u32) { op_rr(w, 0xD3, ext, r, false); }
checkfree fn shift_imm64(ext: u32, r: u32, n: u32) {
    op_rr(1, 0xC1, ext, r, false);
    b1(n);
}
checkfree fn shift_imm32(ext: u32, r: u32, n: u32) {
    op_rr(0, 0xC1, ext, r, false);
    b1(n);
}
checkfree fn shift_imm(w: u32, ext: u32, r: u32, n: u32) {
    if n == 1 { op_rr(w, 0xD1, ext, r, false); return; }
    op_rr(w, 0xC1, ext, r, false);
    b1(n);
}
checkfree fn shld_cl64(d: u32, s: u32) { op_rr(1, 0x0FA5, s, d, false); }  // shld d, s, cl
checkfree fn shrd_cl64(d: u32, s: u32) { op_rr(1, 0x0FAD, s, d, false); }  // shrd d, s, cl
checkfree fn and_ri32(r: u32, imm8: u32) {
    op_rr(0, 0x83, 4, r, false);
    b1(imm8);
}
checkfree fn neg64(r: u32) { op_rr(1, 0xF7, 3, r, false); }
checkfree fn not64(r: u32) { op_rr(1, 0xF7, 2, r, false); }
checkfree fn neg_r(w: u32, r: u32) { op_rr(w, 0xF7, 3, r, false); }
checkfree fn not_r(w: u32, r: u32) { op_rr(w, 0xF7, 2, r, false); }
checkfree fn div64(ext: u32, r: u32) { op_rr(1, 0xF7, ext, r, false); }  // 4 = mul, 6 = div, 7 = idiv
checkfree fn div_r(w: u32, ext: u32, r: u32) { op_rr(w, 0xF7, ext, r, false); }
checkfree fn div_m(w: u32, ext: u32, x: Mem) { op_mem(0, w, 0xF7, ext, x, false); }
checkfree fn cdq() { b1(0x99); }
checkfree fn cqo() { b1(0x48); b1(0x99); }
checkfree fn setcc(cc: u32, r: u32) { op_rr(0, 0x0F90 | cc, 0, r, r >= 4 && r < 8); }
checkfree fn movzx8(d: u32, s: u32) { op_rr(0, 0x0FB6, d, s, s >= 4 && s < 8); }
checkfree fn movzx16(d: u32, s: u32) { op_rr(0, 0x0FB7, d, s, false); }
checkfree fn movsx8_64(d: u32, s: u32) { op_rr(1, 0x0FBE, d, s, s >= 4 && s < 8); }
checkfree fn movsx16_64(d: u32, s: u32) { op_rr(1, 0x0FBF, d, s, false); }
checkfree fn movsx8(w: u32, d: u32, s: u32) { op_rr(w, 0x0FBE, d, s, s >= 4 && s < 8); }
checkfree fn movsx16(w: u32, d: u32, s: u32) { op_rr(w, 0x0FBF, d, s, false); }
checkfree fn movsxd(d: u32, s: u32) { op_rr(1, 0x63, d, s, false); }
checkfree fn test_rr32(a: u32, b: u32) { op_rr(0, 0x85, b, a, false); }
checkfree fn test_rr64(a: u32, b: u32) { op_rr(1, 0x85, b, a, false); }
checkfree fn test_rr(w: u32, a: u32, b: u32) { op_rr(w, 0x85, b, a, false); }
checkfree fn cmov64(cc: u32, d: u32, s: u32) { op_rr(1, 0x0F40 | cc, d, s, false); }
checkfree fn cmov_rm(cc: u32, d: u32, x: Mem) { op_mem(0, 1, 0x0F40 | cc, d, x, false); }
checkfree fn bsr64(d: u32, s: u32) { op_rr(1, 0x0FBD, d, s, false); }
checkfree fn bsf64(d: u32, s: u32) { op_rr(1, 0x0FBC, d, s, false); }
checkfree fn xchg_rr(a: u32, b: u32) { op_rr(1, 0x87, a, b, false); }
checkfree fn bswap64(r: u32) {
    rex(1, 0, r, false);
    b1(0x0F);
    b1(0xC8 | (r & 7));
}
checkfree fn bswap32(r: u32) {
    rex(0, 0, r, false);
    b1(0x0F);
    b1(0xC8 | (r & 7));
}
// bt/bts/btr/btc r64, imm8: ext 4/5/6/7
checkfree fn bt_ri64(ext: u32, r: u32, bit: u32) {
    op_rr(1, 0x0FBA, ext, r, false);
    b1(bit);
}
checkfree fn push_r(r: u32) {
    rex(0, 0, r, false);
    b1(0x50 | (r & 7));
}
checkfree fn pop_r(r: u32) {
    rex(0, 0, r, false);
    b1(0x58 | (r & 7));
}
checkfree fn mov_ri(r: u32, v: u64) {
    if v <= 0xFFFFFFFF {               // mov r32, imm32 (zero-extends)
        rex(0, 0, r, false);
        b1(0xB8 | (r & 7));
        b4(v as! u32);
    } else if fits32(v as! i64) {      // mov r64, simm32
        op_rr(1, 0xC7, 0, r, false);
        b4(v as! u32);
    } else {                           // movabs r64, imm64
        rex(1, 0, r, false);
        b1(0xB8 | (r & 7));
        b8(v);
    }
}
// Zeroes r32 with xor (clobbers the flags).
checkfree fn zero_r(r: u32) { op_rr(0, ALU_XOR, r, r, false); }
checkfree fn rep_movsb() { b1(0xF3); b1(0xA4); }
checkfree fn rep_stosb() { b1(0xF3); b1(0xAA); }
checkfree fn ud2() { b1(0x0F); b1(0x0B); }
checkfree fn call_r(r: u32) { op_rr(0, 0xFF, 2, r, false); }
checkfree fn jmp_r(r: u32) { op_rr(0, 0xFF, 4, r, false); }
// lea r64, [rip + disp32] to a place in this function's code (a jump table);
// returns the disp32 position for patch_here.
checkfree fn lea_here(r: u32) -> u32 {
    rex(1, r, 0, false);
    b1(0x8D);
    b1(0x05 | ((r & 7) << 3));
    let p = here();
    b4(0);
    return p;
}
checkfree fn mfence() { b1(0x0F); b1(0xAE); b1(0xF0); }

// --- SSE (registers xmm0..15 use the GPR numbering)
checkfree fn sse_rm(pfx: u32, w: u32, op: u32, x: u32, m: Mem) { op_mem(pfx, w, op, x, m, false); }
checkfree fn sse_rr(pfx: u32, w: u32, op: u32, d: u32, s: u32) { op_rr_p(pfx, w, op, d, s, false); }
checkfree fn movss_load(x: u32, m: Mem) { sse_rm(P_F3, 0, 0x0F10, x, m); }
checkfree fn movss_store(m: Mem, x: u32) { sse_rm(P_F3, 0, 0x0F11, x, m); }
checkfree fn movsd_load(x: u32, m: Mem) { sse_rm(P_F2, 0, 0x0F10, x, m); }
checkfree fn movsd_store(m: Mem, x: u32) { sse_rm(P_F2, 0, 0x0F11, x, m); }
checkfree fn movups_load(x: u32, m: Mem) { sse_rm(P_NONE, 0, 0x0F10, x, m); }
checkfree fn movups_store(m: Mem, x: u32) { sse_rm(P_NONE, 0, 0x0F11, x, m); }
checkfree fn movq_load(x: u32, m: Mem) { sse_rm(P_F3, 0, 0x0F7E, x, m); }   // movq xmm, m64
checkfree fn movq_store(m: Mem, x: u32) { sse_rm(P_66, 0, 0x0FD6, x, m); }  // movq m64, xmm
checkfree fn movd_load(x: u32, m: Mem) { sse_rm(P_66, 0, 0x0F6E, x, m); }   // movd xmm, m32
checkfree fn movd_store(m: Mem, x: u32) { sse_rm(P_66, 0, 0x0F7E, x, m); }  // movd m32, xmm
checkfree fn movq_xr(x: u32, r: u32) { sse_rr(P_66, 1, 0x0F6E, x, r); }     // movq xmm, r64
checkfree fn movq_rx(r: u32, x: u32) { sse_rr(P_66, 1, 0x0F7E, x, r); }     // movq r64, xmm
checkfree fn movd_xr(x: u32, r: u32) { sse_rr(P_66, 0, 0x0F6E, x, r); }     // movd xmm, r32
checkfree fn movd_rx(r: u32, x: u32) { sse_rr(P_66, 0, 0x0F7E, x, r); }     // movd r32, xmm
checkfree fn movaps_rr(d: u32, s: u32) { sse_rr(P_NONE, 0, 0x0F28, d, s); }  // full register copy
checkfree fn movss_rr(d: u32, s: u32) { sse_rr(P_F3, 0, 0x0F10, d, s); }     // d.lane0 = s.lane0
checkfree fn movsd_rr(d: u32, s: u32) { sse_rr(P_F2, 0, 0x0F10, d, s); }
checkfree fn xorps_rr(d: u32, s: u32) { sse_rr(P_NONE, 0, 0x0F57, d, s); }
checkfree fn shufps(d: u32, s: u32, imm: u32) {
    sse_rr(P_NONE, 0, 0x0FC6, d, s);
    b1(imm);
}
// Packed ops (op: 0x58 add, 0x59 mul, 0x5C sub, 0x5E div, 0x54 and, 0x55 andn, 0x56 or, 0x57 xor,
// 0x14 unpckl, 0x15 unpckh, 0x5F max, 0x5D min); dbl selects the pd forms.
checkfree fn sse_packed(op: u32, dbl: bool, d: u32, s: u32) {
    sse_rr(if dbl { P_66 } else { P_NONE }, 0, 0x0F00 | op, d, s);
}
checkfree fn sse_packed_m(op: u32, dbl: bool, d: u32, m: Mem) {
    sse_rm(if dbl { P_66 } else { P_NONE }, 0, 0x0F00 | op, d, m);
}
checkfree fn pshufd(d: u32, s: u32, imm: u32) {
    sse_rr(P_66, 0, 0x0F70, d, s);
    b1(imm);
}
checkfree fn pinsrw(x: u32, r: u32, k: u32) {   // x.word[k] = r
    sse_rr(P_66, 0, 0x0FC4, x, r);
    b1(k);
}
checkfree fn pextrw(r: u32, x: u32, k: u32) {   // r = zext(x.word[k])
    sse_rr(P_66, 0, 0x0FC5, r, x);
    b1(k);
}
// Packed integer op 66 0F op /r (paddd 0xFE, psubd 0xFA, ...).
checkfree fn sse_pint(op: u32, d: u32, s: u32) { sse_rr(P_66, 0, 0x0F00 | op, d, s); }
// Scalar arithmetic: op 0x58 add, 0x59 mul, 0x5C sub, 0x5E div, 0x51 sqrt; dbl selects sd.
checkfree fn sse_arith(op: u32, dbl: bool, d: u32, s: u32) {
    sse_rr(if dbl { P_F2 } else { P_F3 }, 0, 0x0F00 | op, d, s);
}
checkfree fn sse_arith_m(op: u32, dbl: bool, d: u32, m: Mem) {
    sse_rm(if dbl { P_F2 } else { P_F3 }, 0, 0x0F00 | op, d, m);
}
checkfree fn ucomis(dbl: bool, a: u32, b: u32) { sse_rr(if dbl { P_66 } else { P_NONE }, 0, 0x0F2E, a, b); }
checkfree fn ucomis_m(dbl: bool, a: u32, m: Mem) { sse_rm(if dbl { P_66 } else { P_NONE }, 0, 0x0F2E, a, m); }
checkfree fn cvtsi2s(dbl: bool, w: u32, x: u32, r: u32) { sse_rr(if dbl { P_F2 } else { P_F3 }, w, 0x0F2A, x, r); }
checkfree fn cvtsi2s_m(dbl: bool, w: u32, x: u32, m: Mem) { sse_rm(if dbl { P_F2 } else { P_F3 }, w, 0x0F2A, x, m); }
checkfree fn cvtts2si(dbl: bool, w: u32, r: u32, x: u32) { sse_rr(if dbl { P_F2 } else { P_F3 }, w, 0x0F2C, r, x); }
checkfree fn cvtts2si_m(dbl: bool, w: u32, r: u32, m: Mem) { sse_rm(if dbl { P_F2 } else { P_F3 }, w, 0x0F2C, r, m); }
checkfree fn cvtss2sd(d: u32, s: u32) { sse_rr(P_F3, 0, 0x0F5A, d, s); }
checkfree fn cvtsd2ss(d: u32, s: u32) { sse_rr(P_F2, 0, 0x0F5A, d, s); }
checkfree fn cvtss2sd_m(d: u32, m: Mem) { sse_rm(P_F3, 0, 0x0F5A, d, m); }
checkfree fn cvtsd2ss_m(d: u32, m: Mem) { sse_rm(P_F2, 0, 0x0F5A, d, m); }

// --- x87
// fld/fstp of a float (4), double (8) or x86_fp80 (10) in memory.
checkfree fn fld_m(size: u32, m: Mem) {
    if size == 4 { op_mem(0, 0, 0xD9, 0, m, false); }
    else if size == 8 { op_mem(0, 0, 0xDD, 0, m, false); }
    else { op_mem(0, 0, 0xDB, 5, m, false); }
}
checkfree fn fstp_m(size: u32, m: Mem) {
    if size == 4 { op_mem(0, 0, 0xD9, 3, m, false); }
    else if size == 8 { op_mem(0, 0, 0xDD, 3, m, false); }
    else { op_mem(0, 0, 0xDB, 7, m, false); }
}
// fild/fistp of a 16-, 32- or 64-bit integer.
checkfree fn fild_m(size: u32, m: Mem) {
    if size == 2 { op_mem(0, 0, 0xDF, 0, m, false); }
    else if size == 4 { op_mem(0, 0, 0xDB, 0, m, false); }
    else { op_mem(0, 0, 0xDF, 5, m, false); }
}
checkfree fn fistp_m(size: u32, m: Mem) {
    if size == 2 { op_mem(0, 0, 0xDF, 3, m, false); }
    else if size == 4 { op_mem(0, 0, 0xDB, 3, m, false); }
    else { op_mem(0, 0, 0xDF, 7, m, false); }
}
checkfree fn fnstcw(m: Mem) { op_mem(0, 0, 0xD9, 7, m, false); }
checkfree fn fldcw(m: Mem) { op_mem(0, 0, 0xD9, 5, m, false); }
checkfree fn fadd_m32(m: Mem) { op_mem(0, 0, 0xD8, 0, m, false); }
checkfree fn x87_2(a: u32, b: u32) {  // a two-byte x87 instruction
    b1(a);
    b1(b);
}
let X87_FADDP = 0xC1;   // DE C1: st(1) = st(1) + st(0), pop
let X87_FMULP = 0xC9;   // DE C9
let X87_FSUBP = 0xE9;   // DE E9: st(1) = st(1) - st(0), pop
let X87_FDIVP = 0xF9;   // DE F9: st(1) = st(1) / st(0), pop
checkfree fn fop_p(op: u32) { x87_2(0xDE, op); }
checkfree fn fchs() { x87_2(0xD9, 0xE0); }
checkfree fn fabs_() { x87_2(0xD9, 0xE1); }
checkfree fn fsqrt() { x87_2(0xD9, 0xFA); }
checkfree fn fucomip() { x87_2(0xDF, 0xE9); }   // compare st(0) with st(1), set EFLAGS, pop
checkfree fn fstp_st0() { x87_2(0xDD, 0xD8); }  // pop
checkfree fn fxch() { x87_2(0xD9, 0xC9); }

// --- branches
// Branches to a block that is already placed (b <= cur_blk) are resolved
// at once, with rel8 where it fits; forward branches get a rel32 fixup.
fn jmp_block(b: u32) {
    if b <= cur_blk {
        let d: i64 = block_off[b] as i64 - here() - 2;
        if fits8(d) {
            b1(0xEB);
            b1(d as! u32);
        } else {
            b1(0xE9);
            b4((d - 3) as! u32);
        }
        return;
    }
    b1(0xE9);
    fixups.push(Fixup { pos: here(), blk: b });
    b4(0);
}
fn jcc_block(cc: u32, b: u32) {
    if b <= cur_blk {
        let d: i64 = block_off[b] as i64 - here() - 2;
        if fits8(d) {
            b1(0x70 | cc);
            b1(d as! u32);
        } else {
            b1(0x0F);
            b1(0x80 | cc);
            b4((d - 4) as! u32);
        }
        return;
    }
    b1(0x0F);
    b1(0x80 | cc);
    fixups.push(Fixup { pos: here(), blk: b });
    b4(0);
}
// Forward jcc/jmp to a label inside the current instruction; returns the
// rel32 position for patch_here().
checkfree fn jcc_fwd(cc: u32) -> u32 {
    b1(0x0F);
    b1(0x80 | cc);
    let p = here();
    b4(0);
    return p;
}
checkfree fn jmp_fwd() -> u32 {
    b1(0xE9);
    let p = here();
    b4(0);
    return p;
}
fn patch_here(p: u32) { patch4(p, here() - (p + 4)); }
// Short forward jcc/jmp (the label must be within 127 bytes); patch_here8.
checkfree fn jcc_fwd8(cc: u32) -> u32 {
    b1(0x70 | cc);
    let p = here();
    b1(0);
    return p;
}
checkfree fn jmp_fwd8() -> u32 {
    b1(0xEB);
    let p = here();
    b1(0);
    return p;
}
fn patch_here8(p: u32) { patch1(p, here() - (p + 1)); }
// Backward jcc to code position `target` (a loop inside one instruction).
checkfree fn jcc_back(cc: u32, target: u32) {
    let d: i64 = target as i64 - here() - 2;
    if fits8(d) {
        b1(0x70 | cc);
        b1(d as! u32);
        return;
    }
    b1(0x0F);
    b1(0x80 | cc);
    b4(target - (here() + 4));
}
