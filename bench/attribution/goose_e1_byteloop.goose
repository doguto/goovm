// Attribution variant E1 of backend-goose/cg.goose: the three bulk copies
// (append = memcpy) are replaced by byte-at-a-time push loops, exactly as
// the C++ reference copies. Everything else is identical to cg.goose.
// goovm back-end in Goose: GIR tables -> ELF64 x86-64 relocatable object.
//
// A 1:1 port of backend-cpp/gir_codegen_cpp.cpp (see backend-cpp/DESIGN.md):
// same passes, same functions in the same order, same state, same output
// bytes. Single pass per function, -O0 quality: every instruction result
// lives in an 8-byte frame slot, operands are loaded into fixed scratch
// registers (rax, rcx, rdx), the result is stored back.
//
// Every place where this file differs from the C++ for a reason other
// than syntax is listed in backend-goose/NOTES.md and marked here with
// "NOTE(port)".
//
//   goose --standalone --header cg.h -o cg.c backend-goose/cg.goose
//   (backend-goose/build.sh does this and builds goovm-llc with it.)

// ------------------------------------------------------------- GIR records
// These mirror gir/gir.h byte for byte; tools/goovm-llc checks the layout
// of the generated C structs with static_asserts.

struct Func { global: u32, flags: u32, first_block: u32, n_blocks: u32, first_inst: u32,
              n_inst: u32, n_args: u32, arg_tys: u32, ret_ty: u32 }
struct Block { first_inst: u32, n_inst: u32 }
struct Inst { op: u8, ty: u8, sub: u8, aux: u8, a: u32, b: u32, c: u32 }
struct Const { value: i64, ty: u32, reserved: u32 }  // reserved = GirConst.pad (`pad` is a Goose keyword)
struct Global { name: u32, name_len: u32, kind: u32, flags: u32, data: u32, size: u32,
                align: u32, func: u32 }
struct DataReloc { owner: u32, offset: u32, target: u32, addend: i32 }

// The module, as nine read-only views of the host's tables. This is the
// C++ `const GirModule *M`; the counts are the slices' lengths.
struct Module {
    funcs: const Func[:],
    blocks: const Block[:],
    insts: const Inst[:],
    opnds: const u32[:],
    consts: const Const[:],
    globals: const Global[:],
    data: const u8[:],
    drelocs: const DataReloc[:],
    strtab: const u8[:],
}

// gir.h constants.
let GIR_V_INST = 0;
let GIR_V_ARG = 1;
let GIR_V_CONST = 2;
let GIR_V_GLOBAL = 3;
let GIR_NONE = 0xFFFFFFFF;

checkfree fn gir_kind(v: u32) -> u32 { v >> 30 }
checkfree fn gir_idx(v: u32) -> u32 { v & 0x3FFFFFFF }

let GIR_T_VOID = 0;
let GIR_T_I1 = 1;
let GIR_T_I8 = 2;
let GIR_T_I16 = 3;
let GIR_T_I32 = 4;
let GIR_T_I64 = 5;
let GIR_T_PTR = 6;

let GIR_RET = 0;
let GIR_BR = 1;
let GIR_CONDBR = 2;
let GIR_SWITCH = 3;
let GIR_UNREACHABLE = 4;
let GIR_ADD = 5;
let GIR_SUB = 6;
let GIR_MUL = 7;
let GIR_SDIV = 8;
let GIR_UDIV = 9;
let GIR_SREM = 10;
let GIR_UREM = 11;
let GIR_AND = 12;
let GIR_OR = 13;
let GIR_XOR = 14;
let GIR_SHL = 15;
let GIR_LSHR = 16;
let GIR_ASHR = 17;
let GIR_ICMP = 18;
let GIR_SELECT = 19;
let GIR_ZEXT = 20;
let GIR_SEXT = 21;
let GIR_TRUNC = 22;
let GIR_PTRTOINT = 23;
let GIR_INTTOPTR = 24;
let GIR_BITCAST = 25;
let GIR_ALLOCA = 26;
let GIR_LOAD = 27;
let GIR_STORE = 28;
let GIR_GEP = 29;
let GIR_CALL = 30;
let GIR_PHI = 31;

let GIR_EQ = 0;
let GIR_NE = 1;
let GIR_UGT = 2;
let GIR_UGE = 3;
let GIR_ULT = 4;
let GIR_ULE = 5;
let GIR_SGT = 6;
let GIR_SGE = 7;
let GIR_SLT = 8;
let GIR_SLE = 9;

let GIR_F_VARARG = 1;

let GIR_G_FUNC = 0;
let GIR_G_VAR = 1;
let GIR_GF_DEFINED = 1;
let GIR_GF_INTERNAL = 2;
let GIR_GF_CONST = 4;
let GIR_GF_ZERO = 8;
let GIR_GF_WEAK = 16;

// ------------------------------------------------------------------ constants

// Register numbers (ModRM/REX encoding).
// NOTE(port): registers, opcodes and flags are u32 here (C++: int), so
// that the encoder needs no casts; all values are small and non-negative.
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
let ARG_REG: u32[6] = [RDI, RSI, RDX, RCX, R8, R9];

// Condition codes: low nibble of Jcc (0F 80+cc), SETcc (0F 90+cc), CMOVcc (0F 40+cc).
let CC_B = 0x2;
let CC_AE = 0x3;
let CC_E = 0x4;
let CC_NE = 0x5;
let CC_BE = 0x6;
let CC_A = 0x7;
let CC_L = 0xC;
let CC_GE = 0xD;
let CC_LE = 0xE;
let CC_G = 0xF;

// ALU opcodes, "op r/m64, r64" form.
let ALU_ADD = 0x01;
let ALU_OR = 0x09;
let ALU_AND = 0x21;
let ALU_SUB = 0x29;
let ALU_XOR = 0x31;
let ALU_CMP = 0x39;
// Group-1 (81 /ext, 83 /ext) and shift (C1/D3 /ext) extensions.
let G1_ADD = 0;
let G1_SUB = 5;
let G1_CMP = 7;
let SH_SHL = 4;
let SH_SHR = 5;
let SH_SAR = 7;

// ELF relocation types (x86-64).
let R_X86_64_64 = 1;
let R_X86_64_PC32 = 2;
let R_X86_64_PLT32 = 4;
let R_X86_64_REX_GOTPCRELX = 42;

// Section indices of the output object. The layout is fixed.
let SEC_NULL = 0;
let SEC_TEXT = 1;
let SEC_DATA = 2;
let SEC_BSS = 3;
let SEC_RODATA = 4;
let SEC_RELA_TEXT = 5;
let SEC_RELA_DATA = 6;
let SEC_SYMTAB = 7;
let SEC_STRTAB = 8;
let SEC_SHSTRTAB = 9;
let SEC_NOTE = 10;
let SEC_COUNT = 11;

// Memory operand.
let M_RBP = 0;  // [rbp + disp]
let M_REG = 1;  // [reg]        (reg is rax, rcx or rdx)
let M_RSP = 2;  // [rsp + disp]
let M_RIP = 3;  // [rip + sym]  (relocation of type rtype, addend -4)
struct Mem { kind: u8, reg: u8, rtype: u16, disp: i32, sym: u32 }

struct Rela { offset: u64, info: u64, addend: i64 }  // = Elf64_Rela; info = (symbol << 32) | type

// rel32 at code[pos] -> start of local block `blk`.
// NOTE(port): C++ calls the field `block`, which is a Goose keyword.
struct Fixup { pos: u32, blk: u32 }

// ---------------------------------------------------------------------- state

var M: Module;

var code: u8[>..] = [];        // .text
var rela_text: Rela[>..] = []; // .rela.text
var sdata: u8[>..] = [];       // .data
var srodata: u8[>..] = [];     // .rodata
var bss_size: u64 = 0;
var data_align: u64 = 1;
var rodata_align: u64 = 1;
var bss_align: u64 = 1;

// Per global (index = GIR global index).
var g_sym: u32[>..] = [];      // ELF symbol index
var g_sec: u32[>..] = [];      // ELF section index, 0 = undefined
var g_value: u64[>..] = [];    // offset inside its section
var g_size: u64[>..] = [];
var g_has_reloc: u8[>..] = []; // variable has data relocations
var n_local_syms: u32 = 0;     // = index of the first non-local symbol

// Per function (index = local instruction / block / argument number).
var f_first_inst: u32 = 0;
var f_first_block: u32 = 0;
var f_arg_tys: u32 = 0;
var v_off: i32[>..] = [];      // rbp offset of the result slot, or of the alloca area
var t_off: i32[>..] = [];      // rbp offset of a PHI's temp slot
var a_off: i32[>..] = [];      // rbp offset of an argument's slot
var block_off: u32[>..] = [];  // code offset of each block
var fixups: Fixup[>..] = [];

// The object file being built; the host reads it until the next call.
// (C++: the caller's std::vector `obj_out`.)
var obj: u8[>..] = [];

// ----------------------------------------------------------------- byte output
// NOTE(port): `checkfree` marks the functions that have no bounds check at
// all (the byte output and the whole encoder); the compiler rejects the
// program if one ever gets one. It changes nothing else.

checkfree fn b1(x: u32) { code.push(x as! u8); }
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
    // NOTE(port): one range check for the four bytes instead of four index checks.
    let p: i64 = pos;
    let w = code[p..p + 4];
    w[0] = x as! u8;
    w[1] = (x >> 8) as! u8;
    w[2] = (x >> 16) as! u8;
    w[3] = (x >> 24) as! u8;
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
// One- or two-byte opcode (0x0FB6 = 0F B6).
checkfree fn opc(op: u32) {
    if op > 0xFF { b1(op >> 8); }
    b1(op & 0xFF);
}
checkfree fn modrm_mem(reg: u32, x: Mem) {
    let r: u32 = (reg & 7) << 3;
    if x.kind == M_RBP {
        if fits8(x.disp) {
            b1(0x45 | r);
            b1(x.disp as! u32);
        } else {
            b1(0x85 | r);
            b4(x.disp as! u32);
        }
    } else if x.kind == M_RSP {
        if fits8(x.disp) {
            b1(0x44 | r);
            b1(0x24);
            b1(x.disp as! u32);
        } else {
            b1(0x84 | r);
            b1(0x24);
            b4(x.disp as! u32);
        }
    } else if x.kind == M_REG {
        b1(r | (x.reg & 7));
    } else {
        b1(r | 5);
        rela_text.push(Rela { offset: here(), info: (x.sym as u64 << 32) | x.rtype, addend: -4 });
        b4(0);
    }
}
// [66] [REX] opcode ModRM(reg, mem). byte_reg: `reg` is an 8-bit register.
checkfree fn op_mem(p66: bool, w: u32, op: u32, reg: u32, x: Mem, byte_reg: bool) {
    if p66 { b1(0x66); }
    rex(w, reg, if x.kind == M_REG { x.reg } else { 0 }, byte_reg && reg >= 4 && reg < 8);
    opc(op);
    modrm_mem(reg, x);
}
// [REX] opcode ModRM(11, reg, rm). force: see rex().
checkfree fn op_rr(w: u32, op: u32, reg: u32, rm: u32, force: bool) {
    rex(w, reg, rm, force);
    opc(op);
    b1(0xC0 | ((reg & 7) << 3) | (rm & 7));
}

checkfree fn m_rbp(disp: i32) -> Mem { Mem { M_RBP, 0, 0, disp, 0 } }
checkfree fn m_rsp(disp: i32) -> Mem { Mem { M_RSP, 0, 0, disp, 0 } }
checkfree fn m_reg(r: u32) -> Mem { Mem { M_REG, r as! u8, 0, 0, 0 } }
fn m_rip(g: u32, rtype: u32) -> Mem { Mem { M_RIP, 0, rtype as! u16, 0, g_sym[g] } }

checkfree fn load64(r: u32, x: Mem) { op_mem(false, 1, 0x8B, r, x, false); }   // mov r64, [m]
checkfree fn store64(x: Mem, r: u32) { op_mem(false, 1, 0x89, r, x, false); }  // mov [m], r64
checkfree fn lea64(r: u32, x: Mem) { op_mem(false, 1, 0x8D, r, x, false); }    // lea r64, [m]
// Zero-extending load of type t.
checkfree fn load_typed(r: u32, x: Mem, t: u32) {
    if t == GIR_T_I1 || t == GIR_T_I8 { op_mem(false, 0, 0x0FB6, r, x, false); }   // movzx r32, byte [m]
    else if t == GIR_T_I16 { op_mem(false, 0, 0x0FB7, r, x, false); }              // movzx r32, word [m]
    else if t == GIR_T_I32 { op_mem(false, 0, 0x8B, r, x, false); }                // mov r32, [m]
    else { load64(r, x); }
}
checkfree fn store_typed(x: Mem, r: u32, t: u32) {
    if t == GIR_T_I1 || t == GIR_T_I8 { op_mem(false, 0, 0x88, r, x, true); }      // mov [m], r8
    else if t == GIR_T_I16 { op_mem(true, 0, 0x89, r, x, false); }                 // mov [m], r16
    else if t == GIR_T_I32 { op_mem(false, 0, 0x89, r, x, false); }                // mov [m], r32
    else { store64(x, r); }
}
checkfree fn mov_rr64(d: u32, s: u32) { op_rr(1, 0x89, s, d, false); }
checkfree fn mov_rr32(d: u32, s: u32) { op_rr(0, 0x89, s, d, false); }
checkfree fn alu_rr64(op: u32, d: u32, s: u32) { op_rr(1, op, s, d, false); }
checkfree fn imul_rr64(d: u32, s: u32) { op_rr(1, 0x0FAF, d, s, false); }
checkfree fn imul_rri64(d: u32, s: u32, imm: i32) {
    op_rr(1, 0x69, d, s, false);
    b4(imm as! u32);
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
checkfree fn shift_cl64(ext: u32, r: u32) { op_rr(1, 0xD3, ext, r, false); }
checkfree fn shift_imm64(ext: u32, r: u32, n: u32) {
    op_rr(1, 0xC1, ext, r, false);
    b1(n);
}
checkfree fn and_ri32(r: u32, imm8: u32) {
    op_rr(0, 0x83, 4, r, false);
    b1(imm8);
}
checkfree fn neg64(r: u32) { op_rr(1, 0xF7, 3, r, false); }
checkfree fn div64(ext: u32, r: u32) { op_rr(1, 0xF7, ext, r, false); }  // 6 = div, 7 = idiv
checkfree fn setcc(cc: u32, r: u32) { op_rr(0, 0x0F90 | cc, 0, r, r >= 4 && r < 8); }
checkfree fn movzx8(d: u32, s: u32) { op_rr(0, 0x0FB6, d, s, s >= 4 && s < 8); }
checkfree fn movzx16(d: u32, s: u32) { op_rr(0, 0x0FB7, d, s, false); }
checkfree fn movsx8_64(d: u32, s: u32) { op_rr(1, 0x0FBE, d, s, false); }
checkfree fn movsx16_64(d: u32, s: u32) { op_rr(1, 0x0FBF, d, s, false); }
checkfree fn movsxd(d: u32, s: u32) { op_rr(1, 0x63, d, s, false); }
checkfree fn test_rr32(a: u32, b: u32) { op_rr(0, 0x85, b, a, false); }
checkfree fn cmov64(cc: u32, d: u32, s: u32) { op_rr(1, 0x0F40 | cc, d, s, false); }
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
checkfree fn jmp_block(b: u32) {
    b1(0xE9);
    fixups.push(Fixup { pos: here(), blk: b });
    b4(0);
}
checkfree fn jcc_block(cc: u32, b: u32) {
    b1(0x0F);
    b1(0x80 | cc);
    fixups.push(Fixup { pos: here(), blk: b });
    b4(0);
}
// Forward jcc to a label inside the current instruction; returns the rel32
// position for patch_here().
checkfree fn jcc_fwd(cc: u32) -> u32 {
    b1(0x0F);
    b1(0x80 | cc);
    let p = here();
    b4(0);
    return p;
}
fn patch_here(p: u32) { patch4(p, here() - (p + 4)); }

// -------------------------------------------------------- value conventions

// Values narrower than 64 bits are kept zero-extended in registers and slots.
checkfree fn zext_reg(r: u32, t: u32) {
    if t == GIR_T_I1 { and_ri32(r, 1); }
    else if t == GIR_T_I8 { movzx8(r, r); }
    else if t == GIR_T_I16 { movzx16(r, r); }
    else if t == GIR_T_I32 { mov_rr32(r, r); }
}
checkfree fn sext_reg(r: u32, t: u32) {
    if t == GIR_T_I1 {
        and_ri32(r, 1);
        neg64(r);
    } else if t == GIR_T_I8 { movsx8_64(r, r); }
    else if t == GIR_T_I16 { movsx16_64(r, r); }
    else if t == GIR_T_I32 { movsxd(r, r); }
}
checkfree fn bits_of(t: u32) -> u32 {
    if t == GIR_T_I1 { return 1; }
    if t == GIR_T_I8 { return 8; }
    if t == GIR_T_I16 { return 16; }
    if t == GIR_T_I32 { return 32; }
    return 64;
}
fn type_of(v: u32) -> u32 {
    let i = gir_idx(v);
    let k = gir_kind(v);
    if k == GIR_V_INST { return M.insts[i].ty; }
    if k == GIR_V_ARG { return M.opnds[f_arg_tys + i]; }
    if k == GIR_V_CONST { return M.consts[i].ty; }
    return GIR_T_PTR;
}
fn is_alloca(v: u32) -> bool { gir_kind(v) == GIR_V_INST && M.insts[gir_idx(v)].op == GIR_ALLOCA }
fn is_defined_global(v: u32) -> bool {
    gir_kind(v) == GIR_V_GLOBAL && M.globals[gir_idx(v)].flags & GIR_GF_DEFINED != 0
}

// Loads the value `v` into register r (only r is written).
fn load_val(r: u32, v: u32) {
    let i = gir_idx(v);
    let k = gir_kind(v);
    if k == GIR_V_INST {
        if M.insts[i].op == GIR_ALLOCA { lea64(r, m_rbp(v_off[i - f_first_inst])); }
        else { load64(r, m_rbp(v_off[i - f_first_inst])); }
    } else if k == GIR_V_ARG {
        load64(r, m_rbp(a_off[i]));
    } else if k == GIR_V_CONST {
        mov_ri(r, M.consts[i].value as! u64);
    } else if M.globals[i].flags & GIR_GF_DEFINED != 0 {
        lea64(r, m_rip(i, R_X86_64_PC32));                 // lea r, [rip + sym]
    } else {
        load64(r, m_rip(i, R_X86_64_REX_GOTPCRELX));      // mov r, [rip + sym@GOTPCREL]
    }
}
// Memory operand for the pointer value `v`; loads it into `scratch` unless
// it is an alloca (rbp-relative) or a defined global (rip-relative).
fn addr_of(v: u32, scratch: u32) -> Mem {
    if is_alloca(v) { return m_rbp(v_off[gir_idx(v) - f_first_inst]); }
    if is_defined_global(v) { return m_rip(gir_idx(v), R_X86_64_PC32); }
    load_val(scratch, v);
    return m_reg(scratch);
}
fn store_result(j: u32, r: u32) { store64(m_rbp(v_off[j]), r); }

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

// ------------------------------------------------------------------- PHIs

// NOTE(port): `let I = M.insts[k]` copies the 16-byte record (the Goose
// idiom for a fixed-size element); the C++ binds `const GirInst &`.
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
            load_val(RAX, M.opnds[I.b + 2 * p]);
            store64(m_rbp(t_off[k - f_first_inst]), RAX);
            break;
        }
    }
}

// ------------------------------------------------------------ instructions

fn gen_inst(gi: u32, cur: u32) {
    let I = M.insts[gi];
    let j = gi - f_first_inst;
    let next = cur + 1;
    match I.op {
        GIR_RET => {
            if I.a != GIR_NONE { load_val(RAX, I.a); }
            b1(0xC9);  // leave
            b1(0xC3);  // ret
        },
        GIR_BR => {
            phi_moves(cur, I.a);
            if I.a != next { jmp_block(I.a); }
        },
        GIR_CONDBR => {
            load_val(RAX, I.a);
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
        GIR_SWITCH => {
            load_val(RAX, I.a);
            for k in 0..I.c {
                let v: i64 = M.consts[gir_idx(M.opnds[I.b + 1 + 2 * k])].value;
                let tb = M.opnds[I.b + 2 + 2 * k];
                if fits32(v) {
                    grp1_ri64(G1_CMP, RAX, v as! i32);
                } else {
                    mov_ri(RCX, v as! u64);
                    alu_rr64(ALU_CMP, RAX, RCX);
                }
                if has_phi(tb) {
                    let p = jcc_fwd(CC_NE);
                    phi_moves(cur, tb);
                    jmp_block(tb);
                    patch_here(p);
                } else {
                    jcc_block(CC_E, tb);
                }
            }
            let d = M.opnds[I.b];
            phi_moves(cur, d);
            if d != next { jmp_block(d); }
        },
        GIR_UNREACHABLE => {
            b1(0x0F);  // ud2
            b1(0x0B);
        },
        GIR_ADD, GIR_SUB, GIR_MUL, GIR_AND, GIR_OR, GIR_XOR => {
            load_val(RAX, I.a);
            load_val(RCX, I.b);
            if I.op == GIR_ADD { alu_rr64(ALU_ADD, RAX, RCX); }
            else if I.op == GIR_SUB { alu_rr64(ALU_SUB, RAX, RCX); }
            else if I.op == GIR_AND { alu_rr64(ALU_AND, RAX, RCX); }
            else if I.op == GIR_OR { alu_rr64(ALU_OR, RAX, RCX); }
            else if I.op == GIR_XOR { alu_rr64(ALU_XOR, RAX, RCX); }
            else { imul_rr64(RAX, RCX); }
            zext_reg(RAX, I.ty);
            store_result(j, RAX);
        },
        GIR_SHL, GIR_LSHR, GIR_ASHR => {
            load_val(RAX, I.a);
            load_val(RCX, I.b);
            if I.op == GIR_ASHR { sext_reg(RAX, I.ty); }
            shift_cl64(if I.op == GIR_SHL { SH_SHL } else if I.op == GIR_LSHR { SH_SHR } else { SH_SAR }, RAX);
            zext_reg(RAX, I.ty);
            store_result(j, RAX);
        },
        GIR_SDIV, GIR_SREM => {
            load_val(RAX, I.a);
            load_val(RCX, I.b);
            sext_reg(RAX, I.ty);
            sext_reg(RCX, I.ty);
            b1(0x48);  // cqo
            b1(0x99);
            div64(7, RCX);
            if I.op == GIR_SREM { mov_rr64(RAX, RDX); }
            zext_reg(RAX, I.ty);
            store_result(j, RAX);
        },
        GIR_UDIV, GIR_UREM => {
            load_val(RAX, I.a);
            load_val(RCX, I.b);
            op_rr(0, ALU_XOR, RDX, RDX, false);  // xor edx, edx
            div64(6, RCX);
            if I.op == GIR_UREM { mov_rr64(RAX, RDX); }
            store_result(j, RAX);
        },
        GIR_ICMP => {
            load_val(RAX, I.a);
            load_val(RCX, I.b);
            if I.sub >= GIR_SGT && bits_of(I.aux) < 64 {
                sext_reg(RAX, I.aux);
                sext_reg(RCX, I.aux);
            }
            alu_rr64(ALU_CMP, RAX, RCX);
            setcc(icmp_cc(I.sub), RAX);
            movzx8(RAX, RAX);
            store_result(j, RAX);
        },
        GIR_SELECT => {
            load_val(RAX, I.a);
            load_val(RCX, I.b);
            load_val(RDX, I.c);
            test_rr32(RAX, RAX);
            cmov64(CC_E, RCX, RDX);
            store_result(j, RCX);
        },
        GIR_ZEXT, GIR_INTTOPTR, GIR_BITCAST => {
            load_val(RAX, I.a);
            store_result(j, RAX);
        },
        GIR_TRUNC, GIR_PTRTOINT => {
            load_val(RAX, I.a);
            zext_reg(RAX, I.ty);
            store_result(j, RAX);
        },
        GIR_SEXT => {
            load_val(RAX, I.a);
            sext_reg(RAX, I.aux);
            zext_reg(RAX, I.ty);
            store_result(j, RAX);
        },
        GIR_ALLOCA => {},
        GIR_LOAD => {
            let x = addr_of(I.a, RAX);
            load_typed(RAX, x, I.ty);
            if I.ty == GIR_T_I1 { and_ri32(RAX, 1); }
            store_result(j, RAX);
        },
        GIR_STORE => {
            load_val(RAX, I.a);
            let x = addr_of(I.b, RCX);
            store_typed(x, RAX, I.aux);
        },
        GIR_GEP => {
            load_val(RAX, I.a);
            let off = (M.opnds[I.b] | M.opnds[I.b + 1] as u64 << 32) as! i64;
            for k in 0..I.c {
                let idx = M.opnds[I.b + 2 + 2 * k];
                let sc = M.opnds[I.b + 3 + 2 * k];
                if sc == 0 { continue; }  // the exporter never emits these
                load_val(RCX, idx);
                sext_reg(RCX, type_of(idx));
                if sc & (sc - 1) == 0 {
                    var sh: u32 = 0;
                    while (1 << sh) < sc { sh++; }
                    if sh != 0 { shift_imm64(SH_SHL, RCX, sh); }
                } else if sc <= 0x7FFFFFFF {
                    imul_rri64(RCX, RCX, sc as! i32);
                } else {
                    mov_ri(RDX, sc);
                    imul_rr64(RCX, RDX);
                }
                alu_rr64(ALU_ADD, RAX, RCX);
            }
            if off != 0 {
                if fits32(off) {
                    grp1_ri64(G1_ADD, RAX, off as! i32);
                } else {
                    mov_ri(RCX, off as! u64);
                    alu_rr64(ALU_ADD, RAX, RCX);
                }
            }
            store_result(j, RAX);
        },
        GIR_CALL => {
            let n = I.c;
            let s = I.b;
            // NOTE(port): the arguments ops[s .. s+n) are sliced once, and both
            // argument loops run to args.len (= n), so they index it unchecked.
            let args = M.opnds[s..s as i64 + n];
            let sbytes: u32 = if n > 6 { ((n - 6) * 8 + 15) & ~15 } else { 0 };
            if sbytes != 0 {
                grp1_ri64(G1_SUB, RSP, sbytes as! i32);
                for k in 6..args.len {
                    load_val(RAX, args[k]);
                    store64(m_rsp((8 * (k - 6)) as! i32), RAX);
                }
            }
            let callee = I.a;
            let direct = gir_kind(callee) == GIR_V_GLOBAL && M.globals[gir_idx(callee)].kind == GIR_G_FUNC;
            if !direct { load_val(R11, callee); }
            var k: u32 = 0;
            while k < args.len && k < 6 {
                load_val(ARG_REG[k], args[k]);
                k++;
            }
            if I.sub & GIR_F_VARARG != 0 { mov_ri(RAX, 0); }  // al = number of vector registers used
            if direct {
                b1(0xE8);  // call rel32
                rela_text.push(Rela { offset: here(), info: (g_sym[gir_idx(callee)] as u64 << 32) | R_X86_64_PLT32,
                                      addend: -4 });
                b4(0);
            } else {
                op_rr(0, 0xFF, 2, R11, false);  // call r11
            }
            if sbytes != 0 { grp1_ri64(G1_ADD, RSP, sbytes as! i32); }
            if I.ty != GIR_T_VOID {
                zext_reg(RAX, I.ty);
                store_result(j, RAX);
            }
        },
        GIR_PHI => {
            load64(RAX, m_rbp(t_off[j]));
            store_result(j, RAX);
        },
        _ => {
            b1(0x0F);  // unknown opcode: trap
            b1(0x0B);
        },
    }
}

// --------------------------------------------------------------- functions

fn gen_function(fi: u32) {
    let f = M.funcs[fi];
    while code.len & 15 != 0 { b1(0xCC); }
    let start = here();
    f_first_inst = f.first_inst;
    f_first_block = f.first_block;
    f_arg_tys = f.arg_tys;

    // NOTE(port): the function's runs of instructions, blocks and argument
    // types are sliced once (one range check each) and the loops walk the
    // slices; the asserts state what the resizes guarantee, so the loops
    // index the per-function arrays without checks.
    let insts = M.insts[f.first_inst..f.first_inst + f.n_inst];
    let blocks = M.blocks[f.first_block..f.first_block + f.n_blocks];
    let arg_tys = M.opnds[f.arg_tys..f.arg_tys + f.n_args];

    // Frame layout: argument slots, then one slot per result (two per PHI),
    // alloca areas in between at their alignment. rbp is 16-byte aligned.
    var off: i64 = 0;
    if a_off.len < f.n_args { a_off.resize(f.n_args, 0); }
    assert(a_off.len >= arg_tys.len);
    for a in 0..arg_tys.len {
        off += 8;
        a_off[a] = (-off) as! i32;
    }
    if v_off.len < f.n_inst {
        v_off.resize(f.n_inst, 0);
        t_off.resize(f.n_inst, 0);
    }
    assert(v_off.len >= insts.len && t_off.len >= insts.len);
    for I, j in insts {
        if I.op == GIR_ALLOCA {
            let al: i64 = if I.b != 0 { I.b } else { 1 };
            let size: i64 = if I.a != 0 { I.a } else { 1 };
            off = (off + size + al - 1) / al * al;
            v_off[j] = (-off) as! i32;
        } else if I.ty != GIR_T_VOID {
            off = ((off + 7) & ~7) + 8;  // slots stay 8-byte aligned
            v_off[j] = (-off) as! i32;
            if I.op == GIR_PHI {
                off += 8;
                t_off[j] = (-off) as! i32;
            }
        }
    }
    let frame: i64 = (off + 15) & ~15;

    // Prologue: push rbp; mov rbp, rsp; sub rsp, frame; spill arguments.
    b1(0x55);
    b1(0x48);
    b1(0x89);
    b1(0xE5);
    if frame != 0 { grp1_ri64(G1_SUB, RSP, frame as! i32); }
    for t, a in arg_tys {
        if a < 6 {
            zext_reg(ARG_REG[a], t);
            store64(m_rbp(a_off[a]), ARG_REG[a]);
        } else {
            load64(RAX, m_rbp((16 + 8 * (a - 6)) as! i32));
            zext_reg(RAX, t);
            store64(m_rbp(a_off[a]), RAX);
        }
    }

    if block_off.len < f.n_blocks { block_off.resize(f.n_blocks, 0); }
    assert(block_off.len >= blocks.len);
    fixups.clear();
    for B, b in blocks {
        block_off[b] = here();
        for k in B.first_inst..B.first_inst + B.n_inst { gen_inst(k, b as! u32); }
    }
    for x in fixups {
        patch4(x.pos, block_off[x.blk] - (x.pos + 4));
    }

    g_value[f.global] = start;
    g_size[f.global] = here() - start;
}

// ------------------------------------------------------------ data layout

// NOTE(port): g is an i64 (C++: uint32_t), the type of the caller's loop
// index; with a u32 the call's `g as! u32` hides g < M.globals.len from the
// bounds-check analysis and two checks per variable stay.
fn append_aligned(sec: u8[>..]&, sec_align: u64&, g: i64) {
    let G = M.globals[g];
    let al: u64 = if G.align != 0 { G.align } else { 1 };
    while (sec.len as u64) % al != 0 { sec.push(0); }
    if al > sec_align { sec_align = al; }
    g_value[g] = sec.len as u64;
    // NOTE(port): one append (a memcpy) where the C++ pushes byte by byte.
    for b in M.data[G.data..G.data + G.size] { sec.push(b); }   // E1: byte loop like the C++
}

fn layout_globals() {
    let n = M.globals.len;
    // NOTE(port): C++ `v.assign(n, 0)` is clear() + resize(n, 0).
    g_sym.clear();
    g_sym.resize(n, 0);
    g_sec.clear();
    g_sec.resize(n, SEC_NULL);
    g_value.clear();
    g_value.resize(n, 0);
    g_size.clear();
    g_size.resize(n, 0);
    g_has_reloc.clear();
    g_has_reloc.resize(n, 0);
    for d in M.drelocs { g_has_reloc[d.owner] = 1; }

    // Symbol indices: null symbol, then all local symbols, then the rest.
    var next: u32 = 1;
    for g in 0..n {
        if M.globals[g].flags & GIR_GF_INTERNAL != 0 {
            g_sym[g] = next;
            next++;
        }
    }
    n_local_syms = next;
    for g in 0..n {
        if M.globals[g].flags & GIR_GF_INTERNAL == 0 {
            g_sym[g] = next;
            next++;
        }
    }

    for g in 0..n {
        let G = M.globals[g];
        if G.flags & GIR_GF_DEFINED == 0 { continue; }
        if G.kind == GIR_G_FUNC {
            g_sec[g] = SEC_TEXT;
            continue;
        }
        g_size[g] = G.size;
        if G.flags & GIR_GF_ZERO != 0 {
            let al: u64 = if G.align != 0 { G.align } else { 1 };
            bss_size = (bss_size + al - 1) / al * al;
            if al > bss_align { bss_align = al; }
            g_value[g] = bss_size;
            bss_size += G.size;
            g_sec[g] = SEC_BSS;
        } else if G.flags & GIR_GF_CONST != 0 && g_has_reloc[g] == 0 {
            append_aligned(srodata, rodata_align, g);
            g_sec[g] = SEC_RODATA;
        } else {
            // Read-only data with relocations goes to .data too, so that a
            // PIE link needs no text relocations.
            append_aligned(sdata, data_align, g);
            g_sec[g] = SEC_DATA;
        }
    }
}

// ------------------------------------------------------------------- ELF

checkfree fn o1(o: u8[>..]&, x: u32) { o.push(x as! u8); }
checkfree fn o2(o: u8[>..]&, x: u32) {
    o1(o, x);
    o1(o, x >> 8);
}
checkfree fn o4(o: u8[>..]&, x: u32) {
    o2(o, x);
    o2(o, x >> 16);
}
checkfree fn o8(o: u8[>..]&, x: u64) {
    o4(o, x as! u32);
    o4(o, (x >> 32) as! u32);
}
checkfree fn opad(o: u8[>..]&, al: u64) {
    while (o.len as u64) % al != 0 { o.push(0); }
}
// NOTE(port): one append (a memcpy) where the C++ pushes byte by byte.
fn obytes(o: u8[>..]&, p: const u8[:]) { for b in p { o.push(b); } }   // E1: byte loop like the C++

// Section names, flags and types, in section order.
let SEC_NAMES: const u8[:][11] = ["", ".text", ".data", ".bss", ".rodata", ".rela.text",
                                  ".rela.data", ".symtab", ".strtab", ".shstrtab",
                                  ".note.GNU-stack"];
//                          type flags  link        info           align         entsize
let SH_TYPE: u32[11] = [0, 1, 1, 8, 1, 4, 4, 2, 3, 3, 1];
let SH_FLAGS: u32[11] = [0, 6, 3, 3, 2, 0x40, 0x40, 0, 0, 0, 0];

fn write_elf(o: u8[>..]&) {
    // Section header string table and name offsets.
    var shstr: u8[>..] = [];
    var sh_name: u32[11] = [0; 11];
    for s in SEC_COUNT {
        sh_name[s] = shstr.len as! u32;
        // NOTE(port): append where the C++ walks the C string byte by byte.
        for b in SEC_NAMES[s] { shstr.push(b); }   // E1: byte loop like the C++
        shstr.push(0);
    }
    var sh_off: u64[11] = [0; 11];
    var sh_size: u64[11] = [0; 11];

    o.clear();
    // ELF header (e_shoff patched below).
    o1(o, 0x7F); o1(o, 'E'); o1(o, 'L'); o1(o, 'F');
    o1(o, 2);  // ELFCLASS64
    o1(o, 1);  // ELFDATA2LSB
    o1(o, 1);  // EV_CURRENT
    for i in 9 { o1(o, 0); }
    o2(o, 1);   // ET_REL
    o2(o, 62);  // EM_X86_64
    o4(o, 1);   // e_version
    o8(o, 0);   // e_entry
    o8(o, 0);   // e_phoff
    o8(o, 0);   // e_shoff (patched)
    o4(o, 0);   // e_flags
    o2(o, 64);  // e_ehsize
    o2(o, 0);   // e_phentsize
    o2(o, 0);   // e_phnum
    o2(o, 64);  // e_shentsize
    o2(o, SEC_COUNT);
    o2(o, SEC_SHSTRTAB);

    opad(o, 16);
    sh_off[SEC_TEXT] = o.len as u64;
    obytes(o, code);
    sh_size[SEC_TEXT] = code.len as u64;

    opad(o, data_align);
    sh_off[SEC_DATA] = o.len as u64;
    obytes(o, sdata);
    sh_size[SEC_DATA] = sdata.len as u64;

    sh_off[SEC_BSS] = o.len as u64;
    sh_size[SEC_BSS] = bss_size;

    opad(o, rodata_align);
    sh_off[SEC_RODATA] = o.len as u64;
    obytes(o, srodata);
    sh_size[SEC_RODATA] = srodata.len as u64;

    opad(o, 8);
    sh_off[SEC_RELA_TEXT] = o.len as u64;
    for r in rela_text {
        o8(o, r.offset);
        o8(o, r.info);
        o8(o, r.addend as! u64);
    }
    sh_size[SEC_RELA_TEXT] = o.len as u64 - sh_off[SEC_RELA_TEXT];

    sh_off[SEC_RELA_DATA] = o.len as u64;
    for d in M.drelocs {
        o8(o, g_value[d.owner] + d.offset);
        o8(o, (g_sym[d.target] as u64 << 32) | R_X86_64_64);
        o8(o, d.addend as! u64);
    }
    sh_size[SEC_RELA_DATA] = o.len as u64 - sh_off[SEC_RELA_DATA];

    // Symbol table: null, locals, then globals (same order as g_sym).
    sh_off[SEC_SYMTAB] = o.len as u64;
    for i in 24 { o1(o, 0); }
    for pass: u32 in 0..2 {
        for G, g in M.globals {
            let local: u32 = if G.flags & GIR_GF_INTERNAL != 0 { 1 } else { 0 };
            if local != (if pass == 0 { 1 } else { 0 }) { continue; }
            // STB_LOCAL/GLOBAL/WEAK
            let bind: u32 = if local != 0 { 0 } else if G.flags & GIR_GF_WEAK != 0 { 2 } else { 1 };
            // NOTE(port): C++ calls this `type`, which is a Goose keyword.
            // NOTYPE/FUNC/OBJECT
            let typ: u32 = if G.flags & GIR_GF_DEFINED == 0 { 0 } else if G.kind == GIR_G_FUNC { 2 } else { 1 };
            o4(o, G.name);
            o1(o, (bind << 4) | typ);
            o1(o, 0);
            o2(o, g_sec[g]);
            o8(o, g_value[g]);
            o8(o, g_size[g]);
        }
    }
    sh_size[SEC_SYMTAB] = o.len as u64 - sh_off[SEC_SYMTAB];

    // The GIR string table is a valid ELF string table (gir.h).
    sh_off[SEC_STRTAB] = o.len as u64;
    if M.strtab.len != 0 { obytes(o, M.strtab); }
    else { o1(o, 0); }
    sh_size[SEC_STRTAB] = o.len as u64 - sh_off[SEC_STRTAB];

    sh_off[SEC_SHSTRTAB] = o.len as u64;
    obytes(o, shstr);
    sh_size[SEC_SHSTRTAB] = shstr.len as u64;

    sh_off[SEC_NOTE] = o.len as u64;

    // Section headers.
    opad(o, 8);
    let shoff = o.len as u64;
    let e_shoff = o[40..48];
    for i in 8 { e_shoff[i] = (shoff >> (8 * i)) as! u8; }
    for s in SEC_COUNT {
        var link: u32 = 0;
        var info: u32 = 0;
        var align: u64 = 1;
        var entsize: u64 = 0;
        if s == SEC_TEXT { align = 16; }
        if s == SEC_DATA { align = data_align; }
        if s == SEC_BSS { align = bss_align; }
        if s == SEC_RODATA { align = rodata_align; }
        if s == SEC_RELA_TEXT || s == SEC_RELA_DATA {
            link = SEC_SYMTAB;
            info = if s == SEC_RELA_TEXT { SEC_TEXT } else { SEC_DATA };
            align = 8;
            entsize = 24;
        }
        if s == SEC_SYMTAB {
            link = SEC_STRTAB;
            info = n_local_syms;
            align = 8;
            entsize = 24;
        }
        if s == SEC_NULL { align = 0; }
        o4(o, if s == SEC_NULL { 0 } else { sh_name[s] });
        o4(o, SH_TYPE[s]);
        o8(o, SH_FLAGS[s]);
        o8(o, 0);  // sh_addr
        o8(o, sh_off[s]);
        o8(o, sh_size[s]);
        o4(o, link);
        o4(o, info);
        o8(o, align);
        o8(o, entsize);
    }
}

// ------------------------------------------------------------------ entry

// Compiles the whole module and returns the bytes of an ELF64 x86-64
// relocatable object (valid until the next call). The module must follow
// the structural rules of gir.h; the back-end does not validate its input
// (an out-of-range index aborts on a bounds check instead of reading
// garbage).
export fn gir_codegen(funcs: const Func[:], blocks: const Block[:], insts: const Inst[:],
                      opnds: const u32[:], consts: const Const[:], globals: const Global[:],
                      data: const u8[:], drelocs: const DataReloc[:], strtab: const u8[:]) -> const u8[:] {
    M = Module { funcs: funcs, blocks: blocks, insts: insts, opnds: opnds, consts: consts,
                 globals: globals, data: data, drelocs: drelocs, strtab: strtab };
    code.clear();
    rela_text.clear();
    sdata.clear();
    srodata.clear();
    bss_size = 0;
    data_align = 1;
    rodata_align = 1;
    bss_align = 1;
    layout_globals();
    for fi in 0..funcs.len { gen_function(fi as! u32); }
    write_elf(obj);
    return obj;
}
