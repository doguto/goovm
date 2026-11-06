// Attribution variant E6 of backend-cpp/gir_codegen_cpp.cpp (experiment only):
// bulk copies via insert, reserve() on the vectors, a Goose-style bump buffer
// for .text (address-space reservation, no capacity check, never moves) and
// always_inline on the byte emitters. Output is byte-identical.
// goovm reference back-end: GIR -> x86-64 SysV ELF64 relocatable object.
//
// Single pass per function, -O0 quality: every instruction result lives in
// an 8-byte frame slot, operands are loaded into fixed scratch registers
// (rax, rcx, rdx), the result is stored back. See DESIGN.md.
//
// Written to be ported 1:1 to Goose: plain structs, std::vector as growable
// arrays indexed by u32, no recursion, no maps, no virtual calls, no
// function pointers, no exceptions. All state lives in file-scope variables
// (one growable array per variable, because a Goose struct can only hold
// one variable-length member).

#include "gir_codegen_cpp.h"

#include <cstring>

#include <sys/mman.h>
// Experiment only: a Goose-style grow-only byte array (address-space
// reservation, bump pointer, no capacity check, never moves).
struct Bump {
    uint8_t *b = nullptr, *e = nullptr;
    void init() { if (!b) { b = e = (uint8_t *)mmap(nullptr, 1ull << 31, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0); } }
    void push_back(uint8_t x) { *e++ = x; }
    size_t size() const { return (size_t)(e - b); }
    uint8_t &operator[](size_t i) { return b[i]; }
    const uint8_t *data() const { return b; }
    void clear() { init(); e = b; }
    void reserve(size_t) {}
};
namespace {

// ------------------------------------------------------------------ constants

// Register numbers (ModRM/REX encoding).
enum : int {
    RAX = 0, RCX = 1, RDX = 2, RBX = 3, RSP = 4, RBP = 5, RSI = 6, RDI = 7,
    R8 = 8, R9 = 9, R10 = 10, R11 = 11
};
const int ARG_REG[6] = {RDI, RSI, RDX, RCX, R8, R9};

// Condition codes: low nibble of Jcc (0F 80+cc), SETcc (0F 90+cc), CMOVcc (0F 40+cc).
enum : int {
    CC_B = 0x2, CC_AE = 0x3, CC_E = 0x4, CC_NE = 0x5, CC_BE = 0x6, CC_A = 0x7,
    CC_L = 0xC, CC_GE = 0xD, CC_LE = 0xE, CC_G = 0xF
};

// ALU opcodes, "op r/m64, r64" form.
enum : uint32_t { ALU_ADD = 0x01, ALU_OR = 0x09, ALU_AND = 0x21, ALU_SUB = 0x29, ALU_XOR = 0x31, ALU_CMP = 0x39 };
// Group-1 (81 /ext, 83 /ext) and shift (C1/D3 /ext) extensions.
enum : int { G1_ADD = 0, G1_SUB = 5, G1_CMP = 7, SH_SHL = 4, SH_SHR = 5, SH_SAR = 7 };

// ELF relocation types (x86-64).
enum : uint32_t { R_X86_64_64 = 1, R_X86_64_PC32 = 2, R_X86_64_PLT32 = 4, R_X86_64_REX_GOTPCRELX = 42 };

// Section indices of the output object. The layout is fixed.
enum : uint32_t {
    SEC_NULL = 0, SEC_TEXT = 1, SEC_DATA = 2, SEC_BSS = 3, SEC_RODATA = 4,
    SEC_RELA_TEXT = 5, SEC_RELA_DATA = 6, SEC_SYMTAB = 7, SEC_STRTAB = 8,
    SEC_SHSTRTAB = 9, SEC_NOTE = 10, SEC_COUNT = 11
};

// Memory operand.
enum : uint8_t {
    M_RBP = 0,  // [rbp + disp]
    M_REG = 1,  // [reg]        (reg is rax, rcx or rdx)
    M_RSP = 2,  // [rsp + disp]
    M_RIP = 3   // [rip + sym]  (relocation of type rtype, addend -4)
};
struct Mem {
    uint8_t kind;
    uint8_t reg;
    uint16_t rtype;
    int32_t disp;
    uint32_t sym;
};

struct Rela {      // = Elf64_Rela
    uint64_t offset;
    uint64_t info;  // (symbol << 32) | type
    int64_t addend;
};

struct Fixup {     // rel32 at code[pos] -> start of local block `block`
    uint32_t pos;
    uint32_t block;
};

// ---------------------------------------------------------------------- state

const GirModule *M;

Bump code;        // .text
std::vector<Rela> rela_text;      // .rela.text
std::vector<uint8_t> sdata;       // .data
std::vector<uint8_t> srodata;     // .rodata
uint64_t bss_size;
uint64_t data_align, rodata_align, bss_align;

// Per global (index = GIR global index).
std::vector<uint32_t> g_sym;      // ELF symbol index
std::vector<uint32_t> g_sec;      // ELF section index, 0 = undefined
std::vector<uint64_t> g_value;    // offset inside its section
std::vector<uint64_t> g_size;
std::vector<uint8_t> g_has_reloc; // variable has data relocations
uint32_t n_local_syms;            // = index of the first non-local symbol

// Per function (index = local instruction / block / argument number).
uint32_t f_first_inst, f_first_block, f_arg_tys;
std::vector<int32_t> v_off;       // rbp offset of the result slot, or of the alloca area
std::vector<int32_t> t_off;       // rbp offset of a PHI's temp slot
std::vector<int32_t> a_off;       // rbp offset of an argument's slot
std::vector<uint32_t> block_off;  // code offset of each block
std::vector<Fixup> fixups;

// ----------------------------------------------------------------- byte output

__attribute__((always_inline)) inline void b1(uint32_t x) { code.push_back((uint8_t)x); }
__attribute__((always_inline)) inline void b4(uint32_t x) {
    b1(x);
    b1(x >> 8);
    b1(x >> 16);
    b1(x >> 24);
}
__attribute__((always_inline)) inline void b8(uint64_t x) {
    b4((uint32_t)x);
    b4((uint32_t)(x >> 32));
}
void patch4(uint32_t pos, uint32_t x) {
    code[pos] = (uint8_t)x;
    code[pos + 1] = (uint8_t)(x >> 8);
    code[pos + 2] = (uint8_t)(x >> 16);
    code[pos + 3] = (uint8_t)(x >> 24);
}
__attribute__((always_inline)) inline uint32_t here() { return (uint32_t)code.size(); }

bool fits8(int64_t v) { return v >= -128 && v <= 127; }
bool fits32(int64_t v) { return v >= -2147483648LL && v <= 2147483647LL; }

// ------------------------------------------------------------------ encoder

// REX prefix: w = 64-bit operand size, reg = ModRM.reg register, rm = ModRM.rm
// (or base) register. `force` emits a bare REX (0x40), needed to address
// spl/bpl/sil/dil as byte registers.
__attribute__((always_inline)) inline void rex(int w, int reg, int rm, int force) {
    uint32_t r = 0x40 | ((uint32_t)w << 3) | ((uint32_t)(reg >> 3) << 2) | (uint32_t)(rm >> 3);
    if (r != 0x40 || force) b1(r);
}
// One- or two-byte opcode (0x0FB6 = 0F B6).
__attribute__((always_inline)) inline void opc(uint32_t op) {
    if (op > 0xFF) b1(op >> 8);
    b1(op & 0xFF);
}
__attribute__((always_inline)) inline void modrm_mem(int reg, const Mem &x) {
    uint32_t r = (uint32_t)(reg & 7) << 3;
    if (x.kind == M_RBP) {
        if (fits8(x.disp)) {
            b1(0x45 | r);
            b1((uint32_t)x.disp);
        } else {
            b1(0x85 | r);
            b4((uint32_t)x.disp);
        }
    } else if (x.kind == M_RSP) {
        if (fits8(x.disp)) {
            b1(0x44 | r);
            b1(0x24);
            b1((uint32_t)x.disp);
        } else {
            b1(0x84 | r);
            b1(0x24);
            b4((uint32_t)x.disp);
        }
    } else if (x.kind == M_REG) {
        b1(r | (uint32_t)(x.reg & 7));
    } else {
        b1(r | 5);
        rela_text.push_back(Rela{here(), ((uint64_t)x.sym << 32) | x.rtype, -4});
        b4(0);
    }
}
// [66] [REX] opcode ModRM(reg, mem). byte_reg: `reg` is an 8-bit register.
__attribute__((always_inline)) inline void op_mem(int p66, int w, uint32_t op, int reg, const Mem &x, int byte_reg) {
    if (p66) b1(0x66);
    rex(w, reg, x.kind == M_REG ? x.reg : 0, byte_reg && reg >= 4 && reg < 8);
    opc(op);
    modrm_mem(reg, x);
}
// [REX] opcode ModRM(11, reg, rm). force: see rex().
__attribute__((always_inline)) inline void op_rr(int w, uint32_t op, int reg, int rm, int force) {
    rex(w, reg, rm, force);
    opc(op);
    b1(0xC0 | ((uint32_t)(reg & 7) << 3) | (uint32_t)(rm & 7));
}

Mem m_rbp(int32_t disp) { return Mem{M_RBP, 0, 0, disp, 0}; }
Mem m_rsp(int32_t disp) { return Mem{M_RSP, 0, 0, disp, 0}; }
Mem m_reg(int r) { return Mem{M_REG, (uint8_t)r, 0, 0, 0}; }
Mem m_rip(uint32_t g, uint32_t rtype) { return Mem{M_RIP, 0, (uint16_t)rtype, 0, g_sym[g]}; }

void load64(int r, const Mem &x) { op_mem(0, 1, 0x8B, r, x, 0); }   // mov r64, [m]
void store64(const Mem &x, int r) { op_mem(0, 1, 0x89, r, x, 0); }  // mov [m], r64
void lea64(int r, const Mem &x) { op_mem(0, 1, 0x8D, r, x, 0); }    // lea r64, [m]
// Zero-extending load of type t.
void load_typed(int r, const Mem &x, uint32_t t) {
    if (t == GIR_T_I1 || t == GIR_T_I8) op_mem(0, 0, 0x0FB6, r, x, 0);       // movzx r32, byte [m]
    else if (t == GIR_T_I16) op_mem(0, 0, 0x0FB7, r, x, 0);                  // movzx r32, word [m]
    else if (t == GIR_T_I32) op_mem(0, 0, 0x8B, r, x, 0);                    // mov r32, [m]
    else load64(r, x);
}
void store_typed(const Mem &x, int r, uint32_t t) {
    if (t == GIR_T_I1 || t == GIR_T_I8) op_mem(0, 0, 0x88, r, x, 1);         // mov [m], r8
    else if (t == GIR_T_I16) op_mem(1, 0, 0x89, r, x, 0);                    // mov [m], r16
    else if (t == GIR_T_I32) op_mem(0, 0, 0x89, r, x, 0);                    // mov [m], r32
    else store64(x, r);
}
void mov_rr64(int d, int s) { op_rr(1, 0x89, s, d, 0); }
void mov_rr32(int d, int s) { op_rr(0, 0x89, s, d, 0); }
void alu_rr64(uint32_t op, int d, int s) { op_rr(1, op, s, d, 0); }
void imul_rr64(int d, int s) { op_rr(1, 0x0FAF, d, s, 0); }
void imul_rri64(int d, int s, int32_t imm) {
    op_rr(1, 0x69, d, s, 0);
    b4((uint32_t)imm);
}
void grp1_ri64(int ext, int r, int32_t imm) {
    if (fits8(imm)) {
        op_rr(1, 0x83, ext, r, 0);
        b1((uint32_t)imm);
    } else {
        op_rr(1, 0x81, ext, r, 0);
        b4((uint32_t)imm);
    }
}
void shift_cl64(int ext, int r) { op_rr(1, 0xD3, ext, r, 0); }
void shift_imm64(int ext, int r, uint32_t n) {
    op_rr(1, 0xC1, ext, r, 0);
    b1(n);
}
void and_ri32(int r, uint32_t imm8) {
    op_rr(0, 0x83, 4, r, 0);
    b1(imm8);
}
void neg64(int r) { op_rr(1, 0xF7, 3, r, 0); }
void div64(int ext, int r) { op_rr(1, 0xF7, ext, r, 0); }  // 6 = div, 7 = idiv
void setcc(int cc, int r) { op_rr(0, 0x0F90 | (uint32_t)cc, 0, r, r >= 4 && r < 8); }
void movzx8(int d, int s) { op_rr(0, 0x0FB6, d, s, s >= 4 && s < 8); }
void movzx16(int d, int s) { op_rr(0, 0x0FB7, d, s, 0); }
void movsx8_64(int d, int s) { op_rr(1, 0x0FBE, d, s, 0); }
void movsx16_64(int d, int s) { op_rr(1, 0x0FBF, d, s, 0); }
void movsxd(int d, int s) { op_rr(1, 0x63, d, s, 0); }
void test_rr32(int a, int b) { op_rr(0, 0x85, b, a, 0); }
void cmov64(int cc, int d, int s) { op_rr(1, 0x0F40 | (uint32_t)cc, d, s, 0); }
void mov_ri(int r, uint64_t v) {
    if (v <= 0xFFFFFFFFull) {          // mov r32, imm32 (zero-extends)
        rex(0, 0, r, 0);
        b1(0xB8 | (uint32_t)(r & 7));
        b4((uint32_t)v);
    } else if (fits32((int64_t)v)) {   // mov r64, simm32
        op_rr(1, 0xC7, 0, r, 0);
        b4((uint32_t)v);
    } else {                           // movabs r64, imm64
        rex(1, 0, r, 0);
        b1(0xB8 | (uint32_t)(r & 7));
        b8(v);
    }
}
void jmp_block(uint32_t b) {
    b1(0xE9);
    fixups.push_back(Fixup{here(), b});
    b4(0);
}
void jcc_block(int cc, uint32_t b) {
    b1(0x0F);
    b1(0x80 | (uint32_t)cc);
    fixups.push_back(Fixup{here(), b});
    b4(0);
}
// Forward jcc to a label inside the current instruction; returns the rel32
// position for patch_here().
uint32_t jcc_fwd(int cc) {
    b1(0x0F);
    b1(0x80 | (uint32_t)cc);
    uint32_t p = here();
    b4(0);
    return p;
}
void patch_here(uint32_t p) { patch4(p, here() - (p + 4)); }

// -------------------------------------------------------- value conventions

// Values narrower than 64 bits are kept zero-extended in registers and slots.
void zext_reg(int r, uint32_t t) {
    if (t == GIR_T_I1) and_ri32(r, 1);
    else if (t == GIR_T_I8) movzx8(r, r);
    else if (t == GIR_T_I16) movzx16(r, r);
    else if (t == GIR_T_I32) mov_rr32(r, r);
}
void sext_reg(int r, uint32_t t) {
    if (t == GIR_T_I1) {
        and_ri32(r, 1);
        neg64(r);
    } else if (t == GIR_T_I8) movsx8_64(r, r);
    else if (t == GIR_T_I16) movsx16_64(r, r);
    else if (t == GIR_T_I32) movsxd(r, r);
}
uint32_t bits_of(uint32_t t) {
    if (t == GIR_T_I1) return 1;
    if (t == GIR_T_I8) return 8;
    if (t == GIR_T_I16) return 16;
    if (t == GIR_T_I32) return 32;
    return 64;
}
uint32_t type_of(uint32_t v) {
    uint32_t i = GIR_IDX(v);
    uint32_t k = GIR_KIND(v);
    if (k == GIR_V_INST) return M->insts[i].ty;
    if (k == GIR_V_ARG) return M->opnds[f_arg_tys + i];
    if (k == GIR_V_CONST) return M->consts[i].ty;
    return GIR_T_PTR;
}
bool is_alloca(uint32_t v) { return GIR_KIND(v) == GIR_V_INST && M->insts[GIR_IDX(v)].op == GIR_ALLOCA; }
bool is_defined_global(uint32_t v) {
    return GIR_KIND(v) == GIR_V_GLOBAL && (M->globals[GIR_IDX(v)].flags & GIR_GF_DEFINED) != 0;
}

// Loads the value `v` into register r (only r is written).
void load_val(int r, uint32_t v) {
    uint32_t i = GIR_IDX(v);
    uint32_t k = GIR_KIND(v);
    if (k == GIR_V_INST) {
        if (M->insts[i].op == GIR_ALLOCA) lea64(r, m_rbp(v_off[i - f_first_inst]));
        else load64(r, m_rbp(v_off[i - f_first_inst]));
    } else if (k == GIR_V_ARG) {
        load64(r, m_rbp(a_off[i]));
    } else if (k == GIR_V_CONST) {
        mov_ri(r, (uint64_t)M->consts[i].value);
    } else if (M->globals[i].flags & GIR_GF_DEFINED) {
        lea64(r, m_rip(i, R_X86_64_PC32));                // lea r, [rip + sym]
    } else {
        load64(r, m_rip(i, R_X86_64_REX_GOTPCRELX));     // mov r, [rip + sym@GOTPCREL]
    }
}
// Memory operand for the pointer value `v`; loads it into `scratch` unless
// it is an alloca (rbp-relative) or a defined global (rip-relative).
Mem addr_of(uint32_t v, int scratch) {
    if (is_alloca(v)) return m_rbp(v_off[GIR_IDX(v) - f_first_inst]);
    if (is_defined_global(v)) return m_rip(GIR_IDX(v), R_X86_64_PC32);
    load_val(scratch, v);
    return m_reg(scratch);
}
void store_result(uint32_t j, int r) { store64(m_rbp(v_off[j]), r); }

int icmp_cc(uint32_t p) {
    switch (p) {
    case GIR_EQ: return CC_E;
    case GIR_NE: return CC_NE;
    case GIR_UGT: return CC_A;
    case GIR_UGE: return CC_AE;
    case GIR_ULT: return CC_B;
    case GIR_ULE: return CC_BE;
    case GIR_SGT: return CC_G;
    case GIR_SGE: return CC_GE;
    case GIR_SLT: return CC_L;
    default: return CC_LE;
    }
}

// ------------------------------------------------------------------- PHIs

bool has_phi(uint32_t b) {
    const GirBlock &B = M->blocks[f_first_block + b];
    return B.n_inst != 0 && M->insts[B.first_inst].op == GIR_PHI;
}
// Edge from -> to: write each PHI's incoming value into the PHI's temp slot.
void phi_moves(uint32_t from, uint32_t to) {
    const GirBlock &B = M->blocks[f_first_block + to];
    for (uint32_t k = B.first_inst; k < B.first_inst + B.n_inst; k++) {
        const GirInst &I = M->insts[k];
        if (I.op != GIR_PHI) break;
        for (uint32_t p = 0; p < I.c; p++) {
            if (M->opnds[I.b + 2 * p + 1] != from) continue;
            load_val(RAX, M->opnds[I.b + 2 * p]);
            store64(m_rbp(t_off[k - f_first_inst]), RAX);
            break;
        }
    }
}

// ------------------------------------------------------------ instructions

void gen_inst(uint32_t gi, uint32_t cur) {
    const GirInst &I = M->insts[gi];
    uint32_t j = gi - f_first_inst;
    uint32_t next = cur + 1;
    switch (I.op) {
    case GIR_RET:
        if (I.a != GIR_NONE) load_val(RAX, I.a);
        b1(0xC9);  // leave
        b1(0xC3);  // ret
        return;
    case GIR_BR:
        phi_moves(cur, I.a);
        if (I.a != next) jmp_block(I.a);
        return;
    case GIR_CONDBR:
        load_val(RAX, I.a);
        test_rr32(RAX, RAX);
        if (has_phi(I.b) || has_phi(I.c)) {
            uint32_t p = jcc_fwd(CC_E);
            phi_moves(cur, I.b);
            jmp_block(I.b);
            patch_here(p);
            phi_moves(cur, I.c);
            if (I.c != next) jmp_block(I.c);
        } else if (I.b == next) {
            jcc_block(CC_E, I.c);
        } else {
            jcc_block(CC_NE, I.b);
            if (I.c != next) jmp_block(I.c);
        }
        return;
    case GIR_SWITCH: {
        load_val(RAX, I.a);
        for (uint32_t k = 0; k < I.c; k++) {
            int64_t v = M->consts[GIR_IDX(M->opnds[I.b + 1 + 2 * k])].value;
            uint32_t tb = M->opnds[I.b + 2 + 2 * k];
            if (fits32(v)) {
                grp1_ri64(G1_CMP, RAX, (int32_t)v);
            } else {
                mov_ri(RCX, (uint64_t)v);
                alu_rr64(ALU_CMP, RAX, RCX);
            }
            if (has_phi(tb)) {
                uint32_t p = jcc_fwd(CC_NE);
                phi_moves(cur, tb);
                jmp_block(tb);
                patch_here(p);
            } else {
                jcc_block(CC_E, tb);
            }
        }
        uint32_t d = M->opnds[I.b];
        phi_moves(cur, d);
        if (d != next) jmp_block(d);
        return;
    }
    case GIR_UNREACHABLE:
        b1(0x0F);  // ud2
        b1(0x0B);
        return;
    case GIR_ADD: case GIR_SUB: case GIR_MUL: case GIR_AND: case GIR_OR: case GIR_XOR:
        load_val(RAX, I.a);
        load_val(RCX, I.b);
        if (I.op == GIR_ADD) alu_rr64(ALU_ADD, RAX, RCX);
        else if (I.op == GIR_SUB) alu_rr64(ALU_SUB, RAX, RCX);
        else if (I.op == GIR_AND) alu_rr64(ALU_AND, RAX, RCX);
        else if (I.op == GIR_OR) alu_rr64(ALU_OR, RAX, RCX);
        else if (I.op == GIR_XOR) alu_rr64(ALU_XOR, RAX, RCX);
        else imul_rr64(RAX, RCX);
        zext_reg(RAX, I.ty);
        store_result(j, RAX);
        return;
    case GIR_SHL: case GIR_LSHR: case GIR_ASHR:
        load_val(RAX, I.a);
        load_val(RCX, I.b);
        if (I.op == GIR_ASHR) sext_reg(RAX, I.ty);
        shift_cl64(I.op == GIR_SHL ? SH_SHL : I.op == GIR_LSHR ? SH_SHR : SH_SAR, RAX);
        zext_reg(RAX, I.ty);
        store_result(j, RAX);
        return;
    case GIR_SDIV: case GIR_SREM:
        load_val(RAX, I.a);
        load_val(RCX, I.b);
        sext_reg(RAX, I.ty);
        sext_reg(RCX, I.ty);
        b1(0x48);  // cqo
        b1(0x99);
        div64(7, RCX);
        if (I.op == GIR_SREM) mov_rr64(RAX, RDX);
        zext_reg(RAX, I.ty);
        store_result(j, RAX);
        return;
    case GIR_UDIV: case GIR_UREM:
        load_val(RAX, I.a);
        load_val(RCX, I.b);
        op_rr(0, ALU_XOR, RDX, RDX, 0);  // xor edx, edx
        div64(6, RCX);
        if (I.op == GIR_UREM) mov_rr64(RAX, RDX);
        store_result(j, RAX);
        return;
    case GIR_ICMP: {
        load_val(RAX, I.a);
        load_val(RCX, I.b);
        if (I.sub >= GIR_SGT && bits_of(I.aux) < 64) {
            sext_reg(RAX, I.aux);
            sext_reg(RCX, I.aux);
        }
        alu_rr64(ALU_CMP, RAX, RCX);
        setcc(icmp_cc(I.sub), RAX);
        movzx8(RAX, RAX);
        store_result(j, RAX);
        return;
    }
    case GIR_SELECT:
        load_val(RAX, I.a);
        load_val(RCX, I.b);
        load_val(RDX, I.c);
        test_rr32(RAX, RAX);
        cmov64(CC_E, RCX, RDX);
        store_result(j, RCX);
        return;
    case GIR_ZEXT: case GIR_INTTOPTR: case GIR_BITCAST:
        load_val(RAX, I.a);
        store_result(j, RAX);
        return;
    case GIR_TRUNC: case GIR_PTRTOINT:
        load_val(RAX, I.a);
        zext_reg(RAX, I.ty);
        store_result(j, RAX);
        return;
    case GIR_SEXT:
        load_val(RAX, I.a);
        sext_reg(RAX, I.aux);
        zext_reg(RAX, I.ty);
        store_result(j, RAX);
        return;
    case GIR_ALLOCA:
        return;
    case GIR_LOAD: {
        Mem x = addr_of(I.a, RAX);
        load_typed(RAX, x, I.ty);
        if (I.ty == GIR_T_I1) and_ri32(RAX, 1);
        store_result(j, RAX);
        return;
    }
    case GIR_STORE: {
        load_val(RAX, I.a);
        Mem x = addr_of(I.b, RCX);
        store_typed(x, RAX, I.aux);
        return;
    }
    case GIR_GEP: {
        load_val(RAX, I.a);
        int64_t off = (int64_t)((uint64_t)M->opnds[I.b] | ((uint64_t)M->opnds[I.b + 1] << 32));
        for (uint32_t k = 0; k < I.c; k++) {
            uint32_t idx = M->opnds[I.b + 2 + 2 * k];
            uint32_t sc = M->opnds[I.b + 3 + 2 * k];
            if (sc == 0) continue;  // the exporter never emits these
            load_val(RCX, idx);
            sext_reg(RCX, type_of(idx));
            if ((sc & (sc - 1)) == 0) {
                uint32_t sh = 0;
                while ((1u << sh) < sc) sh++;
                if (sh) shift_imm64(SH_SHL, RCX, sh);
            } else if (sc <= 0x7FFFFFFFu) {
                imul_rri64(RCX, RCX, (int32_t)sc);
            } else {
                mov_ri(RDX, sc);
                imul_rr64(RCX, RDX);
            }
            alu_rr64(ALU_ADD, RAX, RCX);
        }
        if (off != 0) {
            if (fits32(off)) {
                grp1_ri64(G1_ADD, RAX, (int32_t)off);
            } else {
                mov_ri(RCX, (uint64_t)off);
                alu_rr64(ALU_ADD, RAX, RCX);
            }
        }
        store_result(j, RAX);
        return;
    }
    case GIR_CALL: {
        uint32_t n = I.c;
        uint32_t s = I.b;
        uint32_t sbytes = n > 6 ? ((n - 6) * 8 + 15) & ~15u : 0;
        if (sbytes) {
            grp1_ri64(G1_SUB, RSP, (int32_t)sbytes);
            for (uint32_t k = 6; k < n; k++) {
                load_val(RAX, M->opnds[s + k]);
                store64(m_rsp((int32_t)(8 * (k - 6))), RAX);
            }
        }
        uint32_t callee = I.a;
        bool direct = GIR_KIND(callee) == GIR_V_GLOBAL && M->globals[GIR_IDX(callee)].kind == GIR_G_FUNC;
        if (!direct) load_val(R11, callee);
        for (uint32_t k = 0; k < n && k < 6; k++) load_val(ARG_REG[k], M->opnds[s + k]);
        if (I.sub & GIR_F_VARARG) mov_ri(RAX, 0);  // al = number of vector registers used
        if (direct) {
            b1(0xE8);  // call rel32
            rela_text.push_back(Rela{here(), ((uint64_t)g_sym[GIR_IDX(callee)] << 32) | R_X86_64_PLT32, -4});
            b4(0);
        } else {
            op_rr(0, 0xFF, 2, R11, 0);  // call r11
        }
        if (sbytes) grp1_ri64(G1_ADD, RSP, (int32_t)sbytes);
        if (I.ty != GIR_T_VOID) {
            zext_reg(RAX, I.ty);
            store_result(j, RAX);
        }
        return;
    }
    case GIR_PHI:
        load64(RAX, m_rbp(t_off[j]));
        store_result(j, RAX);
        return;
    default:
        b1(0x0F);  // unknown opcode: trap
        b1(0x0B);
        return;
    }
}

// --------------------------------------------------------------- functions

void gen_function(uint32_t fi) {
    const GirFunc &f = M->funcs[fi];
    while (code.size() & 15) b1(0xCC);
    uint32_t start = here();
    f_first_inst = f.first_inst;
    f_first_block = f.first_block;
    f_arg_tys = f.arg_tys;

    // Frame layout: argument slots, then one slot per result (two per PHI),
    // alloca areas in between at their alignment. rbp is 16-byte aligned.
    int64_t off = 0;
    if (a_off.size() < f.n_args) a_off.resize(f.n_args);
    for (uint32_t a = 0; a < f.n_args; a++) {
        off += 8;
        a_off[a] = (int32_t)-off;
    }
    if (v_off.size() < f.n_inst) {
        v_off.resize(f.n_inst);
        t_off.resize(f.n_inst);
    }
    for (uint32_t j = 0; j < f.n_inst; j++) {
        const GirInst &I = M->insts[f.first_inst + j];
        if (I.op == GIR_ALLOCA) {
            int64_t al = I.b ? I.b : 1;
            int64_t size = I.a ? I.a : 1;
            off = (off + size + al - 1) / al * al;
            v_off[j] = (int32_t)-off;
        } else if (I.ty != GIR_T_VOID) {
            off = ((off + 7) & ~(int64_t)7) + 8;  // slots stay 8-byte aligned
            v_off[j] = (int32_t)-off;
            if (I.op == GIR_PHI) {
                off += 8;
                t_off[j] = (int32_t)-off;
            }
        }
    }
    int64_t frame = (off + 15) & ~(int64_t)15;

    // Prologue: push rbp; mov rbp, rsp; sub rsp, frame; spill arguments.
    b1(0x55);
    b1(0x48);
    b1(0x89);
    b1(0xE5);
    if (frame) grp1_ri64(G1_SUB, RSP, (int32_t)frame);
    for (uint32_t a = 0; a < f.n_args; a++) {
        uint32_t t = M->opnds[f.arg_tys + a];
        if (a < 6) {
            zext_reg(ARG_REG[a], t);
            store64(m_rbp(a_off[a]), ARG_REG[a]);
        } else {
            load64(RAX, m_rbp((int32_t)(16 + 8 * (a - 6))));
            zext_reg(RAX, t);
            store64(m_rbp(a_off[a]), RAX);
        }
    }

    if (block_off.size() < f.n_blocks) block_off.resize(f.n_blocks);
    fixups.clear();
    for (uint32_t b = 0; b < f.n_blocks; b++) {
        block_off[b] = here();
        const GirBlock &B = M->blocks[f.first_block + b];
        for (uint32_t k = B.first_inst; k < B.first_inst + B.n_inst; k++) gen_inst(k, b);
    }
    for (uint32_t k = 0; k < fixups.size(); k++)
        patch4(fixups[k].pos, block_off[fixups[k].block] - (fixups[k].pos + 4));

    g_value[f.global] = start;
    g_size[f.global] = here() - start;
}

// ------------------------------------------------------------ data layout

void append_aligned(std::vector<uint8_t> &sec, uint64_t &sec_align, uint32_t g) {
    const GirGlobal &G = M->globals[g];
    uint64_t al = G.align ? G.align : 1;
    while (sec.size() % al) sec.push_back(0);
    if (al > sec_align) sec_align = al;
    g_value[g] = sec.size();
    sec.insert(sec.end(), M->data + G.data, M->data + G.data + G.size);
}

void layout_globals() {
    uint32_t n = M->n_globals;
    g_sym.assign(n, 0);
    g_sec.assign(n, SEC_NULL);
    g_value.assign(n, 0);
    g_size.assign(n, 0);
    g_has_reloc.assign(n, 0);
    for (uint32_t i = 0; i < M->n_drelocs; i++) g_has_reloc[M->drelocs[i].owner] = 1;

    // Symbol indices: null symbol, then all local symbols, then the rest.
    uint32_t next = 1;
    for (uint32_t g = 0; g < n; g++)
        if (M->globals[g].flags & GIR_GF_INTERNAL) g_sym[g] = next++;
    n_local_syms = next;
    for (uint32_t g = 0; g < n; g++)
        if (!(M->globals[g].flags & GIR_GF_INTERNAL)) g_sym[g] = next++;

    for (uint32_t g = 0; g < n; g++) {
        const GirGlobal &G = M->globals[g];
        if (!(G.flags & GIR_GF_DEFINED)) continue;
        if (G.kind == GIR_G_FUNC) {
            g_sec[g] = SEC_TEXT;
            continue;
        }
        g_size[g] = G.size;
        if (G.flags & GIR_GF_ZERO) {
            uint64_t al = G.align ? G.align : 1;
            bss_size = (bss_size + al - 1) / al * al;
            if (al > bss_align) bss_align = al;
            g_value[g] = bss_size;
            bss_size += G.size;
            g_sec[g] = SEC_BSS;
        } else if ((G.flags & GIR_GF_CONST) && !g_has_reloc[g]) {
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

void o1(std::vector<uint8_t> &o, uint32_t x) { o.push_back((uint8_t)x); }
void o2(std::vector<uint8_t> &o, uint32_t x) {
    o1(o, x);
    o1(o, x >> 8);
}
void o4(std::vector<uint8_t> &o, uint32_t x) {
    o2(o, x);
    o2(o, x >> 16);
}
void o8(std::vector<uint8_t> &o, uint64_t x) {
    o4(o, (uint32_t)x);
    o4(o, (uint32_t)(x >> 32));
}
void opad(std::vector<uint8_t> &o, uint64_t al) {
    while (o.size() % al) o.push_back(0);
}
void obytes(std::vector<uint8_t> &o, const uint8_t *p, uint64_t n) {
    o.insert(o.end(), p, p + n);
}

void write_elf(std::vector<uint8_t> &o) {
    // Section header string table and name offsets.
    static const char *names[SEC_COUNT] = {"", ".text", ".data", ".bss", ".rodata", ".rela.text",
                                           ".rela.data", ".symtab", ".strtab", ".shstrtab",
                                           ".note.GNU-stack"};
    std::vector<uint8_t> shstr;
    uint32_t sh_name[SEC_COUNT];
    for (uint32_t s = 0; s < SEC_COUNT; s++) {
        sh_name[s] = (uint32_t)shstr.size();
        shstr.insert(shstr.end(), names[s], names[s] + std::strlen(names[s]));
        shstr.push_back(0);
    }
    uint64_t sh_off[SEC_COUNT] = {0};
    uint64_t sh_size[SEC_COUNT] = {0};

    o.clear();
    o.reserve(code.size() + sdata.size() + srodata.size() + 24 * (rela_text.size() + M->n_drelocs + M->n_globals + 1) + M->n_strtab + 4096);
    // ELF header (e_shoff patched below).
    o1(o, 0x7F); o1(o, 'E'); o1(o, 'L'); o1(o, 'F');
    o1(o, 2);  // ELFCLASS64
    o1(o, 1);  // ELFDATA2LSB
    o1(o, 1);  // EV_CURRENT
    for (int i = 0; i < 9; i++) o1(o, 0);
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
    sh_off[SEC_TEXT] = o.size();
    obytes(o, code.data(), code.size());
    sh_size[SEC_TEXT] = code.size();

    opad(o, data_align);
    sh_off[SEC_DATA] = o.size();
    obytes(o, sdata.data(), sdata.size());
    sh_size[SEC_DATA] = sdata.size();

    sh_off[SEC_BSS] = o.size();
    sh_size[SEC_BSS] = bss_size;

    opad(o, rodata_align);
    sh_off[SEC_RODATA] = o.size();
    obytes(o, srodata.data(), srodata.size());
    sh_size[SEC_RODATA] = srodata.size();

    opad(o, 8);
    sh_off[SEC_RELA_TEXT] = o.size();
    for (uint32_t i = 0; i < rela_text.size(); i++) {
        o8(o, rela_text[i].offset);
        o8(o, rela_text[i].info);
        o8(o, (uint64_t)rela_text[i].addend);
    }
    sh_size[SEC_RELA_TEXT] = o.size() - sh_off[SEC_RELA_TEXT];

    sh_off[SEC_RELA_DATA] = o.size();
    for (uint32_t i = 0; i < M->n_drelocs; i++) {
        const GirDataReloc &d = M->drelocs[i];
        o8(o, g_value[d.owner] + d.offset);
        o8(o, ((uint64_t)g_sym[d.target] << 32) | R_X86_64_64);
        o8(o, (uint64_t)(int64_t)d.addend);
    }
    sh_size[SEC_RELA_DATA] = o.size() - sh_off[SEC_RELA_DATA];

    // Symbol table: null, locals, then globals (same order as g_sym).
    sh_off[SEC_SYMTAB] = o.size();
    for (int i = 0; i < 24; i++) o1(o, 0);
    for (uint32_t pass = 0; pass < 2; pass++) {
        for (uint32_t g = 0; g < M->n_globals; g++) {
            const GirGlobal &G = M->globals[g];
            uint32_t local = (G.flags & GIR_GF_INTERNAL) != 0;
            if (local != (pass == 0 ? 1u : 0u)) continue;
            uint32_t bind = local ? 0 : (G.flags & GIR_GF_WEAK) ? 2 : 1;  // STB_LOCAL/GLOBAL/WEAK
            uint32_t type = !(G.flags & GIR_GF_DEFINED) ? 0 : G.kind == GIR_G_FUNC ? 2 : 1;  // NOTYPE/FUNC/OBJECT
            o4(o, G.name);
            o1(o, (bind << 4) | type);
            o1(o, 0);
            o2(o, g_sec[g]);
            o8(o, g_value[g]);
            o8(o, g_size[g]);
        }
    }
    sh_size[SEC_SYMTAB] = o.size() - sh_off[SEC_SYMTAB];

    // The GIR string table is a valid ELF string table (gir.h).
    sh_off[SEC_STRTAB] = o.size();
    if (M->n_strtab) obytes(o, M->strtab, M->n_strtab);
    else o1(o, 0);
    sh_size[SEC_STRTAB] = o.size() - sh_off[SEC_STRTAB];

    sh_off[SEC_SHSTRTAB] = o.size();
    obytes(o, shstr.data(), shstr.size());
    sh_size[SEC_SHSTRTAB] = shstr.size();

    sh_off[SEC_NOTE] = o.size();

    // Section headers.
    opad(o, 8);
    uint64_t shoff = o.size();
    for (int i = 0; i < 8; i++) o[40 + i] = (uint8_t)(shoff >> (8 * i));
    //                         type flags  link        info           align         entsize
    static const uint32_t sh_type[SEC_COUNT] = {0, 1, 1, 8, 1, 4, 4, 2, 3, 3, 1};
    static const uint32_t sh_flags[SEC_COUNT] = {0, 6, 3, 3, 2, 0x40, 0x40, 0, 0, 0, 0};
    for (uint32_t s = 0; s < SEC_COUNT; s++) {
        uint32_t link = 0, info = 0;
        uint64_t align = 1, entsize = 0;
        if (s == SEC_TEXT) align = 16;
        if (s == SEC_DATA) align = data_align;
        if (s == SEC_BSS) align = bss_align;
        if (s == SEC_RODATA) align = rodata_align;
        if (s == SEC_RELA_TEXT || s == SEC_RELA_DATA) {
            link = SEC_SYMTAB;
            info = s == SEC_RELA_TEXT ? SEC_TEXT : SEC_DATA;
            align = 8;
            entsize = 24;
        }
        if (s == SEC_SYMTAB) {
            link = SEC_STRTAB;
            info = n_local_syms;
            align = 8;
            entsize = 24;
        }
        if (s == SEC_NULL) align = 0;
        o4(o, s == SEC_NULL ? 0 : sh_name[s]);
        o4(o, sh_type[s]);
        o8(o, sh_flags[s]);
        o8(o, 0);  // sh_addr
        o8(o, sh_off[s]);
        o8(o, sh_size[s]);
        o4(o, link);
        o4(o, info);
        o8(o, align);
        o8(o, entsize);
    }
}

}  // namespace

void gir_codegen_cpp(const GirModule &m, std::vector<uint8_t> &obj_out) {
    M = &m;
    code.clear();
    code.reserve(64u << 20);
    rela_text.reserve(4u << 20);
    rela_text.clear();
    sdata.clear();
    srodata.clear();
    bss_size = 0;
    data_align = rodata_align = bss_align = 1;
    layout_globals();
    for (uint32_t fi = 0; fi < m.n_funcs; fi++) gen_function(fi);
    write_elf(obj_out);
}
