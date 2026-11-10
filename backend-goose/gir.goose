// GIR version 2 records and constants, mirroring gir/gir.h byte for byte.
// tools/goovm-llc checks the size and key field offsets of the generated C
// structs with static_asserts. Field names follow gir.h except where gir.h
// uses a Goose keyword.

// r0 = opt_level (E1), r1 = target (F1: GIR_TARGET_*), r2 = tbaa (E2)
struct Header { version: u32, flags: u32, tls_get_addr: u32, n_llvm_insts: u32,
                r0: u32, r1: u32, r2: u32, r3: u32 }
let GIR_TARGET_X86_64 = 0;
let GIR_TARGET_AARCH64 = 1;
struct TypeDef { kind: u8, cls: u8, bits: u16, size: u32, align: u32, store: u32, n: u32, elems: u32 }
struct Func { global: u32, flags: u32, first_block: u32, n_blocks: u32, first_inst: u32,
              n_inst: u32, n_args: u32, args: u32, ret_ty: u32, dbg: u32 }
struct Block { first_inst: u32, n_inst: u32 }
struct Inst { op: u8, sub: u8, flags: u16, ty: u16, aux: u16, a: u32, b: u32, c: u32, dbg: u32 }
struct Const { lo: u64, hi: u64, ty: u32, data: u32 }
struct Global { name: u32, name_len: u32, kind: u32, flags: u32, data: u32, size: u32,
                align: u32, func: u32, section: u32, aux: u32 }
struct Section { name: u32, name_len: u32, flags: u32, typ: u32 }  // typ = GirSection.type (`type` is a keyword)
struct DataReloc { owner: u32, offset: u32, target: u32, kind: u32, addend: i64, blk: u32, blk2: u32 }
struct DLoc { line: u32, col: u32, scope: u32, inlined_at: u32 }
struct DScope { kind: u32, parent: u32, file: u32, line: u32, name: u32, extra: u32 }
struct DFile { name: u32, dir: u32 }
struct Asm { code: u32, code_len: u32, n_in: u32, n_out: u32, ops: u32, x87_pop: u32 }
// Additive tables (exception handling, comdats, debug information entries).
struct Eh { func: u32, personality: u32, ttypes: u32, n_ttypes: u32, specs: u32, n_specs: u32 }
struct Comdat { name: u32, name_len: u32, sig: u32, kind: u32 }
struct Die { tag: u16, flags: u16, parent: u32, attrs: u32, n_attrs: u32 }
struct DAttr { at: u16, form: u16, aux: u32, val: u64 }

// The module, as read-only views of the host's tables (set at entry).
struct Module {
    header: const Header[:],
    types: const TypeDef[:],
    funcs: const Func[:],
    blocks: const Block[:],
    insts: const Inst[:],
    opnds: const u32[:],
    consts: const Const[:],
    globals: const Global[:],
    sections: const Section[:],
    data: const u8[:],
    drelocs: const DataReloc[:],
    strtab: const u8[:],
    dlocs: const DLoc[:],
    dscopes: const DScope[:],
    dfiles: const DFile[:],
    dstr: const u8[:],
    asms: const Asm[:],
    ehs: const Eh[:],
    comdats: const Comdat[:],
    gcomdat: const u32[:],
    dies: const Die[:],
    dattrs: const DAttr[:],
}

let GIR_V_INST = 0;
let GIR_V_ARG = 1;
let GIR_V_CONST = 2;
let GIR_V_GLOBAL = 3;
let GIR_NONE = 0xFFFFFFFF;

checkfree fn gir_kind(v: u32) -> u32 { v >> 30 }
checkfree fn gir_idx(v: u32) -> u32 { v & 0x3FFFFFFF }

// Predefined type ids.
let GIR_T_VOID = 0;
let GIR_T_I1 = 1;
let GIR_T_I8 = 2;
let GIR_T_I16 = 3;
let GIR_T_I32 = 4;
let GIR_T_I64 = 5;
let GIR_T_PTR = 6;
let GIR_T_F32 = 7;
let GIR_T_F64 = 8;
let GIR_T_F80 = 9;
let GIR_T_I128 = 10;
let GIR_T_F16 = 11;
let GIR_T_F128 = 12;     // (additive, F1: AArch64 long double)

// Type kinds and value classes.
let TK_VOID = 0;
let TK_INT = 1;
let TK_PTR = 2;
let TK_FLOAT = 3;
let TK_VECTOR = 4;
let TK_STRUCT = 5;
let TK_ARRAY = 6;

let C_NONE = 0;
let C_INT = 1;
let C_INT2 = 2;
let C_FP = 3;
let C_X87 = 4;
let C_VEC = 5;
let C_MEM = 6;

// Opcodes (gir.h enum GirOp, in order).
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
let GIR_FADD = 32;
let GIR_FSUB = 33;
let GIR_FMUL = 34;
let GIR_FDIV = 35;
let GIR_FNEG = 36;
let GIR_FCMP = 37;
let GIR_FPEXT = 38;
let GIR_FPTRUNC = 39;
let GIR_FPTOSI = 40;
let GIR_FPTOUI = 41;
let GIR_SITOFP = 42;
let GIR_UITOFP = 43;
let GIR_EXTRACTVALUE = 44;
let GIR_INSERTVALUE = 45;
let GIR_EXTRACTELT = 46;
let GIR_INSERTELT = 47;
let GIR_SHUFFLE = 48;
let GIR_DYNALLOCA = 49;
let GIR_STACKSAVE = 50;
let GIR_STACKRESTORE = 51;
let GIR_VASTART = 52;
let GIR_MEMCPY = 53;
let GIR_MEMSET = 54;
let GIR_CTLZ = 55;
let GIR_CTTZ = 56;
let GIR_CTPOP = 57;
let GIR_BSWAP = 58;
let GIR_BITREVERSE = 59;
let GIR_FSHL = 60;
let GIR_FSHR = 61;
let GIR_OVF = 62;
let GIR_SCMP = 63;
let GIR_UCMP = 64;
let GIR_FABS = 65;
let GIR_COPYSIGN = 66;
let GIR_FSQRT = 67;
let GIR_ISFPCLASS = 68;
let GIR_CMPXCHG = 69;
let GIR_ATOMICRMW = 70;
let GIR_FENCE = 71;
let GIR_TLSADDR = 72;
let GIR_FRAMEADDR = 73;
let GIR_RETADDR = 74;
let GIR_SJLJ_SETJMP = 75;
let GIR_SJLJ_LONGJMP = 76;
let GIR_TRAP = 77;
let GIR_DEBUGTRAP = 78;
let GIR_INDIRECTBR = 79;
let GIR_BLOCKADDR = 80;
let GIR_X86 = 81;
let GIR_ASM = 82;
let GIR_LANDINGPAD = 83;
let GIR_NOPS = 84;            // opcode count of the x86-64 back-end's tables (up to LANDINGPAD)
let GIR_FMA = 84;             // (additive, F1: AArch64)
let GIR_A64 = 85;             // (additive, F1: AArch64 intrinsics)
let GIR_NOPS_ALL = 86;        // opcode count (F1)
let ASMREG_V0 = 32;           // AArch64 inline-asm register numbers: 0..30 x, 32..63 v
let ASMREG_XMM0 = 16;
let ASMREG_ST0 = 32;

// ICMP predicates.
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

// FCMP predicates (LLVM numbering).
let F_FALSE = 0;
let F_OEQ = 1;
let F_OGT = 2;
let F_OGE = 3;
let F_OLT = 4;
let F_OLE = 5;
let F_ONE = 6;
let F_ORD = 7;
let F_UNO = 8;
let F_UEQ = 9;
let F_UGT = 10;
let F_UGE = 11;
let F_ULT = 12;
let F_ULE = 13;
let F_UNE = 14;
let F_TRUE = 15;

let OVF_SADD = 0;
let OVF_UADD = 1;
let OVF_SSUB = 2;
let OVF_USUB = 3;
let OVF_SMUL = 4;
let OVF_UMUL = 5;

let RMW_XCHG = 0;
let RMW_ADD = 1;
let RMW_SUB = 2;
let RMW_AND = 3;
let RMW_NAND = 4;
let RMW_OR = 5;
let RMW_XOR = 6;
let RMW_MAX = 7;
let RMW_MIN = 8;
let RMW_UMAX = 9;
let RMW_UMIN = 10;
let RMW_FADD = 11;
let RMW_FSUB = 12;

let X86_MAXPS = 0;
let X86_MINPS = 1;
let X86_MOVMSKPS = 2;
let X86_PACKSSDW = 3;
let X86_PSLLIW = 4;
let X86_PSRLIW = 5;
let X86_PSRAIW = 6;
let X86_PSLLID = 7;
let X86_PSRLID = 8;
let X86_PSRAID = 9;

// Instruction flags.
let IF_VOLATILE = 0x0001;
let IF_ORD_SHIFT = 1;
let IF_ORD_MASK = 0x000E;
let IF_SINGLETHREAD = 0x0100;
let IF_VARARG = 0x0200;
let IF_NORETURN = 0x0400;
let IF_INVOKE = 0x0800;
let IF_NSW = 0x1000;
let IF_NOINLINE_CALL = 0x2000;      // (E2) CALL: call-site noinline
let IF_ALWAYSINLINE_CALL = 0x4000;  // (E2) CALL: call-site always_inline
let IF_CALL_NOWRITE = 0x8000;       // (E2) CALL: writes no memory
let IF_CALL_NOREAD = 0x0040;        // (E2) CALL: reads no memory
let IF_CALL_PURE = 0x0020;          // (E2) CALL: nounwind, willreturn
let ORD_SEQ_CST = 7;

// ABI words.
let ABI_BYVAL = 0x80000000;
let ABI_SRET = 0x40000000;
let ABI_NOALIAS = 0x20000000;       // (E2) a noalias (restrict) pointer parameter

checkfree fn abi_size(w: u32) -> u32 { w & 0x00FFFFFF }
checkfree fn abi_align(w: u32) -> u32 { (1 as u32) << ((w >> 24) & 0x1F) }

// Function flags.
let FN_VARARG = 2;
let FN_INTERNAL = 4;
let FN_VASTART = 8;
let FN_SJLJ = 16;
let FN_RETURNS_TWICE = 32;
let FN_NOINLINE: u32 = 64;          // (E1)
let FN_ALWAYSINLINE: u32 = 128;     // (E1)
let FN_OPTNONE: u32 = 256;          // (E2) LLVM's function attributes
let FN_OPTSIZE: u32 = 512;
let FN_MINSIZE: u32 = 1024;
let FN_COLD: u32 = 2048;
let FN_HOT: u32 = 4096;
let FN_INLINEHINT: u32 = 8192;
let FN_AVAILEXT: u32 = 16384;       // available_externally body: inlining only, never emitted
let FN_ALIGN_SHIFT = 24;

// Globals.
let G_FUNC = 0;
let G_VAR = 1;
let G_ALIAS = 2;
let GF_DEFINED = 1;
let GF_INTERNAL = 2;
let GF_CONST = 4;
let GF_ZERO = 8;
let GF_WEAK = 16;
let GF_TLS = 32;
let GF_COMMON = 64;
let GF_HIDDEN = 128;
let GF_PROTECTED = 256;
let GF_LOCALREF = 512;
let GF_RELOCS = 1024;

// Sections.
let SF_WRITE = 1;
let SF_EXEC = 2;
let SF_TLS = 4;
let SF_NOBITS = 8;

// Data relocations.
let DR_ABS64 = 0;
let DR_BLOCK = 1;
let DR_BLOCKDIFF32 = 2;
let DR_PCREL32 = 3;      // (additive, E1)

let MF_PIE = 1;

// Comdat kinds.
let CD_ANY = 0;
let CD_NODEDUP = 1;

// GIR attribute forms (GirDAttr.form).
let DF_STR = 0x7F01;
let DF_FILE = 0x7F02;
let DF_PC = 0x7F03;
let DF_SCOPE_PC = 0x7F04;
let DF_FRAME_BASE = 0x7F05;
let DF_LOCAL = 0x7F06;
let DF_GLOBAL = 0x7F07;
let DF_STMT_LIST = 0x7F08;
let DF_STR_BASE = 0x7F09;
let DF_CU_PC = 0x7F0A;
let DF_ADDR_BASE = 0x7F0B;
let DF_LABEL = 0x7F0C;

// Debug scope kinds.
let DS_CU = 1;
let DS_SUBPROGRAM = 2;
let DS_LEXICAL = 3;
let DS_FILE = 4;
