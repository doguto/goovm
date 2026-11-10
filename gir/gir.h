/* GIR: goovm's flat IR, version 2.
 *
 * GIR is the hand-off format between LLVM and goovm's fast back-end. The
 * C++ exporter (tools/goovm-llc/gir_export.cpp) walks an llvm::Module once
 * and fills these tables; the Goose back-end (backend-goose/) reads them
 * and writes an ELF64 x86-64 or (milestone F1, GirHeader.target) AArch64
 * relocatable object.
 *
 * Every record is a fixed-size struct whose fields are naturally aligned
 * with no padding, so the same bytes are valid as a C struct and as the
 * packed C struct that Goose generates for the matching Goose struct. The
 * host passes each table to Goose as a slice ({ data, len }) without
 * copying. Indices are u32 and global to the module unless stated
 * otherwise. gir/README.md describes the format in prose and lists the
 * changes from version 0; this header is the normative definition.
 *
 * ------------------------------------------------------------------------
 * Value references (u32), used by instruction operands:
 *
 *   bits 31..30  kind
 *     0  GIR_V_INST   instruction result; low 30 bits = index into insts
 *                     (module-global index; always inside the same function)
 *     1  GIR_V_ARG    function argument; low 30 bits = argument number
 *     2  GIR_V_CONST  constant; low 30 bits = index into consts
 *     3  GIR_V_GLOBAL address of a global; low 30 bits = index into globals
 *
 *   GIR_NONE (0xFFFFFFFF) means "no value" (e.g. `ret void`).
 *
 * The type of a value reference is always recoverable from the tables:
 *   INST -> insts[i].ty, ARG -> opnds[func.args + 2*i],
 *   CONST -> consts[i].ty, GLOBAL -> GIR_T_PTR.
 *
 * Block references inside a function are local block numbers
 * (0 = entry block), i.e. relative to Func.first_block.
 * ------------------------------------------------------------------------
 *
 * Structural rules (guaranteed by the exporter, relied on by back-ends):
 *  - Functions own a contiguous range of blocks and of instructions; each
 *    block owns a contiguous range of instructions; layout order is the
 *    order of the tables. The entry block is local block 0 and has no
 *    predecessors.
 *  - Every block ends with exactly one terminator (RET, BR, CONDBR, SWITCH,
 *    INDIRECTBR, UNREACHABLE); no terminator appears elsewhere. An
 *    instruction that never returns (TRAP, SJLJ_LONGJMP, a noreturn CALL)
 *    is still followed by a terminator.
 *  - PHIs appear only at the start of a block, before any other
 *    instruction. A PHI has exactly one (value, pred) pair per incoming
 *    CFG edge; a predecessor reached by several edges (switch) appears
 *    several times with the same value.
 *  - ALLOCAs (static, constant size) appear only in the entry block, with
 *    any power-of-two alignment. Every other alloca is a DYNALLOCA.
 *  - Instructions without a result have ty = GIR_T_VOID. An instruction
 *    operand never refers to such an instruction.
 *  - An INST operand refers to an instruction that dominates the use (for a
 *    PHI operand: that dominates the end of the predecessor block). It may
 *    lie later in layout order than the use.
 *  - Operations that need a run-time library function (i128 division,
 *    conversions between i128 and floating point, frem, half <-> float,
 *    the libm intrinsics, large or variable-size memcpy/memmove/memset) are
 *    already explicit CALLs of that function: a back-end never has to name
 *    a symbol that is not in the globals table. (AArch64, additive: the
 *    back-end names the soft-float routines of fp128 arithmetic, compares
 *    and conversions (__addtf3, __lttf2, __extenddftf2, ...) and the
 *    outline-atomics helpers (__aarch64_ldadd4_acq_rel, ...) itself, as
 *    LLVM's AArch64 back-end does.)
 *  - ABI details are lowered as far as the IR allows: arguments with the
 *    LLVM `signext` attribute arrive as an explicit SEXT to i32; a function
 *    whose return has `signext` returns an explicit SEXT to i32 (so RET's
 *    operand may be wider than Func.ret_ty); a function with an `sret`
 *    parameter returns that parameter (Func.ret_ty = GIR_T_PTR). What is
 *    left is the plain LLVM x86-64 C calling convention on the argument and
 *    return types, plus the byval words of CALL and Func arguments.
 *    On AArch64 (additive, F1) it is the LLVM AAPCS64 convention
 *    (CC_AArch64_AAPCS) on the types: INT, FP and vector values of 8 or 16
 *    bytes in x0-x7 / v0-v7; i128 in an even-numbered register pair; an
 *    array whose members are all of one type (HFA [n x float], HVA,
 *    [n x i64]) in consecutive registers of one class, or entirely on the
 *    stack; the GIR_ABI_SRET argument in x8 (not returned); aggregate
 *    returns split into their members (x0-x7, v0-v7). Variadic arguments
 *    are passed like the others.
 */
#ifndef GIR_H
#define GIR_H
#include <stdint.h>

#define GIR_VERSION 2u

#define GIR_V_INST   0u
#define GIR_V_ARG    1u
#define GIR_V_CONST  2u
#define GIR_V_GLOBAL 3u
#define GIR_KIND(v)  ((uint32_t)(v) >> 30)
#define GIR_IDX(v)   ((uint32_t)(v) & 0x3FFFFFFFu)
#define GIR_MK(k, i) (((uint32_t)(k) << 30) | (uint32_t)(i))
#define GIR_NONE     0xFFFFFFFFu

/* ---------------------------------------------------------------- types
 * A type id (u16) is an index into the `types` table. Ids 0..15 are
 * predefined: the exporter always writes these 16 records first, with the
 * kinds, sizes and classes listed here. Further ids are integers of other
 * widths (i24, i48, i72, ...), vectors, structs and arrays. */
enum GirType {
    GIR_T_VOID = 0, GIR_T_I1 = 1, GIR_T_I8 = 2, GIR_T_I16 = 3,
    GIR_T_I32 = 4,  GIR_T_I64 = 5, GIR_T_PTR = 6,
    GIR_T_F32 = 7,  GIR_T_F64 = 8, GIR_T_F80 = 9, GIR_T_I128 = 10,
    GIR_T_F16 = 11,              /* IEEE half (_Float16) */
    GIR_T_F128 = 12,             /* additive (F1): IEEE quad (fp128, AArch64 `long double`) */
    GIR_T_FIRST_USER = 16        /* 13..15 are reserved (kind VOID) */
};

/* Type kinds (GirTypeDef.kind). */
enum GirTypeKind {
    GIR_TK_VOID = 0, GIR_TK_INT = 1, GIR_TK_PTR = 2, GIR_TK_FLOAT = 3,
    GIR_TK_VECTOR = 4, GIR_TK_STRUCT = 5, GIR_TK_ARRAY = 6
};

/* Value classes (GirTypeDef.cls): how a value of the type is held. */
enum GirClass {
    GIR_C_NONE = 0,  /* void */
    GIR_C_INT = 1,   /* integer of 1..64 bits or pointer: one general register */
    GIR_C_INT2 = 2,  /* integer of 65..128 bits: two general registers (lo, hi) */
    GIR_C_FP = 3,    /* f16, f32, f64 (and f128 on AArch64): low part of one SSE register
                        (x86-64) or one SIMD&FP register (AArch64) */
    GIR_C_X87 = 4,   /* f80: x87 stack */
    GIR_C_VEC = 5,   /* fixed vector */
    GIR_C_MEM = 6    /* struct or array (first-class aggregate value) */
};

/* 24 bytes. `size` is the DataLayout allocation size (the stride in an
 * array, the size of a stack slot), `store` the number of bytes a LOAD or
 * STORE of the type touches (i24: store 3, size 4; f80: store 10, size 16).
 * Vectors of i1 are the exception: GIR gives them one byte per lane
 * (store = size = n) and the exporter rejects loads, stores and bitcasts of
 * them, so the in-memory bit packing never matters.
 *   INT    bits = width
 *   PTR    bits = 64
 *   FLOAT  bits = 16, 32, 64, 80 or 128
 *   VECTOR n = lanes, elems = lane type id (an INT of 1/8/16/32/64 bits or
 *          F32/F64); lane k is at byte offset k * types[elems].size
 *   ARRAY  n = elements, elems = element type id
 *   STRUCT n = fields; opnds[elems + 2*i] = type id of field i,
 *          opnds[elems + 2*i + 1] = its byte offset (StructLayout) */
typedef struct GirTypeDef {
    uint8_t  kind;    /* GirTypeKind */
    uint8_t  cls;     /* GirClass */
    uint16_t bits;
    uint32_t size;
    uint32_t align;   /* ABI alignment (power of two) */
    uint32_t store;
    uint32_t n;
    uint32_t elems;
} GirTypeDef;

/* ------------------------------------------------------------- opcodes
 * Operand fields a/b/c of GirInst; "ops[s..s+n)" means the run
 * opnds[s .. s+n). Unused fields are 0. "value" means a value reference,
 * "imm" an immediate, "block" a local block number. Unless stated
 * otherwise an operation on a vector type applies lane by lane. */
enum GirOp {
    /* terminators */
    GIR_RET = 0,       /* a = value or GIR_NONE                               */
    GIR_BR,            /* a = target block                                   */
    GIR_CONDBR,        /* a = i1 cond, b = true block, c = false block        */
    GIR_SWITCH,        /* a = cond (INT or INT2), b = s, c = n: ops[s] =      */
                       /*   default block, then n pairs (const ref, block);  */
                       /*   the case constants have the type of cond and are */
                       /*   distinct                                         */
    GIR_UNREACHABLE,
    /* binary integer ops: a, b values; ty = operand and result type (INT,
     * INT2 or an integer vector; never ptr). Shift amounts >= the width and
     * division by zero are undefined. */
    GIR_ADD, GIR_SUB, GIR_MUL, GIR_SDIV, GIR_UDIV, GIR_SREM, GIR_UREM,
    GIR_AND, GIR_OR, GIR_XOR, GIR_SHL, GIR_LSHR, GIR_ASHR,
    GIR_ICMP,          /* a, b; sub = GirPred; aux = operand type; ty = i1   */
                       /*   (or <n x i1> for vectors)                        */
    GIR_SELECT,        /* a = i1 cond (or <n x i1> with a vector ty),        */
                       /*   b = true value, c = false value; any ty          */
    /* casts: a = source value; ty = destination type; aux = source type */
    GIR_ZEXT, GIR_SEXT, GIR_TRUNC, GIR_PTRTOINT, GIR_INTTOPTR,
    GIR_BITCAST,       /* same size, any classes (f64 <-> i64, vectors, ...) */
    GIR_ALLOCA,        /* a = size in bytes, b = alignment (immediates);      */
                       /*   entry block only; ty = ptr                       */
    GIR_LOAD,          /* a = pointer; ty = loaded type; flags: VOLATILE,     */
                       /*   atomic ordering; b = TBAA node (E2, 0 = none)    */
    GIR_STORE,         /* a = value, b = pointer; aux = stored type; flags;   */
                       /*   c = TBAA node (E2, 0 = none)                     */
    GIR_GEP,           /* a = base pointer, b = s, c = n: ops[s], ops[s+1] = */
                       /*   constant byte offset (lo, hi of an i64), then n  */
                       /*   pairs (index value, scale in bytes); result      */
                       /*   = a + offset + sum(sext64(index) * scale). The   */
                       /*   index type is the type of the index value (INT); */
                       /*   all arithmetic wraps modulo 2^64                 */
    GIR_CALL,          /* a = callee value, b = s, c = n: n pairs            */
                       /*   ops[s+2k] = argument value, ops[s+2k+1] = ABI    */
                       /*   word (GIR_ABI_*); ty = return type; flags:       */
                       /*   GIR_IF_VARARG for a variadic callee              */
    GIR_PHI,           /* b = s, c = n: n pairs (value, pred block)          */
    /* --- version 2 --- */
    GIR_FADD, GIR_FSUB, GIR_FMUL, GIR_FDIV,   /* a, b; ty = FP, X87 or FP vector */
    GIR_FNEG,          /* a                                                  */
    GIR_FCMP,          /* a, b; sub = GirFPred; aux = operand type; ty = i1  */
    GIR_FPEXT, GIR_FPTRUNC,                   /* casts between f32/f64/f80   */
    GIR_FPTOSI, GIR_FPTOUI,                   /* FP/X87 -> INT (<= 64 bits)  */
    GIR_SITOFP, GIR_UITOFP,                   /* INT (<= 64 bits) -> FP/X87  */
    GIR_EXTRACTVALUE,  /* a = aggregate, b = byte offset (imm); ty = field   */
    GIR_INSERTVALUE,   /* a = aggregate, b = field value, c = byte offset    */
                       /*   (imm); ty = aggregate type                       */
    GIR_EXTRACTELT,    /* a = vector, b = lane index value; ty = lane type   */
    GIR_INSERTELT,     /* a = vector, b = lane value, c = lane index value   */
    GIR_SHUFFLE,       /* a, b = vectors (type aux); c = s: ops[s..s+n) =    */
                       /*   lane numbers (n = lanes of ty; lanes of a first, */
                       /*   then b; GIR_NONE = undefined lane)               */
    GIR_DYNALLOCA,     /* a = byte count value (i64), b = alignment (imm);   */
                       /*   ty = ptr; memory below the current stack         */
    GIR_STACKSAVE,     /* ty = ptr                                           */
    GIR_STACKRESTORE,  /* a = value from STACKSAVE                           */
    GIR_VASTART,       /* a = pointer to a va_list (SysV: 24 bytes; AAPCS64: */
                       /*   32 bytes)                                        */
    GIR_MEMCPY,        /* a = dst, b = src, c = byte count (imm, <= 4096);   */
                       /*   non-overlapping                                  */
    GIR_MEMSET,        /* a = dst, b = byte value (i8 value), c = count (imm,*/
                       /*   <= 4096)                                         */
    GIR_CTLZ, GIR_CTTZ, /* a; b = 1 if a zero input is poison (imm)          */
    GIR_CTPOP, GIR_BSWAP, GIR_BITREVERSE,     /* a                           */
    GIR_FSHL, GIR_FSHR,                       /* a, b, c (shift amount)      */
    GIR_OVF,           /* a, b; sub = GirOvf; ty = { iN, i1 } struct: field  */
                       /*   0 = wrapped result, field 1 = overflow bit       */
    GIR_SCMP, GIR_UCMP, /* a, b (type aux); ty = result integer (-1, 0, 1)   */
    GIR_FABS,          /* a                                                  */
    GIR_COPYSIGN,      /* a, b                                               */
    GIR_FSQRT,         /* a                                                  */
    GIR_ISFPCLASS,     /* a (type aux), b = class mask (imm, LLVM FPClassTest)*/
    GIR_CMPXCHG,       /* a = ptr, b = expected, c = new value; aux = value  */
                       /*   type; ty = { iN, i1 } (old value, success);      */
                       /*   flags: orderings, WEAK                           */
    GIR_ATOMICRMW,     /* a = ptr, b = value; sub = GirRmw; ty = value type  */
                       /*   (the old value); flags: ordering                 */
    GIR_FENCE,         /* flags: ordering, SINGLETHREAD                      */
    GIR_TLSADDR,       /* a = TLS global index (imm); ty = ptr: its address  */
                       /*   in the current thread                            */
    GIR_FRAMEADDR,     /* a = level (imm); ty = ptr (llvm.frameaddress)      */
    GIR_RETADDR,       /* a = level (imm); ty = ptr (llvm.returnaddress)     */
    GIR_SJLJ_SETJMP,   /* a = buffer; ty = i32: 0, or 1 after a longjmp.     */
                       /*   Stores the resume address in word 1 of the       */
                       /*   buffer; the IR stored the frame address (word 0) */
                       /*   and STACKSAVE (word 2) itself                    */
    GIR_SJLJ_LONGJMP,  /* a = buffer: restores rbp, rsp, jumps to word 1     */
    GIR_TRAP,          /* ud2                                                */
    GIR_DEBUGTRAP,     /* int3                                               */
    GIR_INDIRECTBR,    /* a = address (from BLOCKADDR), b = s, c = n:        */
                       /*   ops[s..s+n) = possible target blocks             */
    GIR_BLOCKADDR,     /* a = function global index (imm), b = local block of*/
                       /*   that function (imm); ty = ptr                    */
    GIR_X86,           /* x86 SSE intrinsic: sub = GirX86, a, b; ty          */
    GIR_ASM,           /* inline assembly: a = index into asms; ty = void,   */
                       /*   the single output, or a struct of the outputs    */
    /* --- version 2, exception handling (additive) --- */
    GIR_LANDINGPAD,    /* first instruction of a landing pad (a block that   */
                       /*   only INVOKE unwind edges reach; it has no PHIs): */
                       /*   ty = { ptr, i32 } (exception object, selector),  */
                       /*   from rax/edx as the personality routine left     */
                       /*   them. a = s, b = n: ops[s..s+n) = the actions,   */
                       /*   in order: k > 0 catches type index k of the      */
                       /*   function's GirEh type table, k < 0 the exception */
                       /*   specification at byte -k-1 of its spec table,    */
                       /*   k = 0 (last only) cleanup; n = 0: cleanup only   */
                       /*   (AArch64: from x0/w1)                            */
    /* --- version 2, AArch64 (additive, milestone F1; x86-64 producers do
     * not emit these) --- */
    GIR_FMA,           /* a * b + c with a single rounding (llvm.fma,        */
                       /*   llvm.fmuladd on AArch64); ty = f32, f64 or a     */
                       /*   vector of them                                   */
    GIR_A64,           /* AArch64 intrinsic (NEON, ACLE): sub = GirA64;      */
                       /*   ty = result type, aux = operand type; a, b, c =  */
                       /*   operands, or for the forms marked "run" in       */
                       /*   GirA64: b = s, c = n: ops[s..s+n) (a unused)     */
    /* --- version 2, optimizer (additive, milestone E2; emitted at opt_level
     * >= 1 only) --- */
    GIR_ISCONST,       /* a = b = c = a value of any type; ty = i1: whether  */
                       /*   it is a constant once optimized (LLVM            */
                       /*   llvm.is.constant, __builtin_constant_p): the     */
                       /*   middle-end folds it after inlining; never reaches */
                       /*   code generation                                  */
    GIR_OP_COUNT
};

enum GirPred {         /* ICMP predicates */
    GIR_EQ = 0, GIR_NE, GIR_UGT, GIR_UGE, GIR_ULT, GIR_ULE,
    GIR_SGT, GIR_SGE, GIR_SLT, GIR_SLE
};

/* FCMP predicates: the LLVM numbering (CmpInst::FCMP_*). O = ordered (false
 * if either operand is NaN), U = unordered (true if either is NaN). */
enum GirFPred {
    GIR_F_FALSE = 0, GIR_F_OEQ, GIR_F_OGT, GIR_F_OGE, GIR_F_OLT, GIR_F_OLE,
    GIR_F_ONE, GIR_F_ORD, GIR_F_UNO, GIR_F_UEQ, GIR_F_UGT, GIR_F_UGE,
    GIR_F_ULT, GIR_F_ULE, GIR_F_UNE, GIR_F_TRUE
};

enum GirOvf {          /* GIR_OVF.sub (llvm.*.with.overflow) */
    GIR_OVF_SADD = 0, GIR_OVF_UADD, GIR_OVF_SSUB, GIR_OVF_USUB,
    GIR_OVF_SMUL, GIR_OVF_UMUL
};

enum GirRmw {          /* GIR_ATOMICRMW.sub */
    GIR_RMW_XCHG = 0, GIR_RMW_ADD, GIR_RMW_SUB, GIR_RMW_AND, GIR_RMW_NAND,
    GIR_RMW_OR, GIR_RMW_XOR, GIR_RMW_MAX, GIR_RMW_MIN, GIR_RMW_UMAX,
    GIR_RMW_UMIN, GIR_RMW_FADD, GIR_RMW_FSUB
};

enum GirX86 {          /* GIR_X86.sub: operands and result are 16-byte vectors */
    GIR_X86_MAXPS = 0,     /* llvm.x86.sse.max.ps (a, b)                      */
    GIR_X86_MINPS,         /* llvm.x86.sse.min.ps (a, b)                      */
    GIR_X86_MOVMSKPS,      /* llvm.x86.sse.movmsk.ps (a) -> i32               */
    GIR_X86_PACKSSDW,      /* llvm.x86.sse2.packssdw.128 (a, b)               */
    GIR_X86_PSLLIW,        /* llvm.x86.sse2.pslli.w (a, b = i32 count)        */
    GIR_X86_PSRLIW,        /* llvm.x86.sse2.psrli.w                           */
    GIR_X86_PSRAIW,        /* llvm.x86.sse2.psrai.w                           */
    GIR_X86_PSLLID,        /* llvm.x86.sse2.pslli.d                           */
    GIR_X86_PSRLID,        /* llvm.x86.sse2.psrli.d                           */
    GIR_X86_PSRAID         /* llvm.x86.sse2.psrai.d                           */
};

/* GirInst.flags */
#define GIR_IF_VOLATILE      0x0001u
#define GIR_IF_ORD_SHIFT     1        /* bits 1..3: atomic ordering (LLVM AtomicOrdering) */
#define GIR_IF_ORD_MASK      0x000Eu  /*   0 = not atomic, 1 unordered, 2 monotonic,     */
                                      /*   4 acquire, 5 release, 6 acq_rel, 7 seq_cst    */
#define GIR_IF_FORD_SHIFT    4        /* bits 4..6: cmpxchg failure ordering             */
#define GIR_IF_FORD_MASK     0x0070u
#define GIR_IF_WEAK          0x0080u  /* weak cmpxchg                                    */
#define GIR_IF_SINGLETHREAD  0x0100u  /* syncscope("singlethread")                       */
#define GIR_IF_VARARG        0x0200u  /* CALL of a variadic function type                */
#define GIR_IF_NORETURN      0x0400u  /* CALL that does not return                       */
#define GIR_IF_INVOKE        0x0800u  /* CALL that is an invoke: ops[s + 2n] = the local  */
                                      /*   block of its landing pad (the unwind edge);   */
                                      /*   the block's terminator, next, is the BR to    */
                                      /*   the normal destination                        */
#define GIR_IF_NSW           0x1000u  /* additive (E1): ADD, SUB, MUL, SHL whose signed   */
                                      /*   overflow is undefined (LLVM nsw); a hint for  */
                                      /*   the optimizer, ignored by -O0 code generation */
/* additive (milestone E2), CALL only, hints for the optimizer: */
#define GIR_IF_NOINLINE_CALL 0x2000u  /* call-site noinline ([[clang::noinline]],         */
                                      /*   -fno-inline's calls): never inlined           */
#define GIR_IF_ALWAYSINLINE_CALL 0x4000u /* call-site always_inline ([[clang::always_inline]]) */
#define GIR_IF_CALL_NOWRITE  0x8000u  /* the call writes no memory (LLVM readonly/readnone, */
                                      /*   memory(read)); not on invokes or variadic calls */
#define GIR_IF_CALL_NOREAD   0x0040u  /* with NOWRITE: it reads none either (memory(none)) */
#define GIR_IF_CALL_PURE     0x0020u  /* nounwind and willreturn: with NOWRITE, a call      */
                                      /*   whose result is unused may be deleted           */
                                      /* (0x0020 and 0x0040 are cmpxchg's failure ordering */
                                      /*   bits on other instructions)                     */

/* ABI words of CALL arguments and Func arguments. 0 = passed by value as
 * its type says. GIR_ABI_BYVAL: the argument is a pointer whose pointee
 * (size bytes, alignment 1 << align_log2) is copied to the stack argument
 * area; the callee sees the address of that copy. */
#define GIR_ABI_BYVAL        0x80000000u
#define GIR_ABI_SIZE(w)      ((w) & 0x00FFFFFFu)        /* byval size (< 16 MiB) */
#define GIR_ABI_ALIGN_LOG2(w) (((w) >> 24) & 0x1Fu)     /* byval alignment       */
#define GIR_ABI_NOALIAS      0x20000000u  /* additive (E2, opt_level >= 1, Func arguments):
                                             a pointer parameter with LLVM's noalias (C
                                             restrict): no other pointer of the function
                                             that is not based on it accesses what it does */
#define GIR_ABI_SRET         0x40000000u  /* the sret pointer: informational on x86-64
                                             (rdi), passed in x8 on AArch64 */

/* One instruction: 24 bytes. Instructions of a block are contiguous, and
 * blocks of a function are contiguous, in layout order. */
typedef struct GirInst {
    uint8_t  op;     /* GirOp */
    uint8_t  sub;    /* predicate, GirOvf, GirRmw, GirX86 */
    uint16_t flags;  /* GIR_IF_* */
    uint16_t ty;     /* result type id */
    uint16_t aux;    /* secondary type id (cast source, compare operand,
                        stored value, shuffle operands, ...) */
    uint32_t a, b, c;
    uint32_t dbg;    /* index into dlocs; 0 = no source location */
} GirInst;

typedef struct GirBlock {
    uint32_t first_inst;   /* module-global index into insts */
    uint32_t n_inst;
} GirBlock;

#define GIR_FN_VARARG   2u     /* variadic definition */
#define GIR_FN_INTERNAL 4u     /* local linkage */
#define GIR_FN_VASTART  8u     /* contains VASTART: needs a register save area */
#define GIR_FN_SJLJ     16u    /* contains SJLJ_SETJMP: preserve all callee-saved registers */
#define GIR_FN_RETURNS_TWICE 32u /* calls a returns_twice function (setjmp, vfork, ...): */
                               /*   a frame slot must not be shared between values */
/* additive (milestone E1), hints for the optimizer (opt_level >= 1); an -O0
 * back-end ignores them */
#define GIR_FN_NOINLINE 64u    /* do not inline calls of this function (LLVM noinline; E2:
                                  also when it comes with optnone, which E1 did not export) */
#define GIR_FN_ALWAYSINLINE 128u /* always_inline */
/* additive (milestone E2): LLVM's function attributes as the optimizer honors
 * them (backend-goose/DESIGN.md §15); an -O0 back-end ignores them */
#define GIR_FN_OPTNONE   256u  /* optnone: the function is not optimized (-O0 code generation
                                  for it, whatever the module's opt_level); implies noinline */
#define GIR_FN_OPTSIZE   512u  /* optsize (clang -Os, -Oz, and __attribute__((cold))) */
#define GIR_FN_MINSIZE  1024u  /* minsize (clang -Oz, __attribute__((minsize))) */
#define GIR_FN_COLD     2048u  /* cold: calls of it are unlikely; .text.unlikely. at -O1+ */
#define GIR_FN_HOT      4096u  /* hot: .text.hot. at -O1+ */
#define GIR_FN_INLINEHINT 8192u /* inlinehint (an `inline` function) */
#define GIR_FN_AVAILEXT 16384u /* the body of an available_externally function (exported at
                                  opt_level >= 1 only): for inlining, never emitted; its global
                                  is not GIR_GF_DEFINED (calls that remain call the external
                                  symbol), but Global.func names this record */
#define GIR_FN_MUSTPROGRESS 32768u /* mustprogress (C++): a loop without side effects ends */
/* bits 16..23 are reserved for back-ends (backend-goose: FN_DEAD = bit 23 in the
 * optimizer's output tables) */
#define GIR_FN_ALIGN_SHIFT 24  /* bits 24..31: log2 of the function alignment (>= 4) */

/* 40 bytes. Functions are also globals (Func.global is their entry in the
 * globals table) so that calls and address-taking use one namespace. */
typedef struct GirFunc {
    uint32_t global;       /* index into globals */
    uint32_t flags;        /* GIR_FN_* */
    uint32_t first_block, n_blocks;
    uint32_t first_inst, n_inst;
    uint32_t n_args;
    uint32_t args;         /* opnds[args + 2*i] = type id of argument i, */
                           /* opnds[args + 2*i + 1] = its ABI word        */
    uint32_t ret_ty;       /* type id */
    uint32_t dbg;          /* DISubprogram: index into dscopes, 0 = none */
} GirFunc;

/* 24 bytes. Constants of every type. `lo` holds bits 0..63 of the value
 * zero-extended from the type's width (i1 true = 1, i8 -1 = 255, f32 and
 * f64 their IEEE bit pattern, f80 its 64-bit significand); `hi` holds bits
 * 64..127 (INT2 integers, the 16 sign/exponent bits of an f80), else 0.
 * Null is value 0 with ty ptr; undef and poison are 0. A constant of class
 * VEC or MEM has data = offset of its `types[ty].size` bytes in `data`, or
 * GIR_NONE if it is all zero. (A vector or aggregate constant that contains
 * an address is not a GirConst: the exporter makes it a private global and
 * LOADs it.) */
typedef struct GirConst {
    uint64_t lo;
    uint64_t hi;
    uint32_t ty;           /* type id */
    uint32_t data;
} GirConst;

#define GIR_G_FUNC     0u
#define GIR_G_VAR      1u
#define GIR_G_ALIAS    2u   /* another name for (globals[func] + aux) */

#define GIR_GF_DEFINED   1u   /* has a body / initializer in this module */
#define GIR_GF_INTERNAL  2u   /* local linkage */
#define GIR_GF_CONST     4u   /* read-only data */
#define GIR_GF_ZERO      8u   /* zero-initialized: no bytes in data (bss) */
#define GIR_GF_WEAK     16u   /* weak binding (weak, linkonce, extern_weak) */
#define GIR_GF_TLS      32u   /* thread-local */
#define GIR_GF_COMMON   64u   /* common symbol (size, align): SHN_COMMON */
#define GIR_GF_HIDDEN  128u   /* STV_HIDDEN */
#define GIR_GF_PROTECTED 256u /* STV_PROTECTED */
#define GIR_GF_LOCALREF 512u  /* references may bind directly (dso_local): no GOT */
#define GIR_GF_RELOCS 1024u   /* the initializer has data relocations */

/* 40 bytes. A named global: a function, a variable or an alias.
 * Names: strtab[name .. name+name_len) is the symbol name; it is followed
 * by a NUL byte and strtab[0] is NUL, so strtab is directly usable as an
 * ELF string table with st_name = name. */
typedef struct GirGlobal {
    uint32_t name, name_len;     /* into strtab */
    uint32_t kind;               /* GIR_G_* */
    uint32_t flags;              /* GIR_GF_* */
    uint32_t data, size;         /* variables: initializer bytes in data[] */
                                 /*   (size is also set for ZERO/COMMON)   */
    uint32_t align;              /* power of two >= 1 */
    uint32_t func;               /* functions: index into funcs (GIR_NONE if */
                                 /*   undefined; E2: an undefined function may */
                                 /*   have a GIR_FN_AVAILEXT body); aliases: the */
                                 /*   aliased global; */
                                 /*   variables: GIR_NONE                  */
    uint32_t section;            /* GIR_NONE = the default section for its */
                                 /*   kind; else index into sections       */
    uint32_t aux;                /* aliases: byte offset (i32) from the target */
} GirGlobal;

/* 16 bytes. An explicitly named output section (section attribute,
 * .init_array/.fini_array for llvm.global_ctors/dtors). */
#define GIR_SF_WRITE   1u
#define GIR_SF_EXEC    2u
#define GIR_SF_TLS     4u
#define GIR_SF_NOBITS  8u   /* zero-initialized: no file bytes (.bss.*) */
typedef struct GirSection {
    uint32_t name, name_len;     /* into strtab (NUL-terminated as well) */
    uint32_t flags;              /* GIR_SF_* */
    uint32_t type;               /* ELF sh_type: 1 PROGBITS, 8 NOBITS, 14 INIT_ARRAY,
                                    15 FINI_ARRAY, 16 PREINIT_ARRAY */
} GirSection;

/* 24 bytes. A relocation inside a variable's initializer, at byte
 * data[Global.data + offset]. The initializer bytes under it are zero.
 * Relocations of one variable are contiguous, in offset order.
 *   ABS64   8 bytes: address of globals[target] + addend
 *   BLOCK   8 bytes: address of local block `block` of the function
 *           globals[target] + addend (blockaddress)
 *   BLOCKDIFF32  4 bytes: (block `block` - block `block2`) of function
 *           globals[target] + addend, a link-time constant the back-end
 *           computes itself (&&l1 - &&l2 in an initializer)
 *   PCREL32 4 bytes: address of globals[target] + addend - address of the
 *           field (additive, E1: the relative lookup tables of LLVM -O2 IR,
 *           whose entries are X - table: addend = X's offset + the field's
 *           offset in the table) */
#define GIR_DR_ABS64      0u
#define GIR_DR_BLOCK      1u
#define GIR_DR_BLOCKDIFF32 2u
#define GIR_DR_PCREL32    3u
typedef struct GirDataReloc {
    uint32_t owner;              /* index into globals (the variable) */
    uint32_t offset;             /* byte offset inside that variable */
    uint32_t target;             /* index into globals */
    uint32_t kind;               /* GIR_DR_* */
    int64_t  addend;
    uint32_t block;              /* BLOCK, BLOCKDIFF32: local block number */
    uint32_t block2;             /* BLOCKDIFF32: the subtracted block */
} GirDataReloc;

/* ---------------------------------------------------------- inline asm
 * A GIR_ASM instruction is machine code assembled by the exporter (LLVM's
 * MC layer) from the template with every operand bound to a register: the
 * exporter allocates registers for "r"/"x"/"m" operands and substitutes
 * them into the template, so the back-end only moves values in and out.
 *   opnds[ops + 2k], opnds[ops + 2k + 1]  (k < n_in): input value, register
 *     (an "m" operand's input is its address, loaded into the register the
 *     template uses as the base)
 *   opnds[ops + 2 n_in + 2k], [... + 1]   (k < n_out): register, byte offset
 *     of the output in the result (0 for a single output)
 * Registers: 0..15 rax..r15 (x86 numbering), 16..31 xmm0..15, 32..39
 * st(0)..st(7). x87 inputs are pushed deepest first; after the code the x87
 * stack holds the st outputs (st(0) first) followed by x87_pop values that
 * the back-end pops. An empty template needs no GIR_ASM (see the exporter).
 * AArch64 (target GIR_TARGET_AARCH64): 0..30 x0..x30, 32..63 v0..v31 (an
 * input or output of a v register is its low 1/2/4/8/16 bytes, by the
 * value's size); x87_pop is 0.
 */
typedef struct GirAsm {          /* 24 bytes */
    uint32_t code, code_len;     /* machine code in data[] */
    uint32_t n_in, n_out;
    uint32_t ops;                /* opnds index */
    uint32_t x87_pop;
} GirAsm;
#define GIR_ASMREG_XMM0 16u
#define GIR_ASMREG_ST0  32u
#define GIR_ASMREG_V0   32u      /* AArch64 */

/* ------------------------------------------------------------ debug info
 * Locations and scopes: the back-end's .debug_line and lexical-block
 * ranges come from these, the DIE tree from `dies` (below). Entry 0
 * of dlocs, dscopes and dfiles means "none". dstr is a string table of
 * NUL-terminated strings with dstr[0] = NUL. */
typedef struct GirDLoc {         /* 16 bytes: a DILocation */
    uint32_t line;
    uint32_t col;
    uint32_t scope;              /* index into dscopes */
    uint32_t inlined_at;         /* index into dlocs, 0 = not inlined */
} GirDLoc;

#define GIR_DS_CU          1u    /* compile unit: name = producer, line = DWARF language */
#define GIR_DS_SUBPROGRAM  2u    /* name, linkage = linkage name, line = scope line */
#define GIR_DS_LEXICAL     3u    /* lexical block: line, col */
#define GIR_DS_FILE        4u    /* lexical block file: file only */
typedef struct GirDScope {       /* 24 bytes */
    uint32_t kind;               /* GIR_DS_* */
    uint32_t parent;             /* enclosing scope, 0 = none */
    uint32_t file;               /* index into dfiles */
    uint32_t line;
    uint32_t name;               /* offset in dstr */
    uint32_t extra;              /* SUBPROGRAM: linkage name offset; LEXICAL: column */
} GirDScope;

typedef struct GirDFile {        /* 8 bytes */
    uint32_t name;               /* offset in dstr */
    uint32_t dir;                /* offset in dstr */
} GirDFile;

/* ------------------------------------------------------ exception handling
 * (additive to version 2: an empty table means no EH.) One GirEh per
 * function that has landing pads; calls of that function's body that are
 * not INVOKEs may throw through it (they unwind without a handler). The
 * personality routine and the typeinfos are reached indirectly, as LLVM does
 * for PIC: through pointer variables the exporter creates (DW.ref.<name>,
 * hidden, in its own comdat; one private stub per typeinfo), so the
 * read-only unwind tables need no dynamic relocations. */
typedef struct GirEh {           /* 24 bytes */
    uint32_t func;               /* index into funcs */
    uint32_t personality;        /* globals index of a pointer variable holding the
                                    personality routine's address */
    uint32_t ttypes, n_ttypes;   /* opnds run: entry k-1 is type index k, a globals
                                    index of a pointer variable holding the typeinfo
                                    address, or GIR_NONE (catch-all, a null entry) */
    uint32_t specs, n_specs;     /* exception specifications: data[specs ..
                                    specs + n_specs), lists of uleb128 type indices,
                                    each ending in 0 */
} GirEh;

/* ------------------------------------------------------------ comdat groups
 * (additive; empty tables: no comdats.) gcomdat is empty or has one entry
 * per global: its comdat (index into comdats) or GIR_NONE. A defined
 * function or variable in a comdat gets a section of its own in that ELF
 * section group (with its relocation and unwind-table sections). */
#define GIR_CD_ANY     0u        /* comdat any: a COMDAT group */
#define GIR_CD_NODEDUP 1u        /* nodeduplicate: a plain (non-COMDAT) group */
typedef struct GirComdat {       /* 16 bytes */
    uint32_t name, name_len;     /* group signature, into strtab */
    uint32_t sig;                /* globals index of the symbol of that name, or
                                    GIR_NONE (the back-end makes a local symbol) */
    uint32_t kind;               /* GIR_CD_* */
} GirComdat;

/* ------------------------------------------------------- debug information
 * entries (additive; empty: the back-end makes a compile unit and one
 * subprogram per function with a DISubprogram from dscopes). The exporter
 * builds the DWARF tree of the compile unit as LLVM's DwarfUnit would; the
 * back-end assigns abbreviations, offsets, string and address indices and
 * fills in what only it knows (code addresses, frame offsets). DIEs are in
 * pre-order: a DIE's children follow it, each child after the subtree of
 * the previous one; die 0 is the DW_TAG_compile_unit (parent GIR_NONE). */
typedef struct GirDie {          /* 16 bytes */
    uint16_t tag;                /* DW_TAG_* */
    uint16_t flags;              /* 0 (reserved) */
    uint32_t parent;             /* index into dies, GIR_NONE for die 0 */
    uint32_t attrs, n_attrs;     /* dattrs run, in output order */
} GirDie;

/* A DIE attribute. `form` is a DWARF form, used as given:
 *   DW_FORM_data1/2/4/8, sdata, udata, flag, flag_present: val
 *   DW_FORM_ref4: val = index into dies (the back-end makes it an offset)
 *   DW_FORM_exprloc, block1: the bytes dstr[val .. val + aux)
 *   DW_FORM_implicit_const: val (a signed value, kept in the abbreviation)
 * or one of the GIR forms, which the back-end resolves: */
#define GIR_DF_STR        0x7F01u /* string at dstr[val] -> DW_FORM_strx1..4 */
#define GIR_DF_FILE       0x7F02u /* dfiles index val -> line-table file number (data1/2) */
#define GIR_DF_PC         0x7F03u /* DW_AT_low_pc + DW_AT_high_pc of function val (funcs index) */
#define GIR_DF_SCOPE_PC   0x7F04u /* the code ranges of scope val (dscopes index: a lexical
                                     block, or an inlined subprogram) in the code inlined at
                                     location aux (dlocs index; 0: the function's own code):
                                     low_pc + high_pc, or DW_AT_ranges; without code the DIE
                                     and its subtree are dropped */
#define GIR_DF_FRAME_BASE 0x7F05u /* DW_AT_frame_base: the frame register */
#define GIR_DF_LOCAL      0x7F06u /* DW_AT_location of a variable whose address is the value
                                     (val & 0xFFFFFFFF) of function (val >> 32): an alloca, a
                                     byval argument, or any pointer value (kept in a frame
                                     slot); aux = 0 or the dstr offset of a count byte and that
                                     many DWARF expression bytes to append */
#define GIR_DF_GLOBAL     0x7F07u /* DW_AT_location: the address of global val (DW_OP_addrx,
                                     or the TLS offset for a thread-local); aux as for LOCAL */
#define GIR_DF_STMT_LIST  0x7F08u /* DW_AT_stmt_list: the line table */
#define GIR_DF_STR_BASE   0x7F09u /* DW_AT_str_offsets_base */
#define GIR_DF_CU_PC      0x7F0Au /* the unit's code: low_pc + high_pc, or low_pc 0 + ranges */
#define GIR_DF_ADDR_BASE  0x7F0Bu /* DW_AT_addr_base (and DW_AT_rnglists_base if needed) */
#define GIR_DF_LABEL      0x7F0Cu /* DW_AT_low_pc: the code of instruction val (insts index) */
typedef struct GirDAttr {        /* 16 bytes */
    uint16_t at;                 /* DW_AT_* */
    uint16_t form;               /* DW_FORM_* or GIR_DF_* */
    uint32_t aux;
    uint64_t val;
} GirDAttr;

/* ---------------------------------------------------------- module header
 * 32 bytes, one record (passed to Goose as a one-element slice). */
#define GIR_MF_PIE   1u          /* linked into an executable (PIE level set):
                                    initial-exec/local-exec TLS are valid */
typedef struct GirHeader {
    uint32_t version;            /* GIR_VERSION */
    uint32_t flags;              /* GIR_MF_* */
    uint32_t tls_get_addr;       /* globals index of __tls_get_addr, or GIR_NONE */
    uint32_t n_llvm_insts;       /* statistics */
    uint32_t opt_level;          /* additive (milestone E1; was reserved, so 0 from older
                                    producers): 0 = -O0 code generation; >= 1 = the
                                    back-end runs its middle-end on the tables and
                                    allocates registers globally (backend-goose/DESIGN.md
                                    §15, §16). E2: bits 0..7 are the level (1, 2, 3 for
                                    -O1, -O2, -O3; -Os and -Oz are 2), bits 8..9 the size
                                    level (GIR_OPT_SIZE: 1 = -Os, 2 = -Oz) */
    uint32_t target;             /* additive (milestone F1; was reserved, so 0 from older
                                    producers): GIR_TARGET_* */
    uint32_t tbaa;               /* additive (milestone E2, opt_level >= 1; 0 = none): the
                                    TBAA type tree of the TBAA nodes that LOAD.b and STORE.c
                                    name: opnds[tbaa] = n, opnds[tbaa + k] = the parent of
                                    node k (1..n; 0 = a root). Two accesses whose nodes have
                                    a common root and neither of which is an ancestor of the
                                    other do not alias (LLVM's scalar TBAA) */
    uint32_t reserved[1];
} GirHeader;
#define GIR_OPT_LEVEL(x)   ((x) & 0xFFu)          /* GirHeader.opt_level (E2) */
#define GIR_OPT_SIZE(x)    (((x) >> 8) & 3u)
#define GIR_TARGET_X86_64  0u    /* x86-64 Linux, SysV ABI */
#define GIR_TARGET_AARCH64 1u    /* AArch64 Linux (aarch64-linux-gnu), AAPCS64, LP64 */

/* The whole module, as the host holds it (host-side only: this struct is
 * not shared with Goose, so its padding does not matter). */
typedef struct GirModule {
    const GirHeader    *header;
    const GirTypeDef   *types;   uint32_t n_types;
    const GirFunc      *funcs;   uint32_t n_funcs;
    const GirBlock     *blocks;  uint32_t n_blocks;
    const GirInst      *insts;   uint32_t n_insts;
    const uint32_t     *opnds;   uint32_t n_opnds;
    const GirConst     *consts;  uint32_t n_consts;
    const GirGlobal    *globals; uint32_t n_globals;
    const GirSection   *sections; uint32_t n_sections;
    const uint8_t      *data;    uint32_t n_data;
    const GirDataReloc *drelocs; uint32_t n_drelocs;
    const uint8_t      *strtab;  uint32_t n_strtab;
    const GirDLoc      *dlocs;   uint32_t n_dlocs;
    const GirDScope    *dscopes; uint32_t n_dscopes;
    const GirDFile     *dfiles;  uint32_t n_dfiles;
    const GirAsm       *asms;    uint32_t n_asms;
    const uint8_t      *dstr;    uint32_t n_dstr;
    /* additive tables (empty in a module without them) */
    const GirEh        *ehs;     uint32_t n_ehs;
    const GirComdat    *comdats; uint32_t n_comdats;
    const uint32_t     *gcomdat; uint32_t n_gcomdat;   /* 0 or n_globals entries */
    const GirDie       *dies;    uint32_t n_dies;
    const GirDAttr     *dattrs;  uint32_t n_dattrs;
} GirModule;

/* Record sizes are part of the format. */
#ifdef __cplusplus
#define GIR_STATIC_ASSERT(c, m) static_assert(c, m)
#else
#define GIR_STATIC_ASSERT(c, m) _Static_assert(c, m)
#endif
GIR_STATIC_ASSERT(sizeof(GirTypeDef) == 24, "GirTypeDef must be 24 bytes");
GIR_STATIC_ASSERT(sizeof(GirInst) == 24, "GirInst must be 24 bytes");
GIR_STATIC_ASSERT(sizeof(GirBlock) == 8, "GirBlock must be 8 bytes");
GIR_STATIC_ASSERT(sizeof(GirFunc) == 40, "GirFunc must be 40 bytes");
GIR_STATIC_ASSERT(sizeof(GirConst) == 24, "GirConst must be 24 bytes");
GIR_STATIC_ASSERT(sizeof(GirGlobal) == 40, "GirGlobal must be 40 bytes");
GIR_STATIC_ASSERT(sizeof(GirSection) == 16, "GirSection must be 16 bytes");
GIR_STATIC_ASSERT(sizeof(GirDataReloc) == 32, "GirDataReloc must be 32 bytes");
GIR_STATIC_ASSERT(sizeof(GirDLoc) == 16, "GirDLoc must be 16 bytes");
GIR_STATIC_ASSERT(sizeof(GirDScope) == 24, "GirDScope must be 24 bytes");
GIR_STATIC_ASSERT(sizeof(GirDFile) == 8, "GirDFile must be 8 bytes");
GIR_STATIC_ASSERT(sizeof(GirHeader) == 32, "GirHeader must be 32 bytes");
GIR_STATIC_ASSERT(sizeof(GirAsm) == 24, "GirAsm must be 24 bytes");
GIR_STATIC_ASSERT(sizeof(GirEh) == 24, "GirEh must be 24 bytes");
GIR_STATIC_ASSERT(sizeof(GirComdat) == 16, "GirComdat must be 16 bytes");
GIR_STATIC_ASSERT(sizeof(GirDie) == 16, "GirDie must be 16 bytes");
GIR_STATIC_ASSERT(sizeof(GirDAttr) == 16, "GirDAttr must be 16 bytes");

#endif /* GIR_H */
