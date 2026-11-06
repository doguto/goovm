/* GIR: goovm's flat IR, version 0, revision 1.
 *
 * GIR is the hand-off format between LLVM and a fast back-end. A C++
 * exporter walks an llvm::Module once and fills these tables; a back-end
 * (written in C++ or in Goose) reads them and produces an ELF object.
 *
 * Every record is a fixed-size struct whose fields are naturally aligned
 * with no padding, so the same bytes are valid as a C struct and as the
 * packed C type that Goose generates for the matching Goose struct. The
 * host passes each table to Goose as a slice ({ data, len }) without
 * copying.
 *
 * Indices are u32 and global to the module unless stated otherwise.
 * gir/README.md describes the format in prose and lists the changes made
 * in revision 1; this header is the normative definition.
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
 *   INST -> insts[i].ty, ARG -> opnds[func.arg_tys + i],
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
 *    UNREACHABLE); no terminator appears elsewhere.
 *  - PHIs appear only at the start of a block, before any other
 *    instruction. A PHI has exactly one (value, pred) pair per incoming
 *    CFG edge; a predecessor reached by several edges (switch) appears
 *    several times with the same value.
 *  - ALLOCAs appear only in the entry block; they are static (constant
 *    size) with alignment <= 16.
 *  - Instructions without a result have ty = GIR_T_VOID (RET, BR, CONDBR,
 *    SWITCH, UNREACHABLE, STORE, CALL of a void function). An instruction
 *    operand never refers to such an instruction.
 *  - An INST operand refers to an instruction that dominates the use (for a
 *    PHI operand: that dominates the end of the predecessor block). It may
 *    lie later in layout order than the use.
 *  - Call ABI details are already lowered by the exporter: arguments with
 *    the LLVM `signext` attribute arrive as an explicit SEXT to i32; a
 *    function whose return has `signext` returns an explicit SEXT to i32
 *    (so RET's operand may be wider than Func.ret_ty); a function with an
 *    `sret` parameter returns that parameter (Func.ret_ty = GIR_T_PTR).
 *    A back-end only has to follow the plain SysV integer convention.
 */
#ifndef GIR_H
#define GIR_H
#include <stdint.h>

#define GIR_V_INST   0u
#define GIR_V_ARG    1u
#define GIR_V_CONST  2u
#define GIR_V_GLOBAL 3u
#define GIR_KIND(v)  ((uint32_t)(v) >> 30)
#define GIR_IDX(v)   ((uint32_t)(v) & 0x3FFFFFFFu)
#define GIR_MK(k, i) (((uint32_t)(k) << 30) | (uint32_t)(i))
#define GIR_NONE     0xFFFFFFFFu

/* Value types. Integers narrower than 64 bits are kept zero-extended in a
 * 64-bit slot by convention of the reference back-ends; that is a back-end
 * choice, not part of the format. */
enum GirType {
    GIR_T_VOID = 0, GIR_T_I1 = 1, GIR_T_I8 = 2, GIR_T_I16 = 3,
    GIR_T_I32 = 4,  GIR_T_I64 = 5, GIR_T_PTR = 6,
    GIR_T_F32 = 7,  GIR_T_F64 = 8   /* reserved: not produced by v0 */
};

/* Opcodes. Operand fields a/b/c of GirInst; "ops[s..s+n)" means the run
 * opnds[s .. s+n) of the opnds table. Unused fields are 0. */
enum GirOp {
    GIR_RET = 0,       /* a = value or GIR_NONE                               */
    GIR_BR,            /* a = target block                                   */
    GIR_CONDBR,        /* a = i1 cond, b = true block, c = false block        */
    GIR_SWITCH,        /* a = cond, b = s, c = n: ops[s] = default block,     */
                       /*   then n pairs (const value ref, block); the case  */
                       /*   constants have the type of cond and are distinct */
    GIR_UNREACHABLE,
    /* binary integer ops: a, b; ty = operand and result type (never ptr).
     * Shift amounts >= the bit width and division by zero are undefined. */
    GIR_ADD, GIR_SUB, GIR_MUL, GIR_SDIV, GIR_UDIV, GIR_SREM, GIR_UREM,
    GIR_AND, GIR_OR, GIR_XOR, GIR_SHL, GIR_LSHR, GIR_ASHR,
    GIR_ICMP,          /* a, b; sub = GirPred; aux = operand type; ty = i1   */
    GIR_SELECT,        /* a = i1 cond, b = true value, c = false value       */
    /* casts: a = source; ty = destination type; aux = source type */
    GIR_ZEXT, GIR_SEXT, GIR_TRUNC, GIR_PTRTOINT, GIR_INTTOPTR, GIR_BITCAST,
    GIR_ALLOCA,        /* a = size in bytes, b = alignment (immediates);      */
                       /*   static allocas only; ty = ptr                    */
    GIR_LOAD,          /* a = pointer; ty = loaded type                      */
    GIR_STORE,         /* a = value, b = pointer; aux = stored type          */
    GIR_GEP,           /* a = base pointer, b = s, c = n: ops[s], ops[s+1] = */
                       /*   constant byte offset (lo, hi of an i64), then n  */
                       /*   pairs (index value ref, scale in bytes); result  */
                       /*   = a + offset + sum(sext64(index) * scale). The   */
                       /*   index type is the type of the index value; all   */
                       /*   arithmetic wraps modulo 2^64                     */
    GIR_CALL,          /* a = callee value ref, b = s, c = n: ops[s..s+n) =  */
                       /*   argument refs; ty = return type;                 */
                       /*   sub = GIR_F_VARARG for a variadic callee         */
    GIR_PHI,           /* b = s, c = n: n pairs (value ref, pred block)      */
    GIR_OP_COUNT
};

enum GirPred {
    GIR_EQ = 0, GIR_NE, GIR_UGT, GIR_UGE, GIR_ULT, GIR_ULE,
    GIR_SGT, GIR_SGE, GIR_SLT, GIR_SLE
};

#define GIR_F_VARARG 1u

/* One instruction: 16 bytes. Instructions of a block are contiguous, and
 * blocks of a function are contiguous, in layout order. */
typedef struct GirInst {
    uint8_t  op;     /* GirOp */
    uint8_t  ty;     /* result type (GirType) */
    uint8_t  sub;    /* predicate for ICMP, GIR_F_* for CALL */
    uint8_t  aux;    /* secondary type (source of a cast, operand of ICMP/STORE) */
    uint32_t a, b, c;
} GirInst;

typedef struct GirBlock {
    uint32_t first_inst;   /* module-global index into insts */
    uint32_t n_inst;
} GirBlock;

#define GIR_FN_DECL     1u   /* declaration only: no body */
#define GIR_FN_VARARG   2u
#define GIR_FN_INTERNAL 4u   /* local linkage */

/* 36 bytes. Functions are also globals (Func.global is their entry in the
 * globals table) so that calls and address-taking use one namespace. */
typedef struct GirFunc {
    uint32_t global;       /* index into globals */
    uint32_t flags;        /* GIR_FN_* */
    uint32_t first_block, n_blocks;
    uint32_t first_inst, n_inst;
    uint32_t n_args;
    uint32_t arg_tys;      /* opnds[arg_tys .. arg_tys+n_args) = GirType of each argument */
    uint32_t ret_ty;       /* GirType */
} GirFunc;

/* 16 bytes. Integer and pointer constants; null is value 0 with ty ptr.
 * `value` is the constant's bit pattern zero-extended from the width of
 * `ty` to 64 bits (i1 true = 1, i8 -1 = 255, i32 -1 = 0xFFFFFFFF). */
typedef struct GirConst {
    int64_t  value;
    uint32_t ty;           /* GirType */
    uint32_t pad;          /* 0 */
} GirConst;

#define GIR_G_FUNC     0u
#define GIR_G_VAR      1u
#define GIR_GF_DEFINED  1u   /* has a body / initializer in this module */
#define GIR_GF_INTERNAL 2u   /* local linkage */
#define GIR_GF_CONST    4u   /* read-only data */
#define GIR_GF_ZERO     8u   /* zero-initialized: no bytes in data (bss) */
#define GIR_GF_WEAK    16u   /* weak binding (weak, linkonce, common, extern_weak) */

/* 32 bytes. A named global: a function or a variable.
 * Names: strtab[name .. name+name_len) is the symbol name; it is followed
 * by a NUL byte and strtab[0] is NUL, so strtab is directly usable as an
 * ELF string table with st_name = name. */
typedef struct GirGlobal {
    uint32_t name, name_len;     /* into strtab */
    uint32_t kind;               /* GIR_G_* */
    uint32_t flags;              /* GIR_GF_* */
    uint32_t data, size;         /* variables: initializer bytes in data[] */
                                 /*   (size is also set for ZERO variables) */
    uint32_t align;              /* power of two >= 1 */
    uint32_t func;               /* functions: index into funcs (GIR_NONE if */
                                 /*   undefined); variables: GIR_NONE        */
} GirGlobal;

/* 16 bytes. A pointer-sized relocation inside a variable's initializer:
 * at data[Global.data + offset] store the address of globals[target] plus
 * addend. Relocations of one variable are contiguous; Global has no direct
 * link to them, the back-end groups them by `owner`. The 8 initializer
 * bytes under a relocation are zero. */
typedef struct GirDataReloc {
    uint32_t owner;              /* index into globals (the variable) */
    uint32_t offset;             /* byte offset inside that variable */
    uint32_t target;             /* index into globals */
    int32_t  addend;
} GirDataReloc;

/* The whole module, as the host holds it (host-side only: this struct is
 * not shared with Goose, so its padding does not matter). */
typedef struct GirModule {
    const GirFunc      *funcs;   uint32_t n_funcs;
    const GirBlock     *blocks;  uint32_t n_blocks;
    const GirInst      *insts;   uint32_t n_insts;
    const uint32_t     *opnds;   uint32_t n_opnds;
    const GirConst     *consts;  uint32_t n_consts;
    const GirGlobal    *globals; uint32_t n_globals;
    const uint8_t      *data;    uint32_t n_data;
    const GirDataReloc *drelocs; uint32_t n_drelocs;
    const uint8_t      *strtab;  uint32_t n_strtab;
} GirModule;

/* Record sizes are part of the format. */
#ifdef __cplusplus
#define GIR_STATIC_ASSERT(c, m) static_assert(c, m)
#else
#define GIR_STATIC_ASSERT(c, m) _Static_assert(c, m)
#endif
GIR_STATIC_ASSERT(sizeof(GirInst) == 16, "GirInst must be 16 bytes");
GIR_STATIC_ASSERT(sizeof(GirBlock) == 8, "GirBlock must be 8 bytes");
GIR_STATIC_ASSERT(sizeof(GirFunc) == 36, "GirFunc must be 36 bytes");
GIR_STATIC_ASSERT(sizeof(GirConst) == 16, "GirConst must be 16 bytes");
GIR_STATIC_ASSERT(sizeof(GirGlobal) == 32, "GirGlobal must be 32 bytes");
GIR_STATIC_ASSERT(sizeof(GirDataReloc) == 16, "GirDataReloc must be 16 bytes");

#endif /* GIR_H */
