// LLVM module -> GIR tables.
//
// One walk over the module. Globals first (so every function and variable
// has a GIR global index), then initializers, then function bodies. Each
// LLVM instruction becomes zero or more GIR instructions in the same block:
// constant-expression operands are materialized right before their user,
// those used by PHIs at the start of the entry block (which dominates every
// predecessor). Uses of instructions that are not exported yet (PHIs, or
// blocks laid out before their dominator) get a placeholder that is patched
// when the function is complete.

#include "gir_export.h"

#include <cstdlib>
#include <cstring>
#include <string>

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

GirModule GirTables::view() const {
    GirModule m;
    m.funcs = funcs.data();     m.n_funcs = (uint32_t)funcs.size();
    m.blocks = blocks.data();   m.n_blocks = (uint32_t)blocks.size();
    m.insts = insts.data();     m.n_insts = (uint32_t)insts.size();
    m.opnds = opnds.data();     m.n_opnds = (uint32_t)opnds.size();
    m.consts = consts.data();   m.n_consts = (uint32_t)consts.size();
    m.globals = globals.data(); m.n_globals = (uint32_t)globals.size();
    m.data = data.data();       m.n_data = (uint32_t)data.size();
    m.drelocs = drelocs.data(); m.n_drelocs = (uint32_t)drelocs.size();
    m.strtab = strtab.data();   m.n_strtab = (uint32_t)strtab.size();
    return m;
}

namespace {

// Placeholder refs for not-yet-exported instructions: kind INST, index in
// [PH_BASE, 2^30). Real instruction indices must stay below PH_BASE.
constexpr uint32_t PH_BASE = 0x3F000000u;

bool is_placeholder(uint32_t r) {
    return GIR_KIND(r) == GIR_V_INST && GIR_IDX(r) >= PH_BASE;
}

struct Fix {
    const Value *v;
    uint32_t where;  // index into insts (field 0..2) or opnds (field 3)
    uint32_t field;  // 0 = a, 1 = b, 2 = c, 3 = opnds[where]
};

enum : unsigned { RA = 1, RB = 2, RC = 4 };  // which of a/b/c hold value refs

struct Exporter {
    const Module &M;
    const DataLayout &DL;
    GirTables &T;

    DenseMap<const GlobalValue *, uint32_t> gmap;  // global -> GIR global index
    uint32_t n_unnamed = 0;
    uint32_t libc_memcpy = GIR_NONE, libc_memmove = GIR_NONE, libc_memset = GIR_NONE;

    // Per function.
    const Function *F = nullptr;
    const Instruction *curI = nullptr;
    DenseMap<const Value *, uint32_t> vmap;     // instruction -> ref
    DenseMap<const Constant *, uint32_t> phice; // CE used by a PHI -> ref
    std::vector<uint32_t> bmap;                 // BB number -> local block
    std::vector<Fix> fixes;
    bool in_phi_prepass = false;

    Exporter(const Module &m, GirTables &t) : M(m), DL(m.getDataLayout()), T(t) {}

    // ---------------------------------------------------------------- errors
    [[noreturn]] void fail(const std::string &why) {
        std::string s;
        raw_string_ostream os(s);
        os << "goovm-llc: unsupported: " << why;
        if (F) os << " in function '" << F->getName() << "'";
        if (curI) {
            os << " at instruction:\n  ";
            curI->print(os);
        }
        os << "\n";
        os.flush();
        std::fputs(s.c_str(), stderr);
        std::exit(2);
    }
    [[noreturn]] void fail_global(const GlobalValue &G, const std::string &why) {
        std::fprintf(stderr, "goovm-llc: unsupported: %s in global '%s'\n", why.c_str(),
                     G.getName().str().c_str());
        std::exit(2);
    }
    static std::string tystr(const Type *t) {
        std::string s;
        raw_string_ostream os(s);
        t->print(os);
        return os.str();
    }

    // ----------------------------------------------------------------- types
    // Scalar value type; fails on anything outside the v0 subset.
    uint8_t ty(const Type *t) {
        if (const auto *it = dyn_cast<IntegerType>(t)) {
            switch (it->getBitWidth()) {
            case 1: return GIR_T_I1;
            case 8: return GIR_T_I8;
            case 16: return GIR_T_I16;
            case 32: return GIR_T_I32;
            case 64: return GIR_T_I64;
            default: break;
            }
            fail("integer type " + tystr(t));
        }
        if (const auto *pt = dyn_cast<PointerType>(t)) {
            if (pt->getAddressSpace() != 0) fail("pointer in address space " + std::to_string(pt->getAddressSpace()));
            return GIR_T_PTR;
        }
        if (t->isVoidTy()) fail("void value");
        if (t->isFloatingPointTy()) fail("floating-point type " + tystr(t));
        if (t->isVectorTy()) fail("vector type " + tystr(t));
        if (t->isStructTy() || t->isArrayTy()) fail("aggregate (by-value) type " + tystr(t));
        fail("type " + tystr(t));
    }
    uint8_t ret_ty(const Type *t) { return t->isVoidTy() ? (uint8_t)GIR_T_VOID : ty(t); }
    static unsigned bits(uint8_t t) {
        switch (t) {
        case GIR_T_I1: return 1;
        case GIR_T_I8: return 8;
        case GIR_T_I16: return 16;
        case GIR_T_I32: return 32;
        default: return 64;
        }
    }

    // ------------------------------------------------------------ strtab etc.
    uint32_t add_name(StringRef name) {
        if (name.contains('\0')) {
            std::fprintf(stderr, "goovm-llc: unsupported: symbol name with a NUL byte\n");
            std::exit(2);
        }
        uint32_t off = (uint32_t)T.strtab.size();
        T.strtab.insert(T.strtab.end(), name.begin(), name.end());
        T.strtab.push_back(0);
        return off;
    }
    uint32_t add_global(StringRef name, uint32_t kind, uint32_t flags, uint32_t align) {
        GirGlobal g{};
        g.name = add_name(name);
        g.name_len = (uint32_t)name.size();
        g.kind = kind;
        g.flags = flags;
        g.align = align;
        g.func = GIR_NONE;
        T.globals.push_back(g);
        return (uint32_t)T.globals.size() - 1;
    }
    std::string sym_name(const GlobalValue &G) {
        StringRef n = G.getName();
        if (n.empty()) return "__unnamed_" + std::to_string(++n_unnamed);
        if (n[0] == 1) n = n.drop_front();  // "\01" = do not mangle
        return n.str();
    }
    uint32_t linkage_flags(const GlobalValue &G) {
        if (G.hasLocalLinkage()) return GIR_GF_INTERNAL;
        if (G.hasWeakLinkage() || G.hasLinkOnceLinkage() || G.hasCommonLinkage() ||
            G.hasExternalWeakLinkage())
            return GIR_GF_WEAK;
        return 0;
    }

    uint32_t libc_func(const char *name, uint32_t &cache) {
        if (cache != GIR_NONE) return cache;
        if (const Function *f = M.getFunction(name)) {
            auto it = gmap.find(f);
            if (it != gmap.end() && !f->hasLocalLinkage()) return cache = it->second;
        }
        return cache = add_global(name, GIR_G_FUNC, 0, 16);
    }

    // ------------------------------------------------------------- constants
    uint32_t new_const(uint64_t v, uint8_t t) {
        unsigned b = bits(t);
        if (b < 64) v &= (1ull << b) - 1;
        T.consts.push_back(GirConst{(int64_t)v, t, 0});
        return GIR_MK(GIR_V_CONST, T.consts.size() - 1);
    }

    // ---------------------------------------------------------- instructions
    uint32_t emit(uint8_t op, uint8_t t, uint8_t sub, uint8_t aux, uint32_t a, uint32_t b, uint32_t c,
                  unsigned refs) {
        uint32_t idx = (uint32_t)T.insts.size();
        if (idx >= PH_BASE) fail("module too large for GIR (instruction count)");
        T.insts.push_back(GirInst{op, t, sub, aux, a, b, c});
        if (refs & RA) note(a, idx, 0);
        if (refs & RB) note(b, idx, 1);
        if (refs & RC) note(c, idx, 2);
        return GIR_MK(GIR_V_INST, idx);
    }
    // A placeholder is used exactly once: remember where it was stored.
    void note(uint32_t r, uint32_t where, uint32_t field) {
        if (!is_placeholder(r)) return;
        Fix &fx = fixes[GIR_IDX(r) - PH_BASE];
        fx.where = where;
        fx.field = field;
    }
    void push_ref(uint32_t r) {
        note(r, (uint32_t)T.opnds.size(), 3);
        T.opnds.push_back(r);
    }
    // ref() for a value used more than once by the lowering of one LLVM
    // instruction: a placeholder is turned into a real (copied) value.
    uint32_t ref_multi(const Value *v) {
        uint32_t r = ref(v);
        if (is_placeholder(r)) {
            uint8_t t = ty(v->getType());
            r = emit(GIR_BITCAST, t, 0, t, r, 0, 0, RA);
        }
        return r;
    }
    // Record that `I` has value `r`: an identity mapping, unless `r` is a
    // one-use placeholder, in which case a copy is emitted.
    void alias(const Instruction &I, uint32_t r, uint8_t t) {
        if (is_placeholder(r)) r = emit(GIR_BITCAST, t, 0, t, r, 0, 0, RA);
        vmap[&I] = r;
    }

    // Value -> ref. May append instructions (materialized constant
    // expressions) to the current block.
    uint32_t ref(const Value *v) {
        if (const auto *I = dyn_cast<Instruction>(v)) {
            auto it = vmap.find(I);
            if (it != vmap.end()) return it->second;
            uint32_t k = (uint32_t)fixes.size();
            if (PH_BASE + k >= (1u << 30)) fail("too many forward references");
            fixes.push_back(Fix{I, GIR_NONE, 0});
            return GIR_MK(GIR_V_INST, PH_BASE + k);
        }
        if (const auto *A = dyn_cast<Argument>(v)) return GIR_MK(GIR_V_ARG, A->getArgNo());
        if (const auto *CI = dyn_cast<ConstantInt>(v)) {
            uint8_t t = ty(CI->getType());
            return new_const(CI->getZExtValue(), t);
        }
        if (isa<ConstantPointerNull>(v)) return new_const(0, ty(v->getType()));
        if (isa<UndefValue>(v)) return new_const(0, ty(v->getType()));  // undef and poison
        if (const auto *G = dyn_cast<GlobalValue>(v)) {
            auto it = gmap.find(G);
            if (it != gmap.end()) return GIR_MK(GIR_V_GLOBAL, it->second);
            if (isa<GlobalAlias>(G)) fail("global alias '" + G->getName().str() + "'");
            if (isa<GlobalIFunc>(G)) fail("ifunc '" + G->getName().str() + "'");
            if (const auto *GV = dyn_cast<GlobalVariable>(G); GV && GV->isThreadLocal())
                fail("thread-local variable '" + G->getName().str() + "'");
            if (const auto *Fn = dyn_cast<Function>(G); Fn && Fn->isIntrinsic())
                fail("address of intrinsic '" + G->getName().str() + "'");
            fail("reference to unexported global '" + G->getName().str() + "'");
        }
        if (const auto *CE = dyn_cast<ConstantExpr>(v)) {
            if (!in_phi_prepass) {
                auto it = phice.find(CE);
                if (it != phice.end()) return it->second;
            }
            return materialize(CE);
        }
        if (isa<ConstantFP>(v)) fail("floating-point constant");
        if (isa<BlockAddress>(v)) fail("blockaddress");
        if (isa<ConstantVector>(v) || isa<ConstantDataVector>(v) || isa<ConstantAggregateZero>(v))
            fail("vector or aggregate constant");
        if (isa<InlineAsm>(v)) fail("inline assembly");
        fail("operand kind");
    }

    uint32_t materialize(const ConstantExpr *CE) {
        switch (CE->getOpcode()) {
        case Instruction::GetElementPtr: return gep(cast<GEPOperator>(CE));
        case Instruction::Trunc:
        case Instruction::ZExt:
        case Instruction::SExt:
        case Instruction::PtrToInt:
        case Instruction::IntToPtr:
        case Instruction::BitCast:
            return cast_op(CE->getOpcode(), CE->getOperand(0), CE->getType());
        case Instruction::Add:
        case Instruction::Sub:
        case Instruction::Mul:
        case Instruction::Xor:
        case Instruction::And:
        case Instruction::Or:
        case Instruction::Shl:
        case Instruction::LShr:
        case Instruction::AShr: {
            uint32_t a = ref(CE->getOperand(0));
            uint32_t b = ref(CE->getOperand(1));
            return emit(binop(CE->getOpcode()), ty(CE->getType()), 0, 0, a, b, 0, RA | RB);
        }
        default: break;
        }
        fail(std::string("constant expression '") + CE->getOpcodeName() + "'");
    }

    uint8_t binop(unsigned opc) {
        switch (opc) {
        case Instruction::Add: return GIR_ADD;
        case Instruction::Sub: return GIR_SUB;
        case Instruction::Mul: return GIR_MUL;
        case Instruction::SDiv: return GIR_SDIV;
        case Instruction::UDiv: return GIR_UDIV;
        case Instruction::SRem: return GIR_SREM;
        case Instruction::URem: return GIR_UREM;
        case Instruction::And: return GIR_AND;
        case Instruction::Or: return GIR_OR;
        case Instruction::Xor: return GIR_XOR;
        case Instruction::Shl: return GIR_SHL;
        case Instruction::LShr: return GIR_LSHR;
        case Instruction::AShr: return GIR_ASHR;
        default: break;
        }
        fail("binary operator");
    }

    uint32_t cast_op(unsigned opc, const Value *src, const Type *dst) {
        uint8_t st = ty(src->getType()), dt = ty(dst);
        uint8_t op;
        switch (opc) {
        case Instruction::Trunc: op = GIR_TRUNC; break;
        case Instruction::ZExt: op = GIR_ZEXT; break;
        case Instruction::SExt: op = GIR_SEXT; break;
        case Instruction::PtrToInt: op = GIR_PTRTOINT; break;
        case Instruction::IntToPtr: op = GIR_INTTOPTR; break;
        case Instruction::BitCast:
            if (st != dt) fail("bitcast between different types");
            op = GIR_BITCAST;
            break;
        default: fail("cast");
        }
        uint32_t a = ref(src);
        return emit(op, dt, 0, st, a, 0, 0, RA);
    }

    // GEP (instruction or constant expression): constant indices fold into
    // one byte offset, the others become (index, scale) pairs.
    uint32_t gep(const GEPOperator *G) {
        if (G->getType()->isVectorTy()) fail("vector GEP");
        uint32_t base = ref(G->getPointerOperand());
        uint64_t off = 0;
        SmallVector<uint32_t, 8> dyn;
        for (auto GTI = gep_type_begin(G), E = gep_type_end(G); GTI != E; ++GTI) {
            const Value *idx = GTI.getOperand();
            if (StructType *ST = GTI.getStructTypeOrNull()) {
                unsigned fi = (unsigned)cast<ConstantInt>(idx)->getZExtValue();
                off += DL.getStructLayout(ST)->getElementOffset(fi).getFixedValue();
                continue;
            }
            TypeSize ts = GTI.getSequentialElementStride(DL);
            if (ts.isScalable()) fail("scalable GEP");
            uint64_t stride = ts.getFixedValue();
            if (const auto *CI = dyn_cast<ConstantInt>(idx)) {
                if (CI->getBitWidth() > 64) fail("GEP index wider than 64 bits");
                off += (uint64_t)CI->getSExtValue() * stride;
                continue;
            }
            if (isa<UndefValue>(idx) || stride == 0) continue;
            if (idx->getType()->isVectorTy()) fail("vector GEP index");
            if (stride > 0xFFFFFFFFull) fail("GEP stride above 4 GiB");
            ty(idx->getType());
            dyn.push_back(ref(idx));
            dyn.push_back((uint32_t)stride);
        }
        if (dyn.empty() && off == 0 && !is_placeholder(base)) return base;
        uint32_t s = (uint32_t)T.opnds.size();
        T.opnds.push_back((uint32_t)off);
        T.opnds.push_back((uint32_t)(off >> 32));
        for (size_t i = 0; i < dyn.size(); i += 2) {
            push_ref(dyn[i]);
            T.opnds.push_back(dyn[i + 1]);
        }
        return emit(GIR_GEP, GIR_T_PTR, 0, 0, base, s, (uint32_t)(dyn.size() / 2), RA);
    }

    static uint8_t pred(CmpInst::Predicate p) {
        switch (p) {
        case CmpInst::ICMP_EQ: return GIR_EQ;
        case CmpInst::ICMP_NE: return GIR_NE;
        case CmpInst::ICMP_UGT: return GIR_UGT;
        case CmpInst::ICMP_UGE: return GIR_UGE;
        case CmpInst::ICMP_ULT: return GIR_ULT;
        case CmpInst::ICMP_ULE: return GIR_ULE;
        case CmpInst::ICMP_SGT: return GIR_SGT;
        case CmpInst::ICMP_SGE: return GIR_SGE;
        case CmpInst::ICMP_SLT: return GIR_SLT;
        default: return GIR_SLE;
        }
    }

    uint32_t block(const BasicBlock *BB) { return bmap[BB->getNumber()]; }

    // ---------------------------------------------------------------- calls
    // Argument for a call: `signext` narrower than 32 bits gets an explicit
    // SEXT to i32 (the SysV caller-extends rule as clang implements it).
    uint32_t call_arg(const CallBase &CB, unsigned i) {
        const Value *v = CB.getArgOperand(i);
        if (CB.paramHasAttr(i, Attribute::ByVal)) fail("byval argument");
        if (CB.paramHasAttr(i, Attribute::InAlloca) || CB.paramHasAttr(i, Attribute::Preallocated))
            fail("inalloca/preallocated argument");
        uint8_t t = ty(v->getType());
        uint32_t r = ref(v);
        if (CB.paramHasAttr(i, Attribute::SExt) && bits(t) < 32)
            r = emit(GIR_SEXT, GIR_T_I32, 0, t, r, 0, 0, RA);
        return r;
    }

    void emit_call(const CallBase &CB, uint32_t callee, unsigned nargs, uint8_t rt, bool vararg) {
        SmallVector<uint32_t, 16> args;
        for (unsigned i = 0; i < nargs; i++) args.push_back(call_arg(CB, i));
        uint32_t s = (uint32_t)T.opnds.size();
        for (uint32_t a : args) push_ref(a);
        uint32_t r = emit(GIR_CALL, rt, vararg ? GIR_F_VARARG : 0, 0, callee, s, nargs, RA);
        if (rt != GIR_T_VOID) vmap[&CB] = r;
    }

    // libc call for a memory intrinsic: (dst, src/val, len), drop isvolatile.
    void libc_call(const CallBase &CB, uint32_t g) {
        uint32_t a0 = ref(CB.getArgOperand(0));
        uint32_t a1 = ref(CB.getArgOperand(1));
        uint32_t a2 = ref(CB.getArgOperand(2));
        ty(CB.getArgOperand(2)->getType());
        uint32_t s = (uint32_t)T.opnds.size();
        push_ref(a0);
        push_ref(a1);
        push_ref(a2);
        emit(GIR_CALL, GIR_T_VOID, 0, 0, GIR_MK(GIR_V_GLOBAL, g), s, 3, 0);
    }

    // select(icmp pred a, b; a; b) etc.
    uint32_t cmp_select(uint8_t p, uint32_t a, uint32_t b, uint32_t x, uint32_t y, uint8_t t) {
        uint32_t c = emit(GIR_ICMP, GIR_T_I1, p, t, a, b, 0, RA | RB);
        return emit(GIR_SELECT, t, 0, 0, c, x, y, RA | RB | RC);
    }

    void intrinsic(const CallBase &CB, Intrinsic::ID id) {
        switch (id) {
        case Intrinsic::memcpy:
        case Intrinsic::memcpy_inline:
            return libc_call(CB, libc_func("memcpy", libc_memcpy));
        case Intrinsic::memmove:
            return libc_call(CB, libc_func("memmove", libc_memmove));
        case Intrinsic::memset:
        case Intrinsic::memset_inline:
            return libc_call(CB, libc_func("memset", libc_memset));
        case Intrinsic::lifetime_start:
        case Intrinsic::lifetime_end:
        case Intrinsic::dbg_declare:
        case Intrinsic::dbg_value:
        case Intrinsic::dbg_label:
        case Intrinsic::dbg_assign:
        case Intrinsic::experimental_noalias_scope_decl:
        case Intrinsic::assume:
        case Intrinsic::donothing:
        case Intrinsic::sideeffect:
        case Intrinsic::var_annotation:
        case Intrinsic::invariant_end:
        case Intrinsic::pseudoprobe:
        case Intrinsic::codeview_annotation:
            return;
        case Intrinsic::invariant_start:
            vmap[&CB] = new_const(0, GIR_T_PTR);
            return;
        case Intrinsic::expect:
        case Intrinsic::expect_with_probability:
        case Intrinsic::ptr_annotation:
        case Intrinsic::annotation:
        case Intrinsic::launder_invariant_group:
        case Intrinsic::strip_invariant_group: {
            uint8_t t = ty(CB.getType());
            alias(CB, ref(CB.getArgOperand(0)), t);
            return;
        }
        case Intrinsic::trap: {
            // __builtin_trap: always followed by `unreachable`, which traps.
            const Instruction *next = CB.getNextNode();
            if (next && isa<UnreachableInst>(next)) return;
            break;
        }
        case Intrinsic::abs: {
            uint8_t t = ty(CB.getType());
            uint32_t x = ref_multi(CB.getArgOperand(0));
            uint32_t neg = emit(GIR_SUB, t, 0, 0, new_const(0, t), x, 0, RB);
            uint32_t r = cmp_select(GIR_SLT, x, new_const(0, t), neg, x, t);
            vmap[&CB] = r;
            return;
        }
        case Intrinsic::smax:
        case Intrinsic::smin:
        case Intrinsic::umax:
        case Intrinsic::umin: {
            uint8_t t = ty(CB.getType());
            uint8_t p = id == Intrinsic::smax ? GIR_SGT : id == Intrinsic::smin ? GIR_SLT
                      : id == Intrinsic::umax ? GIR_UGT : GIR_ULT;
            uint32_t a = ref_multi(CB.getArgOperand(0));
            uint32_t b = ref_multi(CB.getArgOperand(1));
            vmap[&CB] = cmp_select(p, a, b, a, b, t);
            return;
        }
        default: break;
        }
        fail("intrinsic '" + CB.getCalledFunction()->getName().str() + "'");
    }

    void call(const CallBase &CB) {
        const Value *callee = CB.getCalledOperand();
        if (CB.isInlineAsm()) fail("inline assembly");
        if (const auto *fn = dyn_cast<Function>(callee); fn && fn->isIntrinsic())
            return intrinsic(CB, fn->getIntrinsicID());
        if (CB.getCallingConv() != CallingConv::C) fail("calling convention " + std::to_string(CB.getCallingConv()));
        if (CB.hasOperandBundles()) fail("operand bundle");
        FunctionType *FT = CB.getFunctionType();
        uint8_t rt = ret_ty(FT->getReturnType());
        uint32_t c = ref(callee);
        emit_call(CB, c, CB.arg_size(), rt, FT->isVarArg());
    }

    // ------------------------------------------------------------ one inst
    void inst(const Instruction &I) {
        curI = &I;
        switch (I.getOpcode()) {
        case Instruction::Ret: {
            const auto &R = cast<ReturnInst>(I);
            uint32_t v = GIR_NONE;
            if (const Value *rv = R.getReturnValue()) {
                uint8_t t = ty(rv->getType());
                v = ref(rv);
                if (F->hasRetAttribute(Attribute::SExt) && bits(t) < 32)
                    v = emit(GIR_SEXT, GIR_T_I32, 0, t, v, 0, 0, RA);
            } else if (sret_arg != GIR_NONE) {
                v = GIR_MK(GIR_V_ARG, sret_arg);
            }
            emit(GIR_RET, GIR_T_VOID, 0, 0, v, 0, 0, RA);
            return;
        }
        case Instruction::Br: {
            const auto &B = cast<BranchInst>(I);
            if (B.isUnconditional()) {
                emit(GIR_BR, GIR_T_VOID, 0, 0, block(B.getSuccessor(0)), 0, 0, 0);
            } else {
                uint32_t c = ref(B.getCondition());
                emit(GIR_CONDBR, GIR_T_VOID, 0, 0, c, block(B.getSuccessor(0)), block(B.getSuccessor(1)), RA);
            }
            return;
        }
        case Instruction::Switch: {
            const auto &S = cast<SwitchInst>(I);
            uint8_t t = ty(S.getCondition()->getType());
            uint32_t c = ref(S.getCondition());
            SmallVector<uint32_t, 32> cases;
            for (const auto &cs : S.cases()) {
                cases.push_back(new_const(cs.getCaseValue()->getZExtValue(), t));
                cases.push_back(block(cs.getCaseSuccessor()));
            }
            uint32_t s = (uint32_t)T.opnds.size();
            T.opnds.push_back(block(S.getDefaultDest()));
            T.opnds.insert(T.opnds.end(), cases.begin(), cases.end());
            emit(GIR_SWITCH, GIR_T_VOID, 0, 0, c, s, (uint32_t)(cases.size() / 2), RA);
            return;
        }
        case Instruction::Unreachable:
            emit(GIR_UNREACHABLE, GIR_T_VOID, 0, 0, 0, 0, 0, 0);
            return;
        case Instruction::Add: case Instruction::Sub: case Instruction::Mul:
        case Instruction::SDiv: case Instruction::UDiv: case Instruction::SRem: case Instruction::URem:
        case Instruction::And: case Instruction::Or: case Instruction::Xor:
        case Instruction::Shl: case Instruction::LShr: case Instruction::AShr: {
            uint8_t t = ty(I.getType());
            if (t == GIR_T_PTR) fail("pointer arithmetic operator");
            uint32_t a = ref(I.getOperand(0));
            uint32_t b = ref(I.getOperand(1));
            vmap[&I] = emit(binop(I.getOpcode()), t, 0, 0, a, b, 0, RA | RB);
            return;
        }
        case Instruction::ICmp: {
            const auto &C = cast<ICmpInst>(I);
            uint8_t ot = ty(C.getOperand(0)->getType());
            ty(C.getType());
            uint32_t a = ref(C.getOperand(0));
            uint32_t b = ref(C.getOperand(1));
            vmap[&I] = emit(GIR_ICMP, GIR_T_I1, pred(C.getPredicate()), ot, a, b, 0, RA | RB);
            return;
        }
        case Instruction::Select: {
            const auto &S = cast<SelectInst>(I);
            ty(S.getCondition()->getType());
            uint8_t t = ty(S.getType());
            uint32_t c = ref(S.getCondition());
            uint32_t a = ref(S.getTrueValue());
            uint32_t b = ref(S.getFalseValue());
            vmap[&I] = emit(GIR_SELECT, t, 0, 0, c, a, b, RA | RB | RC);
            return;
        }
        case Instruction::Trunc: case Instruction::ZExt: case Instruction::SExt:
        case Instruction::PtrToInt: case Instruction::IntToPtr: case Instruction::BitCast:
            vmap[&I] = cast_op(I.getOpcode(), I.getOperand(0), I.getType());
            return;
        case Instruction::Freeze: {
            uint8_t t = ty(I.getType());
            alias(I, ref(I.getOperand(0)), t);
            return;
        }
        case Instruction::Alloca: {
            const auto &A = cast<AllocaInst>(I);
            if (!A.isStaticAlloca() || A.getParent() != &F->getEntryBlock())
                fail("dynamic alloca (not static or not in the entry block)");
            if (A.getAddressSpace() != 0) fail("alloca in non-zero address space");
            uint64_t align = A.getAlign().value();
            if (align > 16) fail("alloca with alignment above 16");
            std::optional<TypeSize> sz = A.getAllocationSize(DL);
            if (!sz || sz->isScalable()) fail("alloca of unknown size");
            uint64_t size = sz->getFixedValue();
            if (size > 0x7FFFFFFFull) fail("alloca above 2 GiB");
            vmap[&I] = emit(GIR_ALLOCA, GIR_T_PTR, 0, 0, (uint32_t)size, (uint32_t)align, 0, 0);
            return;
        }
        case Instruction::Load: {
            const auto &L = cast<LoadInst>(I);
            if (L.isAtomic()) fail("atomic load");
            uint8_t t = ty(L.getType());
            ty(L.getPointerOperandType());
            uint32_t p = ref(L.getPointerOperand());
            vmap[&I] = emit(GIR_LOAD, t, 0, 0, p, 0, 0, RA);
            return;
        }
        case Instruction::Store: {
            const auto &S = cast<StoreInst>(I);
            if (S.isAtomic()) fail("atomic store");
            uint8_t t = ty(S.getValueOperand()->getType());
            ty(S.getPointerOperandType());
            uint32_t v = ref(S.getValueOperand());
            uint32_t p = ref(S.getPointerOperand());
            emit(GIR_STORE, GIR_T_VOID, 0, t, v, p, 0, RA | RB);
            return;
        }
        case Instruction::GetElementPtr: {
            uint32_t r = gep(cast<GEPOperator>(&I));
            alias(I, r, GIR_T_PTR);
            return;
        }
        case Instruction::Call:
            call(cast<CallBase>(I));
            return;
        case Instruction::PHI: {
            const auto &P = cast<PHINode>(I);
            uint8_t t = ty(P.getType());
            SmallVector<uint32_t, 16> pairs;
            for (unsigned i = 0, n = P.getNumIncomingValues(); i < n; i++) {
                pairs.push_back(ref(P.getIncomingValue(i)));
                pairs.push_back(block(P.getIncomingBlock(i)));
            }
            uint32_t s = (uint32_t)T.opnds.size();
            for (size_t i = 0; i < pairs.size(); i += 2) {
                push_ref(pairs[i]);
                T.opnds.push_back(pairs[i + 1]);
            }
            vmap[&I] = emit(GIR_PHI, t, 0, 0, 0, s, (uint32_t)(pairs.size() / 2), 0);
            return;
        }
        case Instruction::VAArg: fail("va_arg");
        case Instruction::Invoke: case Instruction::Resume: case Instruction::LandingPad:
        case Instruction::CleanupPad: case Instruction::CatchPad: case Instruction::CatchSwitch:
        case Instruction::CatchRet: case Instruction::CleanupRet:
            fail("exception handling");
        case Instruction::AtomicRMW: case Instruction::AtomicCmpXchg: case Instruction::Fence:
            fail("atomics");
        case Instruction::ExtractValue: case Instruction::InsertValue:
            fail("aggregate value operation");
        case Instruction::ExtractElement: case Instruction::InsertElement: case Instruction::ShuffleVector:
            fail("vector operation");
        case Instruction::IndirectBr: fail("indirectbr");
        case Instruction::CallBr: fail("callbr (asm goto)");
        default: break;
        }
        fail(std::string("instruction '") + I.getOpcodeName() + "'");
    }

    // ------------------------------------------------------------ functions
    uint32_t sret_arg = GIR_NONE;

    void function(const Function &Fn, uint32_t g) {
        F = &Fn;
        curI = nullptr;
        if (Fn.getCallingConv() != CallingConv::C) fail("calling convention " + std::to_string(Fn.getCallingConv()));
        if (Fn.hasSection()) fail("function in a custom section");
        if (Fn.hasPrefixData() || Fn.hasPrologueData()) fail("prefix/prologue data");
        if (Fn.hasGC()) fail("garbage collector");
        FunctionType *FT = Fn.getFunctionType();

        GirFunc gf{};
        gf.global = g;
        gf.flags = (Fn.hasLocalLinkage() ? GIR_FN_INTERNAL : 0) | (FT->isVarArg() ? GIR_FN_VARARG : 0);
        gf.first_block = (uint32_t)T.blocks.size();
        gf.first_inst = (uint32_t)T.insts.size();
        gf.n_args = (uint32_t)Fn.arg_size();
        gf.ret_ty = ret_ty(FT->getReturnType());
        sret_arg = GIR_NONE;
        gf.arg_tys = (uint32_t)T.opnds.size();
        for (const Argument &A : Fn.args()) {
            if (A.hasByValAttr()) fail("byval parameter");
            if (A.hasInAllocaAttr() || A.hasPreallocatedAttr()) fail("inalloca/preallocated parameter");
            if (A.hasStructRetAttr()) sret_arg = A.getArgNo();
            T.opnds.push_back(ty(A.getType()));
        }
        if (sret_arg != GIR_NONE) {
            if (gf.ret_ty != GIR_T_VOID) fail("sret function with a return value");
            gf.ret_ty = GIR_T_PTR;
        }
        T.globals[g].func = (uint32_t)T.funcs.size();

        bmap.assign(Fn.getMaxBlockNumber(), GIR_NONE);
        uint32_t nb = 0;
        for (const BasicBlock &BB : Fn) bmap[BB.getNumber()] = nb++;
        vmap.clear();
        phice.clear();
        fixes.clear();
        T.n_llvm_insts += Fn.getInstructionCount();

        bool entry = true;
        for (const BasicBlock &BB : Fn) {
            GirBlock b{(uint32_t)T.insts.size(), 0};
            if (entry) {
                // Constant expressions used by PHIs are computed once, here.
                in_phi_prepass = true;
                for (const BasicBlock &PB : Fn)
                    for (const PHINode &P : PB.phis()) {
                        curI = &P;
                        for (const Value *v : P.incoming_values())
                            if (const auto *CE = dyn_cast<ConstantExpr>(v))
                                if (!phice.count(CE)) phice[CE] = materialize(CE);
                    }
                in_phi_prepass = false;
                entry = false;
            }
            for (const Instruction &I : BB) inst(I);
            b.n_inst = (uint32_t)T.insts.size() - b.first_inst;
            T.blocks.push_back(b);
        }
        curI = nullptr;
        for (const Fix &fx : fixes) {
            auto it = vmap.find(fx.v);
            if (it == vmap.end() || is_placeholder(it->second)) {
                curI = cast<Instruction>(fx.v);
                fail("use of an instruction without a GIR value");
            }
            if (fx.field == 3) T.opnds[fx.where] = it->second;
            else if (fx.field == 0) T.insts[fx.where].a = it->second;
            else if (fx.field == 1) T.insts[fx.where].b = it->second;
            else T.insts[fx.where].c = it->second;
        }
        gf.n_blocks = (uint32_t)T.blocks.size() - gf.first_block;
        gf.n_inst = (uint32_t)T.insts.size() - gf.first_inst;
        T.funcs.push_back(gf);
        F = nullptr;
    }

    // ---------------------------------------------------------- initializers
    void init(const GlobalVariable &GV, uint32_t g, const Constant *C, size_t at, uint32_t off) {
        if (isa<ConstantAggregateZero>(C) || isa<UndefValue>(C) || isa<ConstantPointerNull>(C)) return;
        if (const auto *CI = dyn_cast<ConstantInt>(C)) {
            const APInt &v = CI->getValue();
            unsigned n = (unsigned)DL.getTypeStoreSize(CI->getType());
            for (unsigned i = 0; i < n; i++)
                T.data[at + i] = (uint8_t)v.extractBitsAsZExtValue(std::min(8u, v.getBitWidth() - i * 8), i * 8);
            return;
        }
        if (const auto *CF = dyn_cast<ConstantFP>(C)) {
            APInt v = CF->getValueAPF().bitcastToAPInt();
            unsigned n = (unsigned)DL.getTypeStoreSize(CF->getType());
            for (unsigned i = 0; i < n && i * 8 < v.getBitWidth(); i++)
                T.data[at + i] = (uint8_t)v.extractBitsAsZExtValue(std::min(8u, v.getBitWidth() - i * 8), i * 8);
            return;
        }
        if (const auto *CDS = dyn_cast<ConstantDataSequential>(C)) {
            StringRef raw = CDS->getRawDataValues();
            std::memcpy(&T.data[at], raw.data(), raw.size());
            return;
        }
        if (const auto *CA = dyn_cast<ConstantArray>(C)) {
            uint64_t es = DL.getTypeAllocSize(CA->getType()->getElementType());
            for (unsigned i = 0, n = CA->getNumOperands(); i < n; i++)
                init(GV, g, CA->getOperand(i), at + i * es, off + (uint32_t)(i * es));
            return;
        }
        if (const auto *CS = dyn_cast<ConstantStruct>(C)) {
            const StructLayout *SL = DL.getStructLayout(CS->getType());
            for (unsigned i = 0, n = CS->getNumOperands(); i < n; i++) {
                uint64_t eo = SL->getElementOffset(i).getFixedValue();
                init(GV, g, CS->getOperand(i), at + eo, off + (uint32_t)eo);
            }
            return;
        }
        if (const auto *CV = dyn_cast<ConstantVector>(C)) {
            Type *et = CV->getType()->getElementType();
            if (DL.getTypeSizeInBits(et) % 8) fail_global(GV, "vector initializer with sub-byte elements");
            uint64_t es = DL.getTypeAllocSize(et);
            for (unsigned i = 0, n = CV->getNumOperands(); i < n; i++)
                init(GV, g, CV->getOperand(i), at + i * es, off + (uint32_t)(i * es));
            return;
        }
        if (isa<GlobalValue>(C) || isa<ConstantExpr>(C)) {
            const Constant *p = C;
            unsigned width = (unsigned)DL.getTypeStoreSize(C->getType());
            if (const auto *CE = dyn_cast<ConstantExpr>(C); CE && CE->getOpcode() == Instruction::PtrToInt)
                p = CE->getOperand(0);
            if (const auto *CE = dyn_cast<ConstantExpr>(p); CE && CE->getOpcode() == Instruction::IntToPtr)
                if (const auto *CI = dyn_cast<ConstantInt>(CE->getOperand(0))) {
                    uint64_t v = CI->getZExtValue();
                    for (unsigned i = 0; i < width && i < 8; i++) T.data[at + i] = (uint8_t)(v >> (8 * i));
                    return;
                }
            if (!p->getType()->isPointerTy() || width != 8)
                fail_global(GV, "initializer expression that is not a 64-bit address");
            APInt offs(64, 0);
            const Value *base = p->stripAndAccumulateConstantOffsets(DL, offs, true);
            int64_t addend = offs.getSExtValue();
            if (isa<ConstantPointerNull>(base)) {
                for (unsigned i = 0; i < 8; i++) T.data[at + i] = (uint8_t)((uint64_t)addend >> (8 * i));
                return;
            }
            const auto *bg = dyn_cast<GlobalValue>(base);
            auto it = bg ? gmap.find(bg) : gmap.end();
            if (it == gmap.end()) fail_global(GV, "initializer refers to something other than a global");
            if (addend < INT32_MIN || addend > INT32_MAX) fail_global(GV, "relocation addend out of 32-bit range");
            T.drelocs.push_back(GirDataReloc{g, off, it->second, (int32_t)addend});
            return;
        }
        if (isa<BlockAddress>(C)) fail_global(GV, "blockaddress in initializer");
        fail_global(GV, "initializer constant kind");
    }

    // ---------------------------------------------------------------- module
    void run() {
        T.strtab.push_back(0);
        // Pass 1: global indices.
        for (const GlobalVariable &GV : M.globals()) {
            StringRef n = GV.getName();
            if (n == "llvm.used" || n == "llvm.compiler.used" || n == "llvm.global.annotations") continue;
            if (n.starts_with("llvm.") || GV.hasAppendingLinkage())
                fail_global(GV, "special global (constructors/destructors or appending linkage)");
            if (GV.isThreadLocal()) fail_global(GV, "thread-local variable");
            if (GV.getAddressSpace() != 0) fail_global(GV, "non-zero address space");
            bool defined = !GV.isDeclaration() && !GV.hasAvailableExternallyLinkage();
            if (!defined && GV.use_empty()) continue;
            if (defined && GV.hasSection()) fail_global(GV, "variable in a custom section");
            uint32_t flags = linkage_flags(GV);
            uint32_t align = 1;
            if (defined) {
                flags |= GIR_GF_DEFINED;
                if (GV.isConstant()) flags |= GIR_GF_CONST;
                align = (uint32_t)DL.getPreferredAlign(&GV).value();
            }
            gmap[&GV] = add_global(sym_name(GV), GIR_G_VAR, flags, align);
        }
        for (const Function &Fn : M.functions()) {
            if (Fn.isIntrinsic()) continue;
            bool defined = !Fn.isDeclaration() && !Fn.hasAvailableExternallyLinkage();
            if (!defined && Fn.use_empty()) continue;
            uint32_t flags = linkage_flags(Fn) | (defined ? GIR_GF_DEFINED : 0);
            gmap[&Fn] = add_global(sym_name(Fn), GIR_G_FUNC, flags, 16);
        }
        if (!M.aliases().empty()) {
            const GlobalAlias &A = *M.aliases().begin();
            fail_global(A, "global alias");
        }
        if (!M.ifuncs().empty()) fail_global(*M.ifuncs().begin(), "ifunc");
        if (!M.getModuleInlineAsm().empty()) {
            std::fprintf(stderr, "goovm-llc: unsupported: module-level inline assembly\n");
            std::exit(2);
        }
        // Pass 2: initializers.
        for (const GlobalVariable &GV : M.globals()) {
            auto it = gmap.find(&GV);
            if (it == gmap.end()) continue;
            GirGlobal &G = T.globals[it->second];
            if (!(G.flags & GIR_GF_DEFINED)) continue;
            uint64_t size = DL.getTypeAllocSize(GV.getValueType());
            if (size > 0x7FFFFFFFull) fail_global(GV, "variable above 2 GiB");
            G.size = (uint32_t)size;
            const Constant *C = GV.getInitializer();
            if (C->isNullValue() || isa<UndefValue>(C)) {
                G.flags |= GIR_GF_ZERO;
                continue;
            }
            size_t at = T.data.size();
            T.data.resize(at + size, 0);
            T.globals[it->second].data = (uint32_t)at;
            init(GV, it->second, C, at, 0);
        }
        // Pass 3: function bodies.
        for (const Function &Fn : M.functions()) {
            auto it = gmap.find(&Fn);
            if (it == gmap.end() || !(T.globals[it->second].flags & GIR_GF_DEFINED)) continue;
            function(Fn, it->second);
        }
    }
};

}  // namespace

void gir_export(const Module &m, GirTables &out) {
    Exporter e(m, out);
    e.run();
}

// ------------------------------------------------------------------ dump
static const char *op_name(unsigned op) {
    static const char *names[] = {"ret", "br", "condbr", "switch", "unreachable", "add", "sub", "mul",
                                  "sdiv", "udiv", "srem", "urem", "and", "or", "xor", "shl", "lshr",
                                  "ashr", "icmp", "select", "zext", "sext", "trunc", "ptrtoint",
                                  "inttoptr", "bitcast", "alloca", "load", "store", "gep", "call", "phi"};
    return op < GIR_OP_COUNT ? names[op] : "?";
}
static const char *ty_name(unsigned t) {
    static const char *names[] = {"void", "i1", "i8", "i16", "i32", "i64", "ptr", "f32", "f64"};
    return t <= GIR_T_F64 ? names[t] : "?";
}
static void dump_ref(const GirModule &m, uint32_t r, std::FILE *f) {
    if (r == GIR_NONE) { std::fputs("none", f); return; }
    uint32_t i = GIR_IDX(r);
    switch (GIR_KIND(r)) {
    case GIR_V_INST: std::fprintf(f, "%%%u", i); break;
    case GIR_V_ARG: std::fprintf(f, "arg%u", i); break;
    case GIR_V_CONST: std::fprintf(f, "%s %lld", ty_name(m.consts[i].ty), (long long)m.consts[i].value); break;
    default: std::fprintf(f, "@%.*s", (int)m.globals[i].name_len, (const char *)m.strtab + m.globals[i].name); break;
    }
}

void gir_dump(const GirModule &m, std::FILE *f) {
    static const char *preds[] = {"eq", "ne", "ugt", "uge", "ult", "ule", "sgt", "sge", "slt", "sle"};
    for (uint32_t g = 0; g < m.n_globals; g++) {
        const GirGlobal &G = m.globals[g];
        std::fprintf(f, "global %u %s @%.*s flags=%u align=%u size=%u data=%u func=%d\n", g,
                     G.kind == GIR_G_FUNC ? "func" : "var", (int)G.name_len, (const char *)m.strtab + G.name,
                     G.flags, G.align, G.size, G.data, (int)G.func);
    }
    for (uint32_t i = 0; i < m.n_drelocs; i++)
        std::fprintf(f, "dreloc owner=%u off=%u target=%u addend=%d\n", m.drelocs[i].owner, m.drelocs[i].offset,
                     m.drelocs[i].target, m.drelocs[i].addend);
    for (uint32_t fi = 0; fi < m.n_funcs; fi++) {
        const GirFunc &F = m.funcs[fi];
        const GirGlobal &G = m.globals[F.global];
        std::fprintf(f, "\nfunc %u @%.*s(", fi, (int)G.name_len, (const char *)m.strtab + G.name);
        for (uint32_t a = 0; a < F.n_args; a++) std::fprintf(f, "%s%s", a ? ", " : "", ty_name(m.opnds[F.arg_tys + a]));
        std::fprintf(f, ") -> %s flags=%u\n", ty_name(F.ret_ty), F.flags);
        for (uint32_t b = 0; b < F.n_blocks; b++) {
            const GirBlock &B = m.blocks[F.first_block + b];
            std::fprintf(f, " b%u:\n", b);
            for (uint32_t k = B.first_inst; k < B.first_inst + B.n_inst; k++) {
                const GirInst &I = m.insts[k];
                std::fprintf(f, "  %%%u = %s %s", k, op_name(I.op), ty_name(I.ty));
                switch (I.op) {
                case GIR_RET: std::fputc(' ', f); dump_ref(m, I.a, f); break;
                case GIR_BR: std::fprintf(f, " b%u", I.a); break;
                case GIR_CONDBR: std::fputc(' ', f); dump_ref(m, I.a, f); std::fprintf(f, ", b%u, b%u", I.b, I.c); break;
                case GIR_SWITCH:
                    std::fputc(' ', f); dump_ref(m, I.a, f);
                    std::fprintf(f, " default b%u", m.opnds[I.b]);
                    for (uint32_t c = 0; c < I.c; c++) {
                        std::fputs(", ", f); dump_ref(m, m.opnds[I.b + 1 + 2 * c], f);
                        std::fprintf(f, " -> b%u", m.opnds[I.b + 2 + 2 * c]);
                    }
                    break;
                case GIR_ICMP: std::fprintf(f, " %s %s ", preds[I.sub % 10], ty_name(I.aux)); dump_ref(m, I.a, f); std::fputs(", ", f); dump_ref(m, I.b, f); break;
                case GIR_SELECT: std::fputc(' ', f); dump_ref(m, I.a, f); std::fputs(", ", f); dump_ref(m, I.b, f); std::fputs(", ", f); dump_ref(m, I.c, f); break;
                case GIR_ALLOCA: std::fprintf(f, " size=%u align=%u", I.a, I.b); break;
                case GIR_LOAD: std::fputc(' ', f); dump_ref(m, I.a, f); break;
                case GIR_STORE: std::fprintf(f, " %s ", ty_name(I.aux)); dump_ref(m, I.a, f); std::fputs(", ", f); dump_ref(m, I.b, f); break;
                case GIR_GEP: {
                    std::fputc(' ', f); dump_ref(m, I.a, f);
                    int64_t off = (int64_t)((uint64_t)m.opnds[I.b] | ((uint64_t)m.opnds[I.b + 1] << 32));
                    std::fprintf(f, " + %lld", (long long)off);
                    for (uint32_t c = 0; c < I.c; c++) {
                        std::fputs(" + ", f); dump_ref(m, m.opnds[I.b + 2 + 2 * c], f);
                        std::fprintf(f, "*%u", m.opnds[I.b + 3 + 2 * c]);
                    }
                    break;
                }
                case GIR_CALL:
                    std::fprintf(f, "%s ", I.sub & GIR_F_VARARG ? " vararg" : ""); dump_ref(m, I.a, f); std::fputc('(', f);
                    for (uint32_t c = 0; c < I.c; c++) { if (c) std::fputs(", ", f); dump_ref(m, m.opnds[I.b + c], f); }
                    std::fputc(')', f);
                    break;
                case GIR_PHI:
                    for (uint32_t c = 0; c < I.c; c++) {
                        std::fputs(c ? ", [" : " [", f); dump_ref(m, m.opnds[I.b + 2 * c], f);
                        std::fprintf(f, ", b%u]", m.opnds[I.b + 2 * c + 1]);
                    }
                    break;
                case GIR_UNREACHABLE: break;
                default:
                    if (I.op >= GIR_ZEXT && I.op <= GIR_BITCAST) {
                        std::fprintf(f, " from %s ", ty_name(I.aux)); dump_ref(m, I.a, f);
                    } else {
                        std::fputc(' ', f); dump_ref(m, I.a, f); std::fputs(", ", f); dump_ref(m, I.b, f);
                    }
                }
                std::fputc('\n', f);
            }
        }
    }
}
