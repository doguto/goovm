// LLVM module -> GIR tables (GIR version 2, see gir/gir.h).
//
// One walk over the module. Globals first (so every function, variable and
// alias has a GIR global index), then initializers, then function bodies.
// Each LLVM instruction becomes zero or more GIR instructions in the same
// block: constant-expression operands are materialized right before their
// user, those used by PHIs at the start of the entry block (which dominates
// every predecessor). Uses of instructions that are not exported yet (PHIs,
// or blocks laid out before their dominator) get a placeholder that is
// patched when the function is complete.
//
// Anything GIR cannot express throws GirUnsupported with a message naming
// the construct, the function and the instruction.

#include "gir_export.h"
#include "gir_asm.h"

#include <cstdlib>
#include <cstring>
#include <string>

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IntrinsicsX86.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TargetParser/Triple.h"

using namespace llvm;

GirModule GirTables::view() const {
    GirModule m;
    m.header = &header;
    m.types = types.data();       m.n_types = (uint32_t)types.size();
    m.funcs = funcs.data();       m.n_funcs = (uint32_t)funcs.size();
    m.blocks = blocks.data();     m.n_blocks = (uint32_t)blocks.size();
    m.insts = insts.data();       m.n_insts = (uint32_t)insts.size();
    m.opnds = opnds.data();       m.n_opnds = (uint32_t)opnds.size();
    m.consts = consts.data();     m.n_consts = (uint32_t)consts.size();
    m.globals = globals.data();   m.n_globals = (uint32_t)globals.size();
    m.sections = sections.data(); m.n_sections = (uint32_t)sections.size();
    m.data = data.data();         m.n_data = (uint32_t)data.size();
    m.drelocs = drelocs.data();   m.n_drelocs = (uint32_t)drelocs.size();
    m.strtab = strtab.data();     m.n_strtab = (uint32_t)strtab.size();
    m.dlocs = dlocs.data();       m.n_dlocs = (uint32_t)dlocs.size();
    m.dscopes = dscopes.data();   m.n_dscopes = (uint32_t)dscopes.size();
    m.dfiles = dfiles.data();     m.n_dfiles = (uint32_t)dfiles.size();
    m.dstr = dstr.data();         m.n_dstr = (uint32_t)dstr.size();
    m.asms = asms.data();         m.n_asms = (uint32_t)asms.size();
    return m;
}

namespace {

// Placeholder refs for not-yet-exported instructions: kind INST, index in
// [PH_BASE, 2^30). Real instruction indices must stay below PH_BASE.
constexpr uint32_t PH_BASE = 0x3F000000u;

bool is_placeholder(uint32_t r) { return GIR_KIND(r) == GIR_V_INST && GIR_IDX(r) >= PH_BASE; }

struct Fix {
    const Value *v;
    uint32_t where;  // index into insts (field 0..2) or opnds (field 3)
    uint32_t field;  // 0 = a, 1 = b, 2 = c, 3 = opnds[where]
};

enum : unsigned { RA = 1, RB = 2, RC = 4 };  // which of a/b/c hold value refs

// Open-addressing map from pointers to u32 values, cleared in O(1) by a
// generation count (the per-function value map is cleared once per function
// and hit for every operand; llvm::DenseMap's clear() shrinks and rehashes).
struct PtrMap {
    struct E {
        const void *k;
        uint32_t v;
        uint32_t gen;
    };
    std::vector<E> tab;
    size_t mask = 0;
    uint32_t gen = 1;
    uint32_t count = 0;
    PtrMap() {
        tab.assign(1024, E{nullptr, 0, 0});
        mask = tab.size() - 1;
    }
    static size_t hash(const void *p) { return (size_t)((((uintptr_t)p >> 4) * 0x9E3779B97F4A7C15ull) >> 32); }
    void clear() {
        if (++gen == 0) {
            for (E &e : tab) e.gen = 0;
            gen = 1;
        }
        count = 0;
    }
    uint32_t *find(const void *k) {
        for (size_t i = hash(k) & mask;; i = (i + 1) & mask) {
            E &e = tab[i];
            if (e.gen != gen) return nullptr;
            if (e.k == k) return &e.v;
        }
    }
    bool count_of(const void *k) { return find(k) != nullptr; }
    uint32_t &operator[](const void *k) {
        if (2 * (size_t)(count + 1) > tab.size()) grow();
        for (size_t i = hash(k) & mask;; i = (i + 1) & mask) {
            E &e = tab[i];
            if (e.gen != gen) {
                e = E{k, 0, gen};
                count++;
                return e.v;
            }
            if (e.k == k) return e.v;
        }
    }
    void grow() {
        std::vector<E> old;
        old.swap(tab);
        tab.assign(old.size() * 2, E{nullptr, 0, 0});
        mask = tab.size() - 1;
        uint32_t g = gen;
        gen = 1;
        count = 0;
        for (const E &e : old)
            if (e.gen == g) (*this)[e.k] = e.v;
    }
};

// Inline copies and fills up to this many bytes; larger or variable sizes
// call libc.
constexpr uint64_t MAX_INLINE_MEM = 256;

struct Exporter {
    const Module &M;
    const DataLayout &DL;
    GirTables &T;
    TargetLibraryInfoImpl TLII;
    TargetLibraryInfo TLI;

    DenseMap<const GlobalValue *, uint32_t> gmap;  // global -> GIR global index
    StringMap<uint32_t> libfns;                     // libcall name -> global
    PtrMap tmap;                                    // type -> type id
    DenseMap<const Constant *, uint32_t> cmap;      // FP / wide / aggregate constants
    DenseMap<const Constant *, uint32_t> cglob;     // relocatable aggregate constant -> private global
    StringMap<uint32_t> secmap;                     // section name -> sections index
    StringMap<uint32_t> dstrmap;
    DenseMap<const DILocation *, uint32_t> dlmap;
    DenseMap<const DIScope *, uint32_t> dsmap;
    DenseMap<const DIFile *, uint32_t> dfmap;
    uint32_t n_unnamed = 0;
    bool pie = false;

    // Per function.
    const Function *F = nullptr;
    const Instruction *curI = nullptr;
    PtrMap vmap;                                // instruction -> ref
    PtrMap phimat;                              // value used by a PHI, materialized in the entry block
    std::vector<uint32_t> bmap;                 // BB number -> local block
    std::vector<Fix> fixes;
    bool in_phi_prepass = false;
    uint32_t cur_dbg = 0;
    uint32_t sret_arg = GIR_NONE;
    uint32_t fn_flags = 0;
    const DILocation *last_dl = nullptr;
    uint32_t last_dl_idx = 0;
    std::string where;  // extra context for errors outside instructions

    Exporter(const Module &m, GirTables &t)
        : M(m), DL(m.getDataLayout()), T(t), TLII(Triple(m.getTargetTriple())), TLI(TLII) {}

    // ---------------------------------------------------------------- errors
    [[noreturn]] void fail(const std::string &why) {
        std::string s;
        raw_string_ostream os(s);
        os << "unsupported: " << why;
        if (!where.empty()) os << " (" << where << ")";
        if (F) os << " in function '" << F->getName() << "'";
        if (curI) {
            os << " at instruction:\n  ";
            curI->print(os);
        }
        os.flush();
        throw GirUnsupported{s};
    }
    [[noreturn]] void fail_global(const GlobalValue &G, const std::string &why) {
        throw GirUnsupported{"unsupported: " + why + " in global '" + G.getName().str() + "'"};
    }
    static std::string tystr(const Type *t) {
        std::string s;
        raw_string_ostream os(s);
        t->print(os);
        return os.str();
    }

    // ----------------------------------------------------------------- types
    uint16_t new_type(GirTypeDef d) {
        if (T.types.size() >= 0xFFFF) fail("too many types");
        T.types.push_back(d);
        return (uint16_t)(T.types.size() - 1);
    }
    void predefined_types() {
        auto def = [&](uint8_t k, uint8_t c, uint16_t bits, uint32_t size, uint32_t align, uint32_t store) {
            T.types.push_back(GirTypeDef{k, c, bits, size, align, store, 0, 0});
        };
        def(GIR_TK_VOID, GIR_C_NONE, 0, 0, 1, 0);    // VOID
        def(GIR_TK_INT, GIR_C_INT, 1, 1, 1, 1);      // I1
        def(GIR_TK_INT, GIR_C_INT, 8, 1, 1, 1);      // I8
        def(GIR_TK_INT, GIR_C_INT, 16, 2, 2, 2);     // I16
        def(GIR_TK_INT, GIR_C_INT, 32, 4, 4, 4);     // I32
        def(GIR_TK_INT, GIR_C_INT, 64, 8, 8, 8);     // I64
        def(GIR_TK_PTR, GIR_C_INT, 64, 8, 8, 8);     // PTR
        def(GIR_TK_FLOAT, GIR_C_FP, 32, 4, 4, 4);    // F32
        def(GIR_TK_FLOAT, GIR_C_FP, 64, 8, 8, 8);    // F64
        def(GIR_TK_FLOAT, GIR_C_X87, 80, 16, 16, 10);  // F80
        def(GIR_TK_INT, GIR_C_INT2, 128, 16, 16, 16);  // I128
        def(GIR_TK_FLOAT, GIR_C_FP, 16, 2, 2, 2);    // F16
        while (T.types.size() < GIR_T_FIRST_USER) def(GIR_TK_VOID, GIR_C_NONE, 0, 0, 1, 0);
    }
    // Type id of a value type; fails on anything GIR cannot hold.
    __attribute__((always_inline)) uint16_t ty(Type *t) {
        switch (t->getTypeID()) {
        case Type::IntegerTyID:
            switch (cast<IntegerType>(t)->getBitWidth()) {
            case 1: return GIR_T_I1;
            case 8: return GIR_T_I8;
            case 16: return GIR_T_I16;
            case 32: return GIR_T_I32;
            case 64: return GIR_T_I64;
            default: break;
            }
            break;
        case Type::PointerTyID:
            if (t->getPointerAddressSpace() == 0) return GIR_T_PTR;
            break;
        case Type::FloatTyID: return GIR_T_F32;
        case Type::DoubleTyID: return GIR_T_F64;
        default: break;
        }
        return ty_slow(t);
    }
    uint16_t ty_slow(Type *t) {
        if (auto *it = dyn_cast<IntegerType>(t)) {
            unsigned b = it->getBitWidth();
            switch (b) {
            case 1: return GIR_T_I1;
            case 8: return GIR_T_I8;
            case 16: return GIR_T_I16;
            case 32: return GIR_T_I32;
            case 64: return GIR_T_I64;
            case 128: return GIR_T_I128;
            default: break;
            }
            if (b > 128) fail("integer type " + tystr(t) + " wider than 128 bits");
        } else if (auto *pt = dyn_cast<PointerType>(t)) {
            if (pt->getAddressSpace() != 0) fail("pointer in address space " + std::to_string(pt->getAddressSpace()));
            return GIR_T_PTR;
        } else if (t->isFloatTy()) {
            return GIR_T_F32;
        } else if (t->isDoubleTy()) {
            return GIR_T_F64;
        } else if (t->isX86_FP80Ty()) {
            return GIR_T_F80;
        } else if (t->isHalfTy()) {
            return GIR_T_F16;
        } else if (t->isVoidTy()) {
            fail("void value");
        }
        if (uint32_t *p = tmap.find(t)) return (uint16_t)*p;
        uint16_t id;
        if (auto *itp = dyn_cast<IntegerType>(t)) {
            unsigned b = itp->getBitWidth();
            id = new_type(GirTypeDef{GIR_TK_INT, (uint8_t)(b <= 64 ? GIR_C_INT : GIR_C_INT2), (uint16_t)b,
                                     (uint32_t)DL.getTypeAllocSize(t), (uint32_t)DL.getABITypeAlign(t).value(),
                                     (uint32_t)DL.getTypeStoreSize(t), 0, 0});
        } else if (auto *vt = dyn_cast<FixedVectorType>(t)) {
            Type *et = vt->getElementType();
            uint16_t e = ty(et);
            unsigned n = vt->getNumElements();
            bool ok = (et->isIntegerTy() && (et->getIntegerBitWidth() == 1 || et->getIntegerBitWidth() == 8 ||
                                             et->getIntegerBitWidth() == 16 || et->getIntegerBitWidth() == 32 ||
                                             et->getIntegerBitWidth() == 64)) ||
                      et->isFloatTy() || et->isDoubleTy();
            if (!ok) fail("vector type " + tystr(t));
            if (et->isIntegerTy(1))
                id = new_type(GirTypeDef{GIR_TK_VECTOR, GIR_C_VEC, 0, n, 1, n, n, e});
            else
                id = new_type(GirTypeDef{GIR_TK_VECTOR, GIR_C_VEC, 0, (uint32_t)DL.getTypeAllocSize(t),
                                         (uint32_t)DL.getABITypeAlign(t).value(), (uint32_t)DL.getTypeStoreSize(t),
                                         n, e});
        } else if (auto *st = dyn_cast<StructType>(t)) {
            if (st->isOpaque()) fail("opaque struct type");
            const StructLayout *SL = DL.getStructLayout(st);
            SmallVector<uint32_t, 16> f;
            for (unsigned i = 0; i < st->getNumElements(); i++) {
                f.push_back(ty(st->getElementType(i)));
                f.push_back((uint32_t)SL->getElementOffset(i).getFixedValue());
            }
            uint32_t s = (uint32_t)T.opnds.size();
            T.opnds.insert(T.opnds.end(), f.begin(), f.end());
            id = new_type(GirTypeDef{GIR_TK_STRUCT, GIR_C_MEM, 0, (uint32_t)DL.getTypeAllocSize(t),
                                     (uint32_t)DL.getABITypeAlign(t).value(), (uint32_t)DL.getTypeStoreSize(t),
                                     st->getNumElements(), s});
        } else if (auto *at = dyn_cast<ArrayType>(t)) {
            uint16_t e = ty(at->getElementType());
            uint64_t size = DL.getTypeAllocSize(t);
            if (size > 0x7FFFFFFFull) fail("aggregate type above 2 GiB");
            id = new_type(GirTypeDef{GIR_TK_ARRAY, GIR_C_MEM, 0, (uint32_t)size, (uint32_t)DL.getABITypeAlign(t).value(),
                                     (uint32_t)DL.getTypeStoreSize(t), (uint32_t)at->getNumElements(), e});
        } else if (t->isVectorTy()) {
            fail("scalable vector type " + tystr(t));
        } else if (t->isFloatingPointTy()) {
            fail("floating-point type " + tystr(t));
        } else {
            fail("type " + tystr(t));
        }
        tmap[t] = id;
        return id;
    }
    uint16_t ret_ty(Type *t) { return t->isVoidTy() ? (uint16_t)GIR_T_VOID : ty(t); }
    uint8_t cls(uint16_t t) const { return T.types[t].cls; }
    unsigned bits(uint16_t t) const { return T.types[t].bits; }
    bool is_int(uint16_t t) const { return T.types[t].kind == GIR_TK_INT; }

    // ------------------------------------------------------------ strtab etc.
    uint32_t add_name(StringRef name) {
        if (name.contains('\0')) throw GirUnsupported{"unsupported: symbol name with a NUL byte"};
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
        g.section = GIR_NONE;
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
        uint32_t f = 0;
        if (G.hasLocalLinkage()) f |= GIR_GF_INTERNAL;
        else if (G.hasWeakLinkage() || G.hasLinkOnceLinkage() || G.hasExternalWeakLinkage()) f |= GIR_GF_WEAK;
        if (G.hasHiddenVisibility()) f |= GIR_GF_HIDDEN;
        if (G.hasProtectedVisibility()) f |= GIR_GF_PROTECTED;
        if (G.isDSOLocal() || G.hasLocalLinkage()) f |= GIR_GF_LOCALREF;
        return f;
    }
    uint32_t section(StringRef name, uint32_t flags, uint32_t type) {
        auto it = secmap.find(name);
        if (it != secmap.end()) {
            T.sections[it->second].flags |= flags;
            return it->second;
        }
        GirSection s{add_name(name), (uint32_t)name.size(), flags, type};
        T.sections.push_back(s);
        return secmap[name] = (uint32_t)T.sections.size() - 1;
    }
    // A libc/libm/compiler-rt function, as an undefined external global.
    uint32_t libfn(StringRef name) {
        auto it = libfns.find(name);
        if (it != libfns.end()) return it->second;
        uint32_t g = GIR_NONE;
        if (const Function *f = M.getFunction(name)) {
            auto gi = gmap.find(f);
            if (gi != gmap.end() && !f->hasLocalLinkage()) g = gi->second;
        }
        if (g == GIR_NONE) g = add_global(name, GIR_G_FUNC, 0, 16);
        return libfns[name] = g;
    }

    // ------------------------------------------------------------- constants
    uint32_t new_const(uint64_t lo, uint64_t hi, uint16_t t, uint32_t data = GIR_NONE) {
        if (T.consts.size() >= (1u << 30)) fail("too many constants");
        T.consts.push_back(GirConst{lo, hi, t, data});
        return GIR_MK(GIR_V_CONST, T.consts.size() - 1);
    }
    uint32_t cint(uint64_t v, uint16_t t) {
        unsigned b = bits(t);
        if (b < 64) v &= (1ull << b) - 1;
        return new_const(v, 0, t);
    }
    uint32_t cwide(const APInt &v, uint16_t t) {
        APInt z = v.zext(128);
        return new_const(z.extractBitsAsZExtValue(64, 0), z.extractBitsAsZExtValue(64, 64), t);
    }
    uint32_t czero(uint16_t t) { return new_const(0, 0, t, GIR_NONE); }
    // Writes the bytes of a constant into buf (size bytes, zeroed); false if
    // it holds an address (needs a relocation).
    bool const_bytes(const Constant *C, uint8_t *buf, uint64_t size) {
        if (isa<ConstantAggregateZero>(C) || isa<UndefValue>(C) || isa<ConstantPointerNull>(C)) return true;
        if (auto *CI = dyn_cast<ConstantInt>(C)) {
            const APInt &v = CI->getValue();
            unsigned n = (unsigned)DL.getTypeStoreSize(CI->getType());
            for (unsigned i = 0; i < n && i < size; i++)
                buf[i] = (uint8_t)v.extractBitsAsZExtValue(std::min(8u, v.getBitWidth() - i * 8), i * 8);
            return true;
        }
        if (auto *CF = dyn_cast<ConstantFP>(C)) {
            APInt v = CF->getValueAPF().bitcastToAPInt();
            unsigned n = (unsigned)DL.getTypeStoreSize(CF->getType());
            for (unsigned i = 0; i < n && i * 8 < v.getBitWidth() && i < size; i++)
                buf[i] = (uint8_t)v.extractBitsAsZExtValue(std::min(8u, v.getBitWidth() - i * 8), i * 8);
            return true;
        }
        if (auto *CDS = dyn_cast<ConstantDataSequential>(C)) {
            if (CDS->getElementType()->isIntegerTy(1)) return false;
            StringRef raw = CDS->getRawDataValues();
            std::memcpy(buf, raw.data(), std::min<uint64_t>(raw.size(), size));
            return true;
        }
        if (auto *CA = dyn_cast<ConstantArray>(C)) {
            uint64_t es = DL.getTypeAllocSize(CA->getType()->getElementType());
            for (unsigned i = 0, n = CA->getNumOperands(); i < n; i++)
                if (!const_bytes(CA->getOperand(i), buf + i * es, es)) return false;
            return true;
        }
        if (auto *CS = dyn_cast<ConstantStruct>(C)) {
            const StructLayout *SL = DL.getStructLayout(CS->getType());
            for (unsigned i = 0, n = CS->getNumOperands(); i < n; i++) {
                uint64_t eo = SL->getElementOffset(i).getFixedValue();
                if (!const_bytes(CS->getOperand(i), buf + eo, size - eo)) return false;
            }
            return true;
        }
        if (auto *CV = dyn_cast<ConstantVector>(C)) {
            Type *et = CV->getType()->getElementType();
            if (et->isIntegerTy(1)) {
                for (unsigned i = 0, n = CV->getNumOperands(); i < n; i++) {
                    const Constant *e = CV->getOperand(i);
                    if (auto *ci = dyn_cast<ConstantInt>(e)) buf[i] = (uint8_t)ci->getZExtValue();
                    else if (!isa<UndefValue>(e)) return false;
                }
                return true;
            }
            uint64_t es = DL.getTypeAllocSize(et);
            for (unsigned i = 0, n = CV->getNumOperands(); i < n; i++)
                if (!const_bytes(CV->getOperand(i), buf + i * es, es)) return false;
            return true;
        }
        return false;
    }
    // A vector or aggregate constant: bytes in data, or (with addresses) a
    // private global that is LOADed.
    uint32_t cagg(const Constant *C) {
        auto it = cmap.find(C);
        if (it != cmap.end()) return it->second;
        uint16_t t = ty(C->getType());
        uint64_t size = T.types[t].size;
        if (C->isNullValue() || isa<UndefValue>(C)) return cmap[C] = czero(t);
        std::vector<uint8_t> buf(size, 0);
        if (const_bytes(C, buf.data(), size)) {
            uint32_t at = (uint32_t)T.data.size();
            T.data.insert(T.data.end(), buf.begin(), buf.end());
            return cmap[C] = new_const(0, 0, t, at);
        }
        // Holds addresses: a private read-only global, loaded where used.
        auto gi = cglob.find(C);
        uint32_t g;
        if (gi != cglob.end()) {
            g = gi->second;
        } else {
            g = add_global("__goovm_const." + std::to_string(cglob.size()), GIR_G_VAR,
                           GIR_GF_INTERNAL | GIR_GF_DEFINED | GIR_GF_CONST | GIR_GF_LOCALREF,
                           (uint32_t)DL.getABITypeAlign(C->getType()).value());
            T.globals[g].size = (uint32_t)size;
            uint32_t at = (uint32_t)T.data.size();
            T.data.resize(at + size, 0);
            T.globals[g].data = at;
            const GlobalVariable *none = nullptr;
            init(none, g, C, at, 0);
            cglob[C] = g;
        }
        return emit(GIR_LOAD, t, 0, 0, 0, GIR_MK(GIR_V_GLOBAL, g), 0, 0, 0);
    }
    uint32_t cfp(const ConstantFP *CF) {
        auto it = cmap.find(CF);
        if (it != cmap.end()) return it->second;
        uint16_t t = ty(CF->getType());
        APInt v = CF->getValueAPF().bitcastToAPInt();
        uint64_t lo = v.extractBitsAsZExtValue(std::min(64u, v.getBitWidth()), 0);
        uint64_t hi = v.getBitWidth() > 64 ? v.extractBitsAsZExtValue(v.getBitWidth() - 64, 64) : 0;
        return cmap[CF] = new_const(lo, hi, t);
    }

    // ---------------------------------------------------------- debug info
    uint32_t dstring(StringRef s) {
        if (s.empty()) return 0;
        auto it = dstrmap.find(s);
        if (it != dstrmap.end()) return it->second;
        uint32_t off = (uint32_t)T.dstr.size();
        T.dstr.insert(T.dstr.end(), s.begin(), s.end());
        T.dstr.push_back(0);
        return dstrmap[s] = off;
    }
    uint32_t dfile(const DIFile *f) {
        if (!f) return 0;
        auto it = dfmap.find(f);
        if (it != dfmap.end()) return it->second;
        T.dfiles.push_back(GirDFile{dstring(f->getFilename()), dstring(f->getDirectory())});
        return dfmap[f] = (uint32_t)T.dfiles.size() - 1;
    }
    uint32_t dscope(const DIScope *s) {
        if (!s) return 0;
        auto it = dsmap.find(s);
        if (it != dsmap.end()) return it->second;
        GirDScope d{};
        if (auto *SP = dyn_cast<DISubprogram>(s)) {
            d.kind = GIR_DS_SUBPROGRAM;
            d.parent = dscope(SP->getUnit());
            d.file = dfile(SP->getFile());
            d.line = SP->getLine();
            d.name = dstring(SP->getName());
            d.extra = dstring(SP->getLinkageName());
        } else if (auto *LB = dyn_cast<DILexicalBlock>(s)) {
            d.kind = GIR_DS_LEXICAL;
            d.parent = dscope(LB->getScope());
            d.file = dfile(LB->getFile());
            d.line = LB->getLine();
            d.extra = LB->getColumn();
        } else if (auto *LF = dyn_cast<DILexicalBlockFile>(s)) {
            d.kind = GIR_DS_FILE;
            d.parent = dscope(LF->getScope());
            d.file = dfile(LF->getFile());
        } else if (auto *CU = dyn_cast<DICompileUnit>(s)) {
            d.kind = GIR_DS_CU;
            d.file = dfile(CU->getFile());
            d.line = CU->getSourceLanguage();
            d.name = dstring(CU->getProducer());
        } else {
            // Namespaces, modules, types as scopes: not in C; record the file.
            d.kind = GIR_DS_FILE;
            d.file = dfile(s->getFile());
        }
        T.dscopes.push_back(d);
        return dsmap[s] = (uint32_t)T.dscopes.size() - 1;
    }
    uint32_t dloc(const DILocation *l) {
        if (!l) return 0;
        if (l == last_dl) return last_dl_idx;
        auto it = dlmap.find(l);
        uint32_t idx;
        if (it != dlmap.end()) {
            idx = it->second;
        } else {
            GirDLoc d{l->getLine(), l->getColumn(), dscope(l->getScope()), dloc(l->getInlinedAt())};
            T.dlocs.push_back(d);
            idx = dlmap[l] = (uint32_t)T.dlocs.size() - 1;
        }
        last_dl = l;
        last_dl_idx = idx;
        return idx;
    }

    // ---------------------------------------------------------- instructions
    __attribute__((always_inline)) uint32_t emit(uint8_t op, uint16_t t, uint8_t sub, uint16_t flags, uint16_t aux,
                                                 uint32_t a, uint32_t b, uint32_t c, unsigned refs) {
        uint32_t idx = (uint32_t)T.insts.size();
        if (idx >= PH_BASE) fail("module too large for GIR (instruction count)");
        T.insts.push_back(GirInst{op, sub, flags, t, aux, a, b, c, cur_dbg});
        if (refs & RA) note(a, idx, 0);
        if (refs & RB) note(b, idx, 1);
        if (refs & RC) note(c, idx, 2);
        return GIR_MK(GIR_V_INST, idx);
    }
    // A placeholder is used exactly once: remember where it was stored.
    __attribute__((always_inline)) void note(uint32_t r, uint32_t where, uint32_t field) {
        if (!is_placeholder(r)) return;
        Fix &fx = fixes[GIR_IDX(r) - PH_BASE];
        fx.where = where;
        fx.field = field;
    }
    void push_ref(uint32_t r) {
        note(r, (uint32_t)T.opnds.size(), 3);
        T.opnds.push_back(r);
    }
    // A copy of a value (to turn a one-use placeholder into a real value).
    uint32_t copy(uint32_t r, uint16_t t) { return emit(GIR_BITCAST, t, 0, 0, t, r, 0, 0, RA); }
    // ref() for a value used more than once by the lowering of one LLVM
    // instruction: a placeholder is turned into a real (copied) value.
    uint32_t ref_multi(const Value *v) {
        uint32_t r = ref(v);
        if (is_placeholder(r)) r = copy(r, ty(v->getType()));
        return r;
    }
    // Record that `I` has value `r`: an identity mapping, unless `r` is a
    // one-use placeholder, in which case a copy is emitted.
    void alias(const Instruction &I, uint32_t r, uint16_t t) {
        if (is_placeholder(r)) r = copy(r, t);
        vmap[&I] = r;
    }
    uint32_t vty(uint32_t r) {
        switch (GIR_KIND(r)) {
        case GIR_V_INST: return T.insts[GIR_IDX(r)].ty;
        case GIR_V_CONST: return T.consts[GIR_IDX(r)].ty;
        case GIR_V_GLOBAL: return GIR_T_PTR;
        default: break;
        }
        return GIR_T_VOID;  // ARG: callers know the type from the LLVM value
    }

    bool is_tls(const Value *v) {
        if (auto *GV = dyn_cast<GlobalVariable>(v)) return GV->isThreadLocal();
        if (auto *GA = dyn_cast<GlobalAlias>(v)) return GA->isThreadLocal();
        return false;
    }
    // Values a PHI may use that turn into instructions.
    bool needs_mat(const Value *v) {
        if (isa<ConstantExpr>(v) || isa<BlockAddress>(v) || is_tls(v)) return true;
        if (isa<ConstantAggregate>(v) || isa<ConstantDataSequential>(v)) {
            std::vector<uint8_t> buf(DL.getTypeAllocSize(v->getType()), 0);
            return !const_bytes(cast<Constant>(v), buf.data(), buf.size());
        }
        return false;
    }

    // Value -> ref. May append instructions (materialized constants) to the
    // current block.
    __attribute__((always_inline)) uint32_t ref(const Value *v) {
        if (isa<Instruction>(v))
            if (uint32_t *p = vmap.find(v)) return *p;
        return ref_slow(v);
    }
    uint32_t ref_slow(const Value *v) {
        if (const auto *I = dyn_cast<Instruction>(v)) {
            if (uint32_t *p = vmap.find(I)) return *p;
            uint32_t k = (uint32_t)fixes.size();
            if (PH_BASE + k >= (1u << 30)) fail("too many forward references");
            fixes.push_back(Fix{I, GIR_NONE, 0});
            return GIR_MK(GIR_V_INST, PH_BASE + k);
        }
        if (const auto *A = dyn_cast<Argument>(v)) return GIR_MK(GIR_V_ARG, A->getArgNo());
        if (!in_phi_prepass && phimat.count) {
            if (uint32_t *p = phimat.find(v)) return *p;
        }
        if (const auto *CI = dyn_cast<ConstantInt>(v)) {
            uint16_t t = ty(CI->getType());
            if (cls(t) == GIR_C_INT2) return cwide(CI->getValue(), t);
            return cint(CI->getZExtValue(), t);
        }
        if (const auto *CF = dyn_cast<ConstantFP>(v)) return cfp(CF);
        if (isa<ConstantPointerNull>(v)) return cint(0, ty(v->getType()));
        if (isa<UndefValue>(v) || isa<ConstantAggregateZero>(v)) {  // undef, poison, zeroinitializer
            uint16_t t = ty(v->getType());
            if (cls(t) == GIR_C_VEC || cls(t) == GIR_C_MEM) return czero(t);
            return new_const(0, 0, t);
        }
        if (isa<ConstantAggregate>(v) || isa<ConstantDataSequential>(v)) return cagg(cast<Constant>(v));
        if (const auto *G = dyn_cast<GlobalValue>(v)) {
            auto it = gmap.find(G);
            if (it != gmap.end()) {
                if (is_tls(G)) return tls_addr(it->second);
                return GIR_MK(GIR_V_GLOBAL, it->second);
            }
            if (isa<GlobalIFunc>(G)) fail("ifunc '" + G->getName().str() + "'");
            if (const auto *Fn = dyn_cast<Function>(G); Fn && Fn->isIntrinsic())
                fail("address of intrinsic '" + G->getName().str() + "'");
            fail("reference to unexported global '" + G->getName().str() + "'");
        }
        if (const auto *CE = dyn_cast<ConstantExpr>(v)) return materialize(CE);
        if (const auto *BA = dyn_cast<BlockAddress>(v)) {
            auto it = gmap.find(BA->getFunction());
            if (it == gmap.end()) fail("blockaddress of an unexported function");
            return emit(GIR_BLOCKADDR, GIR_T_PTR, 0, 0, 0, it->second, local_block(BA->getBasicBlock()), 0, 0);
        }
        if (isa<InlineAsm>(v)) fail("inline assembly as a value");
        if (isa<DSOLocalEquivalent>(v) || isa<NoCFIValue>(v)) fail("dso_local_equivalent / no_cfi");
        if (isa<ConstantTargetNone>(v) || isa<ConstantTokenNone>(v)) fail("token or target-none constant");
        fail("operand kind");
    }
    uint32_t tls_addr(uint32_t g) {
        if (!pie && T.header.tls_get_addr == GIR_NONE) T.header.tls_get_addr = libfn("__tls_get_addr");
        return emit(GIR_TLSADDR, GIR_T_PTR, 0, 0, 0, g, 0, 0, 0);
    }
    static uint32_t local_block(const BasicBlock *BB) {
        uint32_t n = 0;
        for (const BasicBlock &B : *BB->getParent()) {
            if (&B == BB) return n;
            n++;
        }
        return GIR_NONE;
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
        case Instruction::AddrSpaceCast:
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
            uint16_t t = ty(CE->getType());
            if (t == GIR_T_PTR) fail("pointer arithmetic constant expression");
            uint32_t a = ref(CE->getOperand(0));
            uint32_t b = ref(CE->getOperand(1));
            return emit(binop(CE->getOpcode()), t, 0, 0, 0, a, b, 0, RA | RB);
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
        case Instruction::FAdd: return GIR_FADD;
        case Instruction::FSub: return GIR_FSUB;
        case Instruction::FMul: return GIR_FMUL;
        case Instruction::FDiv: return GIR_FDIV;
        default: break;
        }
        fail("binary operator");
    }

    // A call of a run-time library function with plain (non-byval) args.
    uint32_t libcall(StringRef name, uint16_t rt, std::initializer_list<uint32_t> args) {
        uint32_t g = libfn(name);
        uint32_t s = (uint32_t)T.opnds.size();
        for (uint32_t a : args) {
            push_ref(a);
            T.opnds.push_back(0);
        }
        return emit(GIR_CALL, rt, 0, 0, 0, GIR_MK(GIR_V_GLOBAL, g), s, (uint32_t)args.size(), RA);
    }
    // FP suffix for libm names: f32 "f", f64 "", f80 "l".
    std::string fsuf(uint16_t t) {
        if (t == GIR_T_F32) return "f";
        if (t == GIR_T_F64) return "";
        if (t == GIR_T_F80) return "l";
        fail("libm call on type " + std::to_string(t));
    }
    static const char *fpart(uint16_t t) { return t == GIR_T_F32 ? "sf" : t == GIR_T_F64 ? "df" : "xf"; }

    // half <-> float through the compiler-rt/libgcc helpers (LLVM -O0 on
    // x86-64 without F16C does the same).
    uint32_t half_to(uint32_t v, uint16_t dst) {
        uint32_t f = libcall("__extendhfsf2", GIR_T_F32, {v});
        if (dst == GIR_T_F32) return f;
        return emit(GIR_FPEXT, dst, 0, 0, GIR_T_F32, f, 0, 0, 0);
    }
    uint32_t to_half(uint32_t v, uint16_t src) {
        const char *fn = src == GIR_T_F32 ? "__truncsfhf2" : src == GIR_T_F64 ? "__truncdfhf2" : "__truncxfhf2";
        return libcall(fn, GIR_T_F16, {v});
    }
    // Integer of 65..127 bits widened to i128 (and back) for the i128 libcalls.
    uint32_t widen128(uint32_t v, uint16_t t, bool sgn) {
        if (t == GIR_T_I128) return v;
        return emit(sgn ? GIR_SEXT : GIR_ZEXT, GIR_T_I128, 0, 0, t, v, 0, 0, RA);
    }

    uint32_t cast_op(unsigned opc, const Value *src, Type *dstT) {
        uint16_t st = ty(src->getType()), dt = ty(dstT);
        uint8_t op;
        switch (opc) {
        case Instruction::Trunc: op = GIR_TRUNC; break;
        case Instruction::ZExt: op = GIR_ZEXT; break;
        case Instruction::SExt: op = GIR_SEXT; break;
        case Instruction::PtrToInt: op = GIR_PTRTOINT; break;
        case Instruction::IntToPtr: op = GIR_INTTOPTR; break;
        case Instruction::AddrSpaceCast:
        case Instruction::BitCast:
            if (T.types[st].store != T.types[dt].store || T.types[st].size != T.types[dt].size)
                fail("bitcast between types of different sizes");
            if ((T.types[st].kind == GIR_TK_VECTOR && bits(T.types[st].elems) == 1) ||
                (T.types[dt].kind == GIR_TK_VECTOR && bits(T.types[dt].elems) == 1))
                fail("bitcast of an i1 vector");
            op = GIR_BITCAST;
            break;
        case Instruction::FPExt: op = GIR_FPEXT; break;
        case Instruction::FPTrunc: op = GIR_FPTRUNC; break;
        case Instruction::FPToSI: op = GIR_FPTOSI; break;
        case Instruction::FPToUI: op = GIR_FPTOUI; break;
        case Instruction::SIToFP: op = GIR_SITOFP; break;
        case Instruction::UIToFP: op = GIR_UITOFP; break;
        default: fail("cast");
        }
        uint32_t a = ref(src);
        bool vec = T.types[dt].kind == GIR_TK_VECTOR;
        // half: through float with the helper functions.
        if (!vec && (st == GIR_T_F16 || dt == GIR_T_F16) && op != GIR_BITCAST) {
            if (op == GIR_FPEXT) return half_to(a, dt);
            if (op == GIR_FPTRUNC) return to_half(a, st);
            if (st == GIR_T_F16) {  // half -> int
                uint32_t f = half_to(a, GIR_T_F32);
                return cast_int_fp(op, f, GIR_T_F32, dt);
            }
            // int -> half
            uint32_t f = cast_int_fp(op, a, st, GIR_T_F32);
            return to_half(f, GIR_T_F32);
        }
        if (!vec && (op == GIR_FPTOSI || op == GIR_FPTOUI || op == GIR_SITOFP || op == GIR_UITOFP))
            return cast_int_fp(op, a, st, dt);
        return emit(op, dt, 0, 0, st, a, 0, 0, RA);
    }
    // Scalar conversions between integers and floating point; i128 ones are
    // library calls.
    uint32_t cast_int_fp(uint8_t op, uint32_t a, uint16_t st, uint16_t dt) {
        if (op == GIR_FPTOSI || op == GIR_FPTOUI) {
            if (cls(dt) == GIR_C_INT2) {
                std::string fn = std::string(op == GIR_FPTOSI ? "__fix" : "__fixuns") + fpart(st) + "ti";
                uint32_t r = libcall(fn, GIR_T_I128, {a});
                if (dt != GIR_T_I128) r = emit(GIR_TRUNC, dt, 0, 0, GIR_T_I128, r, 0, 0, 0);
                return r;
            }
            return emit(op, dt, 0, 0, st, a, 0, 0, RA);
        }
        if (cls(st) == GIR_C_INT2) {
            uint32_t w = widen128(a, st, op == GIR_SITOFP);
            std::string fn = std::string(op == GIR_SITOFP ? "__floatti" : "__floatunti") + fpart(dt);
            return libcall(fn, dt, {w});
        }
        return emit(op, dt, 0, 0, st, a, 0, 0, RA);
    }

    // GEP (instruction or constant expression): constant indices fold into
    // one byte offset, the others become (index, scale) pairs.
    // Alloc sizes and struct layouts, cached per type (DataLayout looks them
    // up in a hash map on every call).
    PtrMap asz_map, lay_map;
    std::vector<const StructLayout *> lays;
    uint64_t alloc_size(Type *t) {
        if (uint32_t *p = asz_map.find(t)) return *p;
        TypeSize ts = DL.getTypeAllocSize(t);
        if (ts.isScalable()) fail("scalable GEP");
        uint64_t v = ts.getFixedValue();
        if (v <= 0xFFFFFFFFull) asz_map[t] = (uint32_t)v;
        return v;
    }
    const StructLayout *layout(StructType *st) {
        if (uint32_t *p = lay_map.find(st)) return lays[*p];
        const StructLayout *L = DL.getStructLayout(st);
        lay_map[st] = (uint32_t)lays.size();
        lays.push_back(L);
        return L;
    }

    uint32_t gep(const GEPOperator *G) {
        if (G->getType()->isVectorTy()) fail("vector GEP");
        uint32_t base = ref(G->getPointerOperand());
        uint64_t off = 0;
        SmallVector<uint32_t, 8> dyn;
        // (the walk of gep_type_iterator: index 0 steps over the source
        // element type, later ones into structs, arrays and vectors)
        Type *cur = G->getSourceElementType();
        unsigned n = G->getNumIndices();
        for (unsigned i = 0; i < n; i++) {
            const Value *idx = G->getOperand(i + 1);
            uint64_t stride;
            if (i == 0) {
                stride = alloc_size(cur);
            } else if (StructType *ST = dyn_cast<StructType>(cur)) {
                unsigned fi = (unsigned)cast<ConstantInt>(idx)->getZExtValue();
                off += layout(ST)->getElementOffset(fi).getFixedValue();
                cur = ST->getElementType(fi);
                continue;
            } else if (auto *VT = dyn_cast<VectorType>(cur)) {
                cur = VT->getElementType();
                TypeSize ts = DL.getTypeStoreSize(cur);
                if (ts.isScalable() || isa<ScalableVectorType>(VT)) fail("scalable GEP");
                stride = ts.getFixedValue();
            } else {
                cur = cur->getArrayElementType();
                stride = alloc_size(cur);
            }
            if (const auto *CI = dyn_cast<ConstantInt>(idx)) {
                if (CI->getBitWidth() > 64) fail("GEP index wider than 64 bits");
                off += (uint64_t)CI->getSExtValue() * stride;
                continue;
            }
            if (isa<UndefValue>(idx) || stride == 0) continue;
            if (idx->getType()->isVectorTy()) fail("vector GEP index");
            if (stride > 0xFFFFFFFFull) fail("GEP stride above 4 GiB");
            uint16_t it = ty(idx->getType());
            if (cls(it) != GIR_C_INT) fail("GEP index wider than 64 bits");
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
        return emit(GIR_GEP, GIR_T_PTR, 0, 0, 0, base, s, (uint32_t)(dyn.size() / 2), RA);
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

    // ---------------------------------------------------------------- ABI
    // Whether LLVM's x86-64 C convention returns a value of this type in
    // registers (RAX/RDX/RCX, XMM0/XMM1 for scalars, XMM0-3 for vectors,
    // ST0/ST1); otherwise it would demote to sret, which clang never needs.
    bool returnable(uint16_t t, unsigned &ngp, unsigned &nfp, unsigned &nvec, unsigned &nx87) {
        const GirTypeDef &d = T.types[t];
        switch (d.cls) {
        case GIR_C_NONE: return true;
        case GIR_C_INT: ngp++; return true;
        case GIR_C_INT2: ngp += 2; return true;
        case GIR_C_FP: nfp++; return true;
        case GIR_C_X87: nx87++; return true;
        case GIR_C_VEC:
            if (d.n == 1) return returnable(d.elems, ngp, nfp, nvec, nx87);
            nvec += d.store <= 16 ? 1 : (d.store + 15) / 16;
            return true;
        default: break;
        }
        if (d.kind == GIR_TK_STRUCT) {
            for (uint32_t i = 0; i < d.n; i++)
                if (!returnable((uint16_t)T.opnds[d.elems + 2 * i], ngp, nfp, nvec, nx87)) return false;
            return true;
        }
        for (uint32_t i = 0; i < d.n; i++)
            if (!returnable((uint16_t)d.elems, ngp, nfp, nvec, nx87)) return false;
        return true;
    }
    std::vector<uint8_t> ret_ok;  // per type id: checked as a return type
    uint16_t check_ret(Type *rt) {
        uint16_t t = ret_ty(rt);
        if (t < ret_ok.size() && ret_ok[t]) return t;
        if (ret_ok.size() <= t) ret_ok.resize(t + 1, 0);
        ret_ok[t] = 1;
        unsigned g = 0, f = 0, v = 0, x = 0;
        if (!returnable(t, g, f, v, x) || g > 3 || f > 2 || f + v > 4 || x > 2)
            fail("return type " + tystr(rt) + " that does not fit the return registers");
        if (T.types[t].kind == GIR_TK_VECTOR && bits(T.types[t].elems) == 1) fail("i1 vector return");
        return t;
    }
    // Facts about a (uniqued) attribute list of a call site or a function.
    enum : uint32_t { AL_DONE = 1, AL_SPECIAL = 2, AL_SEXT = 4, AL_RT = 8, AL_NR = 16 };
    PtrMap alinfo;
    uint32_t alist_bits(const AttributeList &L) {
        const void *k = L.getRawPointer();
        if (!k) return AL_DONE;
        if (uint32_t *p = alinfo.find(k)) return *p;
        uint32_t x = AL_DONE;
        for (auto kind : {Attribute::ByVal, Attribute::StructRet, Attribute::InAlloca, Attribute::Preallocated,
                          Attribute::ByRef})
            if (L.hasAttrSomewhere(kind)) x |= AL_SPECIAL;
        if (L.hasAttrSomewhere(Attribute::SExt)) x |= AL_SEXT;
        if (L.hasFnAttr(Attribute::ReturnsTwice)) x |= AL_RT;
        if (L.hasFnAttr(Attribute::NoReturn)) x |= AL_NR;
        alinfo[k] = x;
        return x;
    }
    // The ABI word of a parameter without special attributes.
    uint32_t abi_plain(uint16_t gt, const char *what) {
        uint8_t c = cls(gt);
        if (c == GIR_C_MEM) fail(std::string("aggregate passed by value as ") + what);
        if (c == GIR_C_VEC && bits(T.types[gt].elems) == 1) fail(std::string("i1 vector ") + what);
        return 0;
    }
    uint32_t abi_word(AttributeSet as, Type *t, const char *what) {
        if (!as.hasAttributes()) {
            uint16_t gt = ty(t);
            uint8_t c = cls(gt);
            if (c == GIR_C_MEM) fail(std::string("aggregate passed by value as ") + what);
            if (c == GIR_C_VEC && bits(T.types[gt].elems) == 1) fail(std::string("i1 vector ") + what);
            return 0;
        }
        if (as.hasAttribute(Attribute::InAlloca) || as.hasAttribute(Attribute::Preallocated))
            fail(std::string("inalloca/preallocated ") + what);
        if (as.hasAttribute(Attribute::ByVal)) {
            Type *bt = as.getByValType();
            uint64_t size = DL.getTypeAllocSize(bt);
            uint64_t al = as.getStackAlignment() ? as.getStackAlignment()->value()
                          : as.getAlignment()   ? as.getAlignment()->value()
                                                : DL.getABITypeAlign(bt).value();
            if (size >= (1u << 24)) fail(std::string("byval ") + what + " of 16 MiB or more");
            return GIR_ABI_BYVAL | (uint32_t)size | ((uint32_t)Log2_64(al) << 24);
        }
        if (as.hasAttribute(Attribute::ByRef)) fail(std::string("byref ") + what);
        uint16_t gt = ty(t);
        uint8_t c = cls(gt);
        if (c == GIR_C_MEM) fail(std::string("aggregate passed by value as ") + what);
        if (c == GIR_C_VEC && bits(T.types[gt].elems) == 1) fail(std::string("i1 vector ") + what);
        if (as.hasAttribute(Attribute::StructRet)) return GIR_ABI_SRET;
        return 0;
    }

    // ---------------------------------------------------------------- calls
    // Argument for a call: `signext` narrower than 32 bits gets an explicit
    // SEXT to i32 (the SysV caller-extends rule as clang implements it).
    void call_arg(const CallBase &CB, unsigned i, uint32_t al, uint32_t &r, uint32_t &w) {
        const Value *v = CB.getArgOperand(i);
        uint16_t t = ty(v->getType());
        w = al & AL_SPECIAL ? abi_word(CB.getParamAttributes(i), v->getType(), "argument") : abi_plain(t, "argument");
        r = ref(v);
        if ((al & AL_SEXT) && is_int(t) && bits(t) < 32 && CB.paramHasAttr(i, Attribute::SExt))
            r = emit(GIR_SEXT, GIR_T_I32, 0, 0, t, r, 0, 0, RA);
    }

    void emit_call(const CallBase &CB, uint32_t callee, uint16_t rt, bool vararg) {
        uint32_t al = alist_bits(CB.getAttributes());
        if (const Function *Fn = CB.getCalledFunction()) al |= alist_bits(Fn->getAttributes());
        if (al & AL_RT) fn_flags |= GIR_FN_RETURNS_TWICE;  // setjmp, vfork, ...
        SmallVector<uint32_t, 32> args;
        for (unsigned i = 0, n = CB.arg_size(); i < n; i++) {
            uint32_t r, w;
            call_arg(CB, i, al, r, w);
            args.push_back(r);
            args.push_back(w);
        }
        uint32_t s = (uint32_t)T.opnds.size();
        for (size_t i = 0; i < args.size(); i += 2) {
            push_ref(args[i]);
            T.opnds.push_back(args[i + 1]);
        }
        uint16_t fl = (vararg ? GIR_IF_VARARG : 0) | (al & AL_NR ? GIR_IF_NORETURN : 0);
        uint32_t r = emit(GIR_CALL, rt, 0, fl, 0, callee, s, (uint32_t)(args.size() / 2), RA);
        if (rt != GIR_T_VOID) vmap[&CB] = r;
    }

    // select(icmp pred a, b; x; y)
    uint32_t cmp_select(uint8_t p, uint32_t a, uint32_t b, uint32_t x, uint32_t y, uint16_t t) {
        uint16_t ct = GIR_T_I1;
        if (T.types[t].kind == GIR_TK_VECTOR) ct = ty(FixedVectorType::get(Type::getInt1Ty(M.getContext()), T.types[t].n));
        uint32_t c = emit(GIR_ICMP, ct, p, 0, t, a, b, 0, RA | RB);
        return emit(GIR_SELECT, t, 0, 0, 0, c, x, y, RA | RB | RC);
    }

    void mem_intrinsic(const CallBase &CB, Intrinsic::ID id) {
        const Value *len = CB.getArgOperand(2);
        const auto *CL = dyn_cast<ConstantInt>(len);
        uint32_t a0 = ref(CB.getArgOperand(0));
        uint32_t a1 = ref(CB.getArgOperand(1));
        bool vol = id != Intrinsic::memmove && cast<ConstantInt>(CB.getArgOperand(3))->isOne();
        if (CL && CL->getZExtValue() <= MAX_INLINE_MEM && id != Intrinsic::memmove) {
            uint8_t op = (id == Intrinsic::memset || id == Intrinsic::memset_inline) ? GIR_MEMSET : GIR_MEMCPY;
            if (CL->getZExtValue() == 0) return;
            emit(op, GIR_T_VOID, 0, vol ? GIR_IF_VOLATILE : 0, 0, a0, a1, (uint32_t)CL->getZExtValue(), RA | RB);
            return;
        }
        uint16_t lt = ty(len->getType());
        if (lt != GIR_T_I64) fail("memory intrinsic with a non-i64 length");
        uint32_t a2 = ref(len);
        const char *fn = id == Intrinsic::memmove ? "memmove"
                         : (id == Intrinsic::memset || id == Intrinsic::memset_inline) ? "memset"
                                                                                         : "memcpy";
        libcall(fn, GIR_T_VOID, {a0, a1, a2});
    }

    // llvm.<math>.<type> -> libm, by name.
    bool libm_intrinsic(const CallBase &CB, Intrinsic::ID id) {
        const char *base = nullptr;
        switch (id) {
        case Intrinsic::floor: base = "floor"; break;
        case Intrinsic::ceil: base = "ceil"; break;
        case Intrinsic::trunc: base = "trunc"; break;
        case Intrinsic::round: base = "round"; break;
        case Intrinsic::roundeven: base = "roundeven"; break;
        case Intrinsic::rint: base = "rint"; break;
        case Intrinsic::nearbyint: base = "nearbyint"; break;
        case Intrinsic::pow: base = "pow"; break;
        case Intrinsic::exp: base = "exp"; break;
        case Intrinsic::exp2: base = "exp2"; break;
        case Intrinsic::exp10: base = "exp10"; break;
        case Intrinsic::log: base = "log"; break;
        case Intrinsic::log2: base = "log2"; break;
        case Intrinsic::log10: base = "log10"; break;
        case Intrinsic::sin: base = "sin"; break;
        case Intrinsic::cos: base = "cos"; break;
        case Intrinsic::tan: base = "tan"; break;
        case Intrinsic::asin: base = "asin"; break;
        case Intrinsic::acos: base = "acos"; break;
        case Intrinsic::atan: base = "atan"; break;
        case Intrinsic::atan2: base = "atan2"; break;
        case Intrinsic::sinh: base = "sinh"; break;
        case Intrinsic::cosh: base = "cosh"; break;
        case Intrinsic::tanh: base = "tanh"; break;
        case Intrinsic::fma: base = "fma"; break;
        case Intrinsic::minnum: base = "fmin"; break;
        case Intrinsic::maxnum: base = "fmax"; break;
        case Intrinsic::ldexp: base = "ldexp"; break;
        case Intrinsic::lround: base = "lround"; break;
        case Intrinsic::llround: base = "llround"; break;
        case Intrinsic::lrint: base = "lrint"; break;
        case Intrinsic::llrint: base = "llrint"; break;
        default: return false;
        }
        Type *ft = CB.getArgOperand(0)->getType();
        uint16_t t = ty(ft);
        if (T.types[t].kind == GIR_TK_VECTOR) fail("vector math intrinsic");
        uint16_t rt = ty(CB.getType());
        SmallVector<uint32_t, 4> args;
        for (unsigned i = 0; i < CB.arg_size(); i++) args.push_back(ref(CB.getArgOperand(i)));
        bool half = t == GIR_T_F16;
        if (half) {
            for (unsigned i = 0; i < args.size(); i++)
                if (ty(CB.getArgOperand(i)->getType()) == GIR_T_F16) args[i] = half_to(args[i], GIR_T_F32);
            t = GIR_T_F32;
        }
        std::string fn = std::string(base) + fsuf(t);
        uint32_t g = libfn(fn);
        uint32_t s = (uint32_t)T.opnds.size();
        for (uint32_t a : args) {
            push_ref(a);
            T.opnds.push_back(0);
        }
        uint16_t crt = rt == GIR_T_F16 ? (uint16_t)GIR_T_F32 : rt;
        uint32_t r = emit(GIR_CALL, crt, 0, 0, 0, GIR_MK(GIR_V_GLOBAL, g), s, (uint32_t)args.size(), RA);
        if (rt == GIR_T_F16) r = to_half(r, GIR_T_F32);
        vmap[&CB] = r;
        return true;
    }

    void intrinsic(const CallBase &CB, Intrinsic::ID id) {
        // Calls with constant arguments fold, as LLVM's code generator folds
        // them (a test may rely on floor(2.5) needing no libm).
        if (const Function *fn = CB.getCalledFunction(); fn && !CB.getType()->isVoidTy() && canConstantFoldCallTo(&CB, fn)) {
            SmallVector<Constant *, 4> cargs;
            for (const Use &u : CB.args())
                if (auto *c = dyn_cast<Constant>(u.get())) cargs.push_back(c);
            if (cargs.size() == CB.arg_size())
                if (Constant *c = ConstantFoldCall(&CB, const_cast<Function *>(fn), cargs, &TLI)) {
                    vmap[&CB] = ref(c);
                    return;
                }
        }
        if (libm_intrinsic(CB, id)) return;
        switch (id) {
        case Intrinsic::memcpy:
        case Intrinsic::memcpy_inline:
        case Intrinsic::memmove:
        case Intrinsic::memset:
        case Intrinsic::memset_inline:
            return mem_intrinsic(CB, id);
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
        case Intrinsic::prefetch:
        case Intrinsic::vaend:
        case Intrinsic::clear_cache:
            return;
        case Intrinsic::invariant_start:
            vmap[&CB] = cint(0, GIR_T_PTR);
            return;
        case Intrinsic::expect:
        case Intrinsic::expect_with_probability:
        case Intrinsic::ptr_annotation:
        case Intrinsic::annotation:
        case Intrinsic::launder_invariant_group:
        case Intrinsic::strip_invariant_group:
        case Intrinsic::threadlocal_address: {
            uint16_t t = ty(CB.getType());
            alias(CB, ref(CB.getArgOperand(0)), t);
            return;
        }
        case Intrinsic::trap:
        case Intrinsic::ubsantrap:
            emit(GIR_TRAP, GIR_T_VOID, 0, 0, 0, 0, 0, 0, 0);
            return;
        case Intrinsic::debugtrap:
            emit(GIR_DEBUGTRAP, GIR_T_VOID, 0, 0, 0, 0, 0, 0, 0);
            return;
        case Intrinsic::abs: {
            uint16_t t = ty(CB.getType());
            uint32_t x = ref_multi(CB.getArgOperand(0));
            uint32_t neg = emit(GIR_SUB, t, 0, 0, 0, T.types[t].kind == GIR_TK_VECTOR ? czero(t) : cint(0, t), x, 0, RB);
            vmap[&CB] = cmp_select(GIR_SLT, x, T.types[t].kind == GIR_TK_VECTOR ? czero(t) : cint(0, t), neg, x, t);
            return;
        }
        case Intrinsic::smax:
        case Intrinsic::smin:
        case Intrinsic::umax:
        case Intrinsic::umin: {
            uint16_t t = ty(CB.getType());
            uint8_t p = id == Intrinsic::smax ? GIR_SGT : id == Intrinsic::smin ? GIR_SLT
                      : id == Intrinsic::umax ? GIR_UGT : GIR_ULT;
            uint32_t a = ref_multi(CB.getArgOperand(0));
            uint32_t b = ref_multi(CB.getArgOperand(1));
            vmap[&CB] = cmp_select(p, a, b, a, b, t);
            return;
        }
        case Intrinsic::ctlz:
        case Intrinsic::cttz: {
            uint16_t t = ty(CB.getType());
            if (cls(t) != GIR_C_INT) fail("ctlz/cttz on a vector or a wide integer");
            uint32_t a = ref(CB.getArgOperand(0));
            uint32_t zp = cast<ConstantInt>(CB.getArgOperand(1))->isOne() ? 1 : 0;
            vmap[&CB] = emit(id == Intrinsic::ctlz ? GIR_CTLZ : GIR_CTTZ, t, 0, 0, t, a, zp, 0, RA);
            return;
        }
        case Intrinsic::ctpop:
        case Intrinsic::bswap:
        case Intrinsic::bitreverse: {
            uint16_t t = ty(CB.getType());
            if (cls(t) != GIR_C_INT) fail("bit-manipulation intrinsic on a vector or a wide integer");
            uint32_t a = ref(CB.getArgOperand(0));
            uint8_t op = id == Intrinsic::ctpop ? GIR_CTPOP : id == Intrinsic::bswap ? GIR_BSWAP : GIR_BITREVERSE;
            vmap[&CB] = emit(op, t, 0, 0, t, a, 0, 0, RA);
            return;
        }
        case Intrinsic::fshl:
        case Intrinsic::fshr: {
            uint16_t t = ty(CB.getType());
            if (cls(t) != GIR_C_INT) fail("funnel shift on a vector or a wide integer");
            uint32_t a = ref(CB.getArgOperand(0));
            uint32_t b = ref(CB.getArgOperand(1));
            uint32_t c = ref(CB.getArgOperand(2));
            vmap[&CB] = emit(id == Intrinsic::fshl ? GIR_FSHL : GIR_FSHR, t, 0, 0, t, a, b, c, RA | RB | RC);
            return;
        }
        case Intrinsic::sadd_with_overflow:
        case Intrinsic::uadd_with_overflow:
        case Intrinsic::ssub_with_overflow:
        case Intrinsic::usub_with_overflow:
        case Intrinsic::smul_with_overflow:
        case Intrinsic::umul_with_overflow: {
            uint16_t vt = ty(CB.getArgOperand(0)->getType());
            if (cls(vt) != GIR_C_INT) fail("overflow intrinsic on a vector or a wide integer");
            uint16_t t = ty(CB.getType());
            uint8_t k = id == Intrinsic::sadd_with_overflow   ? GIR_OVF_SADD
                        : id == Intrinsic::uadd_with_overflow ? GIR_OVF_UADD
                        : id == Intrinsic::ssub_with_overflow ? GIR_OVF_SSUB
                        : id == Intrinsic::usub_with_overflow ? GIR_OVF_USUB
                        : id == Intrinsic::smul_with_overflow ? GIR_OVF_SMUL
                                                              : GIR_OVF_UMUL;
            uint32_t a = ref(CB.getArgOperand(0));
            uint32_t b = ref(CB.getArgOperand(1));
            vmap[&CB] = emit(GIR_OVF, t, k, 0, vt, a, b, 0, RA | RB);
            return;
        }
        case Intrinsic::scmp:
        case Intrinsic::ucmp: {
            uint16_t at = ty(CB.getArgOperand(0)->getType());
            uint16_t t = ty(CB.getType());
            if (cls(at) != GIR_C_INT || cls(t) != GIR_C_INT) fail("scmp/ucmp on a vector or a wide integer");
            uint32_t a = ref(CB.getArgOperand(0));
            uint32_t b = ref(CB.getArgOperand(1));
            vmap[&CB] = emit(id == Intrinsic::scmp ? GIR_SCMP : GIR_UCMP, t, 0, 0, at, a, b, 0, RA | RB);
            return;
        }
        case Intrinsic::fabs:
        case Intrinsic::sqrt:
        case Intrinsic::copysign: {
            uint16_t t = ty(CB.getType());
            uint32_t a = ref(CB.getArgOperand(0));
            if (t == GIR_T_F16) fail("half fabs/sqrt/copysign");
            if (id == Intrinsic::copysign) {
                uint32_t b = ref(CB.getArgOperand(1));
                vmap[&CB] = emit(GIR_COPYSIGN, t, 0, 0, t, a, b, 0, RA | RB);
            } else {
                vmap[&CB] = emit(id == Intrinsic::fabs ? GIR_FABS : GIR_FSQRT, t, 0, 0, t, a, 0, 0, RA);
            }
            return;
        }
        case Intrinsic::fmuladd: {
            // No FMA in the x86-64 baseline: LLVM -O0 computes a * b + c with two roundings.
            uint16_t t = ty(CB.getType());
            if (t == GIR_T_F16) fail("half fmuladd");
            uint32_t a = ref(CB.getArgOperand(0));
            uint32_t b = ref(CB.getArgOperand(1));
            uint32_t m = emit(GIR_FMUL, t, 0, 0, 0, a, b, 0, RA | RB);
            uint32_t c = ref(CB.getArgOperand(2));
            vmap[&CB] = emit(GIR_FADD, t, 0, 0, 0, m, c, 0, RB);
            return;
        }
        case Intrinsic::powi: {
            uint16_t t = ty(CB.getType());
            if (t == GIR_T_F16 || T.types[t].kind == GIR_TK_VECTOR) fail("powi on this type");
            uint32_t a = ref(CB.getArgOperand(0));
            uint32_t b = ref(CB.getArgOperand(1));
            vmap[&CB] = libcall(std::string("__powi") + fpart(t) + "2", t, {a, b});
            return;
        }
        case Intrinsic::is_fpclass: {
            uint16_t at = ty(CB.getArgOperand(0)->getType());
            if (cls(at) != GIR_C_FP && cls(at) != GIR_C_X87) fail("is.fpclass on a vector");
            uint32_t a = ref(CB.getArgOperand(0));
            if (at == GIR_T_F16) {
                a = half_to(a, GIR_T_F32);  // exact: every half is a float of the same class
                at = GIR_T_F32;
            }
            uint32_t mask = (uint32_t)cast<ConstantInt>(CB.getArgOperand(1))->getZExtValue();
            vmap[&CB] = emit(GIR_ISFPCLASS, GIR_T_I1, 0, 0, at, a, mask, 0, RA);
            return;
        }
        case Intrinsic::objectsize: {
            // As LLVM's LowerConstantIntrinsics does for the -O0 pipeline.
            Value *v = lowerObjectSizeCall(const_cast<IntrinsicInst *>(cast<IntrinsicInst>(&CB)), DL, &TLI, true);
            auto *ci = dyn_cast_or_null<ConstantInt>(v);
            if (!ci) fail("dynamic llvm.objectsize");
            vmap[&CB] = cint(ci->getZExtValue(), ty(CB.getType()));
            return;
        }
        case Intrinsic::is_constant:
            vmap[&CB] = cint(isa<Constant>(CB.getArgOperand(0)) ? 1 : 0, GIR_T_I1);
            return;
        case Intrinsic::ptrmask: {
            uint16_t mt = ty(CB.getArgOperand(1)->getType());
            if (mt != GIR_T_I64) fail("ptrmask with a mask narrower than 64 bits");
            uint32_t p = ref(CB.getArgOperand(0));
            uint32_t i = emit(GIR_PTRTOINT, GIR_T_I64, 0, 0, GIR_T_PTR, p, 0, 0, RA);
            uint32_t m = ref(CB.getArgOperand(1));
            uint32_t r = emit(GIR_AND, GIR_T_I64, 0, 0, 0, i, m, 0, RB);
            vmap[&CB] = emit(GIR_INTTOPTR, GIR_T_PTR, 0, 0, GIR_T_I64, r, 0, 0, 0);
            return;
        }
        case Intrinsic::frameaddress:
        case Intrinsic::returnaddress: {
            uint32_t lvl = (uint32_t)cast<ConstantInt>(CB.getArgOperand(0))->getZExtValue();
            vmap[&CB] = emit(id == Intrinsic::frameaddress ? GIR_FRAMEADDR : GIR_RETADDR, GIR_T_PTR, 0, 0, 0, lvl, 0, 0, 0);
            return;
        }
        case Intrinsic::eh_sjlj_setjmp: {
            fn_flags |= GIR_FN_SJLJ;
            uint32_t b = ref(CB.getArgOperand(0));
            vmap[&CB] = emit(GIR_SJLJ_SETJMP, GIR_T_I32, 0, 0, 0, b, 0, 0, RA);
            return;
        }
        case Intrinsic::eh_sjlj_longjmp: {
            uint32_t b = ref(CB.getArgOperand(0));
            emit(GIR_SJLJ_LONGJMP, GIR_T_VOID, 0, 0, 0, b, 0, 0, RA);
            return;
        }
        case Intrinsic::stacksave:
            vmap[&CB] = emit(GIR_STACKSAVE, GIR_T_PTR, 0, 0, 0, 0, 0, 0, 0);
            return;
        case Intrinsic::stackrestore: {
            uint32_t p = ref(CB.getArgOperand(0));
            emit(GIR_STACKRESTORE, GIR_T_VOID, 0, 0, 0, p, 0, 0, RA);
            return;
        }
        case Intrinsic::vastart: {
            fn_flags |= GIR_FN_VASTART;
            uint32_t p = ref(CB.getArgOperand(0));
            emit(GIR_VASTART, GIR_T_VOID, 0, 0, 0, p, 0, 0, RA);
            return;
        }
        case Intrinsic::vacopy: {
            uint32_t d = ref(CB.getArgOperand(0));
            uint32_t s = ref(CB.getArgOperand(1));
            emit(GIR_MEMCPY, GIR_T_VOID, 0, 0, 0, d, s, 24, RA | RB);
            return;
        }
        case Intrinsic::x86_sse_max_ps:
        case Intrinsic::x86_sse_min_ps:
        case Intrinsic::x86_sse_movmsk_ps:
        case Intrinsic::x86_sse2_packssdw_128:
        case Intrinsic::x86_sse2_pslli_w:
        case Intrinsic::x86_sse2_psrli_w:
        case Intrinsic::x86_sse2_psrai_w:
        case Intrinsic::x86_sse2_pslli_d:
        case Intrinsic::x86_sse2_psrli_d:
        case Intrinsic::x86_sse2_psrai_d: {
            uint8_t k = id == Intrinsic::x86_sse_max_ps          ? GIR_X86_MAXPS
                        : id == Intrinsic::x86_sse_min_ps        ? GIR_X86_MINPS
                        : id == Intrinsic::x86_sse_movmsk_ps     ? GIR_X86_MOVMSKPS
                        : id == Intrinsic::x86_sse2_packssdw_128 ? GIR_X86_PACKSSDW
                        : id == Intrinsic::x86_sse2_pslli_w      ? GIR_X86_PSLLIW
                        : id == Intrinsic::x86_sse2_psrli_w      ? GIR_X86_PSRLIW
                        : id == Intrinsic::x86_sse2_psrai_w      ? GIR_X86_PSRAIW
                        : id == Intrinsic::x86_sse2_pslli_d      ? GIR_X86_PSLLID
                        : id == Intrinsic::x86_sse2_psrli_d      ? GIR_X86_PSRLID
                                                                 : GIR_X86_PSRAID;
            uint16_t t = ty(CB.getType());
            uint16_t at = ty(CB.getArgOperand(0)->getType());
            uint32_t a = ref(CB.getArgOperand(0));
            uint32_t b = CB.arg_size() > 1 ? ref(CB.getArgOperand(1)) : 0;
            vmap[&CB] = emit(GIR_X86, t, k, 0, at, a, b, 0, CB.arg_size() > 1 ? RA | RB : RA);
            return;
        }
        default: break;
        }
        fail("intrinsic '" + CB.getCalledFunction()->getName().str() + "'");
    }

    // ---------------------------------------------------------- inline asm
    // Register names (x86 numbering) by operand size, AT&T syntax.
    static const char *gpr_name(unsigned r, unsigned size) {
        static const char *n8[] = {"al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil",
                                   "r8b", "r9b", "r10b", "r11b", "r12b", "r13b", "r14b", "r15b"};
        static const char *n16[] = {"ax", "cx", "dx", "bx", "sp", "bp", "si", "di",
                                    "r8w", "r9w", "r10w", "r11w", "r12w", "r13w", "r14w", "r15w"};
        static const char *n32[] = {"eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi",
                                    "r8d", "r9d", "r10d", "r11d", "r12d", "r13d", "r14d", "r15d"};
        static const char *n64[] = {"rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
                                    "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"};
        r &= 15;
        return size == 1 ? n8[r] : size == 2 ? n16[r] : size == 4 ? n32[r] : n64[r];
    }
    // "{ax}" -> register number (GIR_ASMREG_* numbering), or -1.
    static int fixed_reg(StringRef c) {
        if (!c.starts_with("{") || !c.ends_with("}")) return -1;
        StringRef n = c.drop_front().drop_back();
        static const char *g[] = {"ax", "cx", "dx", "bx", "sp", "bp", "si", "di"};
        for (int i = 0; i < 8; i++) {
            if (n == g[i] || n == std::string("e") + g[i] || n == std::string("r") + g[i]) return i;
        }
        if (n == "al" || n == "ah") return 0;
        if (n == "cl") return 1;
        if (n == "dl") return 2;
        if (n == "bl") return 3;
        if (n.consume_front("r")) {
            unsigned k;
            if (!n.consumeInteger(10, k) && k >= 8 && k < 16 && (n.empty() || n == "d" || n == "w" || n == "b")) return (int)k;
            return -1;
        }
        if (n.consume_front("xmm")) {
            unsigned k;
            if (!n.getAsInteger(10, k) && k < 16) return GIR_ASMREG_XMM0 + k;
            return -1;
        }
        if (n == "st") return GIR_ASMREG_ST0;
        if (n.consume_front("st(") && n.consume_back(")")) {
            unsigned k;
            if (!n.getAsInteger(10, k) && k < 8) return GIR_ASMREG_ST0 + k;
        }
        return -1;
    }
    // Inline assembly with a non-empty template: bind every operand to a
    // register (fixed ones as given, "r"/"x" from the caller-saved pool, "m"
    // as (%reg) holding the address, constant "i" as $imm), substitute them
    // into the template and assemble it with LLVM's MC layer.
    void asm_code(const CallBase &CB) {
        const auto *IA = cast<InlineAsm>(CB.getCalledOperand());
        if (IA->getDialect() != InlineAsm::AD_ATT) fail("Intel-syntax inline assembly");
        InlineAsm::ConstraintInfoVector cons = IA->ParseConstraints();
        struct Op { int kind; int reg; unsigned size; uint64_t imm; const Value *v; };  // kind: 0 reg, 1 mem, 2 imm
        enum { K_REG = 0, K_MEM = 1, K_IMM = 2 };
        std::vector<Op> ops;          // template operand number -> binding
        std::vector<int> op_of_con(cons.size(), -1);
        uint32_t used = 0;            // registers taken (bit r; xmm 16+k; st 32.. not tracked)
        uint64_t used_x = 0;
        // Clobbers.
        unsigned st_clobbered = 0;
        for (const auto &c : cons) {
            if (c.Type != InlineAsm::isClobber) continue;
            for (const std::string &code : c.Codes) {
                int r = fixed_reg(code);
                if (r >= (int)GIR_ASMREG_ST0) st_clobbered |= 1u << (r - GIR_ASMREG_ST0);
                else if (r >= (int)GIR_ASMREG_XMM0) used_x |= 1ull << (r - GIR_ASMREG_XMM0);
                else if (r >= 0) used |= 1u << r;
            }
        }
        // Fixed registers first, so the pool avoids them.
        for (const auto &c : cons)
            if (c.Type != InlineAsm::isClobber && c.Codes.size() == 1) {
                int r = fixed_reg(c.Codes[0]);
                if (r >= 0 && r < (int)GIR_ASMREG_XMM0) used |= 1u << r;
                else if (r >= (int)GIR_ASMREG_XMM0 && r < (int)GIR_ASMREG_ST0) used_x |= 1ull << (r - GIR_ASMREG_XMM0);
            }
        static const int pool[] = {0, 1, 2, 6, 7, 8, 9, 10, 11};
        auto alloc_gpr = [&]() -> int {
            for (int r : pool)
                if (!(used & (1u << r))) {
                    used |= 1u << r;
                    return r;
                }
            fail("inline assembly needs too many registers");
        };
        auto alloc_xmm = [&]() -> int {
            for (int k = 0; k < 16; k++)
                if (!(used_x & (1ull << k))) {
                    used_x |= 1ull << k;
                    return GIR_ASMREG_XMM0 + k;
                }
            fail("inline assembly needs too many xmm registers");
        };
        auto has = [](const InlineAsm::ConstraintInfo &c, const char *k) {
            for (const std::string &x : c.Codes)
                if (x == k) return true;
            return false;
        };
        // Bind operands in order: outputs, then inputs.
        unsigned argi = 0;
        Type *rt = CB.getType();
        unsigned n_direct = 0;
        SmallVector<int, 4> direct_op;  // direct output k -> template operand
        for (unsigned ci = 0; ci < cons.size(); ci++) {
            const auto &c = cons[ci];
            if (c.Type == InlineAsm::isClobber) continue;
            if (c.Type == InlineAsm::isLabel) fail("asm goto");
            Op o{K_REG, -1, 8, 0, nullptr};
            if (c.Type == InlineAsm::isOutput) {
                if (c.isIndirect) {
                    o.v = CB.getArgOperand(argi++);
                    if (!has(c, "m") && !has(c, "imr") ) {
                        bool m = false;
                        for (const std::string &x : c.Codes) if (x.find('m') != std::string::npos) m = true;
                        if (!m) fail("indirect inline-asm output without a memory alternative");
                    }
                    o.kind = K_MEM;
                    o.reg = alloc_gpr();
                } else {
                    Type *ot = rt->isStructTy() ? cast<StructType>(rt)->getElementType(n_direct) : rt;
                    o.size = (unsigned)DL.getTypeStoreSize(ot);
                    int r = c.Codes.size() == 1 ? fixed_reg(c.Codes[0]) : -1;
                    if (r < 0) {
                        if (has(c, "x")) r = alloc_xmm();
                        else if (has(c, "r") || has(c, "q") || has(c, "R") || has(c, "g") || has(c, "imr") || has(c, "rm")) r = alloc_gpr();
                        else fail("inline-asm output constraint '" + (c.Codes.empty() ? std::string() : c.Codes[0]) + "'");
                    }
                    o.reg = r;
                    direct_op.push_back((int)ops.size());
                    n_direct++;
                }
            } else {
                o.v = CB.getArgOperand(argi++);
                if (c.isIndirect) {
                    o.kind = K_MEM;
                    o.reg = alloc_gpr();
                } else if (!c.Codes.empty() && isdigit((unsigned char)c.Codes[0][0])) {
                    unsigned n = (unsigned)std::stoul(c.Codes[0]);
                    if (n >= ops.size() || ops[n].kind != K_REG) fail("inline-asm input tied to a memory output");
                    o.reg = ops[n].reg;
                    o.size = ops[n].size;
                } else {
                    int r = c.Codes.size() == 1 ? fixed_reg(c.Codes[0]) : -1;
                    const auto *ci_ = dyn_cast<ConstantInt>(o.v);
                    bool imm_ok = has(c, "i") || has(c, "n") || has(c, "imr") || has(c, "g") || has(c, "I") ||
                                  has(c, "J") || has(c, "K") || has(c, "N") || has(c, "e") || has(c, "Z");
                    if (r >= 0) {
                        o.reg = r;
                    } else if (ci_ && imm_ok && ci_->getBitWidth() <= 64) {
                        o.kind = K_IMM;
                        o.imm = ci_->getSExtValue();
                    } else if (has(c, "x")) {
                        o.reg = alloc_xmm();
                    } else if (has(c, "r") || has(c, "q") || has(c, "R") || has(c, "g") || has(c, "imr") || has(c, "rm") ||
                               has(c, "ir")) {
                        o.reg = alloc_gpr();
                    } else {
                        fail("inline-asm input constraint '" + (c.Codes.empty() ? std::string() : c.Codes[0]) + "'");
                    }
                    o.size = (unsigned)DL.getTypeStoreSize(o.v->getType());
                }
            }
            op_of_con[ci] = (int)ops.size();
            ops.push_back(o);
        }
        // Substitute operands into the template.
        StringRef s = IA->getAsmString();
        std::string text;
        for (size_t i = 0; i < s.size(); i++) {
            char ch = s[i];
            if (ch != '$') {
                text += ch;
                continue;
            }
            if (i + 1 >= s.size()) fail("inline-asm template ends in '$'");
            char nx = s[i + 1];
            if (nx == '$') { text += '$'; i++; continue; }
            if (nx == '(' || nx == ')' || nx == '|') fail("inline-asm dialect alternatives");
            unsigned n = 0;
            char mod = 0;
            size_t k = i + 1;
            if (nx == '{') {
                k++;
                while (k < s.size() && isdigit((unsigned char)s[k])) n = n * 10 + (s[k++] - '0');
                if (k < s.size() && s[k] == ':') { mod = s[k + 1]; k += 2; }
                if (k >= s.size() || s[k] != '}') fail("inline-asm operand reference");
                i = k;
            } else if (isdigit((unsigned char)nx)) {
                while (k < s.size() && isdigit((unsigned char)s[k])) n = n * 10 + (s[k++] - '0');
                i = k - 1;
            } else {
                fail("inline-asm template escape '$" + std::string(1, nx) + "'");
            }
            if (n >= ops.size()) fail("inline-asm operand number out of range");
            const Op &o = ops[n];
            if (o.kind == K_IMM) {
                if (mod == 'c') text += std::to_string((int64_t)o.imm);
                else if (mod == 'n') text += std::to_string(-(int64_t)o.imm);
                else if (mod == 0) text += "$" + std::to_string((int64_t)o.imm);
                else fail(std::string("inline-asm modifier '") + mod + "' on an immediate");
            } else if (o.kind == K_MEM) {
                if (mod != 0 && mod != 'P' && mod != 'a') fail(std::string("inline-asm modifier '") + mod + "' on memory");
                text += std::string("(%") + gpr_name(o.reg, 8) + ")";
            } else if (o.reg >= (int)GIR_ASMREG_ST0) {
                int k2 = o.reg - GIR_ASMREG_ST0;
                text += k2 == 0 ? "%st" : "%st(" + std::to_string(k2) + ")";
            } else if (o.reg >= (int)GIR_ASMREG_XMM0) {
                text += "%xmm" + std::to_string(o.reg - GIR_ASMREG_XMM0);
            } else {
                unsigned size = o.size > 8 ? 8 : (o.size == 3 ? 4 : o.size > 4 ? 8 : o.size);
                if (mod == 'b') size = 1;
                else if (mod == 'w') size = 2;
                else if (mod == 'k') size = 4;
                else if (mod == 'q') size = 8;
                else if (mod == 'h') {
                    if (o.reg > 3) fail("inline-asm 'h' modifier on a register without a high byte");
                    static const char *hn[] = {"ah", "ch", "dh", "bh"};
                    text += std::string("%") + hn[o.reg];
                    continue;
                } else if (mod != 0) fail(std::string("inline-asm modifier '") + mod + "'");
                text += std::string("%") + gpr_name(o.reg, size);
            }
        }
        std::vector<uint8_t> code;
        std::string err;
        if (!gir_assemble(M.getTargetTriple(), text, false, code, err))
            fail("inline assembly '" + s.substr(0, 60).str() + "': " + err);
        // x87: inputs and outputs must be st(0..k); count the inputs left on
        // the stack (neither tied to an output nor popped by the code).
        unsigned st_in = 0, st_out = 0, st_tied = 0, st_popped = 0;
        for (unsigned ci = 0; ci < cons.size(); ci++) {
            int oi = op_of_con[ci];
            if (oi < 0 || ops[oi].kind != K_REG || ops[oi].reg < (int)GIR_ASMREG_ST0) continue;
            unsigned k2 = ops[oi].reg - GIR_ASMREG_ST0;
            if (cons[ci].Type == InlineAsm::isOutput) st_out |= 1u << k2;
            else {
                st_in |= 1u << k2;
                if (!cons[ci].Codes.empty() && isdigit((unsigned char)cons[ci].Codes[0][0])) st_tied++;
                else if (st_clobbered & (1u << k2)) st_popped++;
            }
        }
        auto contiguous = [](unsigned m) { return (m & (m + 1)) == 0; };
        if (!contiguous(st_in) || !contiguous(st_out)) fail("inline-asm x87 operands that are not st(0..n)");
        unsigned n_st_in = (unsigned)__builtin_popcount(st_in);
        uint32_t pop = n_st_in - st_tied - st_popped;
        // Emit: inputs (values; addresses for memory operands), then outputs.
        GirAsm a{};
        a.code = (uint32_t)T.data.size();
        a.code_len = (uint32_t)code.size();
        T.data.insert(T.data.end(), code.begin(), code.end());
        SmallVector<uint32_t, 16> ins;
        for (unsigned ci = 0; ci < cons.size(); ci++) {
            int oi = op_of_con[ci];
            if (oi < 0) continue;
            const Op &o = ops[oi];
            if (o.kind == K_IMM || !o.v) continue;
            ins.push_back(ref(o.v));
            ins.push_back((uint32_t)o.reg);
            ty(o.v->getType());
        }
        a.n_in = (uint32_t)ins.size() / 2;
        uint16_t rty = ret_ty(rt);  // before the run: a new struct type appends to opnds
        a.ops = (uint32_t)T.opnds.size();
        for (size_t i = 0; i < ins.size(); i += 2) {
            push_ref(ins[i]);
            T.opnds.push_back(ins[i + 1]);
        }
        const StructLayout *SL = rt->isStructTy() ? DL.getStructLayout(cast<StructType>(rt)) : nullptr;
        for (unsigned k = 0; k < n_direct; k++) {
            T.opnds.push_back((uint32_t)ops[direct_op[k]].reg);
            T.opnds.push_back(SL ? (uint32_t)SL->getElementOffset(k).getFixedValue() : 0);
        }
        a.n_out = n_direct;
        a.x87_pop = pop;
        T.asms.push_back(a);
        uint32_t r = emit(GIR_ASM, rty, 0, 0, 0, (uint32_t)T.asms.size() - 1, 0, 0, 0);
        if (rty != GIR_T_VOID) vmap[&CB] = r;
    }

    // Inline assembly with an empty template is an optimization barrier
    // only: a direct output tied to an input gets that input, other outputs
    // are undefined, indirect outputs are untouched.
    void inline_asm(const CallBase &CB) {
        const auto *IA = cast<InlineAsm>(CB.getCalledOperand());
        StringRef s = IA->getAsmString();
        // Strip whitespace and comments.
        std::string body;
        for (size_t i = 0; i < s.size(); i++) {
            if (s[i] == '#') {
                while (i < s.size() && s[i] != '\n') i++;
                continue;
            }
            if (s[i] == '/' && i + 1 < s.size() && s[i + 1] == '*') {
                size_t e = s.find("*/", i + 2);
                i = e == StringRef::npos ? s.size() : e + 1;
                continue;
            }
            if (!isspace((unsigned char)s[i])) body += s[i];
        }
        if (!body.empty()) return asm_code(CB);
        if (CB.getType()->isVoidTy()) return;
        InlineAsm::ConstraintInfoVector cons = IA->ParseConstraints();
        // Call argument of each indirect output / input constraint, the
        // direct outputs in order, and the input tied to each direct output
        // (an output's MatchingInput is the constraint index of its input).
        SmallVector<int, 16> arg_of(cons.size(), -1);
        SmallVector<int, 4> ties;  // per direct output: call argument index or -1
        unsigned argi = 0;
        for (unsigned ci = 0; ci < cons.size(); ci++) {
            const auto &c = cons[ci];
            if ((c.Type == InlineAsm::isOutput && c.isIndirect) || c.Type == InlineAsm::isInput) arg_of[ci] = (int)argi++;
        }
        for (unsigned ci = 0; ci < cons.size(); ci++) {
            const auto &c = cons[ci];
            if (c.Type != InlineAsm::isOutput || c.isIndirect) continue;
            int tied = -1;
            if (c.hasMatchingInput() && (unsigned)c.MatchingInput < cons.size()) tied = arg_of[c.MatchingInput];
            ties.push_back(tied);
        }
        unsigned n_direct = ties.size();
        uint16_t rt = ty(CB.getType());
        auto out_value = [&](unsigned k, Type *t) -> uint32_t {
            uint16_t ot = ty(t);
            if (ties[k] >= 0) {
                const Value *v = CB.getArgOperand((unsigned)ties[k]);
                uint16_t it = ty(v->getType());
                uint32_t r = ref(v);
                if (it == ot) return is_placeholder(r) ? copy(r, ot) : r;
                if (T.types[it].size == T.types[ot].size && cls(it) == cls(ot)) return emit(GIR_BITCAST, ot, 0, 0, it, r, 0, 0, RA);
                if (is_int(it) && is_int(ot) && cls(it) == GIR_C_INT && cls(ot) == GIR_C_INT)
                    return emit(bits(it) > bits(ot) ? GIR_TRUNC : GIR_ZEXT, ot, 0, 0, it, r, 0, 0, RA);
                fail("tied inline-asm operands of different types");
            }
            if (cls(ot) == GIR_C_VEC || cls(ot) == GIR_C_MEM) return czero(ot);
            return new_const(0, 0, ot);
        };
        if (n_direct == 1 && !CB.getType()->isStructTy()) {
            vmap[&CB] = out_value(0, CB.getType());
            return;
        }
        auto *st = cast<StructType>(CB.getType());
        uint32_t agg = czero(rt);
        const StructLayout *SL = DL.getStructLayout(st);
        for (unsigned k = 0; k < st->getNumElements(); k++) {
            uint32_t v = out_value(k, st->getElementType(k));
            agg = emit(GIR_INSERTVALUE, rt, 0, 0, 0, agg, v, (uint32_t)SL->getElementOffset(k).getFixedValue(), RA | RB);
        }
        vmap[&CB] = agg;
    }

    void call(const CallBase &CB) {
        const Value *callee = CB.getCalledOperand();
        if (CB.isInlineAsm()) return inline_asm(CB);
        if (const auto *fn = dyn_cast<Function>(callee); fn && fn->isIntrinsic())
            return intrinsic(CB, fn->getIntrinsicID());
        if (CB.getCallingConv() != CallingConv::C) fail("calling convention " + std::to_string(CB.getCallingConv()));
        if (CB.hasOperandBundles()) fail("operand bundle");
        if (CB.isMustTailCall()) fail("musttail call");
        FunctionType *FT = CB.getFunctionType();
        uint16_t rt = check_ret(FT->getReturnType());
        uint32_t c = ref(callee);
        emit_call(CB, c, rt, FT->isVarArg());
    }

    // Byte offset and type of an extractvalue/insertvalue index path.
    uint32_t agg_offset(Type *t, ArrayRef<unsigned> idx) {
        uint64_t off = 0;
        for (unsigned i : idx) {
            if (auto *st = dyn_cast<StructType>(t)) {
                off += DL.getStructLayout(st)->getElementOffset(i).getFixedValue();
                t = st->getElementType(i);
            } else {
                auto *at = cast<ArrayType>(t);
                off += (uint64_t)i * DL.getTypeAllocSize(at->getElementType());
                t = at->getElementType();
            }
        }
        return (uint32_t)off;
    }

    uint16_t atomic_flags(AtomicOrdering o, SyncScope::ID ss) {
        uint16_t f = (uint16_t)(((unsigned)o & 7) << GIR_IF_ORD_SHIFT);
        if (ss == SyncScope::SingleThread) f |= GIR_IF_SINGLETHREAD;
        return f;
    }

    // ------------------------------------------------------------ one inst
    void inst(const Instruction &I) {
        curI = &I;
        const MDNode *dl = I.getDebugLoc().getAsMDNode();
        cur_dbg = dl ? dloc(static_cast<const DILocation *>(dl)) : 0;
        switch (I.getOpcode()) {
        case Instruction::Ret: {
            const auto &R = cast<ReturnInst>(I);
            uint32_t v = GIR_NONE;
            if (const Value *rv = R.getReturnValue()) {
                uint16_t t = ty(rv->getType());
                v = ref(rv);
                if (F->hasRetAttribute(Attribute::SExt) && is_int(t) && bits(t) < 32)
                    v = emit(GIR_SEXT, GIR_T_I32, 0, 0, t, v, 0, 0, RA);
            } else if (sret_arg != GIR_NONE) {
                v = GIR_MK(GIR_V_ARG, sret_arg);
            }
            emit(GIR_RET, GIR_T_VOID, 0, 0, 0, v, 0, 0, RA);
            return;
        }
        case Instruction::Br: {
            const auto &B = cast<BranchInst>(I);
            if (B.isUnconditional()) {
                emit(GIR_BR, GIR_T_VOID, 0, 0, 0, block(B.getSuccessor(0)), 0, 0, 0);
            } else {
                uint32_t c = ref(B.getCondition());
                emit(GIR_CONDBR, GIR_T_VOID, 0, 0, 0, c, block(B.getSuccessor(0)), block(B.getSuccessor(1)), RA);
            }
            return;
        }
        case Instruction::Switch: {
            const auto &S = cast<SwitchInst>(I);
            uint16_t t = ty(S.getCondition()->getType());
            uint32_t c = ref(S.getCondition());
            SmallVector<uint32_t, 32> cases;
            for (const auto &cs : S.cases()) {
                const ConstantInt *cv = cs.getCaseValue();
                cases.push_back(cls(t) == GIR_C_INT2 ? cwide(cv->getValue(), t) : cint(cv->getZExtValue(), t));
                cases.push_back(block(cs.getCaseSuccessor()));
            }
            uint32_t s = (uint32_t)T.opnds.size();
            T.opnds.push_back(block(S.getDefaultDest()));
            T.opnds.insert(T.opnds.end(), cases.begin(), cases.end());
            emit(GIR_SWITCH, GIR_T_VOID, 0, 0, t, c, s, (uint32_t)(cases.size() / 2), RA);
            return;
        }
        case Instruction::IndirectBr: {
            const auto &B = cast<IndirectBrInst>(I);
            uint32_t a = ref(B.getAddress());
            uint32_t s = (uint32_t)T.opnds.size();
            for (unsigned i = 0; i < B.getNumDestinations(); i++) T.opnds.push_back(block(B.getDestination(i)));
            emit(GIR_INDIRECTBR, GIR_T_VOID, 0, 0, 0, a, s, B.getNumDestinations(), RA);
            return;
        }
        case Instruction::Unreachable:
            emit(GIR_UNREACHABLE, GIR_T_VOID, 0, 0, 0, 0, 0, 0, 0);
            return;
        case Instruction::Add: case Instruction::Sub: case Instruction::Mul:
        case Instruction::SDiv: case Instruction::UDiv: case Instruction::SRem: case Instruction::URem:
        case Instruction::And: case Instruction::Or: case Instruction::Xor:
        case Instruction::Shl: case Instruction::LShr: case Instruction::AShr: {
            uint16_t t = ty(I.getType());
            if (t == GIR_T_PTR) fail("pointer arithmetic operator");
            uint8_t op = binop(I.getOpcode());
            uint32_t a = ref(I.getOperand(0));
            uint32_t b = ref(I.getOperand(1));
            if (cls(t) == GIR_C_INT2 && (op == GIR_SDIV || op == GIR_UDIV || op == GIR_SREM || op == GIR_UREM)) {
                bool sg = op == GIR_SDIV || op == GIR_SREM;
                a = widen128(a, t, sg);
                b = widen128(b, t, sg);
                const char *fn = op == GIR_SDIV ? "__divti3" : op == GIR_UDIV ? "__udivti3"
                                 : op == GIR_SREM ? "__modti3" : "__umodti3";
                uint32_t r = libcall(fn, GIR_T_I128, {a, b});
                if (t != GIR_T_I128) r = emit(GIR_TRUNC, t, 0, 0, GIR_T_I128, r, 0, 0, 0);
                vmap[&I] = r;
                return;
            }
            vmap[&I] = emit(op, t, 0, 0, 0, a, b, 0, RA | RB);
            return;
        }
        case Instruction::FAdd: case Instruction::FSub: case Instruction::FMul: case Instruction::FDiv:
        case Instruction::FRem: {
            uint16_t t = ty(I.getType());
            uint32_t a = ref(I.getOperand(0));
            uint32_t b = ref(I.getOperand(1));
            bool half = t == GIR_T_F16;
            if (half) {
                a = half_to(a, GIR_T_F32);
                b = half_to(b, GIR_T_F32);
            }
            uint16_t ct = half ? (uint16_t)GIR_T_F32 : t;
            uint32_t r;
            if (I.getOpcode() == Instruction::FRem) {
                if (T.types[t].kind == GIR_TK_VECTOR) fail("vector frem");
                r = libcall("fmod" + fsuf(ct), ct, {a, b});
            } else {
                r = emit(binop(I.getOpcode()), ct, 0, 0, 0, a, b, 0, RA | RB);
            }
            vmap[&I] = half ? to_half(r, GIR_T_F32) : r;
            return;
        }
        case Instruction::FNeg: {
            uint16_t t = ty(I.getType());
            uint32_t a = ref(I.getOperand(0));
            if (t == GIR_T_F16) {  // flip the sign bit
                uint32_t i = emit(GIR_BITCAST, GIR_T_I16, 0, 0, t, a, 0, 0, RA);
                uint32_t x = emit(GIR_XOR, GIR_T_I16, 0, 0, 0, i, cint(0x8000, GIR_T_I16), 0, 0);
                vmap[&I] = emit(GIR_BITCAST, t, 0, 0, GIR_T_I16, x, 0, 0, 0);
                return;
            }
            vmap[&I] = emit(GIR_FNEG, t, 0, 0, t, a, 0, 0, RA);
            return;
        }
        case Instruction::ICmp: {
            const auto &C = cast<ICmpInst>(I);
            uint16_t ot = ty(C.getOperand(0)->getType());
            uint16_t rt = ty(C.getType());
            uint32_t a = ref(C.getOperand(0));
            uint32_t b = ref(C.getOperand(1));
            vmap[&I] = emit(GIR_ICMP, rt, pred(C.getPredicate()), 0, ot, a, b, 0, RA | RB);
            return;
        }
        case Instruction::FCmp: {
            const auto &C = cast<FCmpInst>(I);
            uint16_t ot = ty(C.getOperand(0)->getType());
            uint16_t rt = ty(C.getType());
            uint32_t a = ref(C.getOperand(0));
            uint32_t b = ref(C.getOperand(1));
            if (ot == GIR_T_F16) {
                a = half_to(a, GIR_T_F32);
                b = half_to(b, GIR_T_F32);
                ot = GIR_T_F32;
            }
            vmap[&I] = emit(GIR_FCMP, rt, (uint8_t)C.getPredicate(), 0, ot, a, b, 0, RA | RB);
            return;
        }
        case Instruction::Select: {
            const auto &S = cast<SelectInst>(I);
            ty(S.getCondition()->getType());
            uint16_t t = ty(S.getType());
            uint32_t c = ref(S.getCondition());
            uint32_t a = ref(S.getTrueValue());
            uint32_t b = ref(S.getFalseValue());
            vmap[&I] = emit(GIR_SELECT, t, 0, 0, 0, c, a, b, RA | RB | RC);
            return;
        }
        case Instruction::Trunc: case Instruction::ZExt: case Instruction::SExt:
        case Instruction::PtrToInt: case Instruction::IntToPtr: case Instruction::BitCast:
        case Instruction::AddrSpaceCast:
        case Instruction::FPExt: case Instruction::FPTrunc: case Instruction::FPToSI: case Instruction::FPToUI:
        case Instruction::SIToFP: case Instruction::UIToFP: {
            uint32_t r = cast_op(I.getOpcode(), I.getOperand(0), I.getType());
            alias(I, r, ty(I.getType()));
            return;
        }
        case Instruction::Freeze: {
            uint16_t t = ty(I.getType());
            alias(I, ref(I.getOperand(0)), t);
            return;
        }
        case Instruction::Alloca: {
            const auto &A = cast<AllocaInst>(I);
            if (A.getAddressSpace() != 0) fail("alloca in non-zero address space");
            uint64_t align = A.getAlign().value();
            if (align > (1u << 20)) fail("alloca with alignment above 1 MiB");
            if (A.isStaticAlloca() && A.getParent() == &F->getEntryBlock()) {
                std::optional<TypeSize> sz = A.getAllocationSize(DL);
                if (!sz || sz->isScalable()) fail("alloca of unknown size");
                uint64_t size = sz->getFixedValue();
                if (size > 0x7FFFFFFFull) fail("alloca above 2 GiB");
                vmap[&I] = emit(GIR_ALLOCA, GIR_T_PTR, 0, 0, 0, (uint32_t)size, (uint32_t)align, 0, 0);
                return;
            }
            // Dynamic: bytes = count * element size, as i64.
            uint64_t es = DL.getTypeAllocSize(A.getAllocatedType());
            const Value *cnt = A.getArraySize();
            uint32_t bytes;
            if (const auto *cc = dyn_cast<ConstantInt>(cnt)) {
                bytes = cint(cc->getZExtValue() * es, GIR_T_I64);
            } else {
                uint16_t ct = ty(cnt->getType());
                if (cls(ct) != GIR_C_INT) fail("alloca count wider than 64 bits");
                uint32_t c = ref(cnt);
                if (ct != GIR_T_I64) c = emit(GIR_ZEXT, GIR_T_I64, 0, 0, ct, c, 0, 0, RA);
                bytes = es == 1 ? (is_placeholder(c) ? copy(c, GIR_T_I64) : c)
                                : emit(GIR_MUL, GIR_T_I64, 0, 0, 0, c, cint(es, GIR_T_I64), 0, RA);
            }
            vmap[&I] = emit(GIR_DYNALLOCA, GIR_T_PTR, 0, 0, 0, bytes, (uint32_t)align, 0, RA);
            return;
        }
        case Instruction::Load: {
            const auto &L = cast<LoadInst>(I);
            uint16_t t = ty(L.getType());
            ty(L.getPointerOperandType());
            if (T.types[t].kind == GIR_TK_VECTOR && bits(T.types[t].elems) == 1) fail("load of an i1 vector");
            uint16_t fl = (L.isVolatile() ? GIR_IF_VOLATILE : 0) |
                          (L.isAtomic() ? atomic_flags(L.getOrdering(), L.getSyncScopeID()) : 0);
            if (L.isAtomic() && cls(t) != GIR_C_INT && cls(t) != GIR_C_FP) fail("atomic load of this type");
            uint32_t p = ref(L.getPointerOperand());
            vmap[&I] = emit(GIR_LOAD, t, 0, fl, 0, p, 0, 0, RA);
            return;
        }
        case Instruction::Store: {
            const auto &S = cast<StoreInst>(I);
            uint16_t t = ty(S.getValueOperand()->getType());
            ty(S.getPointerOperandType());
            if (T.types[t].kind == GIR_TK_VECTOR && bits(T.types[t].elems) == 1) fail("store of an i1 vector");
            uint16_t fl = (S.isVolatile() ? GIR_IF_VOLATILE : 0) |
                          (S.isAtomic() ? atomic_flags(S.getOrdering(), S.getSyncScopeID()) : 0);
            if (S.isAtomic() && cls(t) != GIR_C_INT && cls(t) != GIR_C_FP) fail("atomic store of this type");
            uint32_t v = ref(S.getValueOperand());
            uint32_t p = ref(S.getPointerOperand());
            emit(GIR_STORE, GIR_T_VOID, 0, fl, t, v, p, 0, RA | RB);
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
            uint16_t t = ty(P.getType());
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
            vmap[&I] = emit(GIR_PHI, t, 0, 0, 0, 0, s, (uint32_t)(pairs.size() / 2), 0);
            return;
        }
        case Instruction::ExtractValue: {
            const auto &E = cast<ExtractValueInst>(I);
            uint16_t t = ty(E.getType());
            ty(E.getAggregateOperand()->getType());
            uint32_t off = agg_offset(E.getAggregateOperand()->getType(), E.getIndices());
            uint32_t a = ref(E.getAggregateOperand());
            vmap[&I] = emit(GIR_EXTRACTVALUE, t, 0, 0, 0, a, off, 0, RA);
            return;
        }
        case Instruction::InsertValue: {
            const auto &E = cast<InsertValueInst>(I);
            uint16_t t = ty(E.getType());
            ty(E.getInsertedValueOperand()->getType());
            uint32_t off = agg_offset(E.getType(), E.getIndices());
            uint32_t a = ref(E.getAggregateOperand());
            uint32_t b = ref(E.getInsertedValueOperand());
            vmap[&I] = emit(GIR_INSERTVALUE, t, 0, 0, 0, a, b, off, RA | RB);
            return;
        }
        case Instruction::ExtractElement: {
            const auto &E = cast<ExtractElementInst>(I);
            uint16_t t = ty(E.getType());
            uint16_t vt = ty(E.getVectorOperandType());
            if (cls(ty(E.getIndexOperand()->getType())) != GIR_C_INT) fail("vector index wider than 64 bits");
            uint32_t a = ref(E.getVectorOperand());
            uint32_t b = ref(E.getIndexOperand());
            vmap[&I] = emit(GIR_EXTRACTELT, t, 0, 0, vt, a, b, 0, RA | RB);
            return;
        }
        case Instruction::InsertElement: {
            const auto &E = cast<InsertElementInst>(I);
            uint16_t t = ty(E.getType());
            if (cls(ty(E.getOperand(2)->getType())) != GIR_C_INT) fail("vector index wider than 64 bits");
            uint32_t a = ref(E.getOperand(0));
            uint32_t b = ref(E.getOperand(1));
            uint32_t c = ref(E.getOperand(2));
            vmap[&I] = emit(GIR_INSERTELT, t, 0, 0, 0, a, b, c, RA | RB | RC);
            return;
        }
        case Instruction::ShuffleVector: {
            const auto &S = cast<ShuffleVectorInst>(I);
            uint16_t t = ty(S.getType());
            uint16_t at = ty(S.getOperand(0)->getType());
            uint32_t a = ref(S.getOperand(0));
            uint32_t b = ref(S.getOperand(1));
            uint32_t s = (uint32_t)T.opnds.size();
            for (int m : S.getShuffleMask()) T.opnds.push_back(m < 0 ? GIR_NONE : (uint32_t)m);
            vmap[&I] = emit(GIR_SHUFFLE, t, 0, 0, at, a, b, s, RA | RB);
            return;
        }
        case Instruction::AtomicCmpXchg: {
            const auto &X = cast<AtomicCmpXchgInst>(I);
            uint16_t vt = ty(X.getCompareOperand()->getType());
            if (cls(vt) != GIR_C_INT) fail("cmpxchg of this type");
            uint16_t t = ty(X.getType());
            uint16_t fl = atomic_flags(X.getSuccessOrdering(), X.getSyncScopeID()) |
                          (uint16_t)(((unsigned)X.getFailureOrdering() & 7) << GIR_IF_FORD_SHIFT) |
                          (X.isWeak() ? GIR_IF_WEAK : 0) | (X.isVolatile() ? GIR_IF_VOLATILE : 0);
            uint32_t p = ref(X.getPointerOperand());
            uint32_t a = ref(X.getCompareOperand());
            uint32_t b = ref(X.getNewValOperand());
            vmap[&I] = emit(GIR_CMPXCHG, t, 0, fl, vt, p, a, b, RA | RB | RC);
            return;
        }
        case Instruction::AtomicRMW: {
            const auto &R = cast<AtomicRMWInst>(I);
            uint16_t t = ty(R.getType());
            uint8_t k;
            switch (R.getOperation()) {
            case AtomicRMWInst::Xchg: k = GIR_RMW_XCHG; break;
            case AtomicRMWInst::Add: k = GIR_RMW_ADD; break;
            case AtomicRMWInst::Sub: k = GIR_RMW_SUB; break;
            case AtomicRMWInst::And: k = GIR_RMW_AND; break;
            case AtomicRMWInst::Nand: k = GIR_RMW_NAND; break;
            case AtomicRMWInst::Or: k = GIR_RMW_OR; break;
            case AtomicRMWInst::Xor: k = GIR_RMW_XOR; break;
            case AtomicRMWInst::Max: k = GIR_RMW_MAX; break;
            case AtomicRMWInst::Min: k = GIR_RMW_MIN; break;
            case AtomicRMWInst::UMax: k = GIR_RMW_UMAX; break;
            case AtomicRMWInst::UMin: k = GIR_RMW_UMIN; break;
            case AtomicRMWInst::FAdd: k = GIR_RMW_FADD; break;
            case AtomicRMWInst::FSub: k = GIR_RMW_FSUB; break;
            default: fail("atomicrmw operation");
            }
            bool fp = k == GIR_RMW_FADD || k == GIR_RMW_FSUB;
            if (fp ? (t != GIR_T_F32 && t != GIR_T_F64) : (cls(t) != GIR_C_INT || (t == GIR_T_PTR && k != GIR_RMW_XCHG)))
                fail("atomicrmw of this type");
            uint16_t fl = atomic_flags(R.getOrdering(), R.getSyncScopeID()) | (R.isVolatile() ? GIR_IF_VOLATILE : 0);
            uint32_t p = ref(R.getPointerOperand());
            uint32_t v = ref(R.getValOperand());
            vmap[&I] = emit(GIR_ATOMICRMW, t, k, fl, t, p, v, 0, RA | RB);
            return;
        }
        case Instruction::Fence: {
            const auto &Fe = cast<FenceInst>(I);
            emit(GIR_FENCE, GIR_T_VOID, 0, atomic_flags(Fe.getOrdering(), Fe.getSyncScopeID()), 0, 0, 0, 0, 0);
            return;
        }
        case Instruction::VAArg: fail("va_arg");
        case Instruction::Invoke: case Instruction::Resume: case Instruction::LandingPad:
        case Instruction::CleanupPad: case Instruction::CatchPad: case Instruction::CatchSwitch:
        case Instruction::CatchRet: case Instruction::CleanupRet:
            fail("exception handling");
        case Instruction::CallBr: fail("callbr (asm goto)");
        default: break;
        }
        fail(std::string("instruction '") + I.getOpcodeName() + "'");
    }

    // ------------------------------------------------------------ functions
    void function(const Function &Fn, uint32_t g) {
        F = &Fn;
        curI = nullptr;
        cur_dbg = 0;
        if (Fn.getCallingConv() != CallingConv::C) fail("calling convention " + std::to_string(Fn.getCallingConv()));
        if (Fn.hasPrefixData() || Fn.hasPrologueData()) fail("prefix/prologue data");
        if (Fn.hasGC()) fail("garbage collector");
        if (Fn.hasPersonalityFn()) fail("personality function (exception handling)");
        if (Fn.hasFnAttribute(Attribute::Naked)) fail("naked function");
        FunctionType *FT = Fn.getFunctionType();

        GirFunc gf{};
        gf.global = g;
        fn_flags = (Fn.hasLocalLinkage() ? GIR_FN_INTERNAL : 0) | (FT->isVarArg() ? GIR_FN_VARARG : 0);
        uint64_t falign = Fn.getAlign() ? Fn.getAlign()->value() : 16;
        if (falign < 16) falign = 16;
        gf.first_block = (uint32_t)T.blocks.size();
        gf.first_inst = (uint32_t)T.insts.size();
        gf.n_args = (uint32_t)Fn.arg_size();
        where = "return type";
        gf.ret_ty = check_ret(FT->getReturnType());
        sret_arg = GIR_NONE;
        SmallVector<uint32_t, 16> args;
        for (const Argument &A : Fn.args()) {
            where = "parameter " + std::to_string(A.getArgNo());
            uint32_t w = alist_bits(Fn.getAttributes()) & AL_SPECIAL
                             ? abi_word(Fn.getAttributes().getParamAttrs(A.getArgNo()), A.getType(), "parameter")
                             : abi_plain(ty(A.getType()), "parameter");
            if (A.hasStructRetAttr()) sret_arg = A.getArgNo();
            args.push_back(ty(A.getType()));
            args.push_back(w);
        }
        gf.args = (uint32_t)T.opnds.size();
        T.opnds.insert(T.opnds.end(), args.begin(), args.end());
        where.clear();
        if (sret_arg != GIR_NONE) {
            if (gf.ret_ty != GIR_T_VOID) fail("sret function with a return value");
            gf.ret_ty = GIR_T_PTR;
        }
        gf.dbg = dscope(Fn.getSubprogram());
        T.globals[g].func = (uint32_t)T.funcs.size();

        bmap.assign(Fn.getMaxBlockNumber(), GIR_NONE);
        uint32_t nb = 0;
        for (const BasicBlock &BB : Fn) bmap[BB.getNumber()] = nb++;
        vmap.clear();
        phimat.clear();
        fixes.clear();

        bool entry = true;
        for (const BasicBlock &BB : Fn) {
            GirBlock b{(uint32_t)T.insts.size(), 0};
            if (entry) {
                // Constants used by PHIs that become instructions are computed once, here.
                in_phi_prepass = true;
                for (const BasicBlock &PB : Fn)
                    for (const PHINode &P : PB.phis()) {
                        curI = &P;
                        cur_dbg = 0;
                        for (const Value *v : P.incoming_values())
                            if (needs_mat(v) && !phimat.count_of(v)) phimat[v] = ref(v);
                    }
                in_phi_prepass = false;
                entry = false;
            }
            for (const Instruction &I : BB) {
                inst(I);
                T.n_llvm_insts++;
            }
            b.n_inst = (uint32_t)T.insts.size() - b.first_inst;
            T.blocks.push_back(b);
        }
        curI = nullptr;
        for (const Fix &fx : fixes) {
            uint32_t *p = vmap.find(fx.v);
            if (!p || is_placeholder(*p)) {
                curI = cast<Instruction>(fx.v);
                fail("use of an instruction without a GIR value");
            }
            if (fx.field == 3) T.opnds[fx.where] = *p;
            else if (fx.field == 0) T.insts[fx.where].a = *p;
            else if (fx.field == 1) T.insts[fx.where].b = *p;
            else T.insts[fx.where].c = *p;
        }
        gf.n_blocks = (uint32_t)T.blocks.size() - gf.first_block;
        gf.n_inst = (uint32_t)T.insts.size() - gf.first_inst;
        gf.flags = fn_flags | ((uint32_t)Log2_64(falign) << GIR_FN_ALIGN_SHIFT);
        T.funcs.push_back(gf);
        F = nullptr;
    }

    // ---------------------------------------------------------- initializers
    void reloc(uint32_t g, uint32_t off, uint32_t target, uint32_t kind, int64_t addend, uint32_t blk = 0,
               uint32_t blk2 = 0) {
        T.drelocs.push_back(GirDataReloc{g, off, target, kind, addend, blk, blk2});
        T.globals[g].flags |= GIR_GF_RELOCS;
    }
    // A blockaddress (possibly with offsets stripped): (function global, local block).
    bool block_of(const Value *v, uint32_t &fg, uint32_t &blk) {
        const auto *BA = dyn_cast<BlockAddress>(v);
        if (!BA) return false;
        auto it = gmap.find(BA->getFunction());
        if (it == gmap.end()) return false;
        fg = it->second;
        blk = local_block(BA->getBasicBlock());
        return true;
    }
    void init(const GlobalVariable *GV, uint32_t g, const Constant *C, size_t at, uint32_t off) {
        auto failg = [&](const std::string &why) -> void {
            throw GirUnsupported{"unsupported: " + why + " in the initializer of '" +
                                 (GV ? GV->getName().str() : std::string("a constant")) + "'"};
        };
        if (isa<ConstantAggregateZero>(C) || isa<UndefValue>(C) || isa<ConstantPointerNull>(C)) return;
        if (isa<ConstantInt>(C) || isa<ConstantFP>(C) || isa<ConstantDataSequential>(C)) {
            uint64_t n = DL.getTypeStoreSize(C->getType());
            if (!const_bytes(C, &T.data[at], n)) failg("constant");
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
            if (DL.getTypeSizeInBits(et) % 8) failg("vector initializer with sub-byte elements");
            uint64_t es = DL.getTypeAllocSize(et);
            for (unsigned i = 0, n = CV->getNumOperands(); i < n; i++)
                init(GV, g, CV->getOperand(i), at + i * es, off + (uint32_t)(i * es));
            return;
        }
        if (isa<GlobalValue>(C) || isa<ConstantExpr>(C) || isa<BlockAddress>(C)) {
            unsigned width = (unsigned)DL.getTypeStoreSize(C->getType());
            const Constant *p = C;
            // trunc (sub (ptrtoint blockaddress A, ptrtoint blockaddress B)) to i32: a label difference.
            if (const auto *CE = dyn_cast<ConstantExpr>(p); CE && CE->getOpcode() == Instruction::Trunc && width == 4)
                if (const auto *S = dyn_cast<ConstantExpr>(CE->getOperand(0)); S && S->getOpcode() == Instruction::Sub) {
                    const auto *L = dyn_cast<ConstantExpr>(S->getOperand(0));
                    const auto *R = dyn_cast<ConstantExpr>(S->getOperand(1));
                    uint32_t fa, ba, fb, bb;
                    if (L && R && L->getOpcode() == Instruction::PtrToInt && R->getOpcode() == Instruction::PtrToInt &&
                        block_of(L->getOperand(0), fa, ba) && block_of(R->getOperand(0), fb, bb) && fa == fb) {
                        reloc(g, off, fa, GIR_DR_BLOCKDIFF32, 0, ba, bb);
                        return;
                    }
                }
            if (const auto *CE = dyn_cast<ConstantExpr>(p); CE && CE->getOpcode() == Instruction::PtrToInt)
                p = CE->getOperand(0);
            if (const auto *CE = dyn_cast<ConstantExpr>(p); CE && CE->getOpcode() == Instruction::IntToPtr)
                if (const auto *CI = dyn_cast<ConstantInt>(CE->getOperand(0))) {
                    uint64_t v = CI->getZExtValue();
                    for (unsigned i = 0; i < width && i < 8; i++) T.data[at + i] = (uint8_t)(v >> (8 * i));
                    return;
                }
            if (!p->getType()->isPointerTy() || width != 8)
                failg("initializer expression that is not a 64-bit address");
            APInt offs(64, 0);
            const Value *base = p->stripAndAccumulateConstantOffsets(DL, offs, true);
            int64_t addend = offs.getSExtValue();
            if (isa<ConstantPointerNull>(base)) {
                for (unsigned i = 0; i < 8; i++) T.data[at + i] = (uint8_t)((uint64_t)addend >> (8 * i));
                return;
            }
            uint32_t fg, blk;
            if (block_of(base, fg, blk)) {
                reloc(g, off, fg, GIR_DR_BLOCK, addend, blk);
                return;
            }
            const auto *bg = dyn_cast<GlobalValue>(base);
            auto it = bg ? gmap.find(bg) : gmap.end();
            if (it == gmap.end()) failg("reference to something other than a global");
            if (is_tls(bg)) failg("address of a thread-local variable");
            reloc(g, off, it->second, GIR_DR_ABS64, addend);
            return;
        }
        failg("constant kind");
    }

    // llvm.global_ctors / llvm.global_dtors: [N x { i32, ptr, ptr }] ->
    // one pointer array per priority in .init_array[.PRIO] / .fini_array[.PRIO].
    void structors(const GlobalVariable &GV, bool ctors) {
        const auto *CA = dyn_cast<ConstantArray>(GV.getInitializer());
        if (!CA) return;  // zeroinitializer: empty list
        std::vector<std::pair<unsigned, const Constant *>> ents;
        for (const Use &u : CA->operands()) {
            const auto *CS = dyn_cast<ConstantStruct>(u.get());
            if (!CS) fail_global(GV, "structor entry");
            const Constant *fn = CS->getOperand(1);
            if (fn->isNullValue()) continue;
            unsigned prio = (unsigned)cast<ConstantInt>(CS->getOperand(0))->getZExtValue();
            ents.push_back({prio, fn});
        }
        std::stable_sort(ents.begin(), ents.end(), [](auto &a, auto &b) { return a.first < b.first; });
        for (size_t i = 0; i < ents.size();) {
            size_t j = i;
            while (j < ents.size() && ents[j].first == ents[i].first) j++;
            std::string sec = ctors ? ".init_array" : ".fini_array";
            if (ents[i].first != 65535) {
                char buf[16];
                std::snprintf(buf, sizeof buf, ".%05u", ents[i].first);
                sec += buf;
            }
            uint32_t s = section(sec, GIR_SF_WRITE, ctors ? 14 : 15);
            uint32_t g = add_global((ctors ? "__goovm_init_array." : "__goovm_fini_array.") + std::to_string(T.globals.size()),
                                    GIR_G_VAR, GIR_GF_INTERNAL | GIR_GF_DEFINED | GIR_GF_LOCALREF, 8);
            T.globals[g].section = s;
            T.globals[g].size = (uint32_t)(8 * (j - i));
            uint32_t at = (uint32_t)T.data.size();
            T.data.resize(at + 8 * (j - i), 0);
            T.globals[g].data = at;
            for (size_t k = i; k < j; k++) {
                APInt offs(64, 0);
                const Value *base = ents[k].second->stripAndAccumulateConstantOffsets(DL, offs, true);
                auto it = gmap.find(dyn_cast<GlobalValue>(base));
                if (it == gmap.end()) fail_global(GV, "structor that is not an exported function");
                reloc(g, (uint32_t)(8 * (k - i)), it->second, GIR_DR_ABS64, offs.getSExtValue());
            }
            i = j;
        }
    }

    // ---------------------------------------------------------------- module
    void run() {
        T.header.version = GIR_VERSION;
        T.header.tls_get_addr = GIR_NONE;
        pie = M.getPIELevel() != PIELevel::Default;
        T.header.flags = pie ? GIR_MF_PIE : 0;
        T.strtab.push_back(0);
        T.dstr.push_back(0);
        T.dlocs.push_back(GirDLoc{0, 0, 0, 0});
        T.dscopes.push_back(GirDScope{0, 0, 0, 0, 0, 0});
        T.dfiles.push_back(GirDFile{0, 0});
        predefined_types();
        if (!M.getModuleInlineAsm().empty())
            throw GirUnsupported{"unsupported: module-level inline assembly"};
        if (!M.ifuncs().empty()) fail_global(*M.ifuncs().begin(), "ifunc");
        // Pass 1: global indices.
        std::vector<const GlobalVariable *> ctors, dtors;
        for (const GlobalVariable &GV : M.globals()) {
            StringRef n = GV.getName();
            if (n == "llvm.used" || n == "llvm.compiler.used" || n == "llvm.global.annotations" ||
                GV.getSection() == "llvm.metadata")
                continue;
            if (n == "llvm.global_ctors") { ctors.push_back(&GV); continue; }
            if (n == "llvm.global_dtors") { dtors.push_back(&GV); continue; }
            if (n.starts_with("llvm.") || GV.hasAppendingLinkage()) fail_global(GV, "special global (appending linkage)");
            if (GV.getAddressSpace() != 0) fail_global(GV, "non-zero address space");
            bool defined = !GV.isDeclaration() && !GV.hasAvailableExternallyLinkage();
            if (!defined && GV.use_empty()) continue;
            uint32_t flags = linkage_flags(GV);
            uint32_t align = 1;
            if (GV.isThreadLocal()) flags |= GIR_GF_TLS;
            if (defined) {
                flags |= GIR_GF_DEFINED;
                if (GV.isConstant()) flags |= GIR_GF_CONST;
                if (GV.hasCommonLinkage()) flags = (flags & ~GIR_GF_DEFINED) | GIR_GF_COMMON;
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
        for (const GlobalAlias &A : M.aliases()) {
            APInt offs(64, 0);
            const Value *base = A.getAliasee()->stripAndAccumulateConstantOffsets(DL, offs, true);
            const auto *bg = dyn_cast<GlobalValue>(base);
            auto it = bg ? gmap.find(bg) : gmap.end();
            if (it == gmap.end() || !(T.globals[it->second].flags & GIR_GF_DEFINED))
                fail_global(A, "alias of something other than a defined global");
            uint32_t flags = linkage_flags(A) | GIR_GF_DEFINED | (T.globals[it->second].flags & (GIR_GF_TLS | GIR_GF_CONST));
            uint32_t g = add_global(sym_name(A), GIR_G_ALIAS, flags, T.globals[it->second].align);
            T.globals[g].func = it->second;
            T.globals[g].aux = (uint32_t)(int32_t)offs.getSExtValue();
            gmap[&A] = g;
        }
        // Pass 2: initializers and sections.
        for (const GlobalVariable &GV : M.globals()) {
            auto it = gmap.find(&GV);
            if (it == gmap.end()) continue;
            uint32_t gi = it->second;
            GirGlobal &G0 = T.globals[gi];
            if (!(G0.flags & (GIR_GF_DEFINED | GIR_GF_COMMON))) continue;
            uint64_t size = DL.getTypeAllocSize(GV.getValueType());
            if (size > 0x7FFFFFFFull) fail_global(GV, "variable above 2 GiB");
            G0.size = (uint32_t)size;
            if (G0.flags & GIR_GF_COMMON) continue;
            const Constant *C = GV.getInitializer();
            bool zero = C->isNullValue() || isa<UndefValue>(C);
            if (GV.hasSection()) {
                StringRef sn = GV.getSection();
                bool bss = sn.starts_with(".bss") || sn.starts_with(".tbss") || sn.starts_with(".sbss");
                uint32_t sf = (GV.isConstant() ? 0 : GIR_SF_WRITE) | (GV.isThreadLocal() ? GIR_SF_TLS : 0);
                if (bss && zero) sf |= GIR_SF_NOBITS | GIR_SF_WRITE;
                T.globals[gi].section = section(sn, sf, bss && zero ? 8 : 1);
                if (!(bss && zero)) zero = false;  // explicit sections are never .bss (LLVM's rule)
            }
            if (zero) {
                T.globals[gi].flags |= GIR_GF_ZERO;
                continue;
            }
            size_t at = T.data.size();
            T.data.resize(at + size, 0);
            T.globals[gi].data = (uint32_t)at;
            init(&GV, gi, C, at, 0);
            if ((T.globals[gi].flags & GIR_GF_RELOCS) && T.globals[gi].section != GIR_NONE)
                T.sections[T.globals[gi].section].flags |= GIR_SF_WRITE;
        }
        for (const GlobalVariable *GV : ctors) structors(*GV, true);
        for (const GlobalVariable *GV : dtors) structors(*GV, false);
        for (const Function &Fn : M.functions()) {
            auto it = gmap.find(&Fn);
            if (it == gmap.end() || !Fn.hasSection()) continue;
            T.globals[it->second].section = section(Fn.getSection(), GIR_SF_EXEC, 1);
        }
        // Pass 3: function bodies.
        for (const Function &Fn : M.functions()) {
            auto it = gmap.find(&Fn);
            if (it == gmap.end() || !(T.globals[it->second].flags & GIR_GF_DEFINED)) continue;
            function(Fn, it->second);
        }
        T.header.n_llvm_insts = (uint32_t)T.n_llvm_insts;
    }
};

}  // namespace

void gir_export(const Module &m, GirTables &out, size_t size_hint) {
    // Bitcode takes 6 to 11 bytes per instruction (more with debug info);
    // over-reserving only costs address space.
    if (size_hint) {
        out.insts.reserve(size_hint / 4 + 1024);
        out.opnds.reserve(size_hint / 3 + 1024);
        out.consts.reserve(size_hint / 4 + 1024);
        out.blocks.reserve(size_hint / 16 + 256);
    }
    Exporter e(m, out);
    e.run();
}

// ------------------------------------------------------------------ dump
static const char *op_name(unsigned op) {
    static const char *names[] = {
        "ret", "br", "condbr", "switch", "unreachable", "add", "sub", "mul", "sdiv", "udiv", "srem", "urem", "and",
        "or", "xor", "shl", "lshr", "ashr", "icmp", "select", "zext", "sext", "trunc", "ptrtoint", "inttoptr",
        "bitcast", "alloca", "load", "store", "gep", "call", "phi", "fadd", "fsub", "fmul", "fdiv", "fneg", "fcmp",
        "fpext", "fptrunc", "fptosi", "fptoui", "sitofp", "uitofp", "extractvalue", "insertvalue", "extractelt",
        "insertelt", "shuffle", "dynalloca", "stacksave", "stackrestore", "vastart", "memcpy", "memset", "ctlz",
        "cttz", "ctpop", "bswap", "bitreverse", "fshl", "fshr", "ovf", "scmp", "ucmp", "fabs", "copysign", "fsqrt",
        "isfpclass", "cmpxchg", "atomicrmw", "fence", "tlsaddr", "frameaddr", "retaddr", "sjlj_setjmp",
        "sjlj_longjmp", "trap", "debugtrap", "indirectbr", "blockaddr", "x86", "asm"};
    static_assert(sizeof(names) / sizeof(names[0]) == GIR_OP_COUNT, "op names");
    return op < GIR_OP_COUNT ? names[op] : "?";
}
static std::string ty_name(const GirModule &m, unsigned t) {
    static const char *names[] = {"void", "i1", "i8", "i16", "i32", "i64", "ptr", "f32", "f64", "f80", "i128", "f16"};
    if (t <= GIR_T_F16) return names[t];
    if (t >= m.n_types) return "?";
    const GirTypeDef &d = m.types[t];
    switch (d.kind) {
    case GIR_TK_INT: return "i" + std::to_string(d.bits);
    case GIR_TK_VECTOR: return "<" + std::to_string(d.n) + " x " + ty_name(m, d.elems) + ">";
    case GIR_TK_ARRAY: return "[" + std::to_string(d.n) + " x " + ty_name(m, d.elems) + "]";
    case GIR_TK_STRUCT: {
        std::string s = "{";
        for (uint32_t i = 0; i < d.n; i++)
            s += (i ? ", " : " ") + ty_name(m, m.opnds[d.elems + 2 * i]) + "@" + std::to_string(m.opnds[d.elems + 2 * i + 1]);
        return s + " }";
    }
    default: return "t" + std::to_string(t);
    }
}
static void dump_ref(const GirModule &m, uint32_t r, std::FILE *f) {
    if (r == GIR_NONE) { std::fputs("none", f); return; }
    uint32_t i = GIR_IDX(r);
    switch (GIR_KIND(r)) {
    case GIR_V_INST: std::fprintf(f, "%%%u", i); break;
    case GIR_V_ARG: std::fprintf(f, "arg%u", i); break;
    case GIR_V_CONST: {
        const GirConst &c = m.consts[i];
        std::string tn = ty_name(m, c.ty);
        if (c.hi) std::fprintf(f, "%s 0x%llx:%016llx", tn.c_str(), (unsigned long long)c.hi, (unsigned long long)c.lo);
        else if (c.data != GIR_NONE) std::fprintf(f, "%s data@%u", tn.c_str(), c.data);
        else std::fprintf(f, "%s %lld", tn.c_str(), (long long)c.lo);
        break;
    }
    default: std::fprintf(f, "@%.*s", (int)m.globals[i].name_len, (const char *)m.strtab + m.globals[i].name); break;
    }
}

void gir_dump(const GirModule &m, std::FILE *f) {
    static const char *preds[] = {"eq", "ne", "ugt", "uge", "ult", "ule", "sgt", "sge", "slt", "sle"};
    std::fprintf(f, "gir version %u flags=%u tls_get_addr=%d types=%u\n", m.header->version, m.header->flags,
                 (int)m.header->tls_get_addr, m.n_types);
    for (uint32_t s = 0; s < m.n_sections; s++)
        std::fprintf(f, "section %u %.*s flags=%u type=%u\n", s, (int)m.sections[s].name_len,
                     (const char *)m.strtab + m.sections[s].name, m.sections[s].flags, m.sections[s].type);
    for (uint32_t g = 0; g < m.n_globals; g++) {
        const GirGlobal &G = m.globals[g];
        static const char *kinds[] = {"func", "var", "alias"};
        std::fprintf(f, "global %u %s @%.*s flags=0x%x align=%u size=%u data=%u func=%d section=%d aux=%d\n", g,
                     G.kind < 3 ? kinds[G.kind] : "?", (int)G.name_len, (const char *)m.strtab + G.name, G.flags,
                     G.align, G.size, G.data, (int)G.func, (int)G.section, (int)G.aux);
    }
    for (uint32_t i = 0; i < m.n_drelocs; i++)
        std::fprintf(f, "dreloc owner=%u off=%u target=%u kind=%u addend=%lld block=%u block2=%u\n", m.drelocs[i].owner,
                     m.drelocs[i].offset, m.drelocs[i].target, m.drelocs[i].kind, (long long)m.drelocs[i].addend,
                     m.drelocs[i].block, m.drelocs[i].block2);
    for (uint32_t fi = 0; fi < m.n_funcs; fi++) {
        const GirFunc &F = m.funcs[fi];
        const GirGlobal &G = m.globals[F.global];
        std::fprintf(f, "\nfunc %u @%.*s(", fi, (int)G.name_len, (const char *)m.strtab + G.name);
        for (uint32_t a = 0; a < F.n_args; a++) {
            uint32_t w = m.opnds[F.args + 2 * a + 1];
            std::fprintf(f, "%s%s", a ? ", " : "", ty_name(m, m.opnds[F.args + 2 * a]).c_str());
            if (w & GIR_ABI_BYVAL) std::fprintf(f, " byval(%u, align %u)", GIR_ABI_SIZE(w), 1u << GIR_ABI_ALIGN_LOG2(w));
            if (w & GIR_ABI_SRET) std::fputs(" sret", f);
        }
        std::fprintf(f, ") -> %s flags=0x%x dbg=%u\n", ty_name(m, F.ret_ty).c_str(), F.flags, F.dbg);
        for (uint32_t b = 0; b < F.n_blocks; b++) {
            const GirBlock &B = m.blocks[F.first_block + b];
            std::fprintf(f, " b%u:\n", b);
            for (uint32_t k = B.first_inst; k < B.first_inst + B.n_inst; k++) {
                const GirInst &I = m.insts[k];
                std::fprintf(f, "  %%%u = %s %s", k, op_name(I.op), ty_name(m, I.ty).c_str());
                if (I.flags) std::fprintf(f, " [flags 0x%x]", I.flags);
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
                case GIR_INDIRECTBR:
                    std::fputc(' ', f); dump_ref(m, I.a, f);
                    for (uint32_t c = 0; c < I.c; c++) std::fprintf(f, ", b%u", m.opnds[I.b + c]);
                    break;
                case GIR_ICMP:
                    std::fprintf(f, " %s %s ", preds[I.sub % 10], ty_name(m, I.aux).c_str());
                    dump_ref(m, I.a, f); std::fputs(", ", f); dump_ref(m, I.b, f);
                    break;
                case GIR_FCMP:
                    std::fprintf(f, " pred%u %s ", I.sub, ty_name(m, I.aux).c_str());
                    dump_ref(m, I.a, f); std::fputs(", ", f); dump_ref(m, I.b, f);
                    break;
                case GIR_ALLOCA: std::fprintf(f, " size=%u align=%u", I.a, I.b); break;
                case GIR_DYNALLOCA: std::fputc(' ', f); dump_ref(m, I.a, f); std::fprintf(f, " align=%u", I.b); break;
                case GIR_STORE:
                    std::fprintf(f, " %s ", ty_name(m, I.aux).c_str());
                    dump_ref(m, I.a, f); std::fputs(", ", f); dump_ref(m, I.b, f);
                    break;
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
                    std::fputc(' ', f); dump_ref(m, I.a, f); std::fputc('(', f);
                    for (uint32_t c = 0; c < I.c; c++) {
                        if (c) std::fputs(", ", f);
                        dump_ref(m, m.opnds[I.b + 2 * c], f);
                        if (m.opnds[I.b + 2 * c + 1]) std::fprintf(f, " [abi 0x%x]", m.opnds[I.b + 2 * c + 1]);
                    }
                    std::fputc(')', f);
                    break;
                case GIR_PHI:
                    for (uint32_t c = 0; c < I.c; c++) {
                        std::fputs(c ? ", [" : " [", f); dump_ref(m, m.opnds[I.b + 2 * c], f);
                        std::fprintf(f, ", b%u]", m.opnds[I.b + 2 * c + 1]);
                    }
                    break;
                case GIR_SHUFFLE:
                    std::fputc(' ', f); dump_ref(m, I.a, f); std::fputs(", ", f); dump_ref(m, I.b, f);
                    std::fputs(" mask", f);
                    for (uint32_t c = 0; c < m.types[I.ty].n; c++) std::fprintf(f, " %d", (int)m.opnds[I.c + c]);
                    break;
                case GIR_EXTRACTVALUE: std::fputc(' ', f); dump_ref(m, I.a, f); std::fprintf(f, " @%u", I.b); break;
                case GIR_INSERTVALUE:
                    std::fputc(' ', f); dump_ref(m, I.a, f); std::fputs(", ", f); dump_ref(m, I.b, f);
                    std::fprintf(f, " @%u", I.c);
                    break;
                case GIR_MEMCPY: case GIR_MEMSET:
                    std::fputc(' ', f); dump_ref(m, I.a, f); std::fputs(", ", f); dump_ref(m, I.b, f);
                    std::fprintf(f, ", %u", I.c);
                    break;
                case GIR_TLSADDR: std::fprintf(f, " @%.*s", (int)m.globals[I.a].name_len, (const char *)m.strtab + m.globals[I.a].name); break;
                case GIR_BLOCKADDR: std::fprintf(f, " global%u b%u", I.a, I.b); break;
                case GIR_FRAMEADDR: case GIR_RETADDR: std::fprintf(f, " %u", I.a); break;
                case GIR_UNREACHABLE: case GIR_TRAP: case GIR_DEBUGTRAP: case GIR_STACKSAVE: case GIR_FENCE: break;
                default: {
                    if (I.sub) std::fprintf(f, " sub%u", I.sub);
                    if ((I.op >= GIR_ZEXT && I.op <= GIR_BITCAST) || (I.op >= GIR_FPEXT && I.op <= GIR_UITOFP))
                        std::fprintf(f, " from %s", ty_name(m, I.aux).c_str());
                    std::fputc(' ', f);
                    dump_ref(m, I.a, f);
                    if (I.b || I.op == GIR_SELECT || I.op <= GIR_ASHR) { std::fputs(", ", f); dump_ref(m, I.b, f); }
                    if (I.op == GIR_SELECT || I.op == GIR_INSERTELT || I.op == GIR_FSHL || I.op == GIR_FSHR || I.op == GIR_CMPXCHG) {
                        std::fputs(", ", f); dump_ref(m, I.c, f);
                    }
                }
                }
                if (I.dbg) std::fprintf(f, "  !%u:%u", m.dlocs[I.dbg].line, m.dlocs[I.dbg].col);
                std::fputc('\n', f);
            }
        }
    }
}
