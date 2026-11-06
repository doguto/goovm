// LLVM debug metadata -> GIR DIE tables. A port of the parts of LLVM 20's
// DwarfDebug, DwarfCompileUnit and DwarfUnit that run for one compile unit
// at -O0 with DWARF 5 and GDB tuning (lib/CodeGen/AsmPrinter, llvmorg-20.1.2):
// the function names below are LLVM's. The DIE tree is built with children
// appended as LLVM appends them (a type DIE goes to its context when it is
// first referenced), in LLVM's order of events:
//   beginModule      the unit, global variables, enums, retained types
//   per function     the subprogram DIE (low/high pc, frame base), its
//                    variables (location only), lexical blocks
//   endModule        imported entities; the subprogram attributes
//                    (finishSubprogramDefinitions), the variables' names
//                    and types (finishEntityDefinitions), containing types
// and is then written in pre-order to T.dies / T.dattrs.
//
// Not ported: inlined subroutines (always_inline code at -O0: its
// locations go to the line table, its scopes to the enclosing function),
// location lists (-O0 variables live in memory), call-site entries,
// accelerator tables, type units, split DWARF, macros.
#include "gir_dwarf.h"

#include <algorithm>
#include <map>

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/BinaryFormat/Dwarf.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"

using namespace llvm;

namespace {

constexpr uint32_t NO = GIR_NONE;

struct Node {
    uint16_t tag;
    uint32_t parent;
    std::vector<uint32_t> kids;
    std::vector<GirDAttr> attrs;
};

// A lexical scope of the function being processed (LexicalScopes).
struct LScope {
    const DILocalScope *node;
    int parent;                    // index, -1 for the function scope
    std::vector<int> kids;
    std::map<unsigned, uint32_t> args;   // arg number -> variable entity
    std::vector<uint32_t> locals;        // variable entities, in collection order
    std::vector<uint32_t> labels;
    std::vector<const DIImportedEntity *> decls;   // local imported entities
};

// A variable or label whose common attributes are added at the end
// (finishEntityDefinitions).
struct Entity {
    uint32_t die;
    const DILocalVariable *var;
    const DILabel *label;
    uint32_t inst;
};

void put_uleb(std::vector<uint8_t> &o, uint64_t x) {
    do {
        uint8_t b = x & 0x7F;
        x >>= 7;
        o.push_back(x ? (uint8_t)(b | 0x80) : b);
    } while (x);
}
void put_sleb(std::vector<uint8_t> &o, int64_t x) {
    while (true) {
        uint8_t b = x & 0x7F;
        x >>= 7;
        if ((x == 0 && !(b & 0x40)) || (x == -1 && (b & 0x40))) {
            o.push_back(b);
            return;
        }
        o.push_back(b | 0x80);
    }
}

}  // namespace

struct GirDwarfBuilder::Impl {
    const Module &M;
    GirTables &T;
    GirDwarfHost &H;
    const DICompileUnit *CU = nullptr;
    dwarf::SourceLanguage lang = (dwarf::SourceLanguage)0;
    bool minimal = false;    // -gline-tables-only
    std::vector<Node> nodes;
    DenseMap<const MDNode *, uint32_t> dmap;   // DINode -> DIE
    uint32_t index_ty = NO;
    std::vector<const DISubprogram *> processed_sps;
    std::vector<Entity> entities;
    std::vector<std::pair<uint32_t, const DIType *>> containing;
    DenseMap<const DILexicalBlock *, uint32_t> lexical_dies;
    std::vector<const DIImportedEntity *> deferred_decls;
    DenseMap<const DIGlobalVariable *, SmallVector<std::pair<const GlobalVariable *, const DIExpression *>, 1>> gvmap;

    Impl(const Module &m, GirTables &t, GirDwarfHost &h) : M(m), T(t), H(h) {
        for (const DICompileUnit *C : M.debug_compile_units()) {
            if (C->getEmissionKind() == DICompileUnit::NoDebug) continue;
            CU = C;
            break;
        }
        if (CU) {
            lang = (dwarf::SourceLanguage)CU->getSourceLanguage();
            minimal = CU->getEmissionKind() == DICompileUnit::LineTablesOnly;
        }
    }

    // ------------------------------------------------------------ DIEs
    uint32_t new_die(uint16_t tag, uint32_t parent, const MDNode *N = nullptr) {
        nodes.push_back(Node{tag, parent, {}, {}});
        uint32_t d = (uint32_t)nodes.size() - 1;
        if (parent != NO) nodes[parent].kids.push_back(d);
        if (N) dmap[N] = d;
        return d;
    }
    uint32_t get_die(const MDNode *N) const {
        auto it = dmap.find(N);
        return it == dmap.end() ? NO : it->second;
    }
    void attr(uint32_t d, uint16_t at, uint16_t form, uint64_t val, uint32_t aux = 0) {
        nodes[d].attrs.push_back(GirDAttr{at, form, aux, val});
    }
    static uint16_t best_form(bool sgn, uint64_t v) {
        if (sgn) {
            int64_t s = (int64_t)v;
            if (s == (int8_t)s) return dwarf::DW_FORM_data1;
            if (s == (int16_t)s) return dwarf::DW_FORM_data2;
            if (s == (int32_t)s) return dwarf::DW_FORM_data4;
            return dwarf::DW_FORM_data8;
        }
        if (v <= 0xFF) return dwarf::DW_FORM_data1;
        if (v <= 0xFFFF) return dwarf::DW_FORM_data2;
        if (v <= 0xFFFFFFFFull) return dwarf::DW_FORM_data4;
        return dwarf::DW_FORM_data8;
    }
    void add_uint(uint32_t d, uint16_t at, uint64_t v) { attr(d, at, best_form(false, v), v); }
    void add_sint(uint32_t d, uint16_t at, int64_t v) { attr(d, at, best_form(true, (uint64_t)v), (uint64_t)v); }
    void add_flag(uint32_t d, uint16_t at) { attr(d, at, dwarf::DW_FORM_flag_present, 1); }
    void add_string(uint32_t d, uint16_t at, StringRef s) { attr(d, at, GIR_DF_STR, H.dw_str(s)); }
    void add_ref(uint32_t d, uint16_t at, uint32_t target) { attr(d, at, dwarf::DW_FORM_ref4, target); }
    void add_block(uint32_t d, uint16_t at, uint16_t form, const std::vector<uint8_t> &b) {
        attr(d, at, form, H.dw_bytes(b.data(), b.size()), (uint32_t)b.size());
    }
    void add_type(uint32_t d, const DIType *Ty, uint16_t at = dwarf::DW_AT_type) {
        uint32_t t = get_type(Ty);
        if (t != NO) add_ref(d, at, t);
    }
    void add_source_line(uint32_t d, unsigned line, unsigned col, const DIFile *F) {
        if (line == 0) return;
        attr(d, dwarf::DW_AT_decl_file, GIR_DF_FILE, H.dw_file(F));
        add_uint(d, dwarf::DW_AT_decl_line, line);
        if (col) add_uint(d, dwarf::DW_AT_decl_column, col);
    }
    void add_access(uint32_t d, DINode::DIFlags f) {
        auto a = f & DINode::FlagAccessibility;
        if (a == DINode::FlagProtected) attr(d, dwarf::DW_AT_accessibility, dwarf::DW_FORM_data1, dwarf::DW_ACCESS_protected);
        else if (a == DINode::FlagPrivate) attr(d, dwarf::DW_AT_accessibility, dwarf::DW_FORM_data1, dwarf::DW_ACCESS_private);
        else if (a == DINode::FlagPublic) attr(d, dwarf::DW_AT_accessibility, dwarf::DW_FORM_data1, dwarf::DW_ACCESS_public);
    }
    void add_linkage_name(uint32_t d, StringRef n) {
        if (!n.empty()) add_string(d, dwarf::DW_AT_linkage_name, GlobalValue::dropLLVMManglingEscape(n));
    }
    void add_const_value(uint32_t d, bool uns, uint64_t v) {
        attr(d, dwarf::DW_AT_const_value, uns ? dwarf::DW_FORM_udata : dwarf::DW_FORM_sdata, v);
    }
    void add_const_value(uint32_t d, const APInt &v, bool uns) {
        if (v.getBitWidth() <= 64) {
            add_const_value(d, uns, uns ? v.getZExtValue() : (uint64_t)v.getSExtValue());
            return;
        }
        std::vector<uint8_t> b;
        for (unsigned i = 0; i < v.getBitWidth() / 8; i++) b.push_back((uint8_t)v.extractBitsAsZExtValue(8, i * 8));
        add_block(d, dwarf::DW_AT_const_value, b.size() <= 0xFF ? dwarf::DW_FORM_block1 : dwarf::DW_FORM_block2, b);
    }
    bool is_unsigned(const DIType *Ty) {
        if (!Ty) return false;
        if (isa<DIStringType>(Ty)) return true;
        if (auto *CT = dyn_cast<DICompositeType>(Ty)) {
            if (CT->getTag() == dwarf::DW_TAG_enumeration_type) return CT->getBaseType() && is_unsigned(CT->getBaseType());
            return true;
        }
        if (auto *DT = dyn_cast<DIDerivedType>(Ty)) {
            unsigned t = DT->getTag();
            if (t == dwarf::DW_TAG_pointer_type || t == dwarf::DW_TAG_ptr_to_member_type ||
                t == dwarf::DW_TAG_reference_type || t == dwarf::DW_TAG_rvalue_reference_type)
                return true;
            return is_unsigned(DT->getBaseType());
        }
        auto *BT = dyn_cast<DIBasicType>(Ty);
        if (!BT) return false;
        unsigned e = BT->getEncoding();
        return e == dwarf::DW_ATE_unsigned || e == dwarf::DW_ATE_unsigned_char || e == dwarf::DW_ATE_UTF ||
               e == dwarf::DW_ATE_boolean || e == dwarf::DW_ATE_unsigned_fixed ||
               Ty->getTag() == dwarf::DW_TAG_unspecified_type;
    }
    uint64_t base_type_size(const DIType *Ty) {
        auto *DT = dyn_cast<DIDerivedType>(Ty);
        if (!DT) return Ty->getSizeInBits();
        unsigned t = DT->getTag();
        if (t != dwarf::DW_TAG_member && t != dwarf::DW_TAG_typedef && t != dwarf::DW_TAG_const_type &&
            t != dwarf::DW_TAG_volatile_type && t != dwarf::DW_TAG_restrict_type && t != dwarf::DW_TAG_atomic_type &&
            t != dwarf::DW_TAG_immutable_type && t != dwarf::DW_TAG_template_alias)
            return DT->getSizeInBits();
        const DIType *B = DT->getBaseType();
        if (!B) return 0;
        if (B->getTag() == dwarf::DW_TAG_reference_type || B->getTag() == dwarf::DW_TAG_rvalue_reference_type)
            return Ty->getSizeInBits();
        return base_type_size(B);
    }
    int64_t default_lower_bound() const {
        switch (lang) {
        case dwarf::DW_LANG_C: case dwarf::DW_LANG_C89: case dwarf::DW_LANG_C_plus_plus:
        case dwarf::DW_LANG_C99: case dwarf::DW_LANG_ObjC: case dwarf::DW_LANG_ObjC_plus_plus:
        case dwarf::DW_LANG_D: case dwarf::DW_LANG_Java: case dwarf::DW_LANG_Python: case dwarf::DW_LANG_UPC:
        case dwarf::DW_LANG_BLISS: case dwarf::DW_LANG_C11: case dwarf::DW_LANG_C_plus_plus_03:
        case dwarf::DW_LANG_C_plus_plus_11: case dwarf::DW_LANG_C_plus_plus_14: case dwarf::DW_LANG_Dylan:
        case dwarf::DW_LANG_Go: case dwarf::DW_LANG_Haskell: case dwarf::DW_LANG_OCaml: case dwarf::DW_LANG_OpenCL:
        case dwarf::DW_LANG_RenderScript: case dwarf::DW_LANG_Rust: case dwarf::DW_LANG_Swift:
            return 0;
        case dwarf::DW_LANG_Fortran77: case dwarf::DW_LANG_Fortran90: case dwarf::DW_LANG_Fortran95:
        case dwarf::DW_LANG_Ada83: case dwarf::DW_LANG_Ada95: case dwarf::DW_LANG_Cobol74: case dwarf::DW_LANG_Cobol85:
        case dwarf::DW_LANG_Modula2: case dwarf::DW_LANG_Pascal83: case dwarf::DW_LANG_PLI:
        case dwarf::DW_LANG_Fortran03: case dwarf::DW_LANG_Fortran08: case dwarf::DW_LANG_Julia:
        case dwarf::DW_LANG_Modula3:
            return 1;
        default:
            return -1;
        }
    }

    // ---------------------------------------------------- DWARF expressions
    // A DIExpression as DWARF operations (a memory location, as
    // DwarfExpression::addExpression writes it). False if it uses an LLVM
    // operation that has no plain DWARF form here.
    bool expr_bytes(const DIExpression *E, std::vector<uint8_t> &o) {
        if (!E) return true;
        for (auto Op : E->expr_ops()) {
            uint64_t op = Op.getOp();
            switch (op) {
            case dwarf::DW_OP_LLVM_fragment: {
                uint64_t off = Op.getArg(0), size = Op.getArg(1);
                if (off % 8 || size % 8) return false;
                // (a gap before the piece would need an empty piece first)
                if (off) {
                    o.insert(o.begin(), {(uint8_t)dwarf::DW_OP_piece});
                    std::vector<uint8_t> g;
                    put_uleb(g, off / 8);
                    o.insert(o.begin() + 1, g.begin(), g.end());
                }
                o.push_back(dwarf::DW_OP_piece);
                put_uleb(o, size / 8);
                break;
            }
            case dwarf::DW_OP_constu: {
                uint64_t v = Op.getArg(0);
                if (v < 32) o.push_back((uint8_t)(dwarf::DW_OP_lit0 + v));
                else if (v == ~0ull) {
                    o.push_back(dwarf::DW_OP_lit0);
                    o.push_back(dwarf::DW_OP_not);
                } else {
                    o.push_back(dwarf::DW_OP_constu);
                    put_uleb(o, v);
                }
                break;
            }
            case dwarf::DW_OP_consts:
                o.push_back(dwarf::DW_OP_consts);
                put_sleb(o, (int64_t)Op.getArg(0));
                break;
            case dwarf::DW_OP_plus_uconst:
                o.push_back(dwarf::DW_OP_plus_uconst);
                put_uleb(o, Op.getArg(0));
                break;
            case dwarf::DW_OP_deref_size:
            case dwarf::DW_OP_pick:
                o.push_back((uint8_t)op);
                o.push_back((uint8_t)Op.getArg(0));
                break;
            case dwarf::DW_OP_deref: case dwarf::DW_OP_plus: case dwarf::DW_OP_minus: case dwarf::DW_OP_mul:
            case dwarf::DW_OP_div: case dwarf::DW_OP_mod: case dwarf::DW_OP_or: case dwarf::DW_OP_and:
            case dwarf::DW_OP_xor: case dwarf::DW_OP_shl: case dwarf::DW_OP_shr: case dwarf::DW_OP_shra:
            case dwarf::DW_OP_not: case dwarf::DW_OP_neg: case dwarf::DW_OP_dup: case dwarf::DW_OP_swap:
            case dwarf::DW_OP_over: case dwarf::DW_OP_stack_value: case dwarf::DW_OP_xderef:
            case dwarf::DW_OP_eq: case dwarf::DW_OP_ne: case dwarf::DW_OP_gt: case dwarf::DW_OP_ge:
            case dwarf::DW_OP_lt: case dwarf::DW_OP_le: case dwarf::DW_OP_push_object_address:
                o.push_back((uint8_t)op);
                break;
            default:
                if (op >= dwarf::DW_OP_lit0 && op <= dwarf::DW_OP_lit31) {
                    o.push_back((uint8_t)op);
                    break;
                }
                return false;
            }
        }
        return true;
    }
    // A count byte and the bytes, in dstr (0: none).
    uint32_t counted(const std::vector<uint8_t> &b) {
        if (b.empty()) return 0;
        std::vector<uint8_t> c;
        c.push_back((uint8_t)b.size());
        c.insert(c.end(), b.begin(), b.end());
        return H.dw_bytes(c.data(), c.size());
    }
    void add_expr_block(uint32_t d, uint16_t at, const DIExpression *E) {
        std::vector<uint8_t> b;
        if (expr_bytes(E, b)) add_block(d, at, dwarf::DW_FORM_exprloc, b);
    }

    // -------------------------------------------------------- contexts
    uint32_t unit() const { return 0; }
    uint32_t context_die(const DIScope *C) {
        if (!C || isa<DIFile>(C) || isa<DICompileUnit>(C)) return unit();
        if (auto *LS = dyn_cast<DILocalScope>(C)) {
            if (auto *LF = dyn_cast<DILexicalBlockFile>(LS)) LS = LF->getNonLexicalBlockFileScope();
            if (auto *LB = dyn_cast<DILexicalBlock>(LS)) {
                auto it = lexical_dies.find(LB);
                if (it != lexical_dies.end()) return it->second;
                // no concrete block (yet): the enclosing subprogram
                return context_die(LB->getSubprogram());
            }
        }
        if (auto *Ty = dyn_cast<DIType>(C)) {
            uint32_t d = get_type(Ty);
            return d == NO ? unit() : d;
        }
        if (auto *NS = dyn_cast<DINamespace>(C)) return get_namespace(NS);
        if (auto *SP = dyn_cast<DISubprogram>(C)) return get_subprogram(SP);
        if (auto *Mo = dyn_cast<DIModule>(C)) return get_module(Mo);
        uint32_t d = get_die(C);
        return d == NO ? unit() : d;
    }
    uint32_t get_namespace(const DINamespace *NS) {
        uint32_t ctx = context_die(NS->getScope());
        uint32_t d = get_die(NS);
        if (d != NO) return d;
        d = new_die(dwarf::DW_TAG_namespace, ctx, NS);
        if (!NS->getName().empty()) add_string(d, dwarf::DW_AT_name, NS->getName());
        if (NS->getExportSymbols()) add_flag(d, dwarf::DW_AT_export_symbols);
        return d;
    }
    uint32_t get_module(const DIModule *Mo) {
        uint32_t ctx = context_die(Mo->getScope());
        uint32_t d = get_die(Mo);
        if (d != NO) return d;
        d = new_die(dwarf::DW_TAG_module, ctx, Mo);
        if (!Mo->getName().empty()) add_string(d, dwarf::DW_AT_name, Mo->getName());
        if (!Mo->getConfigurationMacros().empty())
            add_string(d, dwarf::DW_AT_LLVM_config_macros, Mo->getConfigurationMacros());
        if (!Mo->getIncludePath().empty()) add_string(d, dwarf::DW_AT_LLVM_include_path, Mo->getIncludePath());
        if (!Mo->getAPINotesFile().empty()) add_string(d, dwarf::DW_AT_LLVM_apinotes, Mo->getAPINotesFile());
        if (Mo->getFile()) attr(d, dwarf::DW_AT_decl_file, GIR_DF_FILE, H.dw_file(Mo->getFile()));
        if (Mo->getLineNo()) add_uint(d, dwarf::DW_AT_decl_line, Mo->getLineNo());
        if (Mo->getIsDecl()) add_flag(d, dwarf::DW_AT_declaration);
        return d;
    }

    // ------------------------------------------------------------ types
    uint32_t get_type(const DIType *Ty) {
        if (!Ty) return NO;
        uint32_t ctx = context_die(Ty->getScope());
        uint32_t d = get_die(Ty);
        if (d != NO) return d;
        d = new_die(Ty->getTag(), ctx, Ty);
        if (auto *CT = dyn_cast<DICompositeType>(Ty)) construct_composite(d, CT);
        else if (auto *BT = dyn_cast<DIBasicType>(Ty)) construct_basic(d, BT);
        else if (auto *ST = dyn_cast<DIStringType>(Ty)) construct_string(d, ST);
        else if (auto *SRT = dyn_cast<DISubroutineType>(Ty)) construct_subroutine(d, SRT);
        else construct_derived(d, cast<DIDerivedType>(Ty));
        return d;
    }
    void construct_basic(uint32_t d, const DIBasicType *BT) {
        if (!BT->getName().empty()) add_string(d, dwarf::DW_AT_name, BT->getName());
        if (BT->getTag() == dwarf::DW_TAG_unspecified_type) return;
        if (BT->getTag() != dwarf::DW_TAG_string_type)
            attr(d, dwarf::DW_AT_encoding, dwarf::DW_FORM_data1, BT->getEncoding());
        add_uint(d, dwarf::DW_AT_byte_size, BT->getSizeInBits() >> 3);
        if (BT->isBigEndian()) add_uint(d, dwarf::DW_AT_endianity, dwarf::DW_END_big);
        else if (BT->isLittleEndian()) add_uint(d, dwarf::DW_AT_endianity, dwarf::DW_END_little);
        if (uint32_t n = BT->getNumExtraInhabitants()) add_uint(d, dwarf::DW_AT_LLVM_num_extra_inhabitants, n);
    }
    void construct_string(uint32_t d, const DIStringType *ST) {
        if (!ST->getName().empty()) add_string(d, dwarf::DW_AT_name, ST->getName());
        if (DIVariable *V = ST->getStringLength()) {
            uint32_t vd = get_die(V);
            if (vd != NO) add_ref(d, dwarf::DW_AT_string_length, vd);
        } else if (DIExpression *E = ST->getStringLengthExp()) {
            add_expr_block(d, dwarf::DW_AT_string_length, E);
        } else {
            add_uint(d, dwarf::DW_AT_byte_size, ST->getSizeInBits() >> 3);
        }
        if (DIExpression *E = ST->getStringLocationExp()) add_expr_block(d, dwarf::DW_AT_data_location, E);
        if (ST->getEncoding()) attr(d, dwarf::DW_AT_encoding, dwarf::DW_FORM_data1, ST->getEncoding());
    }
    void construct_derived(uint32_t d, const DIDerivedType *DT) {
        uint64_t size = DT->getSizeInBits() >> 3;
        uint16_t tag = DT->getTag();
        if (const DIType *From = DT->getBaseType()) add_type(d, From);
        if (!DT->getName().empty()) add_string(d, dwarf::DW_AT_name, DT->getName());
        add_annotations(d, DT->getAnnotations());
        if (tag == dwarf::DW_TAG_typedef && DT->getAlignInBytes())
            attr(d, dwarf::DW_AT_alignment, dwarf::DW_FORM_udata, DT->getAlignInBytes());
        if (size && tag != dwarf::DW_TAG_pointer_type && tag != dwarf::DW_TAG_ptr_to_member_type &&
            tag != dwarf::DW_TAG_reference_type && tag != dwarf::DW_TAG_rvalue_reference_type)
            add_uint(d, dwarf::DW_AT_byte_size, size);
        if (tag == dwarf::DW_TAG_ptr_to_member_type) {
            uint32_t c = get_type(DT->getClassType());
            if (c != NO) add_ref(d, dwarf::DW_AT_containing_type, c);
        }
        add_access(d, DT->getFlags());
        if (!DT->isForwardDecl()) add_source_line(d, DT->getLine(), 0, DT->getFile());
        if (DT->getDWARFAddressSpace())
            attr(d, dwarf::DW_AT_address_class, dwarf::DW_FORM_data4, *DT->getDWARFAddressSpace());
        if (tag == dwarf::DW_TAG_template_alias) add_template_params(d, DT->getTemplateParams());
    }
    // Returns the object pointer parameter DIE, if any.
    uint32_t subprogram_arguments(uint32_t d, DITypeRefArray Args) {
        uint32_t objptr = NO;
        for (unsigned i = 1, n = Args.size(); i < n; i++) {
            const DIType *Ty = Args[i];
            if (!Ty) {
                new_die(dwarf::DW_TAG_unspecified_parameters, d);
            } else {
                uint32_t a = new_die(dwarf::DW_TAG_formal_parameter, d);
                add_type(a, Ty);
                if (Ty->isArtificial()) add_flag(a, dwarf::DW_AT_artificial);
                if (Ty->isObjectPointer()) objptr = a;
            }
        }
        return objptr;
    }
    void construct_subroutine(uint32_t d, const DISubroutineType *CT) {
        auto E = CT->getTypeArray();
        if (E.size())
            if (const DIType *R = E[0]) add_type(d, R);
        bool proto = !(E.size() == 2 && !E[1]);
        subprogram_arguments(d, E);
        if (proto && dwarf::isC(lang)) add_flag(d, dwarf::DW_AT_prototyped);
        if (CT->getCC() && CT->getCC() != dwarf::DW_CC_normal)
            attr(d, dwarf::DW_AT_calling_convention, dwarf::DW_FORM_data1, CT->getCC());
        if (CT->isLValueReference()) add_flag(d, dwarf::DW_AT_reference);
        if (CT->isRValueReference()) add_flag(d, dwarf::DW_AT_rvalue_reference);
    }
    void add_annotations(uint32_t d, DINodeArray A) {
        if (!A) return;
        for (const Metadata *Ann : A->operands()) {
            const auto *MD = cast<MDNode>(Ann);
            const auto *Name = cast<MDString>(MD->getOperand(0));
            const auto &V = MD->getOperand(1);
            uint32_t a = new_die(dwarf::DW_TAG_LLVM_annotation, d);
            add_string(a, dwarf::DW_AT_name, Name->getString());
            if (const auto *S = dyn_cast<MDString>(V)) add_string(a, dwarf::DW_AT_const_value, S->getString());
            else if (const auto *C = dyn_cast<ConstantAsMetadata>(V))
                add_const_value(a, C->getValue()->getUniqueInteger(), true);
        }
    }
    void add_template_params(uint32_t d, DINodeArray P) {
        for (const auto *E : P) {
            if (auto *TTP = dyn_cast<DITemplateTypeParameter>(E)) {
                uint32_t p = new_die(dwarf::DW_TAG_template_type_parameter, d);
                if (TTP->getType()) add_type(p, TTP->getType());
                if (!TTP->getName().empty()) add_string(p, dwarf::DW_AT_name, TTP->getName());
                if (TTP->isDefault()) add_flag(p, dwarf::DW_AT_default_value);
            } else if (auto *TVP = dyn_cast<DITemplateValueParameter>(E)) {
                uint32_t p = new_die(TVP->getTag(), d);
                if (TVP->getTag() == dwarf::DW_TAG_template_value_parameter) add_type(p, TVP->getType());
                if (!TVP->getName().empty()) add_string(p, dwarf::DW_AT_name, TVP->getName());
                if (TVP->isDefault()) add_flag(p, dwarf::DW_AT_default_value);
                if (Metadata *V = TVP->getValue()) {
                    if (ConstantInt *CI = mdconst::dyn_extract<ConstantInt>(V))
                        add_const_value(p, CI->getValue(), is_unsigned(TVP->getType()));
                    else if (ConstantFP *CF = mdconst::dyn_extract<ConstantFP>(V))
                        add_const_value(p, CF->getValueAPF().bitcastToAPInt(), true);
                    else if (GlobalValue *GV = mdconst::dyn_extract<GlobalValue>(V)) {
                        uint32_t g = H.dw_global(GV);
                        if (g != NO) {
                            std::vector<uint8_t> sv{(uint8_t)dwarf::DW_OP_stack_value};
                            attr(p, dwarf::DW_AT_location, GIR_DF_GLOBAL, g, counted(sv));
                        }
                    } else if (TVP->getTag() == dwarf::DW_TAG_GNU_template_template_param) {
                        add_string(p, dwarf::DW_AT_GNU_template_name, cast<MDString>(V)->getString());
                    } else if (TVP->getTag() == dwarf::DW_TAG_GNU_template_parameter_pack) {
                        add_template_params(p, cast<MDTuple>(V));
                    }
                }
            }
        }
    }
    uint32_t get_index_ty() {
        if (index_ty != NO) return index_ty;
        index_ty = new_die(dwarf::DW_TAG_base_type, unit());
        add_string(index_ty, dwarf::DW_AT_name, "__ARRAY_SIZE_TYPE__");
        add_uint(index_ty, dwarf::DW_AT_byte_size, 8);
        attr(index_ty, dwarf::DW_AT_encoding, dwarf::DW_FORM_data1, dwarf::getArrayIndexTypeEncoding(lang));
        return index_ty;
    }
    template <class B> void bound(uint32_t d, uint16_t at, B Bound, bool count_attr) {
        if (auto *BV = dyn_cast_if_present<DIVariable *>(Bound)) {
            uint32_t vd = get_die(BV);
            if (vd != NO) add_ref(d, at, vd);
        } else if (auto *BE = dyn_cast_if_present<DIExpression *>(Bound)) {
            add_expr_block(d, at, BE);
        } else if (auto *BI = dyn_cast_if_present<ConstantInt *>(Bound)) {
            int64_t v = BI->getSExtValue();
            if (count_attr) {
                if (v != -1) add_uint(d, at, (uint64_t)v);
            } else if (at != dwarf::DW_AT_lower_bound || default_lower_bound() == -1 || v != default_lower_bound()) {
                attr(d, at, dwarf::DW_FORM_sdata, (uint64_t)v);
            }
        }
    }
    void construct_array(uint32_t d, const DICompositeType *CT) {
        if (CT->isVector()) {
            add_flag(d, dwarf::DW_AT_GNU_vector);
            const DIType *BT = CT->getBaseType();
            auto El = CT->getElements();
            int64_t n = 0;
            if (El.size() == 1)
                if (auto *SR = dyn_cast<DISubrange>(El[0]))
                    if (auto *C = dyn_cast_if_present<ConstantInt *>(SR->getCount())) n = C->getSExtValue();
            if (BT && CT->getSizeInBits() != (uint64_t)n * BT->getSizeInBits())
                add_uint(d, dwarf::DW_AT_byte_size, CT->getSizeInBits() / 8);
        }
        if (DIVariable *V = CT->getDataLocation()) {
            uint32_t vd = get_die(V);
            if (vd != NO) add_ref(d, dwarf::DW_AT_data_location, vd);
        } else if (DIExpression *E = CT->getDataLocationExp()) {
            add_expr_block(d, dwarf::DW_AT_data_location, E);
        }
        if (DIVariable *V = CT->getAssociated()) {
            uint32_t vd = get_die(V);
            if (vd != NO) add_ref(d, dwarf::DW_AT_associated, vd);
        } else if (DIExpression *E = CT->getAssociatedExp()) {
            add_expr_block(d, dwarf::DW_AT_associated, E);
        }
        if (DIVariable *V = CT->getAllocated()) {
            uint32_t vd = get_die(V);
            if (vd != NO) add_ref(d, dwarf::DW_AT_allocated, vd);
        } else if (DIExpression *E = CT->getAllocatedExp()) {
            add_expr_block(d, dwarf::DW_AT_allocated, E);
        }
        if (auto *R = CT->getRankConst()) attr(d, dwarf::DW_AT_rank, dwarf::DW_FORM_sdata, (uint64_t)R->getSExtValue());
        else if (auto *RE = CT->getRankExp()) add_expr_block(d, dwarf::DW_AT_rank, RE);
        add_type(d, CT->getBaseType());
        uint32_t idx = get_index_ty();
        for (DINode *E : CT->getElements()) {
            if (auto *SR = dyn_cast_or_null<DISubrange>(E)) {
                uint32_t s = new_die(dwarf::DW_TAG_subrange_type, d);
                add_ref(s, dwarf::DW_AT_type, idx);
                bound(s, dwarf::DW_AT_lower_bound, SR->getLowerBound(), false);
                bound(s, dwarf::DW_AT_count, SR->getCount(), true);
                bound(s, dwarf::DW_AT_upper_bound, SR->getUpperBound(), false);
                bound(s, dwarf::DW_AT_byte_stride, SR->getStride(), false);
            } else if (auto *GS = dyn_cast_or_null<DIGenericSubrange>(E)) {
                uint32_t s = new_die(dwarf::DW_TAG_generic_subrange, d);
                add_ref(s, dwarf::DW_AT_type, idx);
                auto gb = [&](uint16_t at, DIGenericSubrange::BoundType B) {
                    if (auto *BV = dyn_cast_if_present<DIVariable *>(B)) {
                        uint32_t vd = get_die(BV);
                        if (vd != NO) add_ref(s, at, vd);
                    } else if (auto *BE = dyn_cast_if_present<DIExpression *>(B)) {
                        if (BE->isConstant() &&
                            DIExpression::SignedOrUnsignedConstant::SignedConstant == *BE->isConstant()) {
                            if (at != dwarf::DW_AT_lower_bound || default_lower_bound() == -1 ||
                                (int64_t)BE->getElement(1) != default_lower_bound())
                                attr(s, at, dwarf::DW_FORM_sdata, BE->getElement(1));
                        } else {
                            add_expr_block(s, at, BE);
                        }
                    }
                };
                gb(dwarf::DW_AT_lower_bound, GS->getLowerBound());
                gb(dwarf::DW_AT_count, GS->getCount());
                gb(dwarf::DW_AT_upper_bound, GS->getUpperBound());
                gb(dwarf::DW_AT_byte_stride, GS->getStride());
            }
        }
    }
    void construct_enum(uint32_t d, const DICompositeType *CT) {
        const DIType *B = CT->getBaseType();
        bool uns = B && is_unsigned(B);
        if (B) {
            add_type(d, B);
            if (CT->getFlags() & DINode::FlagEnumClass) add_flag(d, dwarf::DW_AT_enum_class);
        }
        for (const DINode *E : CT->getElements()) {
            auto *En = dyn_cast_or_null<DIEnumerator>(E);
            if (!En) continue;
            uint32_t e = new_die(dwarf::DW_TAG_enumerator, d);
            add_string(e, dwarf::DW_AT_name, En->getName());
            add_const_value(e, En->getValue(), uns);
        }
    }
    void construct_member(uint32_t parent, const DIDerivedType *DT) {
        uint32_t d = new_die(DT->getTag(), parent);
        if (!DT->getName().empty()) add_string(d, dwarf::DW_AT_name, DT->getName());
        add_annotations(d, DT->getAnnotations());
        if (DIType *R = DT->getBaseType()) add_type(d, R);
        add_source_line(d, DT->getLine(), 0, DT->getFile());
        if (DT->getTag() == dwarf::DW_TAG_inheritance && DT->isVirtual()) {
            std::vector<uint8_t> b{(uint8_t)dwarf::DW_OP_dup, (uint8_t)dwarf::DW_OP_deref, (uint8_t)dwarf::DW_OP_constu};
            put_uleb(b, DT->getOffsetInBits());
            b.push_back(dwarf::DW_OP_minus);
            b.push_back(dwarf::DW_OP_deref);
            b.push_back(dwarf::DW_OP_plus);
            add_block(d, dwarf::DW_AT_data_member_location, dwarf::DW_FORM_exprloc, b);
        } else {
            uint64_t size = DT->getSizeInBits();
            bool bitfield = DT->isBitField();
            uint64_t off_bytes;
            if (bitfield) add_uint(d, dwarf::DW_AT_bit_size, size);
            if (bitfield) {
                add_uint(d, dwarf::DW_AT_data_bit_offset, DT->getOffsetInBits());
            } else {
                off_bytes = DT->getOffsetInBits() / 8;
                if (DT->getAlignInBytes()) attr(d, dwarf::DW_AT_alignment, dwarf::DW_FORM_udata, DT->getAlignInBytes());
                add_uint(d, dwarf::DW_AT_data_member_location, off_bytes);
            }
        }
        add_access(d, DT->getFlags());
        if (DT->isVirtual())
            attr(d, dwarf::DW_AT_virtuality, dwarf::DW_FORM_data1, dwarf::DW_VIRTUALITY_virtual);
        if (DT->isArtificial()) add_flag(d, dwarf::DW_AT_artificial);
    }
    uint32_t get_static_member(const DIDerivedType *DT) {
        if (!DT) return NO;
        uint32_t ctx = context_die(DT->getScope());
        uint32_t d = get_die(DT);
        if (d != NO) return d;
        d = new_die(DT->getTag(), ctx, DT);
        const DIType *Ty = DT->getBaseType();
        add_string(d, dwarf::DW_AT_name, DT->getName());
        add_type(d, Ty);
        add_source_line(d, DT->getLine(), 0, DT->getFile());
        add_flag(d, dwarf::DW_AT_external);
        add_flag(d, dwarf::DW_AT_declaration);
        if (DT->isArtificial()) add_flag(d, dwarf::DW_AT_artificial);
        add_access(d, DT->getFlags());
        if (const auto *CI = dyn_cast_or_null<ConstantInt>(DT->getConstant()))
            add_const_value(d, CI->getValue(), is_unsigned(Ty));
        else if (const auto *CF = dyn_cast_or_null<ConstantFP>(DT->getConstant()))
            add_const_value(d, CF->getValueAPF().bitcastToAPInt(), true);
        if (DT->getAlignInBytes()) attr(d, dwarf::DW_AT_alignment, dwarf::DW_FORM_udata, DT->getAlignInBytes());
        return d;
    }
    void construct_composite(uint32_t d, const DICompositeType *CT) {
        StringRef name = CT->getName();
        uint16_t tag = CT->getTag();
        switch (tag) {
        case dwarf::DW_TAG_array_type: construct_array(d, CT); break;
        case dwarf::DW_TAG_enumeration_type: construct_enum(d, CT); break;
        case dwarf::DW_TAG_variant_part: case dwarf::DW_TAG_structure_type: case dwarf::DW_TAG_union_type:
        case dwarf::DW_TAG_class_type: case dwarf::DW_TAG_namelist: {
            if (tag == dwarf::DW_TAG_class_type || tag == dwarf::DW_TAG_structure_type ||
                tag == dwarf::DW_TAG_union_type)
                add_template_params(d, CT->getTemplateParams());
            for (const auto *E : CT->getElements()) {
                if (!E) continue;
                if (auto *SP = dyn_cast<DISubprogram>(E)) get_subprogram(SP);
                else if (auto *DT = dyn_cast<DIDerivedType>(E)) {
                    if (DT->getTag() == dwarf::DW_TAG_friend) {
                        uint32_t f = new_die(dwarf::DW_TAG_friend, d);
                        add_type(f, DT->getBaseType(), dwarf::DW_AT_friend);
                    } else if (DT->isStaticMember()) {
                        get_static_member(DT);
                    } else if (tag == dwarf::DW_TAG_variant_part) {
                        uint32_t v = new_die(dwarf::DW_TAG_variant, d);
                        construct_member(v, DT);
                    } else {
                        construct_member(d, DT);
                    }
                } else if (auto *Co = dyn_cast<DICompositeType>(E)) {
                    if (Co->getTag() == dwarf::DW_TAG_variant_part) {
                        uint32_t vp = new_die(Co->getTag(), d);
                        construct_composite(vp, Co);
                    }
                }
            }
            if (CT->isAppleBlockExtension()) add_flag(d, dwarf::DW_AT_APPLE_block);
            if (CT->getExportSymbols()) add_flag(d, dwarf::DW_AT_export_symbols);
            if (auto *VH = CT->getVTableHolder()) {
                uint32_t h = get_type(VH);
                if (h != NO) add_ref(d, dwarf::DW_AT_containing_type, h);
            }
            if (CT->isObjcClassComplete()) add_flag(d, dwarf::DW_AT_APPLE_objc_complete_type);
            uint8_t cc = 0;
            if (CT->isTypePassByValue()) cc = dwarf::DW_CC_pass_by_value;
            else if (CT->isTypePassByReference()) cc = dwarf::DW_CC_pass_by_reference;
            if (cc) attr(d, dwarf::DW_AT_calling_convention, dwarf::DW_FORM_data1, cc);
            break;
        }
        default:
            break;
        }
        if (!name.empty()) add_string(d, dwarf::DW_AT_name, name);
        add_annotations(d, CT->getAnnotations());
        if (tag == dwarf::DW_TAG_enumeration_type || tag == dwarf::DW_TAG_class_type ||
            tag == dwarf::DW_TAG_structure_type || tag == dwarf::DW_TAG_union_type) {
            uint64_t size = CT->getSizeInBits() >> 3;
            if (size && (!CT->isForwardDecl() || tag == dwarf::DW_TAG_enumeration_type))
                add_uint(d, dwarf::DW_AT_byte_size, size);
            else if (!CT->isForwardDecl())
                add_uint(d, dwarf::DW_AT_byte_size, 0);
            if (CT->isForwardDecl()) add_flag(d, dwarf::DW_AT_declaration);
            add_access(d, CT->getFlags());
            if (!CT->isForwardDecl()) add_source_line(d, CT->getLine(), 0, CT->getFile());
            if (unsigned rl = CT->getRuntimeLang())
                attr(d, dwarf::DW_AT_APPLE_runtime_class, dwarf::DW_FORM_data1, rl);
            if (CT->getAlignInBytes()) attr(d, dwarf::DW_AT_alignment, dwarf::DW_FORM_udata, CT->getAlignInBytes());
            if (uint32_t n = CT->getNumExtraInhabitants()) add_uint(d, dwarf::DW_AT_LLVM_num_extra_inhabitants, n);
        }
    }

    // ------------------------------------------------------ subprograms
    uint32_t get_subprogram(const DISubprogram *SP) {
        uint32_t ctx = minimal ? unit() : context_die(SP->getScope());
        uint32_t d = get_die(SP);
        if (d != NO) return d;
        if (auto *Decl = SP->getDeclaration()) {
            if (!minimal) {
                ctx = unit();
                get_subprogram(Decl);
            }
        }
        d = new_die(dwarf::DW_TAG_subprogram, ctx, SP);
        if (SP->isDefinition()) return d;
        apply_subprogram_attributes(SP, d, false);
        return d;
    }
    bool apply_definition_attributes(const DISubprogram *SP, uint32_t d, bool min) {
        uint32_t decl = NO;
        StringRef decl_link;
        if (auto *Decl = SP->getDeclaration()) {
            if (!min) {
                DITypeRefArray DA = Decl->getType()->getTypeArray(), FA = SP->getType()->getTypeArray();
                if (DA.size() && FA.size())
                    if (FA[0] != nullptr && DA[0] != FA[0]) add_type(d, FA[0]);
                decl = get_die(Decl);
                decl_link = Decl->getLinkageName();
                if (H.dw_file(Decl->getFile()) != H.dw_file(SP->getFile()))
                    attr(d, dwarf::DW_AT_decl_file, GIR_DF_FILE, H.dw_file(SP->getFile()));
                if (SP->getLine() != Decl->getLine()) add_uint(d, dwarf::DW_AT_decl_line, SP->getLine());
            }
        }
        add_template_params(d, SP->getTemplateParams());
        if (decl_link.empty()) add_linkage_name(d, SP->getLinkageName());
        if (decl == NO) return false;
        add_ref(d, dwarf::DW_AT_specification, decl);
        return true;
    }
    void apply_subprogram_attributes(const DISubprogram *SP, uint32_t d, bool skip) {
        bool skip_loc = skip && !CU->getDebugInfoForProfiling();
        if (!skip_loc)
            if (apply_definition_attributes(SP, d, skip)) return;
        if (!SP->getName().empty()) add_string(d, dwarf::DW_AT_name, SP->getName());
        add_annotations(d, SP->getAnnotations());
        if (!skip_loc) add_source_line(d, SP->getLine(), 0, SP->getFile());
        if (skip) return;
        if (SP->isPrototyped() && dwarf::isC(lang)) add_flag(d, dwarf::DW_AT_prototyped);
        if (SP->isObjCDirect()) add_flag(d, dwarf::DW_AT_APPLE_objc_direct);
        unsigned cc = 0;
        DITypeRefArray Args;
        if (const DISubroutineType *Ty = SP->getType()) {
            Args = Ty->getTypeArray();
            cc = Ty->getCC();
        }
        if (cc && cc != dwarf::DW_CC_normal) attr(d, dwarf::DW_AT_calling_convention, dwarf::DW_FORM_data1, cc);
        if (Args.size())
            if (const DIType *R = Args[0]) add_type(d, R);
        if (unsigned vk = SP->getVirtuality()) {
            attr(d, dwarf::DW_AT_virtuality, dwarf::DW_FORM_data1, vk);
            if (SP->getVirtualIndex() != -1u) {
                std::vector<uint8_t> b{(uint8_t)dwarf::DW_OP_constu};
                put_uleb(b, SP->getVirtualIndex());
                add_block(d, dwarf::DW_AT_vtable_elem_location, dwarf::DW_FORM_exprloc, b);
            }
            containing.push_back({d, SP->getContainingType()});
        }
        if (!SP->isDefinition()) {
            add_flag(d, dwarf::DW_AT_declaration);
            uint32_t op = subprogram_arguments(d, Args);
            if (op != NO) add_ref(d, dwarf::DW_AT_object_pointer, op);
        }
        for (const auto *TT : SP->getThrownTypes()) {
            uint32_t t = new_die(dwarf::DW_TAG_thrown_type, d);
            add_type(t, cast<DIType>(TT));
        }
        if (SP->isArtificial()) add_flag(d, dwarf::DW_AT_artificial);
        if (!SP->isLocalToUnit()) add_flag(d, dwarf::DW_AT_external);
        if (SP->isLValueReference()) add_flag(d, dwarf::DW_AT_reference);
        if (SP->isRValueReference()) add_flag(d, dwarf::DW_AT_rvalue_reference);
        if (SP->isNoReturn()) add_flag(d, dwarf::DW_AT_noreturn);
        add_access(d, SP->getFlags());
        if (SP->isExplicit()) add_flag(d, dwarf::DW_AT_explicit);
        if (SP->isMainSubprogram()) add_flag(d, dwarf::DW_AT_main_subprogram);
        if (SP->isPure()) add_flag(d, dwarf::DW_AT_pure);
        if (SP->isElemental()) add_flag(d, dwarf::DW_AT_elemental);
        if (SP->isRecursive()) add_flag(d, dwarf::DW_AT_recursive);
        if (!SP->getTargetFuncName().empty()) add_string(d, dwarf::DW_AT_trampoline, SP->getTargetFuncName());
        if (SP->isDeleted()) add_flag(d, dwarf::DW_AT_deleted);
    }

    // ------------------------------------------------- global variables
    uint32_t get_global_variable(const DIGlobalVariable *GV,
                                 ArrayRef<std::pair<const GlobalVariable *, const DIExpression *>> exprs) {
        uint32_t d = get_die(GV);
        if (d != NO) return d;
        const DIType *GTy = GV->getType();
        uint32_t ctx = context_die(GV->getScope());
        d = new_die(GV->getTag(), ctx, GV);
        if (auto *SDM = GV->getStaticDataMemberDeclaration()) {
            uint32_t spec = get_static_member(SDM);
            if (spec != NO) add_ref(d, dwarf::DW_AT_specification, spec);
            if (GTy != SDM->getBaseType()) add_type(d, GTy);
        } else {
            if (!GV->getDisplayName().empty()) add_string(d, dwarf::DW_AT_name, GV->getDisplayName());
            if (GTy) add_type(d, GTy);
            if (!GV->isLocalToUnit()) add_flag(d, dwarf::DW_AT_external);
            add_source_line(d, GV->getLine(), 0, GV->getFile());
        }
        if (!GV->isDefinition()) add_flag(d, dwarf::DW_AT_declaration);
        add_annotations(d, GV->getAnnotations());
        if (GV->getAlignInBytes()) attr(d, dwarf::DW_AT_alignment, dwarf::DW_FORM_udata, GV->getAlignInBytes());
        if (MDTuple *TP = GV->getTemplateParams()) add_template_params(d, DINodeArray(TP));
        // location
        bool done = false;
        for (const auto &GE : exprs) {
            const GlobalVariable *G = GE.first;
            const DIExpression *E = GE.second;
            if (exprs.size() == 1 && E && E->isConstant()) {
                add_const_value(d, DIExpression::SignedOrUnsignedConstant::UnsignedConstant == *E->isConstant(),
                                E->getElement(1));
                done = true;
                break;
            }
            if (!G) continue;
            uint32_t g = H.dw_global(G);
            if (g == NO || done) continue;
            std::vector<uint8_t> b;
            if (!expr_bytes(E, b)) continue;
            attr(d, dwarf::DW_AT_location, GIR_DF_GLOBAL, g, counted(b));
            done = true;   // (fragments of several globals: the first one)
        }
        add_linkage_name(d, GV->getLinkageName());
        return d;
    }

    // -------------------------------------------------- imported entities
    uint32_t imported_entity(const DIImportedEntity *IE) {
        uint32_t d = new_die(IE->getTag(), NO, IE);
        const DINode *E = IE->getEntity();
        uint32_t ent = NO;
        if (auto *NS = dyn_cast_or_null<DINamespace>(E)) ent = get_namespace(NS);
        else if (auto *Mo = dyn_cast_or_null<DIModule>(E)) ent = get_module(Mo);
        else if (auto *SP = dyn_cast_or_null<DISubprogram>(E)) ent = get_subprogram(SP);
        else if (auto *Ty = dyn_cast_or_null<DIType>(E)) ent = get_type(Ty);
        else if (auto *GV = dyn_cast_or_null<DIGlobalVariable>(E)) ent = get_global_variable(GV, {});
        else if (auto *I2 = dyn_cast_or_null<DIImportedEntity>(E)) ent = get_imported_entity(I2);
        else if (E) ent = get_die(E);
        add_source_line(d, IE->getLine(), 0, IE->getFile());
        if (ent != NO) add_ref(d, dwarf::DW_AT_import, ent);
        if (!IE->getName().empty()) add_string(d, dwarf::DW_AT_name, IE->getName());
        for (const auto *El : IE->getElements()) {
            if (!El) continue;
            uint32_t c = imported_entity(cast<DIImportedEntity>(El));
            nodes[c].parent = d;
            nodes[d].kids.push_back(c);
        }
        return d;
    }
    uint32_t get_imported_entity(const DIImportedEntity *IE) {
        uint32_t d = get_die(IE);
        if (d != NO) return d;
        uint32_t ctx = context_die(IE->getScope());
        d = imported_entity(IE);
        nodes[d].parent = ctx;
        nodes[ctx].kids.push_back(d);
        return d;
    }

    // ------------------------------------------------------------ module
    void begin_module() {
        // the unit
        uint32_t u = new_die(dwarf::DW_TAG_compile_unit, NO);
        (void)u;
        add_string(u, dwarf::DW_AT_producer, CU->getProducer());
        attr(u, dwarf::DW_AT_language, dwarf::DW_FORM_data2, CU->getSourceLanguage());
        add_string(u, dwarf::DW_AT_name, CU->getFilename());
        attr(u, dwarf::DW_AT_str_offsets_base, GIR_DF_STR_BASE, 0);
        attr(u, dwarf::DW_AT_stmt_list, GIR_DF_STMT_LIST, 0);
        if (!CU->getDirectory().empty()) add_string(u, dwarf::DW_AT_comp_dir, CU->getDirectory());
        attr(u, dwarf::DW_AT_low_pc, GIR_DF_CU_PC, 0);
        attr(u, dwarf::DW_AT_addr_base, GIR_DF_ADDR_BASE, 0);
        // global variables, as DwarfDebug::beginModule
        for (const GlobalVariable &G : M.globals()) {
            SmallVector<DIGlobalVariableExpression *, 1> GVs;
            G.getDebugInfo(GVs);
            for (auto *GVE : GVs) gvmap[GVE->getVariable()].push_back({&G, GVE->getExpression()});
        }
        for (auto *GVE : CU->getGlobalVariables()) {
            auto &E = gvmap[GVE->getVariable()];
            auto *X = GVE->getExpression();
            if (E.empty() || (X && X->isConstant())) E.push_back({nullptr, X});
        }
        DenseSet<const DIGlobalVariable *> done;
        for (auto *GVE : CU->getGlobalVariables()) {
            const DIGlobalVariable *GV = GVE->getVariable();
            if (done.insert(GV).second) get_global_variable(GV, sorted_exprs(gvmap[GV]));
        }
        for (auto *Ty : CU->getEnumTypes()) get_type(cast<DIType>(Ty));
        for (auto *Ty : CU->getRetainedTypes())
            if (auto *RT = dyn_cast<DIType>(Ty)) get_type(RT);
    }
    SmallVector<std::pair<const GlobalVariable *, const DIExpression *>, 1>
    sorted_exprs(SmallVector<std::pair<const GlobalVariable *, const DIExpression *>, 1> v) {
        std::stable_sort(v.begin(), v.end(), [](const auto &A, const auto &B) {
            if (!A.second || !B.second) return !!B.second;
            auto FA = A.second->getFragmentInfo(), FB = B.second->getFragmentInfo();
            if (!FA || !FB) return !!FB;
            return FA->OffsetInBits < FB->OffsetInBits;
        });
        v.erase(std::unique(v.begin(), v.end(), [](const auto &A, const auto &B) { return A.second == B.second; }),
                v.end());
        return v;
    }

    // ---------------------------------------------------------- functions
    std::vector<LScope> scopes;
    DenseMap<const DILocalScope *, int> scope_of;

    int get_scope(const DILocalScope *S) {
        S = S->getNonLexicalBlockFileScope();
        auto it = scope_of.find(S);
        if (it != scope_of.end()) return it->second;
        int parent = -1;
        if (auto *LB = dyn_cast<DILexicalBlockBase>(S)) {
            parent = get_scope(LB->getScope());
            if (parent < 0) return -1;
        } else if (!scopes.empty()) {
            return -1;   // another subprogram (not inlined here)
        }
        scopes.push_back(LScope{S, parent, {}, {}, {}, {}, {}});
        int k = (int)scopes.size() - 1;
        if (parent >= 0) scopes[parent].kids.push_back(k);
        scope_of[S] = k;
        return k;
    }
    // The scope of an instruction's location: inlined code counts as the
    // call site's.
    static const DILocation *outer(const DILocation *L) {
        while (const DILocation *IA = L->getInlinedAt()) L = IA;
        return L;
    }
    int find_scope(const DILocalScope *S) {
        auto it = scope_of.find(S->getNonLexicalBlockFileScope());
        return it == scope_of.end() ? -1 : it->second;
    }

    std::vector<uint32_t> sort_locals(const std::vector<uint32_t> &in) {
        // a stable topological sort: variables referenced by other variables'
        // array bounds first (sortLocalVars)
        std::vector<uint32_t> out;
        DenseMap<const DILocalVariable *, uint32_t> byvar;
        for (uint32_t e : in) byvar[entities[e].var] = e;
        DenseSet<uint32_t> visited, visiting;
        std::vector<std::pair<uint32_t, bool>> work;
        for (auto it = in.rbegin(); it != in.rend(); ++it) work.push_back({*it, false});
        while (!work.empty()) {
            auto [e, all] = work.back();
            work.pop_back();
            if (visited.count(e)) continue;
            if (all) {
                visited.insert(e);
                out.push_back(e);
                continue;
            }
            if (!visiting.insert(e).second) continue;
            work.push_back({e, true});
            if (auto *A = dyn_cast_or_null<DICompositeType>(entities[e].var->getType()))
                if (A->getTag() == dwarf::DW_TAG_array_type)
                    for (auto *El : A->getElements())
                        if (auto *SR = dyn_cast_or_null<DISubrange>(El)) {
                            auto dep = [&](DISubrange::BoundType B) {
                                if (auto *V = dyn_cast_if_present<DIVariable *>(B))
                                    if (auto *LV = dyn_cast<DILocalVariable>(V)) {
                                        auto f = byvar.find(LV);
                                        if (f != byvar.end()) work.push_back({f->second, false});
                                    }
                            };
                            dep(SR->getLowerBound());
                            dep(SR->getCount());
                            dep(SR->getUpperBound());
                            dep(SR->getStride());
                        }
        }
        return out;
    }
    uint32_t variable_die(uint32_t e, uint32_t parent, uint32_t &objptr) {
        Entity &E = entities[e];
        uint32_t d = E.die;
        nodes[d].parent = parent;
        nodes[parent].kids.push_back(d);
        if (E.var && E.var->isObjectPointer()) objptr = d;
        return d;
    }
    uint32_t scope_children(int s, uint32_t die) {
        uint32_t objptr = NO;
        LScope &S = scopes[s];
        for (auto &a : S.args) variable_die(a.second, die, objptr);
        for (uint32_t e : sort_locals(S.locals)) variable_die(e, die, objptr);
        for (uint32_t e : S.labels) variable_die(e, die, objptr);
        if (!minimal)
            for (auto *IE : S.decls) deferred_decls.push_back(IE);
        for (int k : scopes[s].kids) {
            LScope &C = scopes[k];
            bool skip = C.args.empty() && C.locals.empty() && (minimal || C.decls.empty());
            if (skip) scope_children(k, die);
            else {
                auto *LB = cast<DILexicalBlockBase>(C.node);
                uint32_t b = new_die(dwarf::DW_TAG_lexical_block, die);
                if (auto *L = dyn_cast<DILexicalBlock>(LB)) lexical_dies[L] = b;
                attr(b, 0, GIR_DF_SCOPE_PC, H.dw_scope(LB));
                scope_children(k, b);
            }
        }
        return objptr;
    }

    void function(const Function &F, uint32_t fi, const std::vector<GirDwarfVar> &vars,
                  const std::vector<GirDwarfLabel> &labels) {
        const DISubprogram *SP = F.getSubprogram();
        if (!SP || SP->getUnit() != CU) return;
        // lexical scopes, in order of the instructions' locations
        scopes.clear();
        scope_of.clear();
        get_scope(SP);
        for (const BasicBlock &BB : F)
            for (const Instruction &I : BB)
                if (const DILocation *L = I.getDebugLoc().get()) {
                    const DILocation *O = outer(L);
                    if (O->getScope()->getSubprogram() == SP) get_scope(O->getScope());
                }
        // variables: the static-alloca ones first (LLVM's MF side table),
        // then the others, each once
        DenseSet<const DILocalVariable *> seen;
        for (int pass = 0; pass < 2; pass++)
            for (const GirDwarfVar &V : vars) {
                if (V.mf != (pass == 0) || V.loc->getInlinedAt()) continue;
                if (!seen.insert(V.var).second) continue;
                int s = find_scope(V.loc->getScope());
                if (s < 0) continue;
                uint32_t d = new_die(V.var->getArg() ? dwarf::DW_TAG_formal_parameter : dwarf::DW_TAG_variable, NO,
                                     V.var);
                std::vector<uint8_t> b;
                if (V.addr != NO && expr_bytes(V.expr, b))
                    attr(d, dwarf::DW_AT_location, GIR_DF_LOCAL, ((uint64_t)fi << 32) | V.addr, counted(b));
                entities.push_back(Entity{d, V.var, nullptr, 0});
                uint32_t e = (uint32_t)entities.size() - 1;
                if (unsigned a = V.var->getArg()) {
                    if (!scopes[s].args.count(a)) scopes[s].args[a] = e;
                } else {
                    scopes[s].locals.push_back(e);
                }
            }
        for (const GirDwarfLabel &L : labels) {
            if (L.loc && L.loc->getInlinedAt()) continue;
            int s = find_scope(L.label->getScope());
            if (s < 0) continue;
            uint32_t d = new_die(dwarf::DW_TAG_label, NO, L.label);
            entities.push_back(Entity{d, nullptr, L.label, L.inst});
            scopes[s].labels.push_back((uint32_t)entities.size() - 1);
        }
        for (const DINode *N : SP->getRetainedNodes()) {
            if (auto *LV = dyn_cast<DILocalVariable>(N)) {
                if (!seen.insert(LV).second) continue;
                int s = find_scope(LV->getScope());
                if (s < 0) continue;
                uint32_t d = new_die(LV->getArg() ? dwarf::DW_TAG_formal_parameter : dwarf::DW_TAG_variable, NO, LV);
                entities.push_back(Entity{d, LV, nullptr, 0});
                uint32_t e = (uint32_t)entities.size() - 1;
                if (unsigned a = LV->getArg()) {
                    if (!scopes[s].args.count(a)) scopes[s].args[a] = e;
                } else {
                    scopes[s].locals.push_back(e);
                }
            } else if (auto *IE = dyn_cast<DIImportedEntity>(N)) {
                if (auto *LS = dyn_cast_or_null<DILocalScope>(IE->getScope())) {
                    int s = find_scope(LS);
                    if (s >= 0) scopes[s].decls.push_back(IE);
                }
            }
        }
        // the subprogram scope DIE
        uint32_t d = get_subprogram(SP);
        attr(d, dwarf::DW_AT_low_pc, GIR_DF_PC, fi);
        if (!minimal) attr(d, dwarf::DW_AT_frame_base, GIR_DF_FRAME_BASE, 0);
        uint32_t op = scope_children(0, d);
        if (op != NO) add_ref(d, dwarf::DW_AT_object_pointer, op);
        if (const DISubroutineType *Ty = SP->getType()) {
            auto A = Ty->getTypeArray();
            if (A.size() > 1 && !A[A.size() - 1] && !minimal) new_die(dwarf::DW_TAG_unspecified_parameters, d);
        }
        processed_sps.push_back(SP);
    }

    void end_module() {
        for (auto *IE : CU->getImportedEntities()) get_imported_entity(IE);
        for (auto *IE : deferred_decls) get_imported_entity(IE);
        // finishSubprogramDefinitions
        for (const DISubprogram *SP : processed_sps) {
            uint32_t d = get_die(SP);
            if (d != NO) apply_subprogram_attributes(SP, d, minimal);
        }
        // finishEntityDefinitions
        for (const Entity &E : entities) {
            uint32_t d = E.die;
            if (E.var) {
                if (!E.var->getName().empty()) add_string(d, dwarf::DW_AT_name, E.var->getName());
                if (E.var->getAlignInBytes())
                    attr(d, dwarf::DW_AT_alignment, dwarf::DW_FORM_udata, E.var->getAlignInBytes());
                add_annotations(d, E.var->getAnnotations());
                add_source_line(d, E.var->getLine(), 0, E.var->getFile());
                add_type(d, E.var->getType());
                if (E.var->isArtificial()) add_flag(d, dwarf::DW_AT_artificial);
            } else {
                if (!E.label->getName().empty()) add_string(d, dwarf::DW_AT_name, E.label->getName());
                add_source_line(d, E.label->getLine(), 0, E.label->getFile());
                attr(d, dwarf::DW_AT_low_pc, GIR_DF_LABEL, E.inst);
            }
        }
        // constructContainingTypeDIEs
        for (auto &P : containing) {
            if (!P.second) continue;
            uint32_t t = get_die(P.second);
            if (t != NO) add_ref(P.first, dwarf::DW_AT_containing_type, t);
        }
        write();
    }

    // Pre-order into T.dies / T.dattrs (refs renumbered).
    void write() {
        std::vector<uint32_t> order, newidx(nodes.size(), NO);
        std::vector<uint32_t> stack{0};
        while (!stack.empty()) {
            uint32_t d = stack.back();
            stack.pop_back();
            newidx[d] = (uint32_t)order.size();
            order.push_back(d);
            const auto &K = nodes[d].kids;
            for (auto it = K.rbegin(); it != K.rend(); ++it) stack.push_back(*it);
        }
        T.dies.reserve(order.size());
        for (uint32_t d : order) {
            const Node &N = nodes[d];
            GirDie g{};
            g.tag = N.tag;
            g.parent = N.parent == NO ? NO : newidx[N.parent];
            g.attrs = (uint32_t)T.dattrs.size();
            g.n_attrs = (uint32_t)N.attrs.size();
            for (GirDAttr a : N.attrs) {
                if (a.form == dwarf::DW_FORM_ref4) {
                    a.val = newidx[a.val];
                    if (a.val == NO) continue;   // (a DIE that never got a parent)
                }
                T.dattrs.push_back(a);
            }
            g.n_attrs = (uint32_t)T.dattrs.size() - g.attrs;
            T.dies.push_back(g);
        }
    }
};

GirDwarfBuilder::GirDwarfBuilder(const Module &m, GirTables &t, GirDwarfHost &host)
    : impl(std::make_unique<Impl>(m, t, host)) {}
GirDwarfBuilder::~GirDwarfBuilder() = default;
bool GirDwarfBuilder::enabled() const { return impl->CU != nullptr; }
void GirDwarfBuilder::begin_module() { impl->begin_module(); }
void GirDwarfBuilder::function(const Function &F, uint32_t fi, const std::vector<GirDwarfVar> &vars,
                               const std::vector<GirDwarfLabel> &labels) {
    impl->function(F, fi, vars, labels);
}
void GirDwarfBuilder::end_module() { impl->end_module(); }
