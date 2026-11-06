// LLVM module -> GIR tables (see gir/gir.h).
#ifndef GOOVM_GIR_EXPORT_H
#define GOOVM_GIR_EXPORT_H

#include <cstdint>
#include <cstdio>
#include <string>
#include <vector>

#include "gir.h"

namespace llvm {
class Module;
}

// The GIR tables of one module, owned by the host.
struct GirTables {
    GirHeader header{};
    std::vector<GirTypeDef> types;
    std::vector<GirFunc> funcs;
    std::vector<GirBlock> blocks;
    std::vector<GirInst> insts;
    std::vector<uint32_t> opnds;
    std::vector<GirConst> consts;
    std::vector<GirGlobal> globals;
    std::vector<GirSection> sections;
    std::vector<uint8_t> data;
    std::vector<GirDataReloc> drelocs;
    std::vector<uint8_t> strtab;
    std::vector<GirDLoc> dlocs;
    std::vector<GirDScope> dscopes;
    std::vector<GirDFile> dfiles;
    std::vector<uint8_t> dstr;
    std::vector<GirAsm> asms;
    uint64_t n_llvm_insts = 0;  // statistics: LLVM instructions in defined functions

    GirModule view() const;
};

// Thrown by gir_export for a construct outside what GIR can express; `msg`
// names the construct, the function (or global) and the instruction.
struct GirUnsupported {
    std::string msg;
};

// Fills `out` from `m`; throws GirUnsupported. The module is not modified.
// size_hint (optional, e.g. the bitcode file size in bytes) pre-sizes the
// tables.
void gir_export(const llvm::Module &m, GirTables &out, size_t size_hint = 0);

// Prints the tables in a readable text form (for debugging and for checking
// another back-end's reading of the format).
void gir_dump(const GirModule &m, std::FILE *f);

#endif
