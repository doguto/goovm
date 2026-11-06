// LLVM module -> GIR tables (see gir/gir.h).
#ifndef GOOVM_GIR_EXPORT_H
#define GOOVM_GIR_EXPORT_H

#include <cstdint>
#include <cstdio>
#include <vector>

#include "gir.h"

namespace llvm {
class Module;
}

// The GIR tables of one module, owned by the host.
struct GirTables {
    std::vector<GirFunc> funcs;
    std::vector<GirBlock> blocks;
    std::vector<GirInst> insts;
    std::vector<uint32_t> opnds;
    std::vector<GirConst> consts;
    std::vector<GirGlobal> globals;
    std::vector<uint8_t> data;
    std::vector<GirDataReloc> drelocs;
    std::vector<uint8_t> strtab;
    uint64_t n_llvm_insts = 0;  // statistics: LLVM instructions in defined functions

    GirModule view() const;
};

// Fills `out` from `m`. On an unsupported construct prints a message naming
// the function (or global) and the instruction to stderr and exits with
// status 2.
void gir_export(const llvm::Module &m, GirTables &out);

// Prints the tables in a readable text form (for debugging and for checking
// another back-end's reading of the format).
void gir_dump(const GirModule &m, std::FILE *f);

#endif
