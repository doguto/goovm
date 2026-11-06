// LLVM debug metadata -> the GIR DIE tables (dies, dattrs; gir/gir.h).
//
// The builder mirrors what LLVM 20's DwarfDebug / DwarfCompileUnit /
// DwarfUnit do for one compile unit at -O0 (DWARF 5, GDB tuning, no
// accelerator tables, no split DWARF): the same DIEs, attributes, forms
// and DIE order, so that a debugger sees what it sees in a clang -O0 -g
// object. What only the back-end knows (code addresses and lengths, frame
// offsets, which lexical blocks have code) is left as GIR attribute forms.
#ifndef GOOVM_GIR_DWARF_H
#define GOOVM_GIR_DWARF_H

#include <cstdint>
#include <memory>
#include <vector>

#include "gir_export.h"

namespace llvm {
class DIExpression;
class DIFile;
class DILabel;
class DILocalVariable;
class DILocation;
class DIScope;
class Function;
class GlobalValue;
class Module;
class StringRef;
}  // namespace llvm

// What the builder needs from the exporter.
struct GirDwarfHost {
    virtual ~GirDwarfHost() = default;
    virtual uint32_t dw_str(llvm::StringRef s) = 0;              // dstr offset (0 for "")
    virtual uint32_t dw_bytes(const uint8_t *p, size_t n) = 0;    // dstr offset of raw bytes
    virtual uint32_t dw_file(const llvm::DIFile *f) = 0;          // dfiles index
    virtual uint32_t dw_scope(const llvm::DIScope *s) = 0;        // dscopes index
    virtual uint32_t dw_global(const llvm::GlobalValue *g) = 0;   // globals index or GIR_NONE
};

// A variable of a function: a #dbg_declare (or llvm.dbg.declare) whose
// address is GIR value `addr` (GIR_NONE: no location). `mf`: the address
// is a static alloca (LLVM's MachineFunction side table, collected first).
struct GirDwarfVar {
    const llvm::DILocalVariable *var;
    const llvm::DIExpression *expr;
    const llvm::DILocation *loc;
    uint32_t addr;
    bool mf;
};
struct GirDwarfLabel {
    const llvm::DILabel *label;
    const llvm::DILocation *loc;
    uint32_t inst;   // GIR instruction the label is at
};

class GirDwarfBuilder {
public:
    GirDwarfBuilder(const llvm::Module &m, GirTables &t, GirDwarfHost &host);
    ~GirDwarfBuilder();
    bool enabled() const;
    void begin_module();
    // After function `fi` (funcs index) of F has been exported.
    void function(const llvm::Function &F, uint32_t fi, const std::vector<GirDwarfVar> &vars,
                  const std::vector<GirDwarfLabel> &labels);
    void end_module();   // writes t.dies / t.dattrs

    struct Impl;

private:
    std::unique_ptr<Impl> impl;
};

#endif
