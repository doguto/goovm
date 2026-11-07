// goovm-cc's bridge to the goovm exporter and the Goose back-end.
#ifndef GOOVM_CC_BACKEND_H
#define GOOVM_CC_BACKEND_H

#include <cstdint>
#include <string>
#include <vector>

namespace llvm {
class Module;
}

// Starts the Goose runtime (goose_init); call once before compiling.
void goovm_backend_init(int argc, char **argv);
void goovm_backend_exit();

// Exports `m` to GIR and compiles it with the Goose back-end into an ELF
// object. Returns 0 on success, 2 if the module uses something GIR cannot
// express (`err` says what), 1 on other errors. The phase times are in
// microseconds. opt_level >= 1 runs the Goose middle-end and the global
// register allocator (GIR header opt_level).
int goovm_compile_module(llvm::Module &m, std::vector<uint8_t> &obj, std::string &err,
                         long long *export_us = nullptr, long long *codegen_us = nullptr,
                         unsigned opt_level = 0);

#endif
