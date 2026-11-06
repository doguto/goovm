// goovm reference back-end: GIR -> x86-64 SysV ELF64 relocatable object.
// See DESIGN.md for the algorithm and the porting notes.
#ifndef GOOVM_BACKEND_CPP_CG_H
#define GOOVM_BACKEND_CPP_CG_H

#include <cstdint>
#include <vector>

#include "gir.h"

// Compiles the whole module and replaces `obj_out` with the bytes of an
// ELF64 x86-64 relocatable object. The module must follow the structural
// rules of gir.h (the exporter guarantees them); the back-end does not
// validate its input.
void gir_codegen_cpp(const GirModule &m, std::vector<uint8_t> &obj_out);

#endif
