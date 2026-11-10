// Assembling inline-asm text with LLVM's MC layer (for GIR_ASM).
#ifndef GOOVM_GIR_ASM_H
#define GOOVM_GIR_ASM_H

#include <cstdint>
#include <string>
#include <vector>

// Assembles x86-64 assembly text (AT&T, or Intel if `intel`) or AArch64
// assembly text (with the subtarget features `features`, e.g. a function's
// "target-features") into machine code. Fails (with a message) if the text
// does not assemble, or if the code needs relocations or defines anything
// outside .text.
bool gir_assemble(const std::string &triple, const std::string &text, bool intel, std::vector<uint8_t> &code,
                  std::string &err, const std::string &features = "");

// A symbol of assembled module-level asm.
struct GirAsmSymbol {
    std::string name;
    bool defined = false;   // defined by the asm itself
    bool global = false;    // STB_GLOBAL
    bool weak = false;      // STB_WEAK
    bool func = false;      // STT_FUNC
};
// Assembles module-level inline asm (AT&T) and lists the symbols it names.
// Fails if the text does not assemble or puts bytes into any section.
bool gir_assemble_module(const std::string &triple, const std::string &text, std::vector<GirAsmSymbol> &syms,
                         std::string &err);

#endif
