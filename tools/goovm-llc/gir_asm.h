// Assembling inline-asm text with LLVM's MC layer (for GIR_ASM).
#ifndef GOOVM_GIR_ASM_H
#define GOOVM_GIR_ASM_H

#include <cstdint>
#include <string>
#include <vector>

// Assembles x86-64 assembly text (AT&T, or Intel if `intel`) into machine
// code. Fails (with a message) if the text does not assemble, or if the
// code needs relocations or defines anything outside .text.
bool gir_assemble(const std::string &triple, const std::string &text, bool intel, std::vector<uint8_t> &code,
                  std::string &err);

#endif
