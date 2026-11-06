// Assembling inline-asm text with LLVM's MC layer (for GIR_ASM and module
// asm).
#include "gir_asm.h"

#include <memory>

#include "llvm/MC/MCAsmBackend.h"
#include "llvm/MC/MCAsmInfo.h"
#include "llvm/MC/MCCodeEmitter.h"
#include "llvm/MC/MCContext.h"
#include "llvm/MC/MCInstrInfo.h"
#include "llvm/MC/MCObjectFileInfo.h"
#include "llvm/MC/MCObjectWriter.h"
#include "llvm/MC/MCParser/MCAsmParser.h"
#include "llvm/MC/MCParser/MCTargetAsmParser.h"
#include "llvm/MC/MCRegisterInfo.h"
#include "llvm/MC/MCStreamer.h"
#include "llvm/MC/MCSubtargetInfo.h"
#include "llvm/MC/MCTargetOptions.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Object/ELFObjectFile.h"
#include "llvm/Object/ObjectFile.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TargetParser/Triple.h"

using namespace llvm;

namespace {

// Assembles `text` into an ELF relocatable object in `buf`.
bool assemble_object(const std::string &triple_str, const std::string &text, bool intel,
                     SmallVectorImpl<char> &buf, std::string &err) {
    static bool inited = false;
    if (!inited) {
        InitializeNativeTarget();
        InitializeNativeTargetAsmParser();
        inited = true;
    }
    Triple triple(triple_str);
    const Target *T = TargetRegistry::lookupTarget(triple_str, err);
    if (!T) return false;
    MCTargetOptions opts;
    std::unique_ptr<MCRegisterInfo> MRI(T->createMCRegInfo(triple_str));
    std::unique_ptr<MCAsmInfo> MAI(T->createMCAsmInfo(*MRI, triple_str, opts));
    std::unique_ptr<MCSubtargetInfo> STI(T->createMCSubtargetInfo(triple_str, "x86-64", ""));
    std::unique_ptr<MCInstrInfo> MII(T->createMCInstrInfo());
    if (!MRI || !MAI || !STI || !MII) {
        err = "no MC support for " + triple_str;
        return false;
    }
    SourceMgr SrcMgr;
    std::string diag;
    SrcMgr.setDiagHandler([](const SMDiagnostic &d, void *ctx) {
        raw_string_ostream os(*static_cast<std::string *>(ctx));
        os << d.getMessage();
    }, &diag);
    SrcMgr.AddNewSourceBuffer(MemoryBuffer::getMemBufferCopy(text + "\n"), SMLoc());
    MCContext Ctx(triple, MAI.get(), MRI.get(), STI.get(), &SrcMgr);
    std::unique_ptr<MCObjectFileInfo> MOFI(T->createMCObjectFileInfo(Ctx, /*PIC=*/true));
    Ctx.setObjectFileInfo(MOFI.get());
    raw_svector_ostream os(buf);
    std::unique_ptr<MCCodeEmitter> CE(T->createMCCodeEmitter(*MII, Ctx));
    std::unique_ptr<MCAsmBackend> MAB(T->createMCAsmBackend(*STI, *MRI, opts));
    if (!CE || !MAB) {
        err = "no MC code emitter";
        return false;
    }
    std::unique_ptr<MCObjectWriter> OW = MAB->createObjectWriter(os);
    std::unique_ptr<MCStreamer> Str(T->createMCObjectStreamer(triple, Ctx, std::move(MAB), std::move(OW),
                                                              std::move(CE), *STI));
    std::unique_ptr<MCAsmParser> Parser(createMCAsmParser(SrcMgr, Ctx, *Str, *MAI));
    std::unique_ptr<MCTargetAsmParser> TAP(T->createMCAsmParser(*STI, *Parser, *MII, opts));
    if (!TAP) {
        err = "no x86 asm parser";
        return false;
    }
    Parser->setTargetParser(*TAP);
    Parser->setAssemblerDialect(intel ? 1 : 0);
    Str->initSections(false, *STI);
    if (Parser->Run(/*NoInitialTextSection=*/true) || !diag.empty()) {
        err = "cannot assemble: " + diag;
        return false;
    }
    Str->finish();
    return true;
}

}  // namespace

bool gir_assemble(const std::string &triple_str, const std::string &text, bool intel, std::vector<uint8_t> &code,
                  std::string &err) {
    SmallVector<char, 0> buf;
    if (!assemble_object(triple_str, text, intel, buf, err)) return false;
    auto obj = object::ObjectFile::createObjectFile(MemoryBufferRef(StringRef(buf.data(), buf.size()), "asm"));
    if (!obj) {
        err = toString(obj.takeError());
        return false;
    }
    code.clear();
    for (const object::SectionRef &s : (*obj)->sections()) {
        Expected<StringRef> name = s.getName();
        if (!name) {
            consumeError(name.takeError());
            continue;
        }
        if (s.relocations().begin() != s.relocations().end()) {
            err = "the assembled code needs relocations";
            return false;
        }
        if (*name == ".text") {
            Expected<StringRef> c = s.getContents();
            if (!c) {
                err = toString(c.takeError());
                return false;
            }
            code.assign(c->begin(), c->end());
        } else if (s.getSize() && (s.isData() || s.isBSS() || s.isText())) {
            err = "the assembly defines data or another section (" + name->str() + ")";
            return false;
        }
    }
    return true;
}

bool gir_assemble_module(const std::string &triple_str, const std::string &text, std::vector<GirAsmSymbol> &syms,
                         std::string &err) {
    SmallVector<char, 0> buf;
    if (!assemble_object(triple_str, text, false, buf, err)) return false;
    auto obj = object::ObjectFile::createObjectFile(MemoryBufferRef(StringRef(buf.data(), buf.size()), "asm"));
    if (!obj) {
        err = toString(obj.takeError());
        return false;
    }
    for (const object::SectionRef &s : (*obj)->sections()) {
        if (s.getSize() && (s.isData() || s.isBSS() || s.isText())) {
            Expected<StringRef> name = s.getName();
            err = "code or data in section " + (name ? name->str() : std::string("?"));
            if (!name) consumeError(name.takeError());
            return false;
        }
    }
    auto *elf = dyn_cast<object::ELFObjectFileBase>(obj->get());
    if (!elf) {
        err = "not an ELF object";
        return false;
    }
    for (const object::ELFSymbolRef &sym : elf->symbols()) {
        Expected<StringRef> name = sym.getName();
        if (!name) {
            consumeError(name.takeError());
            continue;
        }
        if (name->empty()) continue;
        uint8_t bind = sym.getBinding();
        uint8_t type = sym.getELFType();
        if (type == ELF::STT_SECTION || type == ELF::STT_FILE) continue;
        GirAsmSymbol s;
        s.name = name->str();
        Expected<object::section_iterator> sec = sym.getSection();
        if (!sec) {
            consumeError(sec.takeError());
            continue;
        }
        s.defined = *sec != elf->section_end();
        s.global = bind == ELF::STB_GLOBAL;
        s.weak = bind == ELF::STB_WEAK;
        s.func = type == ELF::STT_FUNC;
        syms.push_back(s);
    }
    return true;
}
