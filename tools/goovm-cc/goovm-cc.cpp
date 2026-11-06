// goovm-cc: a drop-in for `clang -c` that runs clang's front end in-process
// and hands the LLVM module straight to a back-end, with no bitcode file and
// no second process.
//
//   goovm-cc [--backend=clang|llvm|goose] [--fallback] [--time] <clang args> -c x.c [-o x.o]
//
// Back-ends:
//   clang   clang's own EmitObjAction: exactly what `clang -c` does, in-process
//           (the baseline).
//   llvm    clang front end -> llvm::Module -> LLVM's -O0 code generator.
//   goose   clang front end -> llvm::Module -> GIR exporter -> Goose back-end.
//           Needs GOOVM_CC_WITH_GOOSE (links the goovm exporter and back-end).
// --fallback: if the Goose back-end rejects the module, use LLVM's.
// --time: phase times in microseconds on stderr, and a machine-readable line
//   `goovm-cc-time: frontend_us=... backend_us=... write_us=... total_us=...`.

#include "clang/Basic/DiagnosticOptions.h"
#include "clang/CodeGen/CodeGenAction.h"
#include "clang/Driver/Compilation.h"
#include "clang/Driver/Driver.h"
#include "clang/Driver/Job.h"
#include "clang/Driver/Tool.h"
#include "llvm/TargetParser/Host.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/CompilerInvocation.h"
#include "clang/Frontend/FrontendOptions.h"
#include "clang/Frontend/TextDiagnosticPrinter.h"
#include "clang/Frontend/Utils.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/VirtualFileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"

#include <chrono>
#include <cstdio>
#include <cstring>
#include <memory>
#include <string>
#include <vector>

#ifdef GOOVM_CC_WITH_GOOSE
#include "goovm_backend.h"
#endif

using clk = std::chrono::steady_clock;
static long long us(clk::time_point a, clk::time_point b) {
    return std::chrono::duration_cast<std::chrono::microseconds>(b - a).count();
}

#ifndef GOOVM_CLANG_PATH
#define GOOVM_CLANG_PATH "/usr/lib/llvm-20/bin/clang"
#endif

// LLVM's own -O0 code generator on a module, writing an object file.
static bool llvm_codegen(llvm::Module &M, const clang::CompilerInvocation &inv, const std::string &out) {
    std::string err;
    const std::string triple = M.getTargetTriple();
    const llvm::Target *T = llvm::TargetRegistry::lookupTarget(triple, err);
    if (!T) { std::fprintf(stderr, "goovm-cc: %s\n", err.c_str()); return false; }
    const auto &TO = inv.getTargetOpts();
    std::string features;
    for (const auto &f : TO.Features) { if (!features.empty()) features += ","; features += f; }
    llvm::TargetOptions opts;
    llvm::Reloc::Model reloc = M.getPICLevel() == llvm::PICLevel::NotPIC ? llvm::Reloc::Static : llvm::Reloc::PIC_;
    std::unique_ptr<llvm::TargetMachine> TM(T->createTargetMachine(
        triple, TO.CPU, features, opts, reloc, std::nullopt, llvm::CodeGenOptLevel::None));
    M.setDataLayout(TM->createDataLayout());
    std::error_code ec;
    llvm::raw_fd_ostream os(out, ec, llvm::sys::fs::OF_None);
    if (ec) { std::fprintf(stderr, "goovm-cc: %s: %s\n", out.c_str(), ec.message().c_str()); return false; }
    llvm::legacy::PassManager PM;
    if (TM->addPassesToEmitFile(PM, os, nullptr, llvm::CodeGenFileType::ObjectFile)) {
        std::fprintf(stderr, "goovm-cc: target cannot emit object files\n");
        return false;
    }
    PM.run(M);
    return true;
}

int main(int argc, char **argv) {
    std::string backend = "goose";
    bool fallback = false, timing = false;
    std::vector<const char *> args = {GOOVM_CLANG_PATH};
    for (int i = 1; i < argc; i++) {
        if (!std::strncmp(argv[i], "--backend=", 10)) backend = argv[i] + 10;
        else if (!std::strcmp(argv[i], "--fallback")) fallback = true;
        else if (!std::strcmp(argv[i], "--time")) timing = true;
        else args.push_back(argv[i]);
    }
#ifndef GOOVM_CC_WITH_GOOSE
    if (backend == "goose") backend = "llvm";   // not built in: behave like clang -c
#endif
    auto t0 = clk::now();
#ifdef GOOVM_CC_WITH_GOOSE
    if (backend == "goose") goovm_backend_init(argc, argv);
#endif
    llvm::InitializeNativeTarget();
    llvm::InitializeNativeTargetAsmPrinter();

    // Run the clang driver to get the cc1 job, exactly as `clang -c` would
    // (createInvocation is meant for tools and forces -fsyntax-only).
    llvm::IntrusiveRefCntPtr<clang::DiagnosticOptions> dopts = new clang::DiagnosticOptions();
    auto *dprinter = new clang::TextDiagnosticPrinter(llvm::errs(), &*dopts);
    llvm::IntrusiveRefCntPtr<clang::DiagnosticsEngine> diags =
        new clang::DiagnosticsEngine(new clang::DiagnosticIDs(), &*dopts, dprinter);
    clang::driver::Driver driver(GOOVM_CLANG_PATH, llvm::sys::getDefaultTargetTriple(), *diags);
    std::unique_ptr<clang::driver::Compilation> comp(driver.BuildCompilation(args));
    if (!comp || diags->hasErrorOccurred()) return 1;
    const clang::driver::JobList &jobs = comp->getJobs();
    if (jobs.size() != 1 || !llvm::isa<clang::driver::Command>(*jobs.begin())) {
        std::fprintf(stderr, "goovm-cc: expected exactly one compile job (use -c with one input)\n");
        return 1;
    }
    const auto &cmd = llvm::cast<clang::driver::Command>(*jobs.begin());
    if (std::strcmp(cmd.getCreator().getName(), "clang") != 0) {
        std::fprintf(stderr, "goovm-cc: the job is not a clang compile\n");
        return 1;
    }
    auto inv = std::make_shared<clang::CompilerInvocation>();
    if (!clang::CompilerInvocation::CreateFromArgs(*inv, cmd.getArguments(), *diags, GOOVM_CLANG_PATH)) return 1;
    const std::string out = inv->getFrontendOpts().OutputFile;
    // -mllvm options (e.g. -enable-matrix from -fenable-matrix), as
    // clang's ExecuteCompilerInvocation applies them
    const auto &llvm_args = inv->getFrontendOpts().LLVMArgs;
    if (!llvm_args.empty()) {
        std::vector<const char *> av = {"goovm-cc (LLVM option parsing)"};
        for (const auto &a : llvm_args) av.push_back(a.c_str());
        llvm::cl::ParseCommandLineOptions((int)av.size(), av.data());
    }

    clang::CompilerInstance CI;
    CI.setInvocation(inv);
    CI.createDiagnostics(*llvm::vfs::getRealFileSystem());
    if (!CI.hasDiagnostics()) return 1;

    long long fe = 0, be = 0, wr = 0, ex = 0, cg = 0;
    int rc = 0;
    if (backend == "clang") {
        clang::EmitObjAction act;
        auto a = clk::now();
        if (!CI.ExecuteAction(act)) rc = 1;
        fe = us(a, clk::now());   // front end and back end together
    } else {
        llvm::LLVMContext ctx;
        clang::EmitLLVMOnlyAction act(&ctx);
        auto a = clk::now();
        if (!CI.ExecuteAction(act)) return 1;
        std::unique_ptr<llvm::Module> M = act.takeModule();
        auto b = clk::now();
        fe = us(a, b);
        if (!M) return 1;
        bool done = false;
#ifdef GOOVM_CC_WITH_GOOSE
        if (backend == "goose") {
            std::vector<uint8_t> obj;
            std::string err;
            int r = goovm_compile_module(*M, obj, err, &ex, &cg);
            auto c = clk::now();
            be = us(b, c);
            if (r == 0) {
                FILE *f = std::fopen(out.c_str(), "wb");
                if (!f || std::fwrite(obj.data(), 1, obj.size(), f) != obj.size()) { std::perror(out.c_str()); return 1; }
                std::fclose(f);
                wr = us(c, clk::now());
                done = true;
            } else if (!fallback) {
                std::fprintf(stderr, "goovm-cc: %s\n", err.c_str());
                return r;
            } else {
                std::fprintf(stderr, "goovm-cc: falling back to LLVM: %s\n", err.c_str());
                b = clk::now();
            }
        }
#endif
        if (!done) {
            if (!llvm_codegen(*M, *inv, out)) return 1;
            be = us(b, clk::now());
        }
    }
    if (timing) {
        long long tot = us(t0, clk::now());
        std::fprintf(stderr, "goovm-cc-time: backend=%s frontend_us=%lld backend_us=%lld export_us=%lld codegen_us=%lld "
                     "write_us=%lld total_us=%lld\n", backend.c_str(), fe, be, ex, cg, wr, tot);
    }
    return rc;
}
