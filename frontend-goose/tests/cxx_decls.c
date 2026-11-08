/* The functions and variables a C++ file declares at namespace or class
 * scope in its main file (not templates), as clang-20 sees them through
 * libclang: "kind|name|mangled name" per line, the format of
 * goosecc --dump-decls (tests/cmp_decls_cxx.py compiles and runs this).
 *
 *   cxx_decls file.cpp [clang flags...]
 */
#include <clang-c/Index.h>
#include <stdio.h>
#include <string.h>

static const char *kind_name(enum CXCursorKind k) {
    switch (k) {
    case CXCursor_FunctionDecl: return "FunctionDecl";
    case CXCursor_CXXMethod: return "CXXMethod";
    case CXCursor_Constructor: return "CXXConstructor";
    case CXCursor_Destructor: return "CXXDestructor";
    case CXCursor_ConversionFunction: return "CXXConversion";
    case CXCursor_VarDecl: return "VarDecl";
    default: return 0;
    }
}

static enum CXChildVisitResult visit(CXCursor c, CXCursor parent, CXClientData d) {
    (void)parent; (void)d;
    enum CXCursorKind k = clang_getCursorKind(c);
    if (k == CXCursor_Namespace || k == CXCursor_LinkageSpec || k == CXCursor_UnexposedDecl ||
        k == CXCursor_StructDecl || k == CXCursor_ClassDecl || k == CXCursor_UnionDecl)
        return CXChildVisit_Recurse;
    if (!clang_Location_isFromMainFile(clang_getCursorLocation(c))) return CXChildVisit_Continue;
    const char *kn = kind_name(k);
    if (!kn) return CXChildVisit_Continue;
    CXString name = clang_getCursorSpelling(c);
    CXString m = clang_Cursor_getMangling(c);
    const char *ms = clang_getCString(m);
    const char *ns = clang_getCString(name);
    int special = k == CXCursor_Constructor || k == CXCursor_Destructor || k == CXCursor_ConversionFunction ||
                  (strncmp(ns, "operator", 8) == 0 && !(ns[8] == '_' || (ns[8] >= 'a' && ns[8] <= 'z') ||
                                                          (ns[8] >= 'A' && ns[8] <= 'Z') || (ns[8] >= '0' && ns[8] <= '9')));
    if (ms && *ms) printf("%s|%s|%s\n", kn, special ? "-" : ns, ms);
    clang_disposeString(name);
    clang_disposeString(m);
    return CXChildVisit_Continue;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: cxx_decls file.cpp [flags]\n"); return 2; }
    CXIndex idx = clang_createIndex(0, 0);
    CXTranslationUnit tu;
    enum CXErrorCode e = clang_parseTranslationUnit2(idx, argv[1], (const char *const *)argv + 2, argc - 2, 0, 0,
                                                     CXTranslationUnit_SkipFunctionBodies, &tu);
    if (e != CXError_Success) { fprintf(stderr, "cxx_decls: cannot parse %s\n", argv[1]); return 1; }
    clang_visitChildren(clang_getTranslationUnitCursor(tu), visit, 0);
    clang_disposeTranslationUnit(tu);
    clang_disposeIndex(idx);
    return 0;
}
