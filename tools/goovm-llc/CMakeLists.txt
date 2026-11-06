add_executable(goovm-llc goovm-llc.cpp gir_export.cpp gir_asm.cpp)
target_include_directories(goovm-llc PRIVATE ${PROJECT_SOURCE_DIR}/gir)
target_include_directories(goovm-llc SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS})
separate_arguments(GOOVM_LLVM_DEFS NATIVE_COMMAND ${LLVM_DEFINITIONS})
target_compile_definitions(goovm-llc PRIVATE ${GOOVM_LLVM_DEFS})
# GirUnsupported is thrown and caught inside goovm-llc's own code (never
# through LLVM frames), so the driver can fall back to LLVM's code generator.
target_compile_options(goovm-llc PRIVATE -Wall -Wextra -Wno-unused-parameter -fexceptions)
if (NOT LLVM_ENABLE_RTTI)
    target_compile_options(goovm-llc PRIVATE -fno-rtti)
endif ()

if (LLVM_LINK_LLVM_DYLIB)
    target_link_libraries(goovm-llc PRIVATE LLVM)
else ()
    llvm_map_components_to_libnames(GOOVM_LLVM_LIBS core bitreader support target analysis mc mcparser object
        x86codegen x86asmparser x86desc x86info)
    target_link_libraries(goovm-llc PRIVATE ${GOOVM_LLVM_LIBS})
endif ()

if (GOOVM_WITH_GOOSE)
    add_dependencies(goovm-llc goovm_backend_goose)
    target_compile_definitions(goovm-llc PRIVATE GOOVM_WITH_GOOSE "GOOVM_GOOSE_HEADER=\"${GOOVM_GOOSE_HEADER}\"")
    target_link_libraries(goovm-llc PRIVATE goovm_backend_goose m pthread)
endif ()
