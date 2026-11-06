# goovm-cc: clang's front end in-process + a goovm back-end. Built from the
# top-level CMakeLists.txt when the Clang CMake package is found
# (Ubuntu: libclang-20-dev).
add_executable(goovm-cc goovm-cc.cpp)
target_include_directories(goovm-cc SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS} ${CLANG_INCLUDE_DIRS})
separate_arguments(GOOVM_CC_LLVM_DEFS NATIVE_COMMAND ${LLVM_DEFINITIONS})
target_compile_definitions(goovm-cc PRIVATE ${GOOVM_CC_LLVM_DEFS} GOOVM_CLANG_PATH="${LLVM_TOOLS_BINARY_DIR}/clang")
if (NOT LLVM_ENABLE_RTTI)
    target_compile_options(goovm-cc PRIVATE -fno-rtti)
endif ()
target_link_libraries(goovm-cc PRIVATE clang-cpp LLVM)

if (GOOVM_WITH_GOOSE)
    set(goovm_cc_exc_srcs goovm_backend.cpp
        ${PROJECT_SOURCE_DIR}/tools/goovm-llc/gir_export.cpp
        ${PROJECT_SOURCE_DIR}/tools/goovm-llc/gir_asm.cpp)
    target_sources(goovm-cc PRIVATE ${goovm_cc_exc_srcs})
    # gir_export reports unsupported input by throwing GirUnsupported inside
    # goovm's own code; only these files need exceptions.
    set_source_files_properties(${goovm_cc_exc_srcs} PROPERTIES COMPILE_OPTIONS "-fexceptions")
    target_include_directories(goovm-cc PRIVATE ${PROJECT_SOURCE_DIR}/gir ${PROJECT_SOURCE_DIR}/tools/goovm-llc)
    target_compile_definitions(goovm-cc PRIVATE GOOVM_CC_WITH_GOOSE "GOOVM_GOOSE_HEADER=\"${GOOVM_GOOSE_HEADER}\"")
    add_dependencies(goovm-cc goovm_backend_goose)
    target_link_libraries(goovm-cc PRIVATE goovm_backend_goose m pthread)
endif ()
