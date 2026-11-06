# The reference back-end does not depend on LLVM: it only reads GIR tables.
add_library(goovm_backend_cpp STATIC gir_codegen_cpp.cpp)
target_include_directories(goovm_backend_cpp PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}
    ${PROJECT_SOURCE_DIR}/gir)
target_compile_options(goovm_backend_cpp PRIVATE -Wall -Wextra -fno-exceptions -fno-rtti)
