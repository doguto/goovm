# goovm-cc: clang front end in-process + a goovm back-end.
# Standalone for now:
#   cmake -G Ninja -S tools/goovm-cc -B build-cc -DCMAKE_BUILD_TYPE=Release \
#     -DCMAKE_CXX_COMPILER=clang++-20 -DClang_DIR=/usr/lib/llvm-20/lib/cmake/clang
cmake_minimum_required(VERSION 3.20)
project(goovm-cc CXX)
set(CMAKE_CXX_STANDARD 17)
find_package(Clang REQUIRED CONFIG)
add_executable(goovm-cc goovm-cc.cpp)
target_include_directories(goovm-cc SYSTEM PRIVATE ${LLVM_INCLUDE_DIRS} ${CLANG_INCLUDE_DIRS})
target_compile_definitions(goovm-cc PRIVATE ${LLVM_DEFINITIONS} GOOVM_CLANG_PATH="${LLVM_TOOLS_BINARY_DIR}/clang")
target_compile_options(goovm-cc PRIVATE -fno-rtti -fno-exceptions)
target_link_libraries(goovm-cc PRIVATE clang-cpp LLVM)
