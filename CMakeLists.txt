# goovm: a fast -O0 LLVM back-end written in Goose.
#
#   cmake -G Ninja -S . -B build -DCMAKE_BUILD_TYPE=Release \
#         -DGOOVM_GOOSE=/path/to/goose -DGOOVM_GOOSE_STDLIB=/path/to/goose/stdlib
#   ninja -C build -j3
#
# The C++ reference back-end of GIR v0 (backend-cpp/) is frozen at commit
# 8f55b18 and is no longer built: it reads GIR v0, this tree is GIR v2.
cmake_minimum_required(VERSION 3.20)
project(goovm C CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
if (NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release)
endif ()

option(GOOVM_WITH_GOOSE "Build the Goose back-end into goovm-llc (needs GOOVM_GOOSE or GOOVM_GOOSE_C)" ON)
set(GOOVM_GOOSE "$ENV{GOOSE}" CACHE FILEPATH "The goose compiler, used to generate C from backend-goose/*.goose")
set(GOOVM_GOOSE_STDLIB "$ENV{GOOSE_STDLIB}" CACHE PATH "goose's stdlib directory (GOOSE_STDLIB)")
set(GOOVM_GOOSE_FLAGS "" CACHE STRING "Extra goose options (the default is goose's -O2)")
set(GOOVM_GOOSE_C "" CACHE FILEPATH
    "Use this pre-generated cg.c (with cg.h next to it) instead of running goose")

# LLVMConfigVersion.cmake only accepts exact major.minor requests, so ask
# for any version and check the major one.
find_package(LLVM REQUIRED CONFIG)
if (NOT LLVM_VERSION_MAJOR EQUAL 20)
    message(FATAL_ERROR "goovm needs LLVM 20 (found ${LLVM_PACKAGE_VERSION} in ${LLVM_DIR}); "
            "pass -DLLVM_DIR=/usr/lib/llvm-20/lib/cmake/llvm")
endif ()
message(STATUS "goovm: LLVM ${LLVM_PACKAGE_VERSION} from ${LLVM_DIR}")

if (GOOVM_WITH_GOOSE)
    add_subdirectory(backend-goose)
endif ()
add_subdirectory(tools/goovm-llc)

# goovm-cc (clang's front end in-process + a goovm back-end) needs the Clang
# CMake package (Ubuntu: libclang-20-dev); skipped when it is missing.
option(GOOVM_WITH_CLANG "Build goovm-cc" ON)
if (GOOVM_WITH_CLANG)
    find_package(Clang CONFIG HINTS "${LLVM_DIR}/../clang")
    if (Clang_FOUND)
        add_subdirectory(tools/goovm-cc)
    else ()
        message(STATUS "goovm: Clang CMake package not found; goovm-cc is not built")
    endif ()
endif ()
