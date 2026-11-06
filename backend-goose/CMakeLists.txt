# The Goose back-end: backend-goose/*.goose -> cg.c + cg.h (goose --standalone
# --header) -> static library goovm_backend_goose.
file(GLOB GOOVM_GOOSE_SRCS CONFIGURE_DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/*.goose")

if (GOOVM_GOOSE_C)
    set(goose_c "${GOOVM_GOOSE_C}")
    get_filename_component(goose_dir "${goose_c}" DIRECTORY)
    set(goose_h "${goose_dir}/cg.h")
    if (NOT EXISTS "${goose_c}" OR NOT EXISTS "${goose_h}")
        message(FATAL_ERROR "GOOVM_GOOSE_C: ${goose_c} or ${goose_h} not found")
    endif ()
else ()
    if (NOT GOOVM_GOOSE)
        message(FATAL_ERROR "The Goose back-end needs the goose compiler: pass -DGOOVM_GOOSE=/path/to/goose "
                "and -DGOOVM_GOOSE_STDLIB=/path/to/goose/stdlib (or set GOOSE / GOOSE_STDLIB), "
                "or -DGOOVM_GOOSE_C=<pre-generated cg.c>, or -DGOOVM_WITH_GOOSE=OFF")
    endif ()
    set(goose_c "${CMAKE_CURRENT_BINARY_DIR}/cg.c")
    set(goose_h "${CMAKE_CURRENT_BINARY_DIR}/cg.h")
    separate_arguments(goose_flags UNIX_COMMAND "${GOOVM_GOOSE_FLAGS}")
    add_custom_command(
        OUTPUT "${goose_c}" "${goose_h}"
        COMMAND ${CMAKE_COMMAND} -E env "GOOSE_STDLIB=${GOOVM_GOOSE_STDLIB}"
                "${GOOVM_GOOSE}" ${goose_flags} --standalone --header "${goose_h}" -o "${goose_c}"
                "${CMAKE_CURRENT_SOURCE_DIR}/cg.goose"
        DEPENDS ${GOOVM_GOOSE_SRCS} "${GOOVM_GOOSE}"
        COMMENT "goose: backend-goose/cg.goose -> cg.c"
        VERBATIM)
endif ()

# The generated C is compiled like any C file; warnings are its own.
add_library(goovm_backend_goose STATIC "${goose_c}")
set_source_files_properties("${goose_c}" PROPERTIES LANGUAGE C GENERATED TRUE)
target_compile_options(goovm_backend_goose PRIVATE -w)
set(GOOVM_GOOSE_HEADER "${goose_h}" PARENT_SCOPE)
