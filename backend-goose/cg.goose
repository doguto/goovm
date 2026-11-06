// goovm back-end in Goose: GIR tables -> ELF64 x86-64 relocatable object.
//
// INTERFACE SKELETON. This file fixes the record layouts (they must match
// gir/gir.h byte for byte) and the exported entry point that
// tools/goovm-llc calls with --backend=goose. The port of
// backend-cpp/gir_codegen_cpp.cpp (see backend-cpp/DESIGN.md) replaces the
// body of gir_codegen; until then it returns an empty object, which the
// driver reports as an error.
//
//   goose --standalone --header cg.h -o cg.c backend-goose/cg.goose

struct Func { global: u32, flags: u32, first_block: u32, n_blocks: u32, first_inst: u32,
              n_inst: u32, n_args: u32, arg_tys: u32, ret_ty: u32 }
struct Block { first_inst: u32, n_inst: u32 }
struct Inst { op: u8, ty: u8, sub: u8, aux: u8, a: u32, b: u32, c: u32 }
struct Const { value: i64, ty: u32, reserved: u32 }  // reserved = GirConst.pad (`pad` is a Goose keyword)
struct Global { name: u32, name_len: u32, kind: u32, flags: u32, data: u32, size: u32,
                align: u32, func: u32 }
struct DataReloc { owner: u32, offset: u32, target: u32, addend: i32 }

// The object file being built; the host reads it until the next call.
var obj: u8[>..] = [];

export fn gir_codegen(funcs: const Func[:], blocks: const Block[:], insts: const Inst[:],
                      opnds: const u32[:], consts: const Const[:], globals: const Global[:],
                      data: const u8[:], drelocs: const DataReloc[:], strtab: const u8[:]) -> const u8[:] {
    obj.clear();
    return obj;
}
