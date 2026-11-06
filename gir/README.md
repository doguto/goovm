# GIR: goovm's flat IR (version 2)

GIR is the hand-off format between LLVM and goovm's fast -O0 back-end. The
C++ exporter (`tools/goovm-llc/gir_export.cpp`) walks an `llvm::Module` once
and fills flat tables; the Goose back-end (`backend-goose/`) reads them and
writes an ELF64 x86-64 relocatable object. [`gir.h`](gir.h) is the normative
definition; this page describes the format in prose and lists what changed
from version 0 (frozen at commit 8f55b18 with the C++ reference back-end).

Version 2 covers what clang-20 emits at -O0 for C and C++17 on x86-64
Linux, with and without `-g`, and after `opt -passes=mem2reg`: every
integer width up to 128 bits, `half`/`float`/`double`/`x86_fp80`, vectors,
first-class aggregates, the SysV ABI attributes, variadic functions,
dynamic stack allocation, the intrinsics C and C++ use, atomics, TLS,
aliases, constructors, sections, inline and module-level assembly, debug
locations and, in tables added by milestone A3 (all additive, see the end),
exception handling, comdat groups and the DWARF debug-information tree.

## Tables

Every record is a fixed-size struct whose fields are naturally aligned with
no padding, so the host passes each table to Goose as a slice (`{data,
len}`) without copying, and Goose's packed structs see the same bytes.
`goovm-llc.cpp` `static_assert`s the size and key field offsets of every
generated Goose struct against `gir.h`.

| table | record | size | content |
|---|---|---:|---|
| `header` | `GirHeader` | 32 | one record: version, module flags (`PIE`), the `__tls_get_addr` global |
| `types` | `GirTypeDef` | 24 | every type id: kind, value class, bits, size, alignment, store size, elements |
| `funcs` | `GirFunc` | 40 | defined functions: block and instruction ranges, argument (type, ABI word) run, return type, flags, DISubprogram |
| `blocks` | `GirBlock` | 8 | basic blocks: instruction range |
| `insts` | `GirInst` | 24 | `op, sub` (u8), `flags, ty, aux` (u16), operands `a, b, c`, debug location `dbg` (u32) |
| `opnds` | `u32` | 4 | variable-length runs (call arguments, PHI pairs, switch cases, GEP terms, struct fields, shuffle masks, asm operands) |
| `consts` | `GirConst` | 24 | constants of every type: `lo`, `hi` (u64), `ty`, `data` |
| `globals` | `GirGlobal` | 40 | functions, variables and aliases: name, kind, flags, initializer, alignment, section |
| `sections` | `GirSection` | 16 | explicitly named sections: name, flags, ELF type |
| `data` | `u8` | 1 | initializer bytes, aggregate constants, assembled inline asm |
| `drelocs` | `GirDataReloc` | 32 | relocations inside initializers (addresses, block addresses, label differences) |
| `strtab` | `u8` | 1 | symbol and section names (a valid ELF string table) |
| `asms` | `GirAsm` | 24 | inline-asm machine code and operand bindings |
| `dlocs` | `GirDLoc` | 16 | DILocations: line, column, scope, inlined-at |
| `dscopes` | `GirDScope` | 24 | compile units, subprograms, lexical blocks |
| `dfiles` | `GirDFile` | 8 | file name and directory |
| `dstr` | `u8` | 1 | debug strings |
| `ehs` | `GirEh` | 24 | functions with landing pads: personality, type table, exception specifications |
| `comdats` | `GirComdat` | 16 | comdat groups: signature, signature symbol, kind |
| `gcomdat` | `u32` | 4 | empty, or per global: its comdat or `GIR_NONE` |
| `dies` | `GirDie` | 16 | the DWARF DIE tree of the compile unit, in pre-order |
| `dattrs` | `GirDAttr` | 16 | DIE attributes: DWARF forms, or GIR forms the back-end resolves |

Functions own contiguous ranges of `blocks` and `insts`, and blocks own
contiguous ranges of `insts`; layout order is table order. Block 0 is the
entry block. Indices are u32 and global to the module; block numbers inside
instructions are local to the function.

## Types

A type id is a u16 index into `types`. Ids 0..15 are predefined and always
present: `void`, `i1`, `i8`, `i16`, `i32`, `i64`, `ptr`, `f32`, `f64`, `f80`,
`i128`, `f16` (11), then reserved. The exporter adds a record for every
other type a value has: integers of other widths (`i24`, `i48`, `i72`, ...),
fixed vectors, structs and arrays. A struct record's fields are an `opnds`
run of (type, byte offset) pairs from LLVM's `StructLayout`.

Each type has a **value class** that tells a back-end how to hold it:

| class | types | held in |
|---|---|---|
| `INT` | `i1`..`i64` (any width), `ptr` | one general register |
| `INT2` | `i65`..`i128` | two general registers (lo, hi) |
| `FP` | `f16`, `f32`, `f64` | the low part of an SSE register |
| `X87` | `f80` (`long double`) | the x87 stack |
| `VEC` | fixed vectors | memory, one lane at a time (SSE registers at call boundaries) |
| `MEM` | structs, arrays (first-class aggregates) | memory |

`size` is the allocation size (array stride, slot size), `store` the bytes a
load or store touches: `i24` is store 3 / size 4, `f80` store 10 / size 16.
Vectors of `i1` (vector compare results) are one byte per lane; the exporter
rejects loads, stores and bitcasts of them, so their bit packing never
matters.

## Value references

An operand that names a value is a u32 with the kind in bits 31..30: `INST`
(an instruction result, module-global index), `ARG` (argument number),
`CONST` (index into `consts`) or `GLOBAL` (the address of a global).
`GIR_NONE` (0xFFFFFFFF) is "no value". The type of a reference is always in
the tables: `insts[i].ty`, `opnds[func.args + 2*i]`, `consts[i].ty`, or `ptr`.
Instructions whose meaning depends on an operand type their result does not
show carry it in `aux` (casts, compares, stores, shuffles, cmpxchg).

## Constants

`GirConst` holds any constant. `lo` is bits 0..63 of the value, zero-extended
from the type's width (`i8 -1` = 255; `f32`/`f64` as their bit pattern; the
64-bit significand of an `f80`); `hi` is bits 64..127 (the high half of an
`INT2`, the sign and exponent of an `f80`). Null is 0 with type `ptr`;
`undef` and `poison` are 0. A vector or aggregate constant points at its
`types[ty].size` bytes in `data`, or has `data = GIR_NONE` if it is all
zero. A vector or aggregate constant that holds an address cannot be bytes:
the exporter makes it a private read-only global and `LOAD`s it.

The exporter deduplicates FP, wide and aggregate constants (integer
constants are cheap to repeat), so a back-end can key a constant pool by the
constant's index.

## Instructions

`GirInst` is 24 bytes: `op`, `sub` (a predicate, overflow kind, RMW operation
or x86 intrinsic), `flags` (volatile, atomic orderings, weak cmpxchg,
single-thread scope, variadic call, noreturn call), the result type `ty`, a
secondary type `aux`, operands `a`, `b`, `c` and `dbg`. The opcodes and their
operand conventions are listed in `gir.h`; by group:

- **Control flow**: `RET`, `BR`, `CONDBR`, `SWITCH` (on any integer, including
  `INT2`), `INDIRECTBR` (with its possible targets), `UNREACHABLE`.
- **Integers**: `ADD` .. `ASHR`, `ICMP` (ten predicates), `SELECT` (any type,
  scalar or vector condition), casts `ZEXT`, `SEXT`, `TRUNC`, `PTRTOINT`,
  `INTTOPTR`, `BITCAST` (any two types of one size).
- **Floating point**: `FADD`, `FSUB`, `FMUL`, `FDIV`, `FNEG`, `FCMP` (all 16
  LLVM predicates), `FPEXT`, `FPTRUNC`, `FPTOSI`, `FPTOUI`, `SITOFP`, `UITOFP`,
  `FABS`, `COPYSIGN`, `FSQRT`, `ISFPCLASS`.
- **Memory**: `ALLOCA` (static, entry block, any alignment), `DYNALLOCA`
  (variable size), `STACKSAVE`, `STACKRESTORE`, `LOAD`, `STORE`, `GEP`
  (constant offset plus (index, scale) pairs), `MEMCPY`/`MEMSET` (constant
  size up to 256 bytes; anything else is a libc call).
- **Aggregates and vectors**: `EXTRACTVALUE`/`INSERTVALUE` (with the byte
  offset the exporter computed from the index path), `EXTRACTELT`,
  `INSERTELT`, `SHUFFLE` (mask in `opnds`). Arithmetic, compares, selects and
  casts on vector types are lane-wise.
- **Calls**: `CALL` with (value, ABI word) argument pairs; `VASTART`. An
  `invoke` is a `CALL` with `GIR_IF_INVOKE`: one more operand, the local
  block of its landing pad, and the block's terminator (the next
  instruction) is the `BR` to the normal destination.
- **Exceptions**: `LANDINGPAD`, the first instruction of a block that only
  unwind edges reach: `{ptr, i32}` from `rax`/`edx`, and its action list
  (catch type index, exception specification, cleanup). `resume` is a call
  of `_Unwind_Resume`; `llvm.eh.typeid.for` folds to the type index.
- **Bit operations**: `CTLZ`, `CTTZ`, `CTPOP`, `BSWAP`, `BITREVERSE`, `FSHL`,
  `FSHR`, `OVF` (the six `*.with.overflow`), `SCMP`, `UCMP`.
- **Atomics**: `LOAD`/`STORE` with an ordering, `CMPXCHG`, `ATOMICRMW` (13
  operations incl. `fadd`/`fsub`), `FENCE`.
- **Platform**: `TLSADDR`, `FRAMEADDR`, `RETADDR`, `SJLJ_SETJMP`,
  `SJLJ_LONGJMP` (`__builtin_setjmp`/`__builtin_longjmp`), `TRAP`,
  `DEBUGTRAP`, `BLOCKADDR`, `X86` (the SSE intrinsics clang emits for
  `<xmmintrin.h>`-style code: `maxps`, `minps`, `movmskps`, `packssdw`, the
  immediate shifts), `ASM`.

### Structural rules

These are guaranteed by the exporter and relied on by a single-pass
back-end:

- Each block ends with exactly one terminator, and terminators appear
  nowhere else. A call that does not return is still followed by one.
- PHIs come first in their block and have one (value, pred) pair per CFG
  edge (a predecessor reached by two switch edges appears twice).
- `ALLOCA`s are static, constant-size and in the entry block; every other
  alloca is a `DYNALLOCA`.
- Void instructions are never operands; an `INST` operand dominates its use
  but may come later in layout order.
- Run-time library functions are already explicit `CALL`s with the symbol in
  `globals`: i128 division (`__divti3` ...), conversions between i128 and
  FP (`__fixdfti`, `__floattidf` ...), `frem` (`fmod`, `fmodf`, `fmodl`),
  half conversions (`__extendhfsf2`, `__truncsfhf2` ...), the libm intrinsics
  (`floor`, `pow`, `fma`, `lround` ...; `powi` as `__powidf2`), and large or
  variable-size `memcpy`/`memmove`/`memset`.

## ABI

GIR leaves the plain LLVM x86-64 C convention on the argument and return
types to the back-end, plus three things the types cannot say:

- **ABI words** (one per argument, in `CALL` pairs and in `Func.args`): 0 for
  a plain argument; `GIR_ABI_BYVAL | size | log2(align) << 24` for `byval`
  (the pointee is copied to the stack argument area, aligned to
  `max(8, align)`); `GIR_ABI_SRET` marks the sret pointer for information.
- `GIR_IF_VARARG` on a `CALL` (set `al` to the number of vector registers).
- Function flags (`GirFunc.flags`): `VARARG`, `INTERNAL`, `VASTART` (needs a
  register save area), `SJLJ` (contains `SJLJ_SETJMP`), `RETURNS_TWICE`
  (calls `setjmp`, `vfork` or another `returns_twice` function: a back-end
  must not let two values share a frame slot, because the second return
  resumes with the frame as it was then), and the log2 of the alignment in
  bits 24..31.
- The exporter lowers what is not a calling-convention matter: `signext`
  arguments narrower than 32 bits are an explicit `SEXT` to i32, a `signext`
  return is an explicit `SEXT` (so `RET`'s operand may be wider than
  `ret_ty`), and an sret function returns its sret pointer (`ret_ty = ptr`).

Return types are checked to fit the return registers (`rax rdx rcx`,
`xmm0 xmm1` for scalars, `xmm0..3` for vectors, `st0 st1`); clang never
needs LLVM's sret demotion for C.

## Globals, sections and data

Every function, variable and alias that the module defines or uses gets a
`GirGlobal`; only defined functions get a `GirFunc` (`GirGlobal.func`,
otherwise `GIR_NONE`). The flags are `DEFINED`, `INTERNAL`, `CONST`, `ZERO`
(.bss), `WEAK`, `TLS`, `COMMON` (an `SHN_COMMON` symbol of `size`/`align`),
`HIDDEN`, `PROTECTED`, `LOCALREF` (LLVM's `dso_local`: references may bind
directly, without the GOT) and `RELOCS` (the initializer has relocations, so
read-only data belongs in `.data` for a PIE link). An alias (`kind = ALIAS`)
names `globals[func]` plus the byte offset in `aux`.

`section` is `GIR_NONE` (the default section for the global's kind) or an
index into `sections`: section attributes, and the `.init_array[.PRIO]` and
`.fini_array[.PRIO]` arrays the exporter builds from `llvm.global_ctors` and
`llvm.global_dtors` (one internal pointer-array global per priority).
Explicitly placed variables are never `.bss` unless the section name says so
(LLVM's rule).

A defined variable's initializer is `data[g.data .. g.data + g.size)`, laid
out with the DataLayout. Each address inside it is 8 zero bytes plus a
`GirDataReloc`: `ABS64` (a global plus addend), `BLOCK` (a block address:
function plus local block number), or `BLOCKDIFF32` (a 4-byte difference of
two blocks of one function, `&&a - &&b`, which the back-end computes itself).

`strtab` starts with a NUL byte and NUL-terminates every name, so it is the
ELF `.strtab` verbatim. Names with a leading `\01` lose it; unnamed globals
get `__unnamed_N`.

## Inline assembly

An empty template (whitespace and comments only, the usual optimization
barrier) needs no instruction: a direct output tied to an input takes that
input, other outputs are undefined, indirect outputs are unchanged. Any
other template becomes a `GIR_ASM`: the exporter binds every operand to a
register (fixed constraints as given, `r`/`q`/`g` and `x` from the
caller-saved pools, `m` as `(%reg)` holding the address, constant `i` as an
immediate), substitutes them into the template, and assembles it with
LLVM's MC layer. `GirAsm` holds the machine code and the (value, register)
inputs and (register, offset) outputs; the back-end only moves values.
x87 operands (`t`, `u`, `{st(N)}`) follow LLVM's stack rules; `x87_pop`
says how many inputs the code leaves on the stack.

## Exception handling

A function with landing pads has a `GirEh` record: its personality routine
and type table, both as globals that hold the address (`DW.ref.<name>`, a
hidden pointer variable in its own comdat, and one private stub per
typeinfo, as LLVM does for PIC, so the read-only tables need no dynamic
relocations), and its exception specifications as uleb128 lists in `data`.
Calls that are not invokes may still throw through the function: the
back-end covers them in the call-site table with no landing pad. Every
function gets an `.eh_frame` FDE, with or without EH.

## Comdat groups

`comdats` lists the module's comdats (signature, the global of that name if
there is one, `any` or `nodeduplicate`) and `gcomdat` gives each global its
comdat. The back-end gives every defined function or variable in a comdat a
section of its own (`.text.<name>`, `.data.<name>`, `.rodata.<name>`,
`.data.rel.ro.<name>`, `.bss.<name>`, ... with its `.rela` and its
`.gcc_except_table` section) in the ELF section group, as LLVM's
`-ffunction-sections`-style comdat lowering does.

Module-level assembly is parsed by the exporter with LLVM's MC for its
symbols only: what it references or marks global or weak (libstdc++ 13's
`<iostream>` emits `.globl _ZSt21ios_base_library_initv`) becomes or
updates a global; assembly that defines a symbol is unsupported.

## Debug information

With `-g`, every instruction's `dbg` names a `GirDLoc` (line, column,
scope, inlined-at), and `GirFunc.dbg` names the function's DISubprogram in
`dscopes`. Scopes form a tree (compile unit, subprograms, lexical blocks,
lexical block files) with files in `dfiles` and strings in `dstr`. Entry 0
of each table means "none". The back-end makes the line table
(`.debug_line`) from these alone.

`dies` and `dattrs` (milestone A3) carry the rest of DWARF 5: the exporter
(`tools/goovm-llc/gir_dwarf.cpp`, a port of LLVM 20's DwarfDebug and
DwarfUnit for one compile unit) builds the DIE tree that LLVM would build -
the unit, types, global variables, namespaces, imported entities,
subprograms with their parameters, variables, labels and lexical blocks,
abstract subprograms and inlined subroutines - in LLVM's DIE order. An
attribute is a DWARF form with its value, or a GIR form for what only the
back-end knows: strings (`GIR_DF_STR`, which become `strx` forms), file
numbers, function and scope code ranges (`GIR_DF_PC`, `GIR_DF_SCOPE_PC`:
low/high pc or a range list; a lexical block or inlined subroutine without
code is dropped with its variables), a variable's frame location
(`GIR_DF_LOCAL`: the GIR value that holds its address), a global's address,
a label's address, and the unit's section offsets. The back-end assigns
abbreviations, offsets and the string, address and range-list indices.
With empty `dies` (goosecc, or a module with locations only), the back-end
makes a unit with one subprogram per function.

## What the exporter drops or folds

- Debug records, `llvm.lifetime.*`, `llvm.assume`, `llvm.donothing`,
  `llvm.sideeffect`, `llvm.var.annotation`, `llvm.invariant.*`,
  `llvm.experimental.noalias.scope.decl`, `llvm.pseudoprobe`,
  `llvm.prefetch`, `llvm.va_end`, `llvm.clear_cache`.
- `llvm.expect*`, `llvm.ptr.annotation`, `llvm.annotation`, `freeze`, the
  invariant-group intrinsics and `llvm.threadlocal.address` map their result
  to their first operand.
- Calls of intrinsics with constant arguments are folded with LLVM's
  `ConstantFoldCall`, as LLVM's code generator folds them.
- `llvm.objectsize` is evaluated as LLVM's `-O0` pipeline does
  (`lowerObjectSizeCall`), `llvm.is.constant` to whether its operand is a
  constant.
- `llvm.abs`, `smin`/`smax`/`umin`/`umax` become `ICMP` + `SELECT`;
  `llvm.fmuladd` becomes `FMUL` + `FADD` (the x86-64 baseline has no FMA);
  `llvm.ptrmask` becomes integer `AND`; half arithmetic is done in float.
- Constant expressions in operands become instructions right before their
  user (for PHI operands, at the start of the entry block). So do TLS
  addresses and block addresses.

Anything else outside the format (`va_arg` instructions, scalable vectors,
`asm goto`, Intel-syntax inline assembly, Windows EH pads, ...) makes
`goovm-llc` exit with status 2 and a message that names the construct, the
function and the instruction, or, with `--fallback`, compile the module with
LLVM's code generator.

## Changes from version 0

GIR v0 (revision 1, commit 8f55b18) was the integer-and-pointer subset that
the C++ and Goose back-ends compiled byte-identically. Version 2:

1. **Type table.** Type ids are u16 indices into `types` (v0: eight fixed
   u8 type codes). The ids 0..8 keep their v0 values.
2. **Instruction record 16 → 24 bytes**: `sub` and `flags` added, `ty` and
   `aux` widened to u16, `dbg` added. `CALL`'s vararg mark moved from `sub` to
   `flags` (`GIR_IF_VARARG`).
3. **Constants 16 → 24 bytes**: `lo`/`hi` for 128-bit and `f80` values,
   `data` for vector and aggregate constants (v0 had only i64 `value`).
4. **Calls and functions carry ABI words**: `CALL` operands are (value, ABI
   word) pairs and `GirFunc.args` is a (type, ABI word) run (v0: plain
   argument refs and a type run). `GirFunc` gained `dbg` (36 → 40 bytes)
   and the flags `VASTART`, `SJLJ`, `RETURNS_TWICE` and the alignment.
5. **Globals 32 → 40 bytes** with `section` and `aux`; new kind `ALIAS`; new
   flags `TLS`, `COMMON`, `HIDDEN`, `PROTECTED`, `LOCALREF`, `RELOCS` (v0
   treated common symbols as weak .bss definitions).
6. **Data relocations 16 → 32 bytes** with a kind (`ABS64`, `BLOCK`,
   `BLOCKDIFF32`) and a 64-bit addend.
7. **New tables**: `header`, `types`, `sections`, `asms`, `dlocs`,
   `dscopes`, `dfiles`, `dstr`.
8. **51 new opcodes** (FP, aggregates, vectors, dynamic stack, va_start,
   inline copies, bit operations, atomics, TLS, setjmp/longjmp, block
   addresses, x86 intrinsics, inline asm); v0's 32 keep their numbers.
9. **Allocas**: any power-of-two alignment (v0: at most 16); non-entry and
   variable-size allocas are `DYNALLOCA`.
10. **Libcalls are explicit**: memory intrinsics with a constant size up to
    256 bytes are `MEMCPY`/`MEMSET` instead of always calling libc.

### Additions in milestone A3 (backward compatible)

The version number stays 2: every addition is either a new table that may
be empty or a new opcode or flag that older producers never emit.

1. **New entry point** `gir_codegen_ex`: `gir_codegen` plus the five new
   tables. `gir_codegen` (which goosecc calls) is unchanged and runs the
   same code with the new tables empty.
2. **New tables**: `ehs`, `comdats`, `gcomdat`, `dies`, `dattrs`.
3. **New opcode** `LANDINGPAD` (83) and flag `GIR_IF_INVOKE` on `CALL`.
4. **New attribute forms** `GIR_DF_*` and `DW_FORM_implicit_const` in
   `dattrs`; `GIR_DF_SCOPE_PC`'s `aux` names the inlined-at location of an
   instance of an inlined scope.
5. **Behaviour with the old tables**: the back-end now writes `.eh_frame`
   for every function and, when `dlocs` has locations, `.debug_line` and a
   minimal `.debug_info` even with empty `dies` - which is how goosecc's
   `-g` gets line tables without a change on its side.

## Debugging aid

`goovm-llc --dump-gir in.bc -o out.o` prints the tables as text: the header,
sections, globals, data relocations and every function with its blocks and
instructions (`%N` is the module-global instruction index, `!line:col` the
debug location).
