# GIR: goovm's flat IR

GIR is the hand-off format between LLVM and goovm's fast -O0 back-ends. The
C++ exporter (`tools/goovm-llc/gir_export.cpp`) walks an `llvm::Module` once
and fills nine flat tables. A back-end reads the tables and writes an ELF
object. There are two back-ends: the C++ reference in `backend-cpp/` and the
Goose port in `backend-goose/`. [`gir.h`](gir.h) is the normative definition;
this page describes the format in prose and records the changes made in
revision 1.

## Tables

All tables are arrays of fixed-size records. Every field is naturally
aligned and no record has padding, so the host can pass each table to Goose
as a slice (`{data, len}`) without copying. Goose sees the same bytes as its
packed structs.

| table | record | size | content |
|---|---|---:|---|
| `funcs` | `GirFunc` | 36 | defined functions: block range, instruction range, argument types, return type |
| `blocks` | `GirBlock` | 8 | basic blocks: instruction range |
| `insts` | `GirInst` | 16 | instructions: `op, ty, sub, aux` (u8 each), operands `a, b, c` (u32) |
| `opnds` | `u32` | 4 | variable-length operand runs (call arguments, PHI pairs, switch cases, GEP terms, argument types) |
| `consts` | `GirConst` | 16 | integer and pointer constants (`value` is i64) |
| `globals` | `GirGlobal` | 32 | named functions and variables: name, kind, flags, initializer range, alignment |
| `data` | `u8` | 1 | initializer bytes of all defined, non-zero variables |
| `drelocs` | `GirDataReloc` | 16 | pointer-sized relocations inside initializers |
| `strtab` | `u8` | 1 | symbol names |

Functions own contiguous ranges of `blocks` and `insts`, and blocks own
contiguous ranges of `insts`. Layout order is table order. Block 0 is the
entry block. Indices are u32 and global to the module. Block numbers inside
instructions are local to the function (relative to `GirFunc.first_block`).

## Value references

An instruction operand that names a value is a u32 reference:

```
bits 31..30  kind           bits 29..0
   0         GIR_V_INST     module-global index into insts (same function)
   1         GIR_V_ARG      argument number of the current function
   2         GIR_V_CONST    index into consts
   3         GIR_V_GLOBAL   index into globals (the value is its address)
GIR_NONE = 0xFFFFFFFF: no value (ret void)
```

The macros are `GIR_KIND(v)`, `GIR_IDX(v)` and `GIR_MK(kind, idx)`. Every
reference has a type that can be read from the tables:

| kind | type |
|---|---|
| INST | `insts[i].ty` |
| ARG | `opnds[func.arg_tys + i]` |
| CONST | `consts[i].ty` |
| GLOBAL | `GIR_T_PTR` |

So GIR never repeats a type at a use. The exceptions are the instructions
whose meaning depends on an operand type the result does not show: ICMP
(`aux` = operand type), casts (`aux` = source type) and STORE (`aux` =
stored type). An instruction that defines no value (`ty = GIR_T_VOID`) is
never an operand.

Instructions refer to their operands only. There are no use lists. A back-end
that needs uses (for liveness, say) builds them in one pass.

## Instructions

The opcodes are listed in `gir.h`. Operands that are not value references
are immediates or block numbers (BR targets, ALLOCA size and alignment) or
indices of `opnds` runs:

- `CALL a=callee, b=s, c=n`: `opnds[s..s+n)` are the arguments.
  `sub & GIR_F_VARARG` marks a variadic callee (the SysV caller sets `al`).
- `PHI b=s, c=n`: n pairs `(value, pred block)`.
- `SWITCH a=cond, b=s, c=n`: `opnds[s]` is the default block, followed by n
  pairs `(const ref, block)`.
- `GEP a=base, b=s, c=n`: `opnds[s]` and `opnds[s+1]` are the low and high
  halves of a constant i64 byte offset. They are followed by n pairs
  `(index ref, scale)`. Result = `base + offset + sum(sext64(index) * scale)`.

The exporter folds constant GEP indices and struct field offsets into the
offset, using the module's DataLayout. A GEP with no dynamic index and offset
0 is not emitted: its users refer to the base directly.

## What the exporter lowers or drops

- `llvm.memcpy`, `llvm.memmove`, `llvm.memset` (and the `.inline` forms)
  become CALLs of libc `memcpy`, `memmove` and `memset` with three arguments.
  The `isvolatile` flag is dropped.
- `llvm.abs`, `llvm.smin`, `llvm.smax`, `llvm.umin` and `llvm.umax` become
  ICMP + SELECT (abs also gets a SUB). clang -O0 emits `llvm.abs` for
  `abs()`.
- The exporter drops these intrinsics: `llvm.lifetime.*`, `llvm.dbg.*`,
  `llvm.experimental.noalias.scope.decl`, `llvm.assume`, `llvm.donothing`,
  `llvm.sideeffect`, `llvm.var.annotation`, `llvm.invariant.*` and
  `llvm.pseudoprobe`. It also drops `llvm.trap` when `unreachable` follows
  it, because that already traps.
- `llvm.expect`, `llvm.ptr.annotation`, `freeze` and the
  launder/strip.invariant.group intrinsics map their result to their first
  operand.
- `undef` and `poison` become the constant 0.
- Constant expressions in operands (GEP, casts, integer binops) become GIR
  instructions right before their user. If a PHI uses one, it is built once
  at the start of the entry block, because the entry block dominates every
  predecessor.
- The exporter lowers ABI attributes. An argument with `signext` and a type
  narrower than 32 bits goes through an explicit `SEXT` to i32, as clang's
  callees expect. A return value with `signext` gets the same treatment. A
  function with an `sret` parameter returns that pointer (`ret_ty = ptr`),
  as SysV requires.

Anything else outside the subset makes `goovm-llc` exit with status 2 and an
error message that names the function and the instruction. Examples are
floating point, vectors, odd-width integers such as i48 (structs of 3, 5, 6
or 7 bytes passed by value), aggregate SSA values, `byval`, `va_start` and
`va_arg`, dynamic allocas, inline asm, exceptions, atomics, TLS, aliases and
custom sections.

## Globals and data

Every function and every variable that the module defines or uses gets a
`GirGlobal`. Functions get a `GirFunc` only if they are defined
(`GirGlobal.func`, otherwise `GIR_NONE`). The flags are `DEFINED`,
`INTERNAL` (local linkage), `CONST` (read-only), `ZERO` (all-zero
initializer: it has no bytes in `data` and goes to .bss) and `WEAK`. The
exporter skips declarations without uses and the intrinsics.

The initializer of a non-zero variable is `data[g.data .. g.data+g.size)`.
It is laid out with the DataLayout (struct padding included). A pointer in an
initializer is written as 8 zero bytes plus a `GirDataReloc`
`(owner, offset, target, addend)`. This covers pointers to variables,
functions and string literals, plus constant offsets such as `"abc" + 1` or
`&arr[3]`. The relocations of one variable are contiguous.

`strtab` starts with a NUL byte and each name is followed by a NUL byte. So
the back-end can use it as the ELF `.strtab` verbatim (`st_name =
GirGlobal.name`). Names with a leading `\01` lose it. Unnamed globals get
`__unnamed_N`.

## Changes in revision 1

Revision 1 is a clarification of v0 plus one additive flag. A back-end
written against v0 keeps working, except for the GIR_FN_DECL change in
point 4.

1. **Constants are zero-extended.** `GirConst.value` is the bit pattern
   zero-extended from the type's width (i8 -1 is 255). v0 did not say. With
   this rule a back-end that keeps narrow values zero-extended can use
   constants as immediates without masking them, and switch case values can
   be compared directly.
2. **`GIR_GF_WEAK` (16).** This flag is new: weak, linkonce(_odr), common and
   extern_weak symbols need `STB_WEAK` to link (C `__attribute__((weak))`
   and linkonce/common symbols, e.g. from `-fcommon` tentative definitions).
3. **Structural rules are normative.** These were implicit in v0 and now
   appear in the header comment:
   - Each block ends with exactly one terminator.
   - PHIs come first in their block and have one pair per CFG edge.
   - ALLOCAs are static, sit in the entry block and have alignment ≤ 16.
   - Void instructions are never operands.
   - An INST operand dominates its use but may come later in layout order.

   A single-pass back-end relies on all of these.
4. **Declarations get no `GirFunc`.** Only defined functions are in `funcs`.
   Undefined ones have `GirGlobal.func = GIR_NONE`. In v0 the
   `GIR_FN_DECL` flag suggested that declarations had entries. Giving them
   entries would force the exporter to encode types of functions that are
   never called, such as `double sqrt(double)` whose address is taken. The
   flag stays defined but is not produced.
5. **The exporter lowers ABI extension and sret** (see above). Otherwise
   every back-end would need per-argument attribute tables to be
   ABI-compatible with clang-compiled code. The rule is "callee may assume
   `signext` arguments are sign-extended to 32 bits", and clang's callees
   rely on it.
6. **GEP index typing is stated.** The index type is the type of the index
   value, and every index is sign-extended to 64 bits. v0 left this open.
7. **`strtab` is NUL-terminated per name** (see above). This saves the
   back-end a copy, and `name_len` stays valid.
8. **Size checks.** `gir.h` has `static_assert`s on all record sizes. It also
   notes that `GirModule` is a host-side view whose padding is irrelevant,
   because it is never passed to Goose.

The record layouts did not change. In the Goose mirror the field
`GirConst.pad` is called `reserved`, because `pad` is a Goose keyword. Only
the offset matters.

## Debugging aid

`goovm-llc --dump-gir in.bc -o out.o` prints the tables as text. It shows
globals, data relocations and every function with its blocks and
instructions, `%N` being the module-global instruction index.
