# The Goose back-end (v1): design

`backend-goose/` turns GIR version 2 tables ([`../gir/README.md`](../gir/README.md))
into an ELF64 x86-64 relocatable object. It compiles everything clang-20
emits at -O0 for C on x86-64 Linux (SysV ABI, PIE), with and without `-g`,
and the same IR after `opt -passes=mem2reg`. It is written in Goose and
called from `goovm-llc` (C++) through one `export fn`.

v1 is still an -O0 code generator: one pass per function, every value in a
frame slot. What is new against v0 (the 1:1 port of the frozen C++
back-end, commit 8f55b18) is the coverage and the structure: instruction
lowerings no longer touch frame slots themselves but go through a small
value-location interface, so that a register allocator (milestone A2) can
replace the "always spill" policy behind it without rewriting the lowerings.

## 1. Files

| file | content |
|---|---|
| `cg.goose` | root: imports, module state, PHI moves, terminators, `gen_inst` (the opcode dispatch), frame layout and prologue (`gen_function`), function ordering, the exported entry `gir_codegen` |
| `gir.goose` | the GIR v2 records (mirrors of `gir.h`) and constants |
| `x86.goose` | byte output, memory operands, the x86-64 encoder (general registers, SSE2, x87), branch fixups |
| `loc.goose` | **the value-location interface**, value homes, normalization of narrow integers, memory copies, constant pools |
| `abi.goose` | SysV classification of arguments and returns, calls, argument spilling, `va_start` |
| `lower.goose` | the instruction lowerings (integer, INT2, floating point, x87, vectors, aggregates, atomics, TLS, bit operations, inline asm, ...) |
| `elf.goose` | output sections, symbols, data layout, relocations and the ELF writer |
| `CMakeLists.txt` | runs `goose --standalone --header cg.h -o cg.c cg.goose` and builds the C |

`goose` compiles the whole program from `cg.goose` (an `import` includes a
file once) into one C file. The encoder and byte-output layer is
`checkfree`: the compiler proves that no bounds check is left in it.

## 2. Passes

```
gir_codegen(tables):
  reset module state (code, data buffers, pools, relocation lists)
  make_sections()          fixed default sections + one per GIR section
  layout_globals()         symbol numbering, globals grouped by section, data placement
  gen_functions()          per code section, per function: gen_function(fi)
  resolve_blockaddrs()     patch lea rip+disp of block addresses
  resolve_aliases()        aliases take their target's section and value
  write_elf()              relocations grouped by section, symbol table, headers
```

`gen_function` is the per-function pass: a frame-layout loop over the
instructions (homes of results, alloca areas, PHI temp slots; §5), the
prologue, then `gen_inst` for every instruction of every block in layout
order, then the branch fixups. Nothing walks the IR twice except the
frame-layout loop; there are no hash maps; all state is flat arrays indexed
by GIR indices (`v_off[local inst]`, `a_off[arg]`, `block_off[local block]`,
`blk_code[global block]`, `c_pool[const]`, `g_sym[global]`, ...).

## 3. Values: classes and homes

A value's GIR class (`gir.h`) decides how it is held:

| class | home size | in registers |
|---|---:|---|
| `INT` (i1..i64, ptr) | 8, zero-extended | one GPR, zero-extended to 64 bits |
| `INT2` (i65..i128) | 16 (lo, hi) | two GPRs |
| `FP` (f16, f32, f64) | 8 | an SSE register (f16 as a 16-bit pattern) |
| `X87` (f80) | 16 (10 used) | the x87 stack, only inside one instruction |
| `VEC` | size rounded to 8 | memory; SSE registers only at call boundaries |
| `MEM` (structs, arrays) | size rounded to 8 | memory |

**Narrow integers are kept zero-extended** to 64 bits (in registers and in
homes). Every operation that can produce higher bits normalizes its result
(`zext_reg`: `and`, `movzx`, `mov r32, r32`, or a shift pair for odd
widths); operations that need the sign (signed compares, division, `ashr`,
`sext`, GEP indices, `sitofp`) sign-extend a copy first (`sext_reg`). Odd
store sizes (i24 = 3 bytes, i48 = 6, ...) are loaded and stored in pieces
(`load_n`, `store_n`).

Homes, per local instruction `j`:

- `H_SLOT`: `v_off[j]` is the rbp offset of its result slot;
- `H_ALLOCA`: the value is the address `rbp + v_off[j]` (a static alloca of
  alignment <= 16);
- `H_PTR`: the value is the pointer stored at `rbp + v_off[j]` (an
  over-aligned alloca, aligned at run time in the prologue).

Arguments are `A_SLOT` (spilled into a slot by the prologue) or `A_BYVAL`
(the value is the address `rbp + a_off[a]` of the caller's copy). Constants
are immediates (`INT`) or pool entries; globals are `lea rip+sym` or a GOT
load.

## 4. The value-location interface (A2's plug-in point)

All lowerings reach operands and results through these functions in
`loc.goose`:

| function | meaning | A1 policy |
|---|---|---|
| `use_gpr(v, r) -> u32` | INT value `v` in a register, zero-extended; `r` is the suggestion; returns the register holding `v` | loads into `r` (`mov`, `lea` for allocas/globals, `mov r, imm` for constants); writes only `r` |
| `use_fixed(v, r)` | `v` in exactly register `r` (shift counts, division, call arguments, inline-asm operands) | = `use_gpr` |
| `use_gpr2(v, lo, hi)` | INT2 value in two registers | two loads or two immediates |
| `use_xmm(v, x) -> u32` | FP value in an SSE register | `movss`/`movsd` from the home or the pool |
| `val_mem(v) -> Mem` | the bytes of a non-INT value (or an INT slot) as a memory operand | its slot, or its constant-pool entry |
| `addr_of(v, scratch) -> Mem` | a memory operand addressing the pointer value `v` | `[rbp+d]` for allocas and byval arguments, `[rip+sym]` for dso-local globals, else `use_gpr(v, scratch)` and `[scratch]` |
| `def_gpr(j, r) -> u32` | the register to compute result `j` in | `r` |
| `put_gpr(j, r)` | the INT result of `j` is in `r` (zero-extended) | `mov [slot], r` |
| `put_gpr2(j, lo, hi)`, `put_xmm(j, x, t)` | likewise for INT2 and FP | stores |
| `res_mem(j) -> Mem` | the home of `j` for results built in memory (X87, VEC, MEM, struct fields) | `[rbp + v_off[j]]` |
| `copy_val(dst, v, n)` | copy `n` bytes of `v` (any class) to `dst` | register or memory copy |

Rules the lowerings follow, which a register allocator can rely on:

- An instruction's operands are fetched before its result is defined, and
  every result is defined exactly once (PHIs through their temp slot, see
  below).
- Fixed-register needs are explicit (`use_fixed`): `rcx` for variable shift
  counts, `rax`/`rdx` for division and `mul`, the argument registers and
  `r11` for calls, `rsi`/`rdi`/`rcx` for `rep movsb`/`stosb`, `rax`/`rdx` and
  the memory operand for `cmpxchg`, inline-asm bindings.
- Scratch registers used *inside* a lowering are caller-saved and never hold
  values across instructions: `rax rcx rdx rsi rdi r8 r9 r10 r11`,
  `xmm0..xmm3`. `load_n`/`store_n` of 3/5/6/7-byte integers use `r10`/`r11`.
  A2 must treat them as clobbered by the lowering (or reserve them).
- Calls clobber all caller-saved registers; under A1 nothing is live in a
  register across an instruction, so nothing is saved.
- A local value's slot is only valid between its definition and its last
  use (`v_span`, §5): the backward layout pass is the liveness A2 can build
  on (last use per value, local vs. used across blocks).
- The x87 stack is empty between instructions.

To plug in a register allocator, A2 changes `use_gpr`/`use_xmm` to return
the register a value lives in (or reload it), `def_gpr` to choose the
result register, `put_gpr` to record the location instead of storing, and
adds spill/reload logic around `use_fixed`, calls and block boundaries
(PHI moves and fixups are already centralized in `phi_moves` and the
terminator lowerings). The lowerings that still name `RAX`/`RCX` directly
after `use_fixed` are the places where A2 can widen the interface
gradually.

## 5. Frame layout

```
rbp+16..        stack arguments (byval copies are used in place)
rbp+8           return address
rbp             saved rbp (rbp is 16-byte aligned)
rbp-8..-40      rbx, r12..r15        only if the function calls __builtin_setjmp
                scratch, 32 bytes    x87 control words, conversion temporaries
                register save area   176 bytes, only if the function calls va_start
                argument slots
                result slots, PHI temp slots, alloca areas (each at its alignment)
rsp             16-byte aligned; dynamic allocas and outgoing call areas below
```

**Slot sharing.** Functions of more than 256 instructions are laid out by
one backward pass (`layout_shared` in `cg.goose`) that also finds each
value's last use: scanning backward, the first use seen is the last one, so
the value takes a slot there and gives it back at its definition. A value
whose uses are all in its own block ("local"; a PHI's incoming value is used
by the predecessor's terminator) shares 8- and 16-byte slots with other local
values; a value used in another block keeps its own slot. Local values of
different blocks are never live at the same time, so this needs no liveness
across blocks. A use above its definition in layout order is detected and
the function is laid out again with one slot per value, as are functions
that call `setjmp` or another `returns_twice` function (`GIR_FN_RETURNS_TWICE`,
`GIR_FN_SJLJ`) and functions of at most 256 instructions (whose value slots
are at most ~2 KB; the backward pass costs about as much as the rest of the
layout). One slot per value made consumer-typeset's recursive `Manifest`
(16 000 instructions) take a 97 KB frame and overflow the 8 MB stack; with
sharing it is 2.9 KB (clang -O0: 2.1 KB). `v_span[j]` records the last use;
`live_check` in the value-location interface aborts if a lowering reads a
local value outside [definition, last use], so a use that the layout's
operand table (`OP_USES`) missed cannot silently read another value.

`frame = align_up(off, 16)`; the prologue is `push rbp; mov rbp, rsp; sub
rsp, frame`, then the callee-saved and va register saves, the argument
spills, and the run-time alignment of over-aligned allocas. Every frame
access is rbp-relative, so `DYNALLOCA` (`sub rsp, round16(n); and rsp,
-align`), `STACKRESTORE` and the per-call `sub rsp, n` / `add rsp, n` never
disturb addressing.

## 6. Instruction selection

| GIR | code |
|---|---|
| integer binops | `rax op rcx` (`imm32` forms for constant second operands of add/sub/and/or/xor and constant shift counts); normalize |
| sdiv/srem, udiv/urem | sign-extend, `cqo; idiv rcx` / `xor edx, edx; div rcx` |
| icmp | `cmp rax, rcx` or `cmp rax, imm32`; `setcc al; movzx` |
| INT2 | `add/adc`, `sub/sbb`, pairwise logic, three-multiply `mul`, `shld/shrd` + `test cl, 64` shifts, `cmp/sbb` compares; division and FP conversions are libcalls (exporter) |
| f32/f64 | `movss/movsd`, `addss/sd` ..., `ucomiss/sd` + setcc (one or two flags per predicate), `cvtsi2s*`, `cvtts*2si`, `cvtss2sd`/`cvtsd2ss`; unsigned 64-bit conversions with the 2^63 split |
| fneg, fabs, copysign | integer bit operations on the bit pattern (`btc`, `btr`, masks) |
| f80 | `fld tbyte`, `faddp/fsubp/fmulp/fdivp`, `fstp tbyte`; `fucomip` compares; `fistp` under a truncating control word; `fild` (+ 2^64 for unsigned) |
| vectors | lane by lane in memory with the scalar operations; vector homes are copied at lane granularity (a wider load of narrower stores misses store-to-load forwarding) |
| select | `cmov` for INT/FP, branches around copies otherwise |
| load/store | `addr_of` + typed moves; seq_cst stores are `xchg`; odd sizes in pieces |
| memcpy/memset (<= 256) | 8-byte moves through rax, `rep movsb`/`rep stosb` above 64 bytes |
| ctlz/cttz | `bsr`/`bsf` + `cmov` for zero; ctpop the bit-twiddling sequence (no `popcnt` in the baseline) |
| overflow | 64-bit op on extended operands + `seto`/`setc`/range check |
| cmpxchg, atomicrmw | `lock cmpxchg`, `lock xadd`, `xchg`, `lock cmpxchg` loops for the rest |
| TLS | PIE: local-exec (`mov rax, fs:0; lea rax, [rax+sym@tpoff]`) for definitions, initial-exec (`add rax, [rip+sym@gottpoff]`) for others; non-PIE: the general-dynamic sequence calling `__tls_get_addr` |
| sjlj | setjmp stores a `lea rip`-resume address into word 1 of the buffer; longjmp restores rbp, rsp and jumps |
| blockaddress | `lea rax, [rip + disp]`, patched once all blocks are placed |
| inline asm | inputs into their registers (x87 ones pushed deepest first), the assembled bytes, outputs out of theirs |

PHIs keep v0's scheme: each PHI has a temp slot and a result slot; every
edge writes the temp slots of the target's PHIs (`phi_moves`), the PHI
itself copies temp to result at the start of its block, which gives
parallel-copy semantics. `INDIRECTBR` writes the temp slots of all its
possible targets.

## 7. Calls and the ABI

`classify(type, abi word)` walks the arguments with LLVM's x86-64 C rules
(`abi.goose` header comment) and is shared by calls (`lower_call`) and the
callee prologue (`spill_args`):

1. classify all arguments; `sub rsp, align16(stack bytes)`;
2. store stack arguments and copy byval pointees (through `rax`, or `rep
   movsb` with `rsi`/`rdi`/`rcx`) first, because they use scratch registers;
3. load an indirect callee into `r11`, then the register arguments (only the
   target register is written, so the order does not matter);
4. variadic callee: `mov eax, <xmm registers used>`;
5. `call rel32` (PLT32) or `call r11`; `add rsp, n`;
6. take the result from `rax`/`rdx`/`rcx`, `xmm0..3`, `st0`/`st1` by the
   return classification (`classify_ret` walks the struct leaves).

Returns use the same classification in the other direction. A variadic
function with `va_start` saves `rdi..r9` and, if `al != 0`, `xmm0..7` into
its register save area; `va_start` fills the 24-byte `va_list` (gp_offset,
fp_offset, overflow area = rbp + 16 + named stack bytes, save area). clang
lowers `va_arg` itself.

## 8. Constants

`INT` constants are immediates. Other constants are pooled on first use,
keyed by the constant's index (the exporter deduplicates them):
f32/f16 in `.rodata.cst4`, f64 in `.rodata.cst8`, f80, i128 and 16-byte
vectors in `.rodata.cst16` (all `SHF_MERGE`), vectors and aggregates of other
sizes at the end of `.rodata`. Entries of the mergeable pools are referenced
through a local symbol each: linkers resolve a section-symbol relocation
into a mergeable section by its addend, which for a rip-relative operand is
`offset - 4` and would name the wrong piece. Pool symbols are numbered
provisionally (`POOL_BASE + k`) and placed after the local globals when the
object is written.

## 9. ELF writer

Sections: `.text` (and custom code sections), `.data`, `.bss`, `.rodata`,
`.rodata.cst4/8/16`, `.tdata`, `.tbss`, then one per GIR section (custom
data sections, `.init_array[.N]`, `.fini_array[.N]`), then `.rela.<name>`
for each section with relocations, `.symtab`, `.strtab` (the GIR string
table verbatim), `.shstrtab` and `.note.GNU-stack`. Functions are generated
grouped by code section, so each code section is a contiguous range of the
code buffer; data sections are laid out section by section from a counting
sort of the globals.

Symbols: null, one `STT_SECTION` per output section, local globals, pool
entries, then the other globals (`STB_GLOBAL`/`STB_WEAK`, `STT_FUNC`,
`STT_OBJECT`, `STT_TLS`, visibility in `st_other`, `SHN_COMMON` for common
symbols, aliases with their target's section and value).

Relocations: `R_X86_64_PC32` (rip-relative data and code addresses),
`R_X86_64_PLT32` (calls), `R_X86_64_REX_GOTPCRELX` (addresses of
preemptible symbols), `R_X86_64_64` (data), `R_X86_64_TPOFF32` and
`R_X86_64_GOTTPOFF` (TLS in PIE), `R_X86_64_TLSGD` (general-dynamic TLS).
Block-address data relocations are `R_X86_64_64` against the function
symbol plus the block's offset; label differences are resolved in place.

## 10. Speed

The back-end stays a single pass with flat arrays. Compared with v0 it does
more per instruction (a type-table lookup for the class of each operand and
result, and a larger dispatch), see `backend-goose/NOTES.md` for the
measurements.
