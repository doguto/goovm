# The Goose back-end (v2): design

`backend-goose/` turns GIR version 2 tables ([`../gir/README.md`](../gir/README.md))
into an ELF64 x86-64 relocatable object. It compiles everything clang-20
emits at -O0 for C and C++17 on x86-64 Linux (SysV ABI, PIE), with and
without `-g`, and the same IR after `opt -passes=mem2reg`. It is written in
Goose and called from `goovm-llc` and `goovm-cc` (C++) and from `goosecc`
(Goose) through two `export fn`s (`gir_codegen`, `gir_codegen_ex`).

Milestone F1 added a second target, AArch64 (aarch64-linux-gnu, ELF64,
LP64, AAPCS64), selected by the GIR header (§17): its own instruction
selection, register allocators, calling convention, frame, unwind
information, DWARF registers and ELF relocations in the `a64*.goose` files,
sharing the GIR reader, the middle-end, the liveness analysis of the global
allocator, the ELF/DWARF/`.eh_frame` writers and the LSDA builder with
x86-64 behind target-dispatch points. x86-64 objects are unchanged.

Milestone E1 added an optimizing mode. When the GIR header's `opt_level`
is 1 or more (`goovm-llc -O1`, `goovm-cc -O1`, `goosecc -O1`), a middle-end
written in Goose optimizes the tables before code generation (§15:
mem2reg and SROA, instruction simplification, dominator CSE with load
forwarding, SimplifyCFG with jump threading and if-conversion, inlining,
tail recursion elimination, loop rotation, LICM with scalar promotion of
globals, induction variable widening, DCE), and the values that live across blocks get a
register for their whole live range from a global allocator (§16), with
the -O0 block-local allocator working around them. At `opt_level` 0 none
of it runs and the objects are byte-identical to the previous milestone's.

Milestone C1 brought floating-point-heavy code to the speed of clang -O0's
(§14; `NOTES.md` §11): small aggregates returned in registers no longer go
through memory in ways that miss store-to-load forwarding, conversions break
their false dependency on the destination, a GEP's base pointer is loaded in
program order, `is.fpclass` has fast paths, and the epilogue is LLVM's
`add rsp, n` instead of `leave`.

Milestone A3 added what a debugger, an unwinder and a C++ program need:
`.eh_frame` for every function with CFI exact at every instruction (§10),
C++ exception tables (§11), comdat groups (§9) and DWARF 5 debug
information as clang -g writes it (§12).

v2 (milestone A2) is a fast -O0 code generator in the class of LLVM's
`-O0` pipeline (FastISel + RegAllocFast) and TPDE: a liveness pre-pass and
one code-generation pass per function, values in registers, compares fused
with their branch, immediates, memory operands and address modes folded into
instructions. v1 (milestone A1) kept every value in a frame slot and
reloaded it for every use; its lowerings already reached operands and
results through a small value-location interface, and v2 replaced the
policy behind that interface (§4) instead of the lowerings, except for the
frequent instructions, which got allocator-aware lowerings (§6).

## 1. Files

| file | content |
|---|---|
| `cg.goose` | root: imports, module state, the dispatch (`gen_inst`: allocator-aware or legacy), PHI moves, terminators, frame and prologue/epilogue (`gen_function`), function placement, the exported entry `gir_codegen` |
| `gir.goose` | the GIR v2 records (mirrors of `gir.h`) and constants |
| `x86.goose` | byte output, memory operands (`[reg+disp]`, `[base+idx*s+disp]`, `[rip+sym]`), the x86-64 encoder (general registers, SSE2, x87), short and long branches |
| `ra.goose` | **register allocation**: per-value records, the liveness pre-pass, frame slots, register file, allocation, eviction, spilling, deferred loads and addresses, the allocator-aware value interface (`ra_gpr`, `ra_xmm`, `ra_set`, ...) |
| `loc.goose` | type helpers, normalization, memory copies, constant pools, global addresses, and the legacy value interface (`use_gpr`, `val_mem`, `put_gpr`, ...) for the legacy lowerings |
| `lowera.goose` | allocator-aware lowerings: integer ops, compares, selects, casts, loads/stores, GEP, FP, vectors in xmm registers, memcpy/memset |
| `abi.goose` | SysV classification, calls (parallel argument moves), returns, argument homes and the prologue's argument code, `va_start` |
| `lower.goose` | legacy lowerings (A1): INT2, x87, vectors in memory, aggregates, bit operations, atomics, TLS, sjlj, inline asm, ... |
| `elf.goose` | output sections (incl. comdat sections and groups), symbols, data layout, relocations and the ELF writer |
| `eh.goose` | `.eh_frame` (CIEs, FDEs, CFI from the prologue/epilogue events) and the LSDAs in `.gcc_except_table` |
| `dwarf.goose` | DWARF 5: line-table rows and scope ranges recorded during code generation, then `.debug_info`/`abbrev`/`str`/`str_offsets`/`addr`/`line`/`line_str`/`rnglists` |
| `opt.goose` | **middle-end** (E1, §15): the working form (OIR), loading and storing functions, canonical constants, the module driver (`opt_module`) and the pass pipeline (`opt_function`) |
| `opt_cfg.goose` | CFG, reverse post-order, dominators and dominator tree, dominance frontiers, natural loops, unreachable blocks |
| `opt_ssa.goose` | use lists, mem2reg, trivial PHIs, DCE |
| `opt_sroa.goose` | scalar replacement of aggregates |
| `opt_fold.goose` | instruction simplification: folding, identities, strength reduction, division by constants, compares, casts, GEPs |
| `opt_gvn.goose` | dominator CSE with load forwarding and local dead-store elimination |
| `opt_scfg.goose` | SimplifyCFG: constant branches, block merging, empty-block forwarding, jump threading over PHIs, if-conversion to selects |
| `opt_inline.goose` | call graph, function order, inlining, tail recursion elimination |
| `opt_licm.goose` | preheaders, loop-invariant code motion, GEP splitting, loop rotation, scalar promotion of globals, layout loop rotation |
| `opt_iv.goose` | sign-extension distribution and induction-variable widening |
| `opt_verify.goose`, `opt_dump.goose` | `GOOVM_OPT=verify` (SSA and CFG invariants after optimization) and `GOOVM_OPT=dump` (text dump of the optimized tables) |
| `rag.goose` | **global register allocation** (E1, §16): liveness, live segments, clobbers, assignment, and the hooks the code generator calls |
| `a64enc.goose` | **AArch64** (F1, §17): the A64 encoder (integer, FP, SIMD, loads/stores with their offset forms, exclusives, branches with fix-ups), relocation numbers |
| `a64ra.goose` | AArch64 register classes, homes, the block-local allocator, constants (pools, `adrp`/`add`, GOT) |
| `a64low.goose` | AArch64 allocator-aware lowerings (integer, compares fused with branches and selects, casts, FP, loads/stores with folded addresses, GEP, funnel shifts, `fence`) |
| `a64mem.goose` | AArch64 memory-tier lowerings: i128, fp128 libcalls, lane-wise vector operations, overflow, `is.fpclass`, aggregates |
| `a64abi.goose` | AAPCS64: classification (HFA/HVA blocks, i128 pairs, vector legalization), calls, returns, parameters, `va_start` |
| `a64atom.goose` | AArch64 atomics (outline-atomics helpers, LL/SC loops, 16-byte), TLS (LE/IE/TLSDESC), sjlj, inline asm binding, landing pads |
| `a64neon.goose` | `GIR_A64`: NEON, crypto, CRC32, exclusives, barriers, system registers |
| `a64cg.goose` | AArch64 code generation per function: kinds, PHIs, terminators, jump tables, frame, prologue/epilogue and CFI events, far branches |
| `a64rag.goose` | AArch64 global register allocation on `rag.goose`'s analysis |
| `CMakeLists.txt` | runs `goose --standalone --header cg.h -o cg.c cg.goose` and builds the C |

`goose` compiles the whole program from `cg.goose` (an `import` includes a
file once) into one C file. The encoder and byte-output layer is
`checkfree`: the compiler proves that no bounds check is left in it.

## 2. Passes

```
gir_codegen(tables):
  reset module state; register classes of all types (t_rc)
  dbg_init(); make_sections() (with comdat, .eh_frame, except and debug
  sections); layout_globals()
  opt_module()       only at opt_level >= 1 (§15): M is replaced by the
                     optimized tables
  gen_functions(): per code section, per function: gen_function(fi)
  resolve_blockaddrs(); resolve_aliases(); dbg_write(); write_elf()

gen_function(f):
  ra_prepass()       uses, last use, local/global, call-spanning values,
                     memory writes between a load and its use, register
                     hints, the lowering kind of every instruction
  rg_alloc()         only at opt_level >= 1 (§16): registers for the values
                     that live across blocks
  frame setup        callee-saved save area (as many as call-spanning values,
                     at most 5), va save area, allocas, argument homes
  body               per block: register file reset, gen_inst per instruction
  epilogue           (pseudo-block n_blocks; returns that are not last jump to it)
  fixups             forward branches within the function
  prologue           emitted last, when the frame size and the callee-saved
                     registers in use are known; placed before the body
  eh_func_end        the FDE (and LSDA) of the placed function
  dbg_func_end       rows and runs rebased, variables' frame offsets,
                     lexical block and inlined subroutine ranges
```

With `-g`, `gen_function` also calls the `dbg_*` hooks of `dwarf.goose`
around every block and instruction (§12); without it they are not called.

The function's code is generated into a per-function buffer (`code`);
`gen_function` appends prologue and body to the module's code (`mcode`) and
rebases the function-relative relocation, block-address and block offsets.
There are no hash maps; all per-function state is flat arrays indexed by
local instruction index (`vi[j]`), block number, or register.

## 3. Values: classes and homes

A value's register class (`t_rc`, from the GIR class and size) decides
where it can live:

| class | GIR types | register | home (frame slot) |
|---|---|---|---|
| `RC_GPR` | `INT` (i1..i64, ptr) | one general register | 8 bytes, the low 1/2/4/8 bytes written |
| `RC_XMM` | f32, f64 | one xmm register | 8 bytes |
| `RC_VX` | vectors of 8 or 16 bytes with i8/i16/i32/i64/f32/f64 lanes | one xmm register | 8 or 16 bytes |
| `RC_MEM` | `INT2`, f16, f80, other vectors, aggregates | memory only | size rounded to 8 (16-aligned from 16) |

**Widths.** An i32 is computed with 32-bit instructions, whose results are
zero-extended for free; i64 and pointers with 64-bit ones. A value of 8, 16
or 32 bits may carry garbage above its width in its register (`ST_EXT`):
the result of an i8/i16 operation done in 32 bits, a `trunc` (a copy of the
wider register), an incoming argument, a call result. Uses that need clean
upper bits (zext, 64-bit arithmetic on narrow values, uitofp, division,
right shifts, narrow call arguments) normalize; stores, compares at the
value's width, 32-bit operations and further narrowing do not. Odd widths
(i1, i24, i48, ...) are always kept zero-extended. Homes are written and
read with the value's width (`store_int`/`load_int`), so a dirty register
can be spilled as is.

Homes (`vi[id].home`, offset `vi[id].off`): `H_SLOT` (a frame slot,
allocated on first need), `H_ALLOCA` (the value is the address `rbp + off`
of a static alloca), `H_PTR` (over-aligned alloca: the pointer is stored
at `rbp + off`), `H_BYVAL` (argument: address of the caller's copy),
`H_STACK` (argument passed on the stack: its home is the incoming slot).

## 4. Register allocation

**Pre-pass** (`ra_prepass`, one forward walk over the function's
instructions and successor PHIs). Per value (instruction result or
argument, a 16-byte `VInfo` record):

- `nuse` (saturating), `st & ST_GLOB` if any use is in another block (a PHI
  incoming value is used at the predecessor's terminator), else `last`, the
  position of the last use;
- `ST_CS` if a call or legacy lowering lies between the definition and the
  last use (the value prefers a callee-saved register); the function reserves
  as many callee-saved registers as it has such values (at most 5; all 5 if
  it contains inline assembly or `__builtin_setjmp`);
- `ST_NODEF` if a memory write lies between a load and its use, or the use
  is a legacy lowering (no deferred load);
- `hint`: the register a return value or a plain call argument is wanted in
  (also given to the operand of an integer/pointer conversion that is
  such an argument, e.g. `(void *)(long)i`). Lowerings with a
  three-operand form (`lea`, `imul r, r/m, imm`, `movsx`, loads, `setcc`)
  write the result straight into a free hint register instead of reusing a
  dying operand's register;
- `kind`: how the instruction is lowered (allocator-aware `K_A`, call, legacy
  `K_B`, or legacy clobbering every register `K_ALL`).

A block whose PHIs read each other on an edge (swaps, rotations), and the
targets of `indirectbr`, use a temp slot per PHI (parallel copy); other
PHIs are written in place by the edges.

**Policy.** Local values (all uses in their block) live in a register from
their definition to their last use; global values are stored to their home
when they are defined ("write-through", like RegAllocFast for live-out
values) and a register copy is a cache for later uses in the block. Every
block starts with all registers free (PHIs and global values are in their
homes; arguments are in their registers at the start of the entry block).
So nothing is spilled at block ends, and loop-carried values (mem2reg) go
through memory at block boundaries, as with LLVM -O0.

**Register file** (`r_val[32]`, 0..15 general, 16..31 xmm; masks
`r_free`, `r_lock`, `r_temp`). Allocation takes a free unlocked register,
preferring caller-saved ones (callee-saved for `ST_CS` values, the hint if
it is free); if none is free, it evicts the unlocked register whose value
is cheapest: one that is also in its home (no store), else the one whose
last use is farthest (spilled to its home). An instruction locks the
registers of its operands as it fetches them; scratch registers
(`ra_temp`) are freed at its end; at its end the registers (and frame
slots) of local values whose last use it was are freed (`dying`). A result
may take over the register of an operand that dies (two-address form
without a copy, `ra_reuse`). Fixed registers (`ra_gpr_into`, `ra_clobber`:
dividend and remainder in rax/rdx, shift counts in rcx, `rep movs`
operands, returns) move the register's occupant to a free register, or
spill it.

**Calls.** Values in caller-saved registers that live past the call move to
a free reserved callee-saved register or are written to their home; register
arguments are moved by a parallel copy (cycles broken with `xchg`), the
others loaded straight into their argument register; after the call every
caller-saved register is free and the result is in rax / xmm0. Most calls
(all arguments plain INT/FP values in registers) skip the classifier.

**Legacy lowerings** (`K_B`): `ra_tierb_begin` writes every value that lives
in a caller-saved or xmm register to its home and forgets the register
copies (callee-saved registers survive: the legacy code never touches them);
the lowering then uses A1's interface (`use_gpr(v, RAX)` copies v into rax,
`val_mem`, `res_mem`, `put_gpr`); `ra_tierb_end` takes over its result
register. `K_ALL` (inline asm, `__builtin_setjmp`) also writes back the
callee-saved registers.

**Frame.** Slots are allocated as values need them (homes of global values
and PHIs, spill slots, temp slots, scratch); a local value's slot returns
to a free list at its last use (not in functions that call a
`returns_twice` function). The frame size is only known at the end, which is
why the prologue is generated after the body:

```
rbp+16..        stack arguments (byval copies are used in place)
rbp+8           return address
rbp             saved rbp
rbp-8..-8n      callee-saved registers in use (pushed; n <= the reserved count)
                va register save area (176 bytes, va_start only)
                allocas, then homes / spill slots / PHI temps / scratch as needed
rsp             16-byte aligned; dynamic allocas and call areas below
```

Leaf functions (no calls, no dynamic stack, no inline asm) whose frame
fits in the red zone have no `sub rsp`; frameless functions end with
`pop rbp; ret`, others with `add rsp, n; pop ...; pop rbp; ret` as LLVM's
(`mov rsp, rbp` / `lea rsp, [rbp-8k]` instead of the `add` when the body
moves rsp; never `leave`, §14).

## 5. Deferred loads and addresses

A single-use local load from a frame or rip-relative address (an alloca,
a byval argument, a local global, a GEP of one with a constant offset) is
not emitted at its position (`PEND`): its user reads the memory itself
(`add eax, [rbp-8]`, `cmp dword [rbp-4], 0`, `movslq -0x1c(%rbp), %rax`,
`cvtsi2sd xmm0, [rbp-4]`, loaded straight into an argument register), unless
a memory write lies in between (`ST_NODEF`). A load whose address is in
registers is deferred the same way into the next instruction when that
instruction reads its operands before touching fixed registers; the address
registers stay locked across (`ra_carry`).

A single-use GEP whose user is the next load, store or GEP is folded into
its address (`PADDR`: `[base + idx*scale + disp]`, the alloca offset or the
global symbol folded in), so `a[i] = x` is `mov [rax+rcx*4], edx`, and a
chain of GEPs (`p->a.b[i]`, one GEP per member access at -O0) becomes one
address: the next GEP adds its offset and index to the folded one, or
starts from it with an `lea` when both have an index.

## 6. Instruction selection

| GIR | code |
|---|---|
| add, sub, and, or, xor, mul | `op r, imm` / `op r, [mem]` / `op r, r`; `lea` for add/sub of a live operand, `imul r, r/[mem], imm`; a constant first operand is swapped (`4 * x`), `0 - x` is `neg`, `c - x` builds c in the result register |
| shifts | `shl/shr/sar r, imm` (`lea r, [x+x]` for `<< 1`); variable counts in cl |
| udiv/urem by 2^k | `shr` / `and` |
| sdiv, udiv, srem, urem | dividend in eax/rax, `cdq/cqo` or `xor edx, edx`, `idiv/div r` or `[mem]` at 32 or 64 bits |
| icmp | `cmp`/`test` at the value's width (8, 16, 32, 64: no extension), immediates and memory operands; fused with the next `condbr` (`jcc`) or `select` (`cmov`), else `setcc` + `movzx` (into a dying operand's register) |
| fcmp | `ucomiss/sd` (one or two flag tests per predicate), fused with the next `condbr` or `select` |
| is.fpclass (f32, f64) | nan / not nan: `ucomis x, x` + parity; finite, inf, normal, zero, subnormal: the bits shifted left by one compared unsigned (§14); fused like a compare; other masks legacy |
| select | `cmov` (INT), a short branch around `movaps` (FP, vectors) |
| zext, sext, trunc, ptr casts | nothing (the register is reused), `mov r32, r32`, `movzx`, `movsx`, `movsxd`, or the load itself (`movsbl (%rcx,%rax), %edx`); of a constant: `mov r, imm` |
| int/FP conversions | `cvtsi2sd xmm, r32/r64/[mem]`, `cvttsd2si`, unsigned 64-bit with the 2^63 split |
| fadd..fdiv, fsqrt | `addsd xmm, xmm/[mem]/[rip+const]`; fneg/fabs/copysign with xorps/andps/orps masks in `.rodata.cst16` |
| load, store | typed moves on the folded address; constants stored as immediates (FP constants as their bit pattern); seq_cst stores are `xchg` |
| GEP | an address mode (folded into the next load/store), else one `lea` |
| memcpy, memset <= 64 bytes | memcpy up to 32 bytes (the exporter's inline limit for non-volatile copies): 8/4/2/1-byte moves through a scratch register, as FastISel copies them (§14); larger copies `movups` 16-byte chunks; memset 8-byte stores of the replicated byte; `rep movsb/stosb` above 64 |
| vectors (RC_VX) | `movups/movq`, `addps/addpd`, `paddb/w/d/q`, `psub*`, `pand/por/pxor`, `pmullw`; insertelement/extractelement with a constant lane by `movss`/`shufps`/`unpcklps`/`unpcklpd`/`pinsrw`/`pextrw`/`pshufd`; bitcasts as register moves |
| switch | dense (at least 4 cases filling at least 40% of their range): `movsx` + `sub lo` + `cmp; ja default` + `lea table(%rip)` + `movslq (table,idx,4)` + `add` + `jmp *r`, the table of rel32 offsets placed right after the jump in `.text` (no relocations), edges into blocks with PHIs through stubs after the table; else a chain of `cmp; je` |
| branches | `jmp`/`jcc rel8` to blocks already placed (backward), `rel32` forward; no jump to the next block |
| extractvalue of a register-class field | a load at the field's width from the aggregate's memory; nothing when the call before it defined it (§14) |
| everything else | the A1 lowerings (§7 of the A1 design: INT2 add/adc..., x87, lane-by-lane vectors, aggregates, atomics, TLS, sjlj, inline asm) |

PHIs: every edge writes the PHI's home (or its temp slot) from the incoming
value's register, as an immediate, or through a scratch register taken before
the terminator branches (a move on one path must not evict values, because
the other path would not see the spill).

## 7. Calls and the ABI

`classify(type, abi word)` walks the arguments with LLVM's x86-64 C rules
(`abi.goose` header comment) and is shared by calls (`lower_call`) and the
callee's argument setup (`setup_args`, `prologue_args`):

1. classify all arguments (skipped by the fast path); `sub rsp,
   align16(stack bytes)`;
2. store stack arguments (immediates, registers, memory copies through one
   scratch register) and copy byval pointees first;
3. save live caller-saved values (§4);
4. parallel moves into the argument registers (and r11 for an indirect
   callee), then the arguments that are not in registers;
5. variadic callee: `mov eax, <xmm registers used>`;
6. `call rel32` (PLT32) or `call r11`; `add rsp, n`;
7. the result is taken over in rax / xmm0, or stored to its home from
   rax/rdx/rcx, xmm0..3, st0/st1 for INT2, vectors in memory and aggregates.

At function entry, arguments of the register classes stay in their
argument registers (entry block) or are stored to their home in the prologue
if used in other blocks; INT2, f16 and memory-class vectors passed in
registers are stored to a home. A variadic function with `va_start` saves
`rdi..r9` and, if `al != 0`, `xmm0..7` into its register save area;
`va_start` fills the 24-byte `va_list`.

## 8. Constants

`INT` constants are immediates. Other constants are pooled on first use,
keyed by the constant's index (the exporter deduplicates them):
f32/f16 in `.rodata.cst4`, f64 in `.rodata.cst8`, f80, i128 and 16-byte
vectors in `.rodata.cst16` (all `SHF_MERGE`), vectors and aggregates of other
sizes at the end of `.rodata`. FP zero is `xorps`. The sign and magnitude
masks for fneg/fabs/copysign are four 16-byte entries of `.rodata.cst16`.
Entries of the mergeable pools are referenced through a local symbol each:
linkers resolve a section-symbol relocation into a mergeable section by its
addend, which for a rip-relative operand is `offset - 4` and would name the
wrong piece. Pool symbols are numbered provisionally (`POOL_BASE + k`) and
placed after the local globals when the object is written.

## 9. ELF writer

Sections: `.text` (and custom code sections), `.data`, `.bss`, `.rodata`,
`.rodata.cst4/8/16`, `.tdata`, `.tbss`, then one per GIR section (custom
data sections, `.init_array[.N]`, `.fini_array[.N]`), then `.rela.<name>`
for each section with relocations, `.symtab`, `.strtab` (the GIR string
table verbatim), `.shstrtab` and `.note.GNU-stack`. Functions are generated
grouped by code section, so each code section is a contiguous range of the
module code buffer; data sections are laid out section by section from a
counting sort of the globals.

Comdats: every defined function or variable in a comdat gets a section of
its own (`.text.<name>`, `.data.rel.ro.<name>`, ...; `make_comdat_sections`)
with `SHF_GROUP`, and its comdat an `SHT_GROUP` section (`GRP_COMDAT` for
`any`, 0 for `nodeduplicate`) listing those sections, their `.rela`
sections and the function's `.gcc_except_table` section. Groups come first
in the file (a group must precede its members), so output section `s` is ELF
section `s + n_groups`. The group's signature is the global of the
comdat's name, or a local `STT_NOTYPE` symbol the back-end adds for it. Other
sections: `.eh_frame` (`SHT_X86_64_UNWIND`), `.gcc_except_table` and the
debug sections, whose bytes are built in their own buffers; their
relocations are collected with the code and data relocations.

Symbols: null, one `STT_SECTION` per output section, local globals, pool
entries, comdat signature symbols, then the other globals (`STB_GLOBAL`/`STB_WEAK`, `STT_FUNC`,
`STT_OBJECT`, `STT_TLS`, visibility in `st_other`, `SHN_COMMON` for common
symbols, aliases with their target's section and value).

Relocations: `R_X86_64_PC32` (rip-relative data and code addresses),
`R_X86_64_PLT32` (calls), `R_X86_64_REX_GOTPCRELX` (addresses of
preemptible symbols), `R_X86_64_64` (data), `R_X86_64_TPOFF32` and
`R_X86_64_GOTTPOFF` (TLS in PIE), `R_X86_64_TLSGD` (general-dynamic TLS).
Block-address data relocations are `R_X86_64_64` against the function
symbol plus the block's offset; label differences are resolved in place.

## 10. Unwind information

Every function has one frame shape: `push rbp; mov rbp, rsp`, a push of
each callee-saved register it uses, `sub rsp, n` (not for a leaf whose frame
fits in the red zone), the body, and one epilogue at the end of the
function (returns elsewhere jump to it). The body addresses its frame
through rbp, so from the fourth byte of the function to the epilogue's `pop
rbp` the CFA is rbp + 16 whatever the body does to rsp (dynamic
allocas, outgoing argument areas, red-zone frames). The CFI therefore only
has to describe a handful of events, which `emit_prologue` and
`emit_epilogue` record as they emit the instructions (`CfiEv`: pos, kind,
register):

```
CIE   zR (or zPLR with a personality): code align 1, data align -8, ra = 16,
      DW_CFA_def_cfa rsp+8, DW_CFA_offset rip at cfa-8
FDE   advance 1, def_cfa_offset 16, offset rbp at cfa-16   (push rbp)
      advance 3, def_cfa_register rbp                      (mov rbp, rsp)
      advance, offset r at cfa-24, -32, ...                (each push r)
      [body: advance, GNU_args_size n                      (invoke with stack arguments)]
      advance, restore r ...                               (each pop r)
      advance, def_cfa rsp+8                               (pop rbp)
```

So the rules are exact at every instruction boundary, including between
the pushes and the pops: `tests/gdb_oracle.py --unwind` single-steps every
function and checks the backtrace after each instruction. There is one CIE
per personality routine (and one without); an FDE's start address and LSDA
pointer are `pcrel sdata4` (`R_X86_64_PC32` against the section symbols),
the CIE's personality pointer `indirect pcrel sdata4` to the `DW.ref`
variable the exporter made.

`DW_CFA_GNU_args_size` is emitted at an invoke that passes arguments on the
stack (`sub rsp` before it, `add rsp` after, which the landing pad does
not run): the unwinder adds the size to the stack pointer it installs for
the landing pad, as for LLVM's X86 back-end.

## 11. C++ exceptions

An invoke is a `CALL` with `GIR_IF_INVOKE`; `emit_call_insn` records the call
instruction's code range with the landing-pad block (`f_sites`). A landing
pad block starts with `LANDINGPAD`, whose result is `{rax, edx}` (exception
object, selector) as the personality routine leaves them; the register file
is empty at block entry, so nothing else is assumed live. `resume` is a
call of `_Unwind_Resume` (exporter).

`eh_lsda` writes the function's LSDA into `.gcc_except_table` (or the except
section of the function's comdat group) after the function is placed:

- header: LPStart omitted (the function start), TType `indirect pcrel
  sdata4` with the offset to the end of the 4-aligned type table (found by
  iterating on the uleb128 length), call sites `uleb128`;
- call sites: the invokes in code order, and a site with no landing pad
  for every gap between them, from the function start to its end, so that a
  throwing call outside any invoke unwinds instead of terminating;
- actions: one chain per landing pad (`lp_action`), shared by the invokes
  that reach the same pad: catch clauses are positive type indices, filters
  negative byte offsets into the exception-specification table, a cleanup
  is 0 at the end of the chain;
- type table: the typeinfo stubs in reverse index order (`R_X86_64_PC32`
  to the stub variable, a null entry for catch-all), then the specification
  lists.

## 12. Debug information

DWARF is split between the exporter, which knows the metadata, and the
back-end, which knows the code. The exporter (`gir_dwarf.cpp`) ports LLVM
20's DwarfDebug / DwarfCompileUnit / DwarfUnit for one compile unit at -O0
(DWARF 5, GDB tuning): the DIE tree with LLVM's attributes, forms and child
order, abstract subprograms and inlined subroutines included, in the
`dies`/`dattrs` tables, where what only the back-end knows is a GIR form
(`gir/README.md`). The back-end (`dwarf.goose`) records three things while
it generates code:

- **Line-table rows**, by LLVM's `DwarfDebug::beginInstruction` rules: a
  row with `is_stmt` when the line changes, `prologue_end` at the first
  instruction with a line after the prologue, `epilogue_begin` at the
  epilogue (with the location of the last return, and no `is_stmt` when a
  jump from the return reaches it, as LLVM's epilogue continues the
  return's statement), a line-0 row at the top
  of a block that has no location after one that had, and `is_stmt` forced
  on the first line of a block that a predecessor leaves on another line
  (computed per function from the terminators before the body is
  generated). A row is (code offset, location, flags); offsets are rebased
  when the function is placed. Three rules keep the rows where LLVM's would
  be although goovm's code differs from FastISel's: a GIR instruction that
  emits no code (a folded compare or GEP, a deferred load, a branch to the
  next block) leaves no trace (`dbg_inst_end` undoes its row); a deferred
  load that an instruction materializes into a register gets a row of its
  own when its line differs (`dbg_ld`, from `ra_mat_gpr`/`ra_mat_xmm`), and
  the first such load also takes the code emitted since its IR position
  (in LLVM it precedes that code); a variadic function's prologue_end is
  on its register-save code (LLVM 20's `findPrologueEndLoc` stops at the
  save area's branch). For the same reason `cg.goose` emits the `jmp` of a
  block that is only a branch to the next block, as FastISel does.
- **Runs** of instructions with one location, from which the code ranges of
  lexical blocks and inlined subroutines follow by LLVM's LexicalScopes
  algorithm: a run opens its scope instance and the enclosing ones, a run in
  a scope that the previous one does not enclose closes the ranges up to the
  common ancestor. A scope instance is a scope of the function's own code
  (its `dscopes` index) or a scope in code inlined at a location (hash map on
  (scope, inlined-at); its parent is the call site's instance). A lexical
  block or inlined subroutine with no range is dropped with its variables,
  as LLVM drops scopes without instructions.
- **Frame locations**: `dbg_keep_homes` keeps every value that is a
  variable's address in a frame slot, and `dbg_func_end` turns its home into
  `DW_OP_fbreg off` (an alloca or byval argument) or `DW_OP_fbreg off,
  DW_OP_deref` (a pointer kept in a slot). Labels get their code address.

`dbg_write` then makes the sections in two passes over the DIE table. The
first resolves each DIE's attributes into a body (`b_body`) and an
abbreviation (hashed, codes in first-use order like LLVM's), drops the
DIEs of empty scopes, and computes every DIE's offset; the second places
the bodies, patches `ref4` values and emits the relocations. Strings go to
`.debug_str` with `strx1..4` indices in first-use order; addresses to
`.debug_addr` (`addrx`); the ranges of multi-range scopes and of a unit
with several code ranges to `.debug_rnglists` (`startx_length`), which also
adds `DW_AT_rnglists_base`. The unit's code ranges are LLVM's
(`DwarfCompileUnit::addRange`): runs of functions with debug information
that follow each other in the module in one section; each run is a
line-table sequence (a function of only line-0 rows then does not inherit
its predecessor's last line in gdb). The line program has the sequences
grouped by section, the DWARF 5 directory and file tables (MD5-less,
`line_strp`), and LLVM's special-opcode parameters (line base -5, range 14,
opcode base 13). A
module with locations but no DIE table (goosecc's `-g`) gets a unit with one
subprogram per function, so its line table is usable by a debugger.

Not done (gaps): location lists (variables at -O0 live in memory; LLVM
uses a list for a VLA's `DBG_VALUE`, we a frame slot), call-site entries
(LLVM emits none at -O0), accelerator tables, type units, split DWARF.

## 13. Code quality and speed

See `NOTES.md` §9 for the measurements. In short: on `bench/codequal` the
generated code runs at 0.98x llc -O0's time with 1.05x its `.text` (spass
1.02x, typeset 1.07x); the CTMark C programs run at 0.95x to 1.01x clang
-O0's time (geometric mean 0.99x; A1 2.78x); Vector/build2 at 1.15x clang
-O0 (A1: 11x). The back-end phase is 1.04x to 1.32x A1's time: the pre-pass
and the allocator's bookkeeping cost more than the 3x fewer bytes save.

A3 (`NOTES.md` §10): without `-g` the back-end takes 1.04x to 1.10x A2's
time (gen-20000, spass, typeset; goovm-llc in total 1.02x to 1.07x), of which
`.eh_frame` is 2% to 4%. With `-g` the back-end takes about 2x its time on C
and 4x on template-heavy C++, the exporter 4x to 6x; goovm with `-g` is
still 8.5x faster than LLVM's -O0 code generator with `-g` on sqlite3 and
tramp3d-v4.

## 14. Floating point and small aggregates

FP scalars (f32, f64) and vectors of 8 or 16 bytes live in xmm registers
like integers in general registers (§3, §4): there are no callee-saved xmm
registers in the SysV ABI, so values that live across a call are written to
their home before it, as with LLVM -O0. Arithmetic takes its second operand
from memory or the constant pool (`addsd xmm, [rbp-8]`, `mulss xmm,
[rip+c]`), FP zero is `xorps`, fneg/fabs/copysign are `xorps`/`andps`/`orps`
with masks in `.rodata.cst16`, conversions read a deferred load in place
(`cvtsi2sd xmm, [mem]`, `cvtss2sd xmm, [mem]`), and an `fcmp` sets the flags
for the branch or select after it (`fcmp_plan`: the predicate's operand
order and one or two condition codes, `oeq` = `e && np`, `une` = `ne || p`;
the ordered "less" predicates swap the operands so that unordered results
take the false edge without a parity test).

**Store-to-load forwarding.** A load that reads data written by narrower
stores (an 8-byte load of two 4-byte stores, a 16-byte load of four) cannot
take the data from the store buffer and waits about 15 cycles until the
stores have reached the cache. Small FP aggregates at -O0 produce such
sequences everywhere, so the back-end keeps to one rule: memory that a
lowering writes with stores of width w is read back by loads no wider than
w. Four places follow from it:

- **Aggregate call results** (`{<2 x float>, <2 x float>}` for a C++ class of
  four floats such as Bullet's `btVector3`, `{double, double}`, `{<2 x float>,
  float}`, `{ptr, i32}`, ...). The pre-pass counts each value's uses by
  extractvalues of its block (`nev`); when all uses of an aggregate call
  result are such extractvalues and each reads exactly one return-register
  part (`ret_parts_fuse`: offset, size and register class of the part from
  `classify_ret`; no x87 part, no part read twice), the call defines the
  extractvalues' values in the return registers (`ra_set` on xmm0/xmm1,
  rax/rdx) and their instructions emit nothing (kind `K_DONE`). A value that
  lives past a later call is saved like any other. Otherwise the parts are
  stored to the aggregate's home at their width (`ret_result`).
- **extractvalue** of a field of a register class is allocator-aware: a load
  of the field at its width from the aggregate's memory (its home, the
  memory of a deferred aggregate load, or a constant's pool entry). (The
  legacy lowering copied the field lane by lane into the field's home, and
  the 8-byte load of that home missed forwarding twice per `btVector3`
  returned.)
- **Aggregate loads** with a single use by a `ret` or an extractvalue,
  from a frame or rip-relative address with no memory write in between, are
  deferred like register loads (§5): `load {<2 x float>, <2 x float>}, ptr
  %retval; ret` is two `movq` into xmm0 and xmm1, as in clang's code.

- **Small memcpys** (at most 32 bytes, which the exporter inlines as LLVM's
  FastISel does) are copied 8, 4, 2 and 1 bytes at a time through a general
  register, like FastISel's `TryEmitSmallMemcpy`: a 16-byte `movups` load
  of a temporary that a call result was just stored to in two 8-byte halves
  (Bullet's `btVector3` copy assignment) missed forwarding.

Legacy lowerings that write a vector result lane by lane into its home still
leave the next full-width load of that home to miss forwarding (shuffles,
vector compares, conversions of vectors); vector homes written by the
allocator-aware code are written and read at full width.

**is.fpclass.** clang emits `llvm.is.fpclass` for `isnan` (mask 3),
`isfinite` (0x1F8), `isnormal` (0x108) and the zero/subnormal tests. For f32
and f64 these masks are lowered without computing the class: nan and not-nan
are `ucomis x, x` and the parity flag; the others take the bits (from memory
or by `movq`/`movd`), shift them left by one (dropping the sign) and compare
unsigned: finite `b < inf`, infinite `b == inf`, normal `b - minnorm < inf -
minnorm`, zero `b == 0`, subnormal `b - 1 < minnorm - 1` (inf and minnorm
shifted likewise). Other masks and f80 keep the legacy lowering.

**False dependencies.** `cvtsi2sd/ss`, `cvtss2sd`, `cvtsd2ss` and
`sqrtsd/ss` write only the low lanes of their destination and so wait for
its previous value. The destination is zeroed first (`xorps x, x`, a
dependency-breaking idiom) unless it is the operand itself; otherwise a
conversion into a register that last held a loop-carried sum serializes
the iterations (spectral-norm: `cvtsi2sd %eax, %xmm0` in a function called
from an `addsd` loop over xmm0). LLVM breaks these dependencies only at -O1
and above (BreakFalseDeps); its -O0 code avoids them or not by its register
choice.

**Load order.** A load deferred to a later user (§5) executes after the
loads in between. For the base pointer of a GEP that is not the next
instruction this reorders `a[i]` into "index, then pointer", which runs
about 20% slower in linpack's daxpy loop than the program order (the loops
are otherwise identical; measured in isolation at equal alignment) and
saves nothing, because a GEP's base is a register: such loads are emitted at
their position (`late_gep_base`).

**Epilogue.** Functions with a frame end as LLVM's do, `add rsp, n; pop
...; pop rbp; ret`, with `mov rsp, rbp` / `lea rsp, [rbp-8k]` only when the
body moves rsp. On the Sapphire Rapids host of the measurements `leave`
makes each return about 5 cycles slower in a chain of small calls (four
nested calls of a 16-byte frame: 0.93 s per 10^8 chains with `leave`, 0.48 s
with any of the other forms), and in deep recursion the `mov`/`lea` forms
are as slow as `leave` (fibo 1.14x clang -O0 with them, 0.94x with `add`).
The frame size is known when the epilogue is emitted (after the body);
`emit_prologue` asserts that it has not changed.

## 15. The middle-end (opt_level >= 1)

`opt_module` (`opt.goose`) runs at the start of `gir_codegen` when the
header's `opt_level` is at least 1. It reads the input tables (M), writes
new tables (`x_insts`, `x_blocks`, `x_funcs`, `x_opnds`, `x_consts`,
`x_asms`, `x_dies`, `x_dattrs`) and points M's fields at them; the rest of
the back-end does not know that the middle-end ran. Globals, types,
strings, data and relocations are not touched. The output arrays only
grow (M holds views of them, and Goose refuses to shrink an array a global
may view): a second module in the same process appends a new region
(`xb_*`), which costs nothing for the tools (one module per process).

**Function order.** Functions are optimized callees first: a post-order
of the direct call graph from every function (`opt_order`; calls inside a
cycle in any order). The inliner then copies a callee that is already
optimized out of the output tables, and its size there is the cost model's
input.

**Working form (OIR).** One function at a time is loaded into flat arrays:
the instruction records (`o_ins`, GIR's 24-byte `Inst` with the INST
operands renumbered to local ids), the operand runs (`o_ops`), a doubly
linked instruction list per block (`o_nxt`/`o_prv`, `b_first`/`b_last`) and
the layout order of the blocks (`b_lnext`). Deleting unlinks; replacing a
value records a forward (`o_fwd`), which readers follow (`res`) until
`resolve_all` rewrites all operands (a dirty flag skips the walk when
nothing was replaced). There are no persistent use lists and no hash maps
of instructions: passes that need uses build CSR arrays (`build_uses`),
and the CFG analyses (successors and predecessors as CSR arrays, RPO,
dominators by Cooper, Harvey and Kennedy, a pre-order numbered dominator
tree for O(1) dominance queries, dominance frontiers, natural loops) are
recomputed on demand after a pass that changed the CFG (`ensure_cfg`).
Integer constants are canonical (a hash of (type, value) over the
constant table), so value equality is reference equality. `oir_store`
writes the function back in layout order, renumbering blocks and
instructions; `in2out` maps each input instruction to its output index
for the debug information.

**Pipeline** (`opt_function`):

```
load
sroa, mem2reg, simplify_phis       (after removing unreachable blocks)
round                              = simplify; simplify_phis; gvn; dce; simplify_cfg
tail_recursion -> round
inline_calls -> round; sroa; mem2reg; round      (if anything was inlined)
rotate_loops -> mem2reg
round
licm -> indvars -> licm; round                   (if anything was hoisted)
promote_globals -> mem2reg; round
rotate_layout
verify (GOOVM_OPT=verify); record the size for the inliner; store
```

- **mem2reg** (`opt_ssa.goose`): allocas of the entry block whose address
  is only loaded and stored with one scalar type become SSA values; PHIs go
  to the iterated dominance frontier of the stores, pruned by liveness
  (only blocks the variable is live into, as in LLVM's PromoteMemToReg);
  renaming walks the dominator tree with an explicit stack and an undo log.
  No PHIs in landing pads (variables live there stay in memory).
- **SROA** (`opt_sroa.goose`): an entry-block alloca accessed only at
  constant offsets (typed loads and stores, constant GEPs, memcpy/memmove/
  memset of constant size, as calls by name or as the inline intrinsics) is
  split into one alloca per slice; overlapping accesses must agree on offset
  and type; copies are split into a load and a store per slice (bytes no
  typed access names get integer slices), memsets into stores. mem2reg then
  promotes the slices: structs passed around by value at -O0 become
  registers.
- **simplify** (`opt_fold.goose`, an instcombine-lite): constant folding
  of the integer operations (srem with C's truncating remainder; Goose's
  `%` is Euclidean), identities (`x+0`, `x*1`, `x&-1`, `x^x`, ...),
  reassociation of constants (`(x+c1)+c2`), `sub x, c` to `add`,
  multiplication and unsigned division and remainder by powers of two to
  shifts and masks, signed division by a power of two with the rounding
  fix-up, i32 division and remainder by other constants with magic numbers
  (Granlund-Montgomery for unsigned, Hacker's Delight figure 10-1 for
  signed; unsigned `x / d` with `d >= 2^31` is a compare), compares
  (constants to the right, unsigned extremes, `(zext i1 x) ==/!= c`,
  `(zext x)` or `(sext x)` against a constant in x's range), selects on
  constants or with equal arms, cast chains, GEPs (constant terms folded
  into the offset, a GEP of a GEP merged when at most two terms result,
  scales other than 1/2/4/8 to an explicit multiply or shift), and
  `pow(x, 2.0)` to `x * x` (what libstdc++'s `std::pow(double, int)` leaves).
- **gvn** (`opt_gvn.goose`): EarlyCSE-style dominator CSE. The dominator
  tree is walked in pre-order with a scoped hash table of pure instructions
  (the key is the record plus its operand run). Loads are keyed by (address,
  type) and forwarded from an earlier load or store while the memory
  generation that guards them has not moved: stores and calls move the
  generation, a block with several predecessors starts a new one, and
  allocas whose address does not escape have generations of their own that
  only stores into them move (calls leave them alone); such an alloca whose
  writes are all in one block that dominates the load keeps its entries
  across merge points (no write can come between: a path from the writing
  block back to the load passes the entry's block again). Within a block a
  store overwritten by a later store to the same address with no possible
  read in between is deleted (local DSE). Functions that call setjmp or use
  sjlj exceptions get no alias information.
- **simplify_cfg** (`opt_scfg.goose`): branches on constants and to one
  target become plain branches; unreachable blocks go; a block is merged
  into its only predecessor when that one only branches to it; a block that
  only branches on is bypassed (its predecessors go straight to its target
  when the PHIs allow); a branch on a PHI with constant incoming values
  (what `while (a && b)` leaves at -O0) is threaded: each such predecessor
  jumps to the known target; small triangles and diamonds (at most four
  cheap speculatable instructions, at most two PHIs to merge, integer or
  pointer PHIs) become selects, which are cmovs, with the hoisted code placed
  before the compare so that the compare sets the flags for the select.
  Functions whose blocks are named by `blockaddress` only get the branch
  folding (block numbers are fixed).
- **tail_recursion** (`opt_inline.goose`): a self-call right before a
  return (`return f(...)`, or `return x + f(...)`: an accumulator) becomes a
  branch back to a new header whose PHIs are the arguments (and the
  accumulator, which every other return then adds); a return of a PHI is
  first copied into the predecessors that compute such a call. Not in
  functions with allocas (the frame is reused), byval or variadic
  arguments.
- **inline_calls** (`opt_inline.goose`): the cost model is the optimized
  callee's instruction count: up to 40 always, up to 80 when the call is in
  a loop, up to 500 for an internal function's only call site, any size for
  `always_inline`; a caller grows by at most 4000 instructions. Never:
  `noinline` (exported only when it does not come with `optnone`, so a user
  `noinline` is seen by `goovm-cc -O1` but not in clang -O0 IR, where every
  function is `noinline optnone`), variadic functions, dynamic allocas,
  stacksave, va_start, setjmp, sjlj, frame or return addresses, landing
  pads and invokes, block addresses, byval parameters, self-recursion; a
  call that is an invoke is not inlined. The callee's blocks are copied
  between the halves of the split call block, arguments are substituted
  (truncated for `signext`/`zeroext` parameters, whose upper bits the callee
  may assume), returns become branches to the continuation with a PHI for
  the value, allocas move to the caller's entry block, and the copied
  instructions take the call's line. Internal functions all of whose calls
  were inlined and whose address is not taken are not emitted (`FN_DEAD`;
  kept with `-g`, whose subprograms name them).
- **licm** (`opt_licm.goose`): each natural loop gets a preheader; pure
  instructions whose operands are defined outside the loop move to it,
  inner loops first. Division only by a constant that cannot trap; loads
  only from a loop that writes no memory, and only when the load is in the
  header or its address is an alloca or a global. A GEP whose index is
  `invariant + variant` is split so that the invariant part is hoisted.
- **indvars** (`opt_iv.goose`): clang computes array indices in i32 and
  sign-extends them for every access. Signed overflow being undefined
  (`nsw`, exported as `GIR_IF_NSW`), `sext (add nsw a, b)` becomes `add
  (sext a), (sext b)` (and sub, mul, shl by constants), and an i32 counter
  `i = phi [init, i + c]` whose extensions are used gets an i64 twin that
  replaces the extensions and the loop's own compares of `i`. With the GEP
  split, `a[i * n + j]` costs one add per iteration.
- **rotate_loops** (`opt_licm.goose`, LLVM's LoopRotate for small headers):
  a loop whose header holds only PHIs, at most four cheap instructions and
  the exit test, with one latch ending in a branch to it, gets a copy of the
  test on the entry edge (a preheader is made first if several edges enter);
  the header is then entered only from the latch and merged into it, so the
  loop is a guarded do-while with no jump on entry (a loop that runs once or
  twice paid one per entry). The header's values used outside it are
  repaired by demotion to an alloca stored in both copies, which mem2reg
  promotes again with the PHIs the new CFG needs. Inner loops first.
- **promote_globals** (`opt_licm.goose`, LICM's scalar promotion where
  LLVM needs GlobalsAA): an internal global whose address is never taken in
  the module (only direct loads and stores; no data relocation, no other
  operand) cannot be reached through a pointer, so in a loop without calls
  and inline asm it is demoted to an alloca: loaded in the preheader,
  stored back on a new block on every exit edge, and promoted by mem2reg.
  Stores are added on the exits only when a store of the loop dominates
  every exiting block (no store on a path that had none: the global may
  belong to another thread then).
- **rotate_layout**: a loop whose header tests and whose single latch
  branches back is laid out with the header after the latch, so an
  iteration takes one taken branch (the preheader jumps to the test once).
- **dce**: mark and sweep from the instructions with effects.

**Cost.** Every pass is linear in the function or close to it (the
dominator walk, the scoped hash table, CSR use lists); the CFG analyses
are rebuilt only when stale; nothing allocates per instruction (all
arrays are cleared and reused across functions). `NOTES.md` §12 has the
measured time per instruction.

**Switches.** `GOOVM_OPT` holds a list of `-pass` names that switch passes
off for bisecting (`-m2r`, `-sroa`, `-fold`, `-gvn`, `-cfg`, `-inline`,
`-licm`, `-iv`, `-rotate`, `-lrot`, `-tre`, `-select`, `-gprom`, `-ra` for the
global allocator, `-all`), plus
`verify` (check the invariants after each function: every operand
dominates its use, PHI entries match the predecessors, one terminator per
block, allocas in the entry block) and `dump` (print the optimized tables).

**Debug information at -O1** degrades and stays valid
(`llvm-dwarfdump --verify` passes): line rows follow the instructions that
survive; inlined code carries the call's line (no inlined-subroutine DIEs);
a variable whose alloca was promoted or deleted loses its location (a
debugger shows it as optimized out; there are no location lists); a
variable whose address survives keeps its frame location, and the value
holding that address stays in its home (`ST_KEEP`). The CFI stays exact:
the prologue and epilogue are generated as at -O0, with more callee-saved
registers.

**LLVM -O2 IR.** `goovm-llc -O1` on IR from `clang -O2` works as far as the
exporter supports what LLVM's optimizers produce; the missing pieces are
listed in `NOTES.md` §12 (mostly vectorizer output: `llvm.vector.reduce.*`,
vectors of pointers, vector GEPs, bitcasts between vectors and integers;
also saturating-arithmetic intrinsics and relative lookup tables).

## 16. Global register allocation

At `opt_level >= 1`, `rg_alloc` (`rag.goose`) runs after the pre-pass. It
gives the values that live across blocks (`ST_GLOB`: values used in another
block, arguments used outside the entry block) and all PHIs one register
for their whole live range, or none; the block-local allocator of §4 then
works around them. There is no splitting and no spilling of a pinned value:
a value that gets no register keeps -O0's write-through home.

- **Liveness**: live-in and live-out bitsets of the global values per block
  (backward dataflow iterated to a fixed point), then the live segments of
  each value in the linear order: instruction j is at position 2j + 2, a
  block spans [2 first + 1, 2 last + 3); a definition starts at its
  position and a use ends one after it, so an instruction's operands
  interfere with its result (a lowering may still give a dying pinned
  operand's register to a local result, `ra_reuse`).
- **Clobbers**: calls and legacy lowerings clobber the caller-saved
  registers (all xmm) at 2j + 3, after the operands are read and before the
  result is written; inline asm and setjmp clobber every register; `rep
  movs`/`stos` (large memcpy/memset) rdi and rsi. A value live across such
  a point cannot take those registers; its own definition is exempt (a call
  result may live in a caller-saved register). There are no callee-saved
  xmm registers, so an FP value live across a call stays in memory.
- **Assignment**: values in order of weight (each use weighted 8^depth; the
  loop depth is estimated from the layout: a backward branch from block l to
  block h marks h..l), each to the first register of its class that is free
  over all its segments (per-register occupancy bitmaps over the
  positions). A value's PHI partner's register (the PHI it feeds or an
  incoming value of it) and an argument's own register come first; values
  that cross a call take callee-saved registers, the others prefer the
  caller-saved ones; the registers the arguments arrive in are taken last.
  GPRs: rbx, r12-r15 (callee-saved) and rsi, rdi, r8, r9, r10; xmm4-xmm15.
  rax, rcx, rdx, r11 and xmm0-3 are never pinned: they are the fixed
  registers of division, shifts, returns and calls, and the lowerings'
  scratch. Functions whose bitsets would exceed 2^26 bits get no global
  allocation.
- **PHIs**: the incoming values are moved to the PHIs' registers with one
  parallel copy per edge (`phi_moves_rg`, `emit_moves`, cycles broken with
  `xchg`); PHIs in memory are written first, constants and deferred loads
  are materialized last. An edge whose incoming values already sit in the
  PHIs' registers emits nothing, and a conditional branch with such an edge
  takes the plain form (`edge_phi`).
- **In the code generator** (guarded by `rg_on`, false at -O0): a pinned
  value is in its register from its definition (`rg_def_start`; when a
  legacy lowering wrote it to its home, it is loaded, `rg_def_end`) or from
  the start of every block it is live into (`rg_block_enter`), and frees the
  register after its last use in each block (kill lists, `rg_kills`).
  `ra_evict` never evicts it, `ra_def` returns its register, no home is
  written for it, and a load deferred into the next instruction refuses a
  pinned destination its address needs. When a lowering needs more scratch
  registers than the pinned values leave, a pinned value the current
  instruction does not use lends its register for that one instruction
  (`rg_borrow`: stored to a slot, reloaded at the end, `rg_restore`). The
  function saves the callee-saved registers of pinned values plus as many
  as the local allocator wants, at most 5 in all, and the entry block moves
  pinned arguments to their registers with a parallel copy
  (`rg_entry_moves`).
- **Read-modify-write**: at -O1 `store (op (load p), x), p`, with the load
  deferred into the operation and the operation used only by the store, is
  one `op [p], x`.

## 17. AArch64 (milestone F1)

`GirHeader.target == GIR_TARGET_AARCH64` (`gir/README.md`, F1 additions)
switches `codegen()` to `a_gen_functions` (`a64cg.goose`); everything after
the per-function code generation - sections, symbols, relocations, the
ELF writer, `.eh_frame` and the LSDAs, DWARF - is shared, with the target
decided at a few dispatch points (`tgt_a64` in `elf.goose`: `e_machine`,
relocation numbers through `r_abs64`/`r_pc32`/`r_dtpoff64`, mapping
symbols; `eh.goose`: the CIE and the CFI events; `dwarf.goose`: the frame
base register and no location for TLS variables).

**Registers.** x0..x30 are 0..30, sp/xzr 31, v0..v31 32..63 (`u64` masks).
x16/x17 are the encoder's scratch registers (large offsets, far branches,
PLT-like veneers are not needed: calls are `bl` with `R_AARCH64_CALL26`,
which lld extends with thunks), x18 is never used (platform register), v31
is the FP scratch, x29 is always the frame pointer.

**Frame.** `stp x29, x30, [sp, #-F]!` (or `sub sp` + `stp` above 504
bytes), `mov x29, sp`; the callee-saved registers the function uses are
stored at x29+16 upwards (x19..x28, and only the low 64 bits of v8..v15, as
AAPCS64 says), then the `va_start` save areas, the allocas (small ones
first, so that more of them are in reach of the unsigned-offset forms),
then the homes of values, all at positive offsets from x29. Incoming stack
arguments are at x29 + F. The prologue is generated after the body (its
size depends on what the body used) and placed before it. CFI: the CIE has
code alignment 1, data alignment -8, return address column 30 and
`def_cfa sp+0`; the FDE records `def_cfa_offset F`, `def_cfa x29` and the
saves as events of the prologue and epilogue, so the CFA is exact at every
instruction (checked by `tests/gdb_oracle.py --unwind --target aarch64`).

**Two tiers.** As on x86-64 (§6), the frequent instructions have
allocator-aware lowerings (`a64low.goose`, kind `K_A`): values in
registers, compares fused with `b.cond`/`csel`/`cset`, immediates (12-bit
arithmetic, logical bitmasks, `movz`/`movk` sequences), address modes (base
+ scaled register, base + offset, folded GEPs). The rest (`a64mem.goose`,
`a64atom.goose`, `a64neon.goose`, kind `K_B`; calls `K_CALL`) works on
fixed scratch registers after the caller-saved registers are flushed:
i128 in x0:x1 pairs, fp128 through the soft-float routines, vectors of
any shape lane by lane in memory, aggregates, atomics. The block-local
allocator (`a64ra.goose`) is §4's design with AArch64's register file.

**AAPCS64** (`a64abi.goose`). The GIR types are classified as LLVM's
`CC_AArch64_AAPCS` does on the IR clang produces: integers and pointers in
x0..x7, FP and short vectors in v0..v7, an array of one FP or vector type
(clang's HFA/HVA lowering) or such a structure in consecutive V registers
all or nothing, `i128` in an even/odd pair or 16-aligned on the stack,
illegal vectors split, widened or promoted like LLVM's type legalization,
everything else on the stack in 8-byte slots (16 for 16-aligned values);
`sret` in x8; variadic calls pass the variadic arguments like fixed ones
(Linux), and a variadic function saves the unnamed x and q argument registers
in its frame for `va_start`. Moves
into argument registers are a parallel copy (cycles through x16/v31).

**Atomics.** As clang's default on Linux (`-moutline-atomics`), atomic
read-modify-write operations and compare-and-swap of 1 to 16 bytes call
`__aarch64_{swp,ldadd,ldclr,ldset,ldeor,cas}{1,2,4,8,16}_{relax,acq,rel,acq_rel}`
from libgcc (they use LSE when the CPU has it); the operations without a
helper (nand, min/max, FP) are `ldaxr`/`stlxr` loops; loads and stores with
ordering are `ldar`/`stlr`, fences `dmb ish`/`ishld`.

**TLS.** The model the IR gives (clang: local-exec for the executable's
own variables, initial-exec for external ones in a PIE, general dynamic
under -fPIC): local-exec as `tprel` `add`s on `tpidr_el0`, initial-exec
through the GOT, general dynamic as TLSDESC (`adrp`/`ldr`/`add`/`blr` with
the four `TLSDESC` relocations).

**Global register allocation** (`a64rag.goose`) reuses `rag.goose`'s
liveness, live segments and occupancy bitmaps. Candidates: x19..x28 and
v8..v15 (values of at most 8 bytes) across calls and memory-tier
lowerings, x2..x15, v2..v7 and v16..v30 otherwise; x0/x1, v0/v1, x16/x17
and v31 are never pinned (the lowerings' fixed registers). A memory-tier
lowering flushes the caller-saved registers first; a pinned value's home
is never current (PHI moves change only its register), so a flush always
stores it.

**NEON and ACLE** (`a64neon.goose`): one lowering per `GIR_A64` group
(three-same, two-misc, across-lanes, three-different, shifts by immediate,
by element, table lookups, crypto, dot product) choosing the vector or the
scalar (SISD) encoding from the type, with the operands in v0..v2 and the
table of `tbl`/`tbx` in v16..v19.

**Inline assembly**: the exporter binds the operands and assembles the
AArch64 text with LLVM's MC layer (as for x86-64, §6 of `NOTES.md` A3);
the back-end moves values in and out of the bound registers.

**Branches.** Conditional branches reach ±1 MB, `tbz`/`cbz` ±32 KB: a
function whose size bound (`a_size_bound`) exceeds the short range gets
the far forms (an inverted short branch over a `b`). At -O0 an
unconditional branch to the next block is still emitted, as FastISel does,
so that the branch's line (a loop body's closing brace) has an address.

**What is not done** (`NOTES.md` F1): SVE/SME; inline asm constraints of
SVE registers; `__attribute__((target_clones))`/function multi-versioning
(ifunc resolvers); goosecc's `arm_neon.h` (its `__builtin_neon_*` calls are
not lowered) and goosecc's AArch64 inline assembly (goosecc has no AArch64
assembler).
