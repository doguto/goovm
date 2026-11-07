# The Goose back-end (v2): design

`backend-goose/` turns GIR version 2 tables ([`../gir/README.md`](../gir/README.md))
into an ELF64 x86-64 relocatable object. It compiles everything clang-20
emits at -O0 for C and C++17 on x86-64 Linux (SysV ABI, PIE), with and
without `-g`, and the same IR after `opt -passes=mem2reg`. It is written in
Goose and called from `goovm-llc` and `goovm-cc` (C++) and from `goosecc`
(Goose) through two `export fn`s (`gir_codegen`, `gir_codegen_ex`).

Milestone C1 brought floating-point-heavy C++ to the speed of clang -O0's
code (Bullet 1.71x -> 0.97x, tramp3d-v4 1.18x -> 1.01x): small aggregates
returned in registers no longer go through memory in ways that miss
store-to-load forwarding, `is.fpclass` has fast paths, and the epilogue
avoids `leave` (§14).

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
  gen_functions(): per code section, per function: gen_function(fi)
  resolve_blockaddrs(); resolve_aliases(); dbg_write(); write_elf()

gen_function(f):
  ra_prepass()       uses, last use, local/global, call-spanning values,
                     memory writes between a load and its use, register
                     hints, the lowering kind of every instruction
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
`pop rbp; ret`, others with `mov rsp, rbp; pop rbp; ret` or `lea rsp,
[rbp-8n]; pop ...; pop rbp; ret` (never `leave`, §14).

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

**Epilogue.** Functions with a frame end with `mov rsp, rbp; pop rbp; ret`,
not `leave; ret`: on the Sapphire Rapids host of the measurements, `leave`
makes each return about 5 cycles slower in a chain of small calls (four
nested calls of a 16-byte frame: 0.93 s per 10^8 chains with `leave`, 0.48 s
with `mov rsp, rbp; pop rbp`, `add rsp, n; pop rbp` or `lea rsp, [rbp-8];
pop rbx; pop rbp`). LLVM never emits `leave` on x86-64.
