# The Goose back-end (v2): design

`backend-goose/` turns GIR version 2 tables ([`../gir/README.md`](../gir/README.md))
into an ELF64 x86-64 relocatable object. It compiles everything clang-20
emits at -O0 for C on x86-64 Linux (SysV ABI, PIE), with and without `-g`,
and the same IR after `opt -passes=mem2reg`. It is written in Goose and
called from `goovm-llc` (C++) through one `export fn`.

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
| `elf.goose` | output sections, symbols, data layout, relocations and the ELF writer |
| `CMakeLists.txt` | runs `goose --standalone --header cg.h -o cg.c cg.goose` and builds the C |

`goose` compiles the whole program from `cg.goose` (an `import` includes a
file once) into one C file. The encoder and byte-output layer is
`checkfree`: the compiler proves that no bounds check is left in it.

## 2. Passes

```
gir_codegen(tables):
  reset module state; register classes of all types (t_rc)
  make_sections(); layout_globals()
  gen_functions(): per code section, per function: gen_function(fi)
  resolve_blockaddrs(); resolve_aliases(); write_elf()

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
```

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
- `hint`: the register a return value or a plain call argument is wanted in;
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
`pop rbp; ret`, others with `leave; ret` or `lea rsp, [rbp-8n]; pop ...;
pop rbp; ret`.

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

A single-use GEP whose user is the next load or store is folded into its
address (`PADDR`: `[base + idx*scale + disp]`, the alloca offset or the
global symbol folded in), so `a[i] = x` is `mov [rax+rcx*4], edx`.

## 6. Instruction selection

| GIR | code |
|---|---|
| add, sub, and, or, xor, mul | `op r, imm` / `op r, [mem]` / `op r, r`; `lea` for add/sub of a live operand, `imul r, r, imm` |
| shifts | `shl/shr/sar r, imm` (`lea r, [x+x]` for `<< 1`); variable counts in cl |
| udiv/urem by 2^k | `shr` / `and` |
| sdiv, udiv, srem, urem | dividend in eax/rax, `cdq/cqo` or `xor edx, edx`, `idiv/div r` or `[mem]` at 32 or 64 bits |
| icmp | `cmp`/`test` at the value's width (8, 16, 32, 64: no extension), immediates and memory operands; fused with the next `condbr` (`jcc`) or `select` (`cmov`), else `setcc` + `movzx` |
| fcmp | `ucomiss/sd` (one or two flag tests per predicate), fused with the next `condbr` or `select` |
| select | `cmov` (INT), a short branch around `movaps` (FP, vectors) |
| zext, sext, trunc, ptr casts | nothing (the register is reused), `mov r32, r32`, `movzx`, `movsx`, `movsxd`, or the load itself (`movsbl (%rcx,%rax), %edx`) |
| int/FP conversions | `cvtsi2sd xmm, r32/r64/[mem]`, `cvttsd2si`, unsigned 64-bit with the 2^63 split |
| fadd..fdiv, fsqrt | `addsd xmm, xmm/[mem]/[rip+const]`; fneg/fabs/copysign with xorps/andps/orps masks in `.rodata.cst16` |
| load, store | typed moves on the folded address; constants stored as immediates (FP constants as their bit pattern); seq_cst stores are `xchg` |
| GEP | an address mode (folded into the next load/store), else one `lea` |
| memcpy, memset <= 64 bytes | `movups` 16-byte chunks and a scratch register; `rep movsb/stosb` above |
| vectors (RC_VX) | `movups/movq`, `addps/addpd`, `paddb/w/d/q`, `psub*`, `pand/por/pxor`, `pmullw`; insertelement/extractelement with a constant lane by `movss`/`shufps`/`unpcklps`/`unpcklpd`/`pinsrw`/`pextrw`/`pshufd`; bitcasts as register moves |
| branches | `jmp`/`jcc rel8` to blocks already placed (backward), `rel32` forward; no jump to the next block |
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

## 10. Code quality and speed

See `NOTES.md` §9 for the measurements. In short: on `bench/codequal` the
generated code runs at 0.99x llc -O0's time with 1.09x its `.text`; the
CTMark C programs run at 0.80x to 1.15x clang -O0's time (geometric mean
1.00); Vector/build2 at 1.28x clang -O0 (A1: 11x). The back-end phase is
1.16x A1's time on gen-20000 and 1.30x on spass: the pre-pass and the
allocator's bookkeeping cost more than the 3-4x fewer bytes save.
