# goovm reference back-end: design and porting guide

`gir_codegen_cpp.cpp` turns GIR tables (see [`../gir/README.md`](../gir/README.md))
into an ELF64 x86-64 relocatable object. It is about 900 lines of C++. It is
written so that it can be ported line by line to Goose
(`backend-goose/cg.goose`).

The output is deterministic. A correct port produces **byte-identical** objects,
so you can check it with `cmp`:

```
goovm-llc --backend=cpp   x.bc -o a.o
goovm-llc --backend=goose x.bc -o b.o
cmp a.o b.o
```

## 1. Algorithm in one paragraph

Each function is compiled in one pass at -O0 quality, with no register
allocation. Every instruction result gets an 8-byte frame slot below `rbp`.
Each static alloca gets its own frame area. An instruction loads its operands
into fixed scratch registers (`rax`, `rcx`, `rdx`), computes, and stores the
result in its slot. Constants become immediates. Globals are addressed
RIP-relative. Branches are rel32 jumps, patched when the function is done.
PHIs use two slots each, a temp slot and the result slot. Each predecessor
edge writes the temp slots, and the start of the PHI's block copies them into
the result slots, which gives parallel-copy semantics. After all functions,
the ELF writer puts code, data, relocations and the symbol table in one byte
buffer.

## 2. Data structures

All state is held in file-scope variables. Each growable array is its own
variable, because a Goose struct can hold only one variable-length member.
In Goose these become global `var x: T[>..] = [];` arrays. Scalars become
global `var`s.

| variable | type | lifetime | meaning |
|---|---|---|---|
| `M` | `const GirModule *` | call | the input tables. In Goose, pass the nine slices down as parameters, or keep them in a struct of slices if allowed |
| `code` | `u8[>..]` | module | `.text` bytes |
| `rela_text` | `Rela[>..]` | module | `.rela.text` entries `{offset u64, info u64, addend i64}` (= `Elf64_Rela`) |
| `sdata`, `srodata` | `u8[>..]` | module | `.data`, `.rodata` bytes |
| `bss_size`, `data_align`, `rodata_align`, `bss_align` | `u64` | module | section sizes and alignments |
| `g_sym` | `u32[>..]` | module, per global | ELF symbol index |
| `g_sec` | `u32[>..]` | module, per global | ELF section index (0 = undefined) |
| `g_value`, `g_size` | `u64[>..]` | module, per global | `st_value` (offset in section), `st_size` |
| `g_has_reloc` | `u8[>..]` | module, per global | the variable has data relocations |
| `n_local_syms` | `u32` | module | index of the first non-local symbol (= `.symtab` `sh_info`) |
| `f_first_inst`, `f_first_block`, `f_arg_tys` | `u32` | function | from the current `GirFunc` |
| `v_off` | `i32[>..]` | function, per local inst | rbp offset of the result slot, or of the alloca area |
| `t_off` | `i32[>..]` | function, per local inst | rbp offset of a PHI's temp slot |
| `a_off` | `i32[>..]` | function, per argument | rbp offset of the argument's slot |
| `block_off` | `u32[>..]` | function, per local block | code offset of the block |
| `fixups` | `Fixup[>..]` | function | `{pos u32, block u32}`: patch rel32 at `code[pos]` to the block |

The per-function arrays are only resized, never shrunk, and are indexed by
`local = global_index - f_first_inst` (or the block or argument number). The
code uses no maps, no recursion, no function pointers, no virtual calls and
no exceptions. `Mem` (memory operand), `Rela` and `Fixup` are plain fixed-size
structs.

## 3. Passes

```
gir_codegen_cpp(m, out):
  reset all module state
  layout_globals()                          pass 1, over globals and drelocs
  for each func: gen_function(fi)           pass 2, one pass per function
  write_elf(out)                            pass 3
```

### Pass 1: `layout_globals`

1. `g_has_reloc[owner] = 1` for every data relocation.
2. Symbol numbering. Index 0 is the null symbol. Every global with
   `GIR_GF_INTERNAL` gets the next index, in table order. That count + 1 is
   `n_local_syms`. All other globals follow, in table order. ELF requires
   local symbols first, and relocations need final indices, so this happens
   before any code is generated.
3. Variable placement (defined variables only):
   - `ZERO`: `.bss` at `align_up(bss_size, align)`.
   - `CONST` without relocations: append to `.rodata`, padded to `align`.
   - Anything else, including `CONST` with relocations: `.data`. This keeps a
     PIE link free of text relocations.

   Defined functions get `g_sec = 1` (`.text`). Their value and size are set
   in pass 2.

### Pass 2: `gen_function`

1. Pad `code` to 16 bytes with `0xCC` and record `start`.
2. **Frame layout** (`off` counts bytes below `rbp`, starting at 0):
   - each argument: `off += 8; a_off[a] = -off`
   - each instruction `j` in order:
     - ALLOCA: `off = align_up(off + max(size, 1), align); v_off[j] = -off`
     - `ty != void`: `off = align_up(off, 8) + 8; v_off[j] = -off`
     - PHI also gets a temp slot: `off += 8; t_off[j] = -off`
   - `frame = align_up(off, 16)`

   `rbp` is 16-byte aligned after `push rbp`, so every area is aligned as
   requested (the exporter guarantees align ≤ 16).
3. **Prologue**: `push rbp; mov rbp, rsp; sub rsp, frame` (the `sub` is left
   out when frame = 0). Then arguments go to their slots, zero-extended to 64
   bits: register arguments 0..5 (`rdi, rsi, rdx, rcx, r8, r9`) are
   normalized in place and stored; stack arguments 6.. are loaded from
   `[rbp + 16 + 8*(a-6)]` into rax, normalized and stored.
4. **Body**: for each block `b`, set `block_off[b] = code.len`, then call
   `gen_inst` for each of its instructions, in order (section 5).
5. **Fixups**: for each fixup, `rel32 = block_off[block] - (pos + 4)`. It is
   written little-endian at `pos`. A negative displacement wraps when
   computed in u32; in Goose, compute it in i64 and truncate.
6. `g_value[func.global] = start`, `g_size = code.len - start`.

### Pass 3: `write_elf` (section 8)

## 4. Value conventions

- A value narrower than 64 bits is kept **zero-extended to 64 bits** in
  registers and slots. i1 is 0 or 1.
- Normalization (`zext_reg`) runs after ADD, SUB, MUL, AND, OR, XOR, SHL,
  ASHR, SDIV and SREM. It also runs after TRUNC, PTRTOINT and SEXT, on the
  return value of a call, and on every argument in the prologue:

  | type | instruction |
  |---|---|
  | i1 | `and r32, 1` |
  | i8 | `movzx r32, r8` |
  | i16 | `movzx r32, r16` |
  | i32 | `mov r32, r32` |

- Sign extension to 64 bits (`sext_reg`) happens only where it changes the
  result: operands of signed ICMP predicates, SDIV and SREM, the first
  operand of ASHR, the source of SEXT and GEP indices narrower than 64 bits:

  | type | instruction |
  |---|---|
  | i1 | `and r32, 1; neg r64` |
  | i8 | `movsx r64, r8` |
  | i16 | `movsx r64, r16` |
  | i32 | `movsxd r64, r32` |

- Results that are already normalized are not normalized again: UDIV,
  UREM, LSHR, ZEXT, INTTOPTR, BITCAST, LOAD (zero-extending loads) and
  ICMP.
- Constants are zero-extended in the table (gir.h), so they can be loaded
  as immediates as they are.

## 5. Instruction selection

`load_val(r, v)` loads value `v` into register `r` and writes nothing else:

| value | code |
|---|---|
| INST that is an ALLOCA | `lea r, [rbp + v_off]` |
| other INST | `mov r, [rbp + v_off]` |
| ARG | `mov r, [rbp + a_off]` |
| CONST | `mov_ri(r, value)` (below) |
| GLOBAL, defined | `lea r, [rip + sym]`, relocation `R_X86_64_PC32`, addend -4 |
| GLOBAL, undefined | `mov r, [rip + sym@GOTPCREL]`, relocation `R_X86_64_REX_GOTPCRELX`, addend -4 |

`addr_of(v, scratch)` gives the memory operand of a pointer for LOAD and
STORE. An alloca becomes `[rbp + v_off]`, a defined global becomes
`[rip + sym]` (PC32), and anything else is loaded into `scratch` and used as
`[scratch]`.

`store_result(j, r)` is `mov [rbp + v_off[j]], r`.

`cur` is the current local block. "next" is `cur + 1`, the block laid out
after it. A jump to "next" is left out.

| GIR op | emitted code |
|---|---|
| RET | `load_val(rax, a)` if a ≠ NONE; `leave; ret` |
| BR | `phi_moves(cur, a)`; `jmp a` unless a = next |
| CONDBR, neither target has PHIs | `load_val(rax, a); test eax, eax`; if b = next: `je c`; else `jne b` and then `jmp c` unless c = next |
| CONDBR, a target has PHIs | `load_val(rax, a); test eax, eax; je L; phi_moves(cur, b); jmp b; L: phi_moves(cur, c); jmp c` unless c = next |
| SWITCH | `load_val(rax, a)`. Each case: `cmp rax, imm32` when the value fits a signed imm32, else `mov rcx, imm; cmp rax, rcx`. Then `je target` if the target has no PHIs, else `jne L; phi_moves(cur, target); jmp target; L:`. Finally `phi_moves(cur, default)` and `jmp default` unless default = next |
| UNREACHABLE | `ud2` |
| ADD SUB AND OR XOR | `load_val(rax, a); load_val(rcx, b); op rax, rcx; zext_reg(rax, ty); store` |
| MUL | the same with `imul rax, rcx` |
| SHL LSHR | `load_val(rax, a); load_val(rcx, b); shl/shr rax, cl; zext_reg; store` |
| ASHR | the same with `sext_reg(rax, ty)` before `sar rax, cl` |
| SDIV SREM | `load a, b; sext_reg(rax); sext_reg(rcx); cqo; idiv rcx`; SREM: `mov rax, rdx`; `zext_reg; store` |
| UDIV UREM | `load a, b; xor edx, edx; div rcx`; UREM: `mov rax, rdx`; `store` |
| ICMP | `load a, b`; signed predicates with aux narrower than 64 bits: `sext_reg` both; `cmp rax, rcx; setcc al; movzx eax, al; store` |
| SELECT | `load_val(rax, a); load_val(rcx, b); load_val(rdx, c); test eax, eax; cmove rcx, rdx; store rcx` |
| ZEXT INTTOPTR BITCAST | `load_val(rax, a); store` |
| TRUNC PTRTOINT | `load_val(rax, a); zext_reg(rax, ty); store` |
| SEXT | `load_val(rax, a); sext_reg(rax, aux); zext_reg(rax, ty); store` |
| ALLOCA | nothing (the frame area is the value) |
| LOAD | `x = addr_of(a, rax)`; zero-extending load by `ty` into rax; i1: `and eax, 1`; `store` |
| STORE | `load_val(rax, a); x = addr_of(b, rcx)`; store of width `aux` from rax |
| GEP | `load_val(rax, a)`. For each `(idx, scale)` with scale ≠ 0 (0 is skipped; the exporter never emits it): `load_val(rcx, idx); sext_reg(rcx, type_of(idx))`, then scale 1: nothing; power of two: `shl rcx, k`; ≤ 2^31-1: `imul rcx, rcx, imm32`; else `mov rdx, scale; imul rcx, rdx`; then `add rax, rcx`. Offset ≠ 0: `add rax, imm` (imm8 or imm32), or `mov rcx, off; add rax, rcx`. `store` |
| CALL | section 6 |
| PHI | `mov rax, [rbp + t_off]; mov [rbp + v_off], rax` |

`phi_moves(from, to)` emits nothing unless block `to` starts with PHIs. For
each leading PHI of `to`, it finds the first pair whose pred is `from`, then
emits `load_val(rax, value); mov [rbp + t_off(phi)], rax`. The temp slots are
written on the edge and the result slots are read only at the start of the
block. That makes a swap (`a = phi [b], b = phi [a]`) correct.

ICMP condition codes:

| predicate | cc |
|---|---|
| eq | E (4) |
| ne | NE (5) |
| ugt | A (7) |
| uge | AE (3) |
| ult | B (2) |
| ule | BE (6) |
| sgt | G (F) |
| sge | GE (D) |
| slt | L (C) |
| sle | LE (E) |

## 6. Calls (SysV x86-64, integer class only)

```
n = c; s = b
sbytes = n > 6 ? align_up(8*(n-6), 16) : 0
if sbytes: sub rsp, sbytes; for k in 6..n: load_val(rax, arg k); mov [rsp + 8*(k-6)], rax
direct = callee is a GLOBAL whose kind is FUNC
if !direct: load_val(r11, callee)
for k in 0..min(n,6): load_val(ARG_REG[k], arg k)      // rdi rsi rdx rcx r8 r9
if sub & VARARG: mov eax, 0                             // al = number of vector registers
direct: call rel32 (R_X86_64_PLT32 against the symbol, addend -4)
else:   call r11
if sbytes: add rsp, sbytes
if ty != void: zext_reg(rax, ty); store
```

`rsp` stays 16-byte aligned: the frame is a multiple of 16, and so is
`sbytes`. `load_val` writes only its target register, so the argument
registers can be loaded in any order. Only caller-saved registers are used
(`rax rcx rdx rsi rdi r8 r9 r11`), plus `rbp` as the frame pointer, so
nothing besides `rbp` has to be saved.

## 7. Encodings

REX is `0x40 | W<<3 | R<<2 | X<<1 | B`. W selects 64-bit operand size, R
extends ModRM.reg and B extends ModRM.rm or the base register. It is left
out when it would be `0x40`, unless an 8-bit operand is one of
`spl bpl sil dil` (registers 4..7), which needs the bare `0x40`. Register
numbers: rax 0, rcx 1, rdx 2, rbx 3, rsp 4, rbp 5, rsi 6, rdi 7, r8..r15
8..15. Two-byte opcodes are written as `0F xx`.

Memory operands (`modrm_mem(reg, m)`, with `r = (reg & 7) << 3`):

| operand | bytes |
|---|---|
| `[rbp + d8]` | `45\|r, d8` |
| `[rbp + d32]` | `85\|r, d32` (used when d does not fit an i8) |
| `[rsp + d8]` | `44\|r, 24, d8` |
| `[rsp + d32]` | `84\|r, 24, d32` |
| `[reg]` (rax, rcx or rdx) | `00\|r\|reg` |
| `[rip + sym]` | `05\|r, 00 00 00 00`, with the relocation at the offset of the 4 zero bytes, addend -4 |

Instruction forms (all that the back-end emits):

| helper | instruction | encoding |
|---|---|---|
| `load64` | `mov r64, [m]` | REX.W `8B /r` |
| `store64` | `mov [m], r64` | REX.W `89 /r` |
| `lea64` | `lea r64, [m]` | REX.W `8D /r` |
| `load_typed` i1, i8 | `movzx r32, byte [m]` | `0F B6 /r` |
| `load_typed` i16 | `movzx r32, word [m]` | `0F B7 /r` |
| `load_typed` i32 | `mov r32, [m]` | `8B /r` |
| `store_typed` i1, i8 | `mov [m], r8` | `88 /r` |
| `store_typed` i16 | `mov [m], r16` | `66 89 /r` |
| `store_typed` i32 | `mov [m], r32` | `89 /r` |
| `mov_rr64 d, s` | `mov d, s` | REX.W `89`, ModRM `11 s d` |
| `mov_rr32 d, s` | `mov d32, s32` | `89`, `11 s d` |
| `alu_rr64 op, d, s` | add/or/and/sub/xor/cmp | REX.W `01`/`09`/`21`/`29`/`31`/`39`, `11 s d` |
| `imul_rr64 d, s` | `imul d, s` | REX.W `0F AF`, `11 d s` |
| `imul_rri64 d, s, i` | `imul d, s, imm32` | REX.W `69`, `11 d s`, id |
| `grp1_ri64 ext, r, i` | add (0) / sub (5) / cmp (7) r, imm | REX.W `83 /ext ib` if i fits an i8, else REX.W `81 /ext id` |
| `shift_cl64 ext, r` | shl (4) / shr (5) / sar (7) r, cl | REX.W `D3 /ext` |
| `shift_imm64 4, r, n` | `shl r, n` | REX.W `C1 /4 ib` |
| `and_ri32 r, i` | `and r32, imm8` | `83 /4 ib` |
| `neg64 r` | `neg r` | REX.W `F7 /3` |
| `div64 ext, r` | div (6) / idiv (7) | REX.W `F7 /ext` |
| — | `cqo` | `48 99` |
| — | `xor edx, edx` | `31 D2` |
| `setcc cc, r` | `setcc r8` | `0F 90+cc`, `11 000 r` |
| `movzx8 d, s` | `movzx d32, s8` | `0F B6`, `11 d s` |
| `movzx16 d, s` | `movzx d32, s16` | `0F B7`, `11 d s` |
| `movsx8_64 d, s` | `movsx d64, s8` | REX.W `0F BE`, `11 d s` |
| `movsx16_64 d, s` | `movsx d64, s16` | REX.W `0F BF`, `11 d s` |
| `movsxd d, s` | `movsxd d64, s32` | REX.W `63`, `11 d s` |
| `test_rr32 a, b` | `test a32, b32` | `85`, `11 b a` |
| `cmov64 cc, d, s` | `cmovcc d, s` | REX.W `0F 40+cc`, `11 d s` |
| `mov_ri r, v` | v ≤ 0xFFFFFFFF: `mov r32, imm32` | `[REX.B] B8+r id` |
| | v fits a signed i32: `mov r64, simm32` | REX.W `C7 /0 id` |
| | otherwise: `movabs r64, imm64` | REX.W `B8+r io` |
| `jmp_block` | `jmp rel32` | `E9 cd` (fixup) |
| `jcc_block` / `jcc_fwd` | `jcc rel32` | `0F 80+cc cd` |
| — | `call rel32` | `E8 cd` (`R_X86_64_PLT32`) |
| — | `call r11` | `41 FF D3` |
| — | `push rbp; mov rbp, rsp` | `55 48 89 E5` |
| — | `leave; ret` | `C9 C3` |
| — | `ud2` | `0F 0B` |
| — | function padding | `CC` |

For example, `mov rax, [rbp-8]` is `48 8B 45 F8`, `mov [rbp-0x90], rcx` is
`48 89 8D 70 FF FF FF` and `movzx edi, dil` is `40 0F B6 FF`. Every branch
uses rel32; there are no short jumps.

## 8. ELF layout

The section table is fixed. Every section is always present, even when it
is empty.

| # | name | type | flags | link | info | align | entsize |
|---|---|---|---|---|---|---|---|
| 0 | — | NULL | | | | 0 | |
| 1 | `.text` | PROGBITS (1) | AX (6) | | | 16 | |
| 2 | `.data` | PROGBITS | WA (3) | | | max variable align | |
| 3 | `.bss` | NOBITS (8) | WA | | | max variable align | |
| 4 | `.rodata` | PROGBITS | A (2) | | | max variable align | |
| 5 | `.rela.text` | RELA (4) | I (0x40) | 7 | 1 | 8 | 24 |
| 6 | `.rela.data` | RELA | I | 7 | 2 | 8 | 24 |
| 7 | `.symtab` | SYMTAB (2) | | 8 | `n_local_syms` | 8 | 24 |
| 8 | `.strtab` | STRTAB (3) | | | | 1 | |
| 9 | `.shstrtab` | STRTAB | | | | 1 | |
| 10 | `.note.GNU-stack` | PROGBITS | none (stack is not executable) | | | 1 | |

File layout, in order:

1. The ELF header (64 bytes): `7F 'E' 'L' 'F'`, class 2, data 1, version 1,
   then zeros up to 16 bytes, `e_type` 1 (REL), `e_machine` 62, `e_version`
   1, `e_shoff` patched at offset 40, `e_ehsize` 64, `e_shentsize` 64,
   `e_shnum` 11, `e_shstrndx` 9.
2. `.text`, aligned to 16.
3. `.data` and `.rodata`, each aligned to its own alignment.
4. `.rela.text` (aligned to 8) and `.rela.data`.
5. `.symtab`, `.strtab` (the GIR `strtab` verbatim) and `.shstrtab`
   (`"\0.text\0.data\0.bss\0.rodata\0.rela.text\0.rela.data\0.symtab\0.strtab\0.shstrtab\0.note.GNU-stack\0"`).
6. The section headers, aligned to 8.

`.bss` and `.note.GNU-stack` take no bytes; their offset is the current
position.

Symbols are 24 bytes each: `st_name u32, st_info u8, st_other u8, st_shndx
u16, st_value u64, st_size u64`. They are written in the order of pass 1:
null, the locals in table order, then the others in table order.

| field | value |
|---|---|
| binding | LOCAL (0) if `INTERNAL`, WEAK (2) if `WEAK`, else GLOBAL (1) |
| type | NOTYPE (0) if undefined, FUNC (2) for a defined function, OBJECT (1) for a defined variable |
| `shndx` | `g_sec` |
| `st_value`, `st_size` | `g_value`, `g_size` |

Relocations used:

| type | number | used for |
|---|---|---|
| `R_X86_64_PC32` | 2 | `lea` or memory operand of a defined global |
| `R_X86_64_PLT32` | 4 | direct calls |
| `R_X86_64_REX_GOTPCRELX` | 42 | address of an undefined global (`mov r, [rip+sym@GOTPCREL]`), which works in PIE and non-PIE links |
| `R_X86_64_64` | 1 | data relocations: `r_offset = g_value[owner] + offset`, symbol = target, addend from GIR |

The relocation `info` field is `(symbol << 32) | type`.

## 9. Porting notes for Goose

- **Arrays.** Every growable array is a global `T[>..]`. Use `push` to emit
  bytes. `resize(n, 0)` replaces the "grow, never shrink" per-function
  arrays, and `clear()` resets the module arrays at the start of
  `gir_codegen`. The object is returned as `const u8[:]` over a global
  `u8[>..]`, so it stays valid until the next call (see `cg.goose`).
- **Data stack.** Goose arrays live on its data stack. The synthetic
  5k-function input (0.8M instructions) gives 12 MB of `.text` and a 14 MB
  object. 20k functions give about 50 MB of `.text`, and the object buffer
  is about the same size again, so the data-stack reservation must be large
  enough.
- **No recursion, maps or callbacks.** The C++ has none.
  `gen_inst` is a `switch` on the opcode, which becomes a `match` or an
  if-chain. `static const` tables (`ARG_REG`, section names, `sh_type`,
  `sh_flags`) become global `let` arrays.
- **Integer widths.** The C++ mixes u32, i32, i64 and u64 with implicit
  conversions. Goose needs them explicit:
  - rbp offsets are i32;
  - frame arithmetic is i64;
  - code positions are u32;
  - `rel32 = target - (pos + 4)` must be computed in i64 and truncated to
    u32 (it is negative for backward jumps);
  - immediates are written as their low 32 bits (`b4((uint32_t)imm)`).

  Byte writes take the low 8 bits (`(uint8_t)x`). In Goose that is an
  explicit truncating cast.
- **`fits8` and `fits32`** test whether a signed 64-bit value fits a signed
  8- or 32-bit immediate. `mov_ri` takes the u64 bit pattern: `v ≤
  0xFFFFFFFF` (unsigned) gives the 5-byte form, and `(i64)v` fitting an i32
  gives the `C7` form.
- **Input access.** `M->insts[i]` and the other tables are read-only slices.
  `type_of(v)` reads `insts`, `opnds` or `consts`. The back-end never writes
  the input.
- **Field names.** The Goose mirror of `GirConst` names its padding field
  `reserved` (`pad` is a keyword). All other names match gir.h, and goose
  adds a `_g` suffix in the generated C.
- **Testing a port.**
  - `tests/run.py --backend=goose --goovm <goovm-llc built with GOOVM_WITH_GOOSE>`
    runs the differential tests.
  - `cmp` against the C++ output checks that the bytes are identical.
  - `goovm-llc --dump-gir` shows what the tables hold.
