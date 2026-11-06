# The Goose back-end: notes

Sections 1-7 are the record of the **v0 port** (GIR v0, commit 8f55b18):
`cg.goose` was then a 1:1 port of `backend-cpp/gir_codegen_cpp.cpp` (see
[`../backend-cpp/DESIGN.md`](../backend-cpp/DESIGN.md)) to Goose (compiler
commit 335fddc), writing **byte-identical** objects (79/79 inputs). They
describe that version; file and function names there are v0's.

Section 8 is milestone **A1**: the v1 back-end for GIR v2 (all of C at -O0),
now split into `cg.goose`, `gir.goose`, `x86.goose`, `loc.goose`,
`abi.goose`, `lower.goose` and `elf.goose` and described in
[`DESIGN.md`](DESIGN.md). It records the new Goose pain points (with the
compiler's messages) and the speed against v0.

v0 page contents:

- the structure of the port;
- every place where it differs from the C++, and why;
- the bounds checks that remain;
- what the measurements say about the speed;
- the Goose pain points met on the way.

| file (v0) | what |
|---|---|
| `cg.goose` | the back-end: `export fn gir_codegen(...) -> const u8[:]` |
| `build.sh` | generated `build/cg.c` + `build/cg.h` and built goovm-llc with `-DGOOVM_WITH_GOOSE=ON` (now: configures CMake, which runs goose) |
| `check_identical.py` | `cmp`s `--backend=cpp` and `--backend=goose` objects over all tests and benchmark inputs (v0 only) |

## 1. Structure

The file follows the C++ top to bottom, with the same section comments and the
same function names in the same order. All 69 C++ functions exist under the
same name. There are three exceptions:
- `gir_codegen_cpp` is `gir_codegen`, the exported name the driver calls.
- `GIR_KIND` and `GIR_IDX` from gir.h become `gir_kind()` and `gir_idx()`.

The data layout is the same:

| C++ | Goose |
|---|---|
| `const GirModule *M` | `var M: Module`, a global struct of nine `const T[:]` slices of the host's tables, set at entry. `M.insts[i]` reads like `M->insts[i]`; the counts are the slices' `.len` |
| file-scope `std::vector<T> x` | global `var x: T[>..] = [];` (15 of them, each on its own data stack: `goose check --stacks` reports 16 regions) |
| scalars (`bss_size`, `f_first_inst`, ...) | global `var`s |
| `struct Mem`, `Rela`, `Fixup` | the same structs, same field types and order (`Fixup.block` is `blk`, see 2) |
| `static const` tables (`ARG_REG`, section names, `sh_type`, `sh_flags`) | global `let` arrays (`ARG_REG`, `SEC_NAMES`, `SH_TYPE`, `SH_FLAGS`) |
| `enum : int { RAX = 0, ... }` | untyped named constants (`let RAX = 0;`), which adapt to any integer type like a literal |
| `switch (I.op)` in `gen_inst` | `match I.op { GIR_RET => ..., GIR_ADD, GIR_SUB, ... => ..., _ => ... }` on named constants; clang turns it into jump tables |
| `vector::assign(n, 0)` | `clear()` + `resize(n, 0)` |
| `obj_out` (the caller's vector) | global `var obj: u8[>..]`, returned as `const u8[:]`, valid until the next call |

The control flow, loop structure, arithmetic, frame layout, instruction
selection, encodings, relocation handling and ELF layout are the C++'s,
statement for statement. Goose's -O2 inliner plus clang -O3 collapse it into
6 C functions:
- `gir_codegen_g`, with gen_function, gen_inst, layout_globals and write_elf inlined;
- `op_mem`, `load_val`, `phi_moves`, `mov_ri` and `addr_of`.

The C++ keeps about 17 helpers out of line (`b4`, `rex`, `opc`, `op_rr`,
`grp1_ri64`, `jmp_block`, ...).

The generated C is built by CMake exactly like the C++ back-end: the same
compiler (clang-20) and `CMAKE_BUILD_TYPE=Release` flags (`-O3 -DNDEBUG`).
That is one level above what `goose build` itself uses (`cc -O2`, no other
flags). `GS_RANGE` (the debug-only `as` check) compiles to nothing in this
build.

## 2. Where the Goose version differs from the C++, and why

Each item is marked `NOTE(port)` in `cg.goose`. None of them changes the
algorithm or the output.

1. **Bulk copies instead of byte loops.** The C++ copies byte by byte with
   `push_back` in three places:
   - `obytes`: `.text`, `.data`, `.rodata`, `.strtab` and `.shstrtab` into the object;
   - `append_aligned`: initializers into `.data`/`.rodata`;
   - the section-name loop in `write_elf`.

   The Goose version uses `append`, which is a memcpy. This is the idiomatic
   form, and a literal byte loop is slow in Goose (section 4, experiment E1,
   and pain point 6). It
   is worth about 24 ms on gen-5000 in Goose (E1). The same change on the
   C++ side (`insert`) is worth about 4 ms (E2).
2. **Records are copied, not referenced.** `let I = M.insts[gi]` copies the
   16-byte record, the Goose idiom for a fixed-size element. The C++ binds
   `const GirInst &I`. The same goes for `GirBlock`, `GirGlobal`, `GirFunc`
   and `GirDataReloc`. This makes no measurable difference (E8).
3. **Integer types of helper parameters.** Registers, opcodes, extensions
   and condition codes are `u32` (C++: `int`), so the encoder needs no casts.
   The `int` 0/1 flags (`p66`, `force`, `byte_reg`) are `bool`. All values
   are small and non-negative, so the behaviour is identical.
4. **Renamed identifiers.** `Fixup.block` is `Fixup.blk`, and the local
   `type` in `write_elf` is `typ`: `block` and `type` are Goose keywords.
   `GirConst.pad` is `reserved`, as before.
5. **Range slices and length asserts (for bounds checks, section 3).**
   - `gen_function` takes each function's runs of instructions, blocks and
     argument types as slices, one range check each, and iterates the slices
     (`for I, j in insts`). It asserts what the grow-only resizes already
     guarantee: `v_off.len >= insts.len`, `t_off.len >= ...`,
     `a_off.len >= ...` and `block_off.len >= ...`. The loops then run
     without checks.
   - `patch4` takes `code[p..p + 4]` (one range check instead of four).
   - The CALL case slices its argument run once.
   - The fixup, `rela_text` and `drelocs` loops are `for x in array` loops.
6. **`append_aligned(sec, sec_align, g)` takes `g: i64`** (C++:
   `uint32_t`), the caller's loop-index type. With a `u32`, the call's
   `g as! u32` hides `g < M.globals.len` from the analysis, and two checks
   per variable stay.
7. **`checkfree`** marks the 54 functions of the byte-output and encoder
   layer: `b1` .. `b8`, `rex`, `opc`, `modrm_mem`, `op_mem`, `op_rr`, the
   `m_*` constructors, every instruction helper, `zext_reg`/`sext_reg`, and
   `o1` .. `obytes`. The compiler verifies that they have no bounds check
   left.
8. **Out-of-range input aborts.** An out-of-range index in the input aborts
   with a bounds-check message instead of being undefined behaviour. The
   exporter never produces one.

**No bug was found in the C++ back-end.** I checked every encoding and the
PHI, CONDBR, SWITCH, GEP, CALL and ELF logic while porting. The only finding
is a performance one: the C++ byte-by-byte `push_back` copies, and the
vector growth (section 4). These are C++ style choices, not bugs, so the C++
is unchanged.

## 3. Bounds checks

`goose check --stats backend-goose/cg.goose` reports:

| | index checks kept | slice/range checks kept | total kept |
|---|---:|---:|---:|
| first working port | 81 of 132 | 2 of 2 | 83 |
| final | 49 of 120 | 10 of 10 | 59 |

These are static sites, counted per inlined copy. The dynamic cost is small.
With `GS_IDX` redefined to an unchecked index in the generated C (E7), the
back-end time on gen-5000 goes from 26.9 to 26.4 ms, about 2%, within noise.

**Removed** (section 2, items 5-6):
- every per-instruction check of the frame-layout loop (`M.insts[...]`,
  `v_off[j]`, `t_off[j]`);
- the per-argument checks (`M.opnds[arg_tys + a]`, `a_off[a]`; `ARG_REG[a]`
  was already elided under `a < 6`);
- the per-block checks (`M.blocks[...]`, `block_off[b]`);
- the per-argument checks of CALL;
- `rela_text[i]` and `M.drelocs[i]` in `write_elf`;
- `M.globals[g]` and `g_value[g]` in `append_aligned`;
- three of the four checks in `patch4`.

**Kept, and why:**

- **Inherent: the index is read from the GIR tables.** No length relation
  can prove these, because they are only as valid as the input. This is the
  great majority of the dynamic checks:
  - operands: `M.insts[i]`, `v_off[i - f_first_inst]`, `a_off[i]`,
    `M.consts[i]`, `M.globals[i]`, `g_sym[g]` in `load_val`, `type_of`,
    `is_alloca`, `is_defined_global`, `addr_of` and `m_rip`;
  - block numbers: `M.blocks[f_first_block + b]` in `has_phi`/`phi_moves`,
    `block_off[x.blk]`;
  - operand runs: `M.opnds[I.b + ...]` in `phi_moves`, SWITCH and GEP;
  - `g_value[f.global]`, `g_has_reloc[d.owner]`, `g_value[d.owner]`,
    `g_sym[d.target]`;
  - the range slices themselves (`M.insts[first..first + n]`,
    `M.data[G.data..G.data + G.size]`, `code[p..p + 4]`).

  Index types (`u32 in a`) cannot help here:
  - they need a global grow-only array, and the GIR tables arrive as slices
    from C;
  - the per-function arrays are indexed by values read from the input, so an
    index type would only move the check to the conversion.

  Removing these checks would need an input-validation pass, which the C++
  does not have, so that would change the algorithm.
- **Analysis gaps** (pain point 5):
  - `g_sec[g]`, `g_value[g]` and `g_size[g]` in `write_elf`'s symbol loop;
  - the operand runs of PHI, SWITCH and GEP (slicing them did not help, and
    that change was reverted);
  - `M.funcs[fi]`;
  - `o[40..48]` (the e_shoff patch, once per object).

## 4. Results

### Byte-identical objects

`check_identical.py` builds the `-O0` and mem2reg bitcode of every
`tests/c/*.c` (as `tests/run.py` does), plus every benchmark input, and
compiles each with both back-ends of one goovm-llc binary:

```
identical: 79/79  (differ: 0, failed: 0, unsupported: 0; 35 test programs x 2 variants + 9 benchmark inputs)
```

The 9 benchmark inputs are gen-1000, gen-5000, gen-20000, spass and typeset
from `make_inputs.sh`, plus an older gen-200, gen-5000, spass and typeset
set. With `--opt-passes "sroa,early-cse,instcombine,simplifycfg,gvn"` the
result is 107/110 identical. The other 3 are unsupported by the exporter on
both back-ends: `llvm.fshl`, `llvm.bitreverse` and `llvm.scmp`, as
`tools/goovm-llc/README.md` predicts.

### Tests

- `tests/run.py --backend goose`: **70 passed, 0 failed** (35 programs,
  O0 and mem2reg).
- `tests/realworld_mixed.py --backend goose`: SPASS (44/51 files by
  goovm-llc) and consumer-typeset (35/51) link, run and print the same as the
  all-clang build.

### Sanity timings

These are `goovm-llc --time` `backend_us` values, the median of 3 runs on a
shared 4-core VM. This is not a quiet machine; the final timing is yours.
Both back-ends come from the same binary, built by `build.sh`.

| input | gir insts | object | C++ back-end | Goose back-end | C++/Goose |
|---|---:|---:|---:|---:|---:|
| gen-5000 | 802K | 14.1 MB | 62.1 ms | 26.9 ms | 2.3x |
| gen-20000 | 3.21M | 56.2 MB | 260 ms | 110 ms | 2.4x |
| spass | 114K | 2.4 MB | 9.4 ms | 4.6 ms | 2.0x |
| typeset | 119K | 2.8 MB | 11.2 ms | 4.9 ms | 2.3x |

`goose_init`/`goose_exit` (which reserve and release 16 data-stack regions)
fall outside `--time`. Their cost is not measurable here. Whole-process wall
time minus `total_us` is about 30 ms (process start-up, loading libLLVM) in
every configuration: the plain C++ build, the Goose-enabled build with
`--backend=cpp`, and with `--backend=goose`. A single `bench/backend/run.sh -n 1`
row can show either back-end ahead in wall time; use `-n 5` or more.

On gen-20000, over the `--backend=llvm-only` process:
- C++: +153 MB peak RSS, +52K page faults;
- Goose: +109 MB peak RSS, +26K page faults (48.8 MB `.text` + 56.2 MB
  object).

### Where the difference comes from (attribution experiments)

Goose is faster, so there was no Goose overhead to fix. Instead, I checked
that the result does not come from the port being less than 1:1.

The experiments use variants of either back-end, relinked into goovm-llc with
the same flags. They live in the scratch directory only; the repo's C++ is
unchanged. Every variant was byte-identical. Times are for gen-5000, median
of 3:

| | variant | C++ | Goose |
|---|---|---:|---:|
| | as committed | 62 | 27 |
| E1 | Goose copies byte by byte like the C++ (`push` loops instead of `append`) | | 51 |
| E2 | C++ uses `insert` instead of its three byte loops | 58 | |
| E3 | E2 + `reserve` (code 64 MB, rela_text, obj exact) | 45 | |
| E4 | E3 + `always_inline` on b1/b4/b8/rex/opc/modrm_mem/op_mem/op_rr/here | 42 | |
| E5 | E3 + a Goose-style bump buffer for `code` (mmap reservation, `*e++ = x`, no capacity check) | 34 | |
| E6 | E5 + E4's `always_inline` | 32 | |
| E7 | Goose with every bounds check removed (`GS_IDX(i,n,f,l)` = `(i)`) | | 26.4 |
| E8 | Goose binds references (`let I .= M.insts[gi]`) instead of copying records | | 27.2 (28.0 in the same session) |

How to read this:

- **The model of the growable array accounts for most of the gap.** The
  Goose `T[>..]` sits on its own data stack, an address-space reservation
  with a guard gap. Each push is just a store plus a bump of `top` and `len`.
  There is no capacity check, no reallocation and no copy, and the elements
  never move. A `std::vector` pays at three points:
  - growth: reallocation, copying, and pages faulted twice. About 13 ms
    (E2 → E3).
  - a capacity compare on every `push_back`. Its inlined `_M_realloc_insert`
    slow path makes every emitter function large: `store64` alone is about
    5 KB of code. Clang then keeps the emitters out of line, and the
    `uint8_t` stores force it to reload `_M_finish` and `_M_end_of_storage`
    after every byte. Removing the check (E5) is worth about 11 ms;
    inlining alone (E4, E6) only 2-3 ms.
  - With Goose's memory model hand-built in C++ (E6), the C++ is still about
    15% behind (32 vs 27 ms). The rest was not attributed. Candidates: the
    remaining vectors (`rela_text` and `fixups` still `push_back`), and the
    Goose inliner flattening gen_function, gen_inst and write_elf into one
    function before clang sees it.
- **Bulk copies.** In C++, `insert` instead of the byte loops gains 4 ms. A
  literal byte loop in Goose costs 24 ms (E1): pushing through a `u8[>..]&`
  parameter keeps both `top` and `len` in memory and does a load/modify/store
  of each per byte (pain point 6). Even with E1, Goose beats the unmodified
  C++ (51 vs 62 ms).
- **Bounds checks cost Goose about 2%** (E7). They are predictable compares
  against lengths that sit in L1.
- **The record-copy idiom is neutral** (E8).

My reading for the research question: with each language's standard
growable array, the same back-end is 2.0-2.4x faster in Goose. That is a
consequence of Goose's memory model, not of a different algorithm. If the
C++ is hand-tuned to emulate that model (E6), the gap shrinks to about 15%.

## 5. Goose pain points

These are in rough order of how much they cost. The messages are verbatim
from `goose check`. Overall the port was easy: `cg.goose` typechecked on its
first compile, and the first build produced byte-identical objects on every
input. Most of the effort went into the bounds-check analysis.

1. **Keywords that collide with ordinary C++ names.**
   - `block`, a struct field in the C++:
     `error: expected identifier in struct body, found 'block'`.
   - `type`, a local in the C++:
     `error: expected identifier in variable declaration, found 'type'`.
   - `pad`, already known.

   The workaround is to rename (`blk`, `typ`). The message does not say that
   the word is a keyword.
2. **Explicit conversions everywhere.** The port has 46 `as!` and 27 `as`
   in 1087 lines. `.len` is `i64`, so every comparison or arithmetic with a
   `u64` or `u32` needs a cast. For example, `sec.len % al` with `al: u64`
   gives
   `error: operands of % have no common type: i64 and u64 (convert one with `as`)`.
   Every byte write needs `x as! u8`
   (`error: expected a value of type u8, got u32 (narrowing and sign changes require an explicit `as`)`),
   and every frame offset needs `(-off) as! i32`. At each site you choose
   between `as` (checked in debug builds) and `as!` (never checked). This is
   noisy, but each message says what to do.
3. **A silent shift hazard.** A shift has its left operand's type and the
   count is masked to the width. So `let x: u64 = s << 32;` with `s: u32`
   compiles without a warning, even with a constant count, and yields `s`
   unchanged: it prints `3` for `s = 3`. The C++ `(uint64_t)x.sym << 32` cast
   must stay as `x.sym as u64 << 32`. Elsewhere the compiler warns about
   casts it considers redundant, which encourages deleting casts. It does not
   flag this one; it is not redundant, but nothing points at the trap either.
4. **No integer enums.** Goose `enum` is an ADT, so each C++ enumerator
   becomes its own `let` named constant: about 120 lines where the C++ has
   about 25. `match` on those constants, with several constants per arm,
   maps the C++ `switch` cleanly.
5. **Gaps in the bounds-check analysis.** Each was found with `--bce-lines`:
   - **a.** `if a.len < n { a.resize(n, 0); }` does not establish
     `a.len >= n` afterwards. An explicit
     `assert(v_off.len >= insts.len && ...)` after it does.
   - **b.** A narrowing at a call site (`append_aligned(..., g as! u32)`)
     drops the caller's `g < M.globals.len` from the callee's entry facts.
     Making the parameter `i64` restores it.
   - **c.** `code[pos..pos + 4]` with `pos: u32` does not give a slice of
     known length 4, presumably because the u32 addition may wrap. All four
     element checks stayed, on top of the range check. Computing in i64
     (`let p: i64 = pos; code[p..p + 4]`) fixes it.
   - **d.** A slice of a data-derived run, indexed with computed offsets,
     elides nothing. Examples are `let ops = M.opnds[s..s + 1 + 2 * n]` with
     `ops[1 + 2 * k]` for `k < n`, and even `ops[0]`. Only loops bounded by
     the slice's own `.len` benefit (the CALL case).
   - **e.** A size-dependent loss. In `write_elf`'s symbol loop,
     `assert(g_sec.len >= M.globals.len && ...)` before the loop does not
     elide `g_sec[g]`, `g_value[g]` or `g_size[g]`. Bisection:
     - Deleting *any one* of the loop body's six statements, even a
       constant `o1(o, 0)`, makes all three elide.
     - A minimal repro with the same shape elides them.
     - A goose build with the analysis's fact cap (`MAXFACTS`, bce.h)
       raised from 200 to 2000 still keeps them.

     So some other budget or heuristic gives up. The checks are left in
     (3 per global symbol) and the ineffective assert was removed.
   - **f.** Index types cannot express the useful cases (section 3).
   - **g.** There is no escape hatch for a check you know is unnecessary.
     The spec mentions "a designated unsafe-fast build", but there is no
     flag for it, and `GS_IDX` is defined unconditionally in the generated
     C. E7 had to rewrite the macro in `cg.c`.
6. **The cost of `push` depends on how the array is reached, which the
   source does not show.**
   - Inside one function, a push to a global or local keeps `top` and `len`
     in registers and stores them back once.
   - A push through a `T[>..]&` parameter, or after a call, does a
     load/store of the data stack's `top` *and* of the header's `len` for
     every element. The `u8` store may alias both, as far as C knows.

   A byte loop through `o: u8[>..]&` (E1) ran at about 1.9 ns/byte, against
   0.5 ns/byte for the C++ `push_back` loop. `std::vector` keeps only one
   counter, `_M_finish`. The fix is to use `append` (memcpy) for bulk data,
   which is the idiom anyway, but nothing warns you when a loop is in the
   slow form.
7. **Mixed index types.** `for x, i in xs` yields an `i64` index, while
   `for k in a..b` takes the type of its bounds (`u32` here). Code that
   mixes them (`gen_inst(k, b as! u32)`) needs casts, and per 5b the choice
   also affects bounds checks.
8. **`--bce-lines` is per line, summed over inlined copies.** For example,
   `patch4` showed "3 kept" for each of its 3 inlined copies. It has no
   column or expression information and does not show the source text. I
   used a 20-line script to join it with the source
   (`python3 $S/work/exp/bce.py $GOOSE cg.goose`, in the scratch directory, not
   committed).

## 6. Things that surprised me

- **Storing export parameters in a global is accepted.** The checker lets
  `M = Module { funcs: funcs, ... }` store the export function's
  parameters, slices of host memory, in a global. This keeps the port's
  `M.insts[i]` exactly like the C++. The flip side: after `gir_codegen`
  returns, `M` holds views the host may free. Nothing stops another export
  function from reading `M` later, and the spec (§7.11) says nothing about
  the lifetime of export parameters. The port only reads `M` during the
  call.
- **The speed result.** I expected Goose to be at best even with the C++.
  The attribution experiments (section 4) say the win is real and comes from
  the growable-array model.
- **The two compilers inline very differently.** The Goose -O2 inliner plus
  clang leave 6 functions; the C++ keeps about 17 helpers out of line.
- **`checkfree` was accepted on the whole encoder at once,** without
  changing a line.

## 7. Rebuild and reproduce (v0, at commit 8f55b18)

```bash
S=/tmp/claude-0/-home-user-goovm/593b2907-8413-508c-8bdb-c68ef6e66f6e/scratchpad   # this session's scratch
export GOOSE=$S/work/goose-build/goose GOOSE_STDLIB=$S/src/goose/stdlib
cd /home/user/goovm

# generate backend-goose/build/cg.{c,h} and build goovm-llc with both back-ends
backend-goose/build.sh $S/work/build-goose
L=$S/work/build-goose/tools/goovm-llc/goovm-llc

# byte-identical check over tests/c (O0 + mem2reg) and the benchmark inputs
backend-goose/check_identical.py --goovm $L --inputs $S/work/inputs-final $S/work/inputs -j4

# differential run tests and real-world mixed links
tests/run.py --goovm $L --backend goose -j4
tests/realworld_mixed.py --goovm $L --backend goose -j4

# timing (one run each; the benchmark script prints best-of-N)
$L --backend=cpp   --time $S/work/inputs-final/gen-5000.bc -o /tmp/a.o
$L --backend=goose --time $S/work/inputs-final/gen-5000.bc -o /tmp/b.o && cmp /tmp/a.o /tmp/b.o
bench/backend/run.sh -n 5 --goovm $L --goose $S/work/inputs-final/*.bc

# bounds-check report
$GOOSE check --stats backend-goose/cg.goose
$GOOSE check --bce-lines backend-goose/cg.goose
```

`bench/backend/make_inputs.sh OUTDIR` regenerates the benchmark inputs. The
E1-E8 variants and the script that relinks them are in
`$S/work/exp/` (`link.sh`, `t.sh`, `e*.cpp`, `e*.goose`, `e*.c`).

## 8. Milestone A1: the v1 back-end

v1 compiles all of C at -O0 (GIR v2): 4,299 lines of Goose in seven files
(v0: 1,087 in one), described in [`DESIGN.md`](DESIGN.md). Everything below
was found while writing and testing it; the messages are verbatim from
`goose check` (compiler commit 335fddc) or from the generated program.

### New pain points

1. **A cast before a range parses as a variable-mode type.** In
   `M.strtab[s.name as i64..s.name as i64 + s.name_len]`, `i64..` is read as
   the variable-mode type `i64..`:
   `error: variable mode (..) applies only to ADT type names`.
   Parenthesizing (`(s.name as i64)..`) works, and then the compiler says
   the cast is redundant (a u32 range bound is fine), so the fix is to drop
   the cast. The message does not hint at the precedence problem.
2. **A `match` arm cannot yield several results.** For a function
   `-> bool, u32, u32, u32`, the arm `F_OEQ => false, CC_E, CC_NP, 1,` is
   parsed as further patterns:
   `error: _ cannot be listed with other patterns` (on the `_ =>` arm).
   Workaround: pack the four values into one integer in the `match` and
   unpack them in a wrapper that `return`s them.
3. **Unsigned arithmetic wraps before widening, silently.**
   `var k: i64 = A.n_in - 1;` with `n_in: u32 = 0` computes `0xFFFFFFFF` in
   u32 and then widens it, so a "count down to 0" loop started at
   4294967295. The bounds check caught it at run time:
   `goose runtime error: index 4294967294 out of bounds (length 118)
   (backend-goose/lower.goose:1397)`. The fix is `A.n_in as i64 - 1` (a
   cast that decides the width of the operation, which the compiler accepts
   without a "redundant" warning). This is the same family as v0's shift
   pitfall (pain point 3): the operation's width comes from the operands,
   the destination type does not matter, and nothing warns.
4. **Self-recursion through a helper needs `recursive fn`**, even for an
   alias that resolves in one step:
   `error: recursive call cycle through sym_type, which is not declared
   `recursive fn` (§7.8)`. Clear and fixable (unrolled the one step); the
   type-walk for struct returns is a real `recursive fn` (`ret_leaves`).
5. **Defensive casts produce warnings by the dozen.** The first compile of
   v1 gave 55 `warning: redundant `as i64`: a u32 converts to i64 implicitly
   here` (and `as u64`). Helpful, but there is no fix-it mode; I removed them
   with a script driven by the warning list.
6. **`inline fn` is not a speed knob here.** Forcing `inline` on the small
   hot helpers (`zext_reg`, `sext_reg`, `grp1_ri64`, `put_gpr`, and even
   `gen_inst` into `gen_function`) changed the instruction count by less
   than 1% (callgrind) and the time not measurably: clang's -O3 on the
   generated C already does what matters. What helped were fast paths that
   do less work (section "Speed").
7. **Keywords keep colliding**: `type` again (`GirSection.type` is `typ` in
   the Goose mirror), and `loop`/`in` had to be avoided as names.
8. **Simple loops are expensive in the generated C.** The slot-sharing
   layout pass (a backward walk: load the 24-byte instruction, look up an
   operand mask, for each operand a range check, a mark check and maybe a
   free-list pop) executes about 150 x86 instructions per GIR instruction
   (callgrind, line-level on the generated C): every array access keeps its
   bounds check (`GS_IDX(...)`), every `i64` add its overflow check
   (`gs_add_i64(..., file, line)`), each record is copied by value, and the
   stores into `u32` arrays may alias the module globals (`GS_GL->...`), so
   clang reloads them after each store. The same loop in C would be a third
   of that. I limited the pass to functions where it matters (more than 256
   instructions) instead of fighting the code shape.

What went well: the seven files typechecked after fixing the four errors
above; the first build passed the 35 v0 tests (70/70); bounds checks turned
two exporter/back-end disagreements into exact `file:line` aborts instead of
corrupt objects (the u32 wrap above, and a GIR operand run that a new struct
type had been appended into, which the abort pointed at directly);
`checkfree` still covers the whole encoder.

### Bugs found by the test corpora (all fixed)

- Constant-pool entries in `SHF_MERGE` sections were referenced through the
  section symbol with addend `off - 4`; linkers resolve such relocations by
  the addend and picked the wrong piece (FP constants read as 0). Pool
  entries now get one local symbol each.
- `or` with a negative imm32 set the upper bits of a narrow value (the
  imm32 is sign-extended); results of `or`/`xor` with an immediate are now
  normalized.
- Vector values copied in 8-byte chunks right after lane-sized stores missed
  store-to-load forwarding: `Vector/build2` (200M calls building `<4 x
  float>` values lane by lane) ran 25x slower than clang -O0 (114 s vs
  4.6 s) and timed out. Vector homes are now copied lane by lane: 52 s,
  still 11x clang -O0, the slowest test relative to clang. Keeping small
  vectors in xmm registers is A2 work.
- Undefined TLS symbols must be `STT_TLS` or ld rejects the definition
  ("TLS definition in b.o section .tdata mismatches non-TLS reference").
- `floor(2.5)` etc. on constants must be folded: LLVM's code generator does,
  and a test links without `-lm`.
- CTMark consumer-typeset crashed (SIGSEGV, stack overflow): with one slot per
  value its recursive `Manifest` (16,000 GIR instructions) had a 97 KB frame
  (clang -O0: 2.1 KB). Large functions now share slots between values that
  die in their block (DESIGN.md §5): 2.9 KB.

### Speed

`goovm-llc --time` back-end phase, best of 7, on a shared (not quiet) 4-core
VM; v0 is the goovm-llc built from commit 8f55b18 (`--backend=goose`):

SPEED_TABLE

The v1 back-end executes about 1.25x the instructions of v0 per GIR
instruction (callgrind, spass: 42.3M vs 33.6M). Where the extra work goes:

- every operand and result now looks up its value class in the type table
  (v0 had eight hard-wired types), and the dispatch has 83 opcodes and six
  classes instead of 32 opcodes and one class;
- the GIR instruction record grew from 16 to 24 bytes (debug location,
  flags, 16-bit types), and the frame-layout loop that streams through it is
  memory-bound;
- calls go through the SysV classifier (FP registers, stack slots, byval);
  a fast path handles calls whose arguments all get registers;
- loads and stores of non-predefined types go through the generic
  odd-size paths; predefined i1..i64/ptr have a fast path.

Fast paths recovered most of the first version's gap (it executed 1.54x v0's
instructions): the frame-slot path in the encoder (`op_mem_t`: 99 → 63
instructions per memory operand), the register-only call path, and the
predefined-type load/store paths.
