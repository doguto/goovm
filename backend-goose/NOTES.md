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

Section 9 is milestone **A2**: the v2 back-end (register allocation and
instruction selection of LLVM -O0 class; two new files, `ra.goose` and
`lowera.goose`), with its bugs, pain points and measurements.

Section 10 is milestone **A3**: unwind information, C++ exception handling
and comdats, DWARF 5 debug information (two new files, `eh.goose` and
`dwarf.goose`), with the bugs the tests and the gdb oracle found, the pain
points and the measurements.

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
   of that. I limited the pass to functions where it matters (more than 512
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

### Correctness

`tests/suite.py --fallback -j3` with the final build (commit c698c97), three
variants each (`O0`, `g` = `-O0 -g`, `mem2reg`); "excluded" tests fail with
plain clang-20 -O0 too (gcc's builtins tests that need -O2 folding):

| corpus | tests | clang -O0 passes | goovm passes (O0 / g / mem2reg) | fallbacks |
|---|---:|---:|---:|---:|
| gcc-c-torture execute | 1427 | 1427 | 1427 / 1427 / 1427 | 0 |
| gcc-c-torture ieee | 57 | 57 | 57 / 57 / 57 | 0 |
| gcc-c-torture builtins | 54 | 48 | 48 / 48 / 48 | 0 |
| SingleSource UnitTests | 129 | 129 | 129 / 129 / 129 | 0 |
| SingleSource Regression/C | 37 | 37 | 37 / 37 / 37 | 0 |
| SingleSource Benchmarks (C) | 100 | 100 | 100 / 100 / 100 | 0 |
| CTMark C programs | 6 | 6 | 6 / 6 / 6 | 0 |

(torture: the 1,514 files minus the 87 the test-suite's CMakeLists lists as
unsupported or failing; ieee: 58 minus 1; builtins: 108 files = 54 tests.)

### Speed

`goovm-llc --time` back-end phase, best of 7, on a shared (not quiet) 4-core
VM; v0 is the goovm-llc built from commit 8f55b18 (`--backend=goose`):

| input | GIR insts | v0 back-end | v1 back-end | v1 / v0 | v0 export | v1 export |
|---|---:|---:|---:|---:|---:|---:|
| gen-20000.bc | 3,205,263 | 139.5 ms | 180.2 ms | 1.29 | 371.6 ms | 441.1 ms |
| spass.bc | 114,371 | 6.1 ms | 8.5 ms | 1.39 | 14.6 ms | 18.0 ms |

v1 before slot sharing (commit b00cfb8): 175.0 ms and 8.2 ms, so slot sharing
in functions of more than 512 instructions costs 3% to 4%; with a limit of
256 it cost 12% on gen-20000 (most of its functions have 257 to 512
instructions) and 5% on spass. The exporter (GIR v2 has more to say: types,
debug locations, ABI words) is 1.19x to 1.23x v0's.

The v1 back-end executes 1.32x the instructions of v0 (callgrind, spass:
44.2M vs 33.6M; 43.0M before slot sharing). Where the extra work goes:

- every operand and result now looks up its value class in the type table
  (v0 had eight hard-wired types), and the dispatch has 83 opcodes and six
  classes instead of 32 opcodes and one class;
- the GIR instruction record grew from 16 to 24 bytes (debug location,
  flags, 16-bit types), and the frame-layout loop that streams through it is
  memory-bound;
- calls go through the SysV classifier (FP registers, stack slots, byval);
  a fast path handles calls whose arguments all get registers;
- loads and stores of non-predefined types go through the generic
  odd-size paths; predefined i1..i64/ptr have a fast path;
- the slot-sharing layout of large functions (pain point 8).

Fast paths recovered most of the first version's gap (it executed 1.54x v0's
instructions): the frame-slot path in the encoder (`op_mem_t`: 99 → 63
instructions per memory operand), the register-only call path, and the
predefined-type load/store paths.

## 9. Milestone A2: register allocation

v2 keeps values in registers (DESIGN.md §4-§6): a forward pre-pass per
function, block-local allocation with write-through homes for values used
in other blocks, folding of compares, immediates, memory operands and
address modes, deferred loads and GEP addresses, jump tables, and vectors of
8 and 16 bytes in xmm registers. 7,269 lines of Goose in nine files
(A1: 4,299 in seven): `ra.goose` (the allocator, 1,034 lines) and
`lowera.goose` (the allocator-aware lowerings, 1,399) are new. A1's
lowerings stay for the rare classes behind a flush of the caller-saved
registers, so the allocator was brought up one opcode class at a time
(integer operations, compares, loads and stores, calls, FP, vectors) with
the tests passing in between. The
messages below are verbatim from `goose check` (compiler commit 335fddc).

### Bugs found by the tests (all fixed)

- **A prologue store into a slot the body had reused.** Arguments used in
  other blocks are stored to their home by the prologue, which is generated
  after the body. The body had already freed such a home at the value's
  last use, which resets its recorded offset to 0, so the prologue stored
  the argument at `[rbp+0]`, over the saved rbp (SIGBUS in
  `tests/c/38_aggregates`). The prologue now uses the offsets recorded when
  the homes were assigned.
- **A register file that outlived its function**: values of the previous
  function were still "in" registers at the next one's entry
  (`ra_func_start` resets it).
- **8-byte alignment for 16-byte slots** (`movaps` faulted); slots are now
  aligned by size class.
- **FP bits in a general register.** A1's `copysign` lowering left its
  result in rax, and the allocator recorded an f64 in a general register;
  three `ieee` tests failed. `ra_tierb_end` moves a legacy result of the
  wrong class, `copysign` got an xmm lowering, and `ra_gpr`/`ra_xmm` assert
  the class.
- **`trunc` to i32 marked clean.** A truncation is a register copy, so the
  upper half is the source's; `2003-05-26-Shorts` (mem2reg) printed wrong
  values once a 64-bit use trusted it. Narrowed values are dirty (`ST_EXT`)
  unless a 32-bit instruction wrote them (`tests/c/45_ra_widths.c`).
- **`lea` with a scaled index and no base.** SIB base 5 with mod 00 means
  "no base, disp32", not rbp, so `lea r, [x*4]` for a shift came out wrong.
  Only `lea r, [x + x]` (shift by 1) is used.
- **A deferred load through registers into a consumer with fixed
  registers.** A consumer that first moves something into a fixed register
  (a shift count into rcx, a dividend into rax) could overwrite the load's
  address register. Only consumers that read all their operands first take
  such a load (`pend_reg_ok`).

### New pain points

1. **A branch cannot yield several values.**
   `let ok, v = if c { two(5) } else { false, 0 };` gives
   `error: several values exist only in `return a, b;` and in a call's results, so a block or branch cannot end in `a, b`: return from each branch instead (§7.1)`.
   The message is good. The workaround (`var`s assigned in each branch, or
   a helper that returns) costs lines in the lowerings, which pick between
   (flag, memory operand) or (register, immediate) pairs all the time.
2. **The declared type does not reach the literals in a branch.**
   `let k: u32 = (if dbl { 0 } else { 2 }) + 1;` gives
   `error: expected a value of type u32, got i64 (narrowing and sign changes require an explicit `as`)`.
   `var k: u32 = 1; if !dbl { k = 3; }` works.
3. **`pad` again**, as a field of the per-value record
   (`struct V { reg: u8, pad: u16 }`):
   `error: expected '}' in struct declaration, found ':'`. Renamed `spare`.
4. **`ctz` is u64 -> i64.** `std`'s `ctz(x: u64) -> i64` is the only bit
   scan, and register masks are u32, so every use is `ctz(m) as! u32`
   (`ctz32` in `ra.goose`). A cast on the argument draws
   `warning: redundant `as u64`: a u32 converts to u64 implicitly here`;
   the narrowing of the result needs `as!`.
5. **Records are cheaper field by field.** The pre-pass first read the
   16-byte `VInfo` record whole (`let x = vi[u]; ...; vi[u] = x`): 75.0M
   instructions on spass, against 68.7M with `vi[u].field` reads and writes
   (callgrind). A `.=` reference binding gave no gain. Each `vi[u]` keeps
   its bounds check either way.
6. **Profiles of the generated C are flat.** clang inlines the static
   functions of the one generated C file into a few large ones:
   `gen_function` alone is 36.6M of the back-end's 72M instructions on
   spass, and line-level annotation spreads over many inlined copies.
   `goose -O0` does not change that (clang still inlines). A separate build
   with `CMAKE_C_FLAGS=-fno-inline` gave a per-function profile (which
   costs about 20% more instructions).
7. **A `match` on integer constants is a chain of compares** in the
   generated C (`if (op == 0) ... else if (op == 5 || op == 6 || ...)`).
   Putting the frequent opcodes (load, store, call, GEP, icmp) first in
   `gen_inst`'s 83-opcode match saved 1.2% of the back-end's instructions,
   so clang evidently did not make a jump table of it. Nothing in the
   source says that arm order matters.

### Results

Measured on the shared 4-core VM (another agent's test runs in parallel, so
single numbers move by a few percent); A1 is the build of commit 5d17665.

**Generated code: `bench/codequal`** (`PER_KERNEL=1 bench/codequal/run.sh
DIR 5 2`, best of 5 runs, seconds):

| kernel | clang -O0 | llc -O0 | TPDE | goovm A1 | goovm A2 | A2 / llc | A1 / llc |
|---|---:|---:|---:|---:|---:|---:|---:|
| sieve | 0.094 | 0.090 | 0.080 | 0.134 | 0.079 | 0.88 | 1.52 |
| sort | 0.370 | 0.370 | 0.362 | 0.522 | 0.364 | 0.98 | 1.43 |
| hash | 0.102 | 0.100 | 0.075 | 0.163 | 0.103 | 1.03 | 1.53 |
| matmul | 0.081 | 0.081 | 0.079 | 0.269 | 0.077 | 0.96 | 3.40 |
| string | 0.306 | 0.306 | 0.263 | 0.547 | 0.318 | 1.04 | 1.81 |
| fib | 0.006 | 0.006 | 0.006 | 0.009 | 0.006 | 1.10 | 1.57 |
| whole program | 0.975 | 0.982 | 0.890 | 1.682 | 0.962 | 0.98 | 1.72 |

(A1's column is from a run of its own, against its own llc time.)

**CTMark C programs** (`tests/suite.py --corpus ctmark --variants O0 -j 1
--time-run N`, best of N, seconds):

| program | clang -O0 | goovm A1 | goovm A2 | A1 / clang | A2 / clang |
|---|---:|---:|---:|---:|---:|
| sqlite3 | 3.669 | 14.803 | 3.694 | 3.95 | 1.01 |
| SPASS | 13.616 | 27.495 | 13.674 | 2.00 | 1.00 |
| ClamAV | 0.162 | 0.330 | 0.159 | 1.95 | 0.98 |
| lencod | 9.518 | 30.735 | 9.432 | 3.21 | 0.99 |
| mafft | 33.314 | 70.665 | 32.933 | 2.12 | 0.99 |
| consumer-typeset | 0.133 | 0.608 | 0.126 | 4.40 | 0.95 |
| geometric mean | | | | 2.78 | 0.99 |

(A2: best of 5; A1: best of 3, its run's clang -O0 times within 5% of
these.) sqlite3 was at 1.10x before the last round of changes (jump tables,
GEP chains, hints through casts); its VDBE loop is a `switch` over about 150
opcodes, which had been a chain of compares.

**Vector/build2** (200M calls building `<4 x float>` lane by lane):
clang -O0 4.757 s, goovm A2 5.484 s (1.15x), A1 51.8 s (10.9x).

**`.text` bytes:**

| input | llc -O0 | TPDE | goovm A1 | goovm A2 | A2 / llc |
|---|---:|---:|---:|---:|---:|
| gen-20000.bc | 10,457,901 | 12,463,678 | 48,124,970 | 10,465,581 | 1.00 |
| spass.bc | 515,668 | 604,813 | 1,478,415 | 525,655 | 1.02 |
| typeset.bc | 483,283 | 521,176 | 1,836,072 | 516,953 | 1.07 |
| codequal kernels | 2,578 | 2,980 | 10,818 | 2,705 | 1.05 |

**Compile speed** (`bench/backend/time_backend.py -n 7`, best of 7, ms;
TPDE: `Compile` of its `--time-trace`, best of 7):

| input | GIR insts | A1 back-end | A2 back-end | A2 / A1 | A1 export | A2 export | goovm A2 total | TPDE Compile |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| gen-20000.bc | 3,205,263 | 179.9 | 208.9 | 1.16 | 448.8 | 215.1 | 424.0 | 506.5 |
| spass.bc | 114,371 | 8.4 | 11.1 | 1.32 | 17.9 | 8.8 | 19.9 | 24.9 |
| typeset.bc | 119,262 | 9.5 | 9.9 | 1.04 | 18.1 | 9.7 | 19.6 | 16.7 |

The back-end does more per instruction (spass, callgrind: 72.5M
instructions, A1 44.2M): the pre-pass is about a quarter of it, the
register file and the allocator-aware lowerings most of the rest. It emits
a third of A1's bytes, which is why typeset (whose large functions made A1
share frame slots) costs about the same. The exporter is twice as fast as
A1's (same GIR, commit 00bdafc, plus cached GEP layouts), so the total is
below A1's everywhere and below TPDE's `Compile` on gen-20000 and spass;
on typeset it is 1.17x TPDE.

**Correctness** (`tests/suite.py -j3`, all corpora, final build):

| corpus | tests | clang -O0 passes | goovm passes (O0 / g / mem2reg) | unsupported | fallbacks |
|---|---:|---:|---:|---:|---:|
| gcc-c-torture execute | 1427 | 1427 | 1427 / 1427 / 1427 | 0 | 0 |
| gcc-c-torture ieee | 57 | 57 | 57 / 57 / 57 | 0 | 0 |
| gcc-c-torture builtins | 54 | 48 | 48 / 48 / 48 | 0 | 0 |
| SingleSource UnitTests | 129 | 129 | 129 / 129 / 129 | 0 | 0 |
| SingleSource Regression/C | 37 | 37 | 37 / 37 / 37 | 0 | 0 |
| SingleSource Benchmarks (C) | 100 | 100 | 100 / 100 / 100 | 0 | 0 |
| CTMark C programs | 6 | 6 | 6 / 6 / 6 | 0 | 0 |

1,810 tests x 3 variants in 1,728 s; the 6 excluded builtins tests fail with
plain clang -O0 too. `tests/run.py`: 98/98 (49 programs, O0 and mem2reg).

### What is left

- **Back-end time on many small functions**: spass (3,700 functions of 31
  instructions on average) is at 1.32x A1's back-end time. The pre-pass (a
  quarter of the back-end's instructions, mostly bounds-checked `vi[u]`
  field accesses) is the largest single cost.
- **typeset's total is 1.17x TPDE's `Compile`**: its exporter phase (9.7 ms,
  GEP-heavy) is the larger half.
- **Forward branches are always rel32** (no relaxation pass): on spass
  9,447 of 10,397 branches are rel32 (llc: 2,680 of 12,199), and rel8
  forms would save up to 24.9 KB, more than the 10.0 KB by which goovm's
  `.text` exceeds llc's (typeset: 28.3 KB of 33.7 KB). A relaxation pass
  would have to move the intra-instruction branches (`jcc_fwd`) and the
  jump-table entries too.
- **A GEP folds only into the instruction right after it**; `p->a[i]`
  with a load of `i` in between still costs an `lea`.
- Values that live across blocks go through memory, as with LLVM -O0
  (no global allocation); INT2, x87, f16, odd vectors, atomics, TLS and
  inline asm keep A1's lowerings behind a flush of the caller-saved
  registers.
- TPDE's code is faster than llc's on two kernels (hash 0.75x, string
  0.86x of llc); goovm is at 1.03x and 1.04x there.

### Rebuild and reproduce (A2)

```bash
S=/tmp/claude-0/-home-user-goovm/593b2907-8413-508c-8bdb-c68ef6e66f6e/scratchpad   # this session's scratch
GOOSE=$S/work/goose-build/goose GOOSE_STDLIB=$S/src/goose/stdlib backend-goose/build.sh build
G=build/tools/goovm-llc/goovm-llc
tests/run.py --goovm $G -j3                                   # 49 programs, O0 + mem2reg
tests/suite.py --goovm $G -j3 --report suite.md               # all corpora, O0 / g / mem2reg
tests/suite.py --goovm $G --corpus ctmark --variants O0 -j 1 --time-run 5
PER_KERNEL=1 GOOVM=$G TPDE=$S/work/a2/tpde-llc bench/codequal/run.sh /tmp/cq 5 2
bench/backend/time_backend.py --goovm $S/work/a2/goovm-a1 --goovm $G -n 7 \
    $S/work/a2/inputs/{gen-20000,spass,typeset}.bc
```

## 10. Milestone A3: unwinding, C++, DWARF

A3 makes the back-end's objects debuggable and unwindable and compiles C++:
`.eh_frame` with exact CFI for every function, the Itanium EH tables
(invoke, landingpad, resume, LSDA, personality), comdat groups, module asm,
and DWARF 5 as clang -g writes it (DESIGN.md §9-§12). The GIR additions are
backward compatible (gir/README.md, "Additions in milestone A3"): goosecc
still calls `gir_codegen` unchanged, and its `-g` objects now get a line
table and a minimal unit without a change on its side. New code: Goose
`eh.goose` (340 lines) and `dwarf.goose` (about 1,770), the
exporter's DWARF builder `gir_dwarf.cpp` (about 1,380 lines of C++, a port
of LLVM 20's DwarfDebug/DwarfUnit/LexicalScopes for one unit), EH and
comdat export in `gir_export.cpp`, module-asm symbol scanning in
`gir_asm.cpp`. The messages below are verbatim from `goose`.

### Bugs found by the tests (all fixed)

- **Comdat `.rodata` sections held the whole `.rodata`.** A constant in a
  comdat got a section of its own, still pointing at the shared `.rodata`
  buffer, so every such section repeated all of `.rodata`. Comdat rodata
  sections are now laid out like data sections.
- **`invalid file index 1 (valid values are [0,1))`** from
  `llvm-dwarfdump --verify` on 79 objects: in DWARF 5 the line program's
  file register still starts at 1, so a sequence whose rows were all in
  file 0 needs an explicit `DW_LNS_set_file 0`.
- **`file_names[1] is a duplicate of file_names[0]`**: the primary file was
  entered once by directory and once by full path.
- **Quadratic group writer**: every comdat scanned every section
  (tramp3d-v4: 75 ms of 102 ms of back-end time; now 28 ms).
- **`LLVM ERROR: Inline asm not supported by this streamer because we don't
  have an asm parser for this target`**: `goovm-llc --backend=llvm`
  (and `--fallback`) and `goovm-cc` on C++ with `<iostream>`'s module asm;
  the drivers now initialize the asm parser.
- **`-fenable-matrix` unsupported in goovm-cc**: the in-process driver did
  not apply the cc1 job's `-mllvm` options.
- Found by the gdb oracle (`tests/gdb_oracle.py`), each a place where gdb
  behaved differently on a goovm build than on a clang build:
  - rows for GIR instructions that emit no code (a folded compare or GEP,
    a deferred load, a branch to the next block) shared their address with
    the next row; gdb then stopped "on" the wrong line (`next` in a nested
    loop went from line 21 to 19). An instruction without code now leaves
    no trace in the line table, as it has no machine instruction in LLVM;
  - a block that is only a branch to the next block gets a 2-byte `jmp`,
    as LLVM's FastISel emits it "for more accurate line information"
    (`step` from an `if` body stops on the closing brace's line);
  - arguments loaded on the next line of a multi-line call were attributed
    to the call's line (deferred loads); their code now gets their row;
  - a variadic function's prologue_end goes on its register-save code, as
    LLVM 20's `findPrologueEndLoc` does past the save area's branch;
  - the unit's code ranges and the line-table sequences follow LLVM's
    `addRange` (a run of functions in one section; another section or a
    function without debug information ends it): a function of only line-0
    rows (`_GLOBAL__sub_I_*`) inherited the previous function's last line;
  - no `epilogue_begin` row at line 0;
  - `llvm.memcpy` above 32 bytes and every `llvm.memset` are libc calls, as
    in LLVM's -O0 (they were inline up to 256 bytes), so that `step` enters
    `memcpy` where it does in a clang build;
- Found by comparing `llvm-dwarfdump --debug-info` of goovm and clang
  objects (normalized for offsets and addresses):
  - libstdc++ 13's `always_inline` functions (`std::distance`,
    `__distance`, ...) are inlined even at -O0, so C++ objects need abstract
    subprograms and `DW_TAG_inlined_subroutine`s: the builder now ports
    LexicalScopes' inlined and abstract scopes and the back-end keeps code
    ranges per (scope, inlined-at) instance; `DW_AT_inline` needs
    `DW_FORM_implicit_const`, which the abbreviation writer now supports;
  - `-gline-tables-only`: no subprogram DIE for a function without inlined
    code (LLVM skips it);
  - a variable whose `#dbg_declare` address is `undef` is dropped, as
    FastISel drops it.

### New pain points

1. **`pad` once more**, as a local: `let pad = ...` gives
   `error: expected identifier in variable declaration, found 'pad'`, and
   in an expression `error: expression expected, found 'pad'`. (§5 and §9
   met it as a field.) Renamed `fill`.
2. **Recursion must be declared.** The scope-instance lookup for inlined
   code creates the enclosing instances first:
   `error: recursive call cycle through inst_of, which is not declared `recursive fn` (§7.8)`.
   `recursive fn inst_of(...)` fixes it; the message is exact. It is the
   only recursive function of the back-end.
3. **Narrowing a `u64` section size** for a `u32` field:
   `error: expected a value of type u32, got u64 (narrowing and sign changes require an explicit `as`)`.
   The ELF and DWARF writers mix u64 (ELF) and u32 (GIR, DWARF 32) offsets
   on every line; `eh.goose` and `dwarf.goose` have 115 `as!` and 39 `as`
   between them.
4. **Redundant-cast warnings in the other direction.**
   `warning: redundant `as u64`: a u32 converts to u64 implicitly here` and
   `warning: redundant `as i64`: a u32 converts to i64 implicitly here`
   (about twenty while writing `dwarf.goose`), also in
   `((s as u64) << 32 | ia as u64)`, about the second cast only: the first
   is required (§5, item 3), and the warnings make it look like noise.
5. **No arrays of growable arrays.** The DWARF writer would naturally keep
   a list of ranges per scope or a list of rows per section; an element type
   may not be resizable, so every per-key list is a linked list in one flat
   array (`Rng.next`, `sc_head`/`sc_tail`) or a counting sort
   (`lv_first`/`lv_attr`, the group members of the ELF writer).
### Results

### Results

Correctness runs shared the 4-core VM with another agent's test runs; the
timings were taken later on a quiet machine (load average 1).

**Correctness** (`tests/suite.py --variants O0,g,mem2reg,cc,cc-g
--verify-dwarf -j3`; `cc` and `cc-g` compile each file with `goovm-cc`,
clang's front end and the Goose back-end in one process; the `g` and `cc-g`
columns were run again on the final build after the last line-table
change, which does not touch code generation):

| corpus | tests | clang -O0 passes | O0 | g | mem2reg | cc | cc-g |
|---|---:|---:|---:|---:|---:|---:|---:|
| gcc-c-torture execute | 1427 | 1427 | 1427 | 1427 | 1427 | 1427 | 1427 |
| gcc-c-torture ieee | 57 | 57 | 57 | 57 | 57 | 57 | 57 |
| gcc-c-torture builtins | 54 | 48 | 48 | 48 | 48 | 48 | 48 |
| SingleSource UnitTests (C) | 129 | 129 | 129 | 129 | 129 | 129 | 129 |
| SingleSource Regression/C | 37 | 37 | 37 | 37 | 37 | 37 | 37 |
| SingleSource Benchmarks (C) | 100 | 100 | 100 | 100 | 100 | 100 | 100 |
| CTMark C programs | 6 | 6 | 6 | 6 | 6 | 6 | 6 |
| SingleSource UnitTests (C++) | 35 | 35 | 35 | 35 | 35 | 35 | 35 |
| SingleSource Regression/C++ | 31 | 31 | 31 | 31 | 31 | 31 | 31 |
| SingleSource Benchmarks (C++) | 41 | 41 | 41 | 41 | 41 | 41 | 41 |
| CTMark C++ programs | 4 | 4 | 4 | 4 | 4 | 4 | 4 |

1,921 tests (1,915 that pass with plain clang; the 6 excluded builtins
tests fail with it too) x 5 variants in 3,705 s at -j3: no failure, no
unsupported input, no fallback. `llvm-dwarfdump --verify` passed on all
5,266 objects of the `g` and `cc-g` variants.

The C++ corpora are SingleSource's C++ tests (UnitTests, Regression,
Benchmarks: 107 programs, including the EH directories) and CTMark's four
C++ programs (7zip, Bullet, kimwitu++, tramp3d-v4); none needs a fallback.
`tests/run.py`: 106/106 (49 C programs, `cxx/01_eh`, `cxx/02_cxx_features`,
`mixed/eh_through_c` with its `c-goovm` and `cxx-goovm` variants).
goosecc, built from the tree with `frontend-goose/build.sh` (no change in
`frontend-goose/`): `tests/run.py --goosecc` 98/98 (49 programs, `-c` and `-c -g`), and its 49 `-g`
objects pass `llvm-dwarfdump --verify` (5,932 line-table rows; gdb
breaks and steps by line in them).

**DWARF against clang** (`llvm-dwarfdump --debug-info`, offsets and
addresses normalized): identical for `t1.c`, `d1.cpp` (1,946 lines:
classes, templates, namespaces, imported entities), `c5.cpp`, `e1.cpp`
(11,193 lines with libstdc++'s inlined `std::distance`), and for programs
of `always_inline` functions with nested inlining, inlined lexical blocks,
methods and labels in C and C++ (1,693 lines); `-gline-tables-only` is
identical too. The only difference left is a VLA's location list.

**gdb oracle** (`tests/gdb_oracle.py`, clang -O0 -g vs goovm, 1,389 stops
in 93 programs: tests/c and a sample of 44 llvm-test-suite C and C++
programs): 87 of 93 transcripts match; the others differ as described under
"What is left". With `--unwind` (the first two activations of every
function single-stepped, the backtrace checked after each instruction):
91 of the 93 programs, 1.7 million instructions, without a mismatch; for
queens and the C++ ackermann (deep recursion) the gdb session did not end
within its 50 minutes.

**Unwind tables**: `llvm-dwarfdump --eh-frame` parses every FDE of the
oracle's objects without a warning, with one FDE per function (aliases
share theirs); C++ exceptions cross goovm-compiled C frames (plain calls,
`qsort` callbacks, function pointers, dynamic allocas, stack arguments)
with the stack pointer unchanged after each catch (`mixed/eh_through_c`).

**Compile speed** (`bench/backend/time_backend.py -n 11`, best of 11, ms;
A2 is the build of commit 35150d8):

| input | GIR insts | A2 back-end | A3 back-end | A3 / A2 | A2 export | A3 export | total A3 / A2 |
|---|---:|---:|---:|---:|---:|---:|---:|
| gen-20000.bc | 3,205,263 | 203.9 | 217.7 | 1.07 | 208.2 | 213.2 | 1.05 |
| spass.bc | 114,371 | 10.9 | 12.0 | 1.10 | 8.5 | 8.7 | 1.07 |
| typeset.bc | 119,262 | 9.5 | 9.9 | 1.04 | 8.8 | 8.8 | 1.02 |

`.eh_frame` costs 2% (gen-20000) to 4% (spass) of the back-end's time (a build without the FDEs of
functions without landing pads). `-g` multiplies the back-end's time by 2 (C) to
4 (tramp3d-v4, many small inlined template functions) and the exporter's by
4 to 6 (most of that is LLVM materializing the debug metadata the exporter
reads, not the DIE builder), but goovm stays far ahead of LLVM's own -O0
code generator with `-g`:

| input | goovm back-end | goovm export | goovm total | LLVM -O0 back-end | LLVM / goovm |
|---|---:|---:|---:|---:|---:|
| sqlite3.c | 9.5 | 7.7 | 17.2 | 233 | 13.5 |
| sqlite3.c -g | 19.0 | 31.3 | 50.3 | 428 | 8.5 |
| tramp3d-v4 (EH) | 34.0 | 29.6 | 63.6 | 1,692 | 26.6 |
| tramp3d-v4 (EH) -g | 129.7 | 167.5 | 297.2 | 2,557 | 8.6 |
| gen-20000 -g | 414.5 | 852.8 | 1,267.3 | | |

(`goovm-llc --backend=llvm --time`, best of 3, for LLVM; tramp3d-v4 without
exceptions: 26.5 + 25.0 ms.)

### What is left

- **Location lists.** LLVM describes a VLA (a `#dbg_declare` of a dynamic
  alloca, which FastISel turns into a `DBG_VALUE`) with a location list
  that starts at the allocation; goovm gives it its frame slot for the
  whole function, so gdb shows `a = <address>` instead of `<optimized out>`
  before the `int a[n]` line runs.
- **Statement starts where goovm folds a load that LLVM does not.** A2's
  deferred loads fold a single-use load into any later instruction of the
  block (LLVM's FastISel only into the instruction right after it). When a
  statement's first load is folded into an instruction on the next line
  (`x = a |\n (1 << b)`), the statement's first row is that line's, and
  `next` stops on the second line first (exptree). Deferred loads
  materialized into registers do get their own rows (above); folded
  memory operands take their user's, as in LLVM.
- **`va_end` lines.** `llvm.va_end` is no code, but LLVM's -O0 sometimes
  leaves the `lea` of its operand behind (and so a row for the line) and
  sometimes not (the oracle saw both);
  goovm has no row. Emitting the `lea` always matched clang in two of the
  four cases of the oracle's programs and broke the other two, so it was
  left out.
- **Jumps into the middle of a row.** In bigfib's `check()`, the early
  `return string();` jumps to the return block, which in clang's code
  starts in the middle of the closing brace's row (so `next` goes straight
  back to the caller) and in goovm's at the start of a forced `is_stmt` row
  (so `next` stops on the brace first).
- **Different frames**: gdb transcripts still differ where the program
  prints stack addresses or reads uninitialized memory that a library call
  wrote (the oracle normalizes what it can), and label differences
  (`&&l1 - &&l0`) are goovm's code sizes.
- **One compile unit per module**: a module linked from several units
  (`llvm-link`) gets DIEs for the first only (clang -c never makes one).
- Range lists use `DW_RLE_startx_length` throughout; LLVM uses
  `base_addressx` + `offset_pair` for several ranges in one section. Both
  are valid and gdb reads both.

### Rebuild and reproduce (A3)

```bash
S=/tmp/claude-0/-home-user-goovm/593b2907-8413-508c-8bdb-c68ef6e66f6e/scratchpad   # this session's scratch
GOOSE=$S/work/goose-build/goose GOOSE_STDLIB=$S/src/goose/stdlib backend-goose/build.sh build
G=build/tools/goovm-llc/goovm-llc; C=build/tools/goovm-cc/goovm-cc
tests/run.py --goovm $G -j3                                   # C, C++ and mixed programs
tests/suite.py --goovm $G --cc $C --variants O0,g,mem2reg,cc,cc-g --verify-dwarf -j3 --report suite.md
tests/gdb_oracle.py --goovm $G -j3                            # clang -O0 -g vs goovm under gdb
tests/gdb_oracle.py --goovm $G --unwind -j2                   # single-step unwinding check
frontend-goose/build.sh /tmp/gcc && tests/run.py --goosecc /tmp/gcc/goosecc
bench/backend/time_backend.py --goovm <A2 build> --goovm $G -n 11 $S/work/inputs-final/{gen-20000,spass,typeset}.bc
```
