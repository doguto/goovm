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

Section 11 is milestone **C1**: floating-point-heavy code at the speed of
clang -O0's (Bullet 1.69x -> 0.97x, tramp3d-v4 1.19x -> 1.02x): the causes
found with their measured shares, the fixes, what was tried and dropped, the
results and the pain points.

Section 12 is milestone **E1**: the optimizing mode (`-O1`): a middle-end
in Goose and a global register allocator (DESIGN.md §15, §16), with the
bugs the tests found, the Goose pain points, correctness, run time against
clang -O0/-O1/-O2, compile time, and the "LLVM -O2 IR + Goose back-end"
experiment.

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

## 11. Milestone C1: floating-point-heavy code

After A3, C programs and integer C++ ran at 0.95x to 1.05x clang -O0's
time, but Bullet (C++ physics, float) took 1.73x and tramp3d-v4 (C++
templates, double) 1.22x (`bench/results/final-2026-11-07/runtime-ctmark.md`).
C1 found the causes, none of them in the FP arithmetic itself (goovm's
`addss`/`ucomisd`/`cvtsi2sd` code was already as good as FastISel's), and
fixed them in the allocator-aware lowerings, the call lowering and the
epilogue (DESIGN.md §14). A screening of all 141 SingleSource benchmarks
found two more FP causes (false dependencies, load order).

### Method

`perf record -e cpu-clock` (software events; the VM has no hardware
counters) of the clang -O0 and the goovm build, compared per function, then
the hottest functions' code side by side (`llvm-objdump -d`), `valgrind
--tool=callgrind` instruction counts on a reduced tramp3d-v4 input, and
microbenchmarks in assembly for the hypotheses that the code alone could
not decide (epilogue forms, load orders). Shares were measured with builds
that add the fixes one at a time, timed in interleaved rounds (best of 3
per build, clang's build in the same rounds): the host's speed changes by
up to 25% within an hour (other VMs on the machine), and some effects grow
with it. tramp3d-v4's clang build took 13.3 s at one time and 16.1 s an
hour later, and goovm's ratio was 1.04x in the fast state and 1.18x in the
slow one (the 1.22x of the A3 report was measured in such a state).

### Causes and their shares

| # | cause | where | effect of the fix (goovm / clang -O0) |
|---|---|---|---|
| 1 | extractvalue of a returned `{<2 x float>, <2 x float>}` (Bullet's `btVector3`) copied the field lane by lane (4-byte moves) into its home; the 8-byte load of that home then missed store-to-load forwarding, twice per vector returned | Bullet | 1.694x -> 1.166x: 76% of the gap |
| 2 | the round trip of such a call result through memory (return registers stored to the aggregate's home, each field loaded, stored again to the temporary) | Bullet | 1.166x -> 1.072x: 13.5% |
| 3 | `load {<2 x float>, <2 x float>}, ptr %retval; ret` copied the aggregate into a home and loaded the return registers from it | Bullet | 1.072x -> 1.003x: 10% |
| 4 | a 16-byte inline memcpy with one `movups` load of a temporary that two 8-byte stores had just written (copy assignment after a call): forwarding missed | Bullet | 0.996x -> 0.962x |
| 5 | `leave` in the epilogue: about 5 cycles more per return in chains of small calls on this Sapphire Rapids host; functions byte-identical to clang's but for `leave` took 2x to 3.5x its time | tramp3d-v4 | 1.184x -> 1.013x: 95% of the gap |
| 6 | `mov rsp, rbp` / `lea rsp, [rbp-8k]` before the pops (the first replacement of `leave`) are as slow as `leave` in deep recursion; LLVM's `add rsp, n` is not | fibo, ackermann, recursive, Towers, oopack | 1.14x -> 0.94x, 1.13x -> 1.02x, 1.10x -> 1.03x, 1.11x -> 1.00x, 1.07x -> 0.96x (tramp3d-v4 1.03x -> 1.05x) |
| 7 | `cvtsi2sd`, `cvtss2sd`, `cvtsd2ss`, `sqrtsd` write only the low lanes of their destination and wait for its old value: in spectral-norm `cvtsi2sd %eax, %xmm0` waited for the caller's previous `addsd` into xmm0, serializing the `divsd` chain across calls | spectral-norm, fp-convert | 1.61x -> 0.52x, 1.52x -> 0.74x |
| 8 | a pointer load deferred to its GEP ran after the index load (`a[i]`: index, then pointer), about 20% slower in linpack's daxpy loop than the program order | Linpack | 1.15x -> 0.95x |
| 9 | `llvm.is.fpclass` (std::isnan) computed the whole FP class (2.9x clang's instructions in `std::isnan`) | tramp3d-v4 | not measurable (0.01% of its instructions) |

Not causes: the FP arithmetic, compares (ucomis with its parity handling),
int/FP and float/double conversions apart from 7, fneg/fabs (masks), libm
calls (the same calls as clang's), xmm spills at calls (as in LLVM -O0,
there are no callee-saved xmm registers), constant pools, the use of
callee-saved registers (a build without them ran tramp3d-v4 and fibo at the
same speed), the `mov rax, r11` before indirect calls, the operand order
of compares.

What is left: tramp3d-v4 runs at 1.01x to 1.07x depending on the host's
state and goovm executes 2.3% fewer instructions than clang (callgrind). Its
hottest remaining functions are byte-identical to clang's, only placed at
other addresses, and take 1.7x the samples while other identical functions
take 0.6x: code placement. clang's own build moves by the same amount with
`-falign-functions=64` (0.944x of its default build). Shootout/methcall
(C, 1.21x) is the same case and was 1.23x before C1.

### Fixes

1. **Call results defined in their return registers** (`ret_parts_fuse`,
   abi.goose): when every use of an aggregate call result is an extractvalue
   in its block that reads exactly one return-register part, the call gives
   each extractvalue its value in that register (xmm0/xmm1, rax/rdx) and the
   extractvalues emit nothing (`K_DONE`). The pre-pass counts extractvalue
   uses per value in the spare byte of `VInfo` (now `nev`).
2. **Allocator-aware extractvalue** of register-class fields: a load at the
   field's width from the aggregate's memory (`lower_extractvalue_a`).
3. **Deferred aggregate loads** into a `ret` or an extractvalue
   (`agg_load_pend`, cg.goose).
4. **Small memcpys in general-register moves**, 8/4/2/1 bytes, up to 32
   bytes, as FastISel's `TryEmitSmallMemcpy`.
5. **LLVM's epilogue** `add rsp, n; pop ...; pop rbp; ret` (`mov`/`lea rsp`
   only when the body moves rsp); `emit_prologue` asserts that the frame
   the epilogue assumed is unchanged.
6. **`xorps x, x` before partial-write conversions and sqrt** into a
   register that is not their operand.
7. **A GEP's base pointer is not deferred** when the GEP is not the next
   instruction (`late_gep_base`).
8. **is.fpclass fast paths** for the masks of `isnan`, `isfinite`,
   `isinf`, `isnormal`, zero and subnormal tests (`lower_isfpclass_a`).
9. A conditional branch with PHI moves on one edge only branches straight
   to the other successor (one taken jump per loop back edge instead of
   two); no measurable effect on these programs.

Tried and removed: constant-index GEPs of static allocas as frame addresses
like the allocas (marked in the pre-pass, offsets fixed up after the frame
layout; `movq %xmm1, -0x34(%rbp)` instead of `leaq -0x34(%rbp), %rax; movq
%xmm1, (%rax)`). It shrank Bullet's `.text` by 0.6% but made no measurable
run-time difference, and the extra pre-pass work cost 4% of the back-end's
time on gen-20000 (1.058x the A3 back-end with it, 1.021x without). An
indirect call through the callee's own register instead of r11 and a
different operand order of `cmp` (the register operand loaded first, as
clang does) made no difference either.

### New tests

`tests/ll/agg_returns` (hand-written IR with a C driver: the shapes the
fusion accepts and rejects: fields in reverse order, a call between the call
and its extractvalues, the same field twice, extractvalues in other blocks,
a whole-aggregate use, a legacy-lowered instruction in between, integer and
mixed parts with narrow integers, values that live across calls; aggregate
loads returned from a frame temporary, through a pointer and with a store in
between; extractvalue from loads, insertvalue chains, constants and of an i1
field), `tests/ll/frame_geps` (GEPs of allocas: chains, negative offsets,
PHIs, pointer compares, over-aligned and dynamic bases), `tests/cxx/03_fp_structs.cpp`
(a btVector3-like class, std::complex, pairs, mixed structs, as clang lowers
them), `tests/c/50_fp_classify.c` (special values of float and double
through every classification macro, NaN with every predicate as value,
branch and select, -0.0), `tests/c/51_fp_convert.c` (conversions at the
limits of every width, float/double rounding, overflow and underflow, mixed
arithmetic). `tests/run.py` runs `tests/ll/<name>/` programs: the IR files go
through `opt` (verify or mem2reg) instead of clang; the reference build
compiles them with clang -O0.

### Results

Raw data and the share measurements: `bench/results/c1-2026-11-07/`.

**CTMark** (`tests/suite.py --corpus ctmark,ctmark-cxx --variants O0,cc -j 1
--time-run 3`, best of 3, seconds; the A3 back-end, commit c96510d, measured
an hour before in the same session):

| program | clang -O0 | goovm C1 | C1 / clang | goovm-cc C1 | cc / clang | A3 / clang |
|---|---:|---:|---:|---:|---:|---:|
| sqlite3 | 3.651 | 3.698 | 1.01 | 3.676 | 1.01 | 1.03 |
| SPASS | 13.414 | 13.324 | 0.99 | 13.289 | 0.99 | 1.03 |
| ClamAV | 0.164 | 0.163 | 0.99 | 0.161 | 0.98 | 0.97 |
| lencod | 9.275 | 9.112 | 0.98 | 9.136 | 0.98 | 1.01 |
| mafft | 32.351 | 31.308 | 0.97 | 31.113 | 0.96 | 0.96 |
| consumer-typeset | 0.134 | 0.128 | 0.95 | 0.128 | 0.95 | 0.94 |
| 7zip | 12.296 | 11.751 | 0.96 | 11.900 | 0.97 | 0.98 |
| Bullet | 16.587 | 16.071 | **0.97** | 16.119 | **0.97** | 1.69 |
| kimwitu++ | 0.024 | 0.023 | 0.95 | 0.022 | 0.92 | 0.98 |
| tramp3d-v4 | 16.949 | 17.327 | **1.02** | 17.178 | **1.01** | 1.19 |
| geometric mean (clang >= 50 ms) | | | 0.983 | | 0.981 | 1.070 |

tramp3d-v4 measured 1.01x to 1.07x over the day's runs of the same build
(placement, see above).

**FP-heavy SingleSource benchmarks** (interleaved best of 3, run time /
clang -O0):

| benchmark | A3 | C1 |
|---|---:|---:|
| BenchmarkGame/spectral-norm | 1.63 | 0.53 |
| BenchmarkGame/n-body | 0.97 | 0.99 |
| Linpack/linpack-pc | 1.14 | 0.98 |
| Misc/fp-convert | 1.53 | 0.77 |
| Misc/flops (all modules) | 0.93 | 0.44 |
| Misc/flops-1 / -2 / -3 | 1.11 / 0.81 / 0.97 | 1.07 / 0.81 / 0.96 |
| Misc/flops-4 / -5 / -6 / -7 / -8 | 0.97 / 0.74 / 1.00 / 1.01 / 0.96 | 0.17 / 0.23 / 0.25 / 0.26 / 0.23 |
| Misc/mandel, mandel-2 | 1.10, 1.13 | 0.63, 1.00 |
| Misc/matmul_f64_4x4 | 0.98 | 0.86 |
| Misc/perlin | 0.99 | 0.86 |
| Misc-C++/Large/ray | 1.14 | 0.96 |
| CoyoteBench/fftbench | 1.40 | 0.91 |
| SmallPT | 1.06 | 0.99 |

With the build before the removal of the frame-address GEPs (no run-time
difference), also: Polybench gemm 0.95 -> 0.94, cholesky 1.01 -> 0.99,
fdtd-2d 1.02 -> 0.99, jacobi-2d 1.03 -> 0.99, seidel-2d 1.01 -> 1.00,
floyd-warshall 1.00 -> 1.00; Misc fbench 1.01 -> 0.99, ffbench 0.97 -> 0.98,
oourafft 1.01 -> 0.99, whetstone 0.99 -> 0.99; CoyoteBench almabench 0.99 ->
0.97, huffbench 1.01 -> 1.02; Stanford FloatMM 1.04 -> 1.01;
partialsums 1.05 -> 1.05; sphereflake 1.03 -> 0.99. The flops-4..8 and
spectral-norm results beat clang -O0 because its code has the same false
dependencies (cause 7), avoided or not by its register choice.

**bench/codequal** (`PER_KERNEL=1 bench/codequal/run.sh DIR 5 2`): 1.03x ->
0.99x llc -O0's time; `.text` 2,725 -> 2,786 bytes (1.08x llc's; `add rsp,
n` is 4 bytes where `leave` was 1, and the `xorps` before conversions).

**Compile speed** (`bench/backend/time_backend.py -n 11`, best of 11, ms):

| input | A3 back-end | C1 back-end | C1 / A3 |
|---|---:|---:|---:|
| gen-20000.bc | 223.3 | 228.0 | 1.021 |
| spass.bc | 12.0 | 12.2 | 1.017 |
| tramp3d-v4 | 26.7 | 27.3 | 1.022 |

(The exporter is unchanged.) An interleaved best of 31 on gen-20000 gives
1.021x; with the frame-address GEPs it was 1.058x, which is why they were
removed.

**Correctness** (final build, commit 6690a17): `tests/suite.py --variants
O0,g,mem2reg,cc,cc-g --verify-dwarf` over all corpora (two runs of `-j 1`
side by side: the C corpora in 5,583 s, CTMark and the C++ corpora in
4,066 s): 1,921 tests, 1,915 that pass with plain clang -O0, no failure, no
unsupported input, no fallback in any variant; `llvm-dwarfdump --verify`
passed on all 5,266 objects of the `g` and `cc-g` variants.
`tests/run.py`: 116/116 (57 programs: 51 in `c/`, 3 in `cxx/`, the mixed
program with its four variants, 2 in `ll/`). goosecc, built from the tree
with `frontend-goose/build.sh` (no change in `frontend-goose/`): `tests/run.py
--goosecc` 102/102, `tests/suite_goosecc.py --corpus ctmark --variants O0,g`
6/6 in both variants. `tests/gdb_oracle.py --corpus c`: 48 of 51 transcripts match clang -O0 -g
(723 stops); the three others (`40_varargs_fp`: the `va_end` line, `41_misc`:
the VLA's location list and label differences, as in §10, and the new
`50_fp_classify`: stepping out of a `switch` that returns) differ in the same
blocks with the A3 back-end. `--unwind --corpus c`: 51/51 programs, 443,090
instructions single-stepped, no mismatch (the new epilogue's `add rsp, n`
and pops included).

### Goose pain points

1. **A cast of an untyped constant to the field's type is "redundant"**:
   `vi[e].kind = K_DONE as! u8;` (a `let K_DONE = 5;` stored into a `u8`
   field) gives `warning: redundant `as! u8`: K_DONE is 5, which fits u8
   here`. Helpful once known: the named constants are untyped literals.
2. **The `u32` against `i64` comparison is implicit, the cast is noise**:
   `sc as i64 > lim` with `sc: u32` gives `warning: redundant `as i64`: a u32
   converts to i64 implicitly here`, while the same comparison against a
   `u64` is an error (§8, pain point 2): which mixes are implicit still has
   to be learned case by case.
3. **The loop index of `for x, i in xs` is `i64`**, so the part number in
   `ret_parts_fuse` needs `q as! u32` before it can index a bit mask (§5,
   pain point 7, still there).
Not Goose: this session's sandbox refuses shell commands with loops,
`awk` or computed program names, so every per-file step became a small
script in the scratch directory.

### Rebuild and reproduce (C1)

```bash
S=/tmp/claude-0/-home-user-goovm/593b2907-8413-508c-8bdb-c68ef6e66f6e/scratchpad   # this session's scratch
GOOSE=$S/work/goose-build/goose GOOSE_STDLIB=$S/src/goose/stdlib JOBS=2 backend-goose/build.sh build
G=build/tools/goovm-llc/goovm-llc; C=build/tools/goovm-cc/goovm-cc
tests/run.py --goovm $G -j2                                   # C, C++, mixed and IR programs
tests/suite.py --goovm $G --cc $C --variants O0,g,mem2reg,cc,cc-g --verify-dwarf -j2 --report suite.md
tests/suite.py --goovm $G --cc $C --corpus ctmark,ctmark-cxx --variants O0,cc -j 1 --time-run 3 --report rt.md
PER_KERNEL=1 GOOVM=$G TPDE=$S/work/a2/tpde-llc bash bench/codequal/run.sh /tmp/cq 5 2
python3 bench/backend/time_backend.py --goovm <A3 build> --goovm $G -n 11 \
    $S/work/inputs-final/{gen-20000,spass}.bc <tramp3d-v4 -O0 bitcode>
frontend-goose/build.sh /tmp/gcc && tests/run.py --goosecc /tmp/gcc/goosecc -j2
# profiles and microbenchmarks of this milestone: $S/work/c1/{prof.sh,cmp.py,dis.py,tround.py,tsuite.py,tbe.py,t/}
```

## 12. Milestone E1: the optimizing mode (-O1)

E1 adds an optimizer and a global register allocator to the back-end, used
when the GIR header's `opt_level` is 1 or more (`goovm-llc -O1`, `goovm-cc
-O1`, `goosecc -O1`; DESIGN.md §15, §16). 6,163 lines of Goose in thirteen
new files (`opt*.goose`, 5,304 lines; `rag.goose`, 859) and 309 changed
lines in `cg.goose`, `ra.goose`, `lowera.goose`, `abi.goose` and
`dwarf.goose`, every change behind `opt_on` / `rg_on`; additive GIR fields
(`opt_level`, `FN_NOINLINE`, `FN_ALWAYSINLINE`, `IF_NSW`), exporter and
driver plumbing in `tools/`, one line in `frontend-goose/src/main.goose`.

The middle-end works on a per-function copy of the GIR records (the OIR)
and writes new tables; it needs no persistent use lists, no hash maps of
instructions and no allocation per instruction. The scalar passes (mem2reg,
the simplifier, DCE, SimplifyCFG, CSE) passed the -O1 suite variant early;
the global allocator took longer, because every lowering of the -O0
allocator had to learn that some registers belong to values it does not
own.

### Bugs found by the tests (all fixed)

1. **srem folded with Goose's `%`** (torture `bitfld-1`): Goose's `%` is
   the Euclidean remainder (never negative), C's is truncating; constant
   folding of `srem` now uses `rem()`.
2. **The canonical-constant hash table filled up** on a module with more
   constants than its initial size; it is now sized from the input's
   constant count and grows.
3. **Block merging corrupted the successor lists** (CSR arrays shared by
   all blocks): merging rewrote the merged block's successors in place;
   they are now recomputed into a scratch array.
4. **Empty-block forwarding read stale predecessor lists** after an earlier
   forward in the same round: blocks touched in a round are marked and
   skipped until the CFG is rebuilt.
5. **The global allocator ran out of scratch registers** (`tests/c/23_matrix`,
   7zip's `Ppmd8.c`, `assert failed (rag.goose:798)`): with all ten
   pinnable GPRs taken, a lowering that needs three scratch registers (a
   GEP of a merged four-term address plus a store) found none. Pinned
   values that the instruction does not use now lend their register for
   one instruction (`rg_borrow`), and GEP merging keeps at most two terms.
6. **GVN's alias analysis read a replaced pointer** (torture
   `mayalias-2`): a store through a pointer that an earlier replacement had
   forwarded was attributed to the wrong memory generation; GVN now resolves
   every operand first.
7. **A pinned vector from a legacy lowering was never loaded** (torture
   `pr53645`, `pr53645-2`): the A1 lowerings write their result to the
   value's home, and the pinned register kept garbage; `rg_def_end` loads
   it.
8. **GVN never matched two GEPs** (a missed optimization): the key included
   the index of the operand run, which differs for every instruction.
9. **Unsigned division by a constant of 2^31 or more** overflowed the
   magic-number shift; it is now a compare (`x >= d`).
10. **Induction-variable widening rewrote a compare outside the loop**
    (`tests/c/21_sort`'s quicksort: the i64 twin does not dominate the
    exit): the "operand does not dominate its use" condition that the
    output then violated is now checked by `GOOVM_OPT=verify`, which found
    no other violation over the corpora.
11. **Loop rotation stored a constant through `o_ins`** (`index 2147483648
    out of bounds (length 80) (opt_licm.goose:521)`, most `tests/` programs
    at once): the demotion store of a header PHI's entry value took the
    value's type from its instruction record, and the entry value is often
    a constant or an argument (kind bits 31..30 set). The type now comes
    from the PHI.
12. **Known limitation, not fixed: torture `pr17377`** fails under
    `goovm-llc -O1` (`O1` and `O1-g`): it needs a `noinline` function to stay
    a call (`__builtin_return_address`), and clang -O0 IR marks every
    function `noinline optnone`, so the source's `noinline` is invisible.
    `goovm-cc -O1` (front end without `optnone`) passes it.

### New pain points

The messages are verbatim from the Goose compiler.

1. **An array a global struct may view cannot shrink.** The middle-end
   points the module's table views (M) at its output arrays, so clearing
   one for the next module is refused:
   `error: cannot clear x_insts: global M may hold a reference into it,
   stored at backend-goose/opt.goose:644 (§5.1)`. The rule is sound (a
   later `clear` would leave M dangling), but there is no way to say "M is
   reassigned before it is read again". The output arrays are append-only,
   with a region base per call (`xb_*`).
2. **Assigning the whole struct widens the analysis to every array of the
   same element type.** `M = Module { ..., insts: x_insts[..], ... }` made
   the checker assume that M may view *any* `u32[>..]` or `u8[>..]` global,
   and code generation's own arrays were refused:
   `error: cannot resize vi: global M may hold a reference into it, stored
   at backend-goose/cg.goose:924 (§5.1)` (and `b_tag`, `block_off`,
   `jt_case`, `mv_src`, `cfi_pro`, ...). Assigning the fields one by one
   (`M.insts = x_insts[xb_i..]`) keeps the analysis precise.
3. **The same code checks differently in another host program.** goosecc
   compiles the back-end with its own globals, and there a local slice
   read out of M before `rg_alloc` resized `vi` was refused:
   `error: cannot resize vi while blocks is still used: it may hold a
   reference or slice into it; it was read out of M and may point into M
   (§5.1)`. goovm-llc's build had accepted it; the field-by-field
   assignment of item 2 fixed both.
4. **One global namespace for all files.** `opt_scfg.goose` and
   `dwarf.goose` both had a counter named `sc_epoch`:
   `error: global name already declared: sc_epoch`. Every global of the
   middle-end now has a pass prefix (`fe_`, `th_`, `gv_`, `ds_`, ...).
5. **Untyped integer constants are `i64` where a type is inferred.** A
   block passed to a generic helper (`each_slot(i) { s => ... vget(i, s)
   ... }`, which calls `F(0)`) got an `i64` parameter from the literal:
   `error: no matching overload for call to vget ... argument 2: cannot
   pass i64 as u32`. The same for named type constants:
   `ins_cast(i, GIR_ZEXT, I64, a, I32)` with `let I64 = 5;` gives
   `argument 3: cannot pass i64 as u32`. Both need typed constants
   (`let SLOT_A: u32 = 0;`).
6. **A table of strings must stay untyped to be indexable.** `let OPN:
   u8[][>..] = ["ret", "br", ...];` cannot be indexed by opcode:
   `error: arrays of variable-size elements cannot be indexed, only
   iterated; for random access, keep your own array of references to them
   (§3.3)`; the untyped literal `let OPN = [...]` can.
7. **A block expression is not an operand.** `x || { opt_off(""); find(e,
   "verify") >= 0 }` gives `error: expression expected, found '{'`; it
   became two statements.
8. **`%` is Euclidean** (bug 1): correct and documented, but a C compiler
   written in Goose has to remember it for every constant fold.

### Correctness

`tests/suite.py` over all eleven corpora (1,921 tests, 1,915 pass with
clang -O0; the optimizing variants run the 1,894 that also pass with plain
clang-20 -O1), with `GOOVM_OPT=verify` (the SSA and CFG invariants checked
after every function) and `--verify-dwarf`:

| variant | pass | fail | unsupported |
|---|---:|---:|---:|
| O1 (`goovm-llc -O1` on clang -O0 IR) | 1,893 | 1 (`pr17377`) | 0 |
| cc-O1 (`goovm-cc -O1`) | 1,894 | 0 | 0 |
| O1-g | 1,893 | 1 (`pr17377`) | 0 |
| O2nv (clang -O2 IR without vectorizers) | 1,875 | 1 (`pr39501`: link) | 18 |
| O2ir (clang -O2 IR) | 1,821 | 1 (`pr39501`: link) | 72 |

`llvm-dwarfdump --verify` passes on all 2,570 `-O1 -g` objects; the
verifier found no violation. `tests/run.py --o1`: 246/246 (61 programs,
O0, mem2reg, O1, O1-g); `tests/run.py --goosecc --o1`: 165/165.

**-O0 unchanged.** Every source file of the corpora (2,651 files) compiled
by the base build (66ea246) and the E1 build gives byte-identical objects
for goovm-llc on -O0, -O0 -g and mem2reg IR and for goovm-cc -O0 and -O0 -g
(13,255 object pairs), and goosecc -O0 and -O0 -g on the 2,250 C files
(with `tests/c`) gives byte-identical objects too (4,500 pairs).

### Run time: CTMark

`tests/suite.py --corpus ctmark,ctmark-cxx -j 1 --time-run 3 --time-ref
O1,O2` (best of 3, seconds; the ratios against clang -O1 timed in the same
rounds; the host was quiet but its speed drifts by up to 25% within an
hour, which the same-round ratios absorb):

| program | clang -O0 | clang -O1 | clang -O2 | O1 | cc-O1 | O1 / clang -O1 | O2nv / clang -O1 |
|---|---:|---:|---:|---:|---:|---:|---:|
| 7zip | 12.12 | 7.66 | 7.66 | 8.46 | 8.50 | 1.10 | 1.15 |
| Bullet | 16.77 | 2.86 | 2.77 | 9.53 | 9.51 | 3.34 | 1.20 |
| kimwitu++ | 0.023 | 0.019 | 0.018 | 0.019 | 0.019 | 1.01 | 0.97 |
| tramp3d-v4 | 16.94 | 0.161 | 0.136 | 0.492 | 0.482 | 3.06 | 1.10 |
| ClamAV | 0.161 | 0.113 | 0.108 | 0.125 | 0.129 | 1.11 | 1.11 |
| SPASS | 13.57 | 5.42 | 5.28 | 5.81 | 6.02 | 1.07 | 1.08 |
| consumer-typeset | 0.134 | 0.084 | 0.079 | 0.091 | 0.091 | 1.09 | 0.92 |
| lencod | 9.61 | 3.16 | 2.99 | 5.02 | 4.98 | 1.59 | - |
| mafft | 32.50 | 13.40 | 13.13 | 23.57 | 23.66 | 1.76 | 1.78 |
| sqlite3 | 3.64 | 1.69 | 1.60 | 2.42 | 2.41 | 1.43 | 1.31 |
| **geometric mean** (9 with clang -O0 >= 50 ms) | | 0.282x -O0 | 0.268x -O0 | 0.443x -O0 | 0.445x -O0 | **1.57** | **1.19** (8) |

goovm -O1 runs CTMark 2.26x faster than its -O0 code (and clang -O0's) and
at 1.57x clang -O1's time (1.65x clang -O2's): the target of about 1.3x is
met by six of the ten programs (7zip, kimwitu++, ClamAV, SPASS, typeset at
1.01x to 1.11x) and missed by four. `cc-O1` (goovm-cc -O1) is the same
code within noise (1.58x).

**LLVM -O2 IR + the Goose back-end (O2nv).** The same back-end on IR that
LLVM's -O2 middle-end produced (`clang -O2 -fno-vectorize
-fno-slp-vectorize -emit-llvm`, then `goovm-llc -O1`: the Goose middle-end
runs on it too) runs at **1.19x clang -O1** over eight
programs (lencod's `macroblock.c` hits an assertion of the -O0 allocator in
a lowering that needs more registers than are free). The split of the gap:

- **Middle-end** (C++ abstraction): Bullet 3.34x -> 1.20x and tramp3d-v4
  3.06x -> 1.10x with LLVM's middle-end. Their hot code is small methods
  that LLVM inlines and then takes apart with SROA (btVector3 math,
  `Loc<3>` arithmetic returned through sret, `DomainTraits` operators); the
  Goose inliner's size limit (40 GIR instructions, 80 in loops) and its SROA
  (constant offsets only, no splitting of arguments passed through memory)
  leave many of those calls and copies.
- **Back-end**: mafft 1.76x / 1.78x and part of sqlite3 (1.43x / 1.31x).
  mafft's two DP loops (98% of its time) keep their loop-invariant floats
  in frame slots: FP values live across calls elsewhere in the function, the
  SysV ABI has no callee-saved xmm registers, and the global allocator does
  not split live ranges, so such a value gets no register anywhere (LLVM's
  greedy allocator splits it around the calls). A conditionally stored
  static (`mi`) also stays in memory (scalar promotion needs a dominating
  store).

### Run time: bench/codequal

The kernels of `bench/codequal/kernels.c` at scale 10 (best of 5, seconds;
`e1/cq.py`): goovm -O1 against clang -O1.

| kernel | clang -O0 | clang -O1 | clang -O2 | goovm -O0 | goovm -O1 | O2ir | goovm -O1 / clang -O1 |
|---|---:|---:|---:|---:|---:|---:|---:|
| sieve | 0.419 | 0.202 | 0.202 | 0.371 | 0.215 | 0.227 | 1.06 |
| sort | 1.720 | 1.018 | 1.000 | 1.699 | 1.171 | 1.345 | 1.15 |
| hash | 0.624 | 0.433 | 0.431 | 0.637 | 0.419 | 0.453 | 0.97 |
| matmul | 7.955 | 1.868 | 2.380 | 7.489 | 1.861 | 8.252 | 1.00 |
| string | 1.331 | 0.711 | 0.650 | 1.375 | 0.773 | 0.675 | 1.09 |
| fib | 0.138 | 0.066 | 0.071 | 0.134 | 0.086 | 0.098 | 1.31 |
| whole program | 12.21 | 4.44 | 4.74 | 11.91 | 4.70 | 11.18 | **1.06** |

What moved the kernels (measured one change at a time on the way): string
1.48x -> 1.09x (if-conversion of `if (k == m) total += ...` into a cmov,
then loop rotation, which removed the jump into the inner loop's test on
every entry; GVN's single-writer rule forwards `pats[p]` across the inner
loop), fib 2.2x -> 1.31x (tail recursion elimination with an accumulator:
one recursive call per level, as clang's), matmul 1.54x -> 1.00x
(induction-variable widening, GEP splitting in LICM). O2ir's matmul is
slow because LLVM -O2 vectorizes it and the vector code goes through the
A1 lowerings (memory homes).

### Compile time: the middle-end

`goovm-llc --time` (best of 5, ms; `e1/ctime.py`), single-threaded:

| input | GIR instructions | -O0 back-end | -O1 back-end | of which middle-end | middle-end per instruction |
|---|---:|---:|---:|---:|---:|
| spass.bc (SPASS, one module) | 114,371 | 10.8 | 245.7 | 210.0 | 1.84 us |
| typeset.bc | 119,262 | 9.2 | 135.9 | 111.2 | 0.93 us |
| gen-20000.bc (generated C) | 3,205,263 | 208.9 | 3,767.9 | 3,196.2 | 1.00 us |

The optimizing back-end takes 15x to 23x the time of the -O0 one: the
middle-end is 85% of it (the global allocator and the larger functions the
rest). The middle-end runs about 15 passes over each function, several of
them more than once (four rounds of simplify/GVN/DCE/SimplifyCFG), and
rebuilds the CFG analyses and use lists after each pass that changes the
CFG; loop rotation rebuilds them after every rotated loop.

### Compile time: goovm-cc -O1 against clang -O1 and -O2

Every compile command of CTMark (632 files, 316 C++; the -O0 configuration
with the level replaced), each file alone and single-threaded, best of 2
wall-clock runs (`e1/ctcomp.py`). The in-process phases: LLVM's
`Optimizer` + `CodeGenPasses` from `-ftime-trace` of `clang -O1 -c` /
`-O2 -c`, against goovm-cc -O1's export + Goose middle-end + Goose code
generation (`--time`):

| program | files (C++) | clang -O1 | clang -O2 | goovm-cc -O0 | goovm-cc -O1 | clang -O1 / goovm-cc -O1 | LLVM -O1 opt+CG | Goose export+opt+CG (middle-end) | LLVM -O1 / Goose |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 7zip | 212 (180) | 47.87 | 52.04 | 33.08 | 33.54 | 1.43x | 16.36 | 0.65 (0.42) | 25.0x |
| Bullet | 121 (121) | 20.47 | 23.26 | 12.02 | 12.47 | 1.64x | 10.01 | 0.49 (0.34) | 20.4x |
| ClamAV | 98 (0) | 10.50 | 12.76 | 3.75 | 4.05 | 2.59x | 7.00 | 0.35 (0.24) | 20.3x |
| SPASS | 51 (0) | 9.48 | 10.95 | 2.96 | 3.14 | 3.02x | 7.11 | 0.32 (0.25) | 22.4x |
| consumer-typeset | 51 (0) | 6.70 | 7.44 | 2.14 | 2.30 | 2.91x | 4.83 | 0.26 (0.18) | 18.6x |
| kimwitu++ | 14 (14) | 9.41 | 10.24 | 4.28 | 4.40 | 2.14x | 6.38 | 0.17 (0.11) | 37.6x |
| lencod | 55 (0) | 9.33 | 12.24 | 2.73 | 2.96 | 3.15x | 7.04 | 0.30 (0.22) | 23.8x |
| mafft | 27 (0) | 5.26 | 7.61 | 1.35 | 1.48 | 3.55x | 4.12 | 0.17 (0.13) | 24.1x |
| sqlite3 | 2 (0) | 6.58 | 8.56 | 0.40 | 0.69 | 9.52x | 6.08 | 0.26 (0.20) | 23.6x |
| tramp3d-v4 | 1 (1) | 12.69 | 14.89 | 2.69 | 3.11 | 4.08x | 12.26 | 0.35 (0.25) | 35.0x |
| **total** | 632 (316) | 138.29 | 160.00 | 65.41 | 68.16 | **2.03x** | 81.20 | 3.31 (2.34) | **24.5x** |

- End to end, `goovm-cc -O1` compiles CTMark 2.03x faster than `clang -O1`
  (2.35x than `clang -O2`): 2.6x to 9.5x on the C programs, 1.4x to 4.1x on
  C++, where clang's front end is most of the time. `-O1` costs goovm-cc 4%
  over its `-O0` (68.2 s against 65.4 s).
- The Goose middle-end and code generation (with the export) take 3.31 s
  where LLVM's -O1 optimizer and code generator take 81.2 s: **24.5x**
  faster (31x against -O2); the target was 5x. The middle-end is 2.34 s of
  the 3.31 s.

