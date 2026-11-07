# goosecc: notes on writing a C compiler in Goose

goosecc is about 17,600 lines of Goose without comments and blank lines
(compiler commit 335fddc, runtime d22ae129d92b): the front end of milestone
B1 (sections 1-8), the lowering to GIR of B2 (section 9), the speed
work of B3 (section 10) and the header cache of B4 (section 11), plus the
Goose back-end imported as a package. It is compiled with `goose
--standalone` to one 5.1 MB C file and then with `clang-20 -O2`
(2 s and 18 s). This page records what was
hard or surprising, with the compiler's own messages, and what was done about
it. Most of it is the price of Goose's memory model, which is also why the
result is fast and small (README.md, "Results").

## 1. Recursion (§7.8)

A recursive-descent parser and a clang-style macro expander are cycles of
dozens of functions. Goose requires each function on a cycle to be marked,
and the message names the function, not the cycle:

```
src/types.goose:...: error: recursive call cycle through type_size, which is not declared `recursive fn` (§7.8)
```

This came up 15 times (`type_size`, `type_name`, `mk_type`, `is_complete`,
`int_rank`, `is_signed`, `compatible_unq`, `member_walk`, `assign_convert`,
`starts_type_name`, `starts_declaration`, `sort_range`,
`find_member_designator`, `base_name`, `is_checkable`). Most are small
helpers over types that recurse once in a rare case (`type_size` of an
array's element, `int_rank` of an enum's underlying type, `mk_type` making
the plain version of an aligned type), so each was found by the compiler
rather than by design. 94 functions ended up `recursive fn`.

The rule that matters more is the one behind it: inside a cycle, no nonfixed
local (a growable array, an owned string) may be live across a call into the
cycle. That shaped the whole program (DESIGN.md, 5): every growable buffer is
a global, used as a stack with marks, and functions on a cycle return
indices instead of slices. Things that would be a local `Vec` in Rust or a
`SmallVector` in clang (the arguments of a macro invocation, the operands of
a call being parsed, the frames of an initializer walk, the parameter types
of a function declarator) are all regions of global arrays with a saved
length. It works, and the discipline is simple, but it is not checked: a
function that forgets to resize back leaks into its caller's part of the
buffer, and the bug shows up far away. The type printer for diagnostics,
which built the "before" and "after" parts of a declarator in local strings
and recursed for the inner declarator, was rewritten without recursion; the
AST dumper's printer recurses, but appends to a global buffer it is passed by
reference.

## 2. The aliasing checker (§5.1)

Goose checks that a slice or reference is not used after the array it may
point into is cleared or shrunk. It is conservative, and the messages say
why it thinks the two may alias:

```
src/main.goose:...: error: cannot clear opt_output while val is still used: it may hold a reference or slice into it; it was read out of a and may point into static data or argv_text (§5.1)
src/main.goose:...: error: cannot clear opt_output: the for loop at src/main.goose:51 iterates ["-I", "-D", "-U", "-isystem", ...], whose elements may refer into opt_output (§5.1)
src/ppexpr.goose:...: error: cannot clear bt while s is still used: it may hold a reference or slice into it (§5.1)
src/ppexpr.goose:...: error: cannot call attr_value: it shrinks bt while name is still used, and name may refer into bt (§5.1)
src/expr.goose:...: error: cannot call tname, which shrinks tn_buf: tname(from), evaluated earlier in the statement, may still refer into tn_buf (§5.1)
```

The second one is a false positive (a list of string literals cannot point
into `opt_output`), the others were plausible: the checker cannot know that
a slice of `argv` and a global buffer are distinct, or that a function
receiving a slice will not reach the buffer through a global. The
workarounds: command-line values are copied into the `names` arena and kept
as (offset, length); the `__has_attribute` normalization got its own buffer
(`bt2`) so that its input and output are different arrays; two type names
in one diagnostic are copied with `str()` first. The last message was a real
bug in a debugging line (two `tname` results compared, the second call
overwriting the first).

## 3. Names that are keywords

`guard`, `pad`, `block`, `type`, `match`, `loop`, `defer`, `in` and `self` are
keywords, and the errors do not say so:

```
src/common.goose:...: error: expected '}' in struct declaration, found ':'
src/common.goose:...: error: expected identifier in field access, found 'guard'
src/common.goose:...: error: guard is a statement: it guards the rest of the block it is in
src/types.goose:...: error: expression expected, found 'pad'
```

The include-guard field became `grd` and the padding fields `rsv`. Porting
code whose vocabulary is the preprocessor's ("guard") and the ABI's ("pad",
"type", "block") hits this often.

## 4. Integer typing

Goose does not convert integers implicitly when the value could change, and
named constants (`let TK_IDENT = 5;`) adapt to their context like literals.
But an `if` expression over named constants has type `i64`:

```
src/lex.goose:305: error: expected a value of type u8, got i64 (narrowing and sign changes require an explicit `as`)
            return Tok { kind: k, flags: flags, ... };    // let k = if lx_dir { TK_EOD } else { TK_EOF };
```

so token kinds and node kinds chosen by a condition need `as! u8`. Struct
fields have the narrowest type that fits, which then bites when a set of
flags grows: the 17th symbol flag gave

```
src/parse.goose:1529: error: constant 65536 does not fit u16
```

(`Sym.flags` became `u32`). In the other direction the compiler warns about
casts that are not needed (`warning: redundant `as i64`: a u32 converts to
i64 implicitly here`, 328 of them in this code), which is useful but makes
the build output noisy; they were left, since knowing which conversions are
implicit takes the compiler's view of every operand's type.
Mixed signedness has to be resolved by hand (`u32 and i32 do not unify; cast
one`), which in a C front end, where every value is a mix of u32 indices and
i64 values, means many casts.

`%` is Euclidean in Goose; C's truncating remainder (for `#if` and constant
folding) is `std.rem`. Operator precedence is Rust's, so `a & B != 0` means
`(a & B) != 0`, the opposite of C: code translated from clang's C++ has to
be read with that in mind.

## 5. Containers

A fixed array of dictionaries is not allowed:

```
src/ppexpr.goose:...: error: fixed array elements must be fixed-size: dictionary<u32, i64>
```

The `__has_*` tables (builtins, features, extensions, attributes, C
attributes, declspec attributes, warning options) became one
`dictionary<u64, i64>` keyed by `table << 32 | identifier`. Most other lookups (identifiers, types, include
paths) are hand-written open-addressing tables over global arrays, because
they key on spans of `src` and must not copy them.

## 6. Interfacing with C

In B1 four things needed C, through `extern fn` and `--include
src/goosecc_rt.h`: reinterpreting f64 bits in both directions (floating
literals and constant folding), rounding a double to float, and `memchr`
(line comments, block comments and line tables; B3 replaced it with std's
`find_any`, section 10). The extern mechanism is simple and worked the
first time.

## 7. Performance notes

(B1; section 10 has what B3 changed.) What the profiles led to: the lexer
hashes an identifier while scanning it and interns it without a second
pass; comments are skipped with `memchr`
(block comments by searching for the `/`, which is rare inside comments,
rather than the `*` that starts every line of a boxed comment); line tables
are built lazily, only for files that get a diagnostic or a line marker;
macro arguments are pre-expanded lazily and only once; the executable is
static. What remains is spread over the lexer, interning, the expander and
the printer, with no single hot spot.

- Each global growable array is its own data stack (a reserved region with
  a guard gap): goosecc has 106 of them plus 7 runtime stacks, and setting
  up 113 regions costs 113 × (mmap + mprotect + madvise) at start-up, about
  0.2 ms of a 1.5 ms run on an empty file. Merging globals would save it but
  would bring back the aliasing of section 1.
- Startup is otherwise glibc's (CPU feature detection, cache-size probing
  through `cpuid`, which is slow in a VM); linking statically saves the
  dynamic loader's 0.3 ms, about 5% of a typical CTMark file, and is the
  default in `build.sh`.
- Bounds checks: the compiler removes about 40% of the index checks (`bce:
  elided 768/1875 index and 79/165 slice checks`); the rest are in the
  profile but never dominant. The lexer's inner loops index `src` directly.
- Growable globals never move each other, so indices are stable and the
  data structures are flat arrays of small structs: peak RSS is 15-18 MB
  where clang needs 84-101 MB.

## 8. What worked well

- Compile errors carry a precise instantiation chain (`in fn ... instantiated
  from ...`), which made the recursion and aliasing errors quick to place.
- Out-of-bounds indexing stops the program instead of corrupting memory,
  so a crash on a corpus file was never a heisenbug.
- Multiple return values (`let ok, v = fold_int(n)`) fit a compiler's "did
  it fold, and to what" style.
- Generated tables as Goose source (`predef_gen.goose`, `builtins_gen.goose`,
  multi-line string literals parsed at start-up) needed nothing special.

## 9. Milestone B2: the lowering

B2 added about 8,100 lines of Goose (`gen_*.goose`, namespace `gen`)
and made goosecc a compiler: the typed AST is lowered to GIR v2 and the
back-end (`backend-goose/`, imported as a package) runs in the same
program. This section records what that was like; the messages are
verbatim from `goose check` (compiler commit 335fddc).

### Putting two Goose programs together

- **The package import worked at once.** `import cg from
  "../../backend-goose";` in the root file declares the back-end as a
  package whose entry is `cg.goose`; its own `import gir;` lines resolve
  inside the package. The front end and the back-end had no name in
  common, but the lowering was put in `namespace gen;` anyway, so that new
  names in either cannot collide later (an unqualified name resolves in
  `gen` first, then globally; `::name` would reach a shadowed global).
- **An export fn called from Goose checks its argument roots.**
  `gir_codegen` stores its parameters (slices) in the global `M`. Called
  from C that is allowed; called from Goose with a local array or a
  literal it is not:

  ```
  backend-goose/cg.goose:675: error: storing a reference rooted at header, which does not outlive the destination (§9.2)
  ```

  So the GIR tables are globals. The other side of the same coin: once `M`
  may hold views of them, nothing anywhere may shrink them:

  ```
  zz_test.goose:213: error: cannot clear hh: global M may hold a reference into it, stored at backend-goose/cg.goose:675 (§5.1)
  gen_tu.goose:223: error: cannot resize m_data: global M may hold a reference into it, stored at backend-goose/cg.goose:676 (§5.1)
  ```

  Even a `resize` that grows is refused (the checker does not know the
  direction); `data_grow` appends zero pages instead. For a compiler that
  handles one translation unit per process the tables never need to
  shrink, so this costs nothing, but the error is reported at the
  `resize`, far from the store that causes it.
- **A cascading error looks like a real one.** While other errors were
  pending, the check also reported

  ```
  backend-goose/cg.goose:669: error: export fn gir_codegen: could not resolve one concrete function signature
  ```

  which disappeared with them; it does not mean what it says.
- **C helpers against generated names.** The long double helpers take and
  return a Goose struct `F80 { lo: u64, hi: u64 }` by value. In namespace
  `gen` its C name is `gen_F80_g3` with fields `lo_g` and `hi_g`
  (spec §7.10), and `goosecc_rt.h` is written against those names; it
  works, but the header now depends on the mangling scheme.

### Recursion and aliasing, again

The expression lowering is one recursive cycle of about 60 functions
(`ex_val`, `ex_lv`, `ex_agg`, `ex_cplx`, `gen_stmt` through statement
expressions, the builtins, the static initializer walk). As in B1, all
growable state is global, and the compiler found the cycle members one by
one:

```
gen_ir.goose:317: error: recursive call cycle through emit, which is not declared `recursive fn` (§7.8)
gen_abi.goose:264: error: recursive call cycle through is_promotable, which is not declared `recursive fn` (§7.8)
gen_stmt.goose:698: error: const_init_global calls into its recursive cycle while non-fixed-size local nm (declared at gen_stmt.goose:684) is in scope (§7.8): end its scope before the call
```

The first was a real design point: `emit` starts a block when there is no
insertion point, `start_block` falls through with `br`, and `br` calls
`emit`. Starting the dead block inline in `emit` broke the cycle instead
of making the hottest function recursive. The third is fixed with a block
`{ var nm ...; g = new_global(nm, ...); }` that ends the name's scope
before the recursive call.

The aliasing checker refused a slice parameter held across a recursive
call, because some function deep in the cycle clears a global buffer:

```
gen_builtin.goose:995: error: cannot call ex_val, which shrinks err_out while name is still used: it may hold a reference or slice into it (§5.1)
```

`name` was a builtin's name (a slice of the identifier arena), and the
callee chain reaches `error_at`, which clears the diagnostic buffer. The
checker cannot tell the two apart through a parameter of a recursive
function. The atomic builtins now decode their name into integer codes
before the first call into the cycle (`atomic_code`), which is also
faster than comparing strings after every operand.

### Typing papercuts

- `match` over named constants yields `i64`, so its result cannot be
  passed to a `u32` parameter:
  `error: no matching overload for call to ins_fcmp ... argument 1: cannot pass i64 as u32`.
  The emission helpers take `op: i64` now.
- `if c { 0xFFFFFFFFFFFFFFFF } else { 0 }`:
  `error: branches have mismatched types: u64 vs i64` (the literal above
  i64.max is `u64`, the `0` is not); written `0 as u64`.
- `0x40 | (if w { 8 } else { 0 })` passed as a byte:
  `error: expected a value of type u8, got i64 (narrowing and sign changes require an explicit `as`)`.
- A local that shadows a function: `let br, bi = ...` followed by
  `br(cont)` gives `error: br is a variable, not a function` (clear,
  but `br` is a common name for both a branch and a real part).
- `dictionary.get` returns an optional, which does not convert where a
  value is expected: `error: no matching overload for call to op_blk ...
  cannot pass u32? as u32`; small `case_block` / `label_block` helpers
  unwrap it.
- Cast and `if` precedence: `(off as! u64 & 0xFFFFFFFF)` gives
  `error: expected ')' in parenthesized expression, found '0xFFFFFFFF'`,
  `nd.c as i64..n_el` gives `error: variable mode (..) applies only to ADT
  type names` (B1 met this one), and
  `(if byte { 0xB0 } else { 0xB8 } + r)` gives
  `error: expected ')' in parenthesized expression, found '+'`. Each needs
  parentheses around the cast or the `if`.

### Front-end bugs that only code generation could find

The B1 oracles compare tokens, types and AST shapes, not values. Running
the programs found these (all fixed in the front end):

- wide string literals stored one byte per ASCII character instead of
  `width` bytes (`L"foo"`);
- wide character constants did not decode UTF-8 (`L'Ä'` was 0x84);
- `-0.0` folded to `+0.0` (`0.0 - f` instead of `-f` in `fold_float`);
- `case` values of `__int128` switches were folded to 64 bits (and so
  reported as duplicates);
- the size expression of a VLA parameter (`int a[n++]`) was dropped by
  the parameter adjustment; it is now kept for the lowering;
- floating-point literals were converted through `double` (now the
  lowering converts the spelling with `strtof`/`strtod`/`strtold`).

### What went well

- The whole lowering type-checked after about 30 error fixes, and the
  first program ran correctly on the first build; 37 of the 44 `tests/c`
  programs and 1,349 of the 1,427 torture tests passed with the first
  binary.
- Bounds checks again turned lowering bugs into exact `file:line` aborts
  (a slice of a wide string's bytes, a flexible array member written past
  its object) instead of corrupt objects.
- Whole-program compilation means the back-end is just more functions:
  no ABI between the two halves, no copies of the tables, one binary.

### Performance

The lowering is 7% of the time of `goosecc -c` over CTMark and 19% on
sqlite3.c, which has much code and few headers (README.md, "Speed of
`goosecc -c`"); its profile has no single hot spot. What helped: a table
from C type kind to GIR type in `vty` (it is called for nearly every
node), debug locations that cost nothing without `-g` (each emitter is
a wrapper that goes straight to the real function unless `-g` is on) and
little with it (a cache of the last source offset and of the last macro
range: `set_loc_dbg` went from 13% to 3% of a `-g` run), constant
conditions decided without materializing an `i1`,
operand fixups recorded at emission so that `fn_finish` is a single pass,
and interning the struct types of two-part ABI values once. What remains
is the cost of the data-stack model: about 15% of a run is page faults and
the kernel, spread over the many growable arrays touched for the first
time.

## 10. Milestone B3: speed

B3 made `goosecc -c` faster than TinyCC over the CTMark C files
(README.md, "Speed (B3)"; DESIGN.md, section 9, has each change with its
numbers). The work was guided by callgrind (instruction counts per
generated C line: the `goose --standalone` output compiles with `-g`, so
each line of the profile maps to a line of Goose), `perf record -e
cpu-clock` (the VM exposes no hardware counters) and micro-benchmarks of
the machine itself. What the Goose side of it was like:

### What the memory model costs at run time

- **A region per global array.** Every global `T[>..]`, `T[>..<]` and
  dictionary is a data stack: a reserved region set up at start-up with
  `mmap`, `mprotect` (the guard gap) and `madvise` (no huge page for its
  first 2 MB). At B2's end goosecc had 227 regions. The profile of a
  one-line file is mostly the kernel's maple tree inserting and splitting
  those mappings, and the exit unmapping them. B3 brought it to 182
  (`goose check --stacks`: `main program: 6 data stacks + 176 global
  stacks = 182 regions`) by turning scratch globals into locals,
  parallel arrays into arrays of structs, and several dictionaries into
  one keyed by `table << 32 | key`. Grouping arrays in a struct is not
  allowed:

  ```
  t3.goose:1: error: resizable field a of struct Tables must be the final field; use root struct for independently stored fields
  ```

  and a root struct's fields are independent stacks again.
- **Locals are stacks too.** A function-local `T[>..]` lives on one of
  the runtime data stacks, whose number is the deepest simultaneous
  nesting of such locals over the call graph (`goose check --stacks`
  lists it per function). Moving the option scratch buffers from globals
  into `main` raised the runtime stacks from 7 to 8 (one more region);
  moving them into a function of their own (`options()`) brought it to 6.
- **Page faults.** A region commits its pages as they are first touched.
  In this VM a first touch costs 1.2 µs per 4 KB page including the
  unmap at exit (a C micro-benchmark); `MADV_POPULATE_WRITE` over 64 KB
  at a time costs 0.68 µs, and a transparent huge page 0.18 µs per 4 KB.
  A typical CTMark compile touches 700-1,500 pages, sqlite3.c 6,000.
  goosecc now populates the big tables (tokens, AST, symbols, GIR, source
  text) ahead of their growth through a C helper that reads the data
  stack's top pointer (`gs_rref`'s `stk->top`), which works but depends on
  the runtime's layout. Huge pages for the large tables (`MADV_HUGEPAGE`
  past their first megabyte) cut sqlite3.c's faults from 6,155 to 4,323
  but did not change its time, and were left out.
- **Clearing a dictionary walks its capacity.** The per-function map of
  labels and `case` blocks was cleared for each of sqlite3.c's 1,900
  functions; `clear` visits every slot, so a map that once grew large
  costs its whole capacity per function. It is now cleared only when it
  has entries.
- **Division by a value known only at run time** goes through a magic
  number that the generated code computes before the loop, bit by bit
  (`gs_divu_gen`): an integer literal's overflow check (`v > (2^64 - 1 -
  d) / base`) ran 60 iterations per literal. The front end now checks
  with a multiplication (`mul_add_overflows`). The back-end has the same
  pattern in `gir_codegen`, `layout_globals`, `write_elf` and `const_mem`
  (reported to A2; B3 does not modify `backend-goose/`).
- **Struct copies.** `let c = ctxs[ci]` copies the 81-byte context; the
  hot paths read fields (`ctxs[ci].kind`) instead.

### Getting at the machine

- **SIMD.** std's `find_any` with a `byte_set` is the only vector code
  Goose offers (16 bytes at a time with SSE2); it replaced the C
  library's `memchr` for comments and line tables. Scanning an identifier
  and hashing it 8 bytes at a time needed C (`goosecc_ident_scan` in
  `goosecc_rt.h`), and its result is two values, which an extern function
  cannot return:

  ```
  t2.goose:1: error: extern fn scan2 returns at most one value
  ```

  so the length and the hash come back packed in a `u64`.
- **Bounds checks in scanning loops.** `while cc[src[q]] & CC_IDCONT !=
  0 { q++; }` keeps its check on `src[q]` (q is unbounded): a compare
  and a branch per byte. The C helpers check once per 16 bytes.
- **Reading a file into a growable array** without a copy needed C as
  well (`goosecc_read_file` reads straight to the top of the array's data
  stack and moves the top and the length, as `goose.h` allows C to do).
  os's `file_exists` + `read_file` make 7 system calls per header (stat,
  fopen, fstat, 64 KB freads, fclose); the helper makes 4.
- **Parsing papercut**: a cast applied to a `match` (or `if`) expression
  needs parentheses or a `let`:

  ```
  t1.goose:5: error: expected ';' in variable declaration, found 'as'
      var j = match c { 'a' => 1, 'b' => 2, _ => 0 } as i64 + name.len;
  ```

### What I would want from the compiler and the runtime

1. **One reservation for all regions** (or a region reserved on its
   first push): 182 regions cost 546 system calls and as many VMA
   operations at start-up and again at exit, a large part of a one-line
   compile's 1.4 ms.
2. **No `MADV_NOHUGEPAGE` when THP is not `always`**: under `madvise`
   (as here) it changes nothing but costs a system call and a VMA split
   per region.
3. **Commit pages in larger steps** as a data stack grows
   (`MADV_POPULATE_WRITE` of 64 KB or more on growth), which halves the
   cost per page.
4. **`dictionary.clear` proportional to the entries**, not the capacity.
5. **Division by a loop-invariant run-time value**: compute the magic
   number with `clz` (a few instructions) or divide in hardware when the
   loop is short.
6. **Several results from an `extern fn`** (a C struct return would do).
7. **Unaligned `u64` loads from a `u8` slice** (and a fast path in
   `find_any` for sets given as byte ranges), so that identifier scanning
   and word-wise hashing could stay in Goose.
8. **Casts and binary operators after `match` / `if` expressions.**

## 11. Milestone B4: the header cache

B4 added `hcache.goose` (2,400 lines with comments), 200 lines of hooks
and changes in the preprocessor, and 450 lines of C in `goosecc_rt.h` (file system,
checksums, the mapped blob's accessors, token relocation). Most of the
Goose type-checked at its first compile; the work went into the design
(DESIGN.md, section 10) and into measuring. What the language and its
runtime were like for it:

### The evaluation order of an index

The only bug that reached a run:

```
goose runtime error: index 0 out of bounds (length 0) (src/hcache.goose:501)
    let ps = wits[wit_stat(p)].state;
```

`wit_stat` appends to `wits` and returns the new entry's index; the
array's length is read *before* the index expression is evaluated, so
the check sees the old length. A ten-line program shows it
(`let x = w[grow()];` with `grow` pushing to `w`). The bounds check
turned it into an exact message instead of a wrong read, but the
reading order is not what the source suggests; `let i = wit_stat(p);
let ps = wits[i].state;` is the fix.

### Slices do not cross `extern fn`

A blob is mapped rather than read into a fresh array (a page fault per
4 KB of a new array cost 0.2 ms per compile). Goose cannot look at the
mapping as a slice:

```
t2.goose:4: error: extern fn mapped cannot return const u32[:]: nested references and slices do not cross
```

so Goose reads it a word at a time through `extern fn mw(i: i64) ->
u32`, which clang inlines into the loops (the generated C and
`goosecc_rt.h` are one translation unit), and the reading code checks
every index against the mapping's length itself (`m32`, `mstr`): the
bounds checks that Goose would have done for a slice, written by hand.
The token arrays, the hottest part, are relocated by a C loop writing
`Tok` records straight into the arrays (`goosecc_reloc_toks`), which
depends on the packed layout of spec C.2; a `_Static_assert` on the
generated `Tok_g` guards it.

### State that hooks must reach

The recording hooks are called from inside the preprocessor's recursive
cycle (`pp_lex` and the directive handlers), where no function may own
growable data across a call into the cycle (section 1), and a struct
cannot hold several growable arrays (section 10). So every recording's
state is global: one array of events for all the nested recordings,
each event tagged with its recording's depth, compacted when a recording
ends (`rec_pop`); per identifier and per file the serials of the
recordings that have seen them, in arrays beside `idents` and in
`FileRec`. The discipline is the one of section 1, and as there nothing
checks it.

### Every global array is a region

The cache needs about twenty buffers of its own (the event list, the
recording stack, the manifests read, the blob being written, maps,
scratch strings), and each global array is a reserved region set up at
every start: the regions went from 291 to 314, about 30 µs of every run,
whether the cache is used or not. Merging them would mean putting
unrelated buffers in one array with offsets, the aliasing hazards of
section 1 again.

### Other notes

- `dictionary.get` returns an optional that an `if` unwraps in its body;
  the postfix `!` some languages use is a parse error (`expected ';' in
  assignment statement, found '!'`).
- `a.append(a[0..2])`, appending a slice of an array to itself, is
  accepted and works (a data stack never moves), which the
  specification does not say; the cache avoids it.
- A push through a `u32[>..]&` parameter stores the data stack's top
  and the length back at every element (backend-goose/NOTES.md, 5.6):
  the serialization of tokens, which took the output array as a
  parameter, now pushes to the global directly.
- Measuring the cache meant measuring the machine: the cost of a page
  fault (1.2 µs) against a page-cache mapping (36 µs per MB), of a stat
  (0.4 µs), of creating a file on `ext4` (inode allocation was a quarter
  of a cold compile), of `madvise(MADV_NOHUGEPAGE)` per region (0.27 ms
  per run, dropped in `build.sh`: section 10's wish 2, done from outside
  the runtime by a header forced in first that undefines the macro the
  runtime tests).

### What went well

- `--pp-state-hash=v` (a checksum of each array the later phases read)
  made exactness a number to compare: the first replay produced the same
  state as preprocessing on the first try, and every later change was
  checked against all 2,357 corpus files in a minute.
- Flat arrays of small structs with integer references are easy to
  serialize and relocate: an effect is a few array suffixes plus base
  offsets.
- Whole-program compilation made the hooks free when no recording is
  active: a test of a global bool next to a load the code does anyway.
