# goosecc: notes on writing a C front end in Goose

goosecc is about 10,000 lines of Goose (compiler commit 335fddc, runtime
d22ae129d92b), compiled with `goose --standalone` to one 2.5 MB C file and
then with `clang-20 -O2` (about 10 s for both). This page records what was
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

Four things needed C, through `extern fn` and `--include src/goosecc_rt.h`:
reinterpreting f64 bits in both directions (floating literals and constant
folding), rounding a double to float, and `memchr` (line comments, block
comments and line tables are scanned with it: glibc's is vectorized, a byte
loop is not). The extern mechanism is simple and worked the first time.

## 7. Performance notes

What the profiles led to: the lexer hashes an identifier while scanning it
and interns it without a second pass; comments are skipped with `memchr`
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
