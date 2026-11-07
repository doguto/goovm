// goosecc: shared definitions. Tokens, the source arena, identifiers,
// files and diagnostics. Everything that lives for the whole translation
// unit is a global grow-only array: each owns a data stack, and functions
// of the recursive parser and preprocessor may push into them freely
// (spec §7.8: storage owned outside the cycle).

import std;
import os;

// ---------------------------------------------------------------------------
// Token kinds. Punctuators each have their own kind; keywords are
// identifiers at the preprocessor level (Ident.kw gives the keyword).

let TK_EOF = 0;          // end of the translation unit / of a pre-expanded argument
let TK_EOD = 1;          // end of a directive line
let TK_IDENT = 2;        // val = ident id
let TK_NUMBER = 3;       // pp-number; val = spelling length
let TK_CHAR = 4;         // character constant (with prefix); val = length
let TK_STRING = 5;       // string literal (with prefix); val = length
let TK_HEADER = 6;       // <...> header name in #include; val = length
let TK_OTHER = 7;        // a stray character; val = length
let TK_PARAM = 8;        // macro body: parameter use; aux = parameter index, val = ident
let TK_HASHHASH_NP = 9;  // a ## that came from an argument: prints as ##, never pastes
let TK_CTX_END = 10;     // internal: a token context ran out
let TK_ANNOT_PACK = 11;  // #pragma pack: val = new max field alignment (0 = default)
let TK_COMMENT = 12;     // internal
let TK_ANNOT_MSSTRUCT = 13; // #pragma ms_struct: val = 1 on, 0 off

let TK_L_SQUARE = 20;
let TK_R_SQUARE = 21;
let TK_L_PAREN = 22;
let TK_R_PAREN = 23;
let TK_L_BRACE = 24;
let TK_R_BRACE = 25;
let TK_PERIOD = 26;
let TK_ELLIPSIS = 27;
let TK_AMP = 28;
let TK_AMPAMP = 29;
let TK_AMPEQUAL = 30;
let TK_STAR = 31;
let TK_STAREQUAL = 32;
let TK_PLUS = 33;
let TK_PLUSPLUS = 34;
let TK_PLUSEQUAL = 35;
let TK_MINUS = 36;
let TK_ARROW = 37;
let TK_MINUSMINUS = 38;
let TK_MINUSEQUAL = 39;
let TK_TILDE = 40;
let TK_EXCLAIM = 41;
let TK_EXCLAIMEQUAL = 42;
let TK_SLASH = 43;
let TK_SLASHEQUAL = 44;
let TK_PERCENT = 45;
let TK_PERCENTEQUAL = 46;
let TK_LESS = 47;
let TK_LESSLESS = 48;
let TK_LESSEQUAL = 49;
let TK_LESSLESSEQUAL = 50;
let TK_GREATER = 51;
let TK_GREATERGREATER = 52;
let TK_GREATEREQUAL = 53;
let TK_GREATERGREATEREQUAL = 54;
let TK_CARET = 55;
let TK_CARETEQUAL = 56;
let TK_PIPE = 57;
let TK_PIPEPIPE = 58;
let TK_PIPEEQUAL = 59;
let TK_QUESTION = 60;
let TK_COLON = 61;
let TK_SEMI = 62;
let TK_EQUAL = 63;
let TK_EQUALEQUAL = 64;
let TK_COMMA = 65;
let TK_HASH = 66;
let TK_HASHHASH = 67;
let TK_NUM_KINDS = 68;

// Spellings of the punctuators, indexed by kind - TK_L_SQUARE.
let PUNCT_SPELL = ["[", "]", "(", ")", "{", "}", ".", "...", "&", "&&", "&=", "*", "*=",
    "+", "++", "+=", "-", "->", "--", "-=", "~", "!", "!=", "/", "/=", "%", "%=",
    "<", "<<", "<=", "<<=", ">", ">>", ">=", ">>=", "^", "^=", "|", "||", "|=",
    "?", ":", ";", "=", "==", ",", "#", "##"];

// Token flags.
let F_LSPACE = 1;     // whitespace before the token
let F_BOL = 2;        // first token on its line
let F_NOEXP = 4;      // names a macro that may never expand here (painted blue)
let F_MACRO = 8;      // produced by a macro expansion
let F_DIGRAPH = 16;   // punctuator spelled as a digraph
let F_SYSHDR = 32;    // lexed from a system header
let F_EMPTYMAC = 64;  // an empty macro expansion preceded it (clang LeadingEmptyMacro)

struct Tok {
    kind: u8,
    flags: u8,
    aux: u16,     // TK_PARAM: parameter index
    spell: u32,   // offset of the spelling in `src`
    val: u32,     // ident id, or spelling length
    xloc: u32,    // location for __LINE__ and diagnostics: the file offset of the
                  // end of the outermost macro expansion (= spell for file tokens)
}

// Function-like macro invocations whose name is a file token, as (name
// offset << 32 | ')' offset): the expansion ranges of -g's locations.
var mx_ranges: u64[>..] = [];

// The translation unit's tokens (-fsyntax-only); keywords already have
// their TK_KW kinds. #pragma pack and ms_struct take effect from token
// index pack_changes[2k] / ms_changes[2k] on (value at 2k + 1).
var tu_toks: Tok[>..] = [];

// The pages after the top of a growing array are committed ahead in 64 KB
// steps (goosecc_rt.h): the token, node, symbol and GIR instruction arrays
// call it when they pass their frontier.
extern fn prefault_toks(a: Tok[>..]&, bytes: i64) = "goosecc_prefault";
var tok_frontier: i64 = 0;
var pack_changes: u32[>..] = [];
var ms_changes: u32[>..] = [];

fn is_punct(k: i64) -> bool { k >= TK_L_SQUARE && k < TK_NUM_KINDS }

// ---------------------------------------------------------------------------
// The source arena: every file's text, followed by a NUL, plus scratch
// spellings made by the preprocessor (pasting, stringizing, __LINE__ ...).
var src: u8[>..] = [];

fn src_add(s: const u8[:]) -> u32 {
    let off = src.len;
    src.append(s);
    return off as! u32;
}

// Text that is not source: paths, file names. Separate from src so that a
// slice of it can be held while src grows (and vice versa).
var names: u8[>..] = [];

fn name_add(s: const u8[:]) -> u32 {
    let off = names.len;
    names.append(s);
    return off as! u32;
}

// ---------------------------------------------------------------------------
// Identifiers.
struct Ident {
    off: u32,       // spelling in src
    len: u32,
    hash: u32,
    macro: i32,     // current macro definition, or -1
    kw: u16,        // C keyword code (0 = none), set by the parser's tables
    ppkw: u8,       // directive keyword code
    flags: u8,      // ID_*
}
let ID_POISONED = 1;
let ID_BUILTIN = 2;     // a builtin function name the parser knows (__builtin_va_arg ...)

var idents: Ident[>..] = [];
var idtab: u32[>..<] = [];    // open addressing: ident id + 1, 0 = empty
var idmask: i64 = 0;

// The identifier hash, 8 bytes at a time (goosecc_rt.h; tools/gen_tables.py
// computes the same for the static tables).
extern fn hash_bytes(s: const u8[:]) -> u32 = "goosecc_hash";
// The run of identifier characters (CC_IDCONT) at s[p..]: its length << 32
// | its hash_bytes, 16 bytes at a time.
extern fn ident_scan(s: const u8[:], p: i64) -> u64 = "goosecc_ident_scan";
// The first i >= p with s[i] one of \n / " ' \ NUL, or s.len.
extern fn skip_text(s: const u8[:], p: i64) -> i64 = "goosecc_skip_text";

fn ident_grow() {
    let n = if idtab.len == 0 { 4096 } else { idtab.len * 2 };
    idtab.clear();
    idtab.resize(n, 0);
    idmask = n - 1;
    for d, i in idents {
        var p = (d.hash as i64) & idmask;
        while idtab[p] != 0 { p = (p + 1) & idmask; }
        idtab[p] = (i + 1) as! u32;
    }
}

// The header cache (hcache.goose) records what a header's preprocessing
// reads and writes: rec_on while any recording is active, rec_cur the
// serial of the innermost one. The hooks (hk_*) are cheap tests of rec_on
// at the places that read or write state the cache must know about.
var rec_on: bool = false;
var rec_cur: u32 = 0;
var hk_notexist: u8 = 0;    // intern is creating the identifier it looks up

// The id of the identifier spelled src[off..off+len] (hash h), or -1: the
// probe of ident_lookup, inlined into the lexer's loop.
inline fn ident_find(off: i64, len: i64, h: u32) -> i64 {
    var p = (h as i64) & idmask;
    loop {
        let e = idtab[p] as i64;
        if e == 0 { return -1; }
        if idents[e - 1].hash == h && idents[e - 1].len == len {
            let o = idents[e - 1].off as i64;
            if src[o..o + len] == src[off..off + len] { return e - 1; }
        }
        p = (p + 1) & idmask;
    }
}

// Interns the spelling src[off..off+len] with hash h. The table exists
// (pp_init_tables interns the empty spelling first); it grows only when a
// new identifier is added.
fn ident_lookup(off: i64, len: i64, h: u32) -> u32 {
    var p = (h as i64) & idmask;
    loop {
        let e = idtab[p] as i64;
        if e == 0 { break; }
        if idents[e - 1].hash == h && idents[e - 1].len == len {
            let o = idents[e - 1].off as i64;
            if src[o..o + len] == src[off..off + len] {
                if rec_on { hk_look((e - 1) as! u32, off); }
                return (e - 1) as! u32;
            }
        }
        p = (p + 1) & idmask;
    }
    let id = ident_add(off, len, h, p);
    if rec_on { hk_look(id, off); }
    return id;
}

// Adds the identifier spelled src[off..off+len] (hash h), which is not in
// the table; p is the empty slot its probe ended at.
fn ident_add(off: i64, len: i64, h: u32, p0: i64) -> u32 {
    var p = p0;
    if (idents.len + 1) * 2 > idtab.len {
        ident_grow();
        p = (h as i64) & idmask;
        while idtab[p] != 0 { p = (p + 1) & idmask; }
    }
    let id = idents.len;
    idents.push(Ident { off: off as! u32, len: len as! u32, hash: h, macro: -1, kw: 0, ppkw: 0, flags: 0 });
    idtab[p] = (id + 1) as! u32;
    return id as! u32;
}

fn intern(s: const u8[:]) -> u32 {
    let h = hash_bytes(s);
    // Look up first, so that a known spelling does not grow src.
    if (idents.len + 1) * 2 > idtab.len { ident_grow(); }
    var p = (h as i64) & idmask;
    loop {
        let e = idtab[p];
        if e == 0 { break; }
        let d = idents[e - 1];
        if d.hash == h && d.len == s.len {
            if src[d.off..d.off + d.len] == s {
                if rec_on { hk_exist(e - 1); }
                return e - 1;
            }
        }
        p = (p + 1) & idmask;
    }
    let off = src_add(s);
    src.push(0);
    // a new identifier grows src: the cache must know it was not there
    hk_notexist = 1;
    let id = ident_lookup(off, s.len, h);
    hk_notexist = 0;
    return id;
}

fn ident_text(id: i64) -> const u8[:] {
    let d = idents[id];
    return src[d.off..d.off + d.len];
}

// Whether v * base + d (d < base, base 2, 8, 10 or 16) exceeds 2^64 - 1:
// v > (2^64 - 1 - d) / base, without the division. Goose divides by a
// value it does not know as a constant through a magic number that it
// computes before the loop, bit by bit: 60 iterations per literal.
fn mul_add_overflows(v: u64, base: u64, d: u64) -> bool {
    var lim: u64 = 1844674407370955160;
    if base == 16 { lim = 1152921504606846975; }
    else if base == 8 { lim = 2305843009213693951; }
    else if base == 2 { lim = 9223372036854775807; }
    else if d <= 5 { lim = 1844674407370955161; }
    return v > lim;
}

// The entry of `name` (h = its hash_bytes) in one of the hash tables of
// tables_gen.goose, which index `text` (of length tlen when they were
// generated): its index, or -1. An entry's name is its line up to `sep`
// or the end of the line.
fn tbl_find(text: const u8[:], offs: const u32[:], ht: const u16[:], tlen: i64, name: const u8[:], h: u32, sep: u8) -> i64 {
    if text.len != tlen { fatal("tables_gen.goose does not match its tables: run tools/gen_tables.py"); }
    let mask = ht.len - 1;
    var p = (h as i64) & mask;
    loop {
        let e = ht[p] as i64;
        if e == 0 { return -1; }
        let o = offs[e - 1] as i64;
        let q = o + name.len;
        if q <= text.len && text[o..q] == name && (q == text.len || text[q] == sep || text[q] == '\n') { return e - 1; }
        p = (p + 1) & mask;
    }
}

// ---------------------------------------------------------------------------
// Files. A file's text is loaded once into src; `start..end` is its range
// (a NUL follows at `end`).
struct FileRec {
    path: u32, path_len: u32,     // normalized path (in names), the cache key
    start: u32, end: u32,
    grd: i32,                   // include-guard macro ident, -1 none known
    once: bool,                   // #pragma once seen
    system: bool,                 // #pragma GCC system_header seen
    lines_first: i32,             // index into line_starts, -1 = not built yet
    lines_count: i32,
    sp_off: u32, sp_len: u32,     // the spelling it was first included by (names), the
                                  // presumed file name of diagnostics; 0 = not included yet
    // B4: the file's identity when it was read (stat), for the header cache
    dev: u64, ino: u64, fsize: u64, mtime: i64, ctime: i64,
    rt: u32, rw: u32,             // header cache: serials of the recordings that read / wrote its state
}
var files: FileRec[>..] = [];
var line_starts: u32[>..] = [];

fn file_text(f: i64) -> const u8[:] { src[files[f].start..files[f].end] }

fn build_lines(f: i64) {
    let first = line_starts.len;
    let s = files[f].start as i64;
    let e = files[f].end as i64;
    line_starts.push(s as! u32);
    var p = s;
    loop {
        let q = find_byte(src[p..e], '\n');
        if q < 0 { break; }
        p = p + q + 1;
        line_starts.push(p as! u32);
    }
    files[f].lines_first = first as! i32;
    files[f].lines_count = (line_starts.len - first) as! i32;
}

// The index of the first c in s, or -1: std's find_any, which scans 16
// bytes at a time (with SSE2), whatever the C library's memchr does.
let BS_NL = byte_set("\n");
let BS_SLASH = byte_set("/");
let BS_STAR = byte_set("*");
fn find_byte(s: const u8[:], c: u8) -> i64 {
    if c == '\n' { return find_any(s, BS_NL); }
    if c == '/' { return find_any(s, BS_SLASH); }
    if c == '*' { return find_any(s, BS_STAR); }
    for x, i in s { if x == c { return i; } }
    return -1;
}

// The file holding source offset `off`, or -1 (scratch text).
var last_file_hit: i64 = 0;
fn file_of(off: i64) -> i64 {
    if last_file_hit < files.len {
        let r = files[last_file_hit];
        if off >= r.start && off <= r.end { return last_file_hit; }
    }
    for r, i in files {
        if off >= r.start && off <= r.end { last_file_hit = i; return i; }
    }
    return -1;
}

// 1-based line and column of offset `off` in file f.
// Lookups come mostly in increasing order within a file (the -E printer),
// so the last hit is remembered and searched forward from first.
var lc_file: i64 = -1;
var lc_idx: i64 = 0;

fn line_col(f: i64, off: i64) -> i64, i64 {
    if files[f].lines_first < 0 { build_lines(f); }
    let first = files[f].lines_first as i64;
    let n = files[f].lines_count as i64;
    if f == lc_file && lc_idx < n && line_starts[first + lc_idx] <= off {
        var i = lc_idx;
        var steps = 0;
        while i + 1 < n && line_starts[first + i + 1] <= off && steps < 64 { i++; steps++; }
        if i + 1 >= n || line_starts[first + i + 1] > off {
            lc_idx = i;
            return i + 1, off - line_starts[first + i] + 1;
        }
    }
    var lo = 0;
    var hi = n;    // invariant: line_starts[first+lo] <= off
    while hi - lo > 1 {
        let mid = (lo + hi) / 2;
        if line_starts[first + mid] <= off { lo = mid; } else { hi = mid; }
    }
    lc_file = f;
    lc_idx = lo;
    return lo + 1, off - line_starts[first + lo] + 1;
}

// ---------------------------------------------------------------------------
// Diagnostics.
var n_errors: i64 = 0;
var n_warnings: i64 = 0;
var quiet_warnings: bool = true;

fn loc_prefix(out: u8[>..]&, loc: i64) {
    let f = file_of(loc);
    if f < 0 { out.append("<scratch>: "); return; }
    let line, col = line_col(f, loc);
    if f < files.len {
        let o = files[f].sp_off as i64;
        out.append(names[o..o + files[f].sp_len]);
    } else {
        let o = files[f].path as i64;
        out.append(names[o..o + files[f].path_len]);
    }
    format(out, ":", line, ":", col, ": ");
}

var diag_suppress: i64 = 0;
var diag_suppressed_errors: i64 = 0;

fn error_at(loc: i64, msg: const u8[:]) {
    if rec_on { hk_bad(HC_BAD_DIAG); }
    if diag_suppress > 0 { diag_suppressed_errors++; return; }
    var err_out: u8[>..] = [];
    loc_prefix(err_out, loc);
    err_out.append("error: ");
    err_out.append(msg);
    err_out.push('\n');
    write_stderr(err_out);
    n_errors++;
    if n_errors >= 50 { write_stderr("fatal error: too many errors emitted, stopping now\n"); exit(1); }
}

fn warn_at(loc: i64, msg: const u8[:]) {
    if rec_on { hk_bad(HC_BAD_DIAG); }
    if diag_suppress > 0 { return; }
    n_warnings++;
    if quiet_warnings { return; }
    var err_out: u8[>..] = [];
    loc_prefix(err_out, loc);
    err_out.append("warning: ");
    err_out.append(msg);
    err_out.push('\n');
    write_stderr(err_out);
}

fn fatal(msg: const u8[:]) {
    write_stderr(str("goosecc: fatal error: ", msg, "\n"));
    exit(1);
}
