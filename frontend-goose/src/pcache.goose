// The parse cache (G1, ../DESIGN.md section 12): the parser's state after
// the translation unit's leading includes, saved once and replayed by
// later compiles that start with the same includes.
//
// A translation unit nearly always begins with a run of #include lines
// (with directives between them, but no tokens of the main file's own):
// its *prefix*. Preprocessing makes the prefix's tokens [0, t1) before
// the parser starts, and the parser's state at token t1, at file scope,
// is a function of those tokens, the text and identifiers they refer to,
// the options, and the state the parser starts from (types_init and
// parse_init, which run before preprocessing for that reason). The key of
// an entry (the *chain*) covers all of that: the configuration and
// options, the built-in text, the identifiers that exist before the first
// include, and per include its identity (the header cache's blob id when
// the include was replayed or recorded as a unit: the blob determines its
// tokens and text; else a checksum of its tokens and text) and what the
// main file's directives added between the includes. Two compiles with
// the same chain have the same tokens [0, t1) with the same identifiers,
// up to where the main file's text ends: everything after it (the
// built-in text, the headers) is shifted by the difference of the main
// files' lengths. The entry is the state at t1 as a delta from the
// starting state; a replay applies it with source offsets relocated, so
// the tables are byte for byte those a fresh parse would leave (the
// identifiers need no relocation: the chain makes them equal).
//
// Not cached: a prefix that reaches into the main file's text (a token
// spelled there: a macro the main file defined expanded inside a header),
// a parse of the prefix with a diagnostic, one that looked past t1 or did
// not end at file scope exactly at t1, state that refers to identifiers or
// text the main file added. The parser may lex builtin signatures while
// it parses the prefix (builtin_type: tokens and text appended after the
// translation unit's): the entry lists them, and a replay lexes them
// again, in order, before it applies the delta.

import std;
import dictionary;
import .common;
import .lex;
import .types;
import .ast;
import .sema;
import .parse;
import .builtins;
import .builtins_gen;
import .dtype;
import .hcache;

let PT_MAGIC = 0x50484347;      // "GCHP"
let PT_VERSION = 1;

// ---------------------------------------------------------------------------
// The main file's includes (preprocessing).

struct PtInc { t0: u32, t1: u32, s0: u32, s1: u32, i0: u32, i1: u32, bid: u64, done: bool }
var pt_incs: PtInc[>..] = [];
var pt_track: bool = false;     // following them: not -E, the cache on
var pt_open: bool = true;       // no token of the main file's own yet
var pt_b0: i64 = 0;             // the built-in text in src (pp_start)
var pt_bend: i64 = 0;
var hc_top_bid: u64 = 0;        // the blob id of the include just replayed or saved (hcache)

// An #include in the main file begins (do_include, after the directive).
fn pt_inc_begin() {
    if !pt_open { return; }
    var prev: i64 = 0;
    if pt_incs.len > 0 {
        let l = pt_incs[pt_incs.len - 1];
        if !l.done {
            pt_open = false;
            return;
        }
        prev = l.t1 as i64;
    }
    if tu_toks.len != prev {
        // tokens of the main file's own: the prefix ended before them
        pt_open = false;
        return;
    }
    pt_incs.push(PtInc { t0: tu_toks.len as! u32, t1: 0, s0: src.len as! u32, s1: 0, i0: idents.len as! u32, i1: 0, bid: 0, done: false });
    hc_top_bid = 0;
}

// It ended: replayed (bid), or its file was popped, or it did nothing.
fn pt_inc_end(bid: u64) {
    if !pt_open || pt_incs.len == 0 { return; }
    let k = pt_incs.len - 1;
    if pt_incs[k].done { return; }
    pt_incs[k].t1 = tu_toks.len as! u32;
    pt_incs[k].s1 = src.len as! u32;
    pt_incs[k].i1 = idents.len as! u32;
    pt_incs[k].bid = bid;
    pt_incs[k].done = true;
}

// ---------------------------------------------------------------------------
// The chain.

fn pt_mix(h: u64, x: u64) -> u64 {
    var v = (h ^ x) * 0x9e3779b97f4a7c15;
    v ^= v >> 29;
    return v * 0xbf58476d1ce4e5b9;
}

extern fn pc_toks(t: Tok[>..]&, from: i64, to: i64, b0: i64, check: i64) -> u64 = "goosecc_pc_toks";

// A checksum of the spellings of identifiers [a, b), with their keyword codes.
fn pt_idents_sum(a: i64, b: i64) -> u64 {
    hcs.clear();
    for i in a..b {
        let d = idents[i];
        hcs.append(src[d.off..d.off + d.len]);
        hcs.push(0);
        hcs.push((d.kw & 255) as! u8);
    }
    return csum_bytes(hcs);
}

var pt_t1: i64 = -1;            // the end of the prefix (its token count)
var pt_s1: i64 = 0;             // src.len and idents.len there
var pt_i1: i64 = 0;
var pt_spp: i64 = 0;            // src.len when parsing began
var pt_key: u64 = 0;

// The chain of the prefix; false when there is none or it cannot be cached.
fn pt_chain() -> bool {
    var n = 0;
    while n < pt_incs.len && pt_incs[n].done { n++; }
    if n == 0 { return false; }
    let last = pt_incs[n - 1];
    if last.t1 == 0 || last.t1 as i64 >= tu_toks.len { return false; }
    // no token of the prefix spelled in the main file's text
    if pc_toks(tu_toks, 0, last.t1 as i64, pt_b0, 1) == 0 { return false; }
    hcs.clear();
    format(hcs, "goosecc parse cache ", PT_VERSION, " ");
    hexd(hcs, build_id(), 16);
    format(hcs, " mode ", opt_mode_pt, " dbg ", bit(dbg_types), bit(dbg_g), " ");
    hcs.append(hcb[hc_cfg_off..hc_cfg_off + hc_cfg_len]);
    hcs.push(1);
    hcs.append(pt_opts);
    var h = csum_bytes(hcs);
    // the built-in text and what was added before the first include, the
    // identifiers that existed then
    let f = pt_incs[0];
    h = pt_mix(h, csum_bytes(src[pt_b0..f.s0 as i64]));
    h = pt_mix(h, pt_idents_sum(0, f.i0 as i64));
    h = pt_mix(h, (f.s0 as i64 - pt_b0) as! u64);
    for k in n {
        let c = pt_incs[k];
        if k > 0 {
            let p = pt_incs[k - 1];
            // what the main file's directives added between the includes
            h = pt_mix(h, csum_bytes(src[(p.s1 as i64)..(c.s0 as i64)]));
            h = pt_mix(h, pt_idents_sum(p.i1 as i64, c.i0 as i64));
        }
        h = pt_mix(h, ((c.t1 - c.t0) as u64) | (((c.s1 - c.s0) as u64) << 32));
        if c.bid != 0 {
            h = pt_mix(h, c.bid);
        } else {
            let th = pc_toks(tu_toks, c.t0 as i64, c.t1 as i64, pt_b0, 0);
            if th == 0 { return false; }
            h = pt_mix(h, th);
            h = pt_mix(h, csum_bytes(src[(c.s0 as i64)..(c.s1 as i64)]));
            h = pt_mix(h, pt_idents_sum(c.i0 as i64, c.i1 as i64));
        }
    }
    pt_key = pt_mix(h, n as u64);
    pt_t1 = last.t1 as i64;
    pt_s1 = last.s1 as i64;
    pt_i1 = last.i1 as i64;
    return true;
}

var opt_mode_pt: i64 = 0;       // main.goose: the mode and the options the key holds
var pt_opts: u8[>..] = [];

// ---------------------------------------------------------------------------
// The tables.

// The parser's tables, in the entry's order (PT_*), with their record
// sizes, the byte offsets of their source offsets (-1: none) and of an
// identifier (-1: none).
let PT_TYPES = 0;
let PT_TPARAMS = 1;
let PT_RECORDS = 2;
let PT_FIELDS = 3;
let PT_ENUMS = 4;
let PT_NODES = 5;
let PT_NLIST = 6;
let PT_STRS = 7;
let PT_STRBYTES = 8;
let PT_SYMS = 9;
let PT_SYMATTRS = 10;
let PT_LATE = 11;
let PT_DTYPES = 12;
let PT_DPARAMS = 13;
let PT_SYMDTY = 14;
let PT_FLDDTY = 15;
let PT_RECFN = 16;
let PT_ENUMFN = 17;
let PT_ENUMC0 = 18;
let PT_ENUMCN = 19;
let PT_ENUMCSYMS = 20;
let PT_RECINREC = 21;
let PT_ENUMINREC = 22;
let PT_SCOPELOG = 23;          // limited arrays: set in place after a resize
let PT_NSCRATCH = 24;
let PT_TYHASH = 25;
let PT_DHASH = 26;
let PT_NTABLES = 27;

fn pt_rs(t: i64) -> i64 {
    return match t {
        PT_TYPES => 40, PT_RECORDS => 48, PT_FIELDS => 40, PT_ENUMS => 24, PT_NODES => 32, PT_STRS => 12,
        PT_STRBYTES => 1, PT_SYMS => 46, PT_SYMATTRS => 42, PT_DTYPES => 32, _ => 4,
    };
}
fn pt_o1(t: i64) -> i64 {
    return match t { PT_RECORDS => 40, PT_FIELDS => 36, PT_ENUMS => 16, PT_NODES => 20, PT_SYMS => 38, _ => -1 };
}
// AST nodes (kv -2): per kind, which of a, b, c (0, 1, 2) hold source offsets
fn pt_kv(t: i64) -> i64 { if t == PT_NODES { return -2; } return -1; }
fn pt_ko(t: i64) -> i64 { return -1; }
extern fn pc_nodeloc(kind: i64, field: i64) = "goosecc_pc_nodeloc";
fn pt_nodelocs() {
    pc_nodeloc(N_FLOAT, 1);       // the spelling
    pc_nodeloc(N_COMPOUND, 1);    // the '}'
    pc_nodeloc(N_DECL, 2);        // the declaration's first token
}
fn pt_io(t: i64) -> i64 {
    return match t { PT_RECORDS => 0, PT_FIELDS => 0, PT_ENUMS => 0, PT_SYMS => 6, _ => -1 };
}

extern fn pc_reloc(b0: i64, st1: i64, spp: i64, d1: i64, d2: i64, imax: i64) = "goosecc_pc_reloc";
extern fn put_types(o: u32[>..]&, a: Type[>..]&, f: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_put";
extern fn put_records(o: u32[>..]&, a: Record[>..]&, f: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_put";
extern fn put_fields(o: u32[>..]&, a: Field[>..]&, f: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_put";
extern fn put_enums(o: u32[>..]&, a: EnumRec[>..]&, f: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_put";
extern fn put_nodes(o: u32[>..]&, a: Node[>..]&, f: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_put";
extern fn put_strs(o: u32[>..]&, a: StrLit[>..]&, f: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_put";
extern fn put_u8(o: u32[>..]&, a: u8[>..]&, f: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_put";
extern fn put_syms(o: u32[>..]&, a: Sym[>..]&, f: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_put";
extern fn put_symattrs(o: u32[>..]&, a: SymAttr[>..]&, f: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_put";
extern fn put_dtypes(o: u32[>..]&, a: DType[>..]&, f: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_put";
extern fn put_u32(o: u32[>..]&, a: u32[>..]&, f: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_put";
extern fn put_i32(o: u32[>..]&, a: i32[>..]&, f: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_put";
// limited arrays do not cross to C by reference; their slices do
extern fn puts_u32(o: u32[>..]&, a: const u32[:], f: i64, n: i64) -> i64 = "goosecc_pc_puts_u32";
extern fn puts_i32(o: u32[>..]&, a: const i32[:], f: i64, n: i64) -> i64 = "goosecc_pc_puts_i32";

extern fn diff_types(o: u32[>..]&, a: Type[>..]&, n: i64, rs: i64, w: const u32[:], wi: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_diff";
extern fn diff_records(o: u32[>..]&, a: Record[>..]&, n: i64, rs: i64, w: const u32[:], wi: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_diff";
extern fn diff_fields(o: u32[>..]&, a: Field[>..]&, n: i64, rs: i64, w: const u32[:], wi: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_diff";
extern fn diff_enums(o: u32[>..]&, a: EnumRec[>..]&, n: i64, rs: i64, w: const u32[:], wi: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_diff";
extern fn diff_nodes(o: u32[>..]&, a: Node[>..]&, n: i64, rs: i64, w: const u32[:], wi: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_diff";
extern fn diff_strs(o: u32[>..]&, a: StrLit[>..]&, n: i64, rs: i64, w: const u32[:], wi: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_diff";
extern fn diff_u8(o: u32[>..]&, a: u8[>..]&, n: i64, rs: i64, w: const u32[:], wi: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_diff";
extern fn diff_syms(o: u32[>..]&, a: Sym[>..]&, n: i64, rs: i64, w: const u32[:], wi: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_diff";
extern fn diff_symattrs(o: u32[>..]&, a: SymAttr[>..]&, n: i64, rs: i64, w: const u32[:], wi: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_diff";
extern fn diff_dtypes(o: u32[>..]&, a: DType[>..]&, n: i64, rs: i64, w: const u32[:], wi: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_diff";
extern fn diff_u32(o: u32[>..]&, a: u32[>..]&, n: i64, rs: i64, w: const u32[:], wi: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_diff";
extern fn diff_i32(o: u32[>..]&, a: i32[>..]&, n: i64, rs: i64, w: const u32[:], wi: i64, o1: i64, o2: i64, kv: i64, ko: i64, io: i64) -> i64 = "goosecc_pc_diff";
extern fn diffs_u32(o: u32[>..]&, a: const u32[:], n: i64, w: const u32[:], wi: i64) -> i64 = "goosecc_pc_diffs_u32";
extern fn diffs_i32(o: u32[>..]&, a: const i32[:], n: i64, w: const u32[:], wi: i64) -> i64 = "goosecc_pc_diffs_i32";

extern fn copy_types(a: Type[>..]&, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_copy";
extern fn copy_records(a: Record[>..]&, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_copy";
extern fn copy_fields(a: Field[>..]&, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_copy";
extern fn copy_enums(a: EnumRec[>..]&, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_copy";
extern fn copy_nodes(a: Node[>..]&, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_copy";
extern fn copy_strs(a: StrLit[>..]&, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_copy";
extern fn copy_u8(a: u8[>..]&, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_copy";
extern fn copy_syms(a: Sym[>..]&, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_copy";
extern fn copy_symattrs(a: SymAttr[>..]&, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_copy";
extern fn copy_dtypes(a: DType[>..]&, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_copy";
extern fn copy_u32(a: u32[>..]&, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_copy";
extern fn copy_i32(a: i32[>..]&, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_copy";

extern fn set_types(a: Type[>..]&, at: i64, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_set";
extern fn set_records(a: Record[>..]&, at: i64, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_set";
extern fn set_fields(a: Field[>..]&, at: i64, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_set";
extern fn set_enums(a: EnumRec[>..]&, at: i64, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_set";
extern fn set_nodes(a: Node[>..]&, at: i64, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_set";
extern fn set_strs(a: StrLit[>..]&, at: i64, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_set";
extern fn set_u8(a: u8[>..]&, at: i64, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_set";
extern fn set_syms(a: Sym[>..]&, at: i64, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_set";
extern fn set_symattrs(a: SymAttr[>..]&, at: i64, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_set";
extern fn set_dtypes(a: DType[>..]&, at: i64, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_set";
extern fn set_u32(a: u32[>..]&, at: i64, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_set";
extern fn set_i32(a: i32[>..]&, at: i64, i: i64, n: i64, rs: i64, o1: i64, o2: i64, kv: i64, ko: i64) -> i64 = "goosecc_pc_set";
extern fn fill_u32(a: u32[:], at: i64, i: i64, n: i64) -> i64 = "goosecc_pc_fill_u32";
extern fn fill_i32(a: i32[:], at: i64, i: i64, n: i64) -> i64 = "goosecc_pc_fill_i32";

fn pt_len(t: i64) -> i64 {
    return match t {
        PT_TYPES => types.len, PT_TPARAMS => tparams.len, PT_RECORDS => records.len, PT_FIELDS => fields.len,
        PT_ENUMS => enums.len, PT_NODES => nodes.len, PT_NLIST => nlist.len, PT_STRS => strs.len,
        PT_STRBYTES => strbytes.len, PT_SYMS => syms.len, PT_SYMATTRS => sym_attrs.len, PT_LATE => late_file_syms.len,
        PT_DTYPES => dtypes.len, PT_DPARAMS => dparams.len, PT_SYMDTY => sym_dty.len, PT_FLDDTY => fld_dty.len,
        PT_RECFN => rec_fn.len, PT_ENUMFN => enum_fn.len, PT_ENUMC0 => enum_c0.len, PT_ENUMCN => enum_cn.len,
        PT_ENUMCSYMS => enum_csyms.len, PT_RECINREC => rec_in_rec.len, PT_ENUMINREC => enum_in_rec.len,
        PT_SCOPELOG => scope_log.len, PT_NSCRATCH => nscratch.len, PT_TYHASH => tyhash.len, _ => dhash.len,
    };
}

// Appends records [f, f + n) of table t to o, checked: 1, or 0.
fn pt_put(o: u32[>..]&, t: i64, f: i64, n: i64) -> i64 {
    let rs = pt_rs(t);
    let o1 = pt_o1(t);
    let kv = pt_kv(t);
    let ko = pt_ko(t);
    let io = pt_io(t);
    return match t {
        PT_TYPES => put_types(o, types, f, n, rs, o1, -1, kv, ko, io),
        PT_TPARAMS => put_u32(o, tparams, f, n, rs, o1, -1, kv, ko, io),
        PT_RECORDS => put_records(o, records, f, n, rs, o1, -1, kv, ko, io),
        PT_FIELDS => put_fields(o, fields, f, n, rs, o1, -1, kv, ko, io),
        PT_ENUMS => put_enums(o, enums, f, n, rs, o1, -1, kv, ko, io),
        PT_NODES => put_nodes(o, nodes, f, n, rs, o1, -1, kv, ko, io),
        PT_NLIST => put_u32(o, nlist, f, n, rs, o1, -1, kv, ko, io),
        PT_STRS => put_strs(o, strs, f, n, rs, o1, -1, kv, ko, io),
        PT_STRBYTES => put_u8(o, strbytes, f, n, rs, o1, -1, kv, ko, io),
        PT_SYMS => put_syms(o, syms, f, n, rs, o1, -1, kv, ko, io),
        PT_SYMATTRS => put_symattrs(o, sym_attrs, f, n, rs, o1, -1, kv, ko, io),
        PT_LATE => put_u32(o, late_file_syms, f, n, rs, o1, -1, kv, ko, io),
        PT_DTYPES => put_dtypes(o, dtypes, f, n, rs, o1, -1, kv, ko, io),
        PT_DPARAMS => put_u32(o, dparams, f, n, rs, o1, -1, kv, ko, io),
        PT_SYMDTY => put_u32(o, sym_dty, f, n, rs, o1, -1, kv, ko, io),
        PT_FLDDTY => put_u32(o, fld_dty, f, n, rs, o1, -1, kv, ko, io),
        PT_RECFN => put_i32(o, rec_fn, f, n, rs, o1, -1, kv, ko, io),
        PT_ENUMFN => put_i32(o, enum_fn, f, n, rs, o1, -1, kv, ko, io),
        PT_ENUMC0 => put_u32(o, enum_c0, f, n, rs, o1, -1, kv, ko, io),
        PT_ENUMCN => put_u32(o, enum_cn, f, n, rs, o1, -1, kv, ko, io),
        PT_ENUMCSYMS => put_u32(o, enum_csyms, f, n, rs, o1, -1, kv, ko, io),
        PT_RECINREC => put_i32(o, rec_in_rec, f, n, rs, o1, -1, kv, ko, io),
        PT_ENUMINREC => put_i32(o, enum_in_rec, f, n, rs, o1, -1, kv, ko, io),
        PT_SCOPELOG => puts_u32(o, scope_log, f, n),
        PT_NSCRATCH => puts_u32(o, nscratch, f, n),
        PT_TYHASH => puts_i32(o, tyhash, f, n),
        _ => puts_i32(o, dhash, f, n),
    };
}

// Appends (index, record) for each record i < n of table t that differs
// from its copy at w[wi..]: their number, or -1.
fn pt_diff(o: u32[>..]&, t: i64, n: i64, w: const u32[:], wi: i64) -> i64 {
    let rs = pt_rs(t);
    let o1 = pt_o1(t);
    let kv = pt_kv(t);
    let ko = pt_ko(t);
    let io = pt_io(t);
    return match t {
        PT_TYPES => diff_types(o, types, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_TPARAMS => diff_u32(o, tparams, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_RECORDS => diff_records(o, records, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_FIELDS => diff_fields(o, fields, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_ENUMS => diff_enums(o, enums, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_NODES => diff_nodes(o, nodes, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_NLIST => diff_u32(o, nlist, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_STRS => diff_strs(o, strs, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_STRBYTES => diff_u8(o, strbytes, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_SYMS => diff_syms(o, syms, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_SYMATTRS => diff_symattrs(o, sym_attrs, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_LATE => diff_u32(o, late_file_syms, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_DTYPES => diff_dtypes(o, dtypes, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_DPARAMS => diff_u32(o, dparams, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_SYMDTY => diff_u32(o, sym_dty, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_FLDDTY => diff_u32(o, fld_dty, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_RECFN => diff_i32(o, rec_fn, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_ENUMFN => diff_i32(o, enum_fn, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_ENUMC0 => diff_u32(o, enum_c0, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_ENUMCN => diff_u32(o, enum_cn, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_ENUMCSYMS => diff_u32(o, enum_csyms, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_RECINREC => diff_i32(o, rec_in_rec, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_ENUMINREC => diff_i32(o, enum_in_rec, n, rs, w, wi, o1, -1, kv, ko, io),
        PT_SCOPELOG => diffs_u32(o, scope_log, n, w, wi),
        PT_NSCRATCH => diffs_u32(o, nscratch, n, w, wi),
        PT_TYHASH => diffs_i32(o, tyhash, n, w, wi),
        _ => diffs_i32(o, dhash, n, w, wi),
    };
}

// Replay: appends n records of table t from word i of the mapping (not for
// the limited arrays). The words read, or -1.
fn pt_copy(t: i64, i: i64, n: i64) -> i64 {
    let rs = pt_rs(t);
    let o1 = pt_o1(t);
    let kv = pt_kv(t);
    let ko = pt_ko(t);
    return match t {
        PT_TYPES => copy_types(types, i, n, rs, o1, -1, kv, ko),
        PT_TPARAMS => copy_u32(tparams, i, n, rs, o1, -1, kv, ko),
        PT_RECORDS => copy_records(records, i, n, rs, o1, -1, kv, ko),
        PT_FIELDS => copy_fields(fields, i, n, rs, o1, -1, kv, ko),
        PT_ENUMS => copy_enums(enums, i, n, rs, o1, -1, kv, ko),
        PT_NODES => copy_nodes(nodes, i, n, rs, o1, -1, kv, ko),
        PT_NLIST => copy_u32(nlist, i, n, rs, o1, -1, kv, ko),
        PT_STRS => copy_strs(strs, i, n, rs, o1, -1, kv, ko),
        PT_STRBYTES => copy_u8(strbytes, i, n, rs, o1, -1, kv, ko),
        PT_SYMS => copy_syms(syms, i, n, rs, o1, -1, kv, ko),
        PT_SYMATTRS => copy_symattrs(sym_attrs, i, n, rs, o1, -1, kv, ko),
        PT_LATE => copy_u32(late_file_syms, i, n, rs, o1, -1, kv, ko),
        PT_DTYPES => copy_dtypes(dtypes, i, n, rs, o1, -1, kv, ko),
        PT_DPARAMS => copy_u32(dparams, i, n, rs, o1, -1, kv, ko),
        PT_SYMDTY => copy_u32(sym_dty, i, n, rs, o1, -1, kv, ko),
        PT_FLDDTY => copy_u32(fld_dty, i, n, rs, o1, -1, kv, ko),
        PT_RECFN => copy_i32(rec_fn, i, n, rs, o1, -1, kv, ko),
        PT_ENUMFN => copy_i32(enum_fn, i, n, rs, o1, -1, kv, ko),
        PT_ENUMC0 => copy_u32(enum_c0, i, n, rs, o1, -1, kv, ko),
        PT_ENUMCN => copy_u32(enum_cn, i, n, rs, o1, -1, kv, ko),
        PT_ENUMCSYMS => copy_u32(enum_csyms, i, n, rs, o1, -1, kv, ko),
        PT_RECINREC => copy_i32(rec_in_rec, i, n, rs, o1, -1, kv, ko),
        PT_ENUMINREC => copy_i32(enum_in_rec, i, n, rs, o1, -1, kv, ko),
        _ => -1,
    };
}

// Replay: overwrites records [at, at + n) of table t (which exist) with n
// records from word i of the mapping. The words read, or -1.
fn pt_set(t: i64, at: i64, i: i64, n: i64) -> i64 {
    let rs = pt_rs(t);
    let o1 = pt_o1(t);
    let kv = pt_kv(t);
    let ko = pt_ko(t);
    return match t {
        PT_TYPES => set_types(types, at, i, n, rs, o1, -1, kv, ko),
        PT_TPARAMS => set_u32(tparams, at, i, n, rs, o1, -1, kv, ko),
        PT_RECORDS => set_records(records, at, i, n, rs, o1, -1, kv, ko),
        PT_FIELDS => set_fields(fields, at, i, n, rs, o1, -1, kv, ko),
        PT_ENUMS => set_enums(enums, at, i, n, rs, o1, -1, kv, ko),
        PT_NODES => set_nodes(nodes, at, i, n, rs, o1, -1, kv, ko),
        PT_NLIST => set_u32(nlist, at, i, n, rs, o1, -1, kv, ko),
        PT_STRS => set_strs(strs, at, i, n, rs, o1, -1, kv, ko),
        PT_STRBYTES => set_u8(strbytes, at, i, n, rs, o1, -1, kv, ko),
        PT_SYMS => set_syms(syms, at, i, n, rs, o1, -1, kv, ko),
        PT_SYMATTRS => set_symattrs(sym_attrs, at, i, n, rs, o1, -1, kv, ko),
        PT_LATE => set_u32(late_file_syms, at, i, n, rs, o1, -1, kv, ko),
        PT_DTYPES => set_dtypes(dtypes, at, i, n, rs, o1, -1, kv, ko),
        PT_DPARAMS => set_u32(dparams, at, i, n, rs, o1, -1, kv, ko),
        PT_SYMDTY => set_u32(sym_dty, at, i, n, rs, o1, -1, kv, ko),
        PT_FLDDTY => set_u32(fld_dty, at, i, n, rs, o1, -1, kv, ko),
        PT_RECFN => set_i32(rec_fn, at, i, n, rs, o1, -1, kv, ko),
        PT_ENUMFN => set_i32(enum_fn, at, i, n, rs, o1, -1, kv, ko),
        PT_ENUMC0 => set_u32(enum_c0, at, i, n, rs, o1, -1, kv, ko),
        PT_ENUMCN => set_u32(enum_cn, at, i, n, rs, o1, -1, kv, ko),
        PT_ENUMCSYMS => set_u32(enum_csyms, at, i, n, rs, o1, -1, kv, ko),
        PT_RECINREC => set_i32(rec_in_rec, at, i, n, rs, o1, -1, kv, ko),
        PT_ENUMINREC => set_i32(enum_in_rec, at, i, n, rs, o1, -1, kv, ko),
        PT_SCOPELOG => fill_u32(scope_log, at, i, n),
        PT_NSCRATCH => fill_u32(nscratch, at, i, n),
        PT_TYHASH => fill_i32(tyhash, at, i, n),
        _ => fill_i32(dhash, at, i, n),
    };
}

// A limited array grown to n (its new entries are overwritten next).
fn pt_grow_limited(t: i64, n: i64) {
    if t == PT_SCOPELOG { scope_log.resize(n, 0); }
    else if t == PT_NSCRATCH { nscratch.resize(n, 0); }
    else if t == PT_TYHASH { tyhash.resize(n, -1); }
    else { dhash.resize(n, -1); }
}

// ---------------------------------------------------------------------------
// Recording.

var pt_rec: bool = false;       // recording the prefix's parse
var pt_peek: i64 = 0;           // the furthest token tk_n looked at (not past pt_eof)
var pt_eof: i64 = 0;            // the translation unit's EOF token
var pt_lex: u32[>..] = [];      // the builtin signatures lexed (builtin_type), in order
var pt_n0: i64[>..] = [];       // per table: its length when parsing began, then where its copy starts in hcr
var pt_id0: i64 = 0;            // id_bind.len then
var pt_err0: i64 = 0;
var pt_warn0: i64 = 0;
var pt_ndict0: i64 = 0;

var st_pt_lookups: i64 = 0;
var st_pt_hits: i64 = 0;
var st_pt_saved: i64 = 0;
var st_pt_bad: i64 = 0;
var tm_pt_replay: i64 = 0;
var tm_pt_save: i64 = 0;
var tm_pt_chain: i64 = 0;

fn pt_dict_count() -> i64 {
    return node_dty.count + enumc_ref.count + tdef_fn.count + fn_proto.count + decl_extern.count + enumc_enum.count +
        local_labels.count + krrefs.count + swapped.count + enum_defloc.count;
}

// When the parse of the translation unit begins (parse_tu): replays the
// prefix's entry if there is one (and returns true: parsing goes on at
// pt_t1), or starts recording it.
fn pt_begin() -> bool {
    if !pt_track || !hc_on || !hc_ready || n_errors > 0 { return false; }
    pt_spp = src.len;
    pt_nodelocs();
    let qc = clock_ns();
    let okc = pt_chain();
    tm_pt_chain += clock_ns() - qc;
    if !okc { return false; }
    st_pt_lookups++;
    let t0 = clock_ns();
    let ok = pt_replay();
    tm_pt_replay += clock_ns() - t0;
    if ok {
        st_pt_hits++;
        return true;
    }
    // recording: the starting state's lengths and copies (unchecked)
    pc_reloc(0, 0x7FFFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFFFF, 0, 0, 0x7FFFFFFFFFFFFFFF);
    hcr.clear();
    pt_n0.clear();
    for t in PT_NTABLES {
        let n = pt_len(t);
        pt_n0.push(n);
        pt_n0.push(hcr.len);
        if pt_put(hcr, t, 0, n) == 0 { return false; }
    }
    pt_id0 = id_bind.len;
    for b in id_bind {
        hcr.push(b.ord as! u32);
        hcr.push(b.tag as! u32);
        hcr.push(b.label as! u32);
    }
    pt_err0 = n_errors;
    pt_warn0 = n_warnings;
    pt_ndict0 = pt_dict_count();
    pt_lex.clear();
    pt_peek = 0;
    pt_eof = tu_toks.len - 1;
    pt_rec = true;
    return false;
}

// parse_tu, at file scope between declarations: the end of the prefix?
fn pt_boundary() {
    if pc < pt_t1 { return; }
    pt_rec = false;
    if pc != pt_t1 || pt_peek >= pt_t1 { st_pt_bad++; return; }
    let t0 = clock_ns();
    if !pt_save() { st_pt_bad++; }
    tm_pt_save += clock_ns() - t0;
}

fn pt_dict_put(o: u32[>..]&, d: dictionary<u64, u32>&, loc: bool) -> bool {
    o.push(d.count as! u32);
    for s in d.slots {
        if s.tag == 0 { continue; }
        w64(o, s.key);
        if loc {
            let v = s.val as i64;
            if v != 0 && !(v >= pt_b0 && v < pt_s1) && v < pt_spp { return false; }
        }
        o.push(s.val);
    }
    return true;
}

// The entry: the state now as a delta from the starting state.
fn pt_save() -> bool {
    if n_errors != pt_err0 || (n_warnings != pt_warn0 && !quiet_warnings) { return false; }
    if scope_depth != 0 || scope_marks.len != 0 || cur_func >= 0 || cur_rec >= 0 || label_syms.len != 0 ||
       switches.len != 0 || loop_depth != 0 || break_depth != 0 || fscratch.len != 0 || ients.len != 0 {
        return false;
    }
    // the dictionaries start empty (pt_dict_put writes them whole)
    if pt_ndict0 != 0 { return false; }
    pc_reloc(pt_b0, pt_s1, pt_spp, 0, 0, pt_i1);
    hcv.clear();
    for i in 5 { hcv.push(0); }
    w64(hcv, pt_key);
    hcv.push(pt_t1 as! u32);
    hcv.push(pt_i1 as! u32);
    hcv.push((pt_s1 - pt_b0) as! u32);
    hcv.push(pt_b0 as! u32);
    hcv.push(pt_s1 as! u32);
    hcv.push(pt_spp as! u32);
    hcv.push(pt_lex.len as! u32);
    for b in pt_lex { hcv.push(b); }
    w64(hcv, func_gen as! u64);
    hcv.push((n_warnings - pt_warn0) as! u32);
    hcv.push(PT_NTABLES as! u32);
    for t in PT_NTABLES {
        let n0 = pt_n0[2 * t];
        let w0 = pt_n0[2 * t + 1];
        let n1 = pt_len(t);
        if n1 < n0 { return false; }
        hcv.push(n0 as! u32);
        let pn = hcv.len;
        hcv.push(0);
        let np = pt_diff(hcv, t, n0, hcr, w0);
        if np < 0 { return false; }
        hcv[pn] = np as! u32;
        hcv.push((n1 - n0) as! u32);
        if pt_put(hcv, t, n0, n1 - n0) == 0 { return false; }
    }
    // id_bind: the bindings that differ from the start (unbound past it);
    // only identifiers of the prefix's
    let pn = hcv.len;
    hcv.push(0);
    var np: i64 = 0;
    for b, i in id_bind {
        var o: u32 = 0xFFFFFFFF;
        var t: u32 = 0xFFFFFFFF;
        var l: u32 = 0xFFFFFFFF;
        if i < pt_id0 {
            o = hcr[hcr.len - 3 * pt_id0 + 3 * i];
            t = hcr[hcr.len - 3 * pt_id0 + 3 * i + 1];
            l = hcr[hcr.len - 3 * pt_id0 + 3 * i + 2];
        }
        if b.ord as! u32 == o && b.tag as! u32 == t && b.label as! u32 == l { continue; }
        if i >= pt_i1 { return false; }
        hcv.push(i as! u32);
        hcv.push(b.ord as! u32);
        hcv.push(b.tag as! u32);
        hcv.push(b.label as! u32);
        np++;
    }
    hcv[pn] = np as! u32;
    // the written types' dictionaries (-g, __PRETTY_FUNCTION__)
    if !pt_dict_put(hcv, node_dty, false) || !pt_dict_put(hcv, enumc_ref, false) || !pt_dict_put(hcv, tdef_fn, false) ||
       !pt_dict_put(hcv, fn_proto, false) || !pt_dict_put(hcv, decl_extern, false) || !pt_dict_put(hcv, enumc_enum, false) ||
       !pt_dict_put(hcv, local_labels, true) || !pt_dict_put(hcv, krrefs, false) || !pt_dict_put(hcv, swapped, false) ||
       !pt_dict_put(hcv, enum_defloc, true) {
        return false;
    }
    // the builtins typed so far
    hcv.push(bentries.len as! u32);
    let bp = hcv.len;
    hcv.push(0);
    var nb: i64 = 0;
    for e, i in bentries {
        if !e.typed && !e.custom && e.ty == 0 { continue; }
        var fl: u32 = 0;
        if e.typed { fl = fl | 1; }
        if e.custom { fl = fl | 2; }
        hcv.push(i as! u32);
        hcv.push(fl);
        hcv.push(e.ty);
        nb++;
    }
    hcv[bp] = nb as! u32;
    hcv.push(tymask as! u32);
    hcv.push(dmask as! u32);
    hcv[0] = PT_MAGIC;
    hcv[1] = PT_VERSION;
    hcv[2] = hcv.len as! u32;
    let cs = csum_words(hcv[5..hcv.len]);
    hcv[3] = (cs & 0xFFFFFFFF) as! u32;
    hcv[4] = (cs >> 32) as! u32;
    pt_path();
    if write_words(hcp, hcv) == 0 { return false; }
    st_pt_saved++;
    st_wbytes += hcv.len * 4;
    return true;
}

fn pt_path() {
    hcp.clear();
    hcp.append(hcb[hc_dir_off..hc_dir_off + hc_dir_len]);
    hcp.push('/');
    hexd(hcp, pt_key, 16);
    hcp.append(".p");
}

// ---------------------------------------------------------------------------
// Replay.

fn pt_corrupt() -> bool {
    st_corrupt++;
    unlink_path(hcp);
    return false;
}

// An inconsistent entry with a correct checksum is a bug; after the first
// change to the state there is no way back.
fn pt_fail(what: const u8[:]) {
    fatal(str("internal error: parse cache entry ", hcp, ": ", what, " (GOOSECC_CACHE=off compiles without the cache)"));
}

fn pt_dict_get(d: dictionary<u64, u32>&, loc: bool, d1: i64, d2: i64, b0r: i64, st1r: i64) {
    let n = m32() as i64;
    for k in n {
        let key = m64();
        var v = m32();
        if loc && v != 0 {
            if v as i64 >= b0r && (v as i64) < st1r { v = ((v as i64) + d1) as! u32; } else { v = ((v as i64) + d2) as! u32; }
        }
        d.insert(key, v);
    }
}

var tm_pt_a: i64 = 0;
var tm_pt_b: i64 = 0;
var tm_pt_c: i64 = 0;
var tm_pt_d: i64 = 0;
var tm_pt_e: i64 = 0;
fn pt_replay() -> bool {
    let q0 = clock_ns();
    pt_path();
    mlen = map_file(hcp);
    if mlen <= 0 {
        mlen = 0;
        return false;
    }
    if mlen < 20 || mw(0) != PT_MAGIC || mw(1) != PT_VERSION || mw(2) as i64 != mlen { return pt_corrupt(); }
    let q1 = clock_ns();
    tm_pt_a += q1 - q0;
    let cs = mcsum(5, mlen);
    tm_pt_b += clock_ns() - q1;
    if (cs & 0xFFFFFFFF) as! u32 != mw(3) || (cs >> 32) as! u32 != mw(4) { return pt_corrupt(); }
    rp = 5;
    rerr = false;
    if m64() != pt_key { return false; }
    let t1 = m32() as i64;
    let i1 = m32() as i64;
    let s1rel = m32() as i64;
    let b0r = m32() as i64;
    let st1r = m32() as i64;
    let sppr = m32() as i64;
    // what the chain guarantees, checked
    if t1 != pt_t1 || i1 != pt_i1 || s1rel != pt_s1 - pt_b0 || st1r - b0r != s1rel { return false; }
    let nlex = m32() as i64;
    if rerr || nlex > mlen { return pt_corrupt(); }
    // the starting state must be what it was (types_init, parse_init)
    let lexp = rp;
    rp += nlex;
    let fgen = m64() as! i64;
    let wdelta = m32() as i64;
    let nt = m32() as i64;
    if rerr || nt != PT_NTABLES { return pt_corrupt(); }
    // first a pass over the tables' headers: the starting lengths
    let tp = rp;
    for t in nt {
        let n0 = m32() as i64;
        if n0 != pt_len(t) { return false; }
        let np = m32() as i64;
        let w = (pt_rs(t) + 3) / 4 + 1;
        if np > mlen { return pt_corrupt(); }
        rp += np * w;
        let ns = m32() as i64;
        if ns > mlen * 4 { return pt_corrupt(); }
        rp += (ns * pt_rs(t) + 3) / 4;
        if rerr || rp > mlen { return pt_corrupt(); }
    }
    // the builtin signatures the parse lexed, in order
    let q2 = clock_ns();
    rp = lexp;
    for k in nlex {
        let b = m32() as i64;
        if b >= TBL_BUILTIN_TYPES_OFF.len { pt_fail("builtin index"); }
        let ts, te = builtin_text(b);
        let first = lex_string_tokens(BUILTIN_TYPES[ts..te]);
    }
    let q3 = clock_ns();
    tm_pt_c += q3 - q2;
    pc_reloc(b0r, st1r, sppr, pt_b0 - b0r, pt_spp - sppr, 0);
    rp = tp;
    for t in nt {
        let n0 = m32() as i64;
        let np = m32() as i64;
        let w = (pt_rs(t) + 3) / 4;
        let limited = t >= PT_SCOPELOG;
        var pp = rp;
        rp += np * (w + 1);
        let ns = m32() as i64;
        let sp = rp;
        rp += (ns * pt_rs(t) + 3) / 4;
        if limited {
            pt_grow_limited(t, n0 + ns);
            if pt_set(t, n0, sp, ns) < 0 { pt_fail("table"); }
        } else {
            if pt_copy(t, sp, ns) < 0 { pt_fail("table"); }
        }
        for k in np {
            let at = mw(pp) as i64;
            if pt_set(t, at, pp + 1, 1) < 0 { pt_fail("patch"); }
            pp += w + 1;
        }
    }
    let q4 = clock_ns();
    tm_pt_d += q4 - q3;
    ensure_ids();
    let nb = m32() as i64;
    for k in nb {
        let id = m32() as i64;
        let o = m32();
        let tg = m32();
        let l = m32();
        if id >= id_bind.len { pt_fail("binding"); }
        id_bind[id] = IdBind { ord: o as! i32, tag: tg as! i32, label: l as! i32 };
    }
    let d1 = pt_b0 - b0r;
    let d2 = pt_spp - sppr;
    pt_dict_get(node_dty, false, d1, d2, b0r, st1r);
    pt_dict_get(enumc_ref, false, d1, d2, b0r, st1r);
    pt_dict_get(tdef_fn, false, d1, d2, b0r, st1r);
    pt_dict_get(fn_proto, false, d1, d2, b0r, st1r);
    pt_dict_get(decl_extern, false, d1, d2, b0r, st1r);
    pt_dict_get(enumc_enum, false, d1, d2, b0r, st1r);
    pt_dict_get(local_labels, true, d1, d2, b0r, st1r);
    pt_dict_get(krrefs, false, d1, d2, b0r, st1r);
    pt_dict_get(swapped, false, d1, d2, b0r, st1r);
    pt_dict_get(enum_defloc, true, d1, d2, b0r, st1r);
    let blen = m32() as i64;
    let nbe = m32() as i64;
    if blen > 0 && bentries.len == 0 { bentries.resize(blen, BuiltinEnt { typed: false, custom: false, ty: 0 }); }
    for k in nbe {
        let i = m32() as i64;
        let fl = m32();
        let ty = m32();
        if i >= bentries.len { pt_fail("builtin"); }
        bentries[i] = BuiltinEnt { typed: fl & 1 != 0, custom: fl & 2 != 0, ty: ty };
    }
    tymask = m32() as i64;
    dmask = m32() as i64;
    if rerr { pt_fail("truncated"); }
    tm_pt_e += clock_ns() - q4;
    func_gen = fgen;
    n_warnings += wdelta;
    node_frontier = 0;
    sym_frontier = 0;
    pc = pt_t1;
    return true;
}

// ---------------------------------------------------------------------------
// --pp-state-hash: after parsing, a checksum of the parser's state too (the
// tables, the bindings, the dictionaries as sets, the builtins typed, the
// tokens and text the parse appended), to show that a replay leaves what a
// parse leaves. With verbose, one per table.

fn pt_dict_sum(d: dictionary<u64, u32>&) -> u64 {
    var h: u64 = d.count as! u64;
    for s in d.slots {
        if s.tag != 0 { h += pt_mix(s.key, s.val as u64); }
    }
    return h;
}

fn pt_state_hash(verbose: bool) {
    var o: u8[>..] = [];
    var all: u64 = 0;
    pc_reloc(0, 0x7FFFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFFFF, 0, 0, 0x7FFFFFFFFFFFFFFF);
    for t in PT_NTABLES + 4 {
        hcw.clear();
        var c: u64 = 0;
        if t < PT_NTABLES {
            let ok = pt_put(hcw, t, 0, pt_len(t));
            hcw.push(pt_len(t) as! u32);
            c = csum_words(hcw);
        } else if t == PT_NTABLES {
            for i in idents.len {
                if i < id_bind.len {
                    let b = id_bind[i];
                    hcw.push(b.ord as! u32);
                    hcw.push(b.tag as! u32);
                    hcw.push(b.label as! u32);
                } else {
                    hcw.push(0xFFFFFFFF);
                    hcw.push(0xFFFFFFFF);
                    hcw.push(0xFFFFFFFF);
                }
            }
            c = csum_words(hcw);
        } else if t == PT_NTABLES + 1 {
            c = pt_mix(pt_dict_sum(node_dty), pt_dict_sum(enumc_ref));
            c = pt_mix(c, pt_dict_sum(tdef_fn));
            c = pt_mix(c, pt_dict_sum(fn_proto));
            c = pt_mix(c, pt_dict_sum(decl_extern));
            c = pt_mix(c, pt_dict_sum(enumc_enum));
            c = pt_mix(c, pt_dict_sum(local_labels));
            c = pt_mix(c, pt_dict_sum(krrefs));
            c = pt_mix(c, pt_dict_sum(swapped));
            c = pt_mix(c, pt_dict_sum(enum_defloc));
        } else if t == PT_NTABLES + 2 {
            for e in bentries {
                var fl: u32 = 0;
                if e.typed { fl = fl | 1; }
                if e.custom { fl = fl | 2; }
                hcw.push(fl);
                hcw.push(e.ty);
            }
            w64(hcw, func_gen as! u64);
            w64(hcw, tymask as! u64);
            w64(hcw, dmask as! u64);
            w64(hcw, n_errors as! u64);
            w64(hcw, n_warnings as! u64);
            w64(hcw, tu_node as u64);
            c = csum_words(hcw);
        } else {
            for tk in tu_toks {
                hcw.push((tk.kind as u32) | ((tk.flags as u32) << 8) | ((tk.aux as u32) << 16));
                hcw.push(tk.spell);
                hcw.push(tk.val);
                hcw.push(tk.xloc);
            }
            c = pt_mix(csum_words(hcw), csum_bytes(src));
            c = pt_mix(c, idents.len as! u64);
        }
        all = (all ^ c) * 0x9e3779b97f4a7c15;
        if verbose {
            format(o, " t", t, " ");
            hexd(o, c, 16);
        }
    }
    var line: u8[>..] = [];
    line.append("goosecc: parse state ");
    hexd(line, all, 16);
    line.append(o);
    line.push('\n');
    write_stderr(line);
}

// The parse cache's part of --cache-stats.
fn pt_report(o: u8[>..]&) {
    format(o, "; parse cache: ", st_pt_lookups, " lookups, ", st_pt_hits, " hits, ", st_pt_saved, " recorded, ",
        st_pt_bad, " not cacheable; replay ", tm_pt_replay / 1000, " us (map ", tm_pt_a / 1000, ", csum ", tm_pt_b / 1000, ", lex ", tm_pt_c / 1000,
        ", tables ", tm_pt_d / 1000, ", rest ", tm_pt_e / 1000, ", chain ", tm_pt_chain / 1000, "), saving ", tm_pt_save / 1000, " us");
}
