// goosecc: the persistent header cache (milestone B4; DESIGN.md, section 10).
//
// The unit is one #include directive: the search for the file, the file
// and everything it includes, to the end of that file. While a unit is
// preprocessed, a recording notes what it reads of the state it started
// in (the macros it tests or expands before changing them, the paths it
// finds or misses, the files it finds already loaded, #pragma pack,
// __COUNTER__, ...) and, at its end, what it did: everything appended to
// the preprocessor's arrays (source text, names, identifiers, macros and
// their tokens, files, the translation unit's tokens or -E's output, ...)
// and the identifiers and files whose state it changed. That is written
// under the directive's key (the include's spelling, how it searches, the
// configuration). A later #include with the same key replays the effect
// when every observation holds again: each array gets what preprocessing
// would have appended, the identifiers are created in the order their
// first lookups would create them, so the state afterwards is the same
// as without the cache, bit for bit, and so is everything compiled from
// it. Recordings nest (each #include inside a recorded one is a unit of
// its own), and a replay inside a recording reports its observations and
// effects to the recordings around it as if it had been preprocessed.

import std;
import os;
import dictionary;
import .common;
import .lex;
import .pp;
import .ppdir;
import .ppexpr;
import .print;
import .sema;

let HC_VERSION = 1;
let HC_MAGIC_M = 0x4D484347;   // "GCHM", a manifest: the variants recorded under a key
let HC_MAGIC_B = 0x42484347;   // "GCHB", a blob: one variant's identifiers and effect
let HC_MAX_VARIANTS = 48;
let HC_MIN_SRC = 2048;          // smaller units (bytes of text and tokens) are not worth a file
let HC_MIN_TOKS = 64;
let HC_RACY_NS = 2000000000;    // files changed less than 2 s before the compile started are not trusted by their stat

// Why a recording is not saved.
let HC_BAD_DIAG = 1;     // the unit printed a diagnostic
let HC_BAD_TIME = 2;     // __DATE__, __TIME__ or __TIMESTAMP__
let HC_BAD_FILE = 4;     // a file changed less than 2 s ago, or not a regular file
let HC_BAD_MACRO = 8;    // #pragma pop_macro of a macro pushed before the unit
let HC_BAD_STATE = 16;   // what the format cannot express (an inconsistency: a bug)
let HC_BAD_NEST = 32;    // too many nested recordings

// Recording events (Ev.kind).
let EV_LOOK = 1;     // a: identifier, b: offset of its first lookup in the unit; flag 1: intern created it
let EV_MOBS = 2;     // a: identifier, b: its macro (i32) at its first read in the unit
let EV_EXIST = 3;    // a: identifier that intern found (it existed)
let EV_MWRITE = 4;   // a: identifier whose macro the unit set
let EV_POISON = 5;   // a: identifier poisoned
let EV_PNEG = 6;     // a: path key and spelling (hcb), b: their lengths (key | spelling << 16): no file there
let EV_PNEW = 7;     // + c: the file loaded from it
let EV_POLD = 8;     // + c: the file already loaded for it, d: its guard; flag: its state (fstate)
let EV_FWRITE = 9;   // a: a file loaded before the unit whose state the unit changed

struct Ev { rec: u16, kind: u8, flag: u8, a: u32, b: u32, c: u32, d: u32 }

// Per identifier: the serial of the innermost recording that has read its
// macro (m, or written it first), looked it up (l), written its macro (w).
// A recording with a serial <= the value has seen it: the recordings that
// have form an outer part of the stack (B4, DESIGN.md 10.3).
struct ITouch { m: u32, l: u32, w: u32 }

struct Rec {
    serial: u32,
    ctxd: u32,         // ctxs.len while the unit's file is the top file context (0: not entered yet)
    src0: u32, names0: u32, idents0: u32, macros0: u32, mtoks0: u32, files0: u32,
    toks0: u32, mx0: u32, packc0: u32, msc0: u32, out0: u32, paths0: u32, push0: u32, ev0: u32,
    key: u32, key_len: u32, keyh: u64,     // the key (hcb)
    bad: u32,
    depth0: u32, maxd: u32,                // include depth at the start, deepest since
    ctr_t: bool, pack_t: bool, uses_depth: bool, uses_base: bool,
    ctr0: i64,                             // __COUNTER__ before its first use
    pack0: u32,                            // #pragma pack state before its first change (hcb)
    so: u32, sl: u32, sys: u8,             // the unit's file context: spelling (names), system header
}

struct HMan { keyh: u64, off: u32, len: u32 }   // a manifest of this process (hcm), len 0: none
struct LEnt { id: u32, flags: u32, off: u32, def: u32 }
struct HDef { id: u32, m: i32 }
struct HPo { kind: u32, f: i32, e: i32, key: u32, klen: u32, path: u32, plen: u32, nf: u32 }

// The local identifier table's flags (LEnt.flags, a blob's identifiers).
let LF_LOOKED = 1;     // looked up in the unit; off: where it was first
let LF_NOTEXIST = 2;   // intern created it: it must not exist
let LF_OBS = 4;        // its macro was read before the unit changed it: undefined, unless LF_DEF
let LF_DEF = 8;        // observed as the macro of the variant's definition `def`
let LF_EXISTS = 16;    // intern found it: it must exist

// Path observations (a variant's head).
let PO_NEG = 1;
let PO_NEW = 2;
let PO_OLD = 3;

var hc_enabled: bool = true;    // -fno-header-cache clears it
var hc_on: bool = false;        // enabled and a directory to use
var hc_ready: bool = false;
var hc_stats_opt: bool = false; // --cache-stats
var hc_t0: i64 = 0;             // the wall clock at start-up
var hc_limit: i64 = 2147483648; // GOOSECC_CACHE_SIZE
var hc_dir_off: u32 = 0;        // the directory (hcb)
var hc_dir_len: u32 = 0;
var hc_cfg_off: u32 = 0;        // the configuration text (hcb)
var hc_cfg_len: u32 = 0;
var hc_serial: u32 = 0;
var hc_keyh: u64 = 0;           // hash of hck

var hcb: u8[>..] = [];          // grow-only: the directory, the configuration, keys, the paths of path events
var hck: u8[>..] = [];          // the key of the include being looked up
var hcs: u8[>..] = [];          // the strings of a variant's head being checked
var hcp: u8[>..] = [];          // a file name
var hcm: u32[>..] = [];         // grow-only: the manifests read by this process
var hcr: u32[>..] = [];         // a blob being replayed; a manifest being rewritten
var hcw: u32[>..] = [];         // output: a blob's effect; a variant's head
var hcv: u32[>..] = [];         // output: a blob; a manifest
var hcx: u32[>..] = [];         // replay: the identifier map and anchor targets; recording: anchor candidates and anchors
var ev: Ev[>..] = [];
var evown: Ev[>..] = [];
var recs: Rec[>..] = [];
var itouch: ITouch[>..] = [];
var hman: HMan[>..] = [];
var lmap: ITouch[>..] = [];     // recording's end: per identifier, a stamp (m) and its local index (l)
var lent: LEnt[>..] = [];
var hdef: HDef[>..] = [];
var hpo: HPo[>..] = [];
var hcd = dictionary<u64, u32> {};

var st_lookups: i64 = 0;
var st_hits: i64 = 0;
var st_misses: i64 = 0;
var st_recorded: i64 = 0;
var st_small: i64 = 0;
var st_bad: i64 = 0;
var st_corrupt: i64 = 0;
var st_wbytes: i64 = 0;
var st_werr: i64 = 0;
var st_skipped: i64 = 0;
var tm_replay: i64 = 0;    // ns in replays: all, reading, checking, appending, committing; in recordings' ends
var tm_read: i64 = 0;
var tm_check: i64 = 0;
var tm_append: i64 = 0;
var tm_commit: i64 = 0;
var tm_save: i64 = 0;
var tm_man: i64 = 0;
var tm_head: i64 = 0;
var tm_csum: i64 = 0;

extern fn words_eq(w: const u32[:], i: i64, s: const u8[:]) -> i64 = "goosecc_words_eq";
extern fn words_hash(w: const u32[:], i: i64, n: i64) -> u32 = "goosecc_words_hash";
extern fn words_to_bytes(out: u8[>..]&, w: const u32[:], i: i64, n: i64) -> i64 = "goosecc_words_to_bytes";
extern fn bytes_to_words(out: u32[>..]&, s: const u8[:]) = "goosecc_bytes_to_words";
extern fn csum_words(w: const u32[:]) -> u64 = "goosecc_csum";
extern fn csum_bytes(s: const u8[:]) -> u64 = "goosecc_csum_bytes";
extern fn read_words(path: const u8[:], out: u32[>..]&) -> i64 = "goosecc_read_words";
extern fn write_words(path: const u8[:], w: const u32[:]) -> i64 = "goosecc_write_words";
extern fn stat_path(path: const u8[:]) -> i64 = "goosecc_stat";
extern fn unlink_path(path: const u8[:]) = "goosecc_unlink";
extern fn evict_dir(dir: const u8[:], limit: i64) -> i64 = "goosecc_evict";
extern fn build_id() -> u64 = "goosecc_build_id";

// ---------------------------------------------------------------------------
// Start-up.

// After the options: the directory ($GOOSECC_CACHE, else ~/.cache/goosecc;
// GOOSECC_CACHE=off disables) and the size limit ($GOOSECC_CACHE_SIZE,
// with K, M or G).
fn hc_init() {
    hc_t0 = time_ns();
    if !hc_enabled { return; }
    var d: u8[>..] = [];
    if env("GOOSECC_CACHE", d) {
        if d.len == 0 || d == "0" || d == "off" || d == "none" { return; }
    } else {
        if !env("HOME", d) || d.len == 0 { return; }
        d.append("/.cache/goosecc");
    }
    while d.len > 1 && d[d.len - 1] == '/' { d.pop(); }
    d.append("/v1");
    hc_dir_off = hcb.len as! u32;
    hcb.append(d);
    hc_dir_len = d.len as! u32;
    var z: u8[>..] = [];
    if env("GOOSECC_CACHE_SIZE", z) && z.len > 0 {
        var v: i64 = 0;
        var i = 0;
        while i < z.len && z[i] >= '0' && z[i] <= '9' { v = v * 10 + (z[i] - '0'); i++; }
        if i < z.len && (z[i] == 'k' || z[i] == 'K') { v = v * 1024; }
        if i < z.len && (z[i] == 'm' || z[i] == 'M') { v = v * 1048576; }
        if i < z.len && (z[i] == 'g' || z[i] == 'G') { v = v * 1073741824; }
        if v > 0 { hc_limit = v; }
    }
    hc_on = true;
}

fn hexd(out: u8[>..]&, v: u64, n: i64) {
    var k = n - 1;
    while k >= 0 {
        let x = ((v >> ((k * 4) as! u64)) & 15) as! u8;
        if x < 10 { out.push('0' + x); } else { out.push('a' + x - 10); }
        k--;
    }
}

fn bit(b: bool) -> u8 { if b { return '1'; } return '0'; }

// The configuration: what preprocessing depends on besides the
// observations (built at the first include: the keyword table is known
// by then). The predefined macros and -D/-U are not in it: a unit
// observes the macros it reads.
fn hc_prepare() -> bool {
    if hc_ready { return hc_on; }
    hc_ready = true;
    if !hc_on { return false; }
    hc_cfg_off = hcb.len as! u32;
    format(hcb, "goosecc header cache ", HC_VERSION, " build ");
    hexd(hcb, build_id(), 16);
    if mode_E { hcb.append(" -E"); } else { hcb.append(" -c"); }
    hcb.append(" std=");
    hcb.append(opt_std());
    hcb.push(' ');
    hcb.push(bit(opt_gnu)); hcb.push(bit(opt_c99)); hcb.push(bit(opt_std_c11)); hcb.push(bit(opt_c11));
    hcb.push(bit(opt_trigraphs)); hcb.push(bit(opt_kw_inline)); hcb.push(bit(opt_kw_restrict)); hcb.push(bit(opt_kw_gnu));
    hcb.push(bit(tu_annot));
    format(hcb, " dirs ", quote_dirs_end, " ", angle_start, " ", sys_start);
    for dr in dirs {
        hcb.push('\n');
        hcb.append(names[dr.path..dr.path + dr.len]);
        hcb.push(bit(dr.sys));
    }
    hc_cfg_len = (hcb.len - hc_cfg_off) as! u32;
    return true;
}

// The key of an #include of `name` from the current file: the
// configuration, the directive, and what of the includer its search uses.
fn hc_key(name: const u8[:], angled: bool, k: i64) {
    hck.clear();
    hck.append(hcb[hc_cfg_off..hc_cfg_off + hc_cfg_len]);
    hck.push(1);
    if k == PK_INCLUDE_NEXT { hck.push('n'); } else if k == PK_IMPORT { hck.push('m'); } else { hck.push('i'); }
    hck.push(bit(angled));
    let ci = cur_file_ctx;
    hck.push(bit(ctxs[ci].sys != 0));
    hck.push(1);
    hck.append(name);
    hck.push(1);
    if k == PK_INCLUDE_NEXT && ctxs[ci].dir_idx >= 0 {
        format(hck, "d", ctxs[ci].dir_idx);
    } else if !angled {
        hck.push('r');
        let dl = ctx_dir_len(ci);
        if dl >= 0 {
            let s = ctxs[ci].spell as i64;
            hck.append(names[s..s + dl]);
            hck.push('/');
        }
    }
    hc_keyh = csum_bytes(hck);
}

// ---------------------------------------------------------------------------
// The hooks (callers test rec_on first).

fn itouch_fit(id: i64) {
    while itouch.len <= id { itouch.push(ITouch { m: 0, l: 0, w: 0 }); }
}

// An identifier lookup (off: the spelling's offset in src).
fn hk_look(id: u32, off: i64) {
    itouch_fit(id as i64);
    let t = itouch[id].l;
    if t >= rec_cur { return; }
    var r = recs.len - 1;
    while r >= 0 && recs[r].serial > t {
        ev.push(Ev { rec: r as! u16, kind: EV_LOOK, flag: hk_notexist, a: id, b: off as! u32, c: 0, d: 0 });
        r--;
    }
    itouch[id].l = rec_cur;
}

// A read of an identifier's macro.
fn hk_mread(id: u32) {
    itouch_fit(id as i64);
    let t = itouch[id].m;
    if t >= rec_cur { return; }
    let m = idents[id].macro;
    var r = recs.len - 1;
    while r >= 0 && recs[r].serial > t {
        ev.push(Ev { rec: r as! u16, kind: EV_MOBS, flag: 0, a: id, b: m as! u32, c: 0, d: 0 });
        r--;
    }
    itouch[id].m = rec_cur;
}

// A write of an identifier's macro: no recording depends on what it was
// any more, and each must set it at its end.
fn hk_mwrite(id: u32) {
    itouch_fit(id as i64);
    if itouch[id].m < rec_cur { itouch[id].m = rec_cur; }
    let t = itouch[id].w;
    if t >= rec_cur { return; }
    var r = recs.len - 1;
    while r >= 0 && recs[r].serial > t {
        ev.push(Ev { rec: r as! u16, kind: EV_MWRITE, flag: 0, a: id, b: 0, c: 0, d: 0 });
        r--;
    }
    itouch[id].w = rec_cur;
}

// intern found the identifier: it existed (or a lookup in the unit made it).
fn hk_exist(id: i64) {
    itouch_fit(id);
    let t = itouch[id].l;
    if t >= rec_cur { return; }
    var r = recs.len - 1;
    while r >= 0 && recs[r].serial > t {
        ev.push(Ev { rec: r as! u16, kind: EV_EXIST, flag: 0, a: id as! u32, b: 0, c: 0, d: 0 });
        r--;
    }
}

fn hk_poison(id: u32) {
    for r in recs.len { ev.push(Ev { rec: r as! u16, kind: EV_POISON, flag: 0, a: id, b: 0, c: 0, d: 0 }); }
}

fn hk_bad(why: u32) {
    for r in recs.len { recs[r].bad = recs[r].bad | why; }
}

// #pragma pop_macro of push_stack entry j.
fn hk_pop_macro(id: u32, j: i64) {
    for r in recs.len {
        if j < recs[r].push0 as i64 { recs[r].bad = recs[r].bad | HC_BAD_MACRO; }
    }
    hk_mwrite(id);
}

fn hk_push() {
    let d = include_depth() as! u32;
    for r in recs.len { if d > recs[r].maxd { recs[r].maxd = d; } }
}

fn hk_counter() {
    for r in recs.len {
        if !recs[r].ctr_t {
            recs[r].ctr_t = true;
            recs[r].ctr0 = counter_value;
        }
    }
}

fn hcb_put32(v: u32) {
    hcb.push((v & 255) as! u8);
    hcb.push(((v >> 8) & 255) as! u8);
    hcb.push(((v >> 16) & 255) as! u8);
    hcb.push((v >> 24) as! u8);
}
fn hcb_get32(o: i64) -> u32 {
    return (hcb[o] as u32) | ((hcb[o + 1] as u32) << 8) | ((hcb[o + 2] as u32) << 16) | ((hcb[o + 3] as u32) << 24);
}

// #pragma pack or ms_struct is about to change the pack state.
fn hk_pack() {
    for r in recs.len {
        if !recs[r].pack_t {
            recs[r].pack_t = true;
            recs[r].pack0 = hcb.len as! u32;
            hcb_put32(pack_cur);
            hcb_put32(pack_stack.len as! u32);
            for e in pack_stack {
                hcb_put32(e.val);
                hcb_put32(e.label);
            }
        }
    }
}

fn hk_depth() {
    for r in recs.len { recs[r].uses_depth = true; }
}

fn hk_basefile() {
    for r in recs.len { recs[r].uses_base = true; }
}

// The state of a loaded file that an include reads: once, system,
// included before (#import), a guard.
fn fstate(f: i64) -> u8 {
    var s: u8 = 0;
    if files[f].once { s = s | 1; }
    if files[f].system { s = s | 2; }
    if files[f].sp_len != 0 { s = s | 4; }
    if files[f].grd >= 0 { s = s | 8; }
    return s;
}

// Whether a file's stat may not tell a change: changed less than 2 s
// before this compile started, or not a regular file.
fn racy(f: i64) -> bool {
    if files[f].fsize == 0xFFFFFFFFFFFFFFFF { return true; }
    let lim = hc_t0 - HC_RACY_NS;
    return files[f].mtime > lim || files[f].ctime > lim;
}

fn hk_store_path(key: const u8[:], path: const u8[:]) -> u32, u32 {
    let a = hcb.len as! u32;
    hcb.append(key);
    var pl: i64 = 0;
    if path != key {
        hcb.append(path);
        pl = path.len;
    }
    return a, (key.len | (pl << 16)) as! u32;
}

// lookup_file found key in the path cache (entry e): file fe, or -1.
fn hk_path_hit(e: i64, fe: i64, key: const u8[:], path: const u8[:]) {
    var a: u32 = 0;
    var b: u32 = 0;
    var stored = false;
    for r in recs.len {
        if e >= recs[r].paths0 as i64 { continue; }
        if fe >= 0 && files[fe].rt >= recs[r].serial { continue; }
        if !stored {
            a, b = hk_store_path(key, path);
            stored = true;
        }
        if fe < 0 {
            ev.push(Ev { rec: r as! u16, kind: EV_PNEG, flag: 0, a: a, b: b, c: 0, d: 0 });
        } else {
            ev.push(Ev { rec: r as! u16, kind: EV_POLD, flag: fstate(fe), a: a, b: b, c: fe as! u32, d: files[fe].grd as! u32 });
            if racy(fe) { recs[r].bad = recs[r].bad | HC_BAD_FILE; }
        }
    }
    if fe >= 0 && files[fe].rt < rec_cur { files[fe].rt = rec_cur; }
}

// lookup_file did not have key: it loaded file f from the spelling path,
// or there is none (-1).
fn hk_path_miss(key: const u8[:], path: const u8[:], f: i64) {
    let a, b = hk_store_path(key, path);
    var k: u8 = EV_PNEG;
    var fl: u32 = 0;
    if f >= 0 {
        k = EV_PNEW;
        fl = f as! u32;
        if racy(f) { hk_bad(HC_BAD_FILE); }
    }
    for r in recs.len { ev.push(Ev { rec: r as! u16, kind: k, flag: 0, a: a, b: b, c: fl, d: 0 }); }
}

// A write of the state of file f (guard, once, system, its spelling).
fn hk_fwrite(f: i64) {
    for r in recs.len {
        if f < recs[r].files0 as i64 && files[f].rw < recs[r].serial {
            ev.push(Ev { rec: r as! u16, kind: EV_FWRITE, flag: 0, a: f as! u32, b: 0, c: 0, d: 0 });
        }
    }
    if files[f].rw < rec_cur { files[f].rw = rec_cur; }
}

// ---------------------------------------------------------------------------
// Looking an include up.

var wk_f: i64 = -1;

// pbuf holds a path find_include would try: 1 when the path cache says a
// file is there (wk_f), 0 when it says none is, -1 when it does not know.
fn wk_cand() -> i64 {
    var nbuf: u8[>..] = [];
    let normal = path_is_normal(pbuf);
    if !normal { normalize_path(nbuf); }
    var r: i64 = 0;
    if normal { r = path_known(pbuf, hash_bytes(pbuf), 0); } else { r = path_known(nbuf, hash_bytes(nbuf), 0); }
    if r >= 0 { wk_f = r; return 1; }
    if r == -1 { return 0; }
    let dl = pbuf_dir_len();
    if dl > 0 && pathtab.len > 0 && dir_missing(dl) { return 0; }
    return -1;
}

// Whether the path cache alone shows that this include will do nothing:
// it finds a file that is already loaded and #pragma once, guarded by a
// defined macro, or #imported. Such an include is neither looked up nor
// recorded. find_include's search, without touching the file system.
fn hc_would_skip(name: const u8[:], angled: bool, k: i64) -> bool {
    var found = -1;
    if name.len > 0 && name[0] == '/' {
        pbuf.clear();
        pbuf.append(name);
        found = wk_cand();
    } else {
        var start: i64 = if angled { angle_start } else { 0 };
        let ci = cur_file_ctx;
        if k == PK_INCLUDE_NEXT && ctxs[ci].dir_idx >= 0 {
            start = (ctxs[ci].dir_idx as i64) + 1;
        } else if !angled {
            let dl = ctx_dir_len(ci);
            pbuf.clear();
            if dl >= 0 {
                let s = ctxs[ci].spell as i64;
                pbuf.append(names[s..s + dl]);
                pbuf.push('/');
            }
            pbuf.append(name);
            found = wk_cand();
            if found < 0 { return false; }
        }
        var d = start;
        while found != 1 && d < dirs.len {
            let dr = dirs[d];
            pbuf.clear();
            pbuf.append(names[dr.path..dr.path + dr.len]);
            if pbuf.len == 0 || pbuf[pbuf.len - 1] != '/' { pbuf.push('/'); }
            pbuf.append(name);
            found = wk_cand();
            if found < 0 { return false; }
            d++;
        }
    }
    if found != 1 { return false; }
    let f = wk_f;
    if files[f].once { return true; }
    let g = files[f].grd as i64;
    if g >= 0 && idents[g].macro >= 0 { return true; }
    return k == PK_IMPORT && files[f].sp_len != 0;
}

// The cache file of the current key: its manifest (bid 0) or a blob.
fn hc_path(bid: u64, blob: bool) {
    hcp.clear();
    hcp.append(hcb[hc_dir_off..hc_dir_off + hc_dir_len]);
    hcp.push('/');
    hexd(hcp, hc_keyh >> 56, 2);
    hcp.push('/');
    hexd(hcp, hc_keyh, 16);
    if blob {
        hcp.push('-');
        hexd(hcp, bid, 16);
        hcp.append(".b");
    } else {
        hcp.append(".m");
    }
}

// Reading the words of a cache file: rp moves through them, rerr notes
// reading past the end (the reads then give 0).
var rp: i64 = 0;
var rerr: bool = false;

fn r32(w: const u32[:]) -> u32 {
    if rp >= w.len {
        rerr = true;
        return 0;
    }
    let v = w[rp];
    rp++;
    return v;
}
fn r64(w: const u32[:]) -> u64 {
    let lo = r32(w) as u64;
    let hi = r32(w) as u64;
    return lo | (hi << 32);
}
// A string: the index of its first word and its length in bytes.
fn rstr(w: const u32[:]) -> i64, i64 {
    let n = r32(w) as i64;
    let i = rp;
    let nw = (n + 3) / 4;
    if nw > w.len - rp {
        rerr = true;
        rp = w.len;
        return 0, 0;
    }
    rp += nw;
    return i, n;
}
fn str_is(w: const u32[:], i: i64, n: i64, s: const u8[:]) -> bool {
    return n == s.len && words_eq(w, i, s) != 0;
}

fn w64(o: u32[>..]&, v: u64) {
    o.push((v & 0xFFFFFFFF) as! u32);
    o.push((v >> 32) as! u32);
}
fn wstr(o: u32[>..]&, s: const u8[:]) {
    o.push(s.len as! u32);
    bytes_to_words(o, s);
}

// Whether w is a whole cache file of the given kind: magic, version,
// length, checksum.
fn file_ok(w: const u32[:], magic: u32) -> bool {
    if w.len < 5 || w[0] != magic || w[1] != HC_VERSION || w[2] as i64 != w.len { return false; }
    let c = csum_words(w[5..]);
    return (c & 0xFFFFFFFF) as! u32 == w[3] && (c >> 32) as! u32 == w[4];
}

// The manifest of the current key (an index into hman), read at its
// first use in this process.
fn man_get() -> i64 {
    for h, i in hman { if h.keyh == hc_keyh { return i; } }
    hc_path(0, false);
    let off = hcm.len;
    let n = read_words(hcp, hcm);
    var len: i64 = 0;
    if n > 0 {
        var ok = file_ok(hcm[off..off + n], HC_MAGIC_M);
        if !ok { st_corrupt++; unlink_path(hcp); }
        if ok {
            rp = 5;
            rerr = false;
            let ki, kn = rstr(hcm[off..off + n]);
            ok = !rerr && str_is(hcm[off..off + n], ki, kn, hck);
        }
        if ok { len = n; } else { hcm.resize(off); }
    }
    hman.push(HMan { keyh: hc_keyh, off: off as! u32, len: len as! u32 });
    return hman.len - 1;
}

// ---------------------------------------------------------------------------
// Replay.

// The identifier spelled by the n bytes at word i of w (hash h), or -1.
fn ident_find_w(w: const u32[:], i: i64, n: i64, h: u32) -> i64 {
    var p = (h as i64) & idmask;
    loop {
        let e = idtab[p] as i64;
        if e == 0 { return -1; }
        if idents[e - 1].hash == h && idents[e - 1].len as i64 == n {
            let o = idents[e - 1].off as i64;
            if words_eq(w, i, src[o..o + n]) != 0 { return e - 1; }
        }
        p = (p + 1) & idmask;
    }
}

// Adds the identifier spelled src[off..off+len] (hash h), not in the table.
fn ident_new(off: i64, len: i64, h: u32) -> u32 {
    var p = (h as i64) & idmask;
    while idtab[p] != 0 { p = (p + 1) & idmask; }
    return ident_add(off, len, h, p);
}

// The spelling of a token whose kind has one in src (literals, others).
fn spelled(k: i64) -> bool {
    return !is_punct(k) && k != TK_IDENT && k != TK_PARAM && k != TK_EOF && k != TK_EOD && k != TK_HASHHASH_NP;
}

var hm_flags: u32 = 0;     // the variant's head: what it observed besides paths and macros
var hm_maxrel: u32 = 0;

// Checks a variant's head (rp at it) against the current state: its path
// observations (hpo, with their strings copied to hcs), the macros it
// observed defined (hdef), the rest.
fn head_check(w: const u32[:]) -> bool {
    hpo.clear();
    hdef.clear();
    hcs.clear();
    let np = r32(w) as i64;
    for i in np {
        let kw = r32(w);
        let kind = kw & 255;
        let st = kw >> 8;
        let ki, kn = rstr(w);
        let pi, pn = rstr(w);
        if rerr { return false; }
        let ko = hcs.len;
        words_to_bytes(hcs, w, ki, kn);
        var po = ko;
        var pl = kn;
        if pn > 0 {
            po = hcs.len;
            words_to_bytes(hcs, w, pi, pn);
            pl = pn;
        }
        var dev: u64 = 0;
        var ino: u64 = 0;
        var fsize: u64 = 0;
        var mt: i64 = 0;
        var ct: i64 = 0;
        if kind == PO_NEW || kind == PO_OLD {
            dev = r64(w);
            ino = r64(w);
            fsize = r64(w);
            mt = r64(w) as! i64;
            ct = r64(w) as! i64;
        }
        var nf: u32 = 0;
        if kind == PO_NEW { nf = r32(w); }
        var gi: i64 = 0;
        var gn: i64 = 0;
        if kind == PO_OLD && st & 8 != 0 { gi, gn = rstr(w); }
        if rerr { return false; }
        let r = path_known(hcs[ko..ko + kn], hash_bytes(hcs[ko..ko + kn]), 0);
        let e = path_known_e;
        if kind == PO_NEG {
            if r >= 0 { return false; }
            if r == -2 {
                // what lookup_file would find: a directory known not to
                // exist, or no file there
                pbuf.clear();
                pbuf.append(hcs[po..po + pl]);
                let dl = pbuf_dir_len();
                if !(dl > 0 && pathtab.len > 0 && dir_missing(dl)) {
                    let s = stat_path(pbuf);
                    if s != 0 && s != 2 { return false; }
                }
            }
        } else if kind == PO_NEW {
            if r != -2 { return false; }
            pbuf.clear();
            pbuf.append(hcs[po..po + pl]);
            let dl = pbuf_dir_len();
            if dl > 0 && pathtab.len > 0 && dir_missing(dl) { return false; }
            if stat_path(pbuf) != 1 { return false; }
            if last_stat(0) as! u64 != dev || last_stat(1) as! u64 != ino || last_stat(2) as! u64 != fsize ||
                    last_stat(3) != mt || last_stat(4) != ct {
                return false;
            }
        } else if kind == PO_OLD {
            if r < 0 { return false; }
            let fr = files[r];
            if fr.dev != dev || fr.ino != ino || fr.fsize != fsize || fr.mtime != mt || fr.ctime != ct { return false; }
            if racy(r) { return false; }
            if fstate(r) as u32 != (st & 15) { return false; }
            if st & 8 != 0 && !str_is(w, gi, gn, ident_text(fr.grd as i64)) { return false; }
        } else {
            return false;
        }
        var fi: i64 = -1;
        if kind == PO_OLD { fi = r; }
        hpo.push(HPo { kind: kind, f: fi as! i32, e: e as! i32, key: ko as! u32, klen: kn as! u32, path: po as! u32, plen: pl as! u32, nf: nf });
    }
    // the macros observed defined, with their definitions
    let nd = r32(w) as i64;
    for j in nd {
        let si, sn = rstr(w);
        let h = r32(w);
        let mf = r32(w);
        let cnt = r32(w);
        if rerr { return false; }
        let id = ident_find_w(w, si, sn, h);
        if id < 0 { return false; }
        let m = idents[id].macro as i64;
        if m < 0 { return false; }
        let mc = macros[m];
        if mc.flags as u32 != (mf & 255) || mc.builtin as u32 != ((mf >> 8) & 255) || mc.nparams as u32 != (mf >> 16) || mc.count != cnt {
            return false;
        }
        for t in cnt as i64 {
            let tw = r32(w);
            let tk = mtoks[(mc.first as i64) + t];
            if (tk.kind as u32) | ((tk.flags as u32) << 8) | ((tk.aux as u32) << 16) != tw { return false; }
            let k = tk.kind as i64;
            if k == TK_IDENT || k == TK_PARAM {
                let ti, tn = rstr(w);
                if rerr || !str_is(w, ti, tn, ident_text(tk.val as i64)) { return false; }
            } else if spelled(k) {
                let ti, tn = rstr(w);
                if rerr || !str_is(w, ti, tn, src[tk.spell..tk.spell + tk.val]) { return false; }
            }
        }
        hdef.push(HDef { id: id as! u32, m: m as! i32 });
    }
    hm_flags = r32(w);
    if hm_flags & 1 != 0 {
        if r64(w) as! i64 != counter_value { return false; }
    }
    if hm_flags & 2 != 0 {
        let cur = r32(w);
        let n = r32(w) as i64;
        if rerr || cur != pack_cur || n != pack_stack.len { return false; }
        for i in n {
            let v = r32(w);
            let li, ln = rstr(w);
            if rerr || v != pack_stack[i].val { return false; }
            let lab = pack_stack[i].label;
            if (ln == 0) != (lab == 0) { return false; }
            if lab != 0 && !str_is(w, li, ln, ident_text((lab - 1) as i64)) { return false; }
        }
    }
    if hm_flags & 4 != 0 {
        if r32(w) as i64 != include_depth() { return false; }
    }
    if hm_flags & 8 != 0 {
        let bi, bn = rstr(w);
        if rerr || !str_is(w, bi, bn, names[base_file_name..base_file_name + base_file_name_len]) { return false; }
    }
    hm_maxrel = r32(w);
    if include_depth() + (hm_maxrel as i64) > 200 { return false; }
    return !rerr;
}

// The include whose key is in hck: replays the first variant whose
// observations all hold. True when one did.
fn hc_replay(name: const u8[:], angled: bool, k: i64) -> bool {
    if !hc_prepare() { return false; }
    let t0 = clock_ns();
    let r = hc_replay1(name, angled, k);
    tm_replay += clock_ns() - t0;
    return r;
}

fn hc_replay1(name: const u8[:], angled: bool, k: i64) -> bool {
    hc_key(name, angled, k);
    st_lookups++;
    let tm0 = clock_ns();
    let mi = man_get();
    tm_man += clock_ns() - tm0;
    let mo = hman[mi].off as i64;
    let ml = hman[mi].len as i64;
    if ml == 0 {
        st_misses++;
        return false;
    }
    rp = 5;
    rerr = false;
    let ki, kn = rstr(hcm[mo..mo + ml]);
    let nv = r32(hcm[mo..mo + ml]) as i64;
    for vi in nv {
        let vlen = r32(hcm[mo..mo + ml]) as i64;
        let vstart = rp;
        let bid = r64(hcm[mo..mo + ml]);
        if rerr { break; }
        let th0 = clock_ns();
        let hok = head_check(hcm[mo..mo + ml]);
        tm_head += clock_ns() - th0;
        if hok {
            if blob_replay(bid) {
                st_hits++;
                return true;
            }
        }
        rp = vstart + vlen;
        rerr = false;
    }
    st_misses++;
    return false;
}

// A blob being replayed is mapped (goosecc_rt.h): mlen words, read with
// mw(i) after checking i against mlen.
extern fn map_file(path: const u8[:]) -> i64 = "goosecc_map";
extern fn mw(i: i64) -> u32 = "goosecc_mw";
extern fn mcsum(from: i64, to: i64) -> u64 = "goosecc_mcsum";
extern fn mcopy(out: u8[>..]&, i: i64, n: i64) = "goosecc_mcopy";
extern fn meq(i: i64, s: const u8[:]) -> i64 = "goosecc_meq";
extern fn reloc_toks(out: Tok[>..]&, i: i64, n: i64, ids: const u32[:], anchors: const u32[:], s0: i64, srclen: i64, kwmin: i64) -> i64 = "goosecc_reloc_toks";
var mlen: i64 = 0;

fn m32() -> u32 {
    if rp >= mlen {
        rerr = true;
        return 0;
    }
    let v = mw(rp);
    rp++;
    return v;
}
fn m64() -> u64 {
    let lo = m32() as u64;
    let hi = m32() as u64;
    return lo | (hi << 32);
}
fn mstr() -> i64, i64 {
    let n = m32() as i64;
    let i = rp;
    let nw = (n + 3) / 4;
    if nw > mlen - rp {
        rerr = true;
        rp = mlen;
        return 0, 0;
    }
    rp += nw;
    return i, n;
}
fn mstr_is(i: i64, n: i64, s: const u8[:]) -> bool {
    return n == s.len && meq(i, s) != 0;
}

// The identifier spelled by the n bytes at word i of the mapping, or -1.
fn ident_find_m(i: i64, n: i64, h: u32) -> i64 {
    var p = (h as i64) & idmask;
    loop {
        let e = idtab[p] as i64;
        if e == 0 { return -1; }
        if idents[e - 1].hash == h && idents[e - 1].len as i64 == n {
            let o = idents[e - 1].off as i64;
            if meq(i, src[o..o + n]) != 0 { return e - 1; }
        }
        p = (p + 1) & idmask;
    }
}

// What a replay relocates by. hcx holds, for the blob's identifiers, their
// ids here (hcx[0..hr_ni]) and their entries' positions in the blob
// (hcx[hr_ni..2 hr_ni]), then the anchors' offsets here.
var hr_s: i64 = 0;        // src.len before
var hr_srclen: i64 = 0;   // the unit's bytes of source text
var hr_ni: i64 = 0;
var hr_abase: i64 = 0;
var hr_na: i64 = 0;
var hb_out: i64 = 0;      // positions in the blob of what blob_commit applies
var hb_mut: i64 = 0;

// A source offset of the blob: in the unit's text, or an anchor.
fn rl(v: u32) -> u32 {
    if v < 0x80000000 {
        if v as i64 > hr_srclen {
            rerr = true;
            return 0;
        }
        return (hr_s + (v as i64)) as! u32;
    }
    let a = (v & 0x7FFFFFFF) as i64;
    if a >= hr_na {
        rerr = true;
        return 0;
    }
    return hcx[hr_abase + a];
}
// A local identifier of the blob.
fn lm(v: u32) -> u32 {
    if v as i64 >= hr_ni {
        rerr = true;
        return 0;
    }
    return hcx[v];
}

// Replays blob bid of the current key: checks what the head did not (the
// identifiers, the anchors), then appends the unit's effect. False, with
// nothing changed, when a check fails or the blob is missing or corrupt.
fn blob_replay(bid: u64) -> bool {
    hc_path(bid, true);
    let t0 = clock_ns();
    mlen = map_file(hcp);
    if mlen <= 0 {
        mlen = 0;
        return false;
    }
    if mw(0) != HC_MAGIC_B || mw(1) != HC_VERSION || mw(2) as i64 != mlen {
        st_corrupt++;
        unlink_path(hcp);
        return false;
    }
    let tc0 = clock_ns();
    let cs = mcsum(5, mlen);
    tm_csum += clock_ns() - tc0;
    if (cs & 0xFFFFFFFF) as! u32 != mw(3) || (cs >> 32) as! u32 != mw(4) {
        st_corrupt++;
        unlink_path(hcp);
        return false;
    }
    let t1 = clock_ns();
    tm_read += t1 - t0;
    rp = 5;
    rerr = false;
    let ki, kn = mstr();
    if rerr || !mstr_is(ki, kn, hck) { return false; }
    hr_srclen = m32() as i64;
    // the identifiers: which exist, and what the variant requires of them
    hr_ni = m32() as i64;
    if hr_ni > mlen { return false; }
    hcx.clear();
    hcx.resize(2 * hr_ni, 0);
    for i in hr_ni {
        let pos = rp;
        let h = m32();
        let fl = m32();
        let off = m32();
        let def = m32();
        let si, sn = mstr();
        if rerr { return false; }
        let id = ident_find_m(si, sn, h);
        if fl & LF_LOOKED == 0 && id < 0 { return false; }
        if fl & LF_EXISTS != 0 && id < 0 { return false; }
        if fl & LF_NOTEXIST != 0 && id >= 0 { return false; }
        if fl & LF_DEF != 0 {
            if def as i64 >= hdef.len || hdef[def].id as i64 != id { return false; }
        } else if fl & LF_OBS != 0 && id >= 0 && idents[id].macro >= 0 {
            return false;
        }
        if fl & LF_LOOKED != 0 && off < 0x80000000 && off as i64 > hr_srclen { return false; }
        if id >= 0 { hcx[i] = id as! u32; } else { hcx[i] = 0xFFFFFFFF; }
        hcx[hr_ni + i] = pos as! u32;
    }
    // the anchors: offsets into text that was there before the unit (the
    // bodies of macros it observed, files it found loaded); every
    // candidate must give the same offset here
    hr_na = m32() as i64;
    hr_abase = hcx.len;
    for a in hr_na {
        let nc = m32() as i64;
        var tgt: i64 = -1;
        for c in nc {
            let k = m32();
            let x = m32() as i64;
            let y = m32() as i64;
            if rerr { return false; }
            var v: i64 = -1;
            if k == 1 {
                if x >= hpo.len || hpo[x].kind != PO_OLD { return false; }
                let f = hpo[x].f as i64;
                if y > (files[f].end as i64) - (files[f].start as i64) { return false; }
                v = (files[f].start as i64) + y;
            } else if k == 2 || k == 3 || k == 4 {
                if x >= hdef.len { return false; }
                let mc = macros[hdef[x].m];
                if k == 4 {
                    v = mc.loc as i64;
                } else {
                    if y >= mc.count as i64 { return false; }
                    let tk = mtoks[(mc.first as i64) + y];
                    v = if k == 2 { tk.spell as i64 } else { tk.xloc as i64 };
                }
            } else {
                return false;
            }
            if tgt >= 0 && v != tgt { return false; }
            tgt = v;
        }
        if tgt < 0 { return false; }
        hcx.push(tgt as! u32);
    }
    if rerr { return false; }
    // the ids of the identifiers the unit creates: in table order
    let i0 = idents.len;
    var nn: i64 = 0;
    for i in hr_ni {
        if hcx[i] == 0xFFFFFFFF {
            hcx[i] = (i0 + nn) as! u32;
            nn++;
        }
    }
    // Append the effect. A structural error (the checksum makes it
    // impossible short of a bug) takes it all back before anything that
    // cannot be undone.
    let s0 = src.len;
    let n0 = names.len;
    let f0 = files.len;
    let m0 = macros.len;
    let mt0 = mtoks.len;
    let t0b = tu_toks.len;
    let x0 = mx_ranges.len;
    let pc0 = pack_changes.len;
    let ms0 = ms_changes.len;
    hr_s = s0;
    let t2 = clock_ns();
    tm_check += t2 - t1;
    let ok = blob_append();
    let t3 = clock_ns();
    tm_append += t3 - t2;
    if !ok {
        src.resize(s0);
        names.resize(n0);
        files.resize(f0);
        macros.resize(m0);
        mtoks.resize(mt0);
        tu_toks.resize(t0b);
        mx_ranges.resize(x0);
        pack_changes.resize(pc0);
        ms_changes.resize(ms0);
        st_corrupt++;
        return false;
    }
    blob_commit(i0, n0, f0, m0);
    tm_commit += clock_ns() - t3;
    return true;
}

// The flags and the definition index of local identifier li.
fn ent_flags(li: u32) -> u32 { mw((hcx[hr_ni + (li as i64)] as i64) + 1) }
fn ent_def(li: u32) -> u32 { mw((hcx[hr_ni + (li as i64)] as i64) + 3) }

fn get_tok(idk_all: bool) -> Tok {
    let a = mw(rp);
    let sp = mw(rp + 1);
    var v = mw(rp + 2);
    let xl = mw(rp + 3);
    rp += 4;
    let k = a & 255;
    if k == TK_IDENT || k == TK_PARAM || (idk_all && k >= TK_KW) { v = lm(v); }
    return Tok { kind: k as! u8, flags: ((a >> 8) & 255) as! u8, aux: (a >> 16) as! u16, spell: rl(sp), val: v, xloc: rl(xl) };
}

// The appends of a replay that can be undone.
fn blob_append() -> bool {
    let srci, srcn = mstr();
    if rerr || srcn != hr_srclen { return false; }
    mcopy(src, srci, srcn);
    let nmi, nmn = mstr();
    if rerr { return false; }
    mcopy(names, nmi, nmn);
    let nbase = (names.len - nmn) as u32;
    // files
    let nf = m32() as i64;
    for i in nf {
        let st = m32();
        let en = m32();
        let pa = m32();
        let pl = m32();
        let gd = m32();
        let fl = m32();
        let sp = m32();
        let spl = m32();
        let dev = m64();
        let ino = m64();
        let fsize = m64();
        let mt = m64() as! i64;
        let ct = m64() as! i64;
        if rerr { return false; }
        if st > en || en as i64 > srcn || (pa as i64) + (pl as i64) > nmn || (sp as i64) + (spl as i64) > nmn { return false; }
        var g: i32 = -1;
        if gd != 0xFFFFFFFF { g = lm(gd) as! i32; }
        var spo: u32 = 0;
        if spl != 0 { spo = nbase + sp; }
        files.push(FileRec { path: nbase + pa, path_len: pl, start: (hr_s as u32) + st, end: (hr_s as u32) + en, grd: g,
            once: fl & 1 != 0, system: fl & 2 != 0, lines_first: -1, lines_count: 0, sp_off: spo, sp_len: spl,
            dev: dev, ino: ino, fsize: fsize, mtime: mt, ctime: ct, rt: 0, rw: 0 });
    }
    // macros and their tokens
    let nm = m32() as i64;
    let mtb = mtoks.len as u32;
    var maxt: i64 = 0;
    if nm * 5 > mlen - rp { return false; }
    for i in nm {
        let nmw = mw(rp);
        let first = mw(rp + 1);
        let count = mw(rp + 2);
        let pk = mw(rp + 3);
        let loc = mw(rp + 4);
        rp += 5;
        if (first as i64) + (count as i64) > maxt { maxt = (first as i64) + (count as i64); }
        macros.push(Macro { name: lm(nmw), first: mtb + first, count: count, nparams: (pk & 0xFFFF) as! u16,
            flags: ((pk >> 16) & 255) as! u8, builtin: (pk >> 24) as! u8, enabled: true, loc: rl(loc) });
    }
    let nmt = m32() as i64;
    if nmt * 4 > mlen - rp || maxt > nmt { return false; }
    if reloc_toks(mtoks, rp, nmt, hcx[0..hr_ni], hcx[hr_abase..hcx.len], hr_s, hr_srclen, 256) == 0 { return false; }
    rp += nmt * 4;
    // the translation unit's tokens
    let nt = m32() as i64;
    if nt * 4 > mlen - rp { return false; }
    if nt > 0 && tu_toks.len + nt >= tok_frontier {
        prefault_toks(tu_toks, nt * 16 + 65536);
        tok_frontier = tu_toks.len + nt + 4096;
    }
    if reloc_toks(tu_toks, rp, nt, hcx[0..hr_ni], hcx[hr_abase..hcx.len], hr_s, hr_srclen, TK_KW) == 0 { return false; }
    rp += nt * 4;
    // -E's output (applied later)
    hb_out = rp;
    let oi, on = mstr();
    let bol = m32();
    // -g's macro expansion ranges, #pragma pack and ms_struct
    let nx = m32() as i64;
    for i in nx {
        let a = rl(m32()) as u64;
        let b = rl(m32()) as u64;
        mx_ranges.push((a << 32) | b);
    }
    let tb = tu_toks.len - nt;
    let npc = m32() as i64;
    for i in npc {
        let ti = m32() as i64;
        let v = m32();
        if ti > nt { rerr = true; }
        pack_changes.push((tb + ti) as! u32);
        pack_changes.push(v);
    }
    let nms = m32() as i64;
    for i in nms {
        let ti = m32() as i64;
        let v = m32();
        if ti > nt { rerr = true; }
        ms_changes.push((tb + ti) as! u32);
        ms_changes.push(v);
    }
    // the changes to what was there before: validated here, applied later
    hb_mut = rp;
    let nim = m32() as i64;
    for i in nim {
        let li = m32();
        let kind = m32();
        let kk = m32();
        lm(li);
        if rerr || kind > 2 || (kind == 1 && kk as i64 >= nm) { return false; }
        if kind == 2 && ent_flags(li) & LF_DEF == 0 { return false; }
    }
    let npo = m32() as i64;
    for i in npo { lm(m32()); }
    let nfm = m32() as i64;
    for i in nfm {
        let x = m32() as i64;
        let gd = m32();
        let fl = m32();
        let sp = m32();
        let spl = m32();
        if x >= hpo.len || hpo[x].kind != PO_OLD { return false; }
        if gd != 0xFFFFFFFF { lm(gd); }
        if (sp as i64) + (spl as i64) > nmn { return false; }
    }
    if hm_flags & 1 != 0 { m64(); }
    if hm_flags & 2 != 0 {
        m32();
        let n = m32() as i64;
        for i in n {
            m32();
            let l = m32();
            if l != 0 { lm(l - 1); }
        }
    }
    let so = m32();
    let sl = m32();
    let sy = m32();
    if (so as i64) + (sl as i64) > nmn { return false; }
    return !rerr;
}

// The rest of a replay, which cannot fail: the identifiers, the path
// cache, the changes to identifiers and files, -E's output, the end of
// the include; and what the recordings around it must know.
fn blob_commit(i0: i64, n0: i64, f0: i64, m0: i64) {
    // identifiers, created in the order of their first lookups
    for i in hr_ni {
        let pos = hcx[hr_ni + i] as i64;
        let id = hcx[i];
        if id as i64 >= i0 { ident_new(rl(mw(pos + 2)) as i64, mw(pos + 4) as i64, mw(pos)); }
        if rec_on {
            let fl = mw(pos + 1);
            if fl & LF_LOOKED != 0 {
                if fl & LF_NOTEXIST != 0 { hk_notexist = 1; }
                hk_look(id, rl(mw(pos + 2)) as i64);
                hk_notexist = 0;
            }
        }
    }
    if rec_on {
        // the observations, before the changes
        for i in hr_ni {
            let fl = mw((hcx[hr_ni + i] as i64) + 1);
            if fl & LF_OBS != 0 { hk_mread(hcx[i]); }
            if fl & LF_EXISTS != 0 { hk_exist(hcx[i] as i64); }
        }
    }
    // the path cache, and the recordings' path observations
    for po in hpo {
        let key = hcs[po.key..po.key + po.klen];
        let path = hcs[po.path..po.path + po.plen];
        if po.kind == PO_NEG {
            if rec_on {
                var a: u32 = 0;
                var b: u32 = 0;
                var stored = false;
                for r in recs.len {
                    if po.e >= 0 && po.e as i64 >= recs[r].paths0 as i64 { continue; }
                    if !stored {
                        a, b = hk_store_path(key, path);
                        stored = true;
                    }
                    ev.push(Ev { rec: r as! u16, kind: EV_PNEG, flag: 0, a: a, b: b, c: 0, d: 0 });
                }
            }
            if po.e < 0 { path_add(key, -1); }
        } else if po.kind == PO_NEW {
            let f = f0 + (po.nf as i64);
            if rec_on {
                let a, b = hk_store_path(key, path);
                for r in recs.len { ev.push(Ev { rec: r as! u16, kind: EV_PNEW, flag: 0, a: a, b: b, c: f as! u32, d: 0 }); }
            }
            path_add(key, f);
        } else if rec_on {
            hk_path_hit(po.e as i64, po.f as i64, key, path);
        }
    }
    // the changes to identifiers' macros, poisoning, files loaded before
    rp = hb_mut;
    let nim = m32() as i64;
    for i in nim {
        let li = m32();
        let kind = m32();
        let kk = m32();
        let id = hcx[li];
        if rec_on { hk_mwrite(id); }
        if kind == 0 {
            idents[id].macro = -1;
        } else if kind == 1 {
            idents[id].macro = (m0 + (kk as i64)) as! i32;
        } else {
            idents[id].macro = hdef[ent_def(li)].m;
        }
    }
    let npo = m32() as i64;
    for i in npo {
        let id = hcx[m32()];
        if rec_on { hk_poison(id); }
        idents[id].flags = idents[id].flags | ID_POISONED;
    }
    let nfm = m32() as i64;
    for i in nfm {
        let x = m32() as i64;
        let gd = m32();
        let fl = m32();
        let sp = m32();
        let spl = m32();
        let f = hpo[x].f as i64;
        if rec_on { hk_fwrite(f); }
        if gd == 0xFFFFFFFF { files[f].grd = -1; } else { files[f].grd = hcx[gd] as! i32; }
        files[f].once = fl & 1 != 0;
        files[f].system = fl & 2 != 0;
        if fl & 4 != 0 {
            files[f].sp_off = (n0 as u32) + sp;
            files[f].sp_len = spl;
        }
    }
    if hm_flags & 1 != 0 {
        if rec_on { hk_counter(); }
        counter_value = m64() as! i64;
    }
    if hm_flags & 2 != 0 {
        if rec_on { hk_pack(); }
        pack_cur = m32();
        let n = m32() as i64;
        pack_stack.clear();
        for i in n {
            let v = m32();
            let l = m32();
            var lab: u32 = 0;
            if l != 0 { lab = hcx[l - 1] + 1; }
            pack_stack.push(PackEnt { val: v, label: lab });
        }
    }
    let so = m32();
    let sl = m32();
    let sy = m32();
    if rec_on {
        let d = (include_depth() + (hm_maxrel as i64)) as! u32;
        for r in recs.len { if d > recs[r].maxd { recs[r].maxd = d; } }
        if hm_flags & 4 != 0 { hk_depth(); }
        if hm_flags & 8 != 0 { hk_basefile(); }
    }
    // -E: the file's line marker, what it printed
    if mode_E {
        pr_file_enter((n0 as u32) + so, sl, sy != 0);
        rp = hb_out;
        let oi, on = mstr();
        let bol = m32();
        mcopy(out, oi, on);
        pr_bol = bol != 0;
        if out.len > 1048576 && !out_to_file && !rec_on { pr_flush(); }
    }
    // back in the includer, as at the end of the file
    save_lexer();
    back_in_includer();
}

// ---------------------------------------------------------------------------
// Recording.

// Starts recording the include whose key hc_replay left in hck.
fn hc_rec_start(name: const u8[:], angled: bool, k: i64) -> bool {
    if !hc_ready || !hc_on { return false; }
    if recs.len >= 60 {
        hk_bad(HC_BAD_NEST);
        return false;
    }
    hc_serial++;
    let ko = hcb.len as! u32;
    hcb.append(hck);
    let d = include_depth() as! u32;
    recs.push(Rec {
        serial: hc_serial, ctxd: 0,
        src0: src.len as! u32, names0: names.len as! u32, idents0: idents.len as! u32, macros0: macros.len as! u32,
        mtoks0: mtoks.len as! u32, files0: files.len as! u32, toks0: tu_toks.len as! u32, mx0: mx_ranges.len as! u32,
        packc0: pack_changes.len as! u32, msc0: ms_changes.len as! u32, out0: out.len as! u32, paths0: pathents.len as! u32,
        push0: push_stack.len as! u32, ev0: ev.len as! u32,
        key: ko, key_len: hck.len as! u32, keyh: hc_keyh,
        bad: 0, depth0: d, maxd: d,
        ctr_t: false, pack_t: false, uses_depth: false, uses_base: false, ctr0: 0, pack0: 0,
        so: 0, sl: 0, sys: 0,
    });
    rec_on = true;
    rec_cur = hc_serial;
    return true;
}

// The include just pushed its file: the unit ends when it is popped.
fn hc_rec_entered() {
    let d = recs.len - 1;
    let ci = ctxs.len - 1;
    recs[d].ctxd = ctxs.len as! u32;
    // -E: what the unit prints starts after the file's line marker (which
    // depends on the line before; a replay prints it)
    recs[d].out0 = out.len as! u32;
    recs[d].so = ctxs[ci].spell;
    recs[d].sl = ctxs[ci].spell_len;
    recs[d].sys = ctxs[ci].sys;
}

// Ends the innermost recording: its events leave ev (the others stay).
fn rec_pop() -> Rec {
    let d = recs.len - 1;
    let r = recs[d];
    evown.clear();
    var j = r.ev0 as i64;
    for i in (r.ev0 as i64)..ev.len {
        let e = ev[i];
        if e.rec as i64 == d { evown.push(e); } else { ev[j] = e; j++; }
    }
    ev.resize(j);
    recs.pop();
    rec_on = recs.len > 0;
    rec_cur = 0;
    if rec_on { rec_cur = recs[recs.len - 1].serial; }
    return r;
}

// The include did nothing (once, guarded, imported): nothing to save.
fn hc_rec_drop() {
    let r = rec_pop();
}

// The end of the unit's file (end_of_file, back in the includer).
fn hc_unit_end() {
    let r = rec_pop();
    if r.bad != 0 {
        st_bad++;
        return;
    }
    if push_stack.len != r.push0 as i64 {
        st_bad++;
        return;
    }
    let srcd = src.len - (r.src0 as i64);
    var nt = tu_toks.len - (r.toks0 as i64);
    if mode_E { nt = (out.len - (r.out0 as i64)) / 8; }
    if srcd < HC_MIN_SRC && nt < HC_MIN_TOKS {
        st_small++;
        return;
    }
    let t0 = clock_ns();
    let ok = rec_save(r);
    tm_save += clock_ns() - t0;
    if !ok {
        st_bad++;
        return;
    }
    st_recorded++;
}

var fr_serial: u32 = 0;
var fr_src0: i64 = 0;
var fr_bad: bool = false;
var fr_anchors: i64 = 0;     // hcx[fr_abase..]: the anchors' offsets
var fr_abase: i64 = 0;

// The local index of identifier id (a new entry if it has none: an
// identifier the unit refers to without looking it up).
fn lid(id: u32) -> u32 {
    if id as i64 >= lmap.len {
        fr_bad = true;
        return 0;
    }
    if lmap[id].m == fr_serial { return lmap[id].l; }
    lmap[id].m = fr_serial;
    lmap[id].l = lent.len as! u32;
    lent.push(LEnt { id: id, flags: 0, off: 0, def: 0 });
    return (lent.len - 1) as! u32;
}

// Anchor candidates: offsets of text before the unit that its effect may
// refer to, in the bodies of the macros it observed (hcd: 1 << 40 |
// offset -> chain in hcx, 4 words each: kind, def, token, next).
fn cand_add(off: u32, kind: u32, x: u32, y: u32) {
    if off as i64 >= fr_src0 { return; }
    let key = (1 << 40) | (off as u64);
    var prev: u32 = 0;
    let g = hcd.get(key);
    if g { prev = g; }
    hcx.push(kind);
    hcx.push(x);
    hcx.push(y);
    hcx.push(prev);
    hcd.insert(key, (hcx.len / 4) as! u32);
}

// A source offset of the unit's effect, for the blob: an offset in the
// unit's text, or an anchor (an offset of text from before the unit,
// which the replay finds through the candidates).
fn frel(v: u32) -> u32 {
    if v as i64 >= fr_src0 {
        let d = (v as i64) - fr_src0;
        if d >= 0x80000000 { fr_bad = true; return 0; }
        return d as! u32;
    }
    let key = (2 << 40) | (v as u64);
    let g = hcd.get(key);
    if g { return g | 0x80000000; }
    var has = hcd.contains((1 << 40) | (v as u64));
    if !has {
        for po in hpo {
            if po.kind == PO_OLD && v >= files[po.f].start && v <= files[po.f].end { has = true; }
        }
    }
    if !has {
        fr_bad = true;
        return 0;
    }
    let a = fr_anchors as! u32;
    fr_anchors++;
    hcx.push(v);
    hcd.insert(key, a);
    return a | 0x80000000;
}

fn wtok(o: u32[>..]&, t: Tok, idk: bool) {
    o.push((t.kind as u32) | ((t.flags as u32) << 8) | ((t.aux as u32) << 16));
    o.push(frel(t.spell));
    if idk { o.push(lid(t.val)); } else { o.push(t.val); }
    o.push(frel(t.xloc));
}

// Saves the recording r: the blob, then the manifest. False when the
// recording cannot be expressed (an offset nothing anchors, ...).
fn rec_save(r: Rec) -> bool {
    fr_serial = r.serial;
    fr_src0 = r.src0 as i64;
    fr_bad = false;
    while lmap.len < idents.len { lmap.push(ITouch { m: 0, l: 0, w: 0 }); }
    lent.clear();
    hdef.clear();
    hpo.clear();
    // the local identifier table: first the lookups, in order
    for e in evown {
        if e.kind == EV_LOOK && lmap[e.a].m != fr_serial {
            lmap[e.a].m = fr_serial;
            lmap[e.a].l = lent.len as! u32;
            var fl: u32 = LF_LOOKED;
            if e.flag != 0 { fl = fl | LF_NOTEXIST; }
            lent.push(LEnt { id: e.a, flags: fl, off: e.b, def: 0 });
        }
    }
    // the identifiers the unit created were created by their first
    // lookups, in this order, and are spelled where those were
    var nexp = r.idents0 as i64;
    for le in lent {
        if le.id >= r.idents0 {
            if le.id as i64 != nexp || idents[le.id].off != le.off { return false; }
            nexp++;
        }
    }
    if nexp != idents.len { return false; }
    // macro observations, intern's findings
    for e in evown {
        if e.kind == EV_MOBS {
            let li = lid(e.a);
            lent[li].flags = lent[li].flags | LF_OBS;
            let m = e.b as! i32;
            if m >= 0 {
                if m as i64 >= r.macros0 as i64 { return false; }
                lent[li].flags = lent[li].flags | LF_DEF;
                lent[li].def = hdef.len as! u32;
                hdef.push(HDef { id: li, m: m });
            }
        } else if e.kind == EV_EXIST {
            let li = lid(e.a);
            lent[li].flags = lent[li].flags | LF_EXISTS;
        }
    }
    // path observations
    var nnew: i64 = 0;
    for e in evown {
        if e.kind == EV_PNEG || e.kind == EV_PNEW || e.kind == EV_POLD {
            let kn = e.b & 0xFFFF;
            let pn = e.b >> 16;
            var kind: u32 = PO_NEG;
            var f: i64 = -1;
            var nf: u32 = 0;
            if e.kind == EV_PNEW {
                kind = PO_NEW;
                f = e.c as i64;
                if f != (r.files0 as i64) + nnew { return false; }
                nf = nnew as! u32;
                nnew++;
            } else if e.kind == EV_POLD {
                kind = PO_OLD;
                f = e.c as i64;
                if f >= r.files0 as i64 { return false; }
            }
            hpo.push(HPo { kind: kind, f: f as! i32, e: e.d as! i32, key: e.a, klen: kn, path: e.a + kn, plen: pn, nf: nf });
            hpo[hpo.len - 1].nf = nf;
            if e.kind == EV_POLD { hpo[hpo.len - 1].nf = e.flag as u32; }
        }
    }
    if (r.files0 as i64) + nnew != files.len { return false; }
    // anchor candidates: the bodies of the observed macros
    hcd.clear();
    hcx.clear();
    for hd, j in hdef {
        let mc = macros[hd.m];
        for k in mc.count as i64 {
            let tk = mtoks[(mc.first as i64) + k];
            cand_add(tk.spell, 2, j as! u32, k as! u32);
            cand_add(tk.xloc, 3, j as! u32, k as! u32);
        }
        cand_add(mc.loc, 4, j as! u32, 0);
    }
    fr_abase = hcx.len;
    fr_anchors = 0;
    // the effect (hcw)
    hcw.clear();
    let srcd = src[fr_src0..src.len];
    wstr(hcw, srcd);
    let nb = r.names0 as i64;
    wstr(hcw, names[nb..names.len]);
    hcw.push((files.len - (r.files0 as i64)) as! u32);
    for fi in (r.files0 as i64)..files.len {
        let fr = files[fi];
        if (fr.start as i64) < fr_src0 || (fr.path as i64) < nb { return false; }
        hcw.push(((fr.start as i64) - fr_src0) as! u32);
        hcw.push(((fr.end as i64) - fr_src0) as! u32);
        hcw.push(((fr.path as i64) - nb) as! u32);
        hcw.push(fr.path_len);
        if fr.grd >= 0 { hcw.push(lid(fr.grd as! u32)); } else { hcw.push(0xFFFFFFFF); }
        var fl: u32 = 0;
        if fr.once { fl = fl | 1; }
        if fr.system { fl = fl | 2; }
        hcw.push(fl);
        if fr.sp_len != 0 {
            if (fr.sp_off as i64) < nb { return false; }
            hcw.push(((fr.sp_off as i64) - nb) as! u32);
        } else {
            hcw.push(0);
        }
        hcw.push(fr.sp_len);
        w64(hcw, fr.dev);
        w64(hcw, fr.ino);
        w64(hcw, fr.fsize);
        w64(hcw, fr.mtime as! u64);
        w64(hcw, fr.ctime as! u64);
    }
    hcw.push((macros.len - (r.macros0 as i64)) as! u32);
    for mi in (r.macros0 as i64)..macros.len {
        let mc = macros[mi];
        if !mc.enabled || (mc.first as i64) < (r.mtoks0 as i64) { return false; }
        hcw.push(lid(mc.name));
        hcw.push(mc.first - r.mtoks0);
        hcw.push(mc.count);
        hcw.push((mc.nparams as u32) | ((mc.flags as u32) << 16) | ((mc.builtin as u32) << 24));
        hcw.push(frel(mc.loc));
    }
    hcw.push((mtoks.len - (r.mtoks0 as i64)) as! u32);
    for ti in (r.mtoks0 as i64)..mtoks.len {
        let t = mtoks[ti];
        wtok(hcw, t, t.kind == TK_IDENT || t.kind == TK_PARAM);
    }
    hcw.push((tu_toks.len - (r.toks0 as i64)) as! u32);
    for ti in (r.toks0 as i64)..tu_toks.len {
        let t = tu_toks[ti];
        wtok(hcw, t, t.kind == TK_IDENT || t.kind as i64 >= TK_KW);
    }
    let ob = r.out0 as i64;
    wstr(hcw, out[ob..out.len]);
    if pr_bol { hcw.push(1); } else { hcw.push(0); }
    hcw.push((mx_ranges.len - (r.mx0 as i64)) as! u32);
    for xi in (r.mx0 as i64)..mx_ranges.len {
        let x = mx_ranges[xi];
        hcw.push(frel((x >> 32) as! u32));
        hcw.push(frel((x & 0xFFFFFFFF) as! u32));
    }
    let tb = r.toks0 as i64;
    hcw.push(((pack_changes.len - (r.packc0 as i64)) / 2) as! u32);
    var pi = r.packc0 as i64;
    while pi + 1 < pack_changes.len {
        if (pack_changes[pi] as i64) < tb { return false; }
        hcw.push(((pack_changes[pi] as i64) - tb) as! u32);
        hcw.push(pack_changes[pi + 1]);
        pi += 2;
    }
    hcw.push(((ms_changes.len - (r.msc0 as i64)) / 2) as! u32);
    pi = r.msc0 as i64;
    while pi + 1 < ms_changes.len {
        if (ms_changes[pi] as i64) < tb { return false; }
        hcw.push(((ms_changes[pi] as i64) - tb) as! u32);
        hcw.push(ms_changes[pi + 1]);
        pi += 2;
    }
    // changes to identifiers and files that were there before
    var nim: i64 = 0;
    for e in evown { if e.kind == EV_MWRITE { nim++; } }
    hcw.push(nim as! u32);
    for e in evown {
        if e.kind != EV_MWRITE { continue; }
        let li = lid(e.a);
        let m = idents[e.a].macro as i64;
        hcw.push(li);
        if m < 0 {
            hcw.push(0);
            hcw.push(0);
        } else if m >= r.macros0 as i64 {
            hcw.push(1);
            hcw.push((m - (r.macros0 as i64)) as! u32);
        } else {
            // restored by #pragma pop_macro: what it was before the unit
            if lent[li].flags & LF_DEF == 0 || hdef[lent[li].def].m as i64 != m { return false; }
            hcw.push(2);
            hcw.push(0);
        }
    }
    var npz: i64 = 0;
    for e in evown { if e.kind == EV_POISON { npz++; } }
    hcw.push(npz as! u32);
    for e in evown { if e.kind == EV_POISON { hcw.push(lid(e.a)); } }
    var nfm: i64 = 0;
    for e in evown { if e.kind == EV_FWRITE { nfm++; } }
    hcw.push(nfm as! u32);
    for e in evown {
        if e.kind != EV_FWRITE { continue; }
        let f = e.a as i64;
        var x: i64 = -1;
        for po, i in hpo { if po.kind == PO_OLD && po.f as i64 == f { x = i; } }
        if x < 0 { return false; }
        hcw.push(x as! u32);
        let fr = files[f];
        if fr.grd >= 0 { hcw.push(lid(fr.grd as! u32)); } else { hcw.push(0xFFFFFFFF); }
        var fl: u32 = 0;
        if fr.once { fl = fl | 1; }
        if fr.system { fl = fl | 2; }
        var sp: u32 = 0;
        if fr.sp_len != 0 && fr.sp_off as i64 >= nb {
            fl = fl | 4;
            sp = ((fr.sp_off as i64) - nb) as! u32;
        }
        hcw.push(fl);
        hcw.push(sp);
        hcw.push(fr.sp_len);
    }
    if r.ctr_t { w64(hcw, counter_value as! u64); }
    if r.pack_t {
        hcw.push(pack_cur);
        hcw.push(pack_stack.len as! u32);
        for pe in pack_stack {
            hcw.push(pe.val);
            if pe.label != 0 { hcw.push(lid(pe.label - 1) + 1); } else { hcw.push(0); }
        }
    }
    if (r.so as i64) < nb && r.sl != 0 { return false; }
    hcw.push(((r.so as i64) - nb) as! u32);
    hcw.push(r.sl);
    hcw.push(r.sys as u32);
    // identifiers named by the head: the guards of files found loaded,
    // the pack labels before the unit
    for po in hpo { if po.kind == PO_OLD && files[po.f].grd >= 0 { } }
    // the blob (hcv): the key, the identifiers, the anchors, the effect
    hcv.clear();
    for i in 5 { hcv.push(0); }
    wstr(hcv, hcb[r.key..r.key + r.key_len]);
    hcv.push(srcd.len as! u32);
    // the identifiers' first offsets may add anchors: relocate them first
    var offs: u32[>..] = [];
    for le in lent {
        if le.flags & LF_LOOKED != 0 { offs.push(frel(le.off)); } else { offs.push(0); }
    }
    if fr_bad { return false; }
    hcv.push(lent.len as! u32);
    for le, i in lent {
        let d = idents[le.id];
        hcv.push(d.hash);
        hcv.push(le.flags);
        hcv.push(offs[i]);
        hcv.push(le.def);
        wstr(hcv, src[d.off..d.off + d.len]);
    }
    hcv.push(fr_anchors as! u32);
    for a in fr_anchors {
        let v = hcx[fr_abase + a];
        // candidates: macro bodies, then files found loaded
        var nc: i64 = 0;
        let g = hcd.get((1 << 40) | (v as u64));
        var ch: u32 = 0;
        if g { ch = g; }
        var c = ch;
        while c != 0 { nc++; c = hcx[((c - 1) * 4 + 3) as i64]; }
        for po in hpo { if po.kind == PO_OLD && v >= files[po.f].start && v <= files[po.f].end { nc++; } }
        hcv.push(nc as! u32);
        c = ch;
        while c != 0 {
            let b = ((c - 1) * 4) as i64;
            hcv.push(hcx[b]);
            hcv.push(hcx[b + 1]);
            hcv.push(hcx[b + 2]);
            c = hcx[b + 3];
        }
        for po, i in hpo {
            if po.kind == PO_OLD && v >= files[po.f].start && v <= files[po.f].end {
                hcv.push(1);
                hcv.push(i as! u32);
                hcv.push(v - files[po.f].start);
            }
        }
    }
    hcv.append(hcw);
    hcv[0] = HC_MAGIC_B;
    hcv[1] = HC_VERSION;
    hcv[2] = hcv.len as! u32;
    let cs = csum_words(hcv[5..]);
    hcv[3] = (cs & 0xFFFFFFFF) as! u32;
    hcv[4] = (cs >> 32) as! u32;
    let bid = cs;
    // write the blob
    hc_keyh = r.keyh;
    hc_path(bid, true);
    if write_words(hcp, hcv) == 0 {
        st_werr++;
        return true;
    }
    st_wbytes += hcv.len * 4;
    // the variant's head (hcw): the path observations, the macros observed
    // defined, the rest
    hcw.clear();
    hcw.push(0);
    w64(hcw, bid);
    hcw.push(hpo.len as! u32);
    for po in hpo {
        var st: u32 = 0;
        if po.kind == PO_OLD { st = po.nf; }
        hcw.push(po.kind | (st << 8));
        wstr(hcw, hcb[po.key..po.key + po.klen]);
        wstr(hcw, hcb[po.path..po.path + po.plen]);
        if po.kind == PO_NEW || po.kind == PO_OLD {
            let fr = files[po.f];
            w64(hcw, fr.dev);
            w64(hcw, fr.ino);
            w64(hcw, fr.fsize);
            w64(hcw, fr.mtime as! u64);
            w64(hcw, fr.ctime as! u64);
        }
        if po.kind == PO_NEW { hcw.push(po.nf); }
        if po.kind == PO_OLD && st & 8 != 0 {
            // the guard at the observation (the event's d)
            wstr(hcw, ident_text(po.e as i64));
        }
    }
    hcw.push(hdef.len as! u32);
    for hd in hdef {
        let id = lent[hd.id].id;
        let d = idents[id];
        wstr(hcw, src[d.off..d.off + d.len]);
        hcw.push(d.hash);
        let mc = macros[hd.m];
        hcw.push((mc.flags as u32) | ((mc.builtin as u32) << 8) | ((mc.nparams as u32) << 16));
        hcw.push(mc.count);
        for k in mc.count as i64 {
            let tk = mtoks[(mc.first as i64) + k];
            hcw.push((tk.kind as u32) | ((tk.flags as u32) << 8) | ((tk.aux as u32) << 16));
            let kk = tk.kind as i64;
            if kk == TK_IDENT || kk == TK_PARAM {
                wstr(hcw, ident_text(tk.val as i64));
            } else if spelled(kk) {
                wstr(hcw, src[tk.spell..tk.spell + tk.val]);
            }
        }
    }
    var mf: u32 = 0;
    if r.ctr_t { mf = mf | 1; }
    if r.pack_t { mf = mf | 2; }
    if r.uses_depth { mf = mf | 4; }
    if r.uses_base { mf = mf | 8; }
    hcw.push(mf);
    if r.ctr_t { w64(hcw, r.ctr0 as! u64); }
    if r.pack_t {
        let p = r.pack0 as i64;
        hcw.push(hcb_get32(p));
        let n = hcb_get32(p + 4) as i64;
        hcw.push(n as! u32);
        for i in n {
            hcw.push(hcb_get32(p + 8 + i * 8));
            let lab = hcb_get32(p + 12 + i * 8);
            if lab != 0 { wstr(hcw, ident_text((lab - 1) as i64)); } else { hcw.push(0); }
        }
    }
    if r.uses_depth { hcw.push(r.depth0); }
    if r.uses_base { wstr(hcw, names[base_file_name..base_file_name + base_file_name_len]); }
    hcw.push(r.maxd - r.depth0);
    hcw[0] = (hcw.len - 1) as! u32;
    man_add(r, bid);
    // now and then, keep the cache within its size
    if bid & 63 == 0 { evict_dir(hcb[hc_dir_off..hc_dir_off + hc_dir_len], hc_limit); }
    return true;
}

// Adds the variant in hcw to the manifest of r's key (the newest first),
// in the file and in this process.
fn man_add(r: Rec, bid: u64) {
    hc_keyh = r.keyh;
    hc_path(0, false);
    hcr.clear();
    let n = read_words(hcp, hcr);
    hcv.clear();
    for i in 5 { hcv.push(0); }
    wstr(hcv, hcb[r.key..r.key + r.key_len]);
    let nvpos = hcv.len;
    hcv.push(1);
    hcv.append(hcw);
    if n > 0 && file_ok(hcr, HC_MAGIC_M) {
        rp = 5;
        rerr = false;
        let ki, kn = rstr(hcr);
        if !rerr && str_is(hcr, ki, kn, hcb[r.key..r.key + r.key_len]) {
            let nv = r32(hcr) as i64;
            var kept: u32 = 1;
            for vi in nv {
                let vl = r32(hcr) as i64;
                let vs = rp;
                if vl < 2 || vl > hcr.len - vs { break; }
                let ob = (hcr[vs] as u64) | ((hcr[vs + 1] as u64) << 32);
                if ob != bid && kept < HC_MAX_VARIANTS {
                    hcv.push(vl as! u32);
                    hcv.append(hcr[vs..vs + vl]);
                    kept++;
                }
                rp = vs + vl;
            }
            hcv[nvpos] = kept;
        }
    }
    hcv[0] = HC_MAGIC_M;
    hcv[1] = HC_VERSION;
    hcv[2] = hcv.len as! u32;
    let cs = csum_words(hcv[5..]);
    hcv[3] = (cs & 0xFFFFFFFF) as! u32;
    hcv[4] = (cs >> 32) as! u32;
    if write_words(hcp, hcv) == 0 {
        st_werr++;
        return;
    }
    st_wbytes += hcv.len * 4;
    // this process sees it too
    let off = hcm.len;
    hcm.append(hcv);
    for h, i in hman {
        if h.keyh == r.keyh {
            hman[i].off = off as! u32;
            hman[i].len = hcv.len as! u32;
            return;
        }
    }
    hman.push(HMan { keyh: r.keyh, off: off as! u32, len: hcv.len as! u32 });
}

// ---------------------------------------------------------------------------
// Reports.

fn hc_report() {
    if !hc_stats_opt { return; }
    var o: u8[>..] = [];
    if !hc_on {
        o.append("goosecc: header cache: off\n");
    } else {
        format(o, "goosecc: header cache: ", st_lookups, " lookups, ", st_hits, " hits, ", st_misses, " misses; ",
            st_recorded, " recorded (", st_wbytes, " bytes written), ", st_small, " too small, ", st_bad, " not cacheable, ",
            st_corrupt, " corrupt, ", st_werr, " write errors; replay ", tm_replay / 1000, " us (read ", tm_read / 1000,
            ", check ", tm_check / 1000, ", append ", tm_append / 1000, ", commit ", tm_commit / 1000, "), saving ", tm_save / 1000, " us\n");
    }
    if hc_on && opt_time {
        var q: u8[>..] = [];
        format(q, "goosecc: header cache: manifests ", tm_man / 1000, " us, heads ", tm_head / 1000, " us, checksums ", tm_csum / 1000, " us\n");
        write_stderr(q);
    }
    write_stderr(o);
}

// --pp-state-hash: a checksum of everything preprocessing leaves for the
// later phases, to show that a replay leaves the same state. Not the
// caches (line tables, the path cache, the identifier hash table), nor
// -E's output (written to stdout in pieces; compare it whole). With
// verbose, one per array.
fn hc_state_hash(verbose: bool) {
    var o: u8[>..] = [];
    var all: u64 = 0;
    for part in 8 {
        hcw.clear();
        if part == 0 { wstr(hcw, src); }
        if part == 1 { wstr(hcw, names); }
        if part == 2 {
            for d in idents {
                hcw.push(d.off); hcw.push(d.len); hcw.push(d.hash); hcw.push(d.macro as! u32);
                hcw.push((d.kw as u32) | ((d.ppkw as u32) << 16) | ((d.flags as u32) << 24));
            }
        }
        if part == 3 {
            for m in macros {
                hcw.push(m.name); hcw.push(m.first); hcw.push(m.count);
                hcw.push((m.nparams as u32) | ((m.flags as u32) << 16) | ((m.builtin as u32) << 24));
                if m.enabled { hcw.push(1); } else { hcw.push(0); }
                hcw.push(m.loc);
            }
        }
        if part == 4 {
            for t in mtoks {
                hcw.push((t.kind as u32) | ((t.flags as u32) << 8) | ((t.aux as u32) << 16));
                hcw.push(t.spell); hcw.push(t.val); hcw.push(t.xloc);
            }
        }
        if part == 5 {
            for t in tu_toks {
                hcw.push((t.kind as u32) | ((t.flags as u32) << 8) | ((t.aux as u32) << 16));
                hcw.push(t.spell); hcw.push(t.val); hcw.push(t.xloc);
            }
        }
        if part == 6 {
            for f in files {
                hcw.push(f.path); hcw.push(f.path_len); hcw.push(f.start); hcw.push(f.end); hcw.push(f.grd as! u32);
                if f.once { hcw.push(1); } else { hcw.push(0); }
                if f.system { hcw.push(1); } else { hcw.push(0); }
                hcw.push(f.sp_off); hcw.push(f.sp_len);
                w64(hcw, f.dev); w64(hcw, f.ino); w64(hcw, f.fsize); w64(hcw, f.mtime as! u64); w64(hcw, f.ctime as! u64);
            }
        }
        if part == 7 {
            for x in mx_ranges { w64(hcw, x); }
            hcw.push(0xFFFFFFFF);
            for x in pack_changes { hcw.push(x); }
            hcw.push(0xFFFFFFFF);
            for x in ms_changes { hcw.push(x); }
            hcw.push(0xFFFFFFFF);
            w64(hcw, counter_value as! u64);
            hcw.push(pack_cur);
            for pe in pack_stack { hcw.push(pe.val); hcw.push(pe.label); }
            hcw.push(0xFFFFFFFF);
            for x in push_stack { hcw.push(x as! u32); }
        }
        let c = csum_words(hcw);
        all = (all ^ c) * 0x9e3779b97f4a7c15;
        if verbose {
            o.append(match part { 0 => " src ", 1 => " names ", 2 => " idents ", 3 => " macros ", 4 => " mtoks ", 5 => " toks ",
                6 => " files ", _ => " misc " });
            hexd(o, c, 16);
        }
    }
    var line: u8[>..] = [];
    line.append("goosecc: pp state ");
    hexd(line, all, 16);
    line.append(o);
    line.push('\n');
    write_stderr(line);
}
