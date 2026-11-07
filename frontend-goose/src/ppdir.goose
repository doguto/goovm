// goosecc: preprocessor directives, the include stack, conditional
// skipping and pragmas.

import .common;
import .lex;
import .pp;
import .print;

// Directive keyword codes (Ident.ppkw).
let PK_IF = 1;
let PK_IFDEF = 2;
let PK_IFNDEF = 3;
let PK_ELIF = 4;
let PK_ELSE = 5;
let PK_ENDIF = 6;
let PK_DEFINE = 7;
let PK_UNDEF = 8;
let PK_INCLUDE = 9;
let PK_INCLUDE_NEXT = 10;
let PK_IMPORT = 11;
let PK_LINE = 12;
let PK_ERROR = 13;
let PK_WARNING = 14;
let PK_PRAGMA = 15;
let PK_IDENT = 16;
let PK_SCCS = 17;
let PK_ELIFDEF = 18;
let PK_ELIFNDEF = 19;
let PK_ASSERT = 20;
let PK_UNASSERT = 21;

// ---------------------------------------------------------------------------
// Include search.

struct Dir { path: u32, len: u32, sys: bool }
var dirs: Dir[>..] = [];
var quote_dirs_end: i64 = 0;   // dirs[0..quote_dirs_end] are -iquote
var angle_start: i64 = 0;      // <...> starts here (-I)
var sys_start: i64 = 0;        // system directories from here

// The path cache: what was found at each path looked up (a file, or -1),
// and which directories do not exist. It only remembers what the file
// system answered: nothing else depends on its contents or its order, so
// the header cache may skip or add entries (B4). Its keys are in their
// own arena, pnames.
struct PathEnt { off: u32, len: u32, hash: u32, file: i32 }
var pathents: PathEnt[>..] = [];
var pathtab: u32[>..<] = [];
var pathmask: i64 = 0;
var pnames: u8[>..] = [];
var pbuf: u8[>..] = [];        // path being built

fn path_grow() {
    let n = if pathtab.len == 0 { 1024 } else { pathtab.len * 2 };
    pathtab.clear();
    pathtab.resize(n, 0);
    pathmask = n - 1;
    for e, i in pathents {
        var p = (e.hash as i64) & pathmask;
        while pathtab[p] != 0 { p = (p + 1) & pathmask; }
        pathtab[p] = (i + 1) as! u32;
    }
}

// Normalizes pbuf into nbuf: drops "." components and empty ones, folds
// "x/.." textually.
fn normalize_path(nbuf: u8[>..]&) {
    var i = 0;
    let n = pbuf.len;
    if n > 0 && pbuf[0] == '/' { nbuf.push('/'); }
    var comps = 0;
    while i < n {
        while i < n && pbuf[i] == '/' { i++; }
        let s = i;
        while i < n && pbuf[i] != '/' { i++; }
        let len = i - s;
        if len == 0 { continue; }
        if len == 1 && pbuf[s] == '.' { continue; }
        if len == 2 && pbuf[s] == '.' && pbuf[s + 1] == '.' && comps > 0 {
            // drop the last component unless it is ".."
            var j = nbuf.len - 1;
            while j > 0 && nbuf[j - 1] != '/' { j--; }
            if !(nbuf.len - j == 2 && nbuf[j] == '.' && nbuf[j + 1] == '.') {
                nbuf.resize(if j > 0 { j - 1 } else { 0 });
                if nbuf.len == 0 && n > 0 && pbuf[0] == '/' { nbuf.push('/'); }
                comps--;
                continue;
            }
        }
        if nbuf.len > 0 && nbuf[nbuf.len - 1] != '/' { nbuf.push('/'); }
        nbuf.append(pbuf[s..i]);
        comps++;
    }
}

// Appends the file at path (anything but a directory) to out with one open,
// fstat, read and close: 1, or 0 if there is no such file (goosecc_rt.h).
extern fn read_source(path: const u8[:], out: u8[>..]&) -> i64 = "goosecc_read_file";

// The slot of key's entry in pathtab, or the empty one where it goes. The
// entries are files (file >= -1) and directories (file <= -2, below),
// apart by `dir`.
fn path_slot(key: const u8[:], h: u32, dir: bool) -> i64 {
    var p = (h as i64) & pathmask;
    loop {
        let e = pathtab[p];
        if e == 0 { return p; }
        let pe = pathents[e - 1];
        if pe.hash == h && pe.len == key.len && (pe.file <= -2) == dir && pnames[pe.off..pe.off + pe.len] == key { return p; }
        p = (p + 1) & pathmask;
    }
}

// The length of pbuf's directory part (before its last '/'); 0 for none
// or the root.
fn pbuf_dir_len() -> i64 {
    var j = pbuf.len;
    while j > 0 && pbuf[j - 1] != '/' { j--; }
    return if j > 1 { j - 1 } else { 0 };
}

// Is p what normalize_path makes of it: no empty, "." or ".." component,
// no '/' at the end?
fn path_is_normal(p: const u8[:]) -> bool {
    if p.len == 0 || p[p.len - 1] == '/' { return false; }
    var i = 0;
    while i < p.len {
        let c = p[i];
        if c == '/' {
            if i > 0 && p[i - 1] == '/' { return false; }
        } else if c == '.' && (i == 0 || p[i - 1] == '/') {
            if i + 1 == p.len || p[i + 1] == '/' { return false; }
            if p[i + 1] == '.' && (i + 2 == p.len || p[i + 2] == '/') { return false; }
        }
        i++;
    }
    return true;
}

// The directories that files were looked for in and not found are entries
// of pathents too: their spelling as searched (not normalized: ".." is the
// kernel's to resolve), file -2 when it is not a directory, -3 when it is.
// No file under a -2 one can be opened, so most of the misses of a search
// path (bits/stdio.h in every -I directory) cost no system call.
fn dir_missing(dl: i64) -> bool {
    let e = pathtab[path_slot(pbuf[..dl], hash_bytes(pbuf[..dl]), true)];
    return e != 0 && pathents[e - 1].file == -2;
}

fn note_dir(dl: i64) {
    if (pathents.len + 1) * 2 > pathtab.len { path_grow(); }
    let h = hash_bytes(pbuf[..dl]);
    let p = path_slot(pbuf[..dl], h, true);
    if pathtab[p] != 0 { return; }
    let isdir = is_dir(pbuf[..dl]);
    let off = pnames.len as! u32;
    pnames.append(pbuf[..dl]);
    pathents.push(PathEnt { off: off, len: dl as! u32, hash: h, file: if isdir { -3 } else { -2 } });
    pathtab[p] = pathents.len as! u32;
}

// The file at path pbuf, loaded once; -1 if there is none. The cache key
// is the normalized path (pbuf itself when it is normal already).
fn lookup_file() -> i64 {
    var nbuf: u8[>..] = [];
    let normal = path_is_normal(pbuf);
    if !normal { normalize_path(nbuf); }
    let key: const u8[:] = if normal { pbuf[..] } else { nbuf[..] };
    let h = hash_bytes(key);
    if (pathents.len + 1) * 2 > pathtab.len { path_grow(); }
    let p = path_slot(key, h, false);
    let e = pathtab[p];
    if e != 0 {
        let fe = pathents[e - 1].file as i64;
        if rec_on { hk_path_hit(e - 1, fe, key, pbuf); }
        return fe;
    }
    let dl = pbuf_dir_len();
    var f: i64 = -1;
    if dl == 0 || !dir_missing(dl) { f = load_file(pbuf); }
    let off = pnames.len as! u32;
    pnames.append(key);
    pathents.push(PathEnt { off: off, len: key.len as! u32, hash: h, file: f as! i32 });
    pathtab[p] = pathents.len as! u32;
    if f >= 0 {
        files[f].path = name_add(key);
        files[f].path_len = key.len as! u32;
    } else if dl > 0 {
        note_dir(dl);
    }
    if rec_on { hk_path_miss(key, pbuf, f); }
    return f;
}

// The path cache's entry for the normalized path key (h its hash): the
// file (>= 0), -1 for no file, -2 when key is not in the cache, -3 when
// it is not but its directory (key[..pdir], pdir > 0) is known not to
// exist. The entry's index goes to path_known_e (-1 for none).
var path_known_e: i64 = -1;
fn path_known(key: const u8[:], h: u32, pdir: i64) -> i64 {
    path_known_e = -1;
    if pathtab.len == 0 { return -2; }
    let e = pathtab[path_slot(key, h, false)];
    if e != 0 {
        path_known_e = (e - 1) as i64;
        return pathents[e - 1].file as i64;
    }
    if pdir > 0 {
        let d = pathtab[path_slot(key[..pdir], hash_bytes(key[..pdir]), true)];
        if d != 0 && pathents[d - 1].file == -2 { return -3; }
    }
    return -2;
}

// Adds key to the path cache (the header cache's replay: what it verified
// with the file system), unless it is there.
fn path_add(key: const u8[:], f: i64) {
    let h = hash_bytes(key);
    if (pathents.len + 1) * 2 > pathtab.len { path_grow(); }
    let p = path_slot(key, h, false);
    if pathtab[p] != 0 { return; }
    let off = pnames.len as! u32;
    pnames.append(key);
    pathents.push(PathEnt { off: off, len: key.len as! u32, hash: h, file: f as! i32 });
    pathtab[p] = pathents.len as! u32;
}

fn load_file(path: const u8[:]) -> i64 {
    let start = src.len;
    if read_source(path, src) == 0 { return -1; }
    var s = start;
    // A UTF-8 byte order mark is skipped.
    if src.len - s >= 3 && src[s] == 239 && src[s + 1] == 187 && src[s + 2] == 191 { s += 3; }
    var e = src.len;
    if opt_trigraphs && has_trigraphs(s, e) {
        var trig_buf: u8[>..] = [];
        replace_trigraphs(s, e, trig_buf);
        s = src.len;
        src.append(trig_buf);
        e = src.len;
    }
    src.push(0);
    src.push(0);
    let f = files.len;
    files.push(FileRec { path: 0, path_len: 0, start: s as! u32, end: e as! u32, grd: -1, once: false, system: false, lines_first: -1, lines_count: 0, sp_off: 0, sp_len: 0,
        dev: last_stat(0) as! u64, ino: last_stat(1) as! u64, fsize: last_stat(2) as! u64, mtime: last_stat(3), ctime: last_stat(4),
        rt: 0, rw: 0 });
    if last_stat(5) == 0 { files[f].fsize = 0xFFFFFFFFFFFFFFFF; }   // not a regular file: never cached
    return f;
}

// Field k of the stat of the file goosecc_read_file read last (goosecc_rt.h).
extern fn last_stat(k: i64) -> i64 = "goosecc_last_stat";

fn trigraph_char(c: u8) -> u8 {
    return match c {
        '=' => '#', '(' => '[', '/' => '\\', ')' => ']', '\'' => '^', '<' => '{', '!' => '|', '>' => '}', '-' => '~',
        _ => 0,
    };
}

fn has_trigraphs(s: i64, e: i64) -> bool {
    var i = s;
    while i + 2 < e {
        if src[i] == '?' && src[i + 1] == '?' && trigraph_char(src[i + 2]) != 0 { return true; }
        i++;
    }
    return false;
}

fn replace_trigraphs(s: i64, e: i64, trig_buf: u8[>..]&) {
    var i = s;
    while i < e {
        if i + 2 < e && src[i] == '?' && src[i + 1] == '?' && trigraph_char(src[i + 2]) != 0 {
            trig_buf.push(trigraph_char(src[i + 2]));
            i += 3;
            continue;
        }
        trig_buf.push(src[i]);
        i++;
    }
}

// The directory part of a context's path ("" when there is none).
fn ctx_dir_len(ci: i64) -> i64 {
    let s = ctxs[ci].spell as i64;
    let n = ctxs[ci].spell_len as i64;
    var j = n;
    while j > 0 && names[s + j - 1] != '/' { j--; }
    if j == 0 { return -1; }
    return j - 1;     // without the trailing '/' (j-1 = 0 means the root "/")
}

// Searches for an include. Leaves the spelling in pbuf; returns the file
// and the index of the directory it was found in (-1 = relative to the
// includer or absolute).
var found_dir: i64 = -1;
fn find_include(name: const u8[:], angled: bool, next: bool) -> i64 {
    found_dir = -1;
    if name.len > 0 && name[0] == '/' {
        pbuf.clear();
        pbuf.append(name);
        return lookup_file();
    }
    var start: i64 = if angled { angle_start } else { 0 };
    let ci = cur_file_ctx;
    if next && ctxs[ci].dir_idx >= 0 {
        start = (ctxs[ci].dir_idx as i64) + 1;
    } else if !angled {
        // The directory of the current file.
        let dl = ctx_dir_len(ci);
        pbuf.clear();
        if dl >= 0 {
            let s = ctxs[ci].spell as i64;
            pbuf.append(names[s..s + dl]);
            pbuf.push('/');
        }
        pbuf.append(name);
        let f = lookup_file();
        if f >= 0 { return f; }
    }
    var d = start;
    while d < dirs.len {
        let dr = dirs[d];
        pbuf.clear();
        pbuf.append(names[dr.path..dr.path + dr.len]);
        if pbuf.len == 0 || pbuf[pbuf.len - 1] != '/' { pbuf.push('/'); }
        pbuf.append(name);
        let f = lookup_file();
        if f >= 0 {
            found_dir = d;
            return f;
        }
        d++;
    }
    return -1;
}

// ---------------------------------------------------------------------------
// The include stack.

fn save_lexer() {
    let ci = cur_file_ctx;
    ctxs[ci].pos = lx_pos as! u32;
    ctxs[ci].end = lx_end as! u32;
    ctxs[ci].lflags = lx_flags;
}

fn restore_lexer(ci: i64) {
    cur_file_ctx = ci;
    lx_pos = ctxs[ci].pos as i64;
    lx_end = ctxs[ci].end as i64;
    lx_flags = ctxs[ci].lflags;
    lx_file = ctxs[ci].file as i64;
    lx_sys = ctxs[ci].sys;
}

fn push_file(f: i64, spell: const u8[:], dir_idx: i64, sys: bool) {
    if ctxs.len > 0 { save_lexer(); }
    let so = name_add(spell);
    let sl = spell.len as! u32;
    if files[f].sp_len == 0 {
        if rec_on { hk_fwrite(f); }
        files[f].sp_off = so;
        files[f].sp_len = sl;
    }
    let s: u8 = if sys || files[f].system { F_SYSHDR } else { 0 };
    ctxs.push(Ctx {
        kind: CTX_FILE, buf: 0, noexp: false, stamp: false, pend: 0, nextspace: false,
        cur: 0, lim: 0, start: 0, macro: -1, xloc: 0, xbase: xbuf.len as! u32, sbase: streams.len as! u32,
        file: f as! i32, pos: files[f].start, end: files[f].end, lflags: F_BOL, sys: s,
        cond_base: conds.len as! u32, spell: so, spell_len: sl, pspell: so, pspell_len: sl,
        dir_idx: dir_idx as! i32, line_delta: 0, mi_state: MI_START, mi_macro: -1,
    });
    restore_lexer(ctxs.len - 1);
    if rec_on { hk_push(); }
    if mode_E { pr_file_enter(so, sl, s != 0); }
}

fn include_depth() -> i64 {
    var n = 0;
    for c in ctxs { if c.kind == CTX_FILE { n++; } }
    return n;
}

// The end of the current file. Returns false at the end of the main file.
fn end_of_file() -> bool {
    let ci = cur_file_ctx;
    let c = ctxs[ci];
    if conds.len > c.cond_base {
        error_at(conds[conds.len - 1].loc as i64, "unterminated conditional directive");
        conds.resize(c.cond_base as i64);
    }
    if c.mi_state == MI_AFTER && c.mi_macro >= 0 {
        if rec_on { hk_fwrite(c.file as i64); }
        files[c.file].grd = c.mi_macro;
    }
    if ci == 0 { return false; }
    ctxs.pop();
    // The includer is the file context below.
    var j = ctxs.len - 1;
    while ctxs[j].kind != CTX_FILE { j--; }
    restore_lexer(j);
    // the end of a header the cache is recording (B4)
    if rec_on && recs[recs.len - 1].ctxd as i64 == ctxs.len + 1 { hc_unit_end(); }
    back_in_includer();
    return true;
}

// The end of an included file, back in the includer (whose lexer state is
// restored): the next token starts a line; -E writes the line marker.
fn back_in_includer() {
    lx_flags = F_BOL;
    if mode_E {
        let j = cur_file_ctx;
        let line, col = line_col(lx_file, lx_pos);
        pr_file_return(line + 1 + ctxs[j].line_delta, ctxs[j].pspell, ctxs[j].pspell_len, ctxs[j].sys != 0);
    }
}

// ---------------------------------------------------------------------------
// Conditionals.

struct Cond { loc: u32, taken: bool, in_else: bool }
var conds: Cond[>..<] = [];

// ---------------------------------------------------------------------------
// Directives.

var dir_text: u8[>..] = [];

recursive fn handle_directive(hash: Tok) {
    lx_dir = true;
    let t = lex_file_token();
    // Multiple-include detection (clang MultipleIncludeOpt): any directive
    // but the null one counts as a token outside the guard.
    let ci = cur_file_ctx;
    let ms = ctxs[ci].mi_state;
    if t.kind != TK_EOD && (ms == MI_START || ms == MI_AFTER) { ctxs[ci].mi_state = MI_INVALID; }
    if t.kind == TK_EOD {
    } else if t.kind == TK_NUMBER {
        do_line(t, true);
    } else if t.kind == TK_IDENT {
        let k = idents[t.val].ppkw as i64;
        if in_macro_args > 0 && (k == PK_INCLUDE || k == PK_INCLUDE_NEXT || k == PK_IMPORT || k == PK_PRAGMA) {
            error_at(t.xloc as i64, "embedding a directive within macro arguments is not supported");
        } else if k == PK_IF || k == PK_IFDEF || k == PK_IFNDEF {
            do_if(t, k, ms);
        } else if k == PK_ELIF || k == PK_ELIFDEF || k == PK_ELIFNDEF || k == PK_ELSE {
            do_else_in_taken(t, k);
        } else if k == PK_ENDIF {
            do_endif(t);
        } else if k == PK_DEFINE {
            do_define();
        } else if k == PK_UNDEF {
            do_undef();
        } else if k == PK_INCLUDE || k == PK_INCLUDE_NEXT || k == PK_IMPORT {
            do_include(t, k);
            return;
        } else if k == PK_LINE {
            do_line(t, false);
        } else if k == PK_ERROR || k == PK_WARNING {
            dir_text.clear();
            lex_rest_of_line(dir_text);
            var j = 0;
            while j < dir_text.len && cc[dir_text[j]] & CC_HSPACE != 0 { j++; }
            if k == PK_ERROR {
                error_at(t.xloc as i64, dir_text[j..]);
            } else {
                warn_at(t.xloc as i64, dir_text[j..]);
            }
        } else if k == PK_PRAGMA {
            do_pragma(t, false);
        } else if k == PK_IDENT || k == PK_SCCS {
            dir_text.clear();
            lex_rest_of_line(dir_text);
            if mode_E {
                var j = 0;
                while j < dir_text.len && cc[dir_text[j]] & CC_HSPACE != 0 { j++; }
                pr_directive_line(str("#ident ", dir_text[j..]));
            }
        } else if k == PK_ASSERT || k == PK_UNASSERT {
            lex_skip_line();
        } else {
            error_at(t.xloc as i64, "invalid preprocessing directive");
        }
    } else {
        error_at(t.xloc as i64, "invalid preprocessing directive");
    }
    lex_skip_line();
    lx_dir = false;
}

// Reads tokens to the end of the directive (warning if there are any).
fn finish_directive() {
    lex_skip_line();
}

fn dir_ident() -> Tok {
    let t = lex_file_token();
    if t.kind != TK_IDENT {
        if t.kind == TK_EOD { error_at(t.xloc as i64, "macro name missing"); }
        else { error_at(t.xloc as i64, "macro name must be an identifier"); }
    }
    return t;
}

recursive fn do_if(t: Tok, k: i64, ms: u8) {
    let ci = cur_file_ctx;
    let top_level = conds.len == ctxs[ci].cond_base;
    var val = false;
    var grdm: i64 = -1;
    if k == PK_IF {
        val = eval_if_expr();
    } else {
        let n = dir_ident();
        if n.kind == TK_IDENT {
            if rec_on { hk_mtest(n.val); }
            let defined = idents[n.val].macro >= 0;
            val = if k == PK_IFDEF { defined } else { !defined };
            if k == PK_IFNDEF && !defined { grdm = n.val as i64; }
        }
        finish_directive();
    }
    if top_level {
        if ms == MI_START && grdm >= 0 {
            ctxs[ci].mi_state = MI_GUARD;
            ctxs[ci].mi_macro = grdm as! i32;
        } else {
            ctxs[ci].mi_state = MI_INVALID;
        }
    }
    conds.push(Cond { loc: t.xloc, taken: val, in_else: false });
    if !val { skip_block(); }
}

// #elif / #else reached while processing a taken branch: skip to #endif.
recursive fn do_else_in_taken(t: Tok, k: i64) {
    let ci = cur_file_ctx;
    if conds.len <= ctxs[ci].cond_base {
        error_at(t.xloc as i64, if k == PK_ELSE { "#else without #if" } else { "#elif without #if" });
        return;
    }
    let top = conds.len - 1;
    if conds[top].in_else { error_at(t.xloc as i64, if k == PK_ELSE { "#else after #else" } else { "#elif after #else" }); }
    if k == PK_ELSE { conds[top].in_else = true; }
    if conds.len == ctxs[ci].cond_base + 1 && ctxs[ci].mi_state == MI_GUARD { ctxs[ci].mi_state = MI_INVALID; }
    finish_directive();
    skip_block();
}

fn do_endif(t: Tok) {
    let ci = cur_file_ctx;
    if conds.len <= ctxs[ci].cond_base {
        error_at(t.xloc as i64, "#endif without #if");
        return;
    }
    conds.pop();
    if conds.len == ctxs[ci].cond_base && ctxs[ci].mi_state == MI_GUARD { ctxs[ci].mi_state = MI_AFTER; }
    finish_directive();
}

// Advances to just after the next '#' that starts a directive line.
// False at the end of the file.
fn skip_to_directive() -> bool {
    var p = lx_pos;
    var at_bol = false;
    loop {
        let c = src[p];
        if c == '\n' { p++; at_bol = true; continue; }
        if c == 0 && p >= lx_end { lx_pos = p; return false; }
        if cc[c] & CC_HSPACE != 0 { p++; continue; }
        if c == '\\' {
            let s = splice_at(p);
            if s > 0 { p += s; continue; }
        }
        if c == '/' && src[p + 1] == '*' {
            p = skip_block_comment(p);
            continue;
        }
        if c == '/' && src[p + 1] == '/' {
            while p < lx_end && src[p] != '\n' {
                if src[p] == '\\' {
                    let s = splice_at(p);
                    if s > 0 { p += s; continue; }
                }
                p++;
            }
            continue;
        }
        if at_bol && c == '#' { lx_pos = p + 1; return true; }
        if at_bol && c == '%' && src[p + 1] == ':' { lx_pos = p + 2; return true; }
        at_bol = false;
        if c == '"' || c == '\'' {
            p++;
            while p < lx_end && src[p] != c && src[p] != '\n' {
                if src[p] == '\\' {
                    let s = splice_at(p);
                    if s > 0 { p += s; continue; }
                    p += 2;
                    continue;
                }
                p++;
            }
            if src[p] == c { p++; }
            continue;
        }
        // The rest of the line up to what the loop must look at (at_bol
        // is false: '#' and '%' are plain here), 16 bytes at a time.
        p = skip_text(src, p + 1);
    }
}

// Skips a group whose condition is false, or the remaining groups of a
// conditional whose branch was taken. Stops after the #elif/#else that
// starts a group to process, or after the #endif.
recursive fn skip_block() {
    let ci = cur_file_ctx;
    var depth = 0;
    loop {
        if !skip_to_directive() { return; }
        lx_dir = true;
        lx_flags = 0;
        let t = lex_file_token();
        if t.kind == TK_IDENT {
            let k = idents[t.val].ppkw as i64;
            if k == PK_IF || k == PK_IFDEF || k == PK_IFNDEF {
                depth++;
            } else if k == PK_ENDIF {
                if depth == 0 {
                    conds.pop();
                    if conds.len == ctxs[ci].cond_base && ctxs[ci].mi_state == MI_GUARD { ctxs[ci].mi_state = MI_AFTER; }
                    lex_skip_line();
                    lx_dir = false;
                    return;
                }
                depth--;
            } else if depth == 0 && (k == PK_ELSE || k == PK_ELIF || k == PK_ELIFDEF || k == PK_ELIFNDEF) {
                let top = conds.len - 1;
                if conds[top].in_else { error_at(t.xloc as i64, "#elif or #else after #else"); }
                if conds.len == ctxs[ci].cond_base + 1 && ctxs[ci].mi_state == MI_GUARD { ctxs[ci].mi_state = MI_INVALID; }
                if k == PK_ELSE {
                    conds[top].in_else = true;
                    if !conds[top].taken {
                        conds[top].taken = true;
                        lex_skip_line();
                        lx_dir = false;
                        return;
                    }
                } else if !conds[top].taken {
                    var v = false;
                    if k == PK_ELIF {
                        v = eval_if_expr();
                    } else {
                        let n = dir_ident();
                        if n.kind == TK_IDENT {
                            if rec_on { hk_mtest(n.val); }
                            let defined = idents[n.val].macro >= 0;
                            v = if k == PK_ELIFDEF { defined } else { !defined };
                        }
                    }
                    if v {
                        conds[top].taken = true;
                        lex_skip_line();
                        lx_dir = false;
                        return;
                    }
                }
            }
        }
        lex_skip_line();
        lx_dir = false;
    }
}

// ---------------------------------------------------------------------------
// #define / #undef

var params: u32[>..<] = [];

fn param_index(id: u32) -> i64 {
    for p, i in params { if p == id { return i; } }
    return -1;
}

fn do_define() {
    let n = dir_ident();
    if n.kind != TK_IDENT { return; }
    if n.val == id_defined { error_at(n.xloc as i64, "'defined' cannot be used as a macro name"); return; }
    var flags: u8 = 0;
    params.clear();
    let first = mtoks.len;
    var gnu_va = false;
    if src[lx_pos] == '(' {
        // Function-like: the parameter list.
        flags = M_FUNC;
        lx_pos++;
        var t = lex_file_token();
        if t.kind != TK_R_PAREN {
            loop {
                if t.kind == TK_ELLIPSIS {
                    flags = flags | M_VARIADIC;
                    params.push(id_va_args);
                    t = lex_file_token();
                    if t.kind != TK_R_PAREN { error_at(t.xloc as i64, "missing ')' in macro parameter list"); return; }
                    break;
                }
                if t.kind != TK_IDENT { error_at(t.xloc as i64, "invalid token in macro parameter list"); return; }
                if param_index(t.val) >= 0 { error_at(t.xloc as i64, "duplicate macro parameter name"); return; }
                params.push(t.val);
                t = lex_file_token();
                if t.kind == TK_ELLIPSIS {
                    flags = flags | M_VARIADIC | M_GNUVA;
                    gnu_va = true;
                    t = lex_file_token();
                    if t.kind != TK_R_PAREN { error_at(t.xloc as i64, "missing ')' in macro parameter list"); return; }
                    break;
                }
                if t.kind == TK_R_PAREN { break; }
                if t.kind != TK_COMMA { error_at(t.xloc as i64, "expected comma in macro parameter list"); return; }
                t = lex_file_token();
            }
        }
    }
    // The body.
    var t = lex_file_token();
    var firsttok = true;
    while t.kind != TK_EOD {
        var bt = t;
        bt.flags = bt.flags & ~(F_BOL | F_SYSHDR);
        if firsttok { bt.flags = bt.flags & ~F_LSPACE; firsttok = false; }
        if flags & M_FUNC != 0 && t.kind == TK_IDENT {
            let pi = param_index(t.val);
            if pi >= 0 && !(t.val == id_va_args && gnu_va) {
                bt.kind = TK_PARAM;
                bt.aux = pi as! u16;
            }
        }
        mtoks.push(bt);
        t = lex_file_token();
    }
    let count = mtoks.len - first;
    // Checks on # and ##.
    if count > 0 {
        if mtoks[first].kind == TK_HASHHASH { error_at(mtoks[first].xloc as i64, "'##' cannot appear at either end of a macro expansion"); mtoks.resize(first); return; }
        if mtoks[mtoks.len - 1].kind == TK_HASHHASH { error_at(mtoks[mtoks.len - 1].xloc as i64, "'##' cannot appear at either end of a macro expansion"); mtoks.resize(first); return; }
        if flags & M_FUNC != 0 {
            for j in first..mtoks.len {
                if mtoks[j].kind == TK_HASH {
                    let ok = j + 1 < mtoks.len && (mtoks[j + 1].kind == TK_PARAM ||
                        (mtoks[j + 1].kind == TK_IDENT && mtoks[j + 1].val == id_va_opt && flags & M_VARIADIC != 0));
                    if !ok { error_at(mtoks[j].xloc as i64, "'#' is not followed by a macro parameter"); mtoks.resize(first); return; }
                }
            }
        }
    }
    if flags & M_FUNC != 0 {
        var simple = true;
        for j in first..mtoks.len {
            let k = mtoks[j].kind;
            if k == TK_HASH || k == TK_HASHHASH || (k == TK_IDENT && mtoks[j].val == id_va_opt) { simple = false; }
        }
        if simple { flags = flags | M_SIMPLE; }
    }
    let m = macros.len;
    macros.push(Macro { name: n.val, first: first as! u32, count: count as! u32, nparams: params.len as! u16,
        flags: flags, builtin: 0, enabled: true, loc: n.xloc });
    if rec_on { hk_mwrite(n.val); }
    idents[n.val].macro = m as! i32;
}

fn do_undef() {
    let n = dir_ident();
    if n.kind != TK_IDENT { return; }
    if rec_on { hk_mwrite(n.val); }
    idents[n.val].macro = -1;
    finish_directive();
}

// ---------------------------------------------------------------------------
// #include

var inc_name: u8[>..] = [];

recursive fn do_include(t: Tok, k: i64) {
    let ht = lex_header_name();
    inc_name.clear();
    var angled = false;
    var ok = true;
    if ht.kind == TK_HEADER {
        angled = true;
        inc_name.append(src[ht.spell + 1..ht.spell + ht.val - 1]);
        finish_directive();
    } else if ht.kind == TK_STRING && src[ht.spell] == '"' {
        inc_name.append(src[ht.spell + 1..ht.spell + ht.val - 1]);
        finish_directive();
    } else if ht.kind == TK_EOD {
        error_at(ht.xloc as i64, "expected \"FILENAME\" or <FILENAME>");
        ok = false;
    } else {
        // A computed include: macro-expand the line.
        let s0 = streams.len;
        streams.push(ht);
        enter_stream(s0, false);
        var x = pp_lex();
        if x.kind == TK_STRING && src[x.spell] == '"' {
            inc_name.append(src[x.spell + 1..x.spell + x.val - 1]);
            x = pp_lex();
        } else if x.kind == TK_LESS {
            angled = true;
            x = pp_lex();
            var firstt = true;
            while x.kind != TK_GREATER && x.kind != TK_EOD {
                if !firstt && x.flags & F_LSPACE != 0 { inc_name.push(' '); }
                firstt = false;
                tok_spelling(inc_name, x);
                x = pp_lex();
            }
            if x.kind == TK_GREATER { x = pp_lex(); } else { ok = false; }
        } else {
            ok = false;
        }
        if !ok { error_at(t.xloc as i64, "expected \"FILENAME\" or <FILENAME>"); }
        while x.kind != TK_EOD { x = pp_lex(); }
    }
    lex_skip_line();
    lx_dir = false;
    if !ok { return; }
    if include_depth() > 200 {
        error_at(t.xloc as i64, "#include nested too deeply");
        return;
    }
    // B4: the header cache replays the whole include (the search, the file
    // and everything it includes) when what it depends on is unchanged;
    // otherwise it records it. The includes of system headers are part of
    // the include of a system header from the program's own files.
    var rec = false;
    if hc_on && ctxs[cur_file_ctx].sys == 0 && !hc_would_skip(inc_name, angled, k) {
        if hc_replay(inc_name, angled, k) { return; }
        rec = hc_rec_start(inc_name, angled, k);
    }
    let f = find_include(inc_name, angled, k == PK_INCLUDE_NEXT);
    if f < 0 {
        error_at(ht.xloc as i64, str("'", inc_name, "' file not found"));
        fatal("compilation terminated");
        return;
    }
    if files[f].once {
        if rec { hc_rec_drop(); }
        return;
    }
    let g = files[f].grd as i64;
    if g >= 0 {
        if rec_on { hk_mtest(g as! u32); }
        if idents[g].macro >= 0 {
            if rec { hc_rec_drop(); }
            return;
        }
    }
    if k == PK_IMPORT {
        // #import: include at most once
        if files[f].sp_len != 0 {
            if rec { hc_rec_drop(); }
            return;
        }
    }
    let sys = found_dir >= sys_start || (ctxs[cur_file_ctx].sys != 0 && found_dir < 0);
    // pbuf holds the spelling of the path that was found
    let dirx = found_dir;
    inc_name.clear();
    inc_name.append(pbuf);
    push_file(f, inc_name, dirx, sys);
    if rec { hc_rec_entered(); }
}

// ---------------------------------------------------------------------------
// #line and GNU line markers.

recursive fn do_line(t: Tok, gnu: bool) {
    var nt = t;
    if !gnu {
        nt = pp_lex();
    }
    if nt.kind != TK_NUMBER {
        error_at(nt.xloc as i64, "#line directive requires a simple digit sequence");
        return;
    }
    var v: i64 = 0;
    for c in src[nt.spell..nt.spell + nt.val] {
        if c < '0' || c > '9' { error_at(nt.xloc as i64, "#line directive requires a simple digit sequence"); return; }
        v = v * 10 + (c - '0');
    }
    let ci = cur_file_ctx;
    var ft = if gnu { lex_file_token() } else { pp_lex() };
    if ft.kind == TK_STRING {
        // The presumed file name (escapes kept as written, except \\ and \").
        dir_text.clear();
        let s = src[ft.spell + 1..ft.spell + ft.val - 1];
        var j = 0;
        while j < s.len {
            if s[j] == '\\' && j + 1 < s.len { j++; }
            dir_text.push(s[j]);
            j++;
        }
        let o = name_add(dir_text);
        ctxs[ci].pspell = o;
        ctxs[ci].pspell_len = dir_text.len as! u32;
        ft = if gnu { lex_file_token() } else { pp_lex() };
    }
    if gnu {
        while ft.kind == TK_NUMBER {
            if ft.val == 1 && src[ft.spell] == '3' { ctxs[ci].sys = F_SYSHDR; lx_sys = F_SYSHDR; }
            ft = lex_file_token();
        }
    }
    while ft.kind != TK_EOD { ft = if gnu { lex_file_token() } else { pp_lex() }; }
    // The line after this directive is line v.
    let line, col = line_col(lx_file, lx_pos);
    ctxs[ci].line_delta = (v - (line + 1)) as! i32;
    if mode_E {
        pr_marker(v, ctxs[ci].pspell, ctxs[ci].pspell_len, "");
        pr_line = v - 1;
    }
}

// ---------------------------------------------------------------------------
// #pragma

struct PackEnt { val: u32, label: u32 }
var pack_stack: PackEnt[>..<] = [];
var pack_cur: u32 = 0;
var ptoks: Tok[>..<] = [];
var push_stack: i32[>..<] = [];        // push_macro: ident, macro index pairs

fn ptok_is(i: i64, s: const u8[:]) -> bool {
    return i < ptoks.len && ptoks[i].kind == TK_IDENT && ident_text(ptoks[i].val as i64) == s;
}

fn ptok_kind(i: i64) -> i64 {
    if i < ptoks.len { return ptoks[i].kind as i64; }
    return TK_EOD;
}

fn print_pragma_tokens(from: i64) {
    dir_text.clear();
    dir_text.append("#pragma");
    for j in from..ptoks.len {
        let t = ptoks[j];
        if t.flags & F_LSPACE != 0 || j == from { dir_text.push(' '); }
        tok_spelling(dir_text, t);
    }
    pr_directive_line(dir_text);
}

fn string_body(t: Tok, out: u8[>..]&) {
    // the characters between the quotes, as written
    var s = t.spell as i64;
    let e = s + (t.val as i64);
    while src[s] != '"' { s++; }
    out.append(src[s + 1..e - 1]);
}

var tu_annot: bool = false;    // not -E: #pragma pack and ms_struct are recorded for the parser

fn emit_pack(loc: u32) {
    if tu_annot {
        pack_changes.push(tu_toks.len as! u32);
        pack_changes.push(pack_cur);
    }
}

fn do_pack() {
    // pack ( [push|pop] [, label] [, n] ) or pack(n) or pack()
    if ptok_kind(1) != TK_L_PAREN { return; }
    var i = 2;
    let loc = ptoks[0].xloc;
    if ptok_kind(i) == TK_R_PAREN { pack_cur = 0; emit_pack(loc); return; }
    if ptok_kind(i) == TK_NUMBER {
        pack_cur = pack_number(ptoks[i]);
        emit_pack(loc);
        return;
    }
    if ptok_is(i, "push") {
        i++;
        var label: u32 = 0;
        var newv: i64 = -1;
        while ptok_kind(i) == TK_COMMA {
            i++;
            if ptok_kind(i) == TK_IDENT { label = ptoks[i].val + 1; i++; }
            else if ptok_kind(i) == TK_NUMBER { newv = pack_number(ptoks[i]) as i64; i++; }
        }
        pack_stack.push(PackEnt { val: pack_cur, label: label });
        if newv >= 0 { pack_cur = newv as! u32; }
        emit_pack(loc);
        return;
    }
    if ptok_is(i, "pop") {
        i++;
        var label: u32 = 0;
        var newv: i64 = -1;
        while ptok_kind(i) == TK_COMMA {
            i++;
            if ptok_kind(i) == TK_IDENT { label = ptoks[i].val + 1; i++; }
            else if ptok_kind(i) == TK_NUMBER { newv = pack_number(ptoks[i]) as i64; i++; }
        }
        if label != 0 {
            var j = pack_stack.len - 1;
            while j >= 0 && pack_stack[j].label != label { j--; }
            if j >= 0 {
                pack_cur = pack_stack[j].val;
                pack_stack.resize(j);
            }
        } else if pack_stack.len > 0 {
            pack_cur = pack_stack.pop().val;
        }
        if newv >= 0 { pack_cur = newv as! u32; }
        emit_pack(loc);
        return;
    }
    if ptok_is(i, "show") { return; }
}

fn pack_number(t: Tok) -> u32 {
    var v: u32 = 0;
    for c in src[t.spell..t.spell + t.val] {
        if c >= '0' && c <= '9' { v = v * 10 + (c - '0'); }
    }
    return v;
}

fn is_known_warning(name: const u8[:]) -> bool {
    if name.len < 2 || name[0] != '-' || name[1] != 'W' { return false; }
    return warning_known(name[2..]);
}

// Handles the pragma whose tokens follow on the current (directive) line.
recursive fn do_pragma(t: Tok, from_op: bool) {
    ptoks.clear();
    var x = lex_file_token();
    // #pragma omp: macro-expanded (clang does so even without -fopenmp)
    if x.kind == TK_IDENT && ident_text(x.val as i64) == "omp" && !from_op {
        ptoks.push(x);
        x = pp_lex();
        while x.kind != TK_EOD { ptoks.push(x); x = pp_lex(); }
    } else {
        while x.kind != TK_EOD { ptoks.push(x); x = lex_file_token(); }
    }
    if ptoks.len == 0 { if mode_E { pr_directive_line("#pragma"); } return; }
    var print = true;
    if ptok_is(0, "once") {
        if cur_file_ctx > 0 {
            if rec_on { hk_fwrite(lx_file); }
            files[lx_file].once = true;
        }
        print = false;
    } else if ptok_is(0, "push_macro") || ptok_is(0, "pop_macro") {
        print = false;
        if ptok_kind(1) == TK_L_PAREN && ptok_kind(2) == TK_STRING {
            dir_text.clear();
            string_body(ptoks[2], dir_text);
            let id = intern(dir_text);
            if ptok_is(0, "push_macro") {
                if rec_on { hk_mread(id); }
                push_stack.push(id as! i32);
                push_stack.push(idents[id].macro);
            } else {
                var j = push_stack.len - 2;
                while j >= 0 && push_stack[j] != (id as! i32) { j -= 2; }
                if j >= 0 {
                    if rec_on { hk_pop_macro(id, j); }
                    idents[id].macro = push_stack[j + 1];
                    // remove the entry
                    var q = j;
                    while q + 2 < push_stack.len { push_stack[q] = push_stack[q + 2]; q++; }
                    push_stack.pop();
                    push_stack.pop();
                }
            }
        }
    } else if ptok_is(0, "mark") || ptok_is(0, "region") || ptok_is(0, "endregion") {
        print = false;
    } else if (ptok_is(0, "GCC") || ptok_is(0, "clang")) && ptok_is(1, "system_header") {
        print = false;
        if cur_file_ctx > 0 {
            if rec_on { hk_fwrite(lx_file); }
            files[lx_file].system = true;
            ctxs[cur_file_ctx].sys = F_SYSHDR;
            lx_sys = F_SYSHDR;
        }
    } else if ptok_is(0, "GCC") && ptok_is(1, "poison") {
        print = false;
        for j in 2..ptoks.len {
            if ptoks[j].kind == TK_IDENT {
                if rec_on { hk_poison(ptoks[j].val); }
                idents[ptoks[j].val].flags = idents[ptoks[j].val].flags | ID_POISONED;
            }
        }
    } else if ptok_is(0, "GCC") && ptok_is(1, "dependency") {
        print = false;
    } else if (ptok_is(0, "GCC") || ptok_is(0, "clang")) && ptok_is(1, "diagnostic") {
        if ptok_is(2, "push") || ptok_is(2, "pop") {
        } else if ptok_kind(3) == TK_STRING {
            dir_text.clear();
            string_body(ptoks[3], dir_text);
            print = is_known_warning(dir_text);
        } else {
            print = false;
        }
    } else if ptok_is(0, "clang") && ptok_is(1, "__debug") {
        print = false;
    } else if ptok_is(0, "message") {
        // printed as message("...") with the strings concatenated
        if mode_E {
            dir_text.clear();
            dir_text.append("#pragma message(\"");
            for j in 1..ptoks.len {
                if ptoks[j].kind == TK_STRING { string_body(ptoks[j], dir_text); }
            }
            dir_text.append("\")");
            pr_directive_line(dir_text);
        }
        print = false;
    } else if ptok_is(0, "GCC") && ptok_is(1, "error") {
        error_at(t.xloc as i64, "#pragma GCC error");
    } else if ptok_is(0, "pack") {
        if rec_on { hk_pack(); }
        do_pack();
    } else if ptok_is(0, "ms_struct") {
        if rec_on { hk_pack(); }
        var v: u32 = 0;
        if ptok_is(1, "on") { v = 1; }
        if tu_annot {
            ms_changes.push(tu_toks.len as! u32);
            ms_changes.push(v);
        }
    }
    if print && mode_E { print_pragma_tokens(0); }
}

// _Pragma("..."): the destringized text is lexed as a #pragma line.
var pragma_text: u8[>..] = [];
recursive fn run_pragma_operator(st: Tok, loc: Tok) {
    pragma_text.clear();
    var s = st.spell as i64;
    let e = s + (st.val as i64);
    while src[s] != '"' { s++; }
    s++;
    while s < e - 1 {
        if src[s] == '\\' && (src[s + 1] == '\\' || src[s + 1] == '"') { s++; }
        pragma_text.push(src[s]);
        s++;
    }
    let start = src.len;
    src.append(pragma_text);
    let end = src.len;
    src.push('\n');
    src.push(0);
    // Lex it with the file lexer, then restore the file's state.
    let sp = lx_pos;
    let se = lx_end;
    let sf = lx_flags;
    let sd = lx_dir;
    lx_pos = start;
    lx_end = end;
    lx_flags = 0;
    lx_dir = true;
    do_pragma(loc, true);
    lx_pos = sp;
    lx_end = se;
    lx_flags = sf;
    lx_dir = sd;
}
