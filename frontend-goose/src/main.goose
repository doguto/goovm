// goosecc: a C17 + GNU compiler written in Goose: preprocessor, parser,
// type checker (B1), and lowering to GIR compiled in-process by the Goose
// back-end (B2). See ../DESIGN.md.
//
//   goosecc -c [options] file.c [-o file.o]  compile to an x86-64 ELF object
//   goosecc --emit-gir [options] file.c      print the GIR (to -o or stdout)
//   goosecc -E [options] file.c            preprocess to stdout (or -o)
//   goosecc -fsyntax-only [options] file.c parse and type-check
//   goosecc --layout-check [options] file.c -o check.c
//
// Options follow clang: -I -isystem -iquote -idirafter -D -U -include
// -std= -O* -g -fPIC -fcommon -pthread -w; others are accepted and ignored.

import std;
import os;
import .common;
import .lex;
import .pp;
import .ppdir;
import .ppexpr;
import .print;
import .predef_gen;
import .types;
import .dtype;
import .ast;
import .sema;
import .expr;
import .parse;
import .init;
import .builtins;
import .layout;
import .dump;
import .gen_ir;
import .gen_abi;
import .gen_ops;
import .gen_expr;
import .gen_glob;
import .gen_stmt;
import .gen_call;
import .gen_builtin;
import .gen_asm;
import .gen_debug;
import .gen_dwarf;
import .gen_tu;
import .hcache;
import .pcache;
import cg from "../../backend-goose";

let OPTS_WITH_VALUE = ["-I", "-D", "-U", "-isystem", "-iquote", "-idirafter", "-include", "-o", "-x", "-MF", "-MT", "-MQ", "-std="];
var in_off: u32 = 0;        // the input file's name (names)
var in_len: i64 = 0;
fn opt_input() -> const u8[:] { names[in_off..in_off + in_len] }
var out_off: u32 = 0;
var out_len: i64 = 0;
var opt_mode: i64 = 0;      // 0 = -fsyntax-only, 1 = -E, 2 = --layout-check, 3 = --dump-ast, 4 = -c, 5 = --emit-gir
var opt_time: bool = false;
var nostdinc: bool = false;
var opt_state_hash: i64 = 0;  // --pp-state-hash (2: =v, per array)

fn add_dir(d: const u8[:], sys: bool) {
    var s = d;
    while s.len > 1 && s[s.len - 1] == '/' { s = s[..s.len - 1]; }
    dirs.push(Dir { path: name_add(s), len: s.len as! u32, sys: sys });
}

// Adds a token to tu_toks, a keyword with its keyword kind (TK_KW + code).
fn tu_add(t0: Tok) {
    var t = t0;
    if tu_toks.len >= tok_frontier {
        prefault_toks(tu_toks, 65536);
        tok_frontier = tu_toks.len + 4096;
    }
    if t.kind == TK_IDENT {
        let kwc = idents[t.val].kw;
        if kwc != 0 { t.kind = (TK_KW + (kwc as i64)) as! u8; }
    }
    tu_toks.push(t);
}

// The translation unit's tokens to tu_toks, the EOF included (with -E to
// the printer, without the EOF): what calling pp_lex until the EOF gives,
// with pp_lex's steps done here for the common tokens:
//  * from a file, the tokens that need no preprocessing (not a directive,
//    not the end of a file, not a macro's name) are returned as they come;
//    identifiers and one-character punctuators are lexed here, as
//    lex_file_token would lex them, without a call per token, and anything
//    else (comments, literals, splices, the end of the file) is left to
//    it. Only the first token of a run can change the file's include-guard
//    state;
//  * from a macro expansion (or another token context), ctx_next's tokens
//    are returned unless they name a macro.
fn pp_fill() {
    loop {
        let ci = ctxs.len - 1;
        let ck = ctxs[ci].kind;
        if ck == CTX_MACRO && (ctxs[ci].buf == BUF_MTOKS || ctxs[ci].buf == BUF_XBUF) {
            // A macro's expansion: ctx_next's steps for the run of tokens
            // up to the next one that names a macro, the next paste (left
            // to ctx_next) or the end of the context.
            let b = ctxs[ci].buf;
            let lim = ctxs[ci].lim as i64;
            let start = ctxs[ci].start as i64;
            let stamp = ctxs[ci].stamp;
            let xl = ctxs[ci].xloc;
            let noexp = ctxs[ci].noexp;
            var cur = ctxs[ci].cur as i64;
            var pend = ctxs[ci].pend;
            var done = false;
            while cur < lim {
                if cur + 1 < lim {
                    let nk = if b == BUF_MTOKS { mtoks[cur + 1].kind } else { xbuf[cur + 1].kind };
                    if nk == TK_HASHHASH { break; }
                }
                var t = if b == BUF_MTOKS { mtoks[cur] } else { xbuf[cur] };
                if stamp {
                    t.xloc = xl;
                    t.flags = t.flags | F_MACRO;
                }
                if cur == start {
                    t.flags = (t.flags & ~(F_BOL | F_LSPACE)) | (pend & (F_BOL | F_LSPACE));
                } else {
                    t.flags = t.flags | (pend & (F_BOL | F_LSPACE));
                }
                pend = 0;
                cur++;
                if t.kind == TK_IDENT && !noexp && rec_on { hk_mtest(t.val); }
                if t.kind == TK_IDENT && !noexp && idents[t.val].macro >= 0 {
                    ctxs[ci].cur = cur as! u32;
                    ctxs[ci].pend = 0;
                    done = true;
                    let ok, m = macro_token(t);
                    if ok {
                        if m.kind == TK_EOF {
                            if !mode_E { tu_toks.push(m); }
                            return;
                        }
                        if mode_E { pr_token(m); } else { tu_add(m); }
                    }
                    break;
                }
                if t.kind == TK_EOF {
                    ctxs[ci].cur = cur as! u32;
                    ctxs[ci].pend = 0;
                    if !mode_E { tu_toks.push(t); }
                    return;
                }
                if mode_E { pr_token(t); } else { tu_add(t); }
            }
            if done { continue; }
            // a paste or the end of the context: ctx_next's, below
            ctxs[ci].cur = cur as! u32;
            ctxs[ci].pend = pend;
        }
        if ck != CTX_FILE {
            let t = ctx_next(ci);
            if t.kind == TK_CTX_END {
                pop_tok_ctx(t.flags);
                continue;
            }
            var r = t;
            if t.kind == TK_IDENT && !ctxs[ci].noexp {
                let ok, m = macro_token(t);
                if !ok { continue; }
                r = m;
            }
            if r.kind == TK_EOF {
                if !mode_E { tu_toks.push(r); }
                return;
            }
            if mode_E { pr_token(r); } else { tu_add(r); }
            continue;
        }
        let ms = ctxs[ci].mi_state;
        var mi = ms != MI_INVALID && ms != MI_GUARD;
        // The lexer's position and pending flags, in locals while the fast
        // path runs (lx_dir is false: pp_fill is not inside a directive).
        var p = lx_pos;
        var flags = lx_flags;
        let sys = lx_sys;
        loop {
            var c = src[p];
            if cc[c] & CC_HSPACE != 0 {
                p++;
                while cc[src[p]] & CC_HSPACE != 0 { p++; }
                flags |= F_LSPACE;
                c = src[p];
            }
            if c == '\n' {
                p++;
                flags = F_BOL;
                continue;
            }
            let cl = lxc[c];
            var t = Tok { kind: 0, flags: 0, aux: 0, spell: 0, val: 0, xloc: 0 };
            var have = false;
            if cl == LX_IDENT || (cl == LX_IDPREFIX && !quote_follows(p)) {
                let r = ident_scan(src, p);
                let q = p + (r >> 32) as! i64;
                let h = (r & 0xFFFFFFFF) as! u32;
                if src[q] != '\\' {
                    var fid = ident_find(p, q - p, h);
                    if fid < 0 { fid = ident_lookup(p, q - p, h) as i64; } else if rec_on { hk_look(fid as! u32, p); }
                    let id = fid as! u32;
                    if rec_on { hk_mtest(id); }
                    t = Tok { kind: TK_IDENT, flags: flags | sys, aux: 0, spell: p as! u32, val: id, xloc: p as! u32 };
                    p = q;
                    flags = 0;
                    if idents[id].macro < 0 {
                        if mi {
                            ctxs[ci].mi_state = MI_INVALID;
                            mi = false;
                        }
                        if mode_E { pr_token(t); } else { tu_add(t); }
                        continue;
                    }
                    have = true;
                }
            } else if cl == LX_PUNCT1 && src[p + 1] != '\\' {
                if mi {
                    ctxs[ci].mi_state = MI_INVALID;
                    mi = false;
                }
                t = Tok { kind: PUNCT1[c], flags: flags | sys, aux: 0, spell: p as! u32, val: 0, xloc: p as! u32 };
                if mode_E { pr_token(t); } else { tu_add(t); }
                p++;
                flags = 0;
                continue;
            }
            lx_pos = p;
            lx_flags = flags;
            if !have {
                t = lex_file_token();
                if rec_on && t.kind == TK_IDENT { hk_mtest(t.val); }
                if t.kind != TK_EOF && !(t.kind == TK_HASH && t.flags & F_BOL != 0) &&
                        !(t.kind == TK_IDENT && idents[t.val].macro >= 0) {
                    if mi {
                        ctxs[ci].mi_state = MI_INVALID;
                        mi = false;
                    }
                    if mode_E { pr_token(t); } else { tu_add(t); }
                    p = lx_pos;
                    flags = lx_flags;
                    continue;
                }
            }
            let ok, r = file_token(t, ci);
            if ok {
                if r.kind == TK_EOF {
                    if !mode_E { tu_toks.push(r); }
                    return;
                }
                if mode_E { pr_token(r); } else { tu_add(r); }
            }
            break;
        }
    }
}

fn usage() {
    write_stderr("usage: goosecc (-E | -fsyntax-only | --layout-check) [clang options] file.c [-o out]\n");
    exit(2);
}

// -o - writes to standard output
fn out_is_stdout() -> bool { out_len == 1 && names[out_off] == '-' }

// Writes an output file, replacing an existing regular file by a new one
// rather than truncating it (goosecc_rt.h): 1 on success.
extern fn write_output(path: const u8[:], data: const u8[:]) -> i64 = "goosecc_write_file";

// The options and the include search list.
fn options() {
    let a = args();
    var sys_dirs_after: u32[>..] = [];   // -idirafter: (off, len) pairs
    var isystem_dirs: u32[>..] = [];
    var i = 1;
    var quote: u32[>..] = [];
    var angled: u32[>..] = [];
    while i < a.len {
        let s = a[i];
        i++;
        // options with a separate or attached value
        var val: const u8[:] = "";
        var has_val = false;
        var which = -1;
        for opt, oi in OPTS_WITH_VALUE {
            if which < 0 && starts_with(s, opt) {
                if s.len > opt.len {
                    val = s[opt.len..];
                    has_val = true;
                    which = oi;
                } else if opt != "-std=" && i < a.len {
                    val = a[i];
                    i++;
                    has_val = true;
                    which = oi;
                }
            }
        }
        if has_val {
            if which == 0 { angled.push(name_add(val)); angled.push(val.len as! u32); }
            else if which == 1 { cmd_macros.push(CmdMacro { def: true, inc: false, off: name_add(val), len: val.len as! u32 }); }
            else if which == 2 { cmd_macros.push(CmdMacro { def: false, inc: false, off: name_add(val), len: val.len as! u32 }); }
            else if which == 3 { isystem_dirs.push(name_add(val)); isystem_dirs.push(val.len as! u32); }
            else if which == 4 { quote.push(name_add(val)); quote.push(val.len as! u32); }
            else if which == 5 { sys_dirs_after.push(name_add(val)); sys_dirs_after.push(val.len as! u32); }
            else if which == 6 { cmd_macros.push(CmdMacro { def: false, inc: true, off: name_add(val), len: val.len as! u32 }); }
            else if which == 7 { out_off = name_add(val); out_len = val.len; }
            else if which == 12 { std_off = name_add(val); std_len = val.len; }
        }
        if has_val { continue; }
        if s == "-E" { opt_mode = 1; }
        else if s == "-fsyntax-only" { opt_mode = 0; }
        else if s == "--layout-check" { opt_mode = 2; }
        else if s == "--dump-ast" { opt_mode = 3; }
        else if s == "-c" { if opt_mode == 0 { opt_mode = 4; } }
        else if s == "--emit-gir" { opt_mode = 5; }
        else if s == "-g" || starts_with(s, "-g") && s != "-g0" && !starts_with(s, "-gno") { gen::opt_debug = true; dbg_types = true; dbg_g = true; }
        else if s == "-g0" { gen::opt_debug = false; dbg_types = false; dbg_g = false; }
        else if s == "-fPIC" || s == "-fpic" { gen::opt_pic = true; gen::opt_pie = false; opt_pic_mode = if s == "-fPIC" { 2 } else { 3 }; }
        else if s == "-fPIE" || s == "-fpie" { gen::opt_pic = false; gen::opt_pie = true; opt_pic_mode = if s == "-fPIE" { 0 } else { 1 }; }
        else if s == "-fno-pic" || s == "-fno-PIC" || s == "-fno-pie" || s == "-fno-PIE" { gen::opt_pic = false; opt_pic_mode = 4; }
        else if s == "-fno-builtin" { gen::opt_no_builtin = true; }
        else if starts_with(s, "-fno-builtin-") { gen::no_builtin_opts.push(name_add(s[13..])); gen::no_builtin_opts.push((s.len - 13) as! u32); }
        else if s == "-fcommon" { gen::opt_common = true; }
        else if s == "-fno-common" { gen::opt_common = false; }
        else if s == "--time" { opt_time = true; }
        else if s == "-fno-header-cache" { hc_enabled = false; }
        else if s == "-fheader-cache" { hc_enabled = true; }
        else if s == "--cache-stats" { hc_stats_opt = true; }
        else if s == "--pp-state-hash" { opt_state_hash = 1; }
        else if s == "--pp-state-hash=v" { opt_state_hash = 2; }
        else if s == "-pthread" { opt_pthread = true; }
        else if s == "-nostdinc" { nostdinc = true; }
        else if s == "-funsigned-char" { opt_unsigned_char = true; }
        else if s == "-trigraphs" { opt_trigraphs = true; }
        else if s == "-Wno-return-type" || s == "-Wno-return-mismatch" || s == "-Wno-error=return-type" || s == "-Wno-error=return-mismatch" { opt_wno_return = true; }
        else if s == "-Wno-int-conversion" || s == "-Wno-error=int-conversion" { opt_wno_int_conv = true; }
        else if s == "-Wno-implicit-function-declaration" || s == "-Wno-error=implicit-function-declaration" { opt_wno_implicit_fn = true; }
        else if s == "-Wno-implicit-int" || s == "-Wno-error=implicit-int" { opt_wno_implicit_int = true; }
        else if s == "-Wall" || s == "-W" { quiet_warnings = false; }
        else if s == "-O0" { opt_optimize = 0; }
        else if starts_with(s, "-O") {
            opt_optimize = 1;
            if s == "-Os" || s == "-Oz" { opt_os = true; }
        }
        else if s == "-" || (s.len > 0 && s[0] != '-') { in_off = name_add(s); in_len = s.len; }
        else if !(starts_with(s, "-W") || s == "-w" || starts_with(s, "-f") || starts_with(s, "-m") || starts_with(s, "-g") ||
                  starts_with(s, "-pedantic") || s == "-pipe" || s == "-ansi" || s == "-v" || s == "-Qunused-arguments" ||
                  starts_with(s, "-M") || s == "-S" || s == "-emit-llvm" || starts_with(s, "--")) {
            write_stderr(str("goosecc: note: ignoring option '", s, "'\n"));
        }
        // everything else (-w, -W..., -f..., -m...) is accepted and ignored
    }
    if in_len == 0 { usage(); }

    pp_init_tables();
    // Search list: -iquote, -I, -isystem, then the system directories.
    var k = 0;
    while k + 1 < quote.len { add_dir(names[quote[k]..quote[k] + quote[k + 1]], false); k += 2; }
    quote_dirs_end = dirs.len;
    angle_start = dirs.len;
    k = 0;
    while k + 1 < angled.len { add_dir(names[angled[k]..angled[k] + angled[k + 1]], false); k += 2; }
    sys_start = dirs.len;
    k = 0;
    while k + 1 < isystem_dirs.len { add_dir(names[isystem_dirs[k]..isystem_dirs[k] + isystem_dirs[k + 1]], true); k += 2; }
    if !nostdinc {
        add_dir("/usr/lib/llvm-20/lib/clang/20/include", true);
        add_dir("/usr/local/include", true);
        add_dir("/usr/include/x86_64-linux-gnu", true);
        add_dir("/usr/include", true);
    }
    k = 0;
    while k + 1 < sys_dirs_after.len { add_dir(names[sys_dirs_after[k]..sys_dirs_after[k] + sys_dirs_after[k + 1]], true); k += 2; }
}

// After preprocessing: the header cache's report (with -E; else after
// parsing, with the parse cache's), the state checksum.
fn after_pp() {
    if mode_E { hc_report(); }
    if opt_state_hash > 0 { hc_state_hash(opt_state_hash == 2); }
}

// The options in the parse cache's key (pcache.goose): all but the input,
// the output and the reports.
fn pt_setup_opts() {
    opt_mode_pt = opt_mode;
    let a = args();
    var i = 1;
    while i < a.len {
        let s = a[i];
        i++;
        if s == "-o" { i++; continue; }
        if s == opt_input() || s == "--time" || s == "--cache-stats" || starts_with(s, "--pp-state-hash") { continue; }
        pt_opts.append(s);
        pt_opts.push(0);
    }
}

fn main() {
    options();
    hc_init();
    let t0 = clock_ns();
    if opt_mode == 1 {
        mode_E = true;
        out_to_file = out_len > 0 && !out_is_stdout();
        if !pp_start(opt_input()) { exit(1); }
        if hc_on { hc_tu_check(); }
        pp_fill();
        after_pp();
        out.push('\n');
        if out_len > 0 && !out_is_stdout() {
            if write_output(names[out_off..out_off + out_len], out) == 0 { fatal("cannot write output"); }
        } else {
            pr_flush();
        }
    } else {
        tu_annot = true;
        if !pp_start(opt_input()) { exit(1); }
        // keywords are known before preprocessing, so that pp_fill gives
        // keyword tokens their kinds as it adds them
        let v = std_version();
        opt_kw_inline = v.len > 0 || opt_gnu;
        opt_kw_restrict = v.len > 0;
        opt_kw_gnu = opt_gnu;
        opt_c89 = v.len == 0;
        keywords_init();
        // G1: the parser's starting state before preprocessing, so that the
        // identifiers it interns are the same in every translation unit
        // (the parse cache's entries refer to them: pcache.goose)
        types_init();
        parse_init();
        pt_track = hc_on;
        pt_setup_opts();
        if hc_on { hc_tu_check(); }
        pp_fill();
        after_pp();
        let t1 = clock_ns();
        pf_scan();
        parse_tu();
        if opt_state_hash > 0 { pt_state_hash(opt_state_hash == 2); }
        hc_report();
        if (opt_mode == 4 || opt_mode == 5) && n_errors == 0 {
            let t2 = clock_ns();
            let ok = gen::lower_tu(opt_input());
            let t3 = clock_ns();
            if !ok { exit(1); }
            if opt_mode == 5 {
                var o: u8[>..] = [];
                gen::dump_gir(o);
                if out_len > 0 && !out_is_stdout() {
                    if !write_file(names[out_off..out_off + out_len], o) { fatal("cannot write the GIR dump"); }
                } else {
                    write_stdout(o);
                }
            } else {
                let obj = gen::codegen();
                let t4 = clock_ns();
                var path: u8[>..] = [];
                if out_len > 0 {
                    path.append(names[out_off..out_off + out_len]);
                } else {
                    // file.c -> file.o in the current directory
                    var b = 0;
                    for c, i in opt_input() { if c == '/' { b = i + 1; } }
                    var e = opt_input().len;
                    if e - b > 2 && opt_input()[e - 2] == '.' { e -= 2; }
                    path.append(opt_input()[b..e]);
                    path.append(".o");
                }
                if out_is_stdout() { write_stdout(obj); }
                else if write_output(path, obj) == 0 { fatal("cannot write the object file"); }
                let t5 = clock_ns();
                if opt_time {
                    write_stderr(str("goosecc: preprocess ", (t1 - t0) / 1000, " us, parse+sema ", (t2 - t1) / 1000, " us, lowering ",
                        (t3 - t2) / 1000, " us, back-end ", (t4 - t3) / 1000, " us, write ", (t5 - t4) / 1000, " us, total ",
                        (t5 - t0) / 1000, " us; ", nodes.len, " nodes, ", gen::m_insts.len, " GIR insts, ", obj.len, " bytes\n"));
                }
            }
            if n_errors > 0 { exit(1); }
            return;
        }
        if opt_mode == 3 && n_errors == 0 {
            if !dump_ast(names[out_off..out_off + out_len]) { fatal("cannot write the AST dump"); }
        }
        if opt_mode == 2 && n_errors == 0 {
            var abs: u8[>..] = [];
            if opt_input()[0] != '/' {
                if !env("PWD", abs) { fatal("cannot determine the current directory (PWD)"); }
                abs.push('/');
            }
            abs.append(opt_input());
            if out_len == 0 { fatal("--layout-check needs -o file"); }
            if !write_layout_check(abs, names[out_off..out_off + out_len]) { fatal("cannot write the layout check file"); }
        }
        if opt_time {
            let t2 = clock_ns();
            write_stderr(str("goosecc: pp ", (t1 - t0) / 1000, " us, parse+sema ", (t2 - t1) / 1000, " us, ", nodes.len, " nodes, ",
                types.len, " types, ", syms.len, " symbols\n"));
        }
    }
    if opt_time {
        let t1 = clock_ns();
        write_stderr(str("goosecc: ", (t1 - t0) / 1000, " us, ", tu_toks.len, " tokens, ", idents.len, " idents, ",
            files.len, " files, src ", src.len, " bytes\n"));
    }
    if n_errors > 0 { exit(1); }
}
