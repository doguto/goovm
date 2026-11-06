// goosecc: a C17 + GNU front end (preprocessor, parser, type checker)
// written in Goose. See ../DESIGN.md.
//
//   goosecc -E [options] file.c            preprocess to stdout (or -o)
//   goosecc -fsyntax-only [options] file.c parse and type-check
//   goosecc --layout-check [options] file.c -o check.c
//
// Options follow clang: -I -isystem -iquote -idirafter -D -U -include
// -std= -O* -pthread -w; others are accepted and ignored.

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
import .ast;
import .sema;
import .expr;
import .parse;
import .init;
import .builtins;
import .layout;
import .dump;

let OPTS_WITH_VALUE = ["-I", "-D", "-U", "-isystem", "-iquote", "-idirafter", "-include", "-o", "-x", "-MF", "-MT", "-MQ", "-std="];
var opt_input: u8[>..] = [];
var out_off: u32 = 0;
var std_off: u32 = 0;
var std_len: i64 = 0;
var out_len: i64 = 0;
var opt_mode: i64 = 0;      // 0 = -fsyntax-only, 1 = -E, 2 = --layout-check
var opt_time: bool = false;
var sys_dirs_after: u32[>..] = [];   // -idirafter: (off, len) pairs
var isystem_dirs: u32[>..] = [];
var nostdinc: bool = false;

fn add_dir(d: const u8[:], sys: bool) {
    var s = d;
    while s.len > 1 && s[s.len - 1] == '/' { s = s[..s.len - 1]; }
    dirs.push(Dir { path: name_add(s), len: s.len as! u32, sys: sys });
}

fn usage() {
    write_stderr("usage: goosecc (-E | -fsyntax-only | --layout-check) [clang options] file.c [-o out]\n");
    exit(2);
}

fn main() {
    let a = args();
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
            else if which == 1 { cmd_macros.push(CmdMacro { def: true, off: name_add(val), len: val.len as! u32 }); }
            else if which == 2 { cmd_macros.push(CmdMacro { def: false, off: name_add(val), len: val.len as! u32 }); }
            else if which == 3 { isystem_dirs.push(name_add(val)); isystem_dirs.push(val.len as! u32); }
            else if which == 4 { quote.push(name_add(val)); quote.push(val.len as! u32); }
            else if which == 5 { sys_dirs_after.push(name_add(val)); sys_dirs_after.push(val.len as! u32); }
            else if which == 6 { cmd_includes.push(name_add(val)); cmd_includes.push(val.len as! u32); }
            else if which == 7 { out_off = name_add(val); out_len = val.len; }
            else if which == 12 { std_off = name_add(val); std_len = val.len; }
        }
        if has_val { continue; }
        if s == "-E" { opt_mode = 1; }
        else if s == "-fsyntax-only" { opt_mode = 0; }
        else if s == "--layout-check" { opt_mode = 2; }
        else if s == "--dump-ast" { opt_mode = 3; }
        else if s == "--time" { opt_time = true; }
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
        else if s == "-" || (s.len > 0 && s[0] != '-') { opt_input.clear(); opt_input.append(s); }
        // everything else (-c, -g, -w, -W..., -f..., -m...) is accepted and ignored
    }
    if opt_input.len == 0 { usage(); }

    opt_std.append(names[std_off..std_off + std_len]);
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

    let t0 = clock_ns();
    if opt_mode == 1 {
        mode_E = true;
        if !pp_start(opt_input) { exit(1); }
        loop {
            let t = pp_lex();
            if t.kind == TK_EOF { break; }
            pr_token(t);
        }
        out.push('\n');
        if out_len > 0 {
            if !write_file(names[out_off..out_off + out_len], out) { fatal("cannot write output"); }
        } else {
            pr_flush();
        }
    } else {
        tu_annot = true;
        if !pp_start(opt_input) { exit(1); }
        loop {
            let t = pp_lex();
            tu_toks.push(t);
            if t.kind == TK_EOF { break; }
        }
        let t1 = clock_ns();
        let v = std_version();
        opt_kw_inline = v.len > 0 || opt_gnu;
        opt_kw_restrict = v.len > 0;
        opt_kw_gnu = opt_gnu;
        opt_c89 = v.len == 0;
        keywords_init();
        types_init();
        prepare_tokens();
        parse_init();
        parse_tu();
        if opt_mode == 3 && n_errors == 0 {
            if !dump_ast(names[out_off..out_off + out_len]) { fatal("cannot write the AST dump"); }
        }
        if opt_mode == 2 && n_errors == 0 {
            var abs: u8[>..] = [];
            if opt_input[0] != '/' {
                if !env("PWD", abs) { fatal("cannot determine the current directory (PWD)"); }
                abs.push('/');
            }
            abs.append(opt_input);
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
