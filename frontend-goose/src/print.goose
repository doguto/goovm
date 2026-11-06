// goosecc: the -E printer. Tokens are written with a space where the
// source had whitespace or where the two spellings would otherwise lex as
// one token; newlines and line markers follow the source lines like clang's
// PrintPreprocessedOutput (only the token stream is meant to match exactly).

import .common;
import .lex;
import .pp;

var out: u8[>..] = [];
var pr_line: i64 = 1;        // presumed line of the current output line
var pr_fname: u32 = 0;       // presumed file name (names) of the output position
var pr_fname_len: u32 = 0;
var pr_bol: bool = true;     // output is at the start of a line
var pr_prev_kind: i64 = -1;  // kind of the previous token on this line
var pr_last: u8 = 0;         // last byte of the previous token's spelling
var pr_first: u8 = 0;        // scratch
var pr_started: bool = false;

fn pr_flush() {
    write_stdout(out);
    out.clear();
}

fn pr_newline() {
    out.push('\n');
    pr_bol = true;
    pr_prev_kind = -1;
    if out.len > 1048576 { pr_flush(); }
}

fn pr_marker(line: i64, fname: u32, flen: u32, flags: const u8[:]) {
    if !pr_bol { pr_newline(); }
    format(out, "# ", line, " \"");
    let s = names[fname..fname + flen];
    for c in s {
        if c == '\\' || c == '"' { out.push('\\'); }
        out.push(c);
    }
    out.push('"');
    out.append(flags);
    pr_newline();
    pr_line = line;
    pr_fname = fname;
    pr_fname_len = flen;
}

// The output moves to `line` of file `fname`.
fn pr_move_to(line: i64, fname: u32, flen: u32) {
    if fname != pr_fname || flen != pr_fname_len {
        pr_marker(line, fname, flen, "");
        return;
    }
    if line == pr_line && pr_started {
        if !pr_bol { out.push(' '); }
        return;
    }
    if line > pr_line && line - pr_line <= 8 {
        if !pr_bol { pr_newline(); pr_line++; }
        while pr_line < line { pr_newline(); pr_line++; }
        return;
    }
    pr_marker(line, fname, flen, "");
}

fn pr_file_enter(fname: u32, flen: u32, sys: bool) {
    pr_started = true;
    pr_marker(1, fname, flen, if sys { " 1 3" } else { " 1" });
}

fn pr_file_return(line: i64, fname: u32, flen: u32, sys: bool) {
    pr_marker(line, fname, flen, if sys { " 2 3" } else { " 2" });
}

// Would the end of the previous token and the start of t lex differently
// when written next to each other?
fn needs_space(t: Tok, first: u8) -> bool {
    if pr_prev_kind < 0 { return false; }
    let a = pr_last;
    let b = first;
    if cc[a] & CC_IDCONT != 0 && (cc[b] & CC_IDCONT != 0 || b == '"' || b == '\'') { return true; }
    if pr_prev_kind == TK_NUMBER && (b == '.' || b == '+' || b == '-' || cc[b] & CC_IDCONT != 0) { return true; }
    if a == '.' && (cc[b] & CC_DIGIT != 0 || b == '.') { return true; }
    match a {
        '+' => { return b == '+' || b == '='; },
        '-' => { return b == '-' || b == '=' || b == '>'; },
        '<' => { return b == '<' || b == '=' || b == ':' || b == '%'; },
        '>' => { return b == '>' || b == '='; },
        '&' => { return b == '&' || b == '='; },
        '|' => { return b == '|' || b == '='; },
        '=' => { return b == '='; },
        '!', '*', '^' => { return b == '='; },
        '/' => { return b == '/' || b == '*' || b == '='; },
        '%' => { return b == '=' || b == '>' || b == ':'; },
        '#' => { return b == '#'; },
        ':' => { return b == '>'; },
        _ => { return false; },
    }
}

var pr_tmp: u8[>..] = [];

fn pr_token(t: Tok) {
    if t.flags & F_BOL != 0 || !pr_started {
        let f = file_of(t.xloc as i64);
        if f >= 0 {
            let line, col = line_col(f, t.xloc as i64);
            let ci = cur_file_ctx;
            let pl = line + ctxs[ci].line_delta;
            pr_move_to(pl, ctxs[ci].pspell, ctxs[ci].pspell_len);
            pr_started = true;
        } else if !pr_bol {
            out.push(' ');
        }
    } else if !pr_bol && t.flags & F_LSPACE != 0 {
        out.push(' ');
    }
    pr_tmp.clear();
    tok_spelling(pr_tmp, t);
    if pr_tmp.len == 0 { return; }
    if !pr_bol && out.len > 0 && out[out.len - 1] != ' ' && needs_space(t, pr_tmp[0]) { out.push(' '); }
    out.append(pr_tmp);
    pr_bol = false;
    pr_prev_kind = t.kind as i64;
    pr_last = pr_tmp[pr_tmp.len - 1];
}

// A #pragma line (or #ident) printed on a line of its own.
fn pr_directive_line(text: const u8[:]) {
    if !pr_bol { pr_newline(); }
    out.append(text);
    pr_newline();
    pr_line++;
}
