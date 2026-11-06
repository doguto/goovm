// goosecc: the raw lexer. It turns the text of the current file into
// preprocessing tokens. The fast path works directly on `src`; a token that
// contains a backslash-newline splice is re-lexed by the slow path from a
// cleaned copy whose text goes to the scratch part of `src`.

import .common;

// Character classes.
let CC_IDSTART = 1;
let CC_IDCONT = 2;
let CC_DIGIT = 4;
let CC_HSPACE = 8;     // space, \t, \v, \f, \r
let CC_NUMCONT = 16;   // [0-9A-Za-z_.$] and bytes >= 0x80
var cc: u8[256] = [0; 256];

fn lex_init_tables() {
    for i in 256 {
        var v: u8 = 0;
        let c = i as! u8;
        if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_' || c == '$' || c >= 128 {
            v |= CC_IDSTART | CC_IDCONT | CC_NUMCONT;
        }
        if c >= '0' && c <= '9' { v |= CC_IDCONT | CC_DIGIT | CC_NUMCONT; }
        if c == '.' { v |= CC_NUMCONT; }
        if c == ' ' || c == '\t' || c == 11 || c == 12 || c == '\r' { v |= CC_HSPACE; }
        cc[i] = v;
    }
}

// Language options that change lexing.
var opt_c11: bool = true;       // u"" U"" u8"" prefixes
var opt_trigraphs: bool = false;

// The lexer state of the current file. Saved in the file context when an
// #include pushes another file.
var lx_pos: i64 = 0;
var lx_end: i64 = 0;
var lx_file: i64 = -1;
var lx_flags: u8 = 0;    // flags for the next token (F_BOL / F_LSPACE)
var lx_dir: bool = false; // lexing a directive: a newline ends it with TK_EOD
var lx_sys: u8 = 0;      // F_SYSHDR when the current file is a system header

// Scratch for the slow path.
var lxtmp: u8[>..] = [];
var lxmap: u32[>..] = [];

// Recognizes the token at buf[i] (which is not whitespace, not an
// identifier start handled by the caller... any token in fact). Returns the
// kind, the end offset and F_DIGRAPH for digraphs. buf must end in a NUL.
// TK_COMMENT for /* */ and // comments (end is after the comment; for //
// it is the newline).
fn scan_token(buf: const u8[:], i: i64) -> i64, i64, u8 {
    let c = buf[i];
    let c1 = if i + 1 < buf.len { buf[i + 1] } else { 0 };
    if cc[c] & CC_IDSTART != 0 {
        // String and character prefixes.
        if c == 'L' || ((c == 'u' || c == 'U') && opt_c11) {
            var j = i + 1;
            if c == 'u' && c1 == '8' && opt_c11 { j = i + 2; }
            let q = if j < buf.len { buf[j] } else { 0 };
            if q == '"' {
                let e = scan_quoted(buf, j, '"');
                if e > 0 { return TK_STRING, e, 0; }
                return TK_OTHER, -e, 0;
            }
            if q == '\'' && j == i + 1 {
                let e = scan_quoted(buf, j, '\'');
                if e > 0 { return TK_CHAR, e, 0; }
                return TK_OTHER, -e, 0;
            }
        }
        var j = i + 1;
        while j < buf.len && cc[buf[j]] & CC_IDCONT != 0 { j++; }
        return TK_IDENT, j, 0;
    }
    if cc[c] & CC_DIGIT != 0 || (c == '.' && cc[c1] & CC_DIGIT != 0) {
        return TK_NUMBER, scan_number(buf, i), 0;
    }
    match c {
        '"' => {
            let e = scan_quoted(buf, i, '"');
            if e > 0 { return TK_STRING, e, 0; }
            return TK_OTHER, -e, 0;
        },
        '\'' => {
            let e = scan_quoted(buf, i, '\'');
            if e > 0 { return TK_CHAR, e, 0; }
            return TK_OTHER, -e, 0;
        },
        '[' => { return TK_L_SQUARE, i + 1, 0; },
        ']' => { return TK_R_SQUARE, i + 1, 0; },
        '(' => { return TK_L_PAREN, i + 1, 0; },
        ')' => { return TK_R_PAREN, i + 1, 0; },
        '{' => { return TK_L_BRACE, i + 1, 0; },
        '}' => { return TK_R_BRACE, i + 1, 0; },
        ';' => { return TK_SEMI, i + 1, 0; },
        ',' => { return TK_COMMA, i + 1, 0; },
        '~' => { return TK_TILDE, i + 1, 0; },
        '?' => { return TK_QUESTION, i + 1, 0; },
        '.' => {
            if c1 == '.' && i + 2 < buf.len && buf[i + 2] == '.' { return TK_ELLIPSIS, i + 3, 0; }
            return TK_PERIOD, i + 1, 0;
        },
        '&' => {
            if c1 == '&' { return TK_AMPAMP, i + 2, 0; }
            if c1 == '=' { return TK_AMPEQUAL, i + 2, 0; }
            return TK_AMP, i + 1, 0;
        },
        '*' => {
            if c1 == '=' { return TK_STAREQUAL, i + 2, 0; }
            return TK_STAR, i + 1, 0;
        },
        '+' => {
            if c1 == '+' { return TK_PLUSPLUS, i + 2, 0; }
            if c1 == '=' { return TK_PLUSEQUAL, i + 2, 0; }
            return TK_PLUS, i + 1, 0;
        },
        '-' => {
            if c1 == '>' { return TK_ARROW, i + 2, 0; }
            if c1 == '-' { return TK_MINUSMINUS, i + 2, 0; }
            if c1 == '=' { return TK_MINUSEQUAL, i + 2, 0; }
            return TK_MINUS, i + 1, 0;
        },
        '!' => {
            if c1 == '=' { return TK_EXCLAIMEQUAL, i + 2, 0; }
            return TK_EXCLAIM, i + 1, 0;
        },
        '/' => {
            if c1 == '*' {
                var j = i + 2;
                while j + 1 < buf.len && !(buf[j] == '*' && buf[j + 1] == '/') {
                    if buf[j] == 0 && j + 1 >= buf.len { break; }
                    j++;
                }
                if j + 1 < buf.len { return TK_COMMENT, j + 2, 0; }
                return TK_COMMENT, buf.len - 1, 0;
            }
            if c1 == '/' {
                var j = i + 2;
                while j < buf.len && buf[j] != '\n' && buf[j] != 0 { j++; }
                return TK_COMMENT, j, 0;
            }
            if c1 == '=' { return TK_SLASHEQUAL, i + 2, 0; }
            return TK_SLASH, i + 1, 0;
        },
        '%' => {
            if c1 == '=' { return TK_PERCENTEQUAL, i + 2, 0; }
            if c1 == '>' { return TK_R_BRACE, i + 2, F_DIGRAPH; }
            if c1 == ':' {
                if i + 3 < buf.len && buf[i + 2] == '%' && buf[i + 3] == ':' { return TK_HASHHASH, i + 4, F_DIGRAPH; }
                return TK_HASH, i + 2, F_DIGRAPH;
            }
            return TK_PERCENT, i + 1, 0;
        },
        '<' => {
            if c1 == '<' {
                if i + 2 < buf.len && buf[i + 2] == '=' { return TK_LESSLESSEQUAL, i + 3, 0; }
                return TK_LESSLESS, i + 2, 0;
            }
            if c1 == '=' { return TK_LESSEQUAL, i + 2, 0; }
            if c1 == ':' { return TK_L_SQUARE, i + 2, F_DIGRAPH; }
            if c1 == '%' { return TK_L_BRACE, i + 2, F_DIGRAPH; }
            return TK_LESS, i + 1, 0;
        },
        '>' => {
            if c1 == '>' {
                if i + 2 < buf.len && buf[i + 2] == '=' { return TK_GREATERGREATEREQUAL, i + 3, 0; }
                return TK_GREATERGREATER, i + 2, 0;
            }
            if c1 == '=' { return TK_GREATEREQUAL, i + 2, 0; }
            return TK_GREATER, i + 1, 0;
        },
        '^' => {
            if c1 == '=' { return TK_CARETEQUAL, i + 2, 0; }
            return TK_CARET, i + 1, 0;
        },
        '|' => {
            if c1 == '|' { return TK_PIPEPIPE, i + 2, 0; }
            if c1 == '=' { return TK_PIPEEQUAL, i + 2, 0; }
            return TK_PIPE, i + 1, 0;
        },
        ':' => {
            if c1 == '>' { return TK_R_SQUARE, i + 2, F_DIGRAPH; }
            return TK_COLON, i + 1, 0;
        },
        '=' => {
            if c1 == '=' { return TK_EQUALEQUAL, i + 2, 0; }
            return TK_EQUAL, i + 1, 0;
        },
        '#' => {
            if c1 == '#' { return TK_HASHHASH, i + 2, 0; }
            return TK_HASH, i + 1, 0;
        },
        _ => { return TK_OTHER, i + 1, 0; },
    }
}

// A quoted literal starting at buf[i] == q. Returns the end (> 0), or
// -(end of line) when unterminated (the token is then TK_OTHER, as in clang).
fn scan_quoted(buf: const u8[:], i: i64, q: u8) -> i64 {
    var j = i + 1;
    while j < buf.len {
        let c = buf[j];
        if c == q { return j + 1; }
        if c == '\\' && j + 1 < buf.len && buf[j + 1] != 0 { j += 2; continue; }
        if c == '\n' || (c == 0 && j + 1 >= buf.len) { return -j; }
        j++;
    }
    return -j;
}

fn scan_number(buf: const u8[:], i: i64) -> i64 {
    var j = i + 1;
    while j < buf.len {
        let c = buf[j];
        if cc[c] & CC_NUMCONT != 0 {
            if (c == 'e' || c == 'E' || c == 'p' || c == 'P') && j + 1 < buf.len && (buf[j + 1] == '+' || buf[j + 1] == '-') {
                j += 2;
                continue;
            }
            j++;
            continue;
        }
        break;
    }
    return j;
}

// Is there a backslash-newline splice at src[p]? Returns its length (0 if none).
fn splice_at(p: i64) -> i64 {
    if src[p] != '\\' { return 0; }
    var q = p + 1;
    // clang accepts whitespace between the backslash and the newline (with a warning)
    while cc[src[q]] & CC_HSPACE != 0 && src[q] != '\r' { q++; }
    if src[q] == '\n' { return q + 1 - p; }
    if src[q] == '\r' {
        if src[q + 1] == '\n' { return q + 2 - p; }
        return q + 1 - p;
    }
    return 0;
}

// The slow path: lex the token at physical offset p0, removing splices.
// Returns the kind, the physical end and the flags; the cleaned spelling is
// appended to src (its offset in lx_slow_spell).
var lx_slow_spell: i64 = 0;
fn lex_slow(p0: i64) -> i64, i64, u8 {
    lxtmp.clear();
    lxmap.clear();
    var p = p0;
    // Gather the logical line from p0.
    loop {
        let s = splice_at(p);
        if s > 0 { p += s; continue; }
        let c = src[p];
        if c == '\n' || (c == 0 && p >= lx_end) { break; }
        lxtmp.push(c);
        lxmap.push(p as! u32);
        p++;
    }
    lxmap.push(p as! u32);
    lxtmp.push(0);
    let k, e, fl = scan_token(lxtmp, 0);
    var pe = lxmap[e] as i64;
    if k == TK_COMMENT && e < lxtmp.len - 1 && lxtmp[e] == 0 { pe = lxmap[e] as i64; }
    // A /* comment may continue past this logical line: finish it physically.
    if k == TK_COMMENT && lxtmp.len >= 2 && lxtmp[0] == '/' && lxtmp[1] == '*' && e >= lxtmp.len - 1 {
        var q = lxmap[lxmap.len - 1] as i64;
        loop {
            if q >= lx_end { pe = lx_end; break; }
            if src[q] == '*' {
                var r = q + 1;
                loop { let s = splice_at(r); if s == 0 { break; } r += s; }
                if src[r] == '/' { pe = r + 1; break; }
            }
            q++;
        }
    }
    lx_slow_spell = src.len;
    src.append(lxtmp[..e]);
    return k, pe, fl;
}

// The position after the block comment starting at p ("/*").
// With trigraphs a splice may also be "??/" + newline: search for '*' and
// let splice_at decide.
fn skip_block_comment_tri(p0: i64) -> i64 {
    var q = p0 + 2;
    loop {
        let r = find_byte(src[q..lx_end], '*');
        if r < 0 { return lx_end; }
        q = q + r + 1;
        if src[q] == '/' { return q + 1; }
        var t = q;
        loop { let s = splice_at(t); if s == 0 { break; } t += s; }
        if t > q && src[t] == '/' { return t + 1; }
    }
}

// It searches for the '/' (rare inside comments, unlike the '*' that
// starts every line of a boxed comment) and looks back for the '*'.
fn skip_block_comment(p0: i64) -> i64 {
    if opt_trigraphs { return skip_block_comment_tri(p0); }
    var q = p0 + 2;
    loop {
        let r = find_byte(src[q..lx_end], '/');
        if r < 0 { return lx_end; }
        q = q + r;
        var b = q - 1;
        if b >= p0 + 2 && src[b] == '*' { return q + 1; }
        // "*\<newline>/": backslash-newline splices between '*' and '/'
        if src[b] == '\n' || src[b] == '\r' {
            var ok = true;
            loop {
                if b < p0 + 2 { ok = false; break; }
                if src[b] == '*' { break; }
                if src[b] != '\n' && src[b] != '\r' { ok = false; break; }
                // a line end: it must follow a backslash (and optional spaces)
                if src[b] == '\n' && b > 0 && src[b - 1] == '\r' { b--; }
                b--;
                while b >= p0 + 2 && (src[b] == ' ' || src[b] == '\t') { b--; }
                if b < p0 + 2 || src[b] != '\\' { ok = false; break; }
                b--;
            }
            if ok { return q + 1; }
        }
        q++;
    }
}

// The next token of the current file.
fn lex_file_token() -> Tok {
    var p = lx_pos;
    var flags = lx_flags;
    loop {
        let c = src[p];
        if cc[c] & CC_HSPACE != 0 { p++; flags |= F_LSPACE; continue; }
        if c == '\n' {
            if lx_dir {
                lx_pos = p;
                lx_flags = flags;
                return Tok { kind: TK_EOD, flags: flags, aux: 0, spell: p as! u32, val: 0, xloc: p as! u32 };
            }
            p++;
            flags = F_BOL;
            continue;
        }
        if c == 0 && p >= lx_end {
            lx_pos = p;
            lx_flags = flags;
            let k = if lx_dir { TK_EOD } else { TK_EOF };
            return Tok { kind: k as! u8, flags: flags, aux: 0, spell: p as! u32, val: 0, xloc: p as! u32 };
        }
        if cc[c] & CC_IDSTART != 0 && !((c == 'L' || c == 'u' || c == 'U') && quote_follows(p)) {
            // Identifier fast path.
            var h: u32 = 2166136261;
            var q = p;
            while cc[src[q]] & CC_IDCONT != 0 {
                h = (h ^ src[q]) * 16777619;
                q++;
            }
            if src[q] == '\\' && splice_at(q) > 0 {
                let k, e, fl = lex_slow(p);
                return finish_slow(k, p, e, fl, flags);
            }
            let id = ident_lookup(p, q - p, h);
            lx_pos = q;
            lx_flags = 0;
            return Tok { kind: TK_IDENT, flags: flags | lx_sys, aux: 0, spell: p as! u32, val: id, xloc: p as! u32 };
        }
        if c == '\\' {
            let s = splice_at(p);
            if s > 0 { p += s; continue; }
        }
        if c == '/' && src[p + 1] == '*' {
            // a block comment: find "*/" (possibly "*\<newline>/")
            p = skip_block_comment(p);
            flags |= F_LSPACE;
            continue;
        }
        if c == '/' && src[p + 1] == '/' {
            // a line comment, continued by a backslash-newline
            var q = p + 2;
            loop {
                let r = find_byte(src[q..lx_end], '\n');
                if r < 0 { q = lx_end; break; }
                q = q + r;
                var b = q - 1;
                if b >= p + 2 && src[b] == '\r' { b--; }
                while b >= p + 2 && cc[src[b]] & CC_HSPACE != 0 && src[b] != '\r' { b--; }
                if b >= p + 2 && src[b] == '\\' { q++; continue; }
                break;
            }
            p = q;
            flags |= F_LSPACE;
            continue;
        }
        let k, e, fl = scan_token(src, p);
        // A splice right after the token, or inside a literal, may change it.
        var dirty = src[e] == '\\' && splice_at(e) > 0;
        if (k == TK_STRING || k == TK_CHAR || k == TK_COMMENT || k == TK_OTHER) && !dirty {
            var j = p;
            while j < e {
                if src[j] == '\\' && splice_at(j) > 0 { dirty = true; break; }
                j++;
            }
        }
        if dirty {
            let k2, e2, fl2 = lex_slow(p);
            if k2 == TK_COMMENT {
                p = e2;
                flags |= F_LSPACE;
                continue;
            }
            return finish_slow(k2, p, e2, fl2, flags);
        }
        if k == TK_COMMENT {
            p = e;
            flags |= F_LSPACE;
            continue;
        }
        lx_pos = e;
        lx_flags = 0;
        var v: u32 = 0;
        if !is_punct(k) { v = (e - p) as! u32; }
        return Tok { kind: k as! u8, flags: flags | fl | lx_sys, aux: 0, spell: p as! u32, val: v, xloc: p as! u32 };
    }
}

fn quote_follows(p: i64) -> bool {
    let c1 = src[p + 1];
    if c1 == '"' { return true; }
    if c1 == '\'' { return src[p] == 'L' || opt_c11; }
    if src[p] == 'u' && c1 == '8' && src[p + 2] == '"' && opt_c11 { return true; }
    return false;
}

fn finish_slow(k: i64, p: i64, e: i64, fl: u8, flags: u8) -> Tok {
    lx_pos = e;
    lx_flags = 0;
    let sp = lx_slow_spell;
    let n = src.len - sp;
    src.push(0);
    if k == TK_IDENT {
        let h = hash_bytes(src[sp..sp + n]);
        let id = ident_lookup(sp, n, h);
        return Tok { kind: TK_IDENT, flags: flags | lx_sys, aux: 0, spell: sp as! u32, val: id, xloc: p as! u32 };
    }
    var v: u32 = 0;
    if !is_punct(k) { v = n as! u32; }
    return Tok { kind: k as! u8, flags: flags | fl | lx_sys, aux: 0, spell: sp as! u32, val: v, xloc: p as! u32 };
}

// Skip the rest of the current directive line (to the newline, which is
// left in place). Handles comments and splices.
fn lex_skip_line() {
    var p = lx_pos;
    loop {
        let c = src[p];
        if c == '\n' { break; }
        if c == 0 && p >= lx_end { break; }
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
                if src[p] == '\\' && splice_at(p) > 0 { p += splice_at(p); continue; }
                p++;
            }
            break;
        }
        if c == '"' || c == '\'' {
            p++;
            while p < lx_end && src[p] != c && src[p] != '\n' {
                if src[p] == '\\' { p += 2; continue; }
                p++;
            }
            if src[p] == c { p++; }
            continue;
        }
        p++;
    }
    lx_pos = p;
}

// The rest of the directive line as raw text (for #error, #warning,
// #ident...): from lx_pos to the newline, splices removed, with leading and
// trailing whitespace trimmed.
fn lex_rest_of_line(out: u8[>..]&) {
    let start = lx_pos;
    lex_skip_line();
    var p = start;
    while p < lx_pos {
        let s = splice_at(p);
        if s > 0 { p += s; continue; }
        out.push(src[p]);
        p++;
    }
}

// A <header-name> at the current position (after optional whitespace).
// Returns the token, or a TK_EOD/other token if there is none.
fn lex_header_name() -> Tok {
    var p = lx_pos;
    while cc[src[p]] & CC_HSPACE != 0 { p++; }
    if src[p] == '<' {
        var q = p + 1;
        while src[q] != '>' && src[q] != '\n' && !(src[q] == 0 && q >= lx_end) { q++; }
        if src[q] == '>' {
            lx_pos = q + 1;
            lx_flags = 0;
            return Tok { kind: TK_HEADER, flags: F_LSPACE, aux: 0, spell: p as! u32, val: (q + 1 - p) as! u32, xloc: p as! u32 };
        }
    }
    return lex_file_token();
}

// Peeks whether the next token in the file is '(' (skipping whitespace,
// newlines and comments, not directives). 1 = yes, 0 = no, 2 = end of file.
fn lex_peek_lparen() -> i64 {
    var p = lx_pos;
    loop {
        let c = src[p];
        if cc[c] & CC_HSPACE != 0 { p++; continue; }
        if c == '\n' {
            if lx_dir { return 0; }
            p++;
            continue;
        }
        if c == 0 && p >= lx_end { return if lx_dir { 0 } else { 2 }; }
        if c == '\\' {
            let s = splice_at(p);
            if s > 0 { p += s; continue; }
            return 0;
        }
        if c == '/' && src[p + 1] == '*' {
            p = skip_block_comment(p);
            continue;
        }
        if c == '/' && src[p + 1] == '/' {
            while p < lx_end && src[p] != '\n' { p++; }
            continue;
        }
        if c == '(' { return 1; }
        return 0;
    }
}
