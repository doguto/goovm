// goosecc: #if expressions, builtin macros (__LINE__, __FILE__,
// __has_include, __has_builtin, ...) and preprocessor initialization.

import std;
import os;
import dictionary;
import .common;
import .lex;
import .pp;
import .ppdir;
import .print;
import .predef_gen;
import .tables_gen;

// ---------------------------------------------------------------------------
// #if expressions. Values are 64-bit with a signedness flag (intmax_t /
// uintmax_t), evaluated as clang's PPExpressions does.

var pe_tok: Tok = Tok { kind: 0, flags: 0, aux: 0, spell: 0, val: 0, xloc: 0 };
var pe_err: bool = false;

recursive fn pe_advance() { pe_tok = pp_lex(); }

fn pe_error(msg: const u8[:]) {
    if !pe_err { error_at(pe_tok.xloc as i64, msg); }
    pe_err = true;
}

recursive fn eval_if_expr() -> bool {
    pe_err = false;
    pe_advance();
    if pe_tok.kind == TK_EOD {
        pe_error("expected value in expression");
        return false;
    }
    let v, u = pe_comma(true);
    if !pe_err && pe_tok.kind != TK_EOD {
        pe_error("token is not a valid binary operator in a preprocessor subexpression");
    }
    while pe_tok.kind != TK_EOD && pe_tok.kind != TK_EOF { pe_advance(); }
    return v != 0 && !pe_err;
}

recursive fn pe_comma(ev: bool) -> i64, bool {
    var v, u = pe_cond(ev);
    while pe_tok.kind == TK_COMMA {
        pe_advance();
        v, u = pe_cond(ev);
    }
    return v, u;
}

recursive fn pe_cond(ev: bool) -> i64, bool {
    let c, cu = pe_bin(1, ev);
    if pe_tok.kind != TK_QUESTION { return c, cu; }
    pe_advance();
    let a, au = pe_comma(ev && c != 0);
    if pe_tok.kind != TK_COLON {
        pe_error("expected ':' in conditional expression");
        return 0, false;
    }
    pe_advance();
    let b, bu = pe_cond(ev && c == 0);
    let uns = au || bu;
    return if c != 0 { a } else { b }, uns;
}

fn pe_prec(k: i64) -> i64 {
    return match k {
        TK_STAR, TK_SLASH, TK_PERCENT => 10,
        TK_PLUS, TK_MINUS => 9,
        TK_LESSLESS, TK_GREATERGREATER => 8,
        TK_LESS, TK_GREATER, TK_LESSEQUAL, TK_GREATEREQUAL => 7,
        TK_EQUALEQUAL, TK_EXCLAIMEQUAL => 6,
        TK_AMP => 5,
        TK_CARET => 4,
        TK_PIPE => 3,
        TK_AMPAMP => 2,
        TK_PIPEPIPE => 1,
        _ => 0,
    };
}

recursive fn pe_bin(minp: i64, ev: bool) -> i64, bool {
    var l, lu = pe_unary(ev);
    loop {
        let op = pe_tok.kind as i64;
        let p = pe_prec(op);
        if p == 0 || p < minp { break; }
        pe_advance();
        var rev = ev;
        if op == TK_AMPAMP { rev = ev && l != 0; }
        if op == TK_PIPEPIPE { rev = ev && l == 0; }
        let r, ru = pe_bin(p + 1, rev);
        if pe_err { return 0, false; }
        let uns = lu || ru;
        let a = l as! u64;
        let b = r as! u64;
        var res: i64 = 0;
        var resu = uns;
        if op == TK_STAR {
            res = (a * b) as! i64;
        } else if op == TK_SLASH || op == TK_PERCENT {
            if r == 0 {
                if ev { pe_error(if op == TK_SLASH { "division by zero in preprocessor expression" } else { "remainder by zero in preprocessor expression" }); }
                res = 0;
            } else if uns {
                res = (if op == TK_SLASH { a / b } else { a % b }) as! i64;
            } else if l == -9223372036854775807 - 1 && r == -1 {
                res = if op == TK_SLASH { l } else { 0 };
            } else {
                res = if op == TK_SLASH { l / r } else { rem(l, r) };
            }
        } else if op == TK_PLUS {
            res = (a + b) as! i64;
        } else if op == TK_MINUS {
            res = (a - b) as! i64;
        } else if op == TK_LESSLESS || op == TK_GREATERGREATER {
            var sh = b;
            if ru == false && r < 0 { sh = 63; }
            if sh > 63 { sh = 63; }
            resu = lu;
            if op == TK_LESSLESS {
                res = (a << sh) as! i64;
            } else if lu {
                res = (a >> sh) as! i64;
            } else {
                res = l >> sh;
            }
        } else if op == TK_LESS || op == TK_GREATER || op == TK_LESSEQUAL || op == TK_GREATEREQUAL {
            var c = false;
            if uns {
                c = match op { TK_LESS => a < b, TK_GREATER => a > b, TK_LESSEQUAL => a <= b, _ => a >= b };
            } else {
                c = match op { TK_LESS => l < r, TK_GREATER => l > r, TK_LESSEQUAL => l <= r, _ => l >= r };
            }
            res = if c { 1 } else { 0 };
            resu = false;
        } else if op == TK_EQUALEQUAL || op == TK_EXCLAIMEQUAL {
            let c = if op == TK_EQUALEQUAL { a == b } else { a != b };
            res = if c { 1 } else { 0 };
            resu = false;
        } else if op == TK_AMP {
            res = (a & b) as! i64;
        } else if op == TK_CARET {
            res = (a ^ b) as! i64;
        } else if op == TK_PIPE {
            res = (a | b) as! i64;
        } else if op == TK_AMPAMP {
            res = if l != 0 && r != 0 { 1 } else { 0 };
            resu = false;
        } else if op == TK_PIPEPIPE {
            res = if l != 0 || r != 0 { 1 } else { 0 };
            resu = false;
        }
        l = res;
        lu = resu;
    }
    return l, lu;
}

recursive fn pe_unary(ev: bool) -> i64, bool {
    let t = pe_tok;
    let k = t.kind as i64;
    if k == TK_PLUS { pe_advance(); return pe_unary(ev); }
    if k == TK_MINUS {
        pe_advance();
        let v, u = pe_unary(ev);
        return (0 - (v as! u64)) as! i64, u;
    }
    if k == TK_TILDE {
        pe_advance();
        let v, u = pe_unary(ev);
        return ~v, u;
    }
    if k == TK_EXCLAIM {
        pe_advance();
        let v, u = pe_unary(ev);
        return if v == 0 { 1 } else { 0 }, false;
    }
    if k == TK_L_PAREN {
        pe_advance();
        let v, u = pe_comma(ev);
        if pe_tok.kind != TK_R_PAREN {
            pe_error("expected ')' in preprocessor expression");
            return 0, false;
        }
        pe_advance();
        return v, u;
    }
    if k == TK_NUMBER {
        let v, u, ok = parse_pp_number(t);
        if !ok { pe_error("invalid integer constant in preprocessor expression"); return 0, false; }
        pe_advance();
        return v, u;
    }
    if k == TK_CHAR {
        let v, u = char_value(t);
        pe_advance();
        return v, u;
    }
    if k == TK_IDENT {
        if t.val == id_defined {
            // defined X / defined ( X ), read without expansion
            var n = pp_lex_unexpanded();
            var paren = false;
            if n.kind == TK_L_PAREN {
                paren = true;
                n = pp_lex_unexpanded();
            }
            if n.kind != TK_IDENT {
                pe_tok = n;
                pe_error("macro name must be an identifier");
                return 0, false;
            }
            let d = idents[n.val].macro >= 0;
            if paren {
                let c = pp_lex_unexpanded();
                if c.kind != TK_R_PAREN {
                    pe_tok = c;
                    pe_error("missing ')' after 'defined'");
                    return 0, false;
                }
            }
            pe_advance();
            return if d { 1 } else { 0 }, false;
        }
        // Any other identifier is 0.
        pe_advance();
        return 0, false;
    }
    if k == TK_EOD {
        pe_error("expected value in expression");
        return 0, false;
    }
    if k == TK_STRING {
        pe_error("invalid token at start of a preprocessor expression");
        return 0, false;
    }
    pe_error("invalid token at start of a preprocessor expression");
    return 0, false;
}

// An integer pp-number. Returns the value, unsignedness and success.
fn parse_pp_number(t: Tok) -> i64, bool, bool {
    let s = src[t.spell..t.spell + t.val];
    var i = 0;
    var base: u64 = 10;
    if s.len >= 2 && s[0] == '0' && (s[1] == 'x' || s[1] == 'X') { base = 16; i = 2; }
    else if s.len >= 2 && s[0] == '0' && (s[1] == 'b' || s[1] == 'B') { base = 2; i = 2; }
    else if s[0] == '0' { base = 8; }
    var v: u64 = 0;
    var overflow = false;
    let digits0 = i;
    while i < s.len {
        let c = s[i];
        var d: u64 = 99;
        if c >= '0' && c <= '9' { d = (c - '0') as u64; }
        else if c >= 'a' && c <= 'f' { d = (c - 'a' + 10) as u64; }
        else if c >= 'A' && c <= 'F' { d = (c - 'A' + 10) as u64; }
        else if c == '\'' { i++; continue; }
        if d >= base { break; }
        if mul_add_overflows(v, base, d) { overflow = true; }
        v = v * base + d;
        i++;
    }
    if base == 16 && i == digits0 { return 0, false, false; }
    // Suffix.
    var uns = false;
    var j = i;
    var nl = 0;
    while j < s.len {
        let c = s[j];
        if c == 'u' || c == 'U' {
            if uns { return 0, false, false; }
            uns = true;
        } else if c == 'l' || c == 'L' {
            nl++;
            if nl > 2 { return 0, false, false; }
        } else {
            return 0, false, false;
        }
        j++;
    }
    if overflow { pe_error("integer literal is too large to be represented in any integer type"); }
    if !uns && v > 9223372036854775807 { uns = true; }
    return v as! i64, uns, true;
}

// The value of a character constant (clang semantics on x86-64 linux).
fn char_value(t: Tok) -> i64, bool {
    let s = src[t.spell..t.spell + t.val];
    var i = 0;
    var kind = 0;    // 0 plain, 1 L, 2 u, 3 U, 4 u8
    if s[0] == 'L' { kind = 1; i = 1; }
    else if s[0] == 'u' && s[1] == '8' { kind = 4; i = 2; }
    else if s[0] == 'u' { kind = 2; i = 1; }
    else if s[0] == 'U' { kind = 3; i = 1; }
    i++;    // the quote
    var v: i64 = 0;
    var n = 0;
    var last: i64 = 0;
    while i < s.len - 1 {
        var c: i64 = s[i];
        i++;
        if c == '\\' {
            let e = s[i];
            i++;
            if e == 'n' { c = 10; } else if e == 't' { c = 9; } else if e == 'r' { c = 13; }
            else if e == 'v' { c = 11; } else if e == 'b' { c = 8; } else if e == 'f' { c = 12; }
            else if e == 'a' { c = 7; } else if e == 'e' || e == 'E' { c = 27; }
            else if e >= '0' && e <= '7' {
                c = (e - '0') as i64;
                var k = 1;
                while k < 3 && i < s.len - 1 && s[i] >= '0' && s[i] <= '7' { c = c * 8 + (s[i] - '0'); i++; k++; }
            } else if e == 'x' {
                c = 0;
                while i < s.len - 1 {
                    let h = s[i];
                    var d: i64 = -1;
                    if h >= '0' && h <= '9' { d = (h - '0') as i64; } else if h >= 'a' && h <= 'f' { d = (h - 'a' + 10) as i64; }
                    else if h >= 'A' && h <= 'F' { d = (h - 'A' + 10) as i64; }
                    if d < 0 { break; }
                    c = c * 16 + d;
                    i++;
                }
            } else if e == 'u' || e == 'U' {
                let nd = if e == 'u' { 4 } else { 8 };
                c = 0;
                var k = 0;
                while k < nd && i < s.len - 1 {
                    let h = s[i];
                    var d: i64 = 0;
                    if h >= '0' && h <= '9' { d = (h - '0') as i64; } else if h >= 'a' && h <= 'f' { d = (h - 'a' + 10) as i64; }
                    else if h >= 'A' && h <= 'F' { d = (h - 'A' + 10) as i64; }
                    c = c * 16 + d;
                    i++;
                    k++;
                }
            } else {
                c = e;
            }
        } else if (kind == 1 || kind == 2 || kind == 3) && c >= 192 {
            // a UTF-8 sequence in a wide character constant: one code point
            var cp = c & 31;
            var extra = 1;
            if c >= 240 { cp = c & 7; extra = 3; } else if c >= 224 { cp = c & 15; extra = 2; }
            var k = 0;
            while k < extra && i < s.len - 1 { cp = (cp << 6) | ((s[i] & 63) as i64); i++; k++; }
            c = cp;
        }
        last = c;
        v = (v << 8) | (c & 255);
        n++;
    }
    if kind == 0 {
        if n == 1 {
            // plain char is signed
            let b = last & 255;
            return if b >= 128 { b - 256 } else { b }, false;
        }
        // multi-character constant: an int
        let w = v & 4294967295;
        return if w >= 2147483648 { w - 4294967296 } else { w }, false;
    }
    if kind == 1 { return last, false; }
    if kind == 4 { return last & 255, false; }
    return last, true;
}

// ---------------------------------------------------------------------------
// Builtin macros.

let B_LINE = 1;
let B_FILE = 2;
let B_COUNTER = 3;
let B_DATE = 4;
let B_TIME = 5;
let B_INCLUDE_LEVEL = 6;
let B_BASE_FILE = 7;
let B_FILE_NAME = 8;
let B_TIMESTAMP = 9;
let B_PRAGMA = 10;
let B_HAS_INCLUDE = 11;
let B_HAS_INCLUDE_NEXT = 12;
let B_HAS_BUILTIN = 13;
let B_HAS_FEATURE = 14;
let B_HAS_EXTENSION = 15;
let B_HAS_ATTRIBUTE = 16;
let B_HAS_C_ATTRIBUTE = 17;
let B_HAS_DECLSPEC = 18;
let B_HAS_WARNING = 19;
let B_IS_IDENTIFIER = 20;
let B_HAS_CONSTEXPR_BUILTIN = 21;
let B_HAS_EMBED = 22;
let B_IS_TARGET_ARCH = 23;
let B_IS_TARGET_VENDOR = 24;
let B_IS_TARGET_OS = 25;
let B_IS_TARGET_ENV = 26;
let B_IS_TARGET_VARIANT_OS = 27;
let B_IS_TARGET_VARIANT_ENV = 28;
let B_BUILDING_MODULE = 29;
let B_FLT_EVAL_METHOD = 30;
let B_LITERAL_ENCODING = 31;
let B_WIDE_LITERAL_ENCODING = 32;

var base_file_name: u32 = 0;
var base_file_name_len: u32 = 0;
var bt: u8[>..] = [];

fn table_text(k: i64) -> const u8[:] {
    return match k {
        0 => HAS_BUILTIN, 1 => HAS_FEATURE, 2 => HAS_EXTENSION, 3 => HAS_ATTRIBUTE,
        4 => HAS_C_ATTRIBUTE, 5 => HAS_DECLSPEC_ATTRIBUTE, _ => WARNING_OPTIONS,
    };
}

// The value of `name` in table k: the number after it on its line (1 when
// there is none), 0 for a name not in the table. The lookup goes through
// the static hash tables of tables_gen.goose.
fn table_lookup(k: i64, name: const u8[:]) -> i64 {
    let text = table_text(k);
    let h = hash_bytes(name);
    let e = match k {
        0 => tbl_find(text, TBL_HAS_BUILTIN_OFF, TBL_HAS_BUILTIN_HT, TBL_HAS_BUILTIN_LEN, name, h, ' '),
        1 => tbl_find(text, TBL_HAS_FEATURE_OFF, TBL_HAS_FEATURE_HT, TBL_HAS_FEATURE_LEN, name, h, ' '),
        2 => tbl_find(text, TBL_HAS_EXTENSION_OFF, TBL_HAS_EXTENSION_HT, TBL_HAS_EXTENSION_LEN, name, h, ' '),
        3 => tbl_find(text, TBL_HAS_ATTRIBUTE_OFF, TBL_HAS_ATTRIBUTE_HT, TBL_HAS_ATTRIBUTE_LEN, name, h, ' '),
        4 => tbl_find(text, TBL_HAS_C_ATTRIBUTE_OFF, TBL_HAS_C_ATTRIBUTE_HT, TBL_HAS_C_ATTRIBUTE_LEN, name, h, ' '),
        5 => tbl_find(text, TBL_HAS_DECLSPEC_ATTRIBUTE_OFF, TBL_HAS_DECLSPEC_ATTRIBUTE_HT, TBL_HAS_DECLSPEC_ATTRIBUTE_LEN, name, h, ' '),
        _ => tbl_find(text, TBL_WARNING_OPTIONS_OFF, TBL_WARNING_OPTIONS_HT, TBL_WARNING_OPTIONS_LEN, name, h, ' '),
    };
    if e < 0 || name.len == 0 { return 0; }
    let off: u32 = match k {
        0 => TBL_HAS_BUILTIN_OFF[e], 1 => TBL_HAS_FEATURE_OFF[e], 2 => TBL_HAS_EXTENSION_OFF[e],
        3 => TBL_HAS_ATTRIBUTE_OFF[e], 4 => TBL_HAS_C_ATTRIBUTE_OFF[e], 5 => TBL_HAS_DECLSPEC_ATTRIBUTE_OFF[e],
        _ => TBL_WARNING_OPTIONS_OFF[e],
    };
    var j = off as i64 + name.len;
    if j >= text.len || text[j] != ' ' { return 1; }
    j++;
    var v: i64 = 0;
    while j < text.len && text[j] >= '0' && text[j] <= '9' { v = v * 10 + (text[j] - '0'); j++; }
    return v;
}

fn warning_known(name: const u8[:]) -> bool { table_lookup(6, name) != 0 }

fn feature_value(kind: i64, name: const u8[:]) -> i64 {
    var nm = name;
    if nm.len >= 4 && nm[0] == '_' && nm[1] == '_' && nm[nm.len - 1] == '_' && nm[nm.len - 2] == '_' {
        nm = nm[2..nm.len - 2];
    }
    if kind == B_HAS_FEATURE {
        if !opt_std_c11 && starts_with(nm, "c_") && nm != "c_fixed_enum" { return 0; }
        return table_lookup(1, nm);
    }
    return table_lookup(2, nm);
}

fn attr_value(k: i64, name: const u8[:]) -> i64 {
    // Normalize __x__ (also after a scope).
    var bt2: u8[>..] = [];
    var nm = name;
    var scope_len = -1;
    let cpos = find(nm, "::");
    if cpos >= 0 {
        bt2.append(nm[..cpos + 2]);
        nm = nm[cpos + 2..];
        scope_len = cpos;
    }
    if nm.len >= 4 && nm[0] == '_' && nm[1] == '_' && nm[nm.len - 1] == '_' && nm[nm.len - 2] == '_' {
        nm = nm[2..nm.len - 2];
    }
    bt2.append(nm);
    return table_lookup(k, bt2);
}

fn two(out: u8[>..]&, v: i64) {
    out.push(('0' + v / 10) as! u8);
    out.push(('0' + v % 10) as! u8);
}

// Seconds since the epoch: SOURCE_DATE_EPOCH or now (UTC).
fn build_time() -> i64 {
    var e: u8[>..] = [];
    if env("SOURCE_DATE_EPOCH", e) {
        let v, ok = parse_int(e);
        if ok { return v; }
    }
    return time_ns() / 1000000000;
}

fn civil(t: i64) -> i64, i64, i64, i64, i64, i64, i64 {
    let days = div_euclid(t, 86400);
    let secs = t - days * 86400;
    let z = days + 719468;
    let era = div_euclid(z, 146097);
    let doe = z - era * 146097;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y0 = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y0 + 1 } else { y0 };
    let wday = (days + 4) % 7;   // 1970-01-01 was a Thursday
    return y, m, d, secs / 3600, (secs / 60) % 60, secs % 60, wday;
}

let MONTHS = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"];
let WDAYS = ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"];

fn quoted_into(out: u8[>..]&, s: const u8[:]) {
    out.push('"');
    for c in s {
        if c == '\\' || c == '"' { out.push('\\'); }
        out.push(c);
    }
    out.push('"');
}

// The presumed line of a location.
fn presumed_line(loc: i64) -> i64 {
    let f = file_of(loc);
    if f < 0 { return 1; }
    let line, col = line_col(f, loc);
    let ci = cur_file_ctx;
    if ctxs[ci].file as i64 == f { return line + ctxs[ci].line_delta; }
    return line;
}

// Reads `( identifier )` for __has_feature and friends. Returns the ident
// (or -1) and leaves the scoped name text in bt.
recursive fn builtin_paren_name(name: Tok, expand: bool) -> i64 {
    let lp = pp_lex_unexpanded();
    if lp.kind != TK_L_PAREN {
        error_at(name.xloc as i64, str("missing '(' after '", ident_text(name.val as i64), "'"));
        return -1;
    }
    bt.clear();
    var t = if expand { pp_lex() } else { pp_lex_unexpanded() };
    var id: i64 = -1;
    var depth = 0;
    loop {
        if t.kind == TK_EOD || t.kind == TK_EOF {
            error_at(name.xloc as i64, "missing ')' after builtin feature-check macro");
            return -1;
        }
        if t.kind == TK_R_PAREN && depth == 0 { break; }
        if t.kind == TK_L_PAREN { depth++; }
        if t.kind == TK_R_PAREN { depth--; }
        if t.kind == TK_IDENT && id < 0 { id = t.val as i64; }
        if t.kind == TK_STRING {
            // __has_warning("-Wx")
            string_body(t, bt);
        } else {
            tok_spelling(bt, t);
        }
        t = if expand { pp_lex() } else { pp_lex_unexpanded() };
    }
    return id;
}

recursive fn has_include(name: Tok, next: bool) -> i64 {
    let lp = pp_lex_unexpanded();
    if lp.kind != TK_L_PAREN {
        error_at(name.xloc as i64, "missing '(' after '__has_include'");
        return 0;
    }
    inc_name.clear();
    var angled = false;
    var t: Tok;
    if ctxs[ctxs.len - 1].kind == CTX_FILE {
        t = lex_header_name();
    } else {
        t = pp_lex();
    }
    if t.kind == TK_HEADER {
        angled = true;
        inc_name.append(src[t.spell + 1..t.spell + t.val - 1]);
    } else if t.kind == TK_STRING {
        inc_name.append(src[t.spell + 1..t.spell + t.val - 1]);
    } else {
        if t.kind == TK_IDENT && ctxs[ctxs.len - 1].kind == CTX_FILE {
            // re-lex with expansion
            let s0 = streams.len;
            streams.push(t);
            enter_stream(s0, false);
            t = pp_lex();
        }
        if t.kind == TK_STRING {
            inc_name.append(src[t.spell + 1..t.spell + t.val - 1]);
        } else if t.kind == TK_LESS {
            angled = true;
            t = pp_lex();
            var firstt = true;
            while t.kind != TK_GREATER && t.kind != TK_EOD && t.kind != TK_EOF {
                if !firstt && t.flags & F_LSPACE != 0 { inc_name.push(' '); }
                firstt = false;
                tok_spelling(inc_name, t);
                t = pp_lex();
            }
        } else {
            error_at(name.xloc as i64, "expected \"FILENAME\" or <FILENAME>");
            return 0;
        }
    }
    let rp = pp_lex_unexpanded();
    if rp.kind != TK_R_PAREN {
        error_at(name.xloc as i64, "missing ')' after '__has_include'");
    }
    let f = find_include(inc_name, angled, next);
    return if f >= 0 { 1 } else { 0 };
}

fn number_token(v: i64, like: Tok) -> Tok {
    var num_buf: u8[>..] = [];
    format(num_buf, v);
    return make_token(TK_NUMBER, num_buf, like);
}

recursive fn expand_builtin(name: Tok, b: i64) -> i64 {
    var like = name;
    like.flags = name.flags & (F_BOL | F_LSPACE);
    if b == B_LINE {
        builtin_result = number_token(presumed_line(name.xloc as i64), like);
        return 2;
    }
    if b == B_FILE || b == B_FILE_NAME || b == B_BASE_FILE {
        let ci = cur_file_ctx;
        var so = ctxs[ci].pspell as i64;
        var se = so + ctxs[ci].pspell_len;
        if b == B_BASE_FILE { so = base_file_name as i64; se = so + base_file_name_len; }
        if b == B_FILE_NAME {
            var j = se;
            while j > so && names[j - 1] != '/' { j--; }
            so = j;
        }
        bt.clear();
        quoted_into(bt, names[so..se]);
        builtin_result = make_token(TK_STRING, bt, like);
        return 2;
    }
    if b == B_COUNTER {
        builtin_result = number_token(counter_value, like);
        counter_value++;
        return 2;
    }
    if b == B_INCLUDE_LEVEL {
        builtin_result = number_token(include_depth() - 1, like);
        return 2;
    }
    if b == B_DATE || b == B_TIME || b == B_TIMESTAMP {
        let y, mo, d, h, mi, s, wd = civil(build_time());
        bt.clear();
        bt.push('"');
        if b == B_DATE {
            bt.append(MONTHS[mo - 1]);
            bt.push(' ');
            if d < 10 { bt.push(' '); }
            format(bt, d, " ", y);
        } else if b == B_TIME {
            two(bt, h); bt.push(':'); two(bt, mi); bt.push(':'); two(bt, s);
        } else {
            bt.append(WDAYS[wd]);
            bt.push(' ');
            bt.append(MONTHS[mo - 1]);
            bt.push(' ');
            if d < 10 { bt.push(' '); }
            format(bt, d, " ");
            two(bt, h); bt.push(':'); two(bt, mi); bt.push(':'); two(bt, s);
            format(bt, " ", y);
        }
        bt.push('"');
        builtin_result = make_token(TK_STRING, bt, like);
        return 2;
    }
    if b == B_FLT_EVAL_METHOD {
        builtin_result = number_token(0, like);
        return 2;
    }
    if b == B_LITERAL_ENCODING || b == B_WIDE_LITERAL_ENCODING {
        builtin_result = make_token(TK_STRING, if b == B_LITERAL_ENCODING { "\"UTF-8\"" } else { "\"UTF-32\"" }, like);
        return 2;
    }
    if b == B_PRAGMA {
        return do_pragma_operator(name);
    }
    if b == B_HAS_INCLUDE || b == B_HAS_INCLUDE_NEXT {
        let v = has_include(name, b == B_HAS_INCLUDE_NEXT);
        builtin_result = number_token(v, like);
        return 2;
    }
    if b == B_BUILDING_MODULE {
        let id = builtin_paren_name(name, false);
        builtin_result = number_token(0, like);
        return 2;
    }
    // The feature-check macros: name ( identifier )
    let expand = b == B_HAS_ATTRIBUTE || b == B_HAS_C_ATTRIBUTE;
    let id = builtin_paren_name(name, expand);
    var v: i64 = 0;
    if b == B_HAS_BUILTIN || b == B_HAS_CONSTEXPR_BUILTIN {
        v = table_lookup(0, bt);
        if b == B_HAS_CONSTEXPR_BUILTIN { v = 0; }
    } else if b == B_HAS_FEATURE || b == B_HAS_EXTENSION {
        v = feature_value(b, bt);
    } else if b == B_HAS_ATTRIBUTE {
        v = attr_value(3, bt);
    } else if b == B_HAS_C_ATTRIBUTE {
        v = attr_value(4, bt);
    } else if b == B_HAS_DECLSPEC {
        v = attr_value(5, bt);
    } else if b == B_HAS_WARNING {
        v = if is_known_warning(bt) { 1 } else { 0 };
    } else if b == B_IS_IDENTIFIER {
        v = if id >= 0 && idents[id].kw == 0 { 1 } else { 0 };
    } else if b == B_IS_TARGET_ARCH {
        v = if bt == "x86_64" || bt == "amd64" || bt == "x86-64" { 1 } else { 0 };
    } else if b == B_IS_TARGET_VENDOR {
        v = if bt == "pc" || bt == "unknown" { 1 } else { 0 };
    } else if b == B_IS_TARGET_OS {
        v = if bt == "linux" { 1 } else { 0 };
    } else if b == B_IS_TARGET_ENV {
        v = if bt == "gnu" { 1 } else { 0 };
    }
    builtin_result = number_token(v, like);
    return 2;
}

// _Pragma ( string-literal )
recursive fn do_pragma_operator(name: Tok) -> i64 {
    let mark = streams.len;
    // Collect the tokens (with expansion), so that they can be put back.
    let lp = pp_lex();
    if lp.kind != TK_L_PAREN {
        error_at(name.xloc as i64, "_Pragma takes a parenthesized string literal");
        return 0;
    }
    let st = pp_lex();
    if st.kind != TK_STRING {
        error_at(name.xloc as i64, "_Pragma takes a parenthesized string literal");
        return 0;
    }
    let rp = pp_lex();
    if rp.kind != TK_R_PAREN {
        error_at(name.xloc as i64, "_Pragma takes a parenthesized string literal");
        return 0;
    }
    if in_preexp > 0 {
        // Defer: put the tokens back and return _Pragma itself.
        let s0 = streams.len;
        streams.push(lp);
        streams.push(st);
        streams.push(rp);
        enter_stream(s0, true);
        return 0;
    }
    run_pragma_operator(st, name);
    return 1;
}

// ---------------------------------------------------------------------------
// Initialization.

fn add_builtin(name: const u8[:], b: i64) {
    let id = intern(name);
    let m = macros.len;
    macros.push(Macro { name: id, first: 0, count: 0, nparams: 0, flags: M_BUILTIN, builtin: b as! u8, enabled: true, loc: 0 });
    idents[id].macro = m as! i32;
}

fn set_ppkw(name: const u8[:], k: i64) {
    let id = intern(name);
    idents[id].ppkw = k as! u8;
}

struct CmdMacro { def: bool, inc: bool, off: u32, len: u32 }   // -D, -U or -include (inc)
var cmd_macros: CmdMacro[>..] = [];
var std_off: u32 = 0;      // -std= (names)
var std_len: i64 = 0;
fn opt_std() -> const u8[:] { names[std_off..std_off + std_len] }
var opt_os: bool = false;
var opt_pic_mode: i64 = 0;     // 0 -fPIE (clang's default), 1 -fpie, 2 -fPIC, 3 -fpic, 4 -fno-pic
var opt_pthread: bool = false;
var opt_unsigned_char: bool = false;

fn pp_init_tables() {
    lex_init_tables();
    // Reserve ident 0 so that 0 can mean "none".
    intern("");
    set_ppkw("if", PK_IF); set_ppkw("ifdef", PK_IFDEF); set_ppkw("ifndef", PK_IFNDEF);
    set_ppkw("elif", PK_ELIF); set_ppkw("else", PK_ELSE); set_ppkw("endif", PK_ENDIF);
    set_ppkw("define", PK_DEFINE); set_ppkw("undef", PK_UNDEF); set_ppkw("include", PK_INCLUDE);
    set_ppkw("include_next", PK_INCLUDE_NEXT); set_ppkw("import", PK_IMPORT); set_ppkw("line", PK_LINE);
    set_ppkw("error", PK_ERROR); set_ppkw("warning", PK_WARNING); set_ppkw("pragma", PK_PRAGMA);
    set_ppkw("ident", PK_IDENT); set_ppkw("sccs", PK_SCCS); set_ppkw("elifdef", PK_ELIFDEF);
    set_ppkw("elifndef", PK_ELIFNDEF); set_ppkw("assert", PK_ASSERT); set_ppkw("unassert", PK_UNASSERT);
    id_defined = intern("defined");
    id_va_args = intern("__VA_ARGS__");
    id_va_opt = intern("__VA_OPT__");
    id_pragma_op = intern("_Pragma");
    add_builtin("__LINE__", B_LINE); add_builtin("__FILE__", B_FILE); add_builtin("__COUNTER__", B_COUNTER);
    add_builtin("__DATE__", B_DATE); add_builtin("__TIME__", B_TIME); add_builtin("__INCLUDE_LEVEL__", B_INCLUDE_LEVEL);
    add_builtin("__BASE_FILE__", B_BASE_FILE); add_builtin("__FILE_NAME__", B_FILE_NAME);
    add_builtin("__TIMESTAMP__", B_TIMESTAMP); add_builtin("_Pragma", B_PRAGMA);
    add_builtin("__has_include", B_HAS_INCLUDE); add_builtin("__has_include_next", B_HAS_INCLUDE_NEXT);
    add_builtin("__has_builtin", B_HAS_BUILTIN); add_builtin("__has_feature", B_HAS_FEATURE);
    add_builtin("__has_extension", B_HAS_EXTENSION); add_builtin("__has_attribute", B_HAS_ATTRIBUTE);
    add_builtin("__has_c_attribute", B_HAS_C_ATTRIBUTE); add_builtin("__has_declspec_attribute", B_HAS_DECLSPEC);
    add_builtin("__has_warning", B_HAS_WARNING); add_builtin("__is_identifier", B_IS_IDENTIFIER);
    add_builtin("__has_constexpr_builtin", B_HAS_CONSTEXPR_BUILTIN); add_builtin("__has_embed", B_HAS_EMBED);
    add_builtin("__is_target_arch", B_IS_TARGET_ARCH); add_builtin("__is_target_vendor", B_IS_TARGET_VENDOR);
    add_builtin("__is_target_os", B_IS_TARGET_OS); add_builtin("__is_target_environment", B_IS_TARGET_ENV);
    add_builtin("__is_target_variant_os", B_IS_TARGET_VARIANT_OS);
    add_builtin("__is_target_variant_environment", B_IS_TARGET_VARIANT_ENV);
    add_builtin("__building_module", B_BUILDING_MODULE); add_builtin("__FLT_EVAL_METHOD__", B_FLT_EVAL_METHOD);
    add_builtin("__clang_literal_encoding__", B_LITERAL_ENCODING);
    add_builtin("__clang_wide_literal_encoding__", B_WIDE_LITERAL_ENCODING);
}

// The <built-in> buffer: predefined macros adjusted for the options, then
// the command line -D/-U, then -include.

fn std_version() -> const u8[:] {
    let s = opt_std();
    if s == "c89" || s == "c90" || s == "gnu89" || s == "gnu90" || s == "iso9899:1990" { return ""; }
    if s == "c99" || s == "gnu99" || s == "iso9899:1999" || s == "c9x" || s == "gnu9x" { return "199901L"; }
    if s == "c11" || s == "gnu11" || s == "iso9899:2011" || s == "c1x" || s == "gnu1x" { return "201112L"; }
    return "201710L";
}

// Appends it to src.
fn build_builtin_text() {
    let s = opt_std();
    let strict = s.len > 0 && s[0] != 'g';
    let c89 = std_version().len == 0;
    let text = PREDEF_BASE;
    var i = 0;
    while i < text.len {
        var j = i;
        while j < text.len && text[j] != '\n' { j++; }
        let line = text[i..j];
        i = j + 1;
        var keep = true;
        if line == "#define __NO_INLINE__ 1" && opt_optimize > 0 { keep = false; }
        if opt_pic_mode != 0 && (starts_with(line, "#define __PIC__ ") || starts_with(line, "#define __pic__ ") ||
                                 starts_with(line, "#define __PIE__ ") || starts_with(line, "#define __pie__ ")) {
            keep = false;
            let pie = line[12] == 'E' || line[12] == 'e';
            let lvl = if opt_pic_mode == 1 || opt_pic_mode == 3 { " 1\n" } else { " 2\n" };
            if opt_pic_mode <= 1 || (opt_pic_mode <= 3 && !pie) { src.append(line[..15]); src.append(lvl); }
        }
        if strict && (line == "#define linux 1" || line == "#define unix 1") { keep = false; }
        if starts_with(line, "#define __STDC_VERSION__ ") {
            keep = false;
            if !c89 { src.append("#define __STDC_VERSION__ "); src.append(std_version()); src.push('\n'); }
        }
        if c89 && line == "#define __GNUC_STDC_INLINE__ 1" {
            keep = false;
            src.append("#define __GNUC_GNU_INLINE__ 1\n");
        }
        if keep { src.append(line); src.push('\n'); }
    }
    if opt_optimize > 0 { src.append("#define __OPTIMIZE__ 1\n"); }
    if opt_os { src.append("#define __OPTIMIZE_SIZE__ 1\n"); }
    if strict { src.append("#define __STRICT_ANSI__ 1\n"); }
    if opt_pthread { src.append("#define _REENTRANT 1\n"); }
    if opt_unsigned_char { src.append("#define __CHAR_UNSIGNED__ 1\n"); }
    for m in cmd_macros {
        if m.inc { continue; }
        let d = names[m.off..m.off + m.len];
        if m.def {
            src.append("#define ");
            let eq = find(d, "=");
            if eq >= 0 {
                src.append(d[..eq]);
                src.push(' ');
                src.append(d[eq + 1..]);
            } else {
                src.append(d);
                src.append(" 1");
            }
        } else {
            src.append("#undef ");
            src.append(d);
        }
        src.push('\n');
    }
    for m in cmd_macros {
        if !m.inc { continue; }
        src.append("#include \"");
        src.append(names[m.off..m.off + m.len]);
        src.append("\"\n");
    }
}

// Sets the language options from -std.
fn pp_set_lang() {
    let s = opt_std();
    opt_gnu = s.len == 0 || s[0] == 'g';
    let v = std_version();
    opt_c99 = v.len > 0;
    opt_std_c11 = v == "201112L" || v == "201710L";
    opt_c11 = opt_std_c11;
    opt_trigraphs = !opt_gnu;
}

// Starts preprocessing `path`.
fn pp_start(path: const u8[:]) -> bool {
    pp_set_lang();
    pbuf.clear();
    pbuf.append(path);
    let f = lookup_file();
    if f < 0 {
        write_stderr(str("goosecc: error: no such file or directory: '", path, "'\n"));
        return false;
    }
    base_file_name = name_add(path);
    base_file_name_len = path.len as! u32;
    // The builtin buffer is file `files.len` (not in the path cache).
    let bstart = src.len;
    build_builtin_text();
    let bend = src.len;
    src.push(0);
    src.push(0);
    let bf = files.len;
    files.push(FileRec { path: name_add("<built-in>"), path_len: 10, start: bstart as! u32, end: bend as! u32, grd: -1, once: false, system: false, lines_first: -1, lines_count: 0, sp_off: 0, sp_len: 0 });
    let save = mode_E;
    mode_E = false;
    push_file(f, path, -1, false);
    push_file(bf, "<built-in>", -1, false);
    mode_E = save;
    if mode_E {
        pr_marker(1, ctxs[0].spell, ctxs[0].spell_len, "");
    }
    return true;
}
