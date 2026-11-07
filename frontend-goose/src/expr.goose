// goosecc: expressions. Recursive descent with the semantic checks done
// as each node is built: operands get their conversions as explicit
// N_ICAST nodes, every node gets its type.

import std;
import .common;
import .lex;
import .ppexpr;
import .types;
import .ast;
import .sema;
import .builtins;
import .dtype;

// ---------------------------------------------------------------------------
// The written type of an expression (-g, dtype.goose), for typeof and
// __auto_type: what clang's expression types keep of the sugar of
// declarations (a variable's, a member's, a cast's, a call's return type);
// otherwise the canonical type.

fn expr_written(n0: u32) -> u32 {
    if !dbg_types { return nodes[n0].ty; }
    var n = n0;
    var drop_quals = false;
    loop {
        let nd = nodes[n];
        let k = nd.kind as i64;
        if k == N_ICAST && (nd.op == CK_LVAL2RVAL || nd.op == CK_NOOP) {
            if nd.op == CK_LVAL2RVAL { drop_quals = true; }
            n = nd.a;
            continue;
        }
        if k == N_UNARY && nd.op == U_EXTENSION { n = nd.a; continue; }
        var w: u32 = 0;
        if k == N_DECLREF && syms[nd.a].kind == SK_VAR { w = sym_written(nd.a as i64); }
        else if k == N_MEMBER { w = field_written(nd.b as i64); }
        else if k == N_CAST { w = node_written(n); }
        else if k == N_CALL {
            // the callee's written function type: through FUNC2PTR to the symbol
            var c = nd.a;
            while nodes[c].kind as i64 == N_ICAST { c = nodes[c].a; }
            if nodes[c].kind as i64 == N_DECLREF && syms[nodes[c].a].kind == SK_FUNC {
                let f = sym_written(nodes[c].a as i64);
                if dq_sugar(f) && dtypes[dq_node(f)].kind as i64 == DK_FUNC { w = dtypes[dq_node(f)].base; }
            }
        }
        if w == 0 || dq_canon(d_unqual(w)) != unqual(nodes[n].ty) { return nodes[n0].ty; }
        if drop_quals { w = d_unqual(w); }
        return w;
    }
}

// ---------------------------------------------------------------------------
// Literals.

fn is_hex_digit(c: u8) -> bool { (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F') }
fn hexval(c: u8) -> u64 {
    if c >= '0' && c <= '9' { return (c - '0') as u64; }
    if c >= 'a' && c <= 'f' { return (c - 'a' + 10) as u64; }
    return (c - 'A' + 10) as u64;
}


fn number_literal(t: Tok) -> u32 {
    let s = src[t.spell..t.spell + t.val];
    let loc = t.xloc;
    var hex = s.len >= 2 && s[0] == '0' && (s[1] == 'x' || s[1] == 'X');
    var isfloat = false;
    for c, i in s {
        if c == '.' { isfloat = true; }
        if !hex && (c == 'e' || c == 'E') && i > 0 { isfloat = true; }
        if hex && (c == 'p' || c == 'P') { isfloat = true; }
    }
    if isfloat { return float_literal(s, loc, hex, t.spell); }
    var i = 0;
    var base: u64 = 10;
    if hex { base = 16; i = 2; }
    else if s.len >= 2 && s[0] == '0' && (s[1] == 'b' || s[1] == 'B') { base = 2; i = 2; }
    else if s[0] == '0' { base = 8; }
    var v: u64 = 0;
    var overflow = false;
    while i < s.len {
        let c = s[i];
        if c == '\'' { i++; continue; }
        if !is_hex_digit(c) { break; }
        let d = hexval(c);
        if d >= base {
            if base == 8 && d < 10 {
                err_at(loc, str("invalid digit '", s[i..i + 1], "' in octal constant"));
                return node(N_INT, 0, t_int, 0, 0, 0, loc);
            }
            break;
        }
        if mul_add_overflows(v, base, d) { overflow = true; }
        v = v * base + d;
        i++;
    }
    var uns = false;
    var nl = 0;
    var imag = false;
    while i < s.len {
        let c = s[i];
        if c == 'u' || c == 'U' { uns = true; }
        else if c == 'l' || c == 'L' { nl++; }
        else if c == 'i' || c == 'j' { imag = true; }
        else {
            err_at(loc, str("invalid suffix '", s[i..], "' on integer constant"));
            return node(N_INT, 0, t_int, 0, 0, 0, loc);
        }
        i++;
    }
    if overflow { err_at(loc, "integer literal is too large to be represented in any integer type"); }
    let dec = base == 10;
    var ty = t_int;
    // C11 6.4.4.1: the first type in the list that can represent the value.
    if !uns && nl == 0 && v <= 2147483647 { ty = t_int; }
    else if (uns || !dec) && nl == 0 && v <= 4294967295 { ty = t_uint; }
    else if !uns && nl <= 1 && v <= 9223372036854775807 { ty = t_long; }
    else if (uns || !dec) && nl <= 1 { ty = t_ulong; }
    else if !uns && v <= 9223372036854775807 { ty = t_llong; }
    else if uns || !dec { ty = t_ullong; }
    else {
        warn(loc, "integer literal is too large to be represented in a signed integer type, interpreting as unsigned");
        ty = if nl <= 1 { t_ulong } else { t_ullong };
    }
    if uns && nl == 0 && v > 4294967295 { ty = t_ulong; }
    if uns && nl == 1 { ty = t_ulong; }
    if uns && nl == 2 { ty = t_ullong; }
    var n = node_v(N_INT, 0, ty, 0, 0, 0, loc, v as! i64);
    nodes[n].flags = NF_ICE;
    if imag {
        let ct = mk_complex(ty);
        n = node(N_BUILTIN, BI_IMAG_CONST, ct, n as i64, 0, 0, loc);
    }
    return n;
}

fn float_literal(s: const u8[:], loc: u32, hex: bool, off: u32) -> u32 {
    var e = s.len;
    var ty = t_double;
    var imag = false;
    // suffixes
    loop {
        if e == 0 { break; }
        let c = s[e - 1];
        if c == 'f' || c == 'F' {
            if e >= 3 && s[e - 2] == '1' && s[e - 3] == 'f' { break; }
            ty = t_float; e--; continue;
        }
        if c == 'l' || c == 'L' { ty = t_ldouble; e--; continue; }
        if c == 'q' || c == 'Q' { ty = t_float128; e--; continue; }
        if c == 'i' || c == 'j' { imag = true; e--; continue; }
        if c == '6' && e >= 3 && s[e - 2] == '1' && (s[e - 3] == 'f' || s[e - 3] == 'F') && !hex {
            ty = t_float16; e -= 3; continue;
        }
        break;
    }
    let body = s[..e];
    var v = 0.0;
    if hex {
        var m: f64 = 0.0;
        var i = 2;
        var exp: i64 = 0;
        var seen_dot = false;
        while i < body.len && (is_hex_digit(body[i]) || body[i] == '.') {
            if body[i] == '.' { seen_dot = true; }
            else {
                m = m * 16.0 + (hexval(body[i]) as f64);
                if seen_dot { exp -= 4; }
            }
            i++;
        }
        if i < body.len && (body[i] == 'p' || body[i] == 'P') {
            i++;
            var neg = false;
            if i < body.len && (body[i] == '+' || body[i] == '-') { neg = body[i] == '-'; i++; }
            var x: i64 = 0;
            while i < body.len && body[i] >= '0' && body[i] <= '9' { x = x * 10 + (body[i] - '0'); i++; }
            exp += if neg { -x } else { x };
        }
        v = float_text::ldexp(m, exp as! i32);
    } else {
        var lit_buf: u8[>..] = [];
        for c in body { if c != '\'' { lit_buf.push(c); } }
        // parse_flt wants a digit before a '.'
        if lit_buf.len > 0 && lit_buf[0] == '.' {
            var t2: u8[>..] = [];
            t2.push('0');
            t2.append(lit_buf);
            lit_buf.clear();
            lit_buf.append(t2);
        }
        let f, ok = parse_flt(lit_buf);
        if !ok {
            // "1." and "1.e5"
            var t2: u8[>..] = [];
            for c, i in lit_buf {
                t2.push(c);
                if c == '.' && (i + 1 >= lit_buf.len || lit_buf[i + 1] < '0' || lit_buf[i + 1] > '9') { t2.push('0'); }
            }
            let f2, ok2 = parse_flt(t2);
            if !ok2 { err_at(loc, "invalid floating point constant"); }
            v = f2;
        } else {
            v = f;
        }
    }
    if kind_of(ty) == TY_FLOAT { v = round_f32(v); }
    // b, c: the literal's text without suffix (B2 lowering converts it exactly)
    var n = node_v(N_FLOAT, 0, ty, 0, off as i64, e, loc, reinterpret_i64(v));
    if imag {
        n = node(N_BUILTIN, BI_IMAG_CONST, mk_complex(ty), n as i64, 0, 0, loc);
    }
    return n;
}

fn char_literal(t: Tok) -> u32 {
    let v, u = char_value(t);
    let c = src[t.spell];
    var ty = t_int;
    if c == 'u' {
        ty = if src[t.spell + 1] == '8' { t_uchar } else { t_ushort };
    } else if c == 'U' {
        ty = t_uint;
    }
    var vv = v;
    if ty == t_ushort { vv = v & 65535; }
    if ty == t_uint { vv = v & 4294967295; }
    if ty == t_uchar { vv = v & 255; }
    let n = node_v(N_INT, 0, ty, 0, 0, 0, t.xloc, vv);
    nodes[n].flags = NF_ICE;
    return n;
}

// Appends code point cp in the string's element encoding.
fn str_put(width: i64, cp: i64) {
    if width == 1 {
        strbytes.push((cp & 255) as! u8);
    } else if width == 2 {
        strbytes.push((cp & 255) as! u8);
        strbytes.push(((cp >> 8) & 255) as! u8);
    } else {
        strbytes.push((cp & 255) as! u8);
        strbytes.push(((cp >> 8) & 255) as! u8);
        strbytes.push(((cp >> 16) & 255) as! u8);
        strbytes.push(((cp >> 24) & 255) as! u8);
    }
}

fn utf8_put(cp: i64) {
    if cp < 128 { strbytes.push(cp as! u8); }
    else if cp < 2048 { strbytes.push((192 | (cp >> 6)) as! u8); strbytes.push((128 | (cp & 63)) as! u8); }
    else if cp < 65536 {
        strbytes.push((224 | (cp >> 12)) as! u8); strbytes.push((128 | ((cp >> 6) & 63)) as! u8); strbytes.push((128 | (cp & 63)) as! u8);
    } else {
        strbytes.push((240 | (cp >> 18)) as! u8); strbytes.push((128 | ((cp >> 12) & 63)) as! u8);
        strbytes.push((128 | ((cp >> 6) & 63)) as! u8); strbytes.push((128 | (cp & 63)) as! u8);
    }
}

// Decodes the body of one string token into strbytes (elements of `width`).
fn decode_string(t: Tok, width: i64) -> i64 {
    let s = src[t.spell..t.spell + t.val];
    var i = 0;
    while s[i] != '"' { i++; }
    i++;
    var count = 0;
    let e = s.len - 1;
    while i < e {
        var c = s[i] as i64;
        if c == '\\' {
            i++;
            let x = s[i];
            i++;
            if x == 'n' { c = 10; } else if x == 't' { c = 9; } else if x == 'r' { c = 13; }
            else if x == 'v' { c = 11; } else if x == 'b' { c = 8; } else if x == 'f' { c = 12; }
            else if x == 'a' { c = 7; } else if x == 'e' || x == 'E' { c = 27; }
            else if x >= '0' && x <= '7' {
                c = (x - '0') as i64;
                var k = 1;
                while k < 3 && i < e && s[i] >= '0' && s[i] <= '7' { c = c * 8 + (s[i] - '0'); i++; k++; }
            } else if x == 'x' {
                c = 0;
                while i < e && is_hex_digit(s[i]) { c = c * 16 + (hexval(s[i]) as i64); i++; }
            } else if x == 'u' || x == 'U' {
                let nd = if x == 'u' { 4 } else { 8 };
                c = 0;
                var k = 0;
                while k < nd && i < e && is_hex_digit(s[i]) { c = c * 16 + (hexval(s[i]) as i64); i++; k++; }
                if width == 1 { utf8_put(c); count += 0; continue; }
            } else {
                c = x as i64;
            }
            str_put(width, c);
            count++;
            continue;
        }
        if width > 1 && c >= 128 {
            // decode UTF-8 into a code point
            var cp = c;
            var extra = 0;
            if c >= 240 { cp = c & 7; extra = 3; } else if c >= 224 { cp = c & 15; extra = 2; } else if c >= 192 { cp = c & 31; extra = 1; }
            i++;
            var k = 0;
            while k < extra && i < e { cp = (cp << 6) | ((s[i] & 63) as i64); i++; k++; }
            if width == 2 && cp >= 65536 {
                let u = cp - 65536;
                str_put(2, 55296 + (u >> 10));
                str_put(2, 56320 + (u & 1023));
                count += 2;
            } else {
                str_put(width, cp);
                count++;
            }
            continue;
        }
        if width > 1 { str_put(width, c); } else { strbytes.push(c as! u8); }
        count++;
        i++;
    }
    return count;
}

// One or more adjacent string literals.
fn string_literal() -> u32 {
    let loc = tloc();
    // the element type from the prefixes
    var width = 1;
    var elem = t_char;
    var j = pc;
    while j < tu_toks.len && tu_toks[j].kind == TK_STRING {
        let c = src[tu_toks[j].spell];
        if c == 'L' { width = 4; elem = t_int; }
        else if c == 'U' { width = 4; elem = t_uint; }
        else if c == 'u' && src[tu_toks[j].spell + 1] != '8' { width = 2; elem = t_ushort; }
        j++;
    }
    let start = strbytes.len;
    var count = 0;
    while at(TK_STRING) {
        count += decode_string(tu_toks[pc], width);
        adv();
    }
    // count elements: for width 1 the bytes, else computed
    if width == 1 { count = strbytes.len - start; }
    str_put(width, 0);
    let si = strs.len;
    strs.push(StrLit { start: start as! u32, len: (count + 1) as! u32, elem: elem });
    let ty = mk_array(elem, count + 1);
    let n = node(N_STRING, 0, ty, si, 0, 0, loc);
    nodes[n].flags = NF_LVALUE;
    return n;
}

var pf_out: u8[>..] = [];
fn make_string_node(s: const u8[:], loc: u32) -> u32 {
    let start = strbytes.len;
    strbytes.append(s);
    strbytes.push(0);
    let si = strs.len;
    strs.push(StrLit { start: start as! u32, len: (s.len + 1) as! u32, elem: t_char });
    let ty = mk_array(t_char | Q_CONST, s.len + 1);
    let n = node(N_STRING, 0, ty, si, 0, 0, loc);
    nodes[n].flags = NF_LVALUE | NF_PREDEF;
    return n;
}

fn int_node(v: i64, ty: u32, loc: u32) -> u32 {
    let n = node_v(N_INT, 0, ty, 0, 0, 0, loc, v);
    nodes[n].flags = NF_ICE;
    return n;
}

fn error_node(loc: u32) -> u32 { node(N_ERROR, 0, t_int, 0, 0, 0, loc) }
fn is_error(n: u32) -> bool { nodes[n].kind == N_ERROR }

// ---------------------------------------------------------------------------
// Expression grammar.

recursive fn parse_expr() -> u32 {
    var e = parse_assign();
    while at(TK_COMMA) {
        let loc = tloc();
        adv();
        let r = parse_assign();
        e = mk_comma(e, r, loc);
    }
    return e;
}

fn mk_comma(l: u32, r: u32, loc: u32) -> u32 {
    let b = rv(r);
    return node(N_BINARY, B_COMMA, nty(b), discard_value(l) as i64, b as i64, 0, loc);
}

// A discarded-value expression (expression statement, for-init/increment,
// left operand of a comma). C: an lvalue still undergoes lvalue conversion
// and functions and arrays decay (clang's IgnoredValueConversions).
fn discard_value(e: u32) -> u32 {
    if is_error(e) { return e; }
    let t = nty(e);
    if is_func(t) { return rv(e); }
    if !is_lvalue(e) || is_void(t) { return e; }
    if is_record(t) && !is_complete(t) { return e; }
    return rv(e);
}

fn assign_op(k: i64) -> i64 {
    return match k {
        TK_EQUAL => 100, TK_STAREQUAL => B_MUL, TK_SLASHEQUAL => B_DIV, TK_PERCENTEQUAL => B_REM,
        TK_PLUSEQUAL => B_ADD, TK_MINUSEQUAL => B_SUB, TK_LESSLESSEQUAL => B_SHL, TK_GREATERGREATEREQUAL => B_SHR,
        TK_AMPEQUAL => B_AND, TK_CARETEQUAL => B_XOR, TK_PIPEEQUAL => B_OR, _ => 0,
    };
}

recursive fn parse_assign() -> u32 {
    let l = parse_cond();
    let op = assign_op(tk());
    if op == 0 { return l; }
    let loc = tloc();
    adv();
    let r = parse_assign();
    return mk_assign(if op == 100 { 0 } else { op }, l, r, loc);
}

recursive fn parse_cond() -> u32 {
    let c = parse_binary(1);
    if !at(TK_QUESTION) { return c; }
    let loc = tloc();
    adv();
    if at(TK_COLON) {
        adv();
        let e = parse_cond();
        return mk_cond(c, 0, e, loc);
    }
    let a = parse_expr();
    expect(TK_COLON, "':'");
    let b = parse_cond();
    return mk_cond(c, a, b, loc);
}

fn bin_prec(k: i64) -> i64 {
    return match k {
        TK_PIPEPIPE => 1, TK_AMPAMP => 2, TK_PIPE => 3, TK_CARET => 4, TK_AMP => 5,
        TK_EQUALEQUAL, TK_EXCLAIMEQUAL => 6,
        TK_LESS, TK_GREATER, TK_LESSEQUAL, TK_GREATEREQUAL => 7,
        TK_LESSLESS, TK_GREATERGREATER => 8,
        TK_PLUS, TK_MINUS => 9,
        TK_STAR, TK_SLASH, TK_PERCENT => 10,
        _ => 0,
    };
}

fn bin_op(k: i64) -> i64 {
    return match k {
        TK_PIPEPIPE => B_LOR, TK_AMPAMP => B_LAND, TK_PIPE => B_OR, TK_CARET => B_XOR, TK_AMP => B_AND,
        TK_EQUALEQUAL => B_EQ, TK_EXCLAIMEQUAL => B_NE, TK_LESS => B_LT, TK_GREATER => B_GT,
        TK_LESSEQUAL => B_LE, TK_GREATEREQUAL => B_GE, TK_LESSLESS => B_SHL, TK_GREATERGREATER => B_SHR,
        TK_PLUS => B_ADD, TK_MINUS => B_SUB, TK_STAR => B_MUL, TK_SLASH => B_DIV, _ => B_REM,
    };
}

recursive fn parse_binary(minp: i64) -> u32 {
    var l = parse_cast();
    loop {
        let k = tk();
        let p = bin_prec(k);
        if p == 0 || p < minp { break; }
        let loc = tloc();
        adv();
        let r = parse_binary(p + 1);
        l = mk_binary(bin_op(k), l, r, loc);
    }
    return l;
}

recursive fn parse_cast() -> u32 {
    if at(TK_L_PAREN) && starts_type_name(pc + 1) {
        let loc = tloc();
        adv();
        let ty = parse_type_name();
        let dty = tn_dty;
        expect(TK_R_PAREN, "')'");
        if at(TK_L_BRACE) {
            let e = parse_compound_literal(ty, loc);
            return parse_postfix(e);
        }
        let e = parse_cast();
        let c = mk_cast(ty, e, loc);
        if dbg_types && nodes[c].kind as i64 == N_CAST { dt_set_node(c, d_unqual(dty)); }
        return c;
    }
    return parse_unary();
}

recursive fn parse_unary() -> u32 {
    let k = tk();
    let loc = tloc();
    if k == TK_PLUSPLUS || k == TK_MINUSMINUS {
        adv();
        let e = parse_unary();
        return mk_incdec(e, if k == TK_PLUSPLUS { U_PREINC } else { U_PREDEC }, loc);
    }
    if k == TK_AMP {
        adv();
        let e = parse_cast();
        return mk_addr(e, loc);
    }
    if k == TK_AMPAMP {
        // GNU: the address of a label
        adv();
        if !at(TK_IDENT) { err("expected identifier"); return error_node(loc); }
        let ls = label_ref(tval(), loc);
        adv();
        return node(N_LABELADDR, 0, t_voidptr, ls, 0, 0, loc);
    }
    if k == TK_STAR {
        adv();
        let e = parse_cast();
        return mk_deref(e, loc);
    }
    if k == TK_PLUS || k == TK_MINUS || k == TK_TILDE || k == TK_EXCLAIM {
        adv();
        let e = parse_cast();
        let op = match k { TK_PLUS => U_PLUS, TK_MINUS => U_NEG, TK_TILDE => U_BITNOT, _ => U_NOT };
        return mk_unary_arith(op, e, loc);
    }
    if k == kw(KW_SIZEOF) || k == kw(KW_ALIGNOF) {
        adv();
        let is_align = k == kw(KW_ALIGNOF);
        if at(TK_L_PAREN) && starts_type_name(pc + 1) {
            adv();
            let ty = parse_type_name();
            expect(TK_R_PAREN, "')'");
            if at(TK_L_BRACE) {
                // sizeof (T){...}: a compound literal operand
                let cl = parse_compound_literal(ty, loc);
                let e = parse_postfix(cl);
                return mk_sizeof_expr(e, is_align, loc);
            }
            return mk_sizeof_type(ty, is_align, loc);
        }
        let e = parse_unary();
        return mk_sizeof_expr(e, is_align, loc);
    }
    if k == kw(KW_EXTENSION) {
        adv();
        return parse_cast();
    }
    if k == kw(KW_REAL) || k == kw(KW_IMAG) {
        adv();
        let e = parse_cast();
        return mk_real_imag(e, k == kw(KW_REAL), loc);
    }
    let p = parse_primary();
    return parse_postfix(p);
}

recursive fn parse_postfix(e0: u32) -> u32 {
    var e = e0;
    loop {
        let k = tk();
        let loc = tloc();
        if k == TK_L_SQUARE {
            adv();
            let idx = parse_expr();
            expect(TK_R_SQUARE, "']'");
            e = mk_index(e, idx, loc);
        } else if k == TK_L_PAREN {
            e = parse_call(e);
        } else if k == TK_PERIOD || k == TK_ARROW {
            adv();
            if !at(TK_IDENT) && tk() < TK_KW {
                err("expected identifier");
                return error_node(loc);
            }
            let name = tval();
            let nloc = tloc();
            adv();
            e = mk_member(e, name, k == TK_ARROW, nloc);
        } else if k == TK_PLUSPLUS || k == TK_MINUSMINUS {
            adv();
            e = mk_incdec(e, if k == TK_PLUSPLUS { U_POSTINC } else { U_POSTDEC }, loc);
        } else {
            break;
        }
    }
    return e;
}

recursive fn parse_call(callee: u32) -> u32 {
    let loc = tloc();
    adv();   // (
    let mark = nscratch.len;
    if !at(TK_R_PAREN) {
        loop {
            let a = parse_assign();
            nscratch.push(a);
            if !accept(TK_COMMA) { break; }
        }
    }
    expect(TK_R_PAREN, "')'");
    return mk_call(callee, mark, loc);
}

recursive fn parse_primary() -> u32 {
    let t = tu_toks[pc];
    let k = t.kind as i64;
    let loc = t.xloc;
    if k == TK_IDENT {
        adv();
        return ident_expr(t.val, loc);
    }
    if k == TK_NUMBER { adv(); return number_literal(t); }
    if k == TK_CHAR { adv(); return char_literal(t); }
    if k == TK_STRING { return string_literal(); }
    if k == TK_L_PAREN {
        if tk_n(1) == TK_L_BRACE {
            // GNU statement expression
            adv();
            let body = parse_compound_stmt(true);
            expect(TK_R_PAREN, "')'");
            return mk_stmt_expr(body, loc);
        }
        adv();
        let e = parse_expr();
        expect(TK_R_PAREN, "')'");
        nodes[e].flags = nodes[e].flags | NF_PAREN;
        return e;
    }
    if k == kw(KW_GENERIC) { return parse_generic(); }
    if k == kw(KW_VA_ARG) {
        adv();
        expect(TK_L_PAREN, "'('");
        let ap = parse_assign();
        expect(TK_COMMA, "','");
        let ty = parse_type_name();
        expect(TK_R_PAREN, "')'");
        return node(N_VAARG, 0, unqual(ty), ap as i64, 0, 0, loc);
    }
    if k == kw(KW_OFFSETOF) { return parse_offsetof(); }
    if k == kw(KW_TYPES_COMPAT) {
        adv();
        expect(TK_L_PAREN, "'('");
        let a = parse_type_name();
        expect(TK_COMMA, "','");
        let b = parse_type_name();
        expect(TK_R_PAREN, "')'");
        return int_node(if compatible_unq(a, b) { 1 } else { 0 }, t_int, loc);
    }
    if k == kw(KW_CHOOSE_EXPR) {
        adv();
        expect(TK_L_PAREN, "'('");
        let c = parse_assign();
        expect(TK_COMMA, "','");
        let a = parse_assign();
        expect(TK_COMMA, "','");
        let b = parse_assign();
        expect(TK_R_PAREN, "')'");
        let ok, v = fold_int(rv(c));
        if !ok { err_at(loc, "'__builtin_choose_expr' requires a constant expression"); }
        return if v != 0 { a } else { b };
    }
    if k == kw(KW_CONVERTVECTOR) || k == kw(KW_BITCAST) {
        adv();
        expect(TK_L_PAREN, "'('");
        var e: u32 = 0;
        var ty: u32 = 0;
        if k == kw(KW_BITCAST) {
            ty = parse_type_name();
            expect(TK_COMMA, "','");
            e = parse_assign();
        } else {
            e = parse_assign();
            expect(TK_COMMA, "','");
            ty = parse_type_name();
        }
        expect(TK_R_PAREN, "')'");
        return node(N_BUILTIN, if k == kw(KW_BITCAST) { BI_BITCAST } else { BI_CONVERTVECTOR }, unqual(ty), rv(e) as i64, 0, 0, loc);
    }
    if k == kw(KW_FUNC) {
        adv();
        if cur_func < 0 {
            warn(loc, "predefined identifier is only valid inside function");
            return make_string_node("", loc);
        }
        if ident_text(tu_toks[pc - 1].val as i64) == "__PRETTY_FUNCTION__" {
            pf_out.clear();
            pretty_function(pf_out, cur_func);
            return make_string_node(pf_out, loc);
        }
        return make_string_node(sym_name(cur_func), loc);
    }
    tok_buf.clear();
    tok_buf.append("expected expression, got ");
    tok_desc(tok_buf, pc);
    err(tok_buf);
    if !at(TK_EOF) && !at(TK_SEMI) && !at(TK_R_BRACE) && !at(TK_R_PAREN) { adv(); }
    return error_node(loc);
}

fn ident_expr(id: u32, loc: u32) -> u32 {
    var s = lookup_ord(id);
    if s < 0 {
        s = builtin_or_implicit(id, loc, at(TK_L_PAREN));
        if s < 0 {
            err_at(loc, str("use of undeclared identifier '", ident_text(id as i64), "'"));
            return error_node(loc);
        }
    }
    let sy = syms[s];
    let k = sy.kind as i64;
    syms[s].flags = sy.flags | SF_USED;
    if k == SK_ENUMC {
        let n = int_node(sy.v, sy.ty, loc);
        if dbg_types { dt_note_enumc(n, s); }
        return n;
    }
    if k == SK_TYPEDEF {
        err_at(loc, str("unexpected type name '", ident_text(id as i64), "': expected expression"));
        return error_node(loc);
    }
    var ty = sy.ty;
    if k == SK_FUNC && sy.flags & SF_KRDEF != 0 && types[ty >> 4].flags & TF_NOPROTO == 0 {
        // a function defined without a prototype is referenced with the
        // type without prototype (clang, C99 DR 316)
        fn_scratch.clear();
        let ft = types[ty >> 4];
        ty = qt(mk_type(TY_FUNC, TF_NOPROTO, ft.base, 0, 0, 0) as i64, 0);
    }
    let n = node(N_DECLREF, 0, ty, s, 0, 0, loc);
    if k == SK_VAR { nodes[n].flags = NF_LVALUE; }
    return n;
}

recursive fn parse_generic() -> u32 {
    let loc = tloc();
    adv();
    expect(TK_L_PAREN, "'('");
    let ctl = parse_assign();
    let ct = unqual(nty(rv(ctl)));
    var chosen: u32 = 0;
    var def: u32 = 0;
    var found = false;
    while accept(TK_COMMA) {
        if at_kw(KW_DEFAULT) {
            adv();
            expect(TK_COLON, "':'");
            def = parse_assign();
            continue;
        }
        let ty = parse_type_name();
        expect(TK_COLON, "':'");
        let e = parse_assign();
        if !found && compatible(unqual(ty), ct) {
            chosen = e;
            found = true;
        }
    }
    expect(TK_R_PAREN, "')'");
    if found { return chosen; }
    if def != 0 { return def; }
    err_at(loc, str("controlling expression type ", tname(ct), " not compatible with any generic association type"));
    return error_node(loc);
}

recursive fn parse_offsetof() -> u32 {
    let loc = tloc();
    adv();
    expect(TK_L_PAREN, "'('");
    let ty = parse_type_name();
    expect(TK_COMMA, "','");
    var off: i64 = 0;
    var cur = ty;
    var first = true;
    var constant = true;
    loop {
        if first || accept(TK_PERIOD) {
            first = false;
            if !at(TK_IDENT) && tk() < TK_KW { err("expected identifier"); break; }
            let name = tval();
            adv();
            if !is_record(cur) || !is_complete(cur) {
                err_at(loc, str("offsetof requires struct, union, or class type, ", tname(cur), " invalid"));
                break;
            }
            let ok, fo, fty = field_offset_path(rec_of(cur), name);
            if !ok {
                err_at(loc, str("no member named '", ident_text(name as i64), "' in ", tname(cur)));
                break;
            }
            off += fo;
            cur = fty;
        } else if at(TK_L_SQUARE) {
            adv();
            let ie = parse_expr();
            expect(TK_R_SQUARE, "']'");
            if !is_array(cur) { err_at(loc, "subscript of non-array type in offsetof"); break; }
            let ok, v = fold_int(rv(ie));
            if !ok { constant = false; }
            let es = type_size(tbase(cur));
            off += v * es;
            cur = tbase(cur);
        } else {
            break;
        }
    }
    expect(TK_R_PAREN, "')'");
    let n = node_v(N_OFFSETOF, 0, t_ulong, 0, 0, 0, loc, if constant { off } else { -1 });
    if constant { nodes[n].flags = NF_ICE; }
    return n;
}

// The byte offset and type of member `name` of record r (looking into
// anonymous members). Bit-fields give their storage offset.
fn field_offset_path(r: i64, name: u32) -> bool, i64, u32 {
    let rec = records[r];
    for i in rec.first..rec.first + rec.count {
        let f = fields[i];
        if f.name == name && name != 0 { return true, f.offset, f.ty; }
    }
    for i in rec.first..rec.first + rec.count {
        let f = fields[i];
        if f.flags & FF_ANON != 0 {
            let ok, o, t = field_offset_path2(rec_of(f.ty), name);
            if ok { return true, f.offset + o, t; }
        }
    }
    return false, 0, 0;
}

fn field_offset_path2(r: i64, name: u32) -> bool, i64, u32 {
    let rec = records[r];
    for i in rec.first..rec.first + rec.count {
        let f = fields[i];
        if f.name == name && name != 0 { return true, f.offset, f.ty; }
    }
    for i in rec.first..rec.first + rec.count {
        let f = fields[i];
        if f.flags & FF_ANON != 0 {
            let ok, o, t = field_offset_path3(rec_of(f.ty), name);
            if ok { return true, f.offset + o, t; }
        }
    }
    return false, 0, 0;
}

fn field_offset_path3(r: i64, name: u32) -> bool, i64, u32 {
    let rec = records[r];
    for i in rec.first..rec.first + rec.count {
        let f = fields[i];
        if f.name == name && name != 0 { return true, f.offset, f.ty; }
    }
    return false, 0, 0;
}

// ---------------------------------------------------------------------------
// Building and checking expressions.

fn mk_stmt_expr(body: u32, loc: u32) -> u32 {
    // The value is the last expression statement of the compound.
    var ty = t_void;
    let c = nodes[body].c as i64;
    if c > 0 {
        let last = nlist[nodes[body].v + c - 1];
        if nodes[last].kind == N_EXPR {
            let e = rv(nodes[last].a);
            nodes[last].a = e;
            ty = nty(e);
        }
    }
    return node(N_STMTEXPR, 0, ty, body as i64, 0, 0, loc);
}

fn is_modifiable(n: u32, loc: u32, what: const u8[:]) -> bool {
    if !is_lvalue(n) {
        err_at(loc, "expression is not assignable");
        return false;
    }
    var t = nty(n);
    if is_array(t) {
        err_at(loc, str("array type ", tname(t), " is not assignable"));
        return false;
    }
    if nodes[n].kind == N_SWIZZLE {
        // the element type is unqualified (clang); the vector's counts
        let vt = nty(nodes[n].a);
        t = if nodes[n].op == 1 { tbase(vt) } else { vt };
    }
    if quals(t) & Q_CONST != 0 {
        err_at(loc, str("cannot assign to ", what, " with const-qualified type ", tname(t)));
        return false;
    }
    if is_record(t) && records[rec_of(t)].flags & RF_CONST_MEMBER != 0 {
        err_at(loc, str("cannot assign to ", what, " with const-qualified data member"));
        return false;
    }
    return true;
}

fn mk_assign(op: i64, l: u32, r: u32, loc: u32) -> u32 {
    if is_error(l) || is_error(r) { return error_node(loc); }
    let lt = nty(l);
    if !is_modifiable(l, loc, "variable") { return error_node(loc); }
    let to = unqual(lt);
    let b = rv(r);
    if op == 0 {
        let cb = assign_convert(b, lt, loc, 0);
        return node(N_ASSIGN, 0, to, l as i64, cb as i64, 0, loc);
    }
    // compound assignment: the computation type
    let la = rv_load_type(l);
    if (op == B_ADD || op == B_SUB) && is_pointer(to) {
        if !is_integer(nty(b)) {
            err_at(loc, str("invalid operands to binary expression (", tname(to), " and ", tname(nty(b)), ")"));
            return error_node(loc);
        }
        let ib = promote(b);
        return node(N_ASSIGN, if op == B_ADD { B_PTRADD } else { B_PTRSUB }, to, l as i64, ib as i64, to as i64, loc);
    }
    if (op == B_SHL || op == B_SHR) && is_vector(to) {
        var cb = b;
        if !is_vector(nty(b)) {
            let vt = qt(mk_type(TY_EXTVECTOR, 0, unqual(nty(b)), types[to >> 4].n, 0, 0) as i64, 0);
            cb = icast(b, CK_VECSPLAT, vt);
        }
        return node(N_ASSIGN, op, to, l as i64, cb as i64, to as i64, loc);
    }
    if op == B_SHL || op == B_SHR {
        if !is_integer(to) || !is_integer(nty(b)) {
            err_at(loc, str("invalid operands to binary expression (", tname(to), " and ", tname(nty(b)), ")"));
            return error_node(loc);
        }
        let comp = promoted_type(la);
        return node(N_ASSIGN, op, to, l as i64, promote(b) as i64, comp as i64, loc);
    }
    if is_vector(to) {
        let cb = if is_vector(nty(b)) { b } else { convert(b, to) };
        return node(N_ASSIGN, op, to, l as i64, cb as i64, to as i64, loc);
    }
    let int_only = op == B_REM || op == B_AND || op == B_OR || op == B_XOR;
    if !is_arith(to) || !is_arith(nty(b)) || (int_only && (!is_integer(to) || !is_integer(nty(b)))) {
        err_at(loc, str("invalid operands to binary expression (", tname(to), " and ", tname(nty(b)), ")"));
        return error_node(loc);
    }
    let comp = arith_common(la, b);
    return node(N_ASSIGN, op, to, l as i64, convert(b, comp) as i64, comp as i64, loc);
}

// A node standing for the loaded value of lvalue l (for type computations).
fn rv_load_type(l: u32) -> u32 {
    let n = node(N_ICAST, CK_LVAL2RVAL, unqual(nty(l)), l as i64, 0, 0, nodes[l].loc);
    return n;
}

// Conversion as if by assignment (C11 6.5.16.1). what: 0 assign, 1 init,
// 2 argument, 3 return.
// `to0` may be qualified: a null pointer constant is converted to the
// qualified type (clang), everything else to the unqualified one.
recursive fn assign_convert(n: u32, to0: u32, loc: u32, what: i64) -> u32 {
    if is_error(n) { return n; }
    if quals(to0) & Q_ATOMIC != 0 && !is_error(n) {
        // to an _Atomic type: convert to the value type, then NonAtomicToAtomic
        let c = assign_convert(n, to0 & ~(Q_ATOMIC as! u32), loc, what);
        if is_error(c) { return c; }
        return icast(c, CK_ATOMIC, unqual(to0) | (Q_ATOMIC as! u32));
    }
    let to = unqual(to0);
    let from = nty(n);
    let kt = kind_of(to);
    let kf = kind_of(from);
    if unqual(tcanon(from)) == unqual(tcanon(to)) { return n; }
    if is_arith(to) && is_arith(from) { return convert(n, to); }
    if kt == TY_BOOL && kf == TY_POINTER { return icast(n, CK_PTR2BOOL, to); }
    if kt == TY_POINTER {
        if is_null_const(n) { return icast(n, CK_NULL2PTR, to0 & ~(Q_ATOMIC as! u32)); }
        if kf == TY_POINTER {
            let tp = tbase(to);
            let fp = tbase(from);
            if (quals(fp) & ~quals(tp)) != 0 {
                warn(loc, str("passing/assigning ", tname(from), " to ", tname(to), " discards qualifiers"));
            }
            if !is_void(tp) && !is_void(fp) && !compatible_unq(tp, fp) {
                warn(loc, str("incompatible pointer types converting ", tname(from), " to ", tname(to)));
            }
            return icast(n, cast_kind(from, to), unqual(to));
        }
        if is_integer(from) {
            int_conversion(loc, str("incompatible integer to pointer conversion from ", tname(from), " to ", tname(to)));
            return icast(n, CK_INT2PTR, unqual(to));
        }
    }
    if is_integer(to) && kf == TY_POINTER {
        int_conversion(loc, str("incompatible pointer to integer conversion from ", tname(from), " to ", tname(to)));
        return icast(n, CK_PTR2INT, unqual(to));
    }
    if is_record(to) && compatible_unq(to, from) { return n; }
    if kt == TY_UNION && records[rec_of(to)].flags & RF_TRANSPARENT != 0 {
        // the first member the argument can be assigned to without a
        // diagnostic, converted to the member's declared type (clang's
        // CheckTransparentUnionArgumentConstraints)
        let r = records[rec_of(to)];
        for i in r.first..r.first + r.count {
            let ft = fields[i].ty & ~(Q_ATOMIC as! u32);
            var c: u32 = 0;
            if is_pointer(ft) && kf == TY_POINTER && is_void(tbase(from)) {
                c = icast(n, CK_BITCAST, ft);
            } else if is_pointer(ft) && is_null_const(n) {
                c = icast(n, CK_NULL2PTR, ft);
            } else if tu_member_ok(ft, from) {
                c = assign_convert(n, ft, loc, what);
                if c == n {
                    if ft != unqual(ft) { c = icast(n, CK_NOOP, ft); }
                } else if nodes[c].kind == N_ICAST && nodes[c].a == n {
                    nodes[c].ty = ft;
                }
            }
            if c != 0 { return icast(c, CK_TOUNION, unqual(to)); }
        }
    }
    if (kt == TY_VECTOR || kt == TY_EXTVECTOR) && (kf == TY_VECTOR || kf == TY_EXTVECTOR) && type_size(to) == type_size(from) {
        return icast(n, CK_BITCAST, unqual(to));
    }
    if kt == TY_EXTVECTOR && is_arith(from) {
        return icast(convert(n, tbase(to)), CK_VECSPLAT, unqual(to));
    }
    let verb = match what { 0 => "assigning to ", 1 => "initializing ", 2 => "passing ", _ => "returning " };
    if what == 0 || what == 1 {
        err_at(loc, str(verb, tname(to), " from incompatible type ", tname(from)));
    } else {
        err_at(loc, str(verb, tname(from), " to parameter/result of incompatible type ", tname(to)));
    }
    return error_node(loc);
}

// Can a value of type `from` be assigned to type ft without a diagnostic?
fn tu_member_ok(ft: u32, from: u32) -> bool {
    if is_arith(ft) && is_arith(from) { return true; }
    if is_pointer(ft) && is_pointer(from) {
        let tp = tbase(ft);
        let fp = tbase(from);
        if (quals(fp) & ~quals(tp)) != 0 { return false; }
        return compatible_unq(tp, fp) || is_void(tp) || is_void(fp);
    }
    return compatible_unq(ft, from);
}

fn mk_cond(c0: u32, a0: u32, b0: u32, loc: u32) -> u32 {
    if is_error(c0) || is_error(b0) || (a0 != 0 && is_error(a0)) { return error_node(loc); }
    // C: the condition gets the usual unary conversions (clang)
    let c = promote(rv(c0));
    if !is_scalar(nty(c)) && !is_vector(nty(c)) {
        err_at(loc, str("used type ", tname(nty(c)), " where arithmetic or pointer type is required"));
        return error_node(loc);
    }
    let a = if a0 == 0 { c } else { rv(a0) };
    let b = rv(b0);
    let ta = nty(a);
    let tb = nty(b);
    var rt = t_void;
    var ca = a;
    var cb = b;
    if is_arith(ta) && is_arith(tb) {
        rt = arith_common(a, b);
        ca = convert(a, rt);
        cb = convert(b, rt);
    } else if is_void(ta) || is_void(tb) {
        // the other arm is converted to void (clang ToVoid)
        rt = t_void;
        if !is_void(ta) { ca = icast(a, CK_TOVOID, t_void); }
        if !is_void(tb) { cb = icast(b, CK_TOVOID, t_void); }
    } else if is_record(ta) && compatible_unq(ta, tb) {
        rt = unqual(ta);
    } else if is_pointer(ta) && is_pointer(tb) {
        let pa = tbase(ta);
        let pb = tbase(tb);
        let q = quals(pa) | quals(pb);
        if is_void(pa) || is_void(pb) {
            if is_null_const(a) && !is_null_const(b) { rt = tb; }
            else if is_null_const(b) && !is_null_const(a) { rt = ta; }
            else { rt = mk_ptr(with_quals(t_void, q)); }
        } else if compatible_unq(pa, pb) {
            rt = mk_ptr(with_quals(unqual(composite(pa, pb)), q));
        } else {
            warn(loc, str("pointer type mismatch (", tname(ta), " and ", tname(tb), ")"));
            rt = mk_ptr(with_quals(t_void, q));
        }
        ca = cond_ptr_arm(a, rt);
        cb = cond_ptr_arm(b, rt);
    } else if is_pointer(ta) && is_integer(tb) {
        if !is_null_const(b) { warn(loc, "pointer/integer type mismatch in conditional expression"); }
        rt = ta;
        cb = convert(b, rt);
    } else if is_integer(ta) && is_pointer(tb) {
        if !is_null_const(a) { warn(loc, "pointer/integer type mismatch in conditional expression"); }
        rt = tb;
        ca = convert(a, rt);
    } else if is_vector(ta) && compatible_unq(ta, tb) {
        rt = unqual(ta);
    } else {
        err_at(loc, str("incompatible operand types (", tname(ta), " and ", tname(tb), ")"));
        return error_node(loc);
    }
    if a0 == 0 {
        // GNU a ?: b: the condition is evaluated once
        return node(N_COND, 0, rt, c as i64, 0, cb as i64, loc);
    }
    return node(N_COND, 0, rt, c as i64, ca as i64, cb as i64, loc);
}

fn cond_ptr_arm(n: u32, rt: u32) -> u32 {
    if unqual(nty(n)) == unqual(rt) { return n; }
    if is_null_const(n) { return icast(n, CK_NULL2PTR, unqual(rt)); }
    return icast(n, CK_BITCAST, unqual(rt));
}

fn ptr_elem_ok(pt: u32, loc: u32) -> bool {
    let e = tbase(pt);
    if is_void(e) || is_func(e) { return true; }     // GNU: size 1
    if !is_complete(e) {
        err_at(loc, str("arithmetic on a pointer to an incomplete type ", tname(e)));
        return false;
    }
    return true;
}

fn bad_operands(l: u32, r: u32, loc: u32) -> u32 {
    err_at(loc, str("invalid operands to binary expression (", tname(nty(l)), " and ", tname(nty(r)), ")"));
    return error_node(loc);
}

fn mk_binary(op: i64, l: u32, r: u32, loc: u32) -> u32 {
    if is_error(l) || is_error(r) { return error_node(loc); }
    let a = rv(l);
    let b = rv(r);
    let ta = nty(a);
    let tb = nty(b);
    if op == B_LAND || op == B_LOR {
        if !is_scalar(ta) || !is_scalar(tb) {
            if !(is_vector(ta) || is_vector(tb)) { return bad_operands(a, b, loc); }
        }
        // C: the operands get the usual unary conversions (promotions)
        let pa = if is_integer(ta) { promote(a) } else { a };
        let pb = if is_integer(tb) { promote(b) } else { b };
        return node(N_BINARY, op, t_int, pa as i64, pb as i64, 0, loc);
    }
    if (is_vector(ta) || is_vector(tb)) && (op == B_SHL || op == B_SHR) {
        // clang's checkVectorShift: a scalar operand is splatted to an
        // ext_vector_type of its own type (the left one converted to the
        // element type first); a scalar left operand makes the result an
        // ext_vector_type
        if !is_vector(ta) {
            let et = unqual(tbase(tb));
            let vt = qt(mk_type(TY_EXTVECTOR, 0, et, types[tb >> 4].n, 0, 0) as i64, 0);
            let sa = icast(convert(a, et), CK_VECSPLAT, vt);
            return node(N_BINARY, op, vt, sa as i64, b as i64, 0, loc);
        }
        var cb = b;
        if !is_vector(tb) {
            let vt = qt(mk_type(TY_EXTVECTOR, 0, unqual(tb), types[ta >> 4].n, 0, 0) as i64, 0);
            cb = icast(b, CK_VECSPLAT, vt);
        }
        return node(N_BINARY, op, unqual(ta), a as i64, cb as i64, 0, loc);
    }
    if is_vector(ta) || is_vector(tb) {
        // element-wise; a scalar operand is splatted
        let vt = if is_vector(ta) { unqual(ta) } else { unqual(tb) };
        let ca = if is_vector(ta) { a } else { icast(convert(a, tbase(vt)), CK_VECSPLAT, vt) };
        let cb = if is_vector(tb) { b } else { icast(convert(b, tbase(vt)), CK_VECSPLAT, vt) };
        var rt = vt;
        if op >= B_LT && op <= B_NE {
            // comparison: a vector of signed integers of the element size
            // (clang's GetSignedVectorType: char, and long long for a
            // generic vector, long for an ext_vector_type)
            let es = type_size(tbase(vt));
            let ext = kind_of(vt) == TY_EXTVECTOR;
            let it = match es { 1 => t_char, 2 => t_short, 4 => t_int, 8 => if ext { t_long } else { t_llong }, _ => t_int128 };
            rt = qt(mk_type(kind_of(vt), 0, it, types[vt >> 4].n, 0, 0) as i64, 0);
        }
        return node(N_BINARY, op, rt, ca as i64, cb as i64, 0, loc);
    }
    if op == B_MUL || op == B_DIV {
        if !is_arith(ta) || !is_arith(tb) { return bad_operands(a, b, loc); }
        let t = arith_common(a, b);
        return node(N_BINARY, op, t, arith_operand(a, t) as i64, arith_operand(b, t) as i64, 0, loc);
    }
    if op == B_REM || op == B_AND || op == B_OR || op == B_XOR {
        if !is_integer(ta) || !is_integer(tb) { return bad_operands(a, b, loc); }
        let t = arith_common(a, b);
        return node(N_BINARY, op, t, arith_operand(a, t) as i64, arith_operand(b, t) as i64, 0, loc);
    }
    if op == B_ADD {
        if is_arith(ta) && is_arith(tb) {
            let t = arith_common(a, b);
            return node(N_BINARY, op, t, arith_operand(a, t) as i64, arith_operand(b, t) as i64, 0, loc);
        }
        if is_pointer(ta) && is_integer(tb) {
            if !ptr_elem_ok(ta, loc) { return error_node(loc); }
            return node(N_BINARY, B_PTRADD, unqual(ta), a as i64, promote(b) as i64, 0, loc);
        }
        if is_integer(ta) && is_pointer(tb) {
            if !ptr_elem_ok(tb, loc) { return error_node(loc); }
            return node(N_BINARY, B_PTRADD, unqual(tb), b as i64, promote(a) as i64, 0, loc);
        }
        return bad_operands(a, b, loc);
    }
    if op == B_SUB {
        if is_arith(ta) && is_arith(tb) {
            let t = arith_common(a, b);
            return node(N_BINARY, op, t, arith_operand(a, t) as i64, arith_operand(b, t) as i64, 0, loc);
        }
        if is_pointer(ta) && is_integer(tb) {
            if !ptr_elem_ok(ta, loc) { return error_node(loc); }
            return node(N_BINARY, B_PTRSUB, unqual(ta), a as i64, promote(b) as i64, 0, loc);
        }
        if is_pointer(ta) && is_pointer(tb) {
            if !compatible_unq(tbase(ta), tbase(tb)) {
                err_at(loc, str(tname(ta), " and ", tname(tb), " are not pointers to compatible types"));
                return error_node(loc);
            }
            if !ptr_elem_ok(ta, loc) { return error_node(loc); }
            return node(N_BINARY, B_PTRDIFF, t_long, a as i64, b as i64, 0, loc);
        }
        return bad_operands(a, b, loc);
    }
    if op == B_SHL || op == B_SHR {
        if !is_integer(ta) || !is_integer(tb) { return bad_operands(a, b, loc); }
        let pa = promote(a);
        return node(N_BINARY, op, nty(pa), pa as i64, promote(b) as i64, 0, loc);
    }
    // comparisons
    if is_arith(ta) && is_arith(tb) {
        let t = arith_common(a, b);
        return node(N_BINARY, op, t_int, arith_operand(a, t) as i64, arith_operand(b, t) as i64, 0, loc);
    }
    if is_pointer(ta) && is_pointer(tb) {
        let pa = tbase(ta);
        let pb = tbase(tb);
        var ca = a;
        var cb = b;
        if !compatible_unq(pa, pb) && !is_void(pa) && !is_void(pb) {
            warn(loc, str("comparison of distinct pointer types (", tname(ta), " and ", tname(tb), ")"));
        }
        if tcanon(pa) != tcanon(pb) {
            // clang: the right operand is converted to the left one's type
            // (BitCast), unless only the left one is a null constant
            if is_null_const(a) && !is_null_const(b) { ca = icast(a, CK_BITCAST, unqual(tb)); }
            else { cb = icast(b, CK_BITCAST, unqual(ta)); }
        }
        return node(N_BINARY, op, t_int, ca as i64, cb as i64, 0, loc);
    }
    if is_pointer(ta) && is_integer(tb) {
        if !is_null_const(b) { warn(loc, "comparison between pointer and integer"); }
        return node(N_BINARY, op, t_int, a as i64, convert(b, ta) as i64, 0, loc);
    }
    if is_integer(ta) && is_pointer(tb) {
        if !is_null_const(a) { warn(loc, "comparison between pointer and integer"); }
        return node(N_BINARY, op, t_int, convert(a, tb) as i64, b as i64, 0, loc);
    }
    return bad_operands(a, b, loc);
}

// An operand converted for an arithmetic operation of type t. With a
// complex result, a real operand is converted to the element type only
// (clang keeps mixed complex/real operations).
fn arith_operand(n: u32, t: u32) -> u32 {
    // clang promotes first (a bit-field or char is converted from its
    // promoted type; the casts merge)
    var x = n;
    if is_integer(nty(n)) { x = promote(n); }
    if is_complex(t) && !is_complex(nty(x)) && is_real_float(tbase(t)) { return convert(x, tbase(t)); }
    return convert(x, t);
}

fn mk_unary_arith(op: i64, e: u32, loc: u32) -> u32 {
    if is_error(e) { return e; }
    let a = rv(e);
    let t = nty(a);
    if op == U_NOT {
        if !is_scalar(t) && !is_vector(t) {
            err_at(loc, str("invalid argument type ", tname(t), " to unary expression"));
            return error_node(loc);
        }
        return node(N_UNARY, U_NOT, if is_vector(t) { unqual(t) } else { t_int }, a as i64, 0, 0, loc);
    }
    if is_vector(t) { return node(N_UNARY, op, unqual(t), a as i64, 0, 0, loc); }
    if op == U_BITNOT {
        if is_complex(t) { return node(N_UNARY, op, unqual(t), a as i64, 0, 0, loc); }   // GNU: conjugate
        if !is_integer(t) {
            err_at(loc, str("invalid argument type ", tname(t), " to unary expression"));
            return error_node(loc);
        }
        let p = promote(a);
        return node(N_UNARY, op, nty(p), p as i64, 0, 0, loc);
    }
    if !is_arith(t) {
        err_at(loc, str("invalid argument type ", tname(t), " to unary expression"));
        return error_node(loc);
    }
    let p = promote(a);
    return node(N_UNARY, op, nty(p), p as i64, 0, 0, loc);
}

fn mk_incdec(e: u32, op: i64, loc: u32) -> u32 {
    if is_error(e) { return e; }
    if !is_modifiable(e, loc, "variable") { return error_node(loc); }
    let t = unqual(nty(e));
    if !is_arith(t) && !is_pointer(t) && !is_vector(t) {
        err_at(loc, str("cannot increment value of type ", tname(t)));
        return error_node(loc);
    }
    if is_pointer(t) && !ptr_elem_ok(t, loc) { return error_node(loc); }
    return node(N_UNARY, op, t, e as i64, 0, 0, loc);
}

fn mk_addr(e: u32, loc: u32) -> u32 {
    if is_error(e) { return e; }
    let nd = nodes[e];
    if nd.flags & NF_BITFIELD != 0 {
        err_at(loc, "address of bit-field requested");
        return error_node(loc);
    }
    let t = nd.ty;
    if !is_lvalue(e) && !is_func(t) {
        err_at(loc, str("cannot take the address of an rvalue of type ", tname(t)));
        return error_node(loc);
    }
    if nd.kind == N_DECLREF {
        let s = nd.a as i64;
        syms[s].flags = syms[s].flags | SF_ADDR;
        if syms[s].sc == SC_REGISTER && scope_depth > 0 {
            err_at(loc, "address of register variable requested");
        }
    }
    return node(N_UNARY, U_ADDR, mk_ptr(t), e as i64, 0, 0, loc);
}

fn mk_deref(e: u32, loc: u32) -> u32 {
    if is_error(e) { return e; }
    let a = rv(e);
    let t = nty(a);
    if !is_pointer(t) {
        err_at(loc, str("indirection requires pointer operand (", tname(t), " invalid)"));
        return error_node(loc);
    }
    let pt = tbase(t);
    let n = node(N_UNARY, U_DEREF, pt, a as i64, 0, 0, loc);
    if !is_func(pt) && !is_void(pt) { nodes[n].flags = NF_LVALUE; }
    if is_void(pt) { nodes[n].flags = NF_LVALUE; }
    return n;
}

fn mk_real_imag(e: u32, real: bool, loc: u32) -> u32 {
    if is_error(e) { return e; }
    let t = nty(e);
    let op = if real { U_REAL } else { U_IMAG };
    if is_complex(t) {
        let n = node(N_UNARY, op, with_quals(tbase(t), quals(t)), e as i64, 0, 0, loc);
        if is_lvalue(e) { nodes[n].flags = NF_LVALUE; }
        return n;
    }
    if !is_arith(t) {
        err_at(loc, str("invalid type ", tname(t), " to ", if real { "__real" } else { "__imag" }, " operator"));
        return error_node(loc);
    }
    let a = rv(e);
    return node(N_UNARY, op, nty(a), a as i64, 0, 0, loc);
}

fn mk_index(base: u32, idx: u32, loc: u32) -> u32 {
    if is_error(base) || is_error(idx) { return error_node(loc); }
    // vector subscript
    if is_vector(nty(base)) {
        let i = rv(idx);
        let n = node(N_INDEX, 1, with_quals(tbase(nty(base)), quals(nty(base))), base as i64, i as i64, 0, loc);
        if is_lvalue(base) { nodes[n].flags = NF_LVALUE; }
        return n;
    }
    var a = rv(base);
    var b = rv(idx);
    if is_integer(nty(a)) && is_pointer(nty(b)) {
        let t = a;
        a = b;
        b = t;
    }
    if !is_pointer(nty(a)) || !is_integer(nty(b)) {
        err_at(loc, "subscripted value is not an array, pointer, or vector");
        return error_node(loc);
    }
    let et = tbase(nty(a));
    if !is_complete(et) && !is_void(et) {
        err_at(loc, str("subscript of pointer to incomplete type ", tname(et)));
        return error_node(loc);
    }
    let n = node(N_INDEX, 0, et, a as i64, b as i64, 0, loc);
    if !is_func(et) { nodes[n].flags = NF_LVALUE; }
    return n;
}

// Member access. Anonymous struct/union members are walked through.
fn mk_member(base: u32, name: u32, arrow: bool, loc: u32) -> u32 {
    if is_error(base) { return base; }
    var b = base;
    var rt: u32 = 0;
    var lval = false;
    if arrow {
        b = rv(base);
        let t = nty(b);
        if is_pointer(t) && kind_of(tbase(t)) == TY_EXTVECTOR {
            let r = mk_swizzle(b, tbase(t), name, loc);
            if !is_error(r) {
                nodes[r].op = 1;
                nodes[r].flags = NF_LVALUE;
            }
            return r;
        }
        if !is_pointer(t) || !is_record(tbase(t)) {
            err_at(loc, str("member reference type ", tname(t), " is not a pointer to a structure or union"));
            return error_node(loc);
        }
        rt = tbase(t);
        lval = true;
    } else {
        rt = nty(b);
        if kind_of(rt) == TY_EXTVECTOR { return mk_swizzle(b, rt, name, loc); }
        if !is_record(rt) {
            err_at(loc, str("member reference base type ", tname(rt), " is not a structure or union"));
            return error_node(loc);
        }
        lval = is_lvalue(b);
    }
    if !is_complete(rt) {
        err_at(loc, str("incomplete definition of type ", tname(rt)));
        return error_node(loc);
    }
    return member_walk(b, rec_of(rt), quals(rt), name, arrow, lval, loc, 0);
}

// An ext_vector_type element access (clang's ExtVectorElementExpr): v.x,
// v.xyzw / v.rgba, v.s0123 (hex digits), v.hi / v.lo / v.even / v.odd.
// One element has the element type; several make an ext vector of them.
// It is an lvalue when the vector is one and no element repeats.
fn mk_swizzle(b: u32, vt: u32, name: u32, loc: u32) -> u32 {
    let s = ident_text(name as i64);
    let n = types[vt >> 4].n;
    var idx: i64 = 0;
    var cnt: i64 = 0;
    var bad = false;
    if s == "hi" || s == "lo" || s == "even" || s == "odd" {
        let half = (n + 1) / 2;
        for i in half {
            let e = if s == "lo" { i } else if s == "hi" { half + i } else if s == "even" { 2 * i } else { 2 * i + 1 };
            idx = idx | (e << (4 * cnt));
            cnt++;
        }
    } else if s.len > 1 && (s[0] == 's' || s[0] == 'S') {
        for c in s[1..] {
            var e: i64 = -1;
            if c >= '0' && c <= '9' { e = (c - '0') as i64; }
            else if c >= 'a' && c <= 'f' { e = (c - 'a') as i64 + 10; }
            else if c >= 'A' && c <= 'F' { e = (c - 'A') as i64 + 10; }
            if e < 0 || e >= n || cnt >= 16 { bad = true; break; }
            idx = idx | (e << (4 * cnt));
            cnt++;
        }
    } else {
        for c in s {
            let e: i64 = match c { 'x', 'r' => 0, 'y', 'g' => 1, 'z', 'b' => 2, 'w', 'a' => 3, _ => -1 };
            if e < 0 || e >= n || cnt >= 16 { bad = true; break; }
            idx = idx | (e << (4 * cnt));
            cnt++;
        }
    }
    if bad || cnt == 0 {
        err_at(loc, str("vector component access exceeds type ", tname(vt)));
        return error_node(loc);
    }
    var dup = false;
    for i in cnt {
        for j in i + 1..cnt {
            if (idx >> (4 * i)) & 15 == (idx >> (4 * j)) & 15 { dup = true; }
        }
    }
    // the result type is unqualified, as in clang (is_modifiable looks at
    // the vector's qualifiers)
    var rt = unqual(tbase(vt));
    if cnt > 1 { rt = qt(mk_type(TY_EXTVECTOR, 0, unqual(tbase(vt)), cnt, 0, 0) as i64, 0); }
    let r = node_v(N_SWIZZLE, 0, rt, b as i64, 0, cnt, loc, idx);
    if is_lvalue(b) && !dup { nodes[r].flags = NF_LVALUE; }
    return r;
}

recursive fn member_walk(b: u32, r: i64, q: i64, name: u32, arrow: bool, lval: bool, loc: u32, depth: i64) -> u32 {
    let rec = records[r];
    for i in rec.first..rec.first + rec.count {
        let f = fields[i];
        if f.name == name && name != 0 {
            let n = node(N_MEMBER, if arrow { 1 } else { 0 }, with_quals(f.ty, q), b as i64, i, 0, loc);
            var fl: u16 = 0;
            if lval { fl = NF_LVALUE; }
            if f.width >= 0 { fl = fl | NF_BITFIELD; }
            nodes[n].flags = fl;
            return n;
        }
    }
    if depth < 8 {
        for i in rec.first..rec.first + rec.count {
            let f = fields[i];
            if f.flags & FF_ANON != 0 && has_member(rec_of(f.ty), name, 0) {
                let n = node(N_MEMBER, if arrow { 1 } else { 0 }, with_quals(f.ty, q), b as i64, i, 0, loc);
                if lval { nodes[n].flags = NF_LVALUE; }
                return member_walk(n, rec_of(f.ty), q | quals(f.ty), name, false, lval, loc, depth + 1);
            }
        }
    }
    err_at(loc, str("no member named '", ident_text(name as i64), "' in ", tname(records[r].ty << 4)));
    return error_node(loc);
}

fn has_member(r: i64, name: u32, depth: i64) -> bool {
    let rec = records[r];
    for i in rec.first..rec.first + rec.count {
        let f = fields[i];
        if f.name == name { return true; }
        if f.flags & FF_ANON != 0 && depth < 8 && has_member2(rec_of(f.ty), name) { return true; }
    }
    return false;
}

fn has_member2(r: i64, name: u32) -> bool {
    let rec = records[r];
    for i in rec.first..rec.first + rec.count {
        let f = fields[i];
        if f.name == name { return true; }
        if f.flags & FF_ANON != 0 && has_member3(rec_of(f.ty), name) { return true; }
    }
    return false;
}

fn has_member3(r: i64, name: u32) -> bool {
    let rec = records[r];
    for i in rec.first..rec.first + rec.count {
        if fields[i].name == name { return true; }
    }
    return false;
}

fn mk_sizeof_type(ty: u32, is_align: bool, loc: u32) -> u32 {
    var v: i64 = 0;
    if is_align {
        v = type_align(ty);
    } else if kind_of(ty) == TY_VLA {
        v = -1;
    } else if is_void(ty) || is_func(ty) {
        v = 1;     // GNU
    } else if !is_complete(ty) {
        err_at(loc, str("invalid application of '", if is_align { "alignof" } else { "sizeof" }, "' to an incomplete type ", tname(ty)));
        return error_node(loc);
    } else {
        v = type_size(ty);
    }
    let n = node_v(N_SIZEOF, if is_align { 1 } else { 0 }, t_ulong, 0, ty as i64, 0, loc, v);
    if v >= 0 { nodes[n].flags = NF_ICE; }
    return n;
}

fn mk_sizeof_expr(e: u32, is_align: bool, loc: u32) -> u32 {
    if is_error(e) { return e; }
    if nodes[e].flags & NF_BITFIELD != 0 {
        err_at(loc, "invalid application of 'sizeof' to bit-field");
        return error_node(loc);
    }
    let ty = nty(e);
    var v: i64 = 0;
    if is_align {
        v = type_align(ty);
        if nodes[e].kind == N_DECLREF {
            let s = nodes[e].a as i64;
            if syms[s].attr != 0 && sym_attrs[syms[s].attr].align as i64 > v { v = sym_attrs[syms[s].attr].align as i64; }
        }
    } else if kind_of(ty) == TY_VLA {
        v = -1;
    } else if is_void(ty) || is_func(ty) {
        v = 1;
    } else if !is_complete(ty) {
        err_at(loc, str("invalid application of 'sizeof' to an incomplete type ", tname(ty)));
        return error_node(loc);
    } else {
        v = type_size(ty);
    }
    let n = node_v(N_SIZEOF, if is_align { 1 } else { 0 }, t_ulong, e as i64, ty as i64, 0, loc, v);
    if v >= 0 { nodes[n].flags = NF_ICE; }
    return n;
}

fn mk_cast(ty: u32, e: u32, loc: u32) -> u32 {
    if is_error(e) { return e; }
    let to = ty;
    if is_void(to) {
        // C: the operand of a cast to void is converted to an rvalue (clang)
        let a = if is_void(nty(e)) { e } else { rv(e) };
        return node(N_CAST, CK_TOVOID, unqual(to), a as i64, 0, 0, loc);
    }
    let a = rv(e);
    let from = nty(a);
    if kind_of(to) == TY_UNION && !compatible_unq(to, from) {
        let r = records[rec_of(to)];
        for i in r.first..r.first + r.count {
            if compatible_unq(fields[i].ty, from) {
                return node(N_CAST, CK_TOUNION, unqual(to), a as i64, 0, 0, loc);
            }
        }
        err_at(loc, str("cast to union type from type ", tname(from), " not present in union"));
        return error_node(loc);
    }
    if is_record(to) || is_record(from) {
        if compatible_unq(to, from) { return node(N_CAST, CK_NOOP, unqual(to), a as i64, 0, 0, loc); }
        err_at(loc, str("used type ", tname(if is_record(to) { to } else { from }), " where arithmetic or pointer type is required"));
        return error_node(loc);
    }
    if is_array(to) || is_func(to) {
        err_at(loc, str("cast to incomplete/array/function type ", tname(to)));
        return error_node(loc);
    }
    if (is_pointer(to) && is_real_float(from)) || (is_pointer(from) && is_real_float(to)) {
        err_at(loc, str("operand of type ", tname(from), " cannot be cast to a pointer type"));
        return error_node(loc);
    }
    if is_complex(from) && !is_complex(to) && kind_of(to) != TY_BOOL {
        // complex to another real type: to the element type first (clang)
        let et = unqual(tbase(from));
        if unqual(tcanon(et)) != unqual(tcanon(to)) {
            let inner = icast(a, CK_COMPLEX2REAL, et);
            return node(N_CAST, cast_kind(et, to), unqual(to), inner as i64, 0, 0, loc);
        }
    }
    if is_complex(to) && !is_complex(from) && is_arith(from) {
        // real to another complex type: to the element type first (clang)
        let et = unqual(tbase(to));
        if unqual(tcanon(from)) != unqual(tcanon(et)) {
            return node(N_CAST, CK_REAL2COMPLEX, unqual(to), convert(a, et) as i64, 0, 0, loc);
        }
    }
    var ck = cast_kind(from, to);
    // clang: only an integer null constant becomes NullToPointer in a cast
    if is_null_const(a) && is_pointer(to) && is_integer(from) { ck = CK_NULL2PTR; }
    // a vector cast is a BitCast even to the same type
    if is_vector(to) && is_vector(from) { ck = CK_BITCAST; }
    return node(N_CAST, ck, unqual(to), a as i64, 0, 0, loc);
}

// Default argument promotions (C11 6.5.2.2p6).
fn default_promote(n: u32) -> u32 {
    let t = nty(n);
    if kind_of(t) == TY_FLOAT { return icast(n, CK_FLOATCAST, t_double); }
    if is_integer(t) { return promote(n); }
    return n;
}

fn mk_call(callee0: u32, mark: i64, loc: u32) -> u32 {
    let nargs = nscratch.len - mark;
    if is_error(callee0) {
        nscratch.resize(mark);
        return error_node(loc);
    }
    // custom-checked builtins
    let cn = nodes[callee0];
    if cn.kind == N_DECLREF && syms[cn.a].kind == SK_BUILTIN {
        let r = builtin_call(cn.a as i64, mark, loc);
        if r != 0 { return r; }
    }
    let callee = rv(callee0);
    let ct = nty(callee);
    if !is_pointer(ct) || !is_func(tbase(ct)) {
        err_at(loc, str("called object type ", tname(ct), " is not a function or function pointer"));
        nscratch.resize(mark);
        return error_node(loc);
    }
    var ft = types[tbase(ct) >> 4];
    var check_count = true;
    if cn.kind == N_DECLREF && syms[cn.a].kind == SK_FUNC && syms[cn.a].flags & SF_KRDEF != 0 {
        // the parameter types of the definition convert the arguments
        // (clang); a count mismatch is only a warning
        ft = types[syms[cn.a].ty >> 4];
        check_count = false;
    }
    let proto = ft.flags & TF_NOPROTO == 0;
    let np = ft.n;
    if proto && check_count {
        if nargs < np {
            err_at(loc, str("too few arguments to function call, expected ", np, ", have ", nargs));
        } else if nargs > np && ft.flags & TF_VARIADIC == 0 {
            err_at(loc, str("too many arguments to function call, expected ", np, ", have ", nargs));
        }
    }
    for i in nargs {
        let a = nscratch[mark + i];
        if is_error(a) { continue; }
        var c = rv(a);
        if proto && i < np {
            c = assign_convert(c, unqual(tparams[ft.extra + i]), nodes[a].loc, 2);
        } else {
            c = default_promote(c);
        }
        nscratch[mark + i] = c;
    }
    let start = commit_list(mark);
    let rt = unqual(ft.base);
    let n = node_v(N_CALL, 0, rt, callee as i64, 0, nargs, loc, start);
    if is_record(rt) && !is_complete(rt) {
        err_at(loc, str("calling function with incomplete return type ", tname(rt)));
    }
    return n;
}

// (T){ initializer }
recursive fn parse_compound_literal(ty: u32, loc: u32) -> u32 {
    let s = new_sym(SK_VAR, 0, ty, loc);
    syms[s].flags = SF_COMPLIT;
    if scope_depth == 0 { syms[s].sc = SC_STATIC; syms[s].flags = syms[s].flags | SF_FILESCOPE; }
    let init = parse_initializer_for(s, ty, scope_depth == 0);
    let t = syms[s].ty;
    let n = node(N_COMPLIT, 0, t, init as i64, s, 0, loc);
    nodes[n].flags = NF_LVALUE;
    return n;
}
