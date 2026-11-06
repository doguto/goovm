// goosecc: the preprocessor core. Contexts (files and token lexers),
// macro expansion, argument collection and pre-expansion, pasting and
// stringizing. The structure follows clang's Preprocessor/TokenLexer so
// that `goosecc -E` produces the same tokens as `clang -E`, quirks included:
//  * a macro is disabled while its expansion context is on the stack; an
//    identifier naming a disabled macro is marked F_NOEXP for good;
//  * a context is popped (re-enabling its macro) only when a token is read
//    past its end, so `f(1)(2)` style rescans behave as in clang/gcc;
//  * arguments are pre-expanded lazily, in body order, while the macro is
//    still enabled.
// All state lives in global arrays: pp_lex and everything it calls form one
// recursive cycle, which may not own growable data (spec §7.8).

import .common;
import .lex;

struct Macro {
    name: u32,
    first: u32,      // body in mtoks
    count: u32,
    nparams: u16,
    flags: u8,       // M_*
    builtin: u8,     // B_* for builtin macros
    enabled: bool,
    loc: u32,
}
let M_FUNC = 1;
let M_VARIADIC = 2;
let M_BUILTIN = 4;
let M_GNUVA = 8;      // named variadic parameter: `args...`

var macros: Macro[>..] = [];
var mtoks: Tok[>..] = [];

let CTX_FILE = 0;
let CTX_MACRO = 1;
let CTX_STREAM = 2;

let BUF_MTOKS = 0;
let BUF_XBUF = 1;
let BUF_ARGS = 2;
let BUF_STREAM = 3;

let MI_START = 0;
let MI_GUARD = 1;     // inside the top-level #ifndef
let MI_AFTER = 2;     // after its #endif, nothing seen since
let MI_INVALID = 3;

struct Ctx {
    kind: u8,
    buf: u8,
    noexp: bool,     // a stream entered with macro expansion disabled
    stamp: bool,     // stamp xloc / F_MACRO on tokens as they are read
    pend: u8,        // F_BOL / F_LSPACE for the next token (AtStartOfLine/HasLeadingSpace)
    nextspace: bool, // NextTokGetsSpace at the end
    cur: u32,
    lim: u32,
    start: u32,      // first index (to tell the first token)
    macro: i32,
    xloc: u32,
    xbase: u32,      // xbuf.len to restore when popped
    sbase: u32,      // streams.len to restore when popped
    // CTX_FILE
    file: i32,
    pos: u32,
    end: u32,
    lflags: u8,
    sys: u8,
    cond_base: u32,
    spell: u32,      // the path as opened (names); its directory is used for "..." includes
    spell_len: u32,
    pspell: u32,     // presumed name (#line)
    pspell_len: u32,
    dir_idx: i32,    // search directory it was found in, -1 if not via the search path
    line_delta: i32,
    mi_state: u8,
    mi_macro: i32,
}

var ctxs: Ctx[>..<] = [];
var xbuf: Tok[>..<] = [];      // macro expansions with arguments
var argtoks: Tok[>..<] = [];   // collected macro arguments, each ended by TK_EOF
var argidx: u32[>..<] = [];    // start of each argument in argtoks
var pre: Tok[>..<] = [];       // pre-expanded arguments
var precache: i64[>..<] = [];  // per argument: start, end in pre (-1 = not yet)
var streams: Tok[>..<] = [];   // re-injected tokens

var cur_file_ctx: i64 = 0;     // index of the topmost file context
var pp_noexpand: i64 = 0;      // > 0: macro expansion disabled (LexUnexpandedToken)
var in_macro_args: i64 = 0;
var in_preexp: i64 = 0;        // pre-expanding an argument (_Pragma is deferred)
var va_elided: bool = false;   // the variadic argument was left out entirely
var rparen_xloc: u32 = 0;      // xloc of the ')' that ended the last argument list
var counter_value: i64 = 0;

// Options.
var mode_E: bool = false;
var opt_gnu: bool = true;      // GNU mode (vs. strict ISO)
var opt_c99: bool = true;
var opt_std_c11: bool = true;  // C11 or later
var opt_optimize: i64 = 0;     // -O level (1 = -O1.., 2 = -Os/-Oz marker handled separately)

// Well-known identifiers.
var id_defined: u32 = 0;
var id_va_args: u32 = 0;
var id_va_opt: u32 = 0;
var id_pragma_op: u32 = 0;

// ---------------------------------------------------------------------------
// Token buffers.

fn buf_get(b: u8, i: i64) -> Tok {
    if b == BUF_XBUF { return xbuf[i]; }
    if b == BUF_MTOKS { return mtoks[i]; }
    if b == BUF_ARGS { return argtoks[i]; }
    return streams[i];
}

fn push_tok_ctx(kind: u8, b: u8, first: i64, lim: i64, m: i64, xl: u32, pend: u8, stamp: bool, noexp: bool) {
    ctxs.push(Ctx {
        kind: kind, buf: b, noexp: noexp, stamp: stamp, pend: pend, nextspace: false,
        cur: first as! u32, lim: lim as! u32, start: first as! u32, macro: m as! i32, xloc: xl,
        xbase: xbuf.len as! u32, sbase: streams.len as! u32,
        file: -1, pos: 0, end: 0, lflags: 0, sys: 0, cond_base: 0, spell: 0, spell_len: 0,
        pspell: 0, pspell_len: 0, dir_idx: -1, line_delta: 0, mi_state: MI_INVALID, mi_macro: -1,
    });
}

// Enters a stream of tokens held in `streams[first..]` (the caller pushed
// them). Used for re-injected tokens.
fn enter_stream(first: i64, noexp: bool) {
    push_tok_ctx(CTX_STREAM, BUF_STREAM, first, streams.len, -1, 0, 0, false, noexp);
    ctxs[ctxs.len - 1].sbase = first as! u32;
}

// Pops the top token context. Its pending flags go to the new top.
fn pop_tok_ctx(fl: u8) {
    let c = ctxs[ctxs.len - 1];
    if c.buf == BUF_XBUF { xbuf.resize(c.xbase as i64); }
    if c.buf == BUF_STREAM { streams.resize(c.sbase as i64); }
    ctxs.pop();
    propagate_flags(fl);
}

// clang's PropagateLineStartLeadingSpaceInfo.
fn propagate_flags(fl: u8) {
    let ti = ctxs.len - 1;
    if ctxs[ti].kind == CTX_FILE {
        lx_flags = lx_flags | (fl & (F_BOL | F_LSPACE | F_EMPTYMAC));
    } else {
        ctxs[ti].pend = fl & (F_BOL | F_LSPACE | F_EMPTYMAC);
    }
}

// ---------------------------------------------------------------------------
// Spelling of a token (into out).

fn tok_spelling(out: u8[>..]&, t: Tok) {
    let k = t.kind as i64;
    if k == TK_IDENT || k == TK_PARAM {
        let d = idents[t.val];
        out.append(src[d.off..d.off + d.len]);
    } else if is_punct(k) {
        if t.flags & F_DIGRAPH != 0 {
            out.append(match k {
                TK_L_SQUARE => "<:", TK_R_SQUARE => ":>", TK_L_BRACE => "<%", TK_R_BRACE => "%>",
                TK_HASH => "%:", _ => "%:%:",
            });
        } else {
            out.append(PUNCT_SPELL[k - TK_L_SQUARE]);
        }
    } else if k == TK_HASHHASH_NP {
        out.append("##");
    } else if k == TK_EOF || k == TK_EOD {
    } else {
        out.append(src[t.spell..t.spell + t.val]);
    }
}

fn tok_text_len(t: Tok) -> i64 {
    let k = t.kind as i64;
    if k == TK_IDENT || k == TK_PARAM { return idents[t.val].len; }
    if is_punct(k) {
        if t.flags & F_DIGRAPH != 0 { return if k == TK_HASHHASH { 4 } else { 2 }; }
        return PUNCT_SPELL[k - TK_L_SQUARE].len;
    }
    if k == TK_HASHHASH_NP { return 2; }
    if k == TK_EOF || k == TK_EOD { return 0; }
    return t.val;
}

// Makes a token whose spelling is `s`, lexed as one token (for builtin
// macro results). The text goes to the src scratch area.
var mk_buf: u8[>..] = [];
fn make_token(kind: i64, s: const u8[:], like: Tok) -> Tok {
    let off = src_add(s);
    src.push(0);
    var t = Tok { kind: kind as! u8, flags: like.flags & (F_BOL | F_LSPACE), aux: 0, spell: off, val: s.len as! u32, xloc: like.xloc };
    if kind == TK_IDENT { t.val = ident_lookup(off, s.len, hash_bytes(s)); }
    return t;
}

// ---------------------------------------------------------------------------
// The main entry point: the next fully macro-expanded token.

recursive fn pp_lex() -> Tok {
    loop {
        let ci = ctxs.len - 1;
        var t: Tok;
        var noexp = false;
        if ctxs[ci].kind == CTX_FILE {
            t = lex_file_token();
            if t.kind == TK_HASH && t.flags & F_BOL != 0 && !lx_dir {
                handle_directive(t);
                continue;
            }
            if t.kind == TK_EOF {
                if end_of_file() { continue; }
                return t;
            }
            if !lx_dir {
                let ms = ctxs[ci].mi_state;
                if ms != MI_INVALID && ms != MI_GUARD { ctxs[ci].mi_state = MI_INVALID; }
            }
        } else {
            t = ctx_next(ci);
            if t.kind == TK_CTX_END {
                pop_tok_ctx(t.flags);
                continue;
            }
            noexp = ctxs[ci].noexp;
        }
        if t.kind == TK_IDENT && !noexp {
            let m = idents[t.val].macro;
            if m >= 0 && pp_noexpand == 0 {
                if t.flags & F_NOEXP == 0 && macros[m].enabled {
                    if macros[m].flags & M_FUNC == 0 || next_is_lparen() {
                        let r = enter_macro(t, m);
                        if r == 1 { continue; }
                        if r == 2 { return builtin_result; }
                    }
                } else {
                    t.flags = t.flags | F_NOEXP;
                }
            }
        }
        return t;
    }
}

// Lex without macro expansion (clang LexUnexpandedToken).
recursive fn pp_lex_unexpanded() -> Tok {
    pp_noexpand++;
    let t = pp_lex();
    pp_noexpand--;
    return t;
}

// TokenLexer::Lex for token contexts.
fn ctx_next(ci: i64) -> Tok {
    let c = ctxs[ci];
    if c.cur >= c.lim {
        if c.macro >= 0 { macros[c.macro].enabled = true; }
        var fl = c.pend;
        if c.nextspace { fl = fl | F_LSPACE; }
        if c.cur == c.start { fl = fl | F_EMPTYMAC; }
        return Tok { kind: TK_CTX_END, flags: fl, aux: 0, spell: 0, val: 0, xloc: 0 };
    }
    var t = buf_get(c.buf, c.cur as i64);
    var cur = c.cur + 1;
    if c.kind == CTX_MACRO && cur < c.lim && buf_get(c.buf, cur as i64).kind == TK_HASHHASH {
        // Paste: LHS ## RHS [## RHS ...]
        loop {
            let rhs = buf_get(c.buf, (cur + 1) as i64);
            let ok, res = paste_two(t, rhs, c.xloc);
            if !ok {
                // Invalid paste: return the LHS; the RHS comes next.
                cur = cur + 1;
                break;
            }
            t = res;
            cur = cur + 2;
            if !(cur < c.lim && buf_get(c.buf, cur as i64).kind == TK_HASHHASH) { break; }
        }
    }
    ctxs[ci].cur = cur;
    if c.stamp {
        t.xloc = c.xloc;
        t.flags = t.flags | F_MACRO;
    }
    if c.cur == c.start {
        t.flags = (t.flags & ~(F_BOL | F_LSPACE)) | (c.pend & (F_BOL | F_LSPACE));
    } else {
        t.flags = t.flags | (c.pend & (F_BOL | F_LSPACE));
    }
    ctxs[ci].pend = 0;
    return t;
}

// Pastes lhs and rhs. Returns false if they do not form one token.
fn paste_two(lhs: Tok, rhs: Tok, xl: u32) -> bool, Tok {
    mk_buf.clear();
    tok_spelling(mk_buf, lhs);
    let ll = mk_buf.len;
    tok_spelling(mk_buf, rhs);
    let n = mk_buf.len;
    let fl = lhs.flags & (F_BOL | F_LSPACE);
    if n == 0 {
        return true, lhs;
    }
    if (lhs.kind == TK_IDENT || ll == 0) && (rhs.kind == TK_IDENT || rhs.kind == TK_NUMBER && ll > 0) && cc[mk_buf[0]] & CC_IDSTART != 0 {
        // identifier ## identifier (or number): an identifier, unless a
        // prefix makes it a literal (handled by the general path).
        var allid = true;
        for ch in mk_buf { if cc[ch] & CC_IDCONT == 0 { allid = false; } }
        if allid {
            let off = src_add(mk_buf);
            src.push(0);
            let id = ident_lookup(off, n, hash_bytes(src[off..off + n]));
            return true, Tok { kind: TK_IDENT, flags: fl, aux: 0, spell: off, val: id, xloc: xl };
        }
    }
    mk_buf.push(0);
    let k, e, dg = scan_token(mk_buf, 0);
    if e != n || k == TK_COMMENT || (k == TK_OTHER && n > 1) {
        mk_buf.pop();
        error_at(xl as i64, str("pasting formed '", mk_buf, "', an invalid preprocessing token"));
        return false, lhs;
    }
    let off = src_add(mk_buf[..n]);
    src.push(0);
    var res = Tok { kind: k as! u8, flags: fl | dg, aux: 0, spell: off, val: n as! u32, xloc: xl };
    if k == TK_IDENT {
        res.val = ident_lookup(off, n, hash_bytes(src[off..off + n]));
    } else if is_punct(k) {
        res.val = 0;
        if k == TK_HASHHASH { res.kind = TK_HASHHASH_NP; }
    }
    return true, res;
}

// Is the next token '(' ? Looks through the end of token contexts (without
// popping them) but not past the end of a file.
fn next_is_lparen() -> bool {
    var i = ctxs.len - 1;
    while i >= 0 {
        let c = ctxs[i];
        if c.kind == CTX_FILE { return lex_peek_lparen() == 1; }
        if c.cur < c.lim { return buf_get(c.buf, c.cur as i64).kind == TK_L_PAREN; }
        i--;
    }
    return false;
}

// ---------------------------------------------------------------------------
// Macro expansion.

var builtin_result: Tok = Tok { kind: 0, flags: 0, aux: 0, spell: 0, val: 0, xloc: 0 };

// Returns 0 to return the name token unchanged, 1 when expanded (lex
// again), 2 to return builtin_result.
recursive fn enter_macro(name: Tok, m: i64) -> i64 {
    let mc = macros[m];
    if mc.flags & M_BUILTIN != 0 {
        return expand_builtin(name, mc.builtin as i64);
    }
    var xl = name.xloc;
    let a0 = argtoks.len;
    let i0 = argidx.len;
    if mc.flags & M_FUNC != 0 {
        in_macro_args++;
        let ok = read_macro_args(name, m);
        in_macro_args--;
        if !ok {
            // clang returns the macro name as a plain token
            argtoks.resize(a0);
            argidx.resize(i0);
            return 0;
        }
        xl = rparen_xloc;
    }
    let elided = va_elided;
    let nameflags = name.flags & (F_BOL | F_LSPACE);
    if mc.count == 0 {
        argtoks.resize(a0);
        argidx.resize(i0);
        propagate_flags(nameflags | F_EMPTYMAC);
        return 1;
    }
    if mc.flags & M_FUNC != 0 && mc.nparams > 0 {
        let xb = xbuf.len;
        let p0 = pre.len;
        let c0 = precache.len;
        let ns = expand_args(m, i0, xl, elided);
        pre.resize(p0);
        precache.resize(c0);
        argtoks.resize(a0);
        argidx.resize(i0);
        macros[m].enabled = false;
        push_tok_ctx(CTX_MACRO, BUF_XBUF, xb, xbuf.len, m, xl, nameflags, false, false);
        ctxs[ctxs.len - 1].xbase = xb as! u32;
        ctxs[ctxs.len - 1].nextspace = ns;
        return 1;
    }
    argtoks.resize(a0);
    argidx.resize(i0);
    macros[m].enabled = false;
    push_tok_ctx(CTX_MACRO, BUF_MTOKS, mc.first as i64, (mc.first + mc.count) as i64, m, xl, nameflags, true, false);
    return 1;
}

// ReadMacroCallArgumentList. The '(' is next. Appends the arguments to
// argtoks (each followed by TK_EOF) and their starts to argidx.
recursive fn read_macro_args(name: Tok, m: i64) -> bool {
    let mc = macros[m];
    var fixed_left = mc.nparams as i64;
    let variadic = mc.flags & M_VARIADIC != 0;
    let lp = pp_lex_unexpanded();     // the '('
    var t = lp;
    var nactual = 0;
    let a0 = argtoks.len;
    va_elided = false;
    while t.kind != TK_R_PAREN {
        let start = argtoks.len;
        var parens = 0;
        loop {
            t = pp_lex_unexpanded();
            if t.kind == TK_EOF || t.kind == TK_EOD {
                error_at(name.xloc as i64, str("unterminated function-like macro invocation of '", ident_text(name.val as i64), "'"));
                // Do not lose the EOF/EOD: re-inject it.
                let s0 = streams.len;
                streams.push(t);
                enter_stream(s0, true);
                return false;
            }
            if t.kind == TK_R_PAREN {
                if parens == 0 {
                    rparen_xloc = t.xloc;
                    break;
                }
                parens--;
            } else if t.kind == TK_L_PAREN {
                parens++;
            } else if t.kind == TK_COMMA && parens == 0 {
                if !variadic { break; }
                if fixed_left > 1 { break; }
            } else if t.kind == TK_IDENT {
                let mm = idents[t.val].macro;
                if mm >= 0 && !macros[mm].enabled { t.flags = t.flags | F_NOEXP; }
            }
            argtoks.push(t);
        }
        // foo(): no argument at all.
        if argtoks.len == a0 && t.kind == TK_R_PAREN && nactual == 0 { break; }
        argidx.push(start as! u32);
        argtoks.push(Tok { kind: TK_EOF, flags: 0, aux: 0, spell: t.spell, val: 0, xloc: t.xloc });
        nactual++;
        if fixed_left != 0 { fixed_left--; }
    }
    let minargs = mc.nparams as i64;
    if !variadic && nactual > minargs {
        error_at(name.xloc as i64, str("too many arguments provided to function-like macro invocation '", ident_text(name.val as i64), "'"));
        return false;
    }
    if nactual < minargs {
        if nactual == 0 && minargs == 1 {
            va_elided = variadic;
        } else if variadic && (nactual + 1 == minargs || (nactual == 0 && minargs == 2)) {
            va_elided = true;
        } else {
            error_at(name.xloc as i64, str("too few arguments provided to function-like macro invocation '", ident_text(name.val as i64), "'"));
            return false;
        }
        argidx.push(argtoks.len as! u32);
        argtoks.push(Tok { kind: TK_EOF, flags: 0, aux: 0, spell: t.spell, val: 0, xloc: t.xloc });
        if nactual == 0 && minargs == 2 {
            argidx.push(argtoks.len as! u32);
            argtoks.push(Tok { kind: TK_EOF, flags: 0, aux: 0, spell: t.spell, val: 0, xloc: t.xloc });
        }
    }
    return true;
}

// The pre-expanded tokens of argument k (cached in pre). Returns its range.
recursive fn preexpanded(i0: i64, k: i64) -> i64, i64 {
    let ci = (precache.len - 2 * (argidx.len - i0)) + 2 * k;
    if precache[ci] >= 0 { return precache[ci], precache[ci + 1]; }
    let s = argidx[i0 + k] as i64;
    var e = s;
    while argtoks[e].kind != TK_EOF { e++; }
    let start = pre.len;
    if !arg_needs_preexp(s, e) {
        for j in s..e { pre.push(argtoks[j]); }
    } else {
        // Enter the argument (with its EOF) as a token stream and lex to EOF.
        push_tok_ctx(CTX_STREAM, BUF_ARGS, s, e + 1, -1, 0, 0, false, false);
        let depth = ctxs.len;
        in_preexp++;
        loop {
            let t = pp_lex();
            if t.kind == TK_EOF { break; }
            pre.push(t);
        }
        in_preexp--;
        // The EOF came from our stream: it is now at its end.
        if ctxs.len == depth {
            ctxs.pop();
        }
    }
    precache[ci] = start;
    precache[ci + 1] = pre.len;
    return start, pre.len;
}

fn arg_needs_preexp(s: i64, e: i64) -> bool {
    for j in s..e {
        let t = argtoks[j];
        if t.kind == TK_IDENT && idents[t.val].macro >= 0 { return true; }
    }
    return false;
}

fn arg_range(i0: i64, k: i64) -> i64, i64 {
    let s = argidx[i0 + k] as i64;
    var e = s;
    while argtoks[e].kind != TK_EOF { e++; }
    return s, e;
}

fn last_kind() -> i64 {
    return xbuf[xbuf.len - 1].kind as i64;
}

// ExpandFunctionArguments: substitutes the arguments into the body of
// macro m, appending the result to xbuf. Returns NextTokGetsSpace.
recursive fn expand_args(m: i64, i0: i64, xl: u32, elided: bool) -> bool {
    let mc = macros[m];
    let b = mc.first as i64;
    let n = mc.count as i64;
    let first_res = xbuf.len;
    let nargs = argidx.len - i0;
    for k in nargs { precache.push(-1); precache.push(-1); }
    var next_space = false;
    let va_k = (mc.nparams as i64) - 1;
    // __VA_OPT__ state
    var vo_active = false;
    var vo_depth = 0;
    var vo_prior = 0;          // result size before the __VA_OPT__
    var vo_stringify = false;
    var vo_space = false;
    var vo_called: i64 = -1;   // invoked with variadic arguments? -1 unknown
    var i = 0;
    while i < n {
        let ct = mtoks[b + i];
        if i != 0 && mtoks[b + i - 1].kind != TK_HASHHASH && ct.flags & F_LSPACE != 0 { next_space = true; }

        if ct.kind == TK_IDENT && ct.val == id_va_opt && mc.flags & M_VARIADIC != 0 && !vo_active {
            vo_active = true;
            vo_depth = 0;
            vo_prior = xbuf.len;
            i += 2;      // __VA_OPT__ (
            continue;
        }
        if vo_active {
            if ct.kind == TK_L_PAREN { vo_depth++; }
            var closing = false;
            if ct.kind == TK_R_PAREN {
                if vo_depth == 0 { closing = true; } else { vo_depth--; }
            }
            if !closing {
                if vo_called < 0 {
                    let ps, pe = preexpanded(i0, va_k);
                    vo_called = if pe > ps { 1 } else { 0 };
                }
                if vo_called == 0 { i++; continue; }
            } else {
                if vo_stringify {
                    let st = stringify_range(BUF_XBUF, vo_prior, xbuf.len, xl);
                    xbuf.resize(vo_prior);
                    var st2 = st;
                    if vo_space { st2.flags = st2.flags | F_LSPACE; }
                    xbuf.push(st2);
                } else if xbuf.len == vo_prior {
                    if xbuf.len > first_res && last_kind() == TK_HASHHASH {
                        xbuf.pop();
                    } else if i + 1 < n && mtoks[b + i + 1].kind == TK_HASHHASH {
                        i++;
                    }
                }
                vo_active = false;
                vo_stringify = false;
                i++;
                continue;
            }
        }

        // # param, or # __VA_OPT__
        if ct.kind == TK_HASH && i + 1 < n && (mtoks[b + i + 1].kind == TK_PARAM ||
                (mtoks[b + i + 1].kind == TK_IDENT && mtoks[b + i + 1].val == id_va_opt)) && mc.flags & M_FUNC != 0 {
            let nt = mtoks[b + i + 1];
            if nt.kind == TK_IDENT {
                vo_stringify = true;
                vo_space = next_space;
                next_space = false;
                i++;
                continue;
            }
            let s, e = arg_range(i0, nt.aux as i64);
            var st = stringify_range(BUF_ARGS, s, e, xl);
            st.flags = F_MACRO;
            if next_space { st.flags = st.flags | F_LSPACE; }
            xbuf.push(st);
            i += 2;
            next_space = false;
            continue;
        }

        let nonempty_paste_before = xbuf.len > first_res && last_kind() == TK_HASHHASH;
        let paste_before = i != 0 && mtoks[b + i - 1].kind == TK_HASHHASH;
        let paste_after = i + 1 < n && mtoks[b + i + 1].kind == TK_HASHHASH;

        if ct.kind != TK_PARAM {
            var t = ct;
            t.xloc = xl;
            t.flags = t.flags | F_MACRO;
            if next_space {
                t.flags = t.flags | F_LSPACE;
                next_space = false;
            } else if paste_before && !nonempty_paste_before {
                t.flags = t.flags & ~F_LSPACE;
            }
            xbuf.push(t);
            i++;
            continue;
        }

        let k = ct.aux as i64;
        if !paste_before && !paste_after {
            let ps, pe = preexpanded(i0, k);
            if pe > ps {
                let fr = xbuf.len;
                for j in ps..pe {
                    var t = pre[j];
                    if t.kind == TK_HASHHASH { t.kind = TK_HASHHASH_NP; }
                    xbuf.push(t);
                }
                var f0 = xbuf[fr];
                f0.flags = f0.flags & ~(F_LSPACE | F_BOL);
                if next_space { f0.flags = f0.flags | F_LSPACE; }
                xbuf[fr] = f0;
                next_space = false;
            }
            i++;
            continue;
        }

        // LHS or RHS of ##: the unexpanded argument.
        let s, e = arg_range(i0, k);
        if e > s {
            var pseudo = false;
            if nonempty_paste_before && xbuf.len - first_res >= 2 && xbuf[xbuf.len - 2].kind == TK_COMMA &&
                    k == va_k && mc.flags & M_VARIADIC != 0 {
                // GNU ", ## __VA_ARGS__" with a non-empty __VA_ARGS__: drop the ##.
                pseudo = true;
                xbuf.pop();
            }
            let fr = xbuf.len;
            for j in s..e {
                var t = argtoks[j];
                if t.kind == TK_HASHHASH { t.kind = TK_HASHHASH_NP; }
                xbuf.push(t);
            }
            if !pseudo {
                var f0 = xbuf[fr];
                f0.flags = f0.flags & ~(F_LSPACE | F_BOL);
                if next_space { f0.flags = f0.flags | F_LSPACE; }
                xbuf[fr] = f0;
            }
            next_space = false;
            i++;
            continue;
        }
        // An empty argument next to ##: placemarker rules.
        if paste_after {
            i += 2;
            continue;
        }
        // RHS of a paste (paste_before): remove the ## already copied.
        if nonempty_paste_before {
            if !vo_active || xbuf.len > vo_prior {
                xbuf.pop();
            }
        }
        // GNU comma elision: ", ## __VA_ARGS__" with __VA_ARGS__ left out
        // (clang: only when the argument was elided, not merely empty).
        if k == va_k && mc.flags & M_VARIADIC != 0 && elided && xbuf.len > first_res && last_kind() == TK_COMMA {
            if !(opt_c99 && !opt_gnu && (mc.nparams as i64) < 2) {
                xbuf.pop();
                if xbuf.len > first_res && last_kind() == TK_HASHHASH { xbuf.pop(); }
                next_space = false;
            }
        }
        i++;
    }
    return next_space;
}

// Stringizes the tokens b..e of buffer `bf` (# operator).
fn stringify_range(bf: u8, s: i64, e: i64, xl: u32) -> Tok {
    mk_buf.clear();
    mk_buf.push('"');
    var first = true;
    for j in s..e {
        let t = buf_get(bf, j);
        if t.kind == TK_EOF { break; }
        if !first && t.flags & (F_LSPACE | F_BOL) != 0 { mk_buf.push(' '); }
        first = false;
        if t.kind == TK_STRING || t.kind == TK_CHAR {
            let sp = src[t.spell..t.spell + t.val];
            for ch in sp {
                if ch == '\\' || ch == '"' { mk_buf.push('\\'); }
                mk_buf.push(ch);
            }
        } else {
            tok_spelling(mk_buf, t);
        }
    }
    // An unescaped trailing backslash is invalid: drop it.
    if mk_buf.len >= 2 && mk_buf[mk_buf.len - 1] == '\\' {
        var j = mk_buf.len - 2;
        while mk_buf[j] == '\\' { j--; }
        if (mk_buf.len - 1 - j) % 2 == 1 {
            error_at(xl as i64, "invalid string literal, ignoring final '\\'");
            mk_buf.pop();
        }
    }
    mk_buf.push('"');
    let off = src_add(mk_buf);
    src.push(0);
    return Tok { kind: TK_STRING, flags: 0, aux: 0, spell: off, val: mk_buf.len as! u32, xloc: xl };
}
