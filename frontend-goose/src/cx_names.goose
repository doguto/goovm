// goosecc D1: tokens, names and template arguments for the C++ parser.
//
// The cursor is C's (pc over tu_toks), read through cx's tk/at/adv so that
// a `>>` closing two template argument lists can be consumed one `>` at a
// time (gt_pos / gt_kind: the token at gt_pos now reads as gt_kind).
//
// A name is parsed into a QN: the nested-name-specifier's scope (or a
// dependent type when the qualifier is dependent or not instantiated), the
// final unqualified-id (an identifier, operator-function-id,
// conversion-function-id, destructor name), its template arguments, and
// the result of looking it up.

namespace cx;

import std;
import dictionary;
import .common;
import .types;
import .ast;
import .sema;
import .pp;
import .expr;
import .cx_core;

// ---------------------------------------------------------------------------
// The cursor.

var gt_pos: i64 = -1;
var gt_kind: i64 = 0;

fn tk() -> i64 {
    if pc == gt_pos { return gt_kind; }
    return tu_toks[pc].kind as i64;
}
fn tk_n(k: i64) -> i64 {
    if k == 0 { return tk(); }
    let i = pc + k;
    if i < tu_toks.len { return tu_toks[i].kind as i64; }
    return TK_EOF;
}
fn tk_at(i: i64) -> i64 {
    if i == gt_pos { return gt_kind; }
    if i < tu_toks.len { return tu_toks[i].kind as i64; }
    return TK_EOF;
}
fn at(k: i64) -> bool { tk() == k }
fn at_kw(k: i64) -> bool { tk() == TK_KW + k }
fn adv() {
    if pc == gt_pos { gt_pos = -1; }
    if pc < tu_toks.len - 1 { pc++; }
}
fn accept(k: i64) -> bool {
    if at(k) { adv(); return true; }
    return false;
}
fn accept_kw(k: i64) -> bool { accept(TK_KW + k) }

fn expect(k: i64, what: const u8[:]) -> bool {
    if at(k) { adv(); return true; }
    if k == TK_GREATER && take_gt() { return true; }
    perr_expected(what);
    return false;
}

fn perr_expected(what: const u8[:]) {
    tok_buf.clear();
    tok_buf.append("expected ");
    tok_buf.append(what);
    tok_buf.append(", got ");
    tok_desc(tok_buf, pc);
    error_at(tloc() as i64, tok_buf);
}

// Consumes one '>' of the token at pc (> >> >= >>=).
fn take_gt() -> bool {
    let k = tk();
    if k == TK_GREATER { adv(); return true; }
    if k == TK_GREATERGREATER { gt_pos = pc; gt_kind = TK_GREATER; return true; }
    if k == TK_GREATEREQUAL { gt_pos = pc; gt_kind = TK_EQUAL; return true; }
    if k == TK_GREATERGREATEREQUAL { gt_pos = pc; gt_kind = TK_GREATEREQUAL; return true; }
    return false;
}
fn at_gt() -> bool {
    let k = tk();
    return k == TK_GREATER || k == TK_GREATERGREATER || k == TK_GREATEREQUAL || k == TK_GREATERGREATEREQUAL;
}

struct Save { p: i64, gp: i64, gk: i64, nerr: i64 }
fn save() -> Save { Save { p: pc, gp: gt_pos, gk: gt_kind, nerr: n_errors } }
fn restore(s: Save) { pc = s.p; gt_pos = s.gp; gt_kind = s.gk; }

// Skips a balanced group starting at the opening token at pc ( ( [ { ).
fn skip_group() {
    var depth = 0;
    loop {
        let k = tk();
        if k == TK_EOF { return; }
        if k == TK_L_PAREN || k == TK_L_SQUARE || k == TK_L_BRACE { depth++; }
        if k == TK_R_PAREN || k == TK_R_SQUARE || k == TK_R_BRACE {
            depth--;
            if depth <= 0 { adv(); return; }
        }
        adv();
    }
}

// Skips to the next token of kind k at nesting depth 0 (not consuming it);
// stops at a closing bracket of an enclosing group or the end.
fn skip_to(k: i64) {
    loop {
        let t = tk();
        if t == k || t == TK_EOF { return; }
        if t == TK_L_PAREN || t == TK_L_SQUARE || t == TK_L_BRACE { skip_group(); continue; }
        if t == TK_R_PAREN || t == TK_R_SQUARE || t == TK_R_BRACE { return; }
        adv();
    }
}

fn ident_is(i: i64, s: const u8[:]) -> bool {
    let t = tu_toks[i];
    if t.kind as i64 != TK_IDENT { return false; }
    return ident_text(t.val as i64) == s;
}

var id_override: u32 = 0;
var id_final: u32 = 0;
var id_main: u32 = 0;
var id_std: u32 = 0;
var id_C: u32 = 0;

// ---------------------------------------------------------------------------
// Operators (operator-function-ids).

let OP_NEW = 1;
let OP_DELETE = 2;
let OP_NEW_ARR = 3;
let OP_DELETE_ARR = 4;
let OP_PLUS = 5;
let OP_MINUS = 6;
let OP_STAR = 7;
let OP_SLASH = 8;
let OP_PERCENT = 9;
let OP_CARET = 10;
let OP_AMP = 11;
let OP_PIPE = 12;
let OP_TILDE = 13;
let OP_EXCLAIM = 14;
let OP_EQUAL = 15;
let OP_LESS = 16;
let OP_GREATER = 17;
let OP_PLUSEQ = 18;
let OP_MINUSEQ = 19;
let OP_STAREQ = 20;
let OP_SLASHEQ = 21;
let OP_PERCENTEQ = 22;
let OP_CARETEQ = 23;
let OP_AMPEQ = 24;
let OP_PIPEEQ = 25;
let OP_LSHIFT = 26;
let OP_RSHIFT = 27;
let OP_RSHIFTEQ = 28;
let OP_LSHIFTEQ = 29;
let OP_EQEQ = 30;
let OP_NE = 31;
let OP_LE = 32;
let OP_GE = 33;
let OP_SPACESHIP = 34;
let OP_AMPAMP = 35;
let OP_PIPEPIPE = 36;
let OP_PLUSPLUS = 37;
let OP_MINUSMINUS = 38;
let OP_COMMA = 39;
let OP_ARROWSTAR = 40;
let OP_ARROW = 41;
let OP_CALL = 42;
let OP_SUBSCRIPT = 43;
let OP_COAWAIT = 44;

// The operator a token denotes after `operator` (OP_*), 0 none.
fn tok_op(k: i64) -> i64 {
    return match k {
        TK_PLUS => OP_PLUS, TK_MINUS => OP_MINUS, TK_STAR => OP_STAR, TK_SLASH => OP_SLASH, TK_PERCENT => OP_PERCENT,
        TK_CARET => OP_CARET, TK_AMP => OP_AMP, TK_PIPE => OP_PIPE, TK_TILDE => OP_TILDE, TK_EXCLAIM => OP_EXCLAIM,
        TK_EQUAL => OP_EQUAL, TK_LESS => OP_LESS, TK_GREATER => OP_GREATER, TK_PLUSEQUAL => OP_PLUSEQ,
        TK_MINUSEQUAL => OP_MINUSEQ, TK_STAREQUAL => OP_STAREQ, TK_SLASHEQUAL => OP_SLASHEQ,
        TK_PERCENTEQUAL => OP_PERCENTEQ, TK_CARETEQUAL => OP_CARETEQ, TK_AMPEQUAL => OP_AMPEQ,
        TK_PIPEEQUAL => OP_PIPEEQ, TK_LESSLESS => OP_LSHIFT, TK_GREATERGREATER => OP_RSHIFT,
        TK_GREATERGREATEREQUAL => OP_RSHIFTEQ, TK_LESSLESSEQUAL => OP_LSHIFTEQ, TK_EQUALEQUAL => OP_EQEQ,
        TK_EXCLAIMEQUAL => OP_NE, TK_LESSEQUAL => OP_LE, TK_GREATEREQUAL => OP_GE, TK_SPACESHIP => OP_SPACESHIP,
        TK_AMPAMP => OP_AMPAMP, TK_PIPEPIPE => OP_PIPEPIPE, TK_PLUSPLUS => OP_PLUSPLUS, TK_MINUSMINUS => OP_MINUSMINUS,
        TK_COMMA => OP_COMMA, TK_ARROWSTAR => OP_ARROWSTAR, TK_ARROW => OP_ARROW,
        _ => 0,
    };
}

// The identifier an operator function is filed under in scopes (a fixed
// spelling per operator, e.g. "operator+", interned at start-up).
var op_ids: u32[>..] = [];
let OP_NAMES = ["", "operator new", "operator delete", "operator new[]", "operator delete[]", "operator+", "operator-",
    "operator*", "operator/", "operator%", "operator^", "operator&", "operator|", "operator~", "operator!", "operator=",
    "operator<", "operator>", "operator+=", "operator-=", "operator*=", "operator/=", "operator%=", "operator^=",
    "operator&=", "operator|=", "operator<<", "operator>>", "operator>>=", "operator<<=", "operator==", "operator!=",
    "operator<=", "operator>=", "operator<=>", "operator&&", "operator||", "operator++", "operator--", "operator,",
    "operator->*", "operator->", "operator()", "operator[]", "operator co_await"];
var id_conv: u32 = 0;       // conversion functions are filed under "operator <conversion>"
var id_dtor: u32 = 0;       // destructors under "~"
var id_ctor: u32 = 0;       // constructors under "<init>"

fn names_init() {
    for n in OP_NAMES { op_ids.push(intern(n)); }
    id_conv = intern("operator <conversion>");
    id_dtor = intern("~");
    id_ctor = intern("<init>");
    id_override = intern("override");
    id_final = intern("final");
    id_main = intern("main");
    id_std = intern("std");
    id_C = intern("C");
}

// ---------------------------------------------------------------------------
// Qualified names.

let QK_NONE = 0;
let QK_IDENT = 1;
let QK_OP = 2;
let QK_CONV = 3;
let QK_DTOR = 4;
let QK_LITOP = 5;       // operator "" _x

struct QN {
    scope: i32 = -1,        // the qualifier's scope; -1 unqualified
    dep: u32 = 0,           // a dependent or opaque qualifier (type)
    qual: bool = false,     // a nested-name-specifier was given
    global: bool = false,   // ::name
    kind: u8 = 0,
    op: u8 = 0,
    name: u32 = 0,          // the identifier (QK_IDENT / QK_DTOR: the class name; QK_OP: op_ids[op])
    targs: i32 = -1,
    has_targs: bool = false,
    tkw: bool = false,      // `template` before the last component
    conv: u32 = 0,          // QK_CONV: the type; QK_DTOR: the class type if known
    sym: i32 = -1,          // the lookup result
    loc: u32 = 0,
    start: u32 = 0,         // its first token
}

// Is symbol s (resolved) usable before :: (a namespace, a type, a class template)?
fn nns_kind_ok(s: i64) -> bool {
    let k = syms[s].kind as i64;
    if k == SK_NAMESPACE || k == SK_NSALIAS || k == SK_TAG || k == SK_TYPEDEF { return true; }
    if k == SK_TEMPLATE {
        let t = cxs[s].tmpl;
        return t >= 0 && (tmpls[t].kind as i64 == TT_CLASS || tmpls[t].kind as i64 == TT_ALIAS || tmpls[t].kind as i64 == TT_PARAM);
    }
    return false;
}

// The first symbol of a lookup chain (from s0) that nns_kind_ok, or -1.
fn chain_nns(s0: i64) -> i64 {
    var s = s0;
    while s >= 0 {
        let r = resolve(s);
        if r >= 0 && visible(s) && nns_kind_ok(r) { return r; }
        s = cxs[s].nnext as i64;
    }
    return -1;
}

// The first type or template symbol of a lookup chain, or -1.
fn chain_type(s0: i64) -> i64 {
    var s = s0;
    while s >= 0 {
        let r = resolve(s);
        if r >= 0 && visible(s) {
            let k = syms[r].kind as i64;
            if k == SK_TAG || k == SK_TYPEDEF || k == SK_TEMPLATE { return r; }
        }
        s = cxs[s].nnext as i64;
    }
    return -1;
}

// Unqualified lookup for a name before :: (only namespaces, types and
// templates count: C++ [basic.lookup.qual]p1).
recursive fn lookup_nns_unqual(name: u32) -> i64 {
    let l = local_lookup(name);
    if l >= 0 {
        let r = resolve(l);
        if r >= 0 && nns_kind_ok(r) { return r; }
    }
    var sc = cur_scope;
    while sc >= 0 {
        let k = scopes[sc].kind as i64;
        var s: i64 = -1;
        if k == CS_CLASS {
            s = chain_nns(class_lookup(sc, name));
            if s < 0 && scopes[sc].tps >= 0 { s = chain_nns(scope_find(scopes[sc].tps as i64, name)); }
        }
        else if k == CS_NS { s = chain_nns(ns_lookup(sc, name, false)); }
        if s >= 0 { return s; }
        sc = scopes[sc].parent as i64;
    }
    return -1;
}

// The type a type or class-template symbol names (the injected class, a
// typedef's type), 0 if it is not a type.
fn sym_type(s0: i64) -> u32 {
    let s = resolve(s0);
    if s < 0 { return 0; }
    let k = syms[s].kind as i64;
    if k == SK_TAG || k == SK_TYPEDEF { return syms[s].ty; }
    return 0;
}

// Is the symbol (resolved) a template, and of which kind (TT_*, 0 none)?
fn tmpl_kind(s: i64) -> i64 {
    if s < 0 { return 0; }
    if syms[s].kind as i64 != SK_TEMPLATE { return 0; }
    let t = cxs[s].tmpl;
    if t < 0 { return 0; }
    return tmpls[t].kind as i64;
}

// Does a lookup chain contain a template (any kind)?
fn chain_has_template(s0: i64) -> bool {
    var s = s0;
    while s >= 0 {
        let r = resolve(s);
        if r >= 0 && syms[r].kind as i64 == SK_TEMPLATE { return true; }
        if r >= 0 && cxs[r].flags & CF_INJECTED != 0 && cxs[r].tmpl >= 0 { return true; }
        s = cxs[s].nnext as i64;
    }
    return false;
}

// Turns a qualifier type into the qualifier: a class or enum scope, or a
// dependent / opaque type.
fn qual_from_type(qn: QN&, t: u32) {
    let sc = type_scope(t);
    if sc >= 0 && !is_opaque(t) {
        qn.scope = sc as! i32;
        qn.dep = 0;
        return;
    }
    if sc >= 0 && is_record(t) {
        // a class template's pattern: its own members are known
        qn.scope = sc as! i32;
        qn.dep = 0;
        return;
    }
    qn.scope = -1;
    qn.dep = if t == 0 { t_unknown } else { t };
}

// Parses an optional '::' and nested-name-specifier into qn (scope / dep),
// leaving pc at the final unqualified-id. A component `X<args>` that turns
// out not to be followed by '::' is the final one: qn gets its name and
// arguments (has_targs) and the function returns with pc after the '>'.
// Returns false when nothing was consumed.
recursive fn parse_nns(qn: QN&) -> bool {
    let start = pc;
    qn.start = pc as! u32;
    qn.loc = tloc();
    if at(TK_COLONCOLON) {
        adv();
        qn.scope = 0;
        qn.global = true;
        qn.qual = true;
    } else if at_kw(KW_DECLTYPE) && decltype_then_cc() {
        let t = parse_decltype();
        adv();     // ::
        qual_from_type(qn, t);
        qn.qual = true;
    }
    loop {
        var tkw = false;
        if at_kw(KW_TEMPLATE) && qn.qual && tk_n(1) == TK_IDENT {
            tkw = true;
            adv();
        }
        if !at(TK_IDENT) { if tkw { pc--; } break; }
        let id = tu_toks[pc].val;
        let k1 = tk_n(1);
        if k1 == TK_COLONCOLON {
            // X ::
            qn.loc = tloc();
            adv();
            adv();
            qual_component(qn, id, -1, false);
            qn.qual = true;
            continue;
        }
        if k1 == TK_LESS {
            // X < args > (::)?
            var is_tmpl = tkw;
            var s: i64 = -1;
            if !tkw {
                if qn.dep != 0 { is_tmpl = false; }
                else if qn.scope >= 0 { s = qual_lookup(qn.scope as i64, id); is_tmpl = chain_has_template(s); }
                else { s = unqual_lookup(id); is_tmpl = chain_has_template(s); }
            }
            if !is_tmpl { break; }
            let save_loc = tloc();
            let sv = save();
            adv();
            let args = parse_targs();
            if at(TK_COLONCOLON) {
                adv();
                qn.loc = save_loc;
                qual_component(qn, id, args, true);
                qn.qual = true;
                continue;
            }
            // the final component: a template-id
            qn.kind = QK_IDENT;
            qn.name = id;
            qn.targs = args;
            qn.has_targs = true;
            qn.tkw = tkw;
            qn.loc = save_loc;
            let r = save();
            return true;
        }
        if tkw { pc--; }
        break;
    }
    return pc != start;
}

// Is the decltype(...) at pc followed by '::'?
fn decltype_then_cc() -> bool {
    if tk_n(1) != TK_L_PAREN { return false; }
    var j = pc + 1;
    var depth = 0;
    loop {
        let k = tu_toks[j].kind as i64;
        if k == TK_EOF { return false; }
        if k == TK_L_PAREN { depth++; }
        if k == TK_R_PAREN { depth--; if depth == 0 { break; } }
        j++;
    }
    return tu_toks[j + 1].kind as i64 == TK_COLONCOLON;
}

// Applies one nested-name-specifier component `id` (with template args
// when has_args) to qn.
recursive fn qual_component(qn: QN&, id: u32, args: i32, has_args: bool) {
    if qn.dep != 0 {
        qn.dep = mk_depname(qn.dep, id, if has_args { args } else { -1 });
        return;
    }
    var s: i64 = -1;
    if qn.scope >= 0 {
        s = chain_nns(qual_lookup(qn.scope as i64, id));
        if s < 0 && has_args { s = chain_nns_tmpl(qual_lookup(qn.scope as i64, id)); }
    } else {
        s = lookup_nns_unqual(id);
    }
    if s < 0 {
        if qn.scope >= 0 && (scopes[qn.scope].flags & SCF_PATTERN != 0 || has_dep_base(qn.scope as i64)) {
            // a member of the current instantiation's dependent bases
            qn.dep = mk_depname(scope_class_type(qn.scope as i64), id, if has_args { args } else { -1 });
            qn.scope = -1;
            return;
        }
        if !dependent_ctx() && diag_suppress == 0 {
            err_at(qn.loc, str("use of undeclared identifier '", ident_text(id as i64), "'"));
        }
        qn.dep = t_unknown;
        qn.scope = -1;
        return;
    }
    let k = syms[s].kind as i64;
    if k == SK_NAMESPACE || k == SK_NSALIAS {
        qn.scope = syms[s].v as! i32;
        return;
    }
    if k == SK_TEMPLATE {
        if !has_args {
            // a class template's name inside it is the injected class
            let t = tmpl_injected(s);
            qual_from_type(qn, t);
            return;
        }
        let t = specialization(s, args);
        qual_from_type(qn, t);
        return;
    }
    if has_args && cxs[s].flags & CF_INJECTED != 0 && cxs[s].tmpl >= 0 {
        // X<args>:: through the injected-class-name of X's specialization
        let t = specialization(tmpls[cxs[s].tmpl].sym as i64, args);
        qual_from_type(qn, t);
        return;
    }
    qual_from_type(qn, syms[s].ty);
}

fn chain_nns_tmpl(s0: i64) -> i64 {
    var s = s0;
    while s >= 0 {
        let r = resolve(s);
        if r >= 0 && syms[r].kind as i64 == SK_TEMPLATE { return r; }
        s = cxs[s].nnext as i64;
    }
    return -1;
}

// Parses a full id-expression / declarator-id / type name: the
// nested-name-specifier, then the unqualified-id. mode: 0 any, 1 the
// destructor's ~X allowed. Fills qn.kind and the name; does not look it up
// (see lookup_qn). Returns false if no name is there (pc unchanged).
recursive fn parse_qname(qn: QN&) -> bool {
    let start = pc;
    let had = parse_nns(qn);
    if qn.has_targs { return true; }
    qn.loc = tloc();
    if at(TK_IDENT) {
        qn.kind = QK_IDENT;
        qn.name = tu_toks[pc].val;
        adv();
        return true;
    }
    if at_kw(KW_TEMPLATE) && qn.qual && tk_n(1) == TK_IDENT {
        adv();
        qn.tkw = true;
        qn.kind = QK_IDENT;
        qn.name = tu_toks[pc].val;
        adv();
        return true;
    }
    if at_kw(KW_OPERATOR) {
        parse_operator_name(qn);
        return true;
    }
    if at(TK_TILDE) && (tk_n(1) == TK_IDENT || tk_n(1) == TK_KW + KW_DECLTYPE) {
        adv();
        qn.kind = QK_DTOR;
        if at_kw(KW_DECLTYPE) {
            qn.conv = parse_decltype();
            qn.name = 0;
        } else {
            qn.name = tu_toks[pc].val;
            adv();
            if at(TK_LESS) {
                // ~X<args>
                let s = if qn.scope >= 0 { qual_lookup(qn.scope as i64, qn.name) } else { unqual_lookup(qn.name) };
                if chain_has_template(s) { adv(); let a = parse_targs(); }
            }
        }
        return true;
    }
    if had { return true; }
    pc = start;
    return false;
}

// operator-function-id, conversion-function-id or literal operator.
recursive fn parse_operator_name(qn: QN&) {
    adv();      // operator
    qn.kind = QK_OP;
    let k = tk();
    if k == TK_KW + KW_NEW || k == TK_KW + KW_DELETE {
        let isnew = k == TK_KW + KW_NEW;
        adv();
        var arr = false;
        if at(TK_L_SQUARE) && tk_n(1) == TK_R_SQUARE { adv(); adv(); arr = true; }
        qn.op = (if isnew { if arr { OP_NEW_ARR } else { OP_NEW } } else { if arr { OP_DELETE_ARR } else { OP_DELETE } }) as! u8;
    } else if k == TK_L_PAREN && tk_n(1) == TK_R_PAREN {
        adv(); adv();
        qn.op = OP_CALL as! u8;
    } else if k == TK_L_SQUARE && tk_n(1) == TK_R_SQUARE {
        adv(); adv();
        qn.op = OP_SUBSCRIPT as! u8;
    } else if k == TK_STRING && tk_n(1) == TK_IDENT {
        // operator "" _x (older spelling)
        adv();
        qn.kind = QK_LITOP;
        qn.name = tu_toks[pc].val;
        adv();
        return;
    } else if k == TK_STRING {
        // operator ""_x: the suffix is part of the string token
        let t = tu_toks[pc];
        qn.kind = QK_LITOP;
        let sp = src[t.spell..t.spell + t.val];
        var j = sp.len;
        while j > 0 && sp[j - 1] != '"' { j--; }
        qn.name = intern(sp[j..]);
        adv();
        return;
    } else if k == TK_KW + KW_CO {
        adv();
        qn.op = OP_COAWAIT as! u8;
    } else {
        let op = tok_op(k);
        if op != 0 {
            adv();
            qn.op = op as! u8;
        } else {
            // conversion-function-id: operator type-specifiers ptr-operators
            qn.kind = QK_CONV;
            qn.conv = parse_conv_type();
            qn.name = id_conv;
            return;
        }
    }
    qn.name = op_ids[qn.op];
    // operator<<int> is not valid C++; operator() < is handled by the caller
}

// ---------------------------------------------------------------------------
// Looking a name up.

// Looks qn up (unless dependent): qn.sym is the newest symbol of the
// chain, -1 when not found.
recursive fn lookup_qn(qn: QN&) {
    if qn.dep != 0 { qn.sym = -1; return; }
    var name = qn.name;
    if qn.kind as i64 == QK_DTOR { name = id_dtor; }
    if name == 0 { qn.sym = -1; return; }
    if qn.scope >= 0 {
        qn.sym = qual_lookup(qn.scope as i64, name) as! i32;
        if qn.sym < 0 && scopes[qn.scope].kind as i64 == CS_CLASS && has_dep_base(qn.scope as i64) {
            // a member of a class whose bases are not known (yet): a dependent name
            qn.dep = scope_class_type(qn.scope as i64);
            if qn.dep == 0 { qn.dep = t_unknown; }
            qn.scope = -1;
        }
    } else {
        qn.sym = unqual_lookup(name) as! i32;
    }
}

// The type a parsed name denotes (it was looked up), or 0 when it is not a
// type. Template-ids of class and alias templates give their
// specialization; a dependent qualifier gives a dependent name.
recursive fn qn_type(qn: QN&) -> u32 {
    if qn.dep != 0 {
        return mk_depname(qn.dep, qn.name, if qn.has_targs { qn.targs } else { -1 });
    }
    let s = chain_type(qn.sym as i64);
    if s < 0 { return 0; }
    if syms[s].kind as i64 == SK_TEMPLATE {
        let k = tmpl_kind(s);
        if k == TT_CLASS || k == TT_ALIAS || k == TT_PARAM {
            if qn.has_targs { return specialization(s, qn.targs); }
            // the template's own name inside its definition
            return tmpl_injected(s);
        }
        return 0;
    }
    if qn.has_targs && cxs[s].flags & CF_INJECTED != 0 && cxs[s].tmpl >= 0 {
        // X<args> through the injected class name of a class template
        return specialization(tmpls[cxs[s].tmpl].sym as i64, qn.targs);
    }
    return syms[s].ty;
}

// ---------------------------------------------------------------------------
// Template arguments.

// Parses template arguments at '<' ... '>' (the '<' is at pc): the list.
recursive fn parse_targs() -> i32 {
    adv();      // <
    let mark = targ_scratch.len;
    targ_depth++;
    loop {
        if at_gt() { break; }
        if at(TK_EOF) { break; }
        parse_targ();
        if accept(TK_ELLIPSIS) {
            // a pack expansion
            let a = targ_scratch[targ_scratch.len - 1];
            if a.kind as i64 == TA_TYPE {
                targ_scratch[targ_scratch.len - 1].ty = mk_packexp(a.ty);
            } else if a.kind as i64 == TA_VALUE {
                targ_scratch[targ_scratch.len - 1].ty = mk_packexp(if a.ty == 0 { t_unknown } else { a.ty });
            }
        }
        if !accept(TK_COMMA) { break; }
    }
    targ_depth--;
    if !take_gt() { perr_expected("'>'"); }
    return targ_intern(mark);
}
var targ_depth: i64 = 0;

// One template argument, pushed to targ_scratch.
recursive fn parse_targ() {
    if looks_like_type_id() && type_id_then_gt() {
        let t = parse_type_id();
        targ_scratch.push(TArg { kind: TA_TYPE as! u8, rsv: 0, rsv2: 0, ty: t, v: 0 });
        return;
    }
    // a template name as a template template argument
    if at(TK_IDENT) || at(TK_COLONCOLON) {
        let sv = save();
        var qn = QN { .. };
        let diag0 = n_errors;
        diag_suppress++;
        let ok = parse_qname(qn);
        diag_suppress--;
        if ok && !qn.has_targs && (at_gt() || at(TK_COMMA) || at(TK_ELLIPSIS)) {
            lookup_qn(qn);
            let s = if qn.sym >= 0 { resolve(qn.sym as i64) } else { -1 };
            if s >= 0 && syms[s].kind as i64 == SK_TEMPLATE && tmpl_kind(s) != TT_FUNC && tmpl_kind(s) != TT_VAR {
                targ_scratch.push(TArg { kind: TA_TEMPLATE as! u8, rsv: 0, rsv2: 0, ty: 0, v: s });
                return;
            }
            if qn.dep != 0 && qn.tkw {
                targ_scratch.push(TArg { kind: TA_TEMPLATE as! u8, rsv: 0, rsv2: 0, ty: qn.dep, v: -1 });
                return;
            }
        }
        restore(sv);
    }
    let t0 = pc;
    let e = parse_cexpr_noGT();
    let ty = nodes[e].ty;
    if nodes[e].kind as i64 == N_CXX && nodes[e].op == 2 && nodes[e].flags & NF_PAREN == 0 && (at_gt() || at(TK_COMMA) || at(TK_ELLIPSIS)) {
        // a non-type template parameter: the canonical argument own_args makes
        let ps = nodes[e].a as i64;
        let dv = syms[ps].v;
        targ_scratch.push(TArg { kind: TA_VALUE as! u8, rsv: 0, rsv2: 0, ty: mk_tparam(dv >> 16, dv & 0xFFFF, 0, false), v: -1 });
        return;
    }
    if is_opaque(ty) || nodes[e].kind as i64 == N_ERROR {
        targ_scratch.push(TArg { kind: TA_VALUE as! u8, rsv: 0, rsv2: 0, ty: mk_depexpr(t0), v: t0 });
        return;
    }
    let ok, v = const_int(e);
    if ok {
        targ_scratch.push(TArg { kind: TA_VALUE as! u8, rsv: 0, rsv2: 0, ty: unqual(nonref(ty)), v: v });
    } else {
        // an address or a value D1 does not evaluate: opaque
        targ_scratch.push(TArg { kind: TA_VALUE as! u8, rsv: 0, rsv2: 0, ty: mk_depexpr(t0), v: t0 });
    }
}
