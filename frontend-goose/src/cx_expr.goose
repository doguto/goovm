// goosecc D1: C++ expressions. Parsing (the full C++17 grammar as
// libstdc++ and the corpora use it) and typing: every node gets a
// non-reference type and a value category. What D1 does not compute (an
// expression in a template pattern, a member of an uninstantiated
// template, a call resolved to a function template) gets an opaque type
// (dependent or TY_UNKNOWN) and an N_CXX node: it is never checked and
// never lowered.

namespace cx;

import std;
import os;
import dictionary;
import .common;
import .types;
import .ast;
import .sema;
import .pp;
import .ppexpr;
import .expr;
import .parse;
import .builtins;
import .cx_core;
import .cx_names;
import .cx_decl;
import .cx_class;
import .cx_tmpl;
import .cx_decl2;

// C++ node kinds (ast.goose has C's).
let N_THIS = 70;        // ty: pointer to the class
let N_MCALL = 71;       // a = object (glvalue of class type), b = member function, v/c = arguments; op 1: virtual call
let N_CTOR = 72;        // a = constructor (0: value-initialization), ty = class, v/c = arguments: a prvalue
let N_TEMP = 73;        // a = prvalue materialized as a temporary: an xvalue
let N_NEW = 74;
let N_DELETE = 75;
let N_THROW = 76;
let N_CXX = 77;         // an expression D1 does not model (opaque type)
let N_TYPEID = 78;
let N_DYNCAST = 79;
let N_FUNCREF = 80;     // an unresolved overload set: a = the first symbol of the chain, b = object for member calls (0), c = template args + 1
let N_INITBRACE = 81;   // a braced-init-list before its target is known: v/c = elements

let NF_XVALUE = 512;    // with NF_LVALUE: an xvalue
let NF_REFDEREF = 1024; // a reference variable / member / call returning a reference: the object is behind it
let NF_DEP = 2048;      // dependent or unknown

fn opaque_node(loc: u32) -> u32 {
    let n = node(N_CXX, 0, t_unknown, 0, 0, 0, loc);
    nodes[n].flags = NF_DEP;
    if opq_report() { opq_note(loc, 0); }
    return n;
}
fn dep_node(ty: u32, loc: u32) -> u32 {
    let n = node(N_CXX, 0, if ty == 0 { t_unknown } else { ty }, 0, 0, 0, loc);
    nodes[n].flags = NF_DEP;
    if opq_report() { opq_note(loc, 1); }
    return n;
}

// D2: GOOSECC_OPAQUE=1 lists the opaque expressions made outside templates
// (what the semantic analysis does not compute yet), with GOOSECC_OPAQUE=2
// also inside tentative parses.
var opq_mode: i64 = -1;
fn opq_report() -> bool {
    if opq_mode < 0 {
        var v: u8[>..] = [];
        opq_mode = if env("GOOSECC_OPAQUE", v) && v.len > 0 { (v[0] - '0') as i64 } else { 0 };
    }
    return opq_mode > 0;
}
fn opq_note(loc: u32, kind: i64) {
    if dependent_ctx() { return; }
    if opq_mode < 2 && diag_suppress > 0 && diag_suppress != diag_inst_level { return; }
    var o: u8[>..] = [];
    loc_prefix(o, loc as i64);
    o.append(if kind == 0 { "opaque" } else { "opaque-typed" });
    o.append(" at token ");
    tok_desc(o, pc);
    o.push('\n');
    write_stderr(o);
}
fn is_opq(n: u32) -> bool { nodes[n].flags & NF_DEP != 0 || is_opaque(nodes[n].ty) }

var paren_depth: i64 = 0;   // template argument lists: a '>' at paren depth 0 ends the list

// The constant value of an integral (or unscoped enum, bool) expression.
recursive fn const_int(e: u32) -> bool, i64 {
    if is_opq(e) { return false, 0; }
    let t = nodes[e].ty;
    if !is_integer(t) && kind_of(t) != TY_BOOL { return false, 0; }
    let r = if is_lvalue(e) { icast(e, CK_LVAL2RVAL, unqual(t)) } else { e };
    // const integral variables with constant initializers are constants
    // (C++ [expr.const]): C's evaluator reads them with fold_cvars
    return fold_gnu(r);
}

fn sa_checked(e: u32) -> bool { true }

// ---------------------------------------------------------------------------
// Entry points.

recursive fn parse_cexpr_full() -> u32 { parse_expr_cx() }
recursive fn parse_cexpr() -> u32 { parse_cond_cx() }
// A constant-expression where '>' ends a template argument list.
recursive fn parse_cexpr_noGT() -> u32 {
    let sp = paren_depth;
    paren_depth = 0;
    targ_depth++;
    let e = parse_cond_cx();
    targ_depth--;
    paren_depth = sp;
    return e;
}
recursive fn parse_cexpr_noGT_init() -> u32 { parse_cond_cx() }

recursive fn parse_expr_cx() -> u32 {
    var l = parse_assign_cx();
    while at(TK_COMMA) && tk_n(1) != TK_ELLIPSIS {
        let loc = tloc();
        adv();
        let r = parse_assign_cx();
        l = mk_binop(OP_COMMA, B_COMMA, l, r, loc);
    }
    return l;
}

recursive fn parse_assign_cx() -> u32 {
    if at_kw(KW_THROW) { return parse_throw(); }
    let l = parse_cond_cx();
    let k = tk();
    let aop = assign_op(k);
    if k == TK_EQUAL || aop != 0 {
        let loc = tloc();
        adv();
        var r: u32 = 0;
        if at(TK_L_BRACE) { r = parse_braced(); } else { r = parse_assign_cx(); }
        return mk_assign_cx(if k == TK_EQUAL { 0 } else { aop }, l, r, loc, k);
    }
    return l;
}

recursive fn parse_throw() -> u32 {
    let loc = tloc();
    adv();
    var e: u32 = 0;
    let k = tk();
    if k != TK_SEMI && k != TK_R_PAREN && k != TK_COMMA && k != TK_COLON && k != TK_R_SQUARE && k != TK_R_BRACE {
        e = parse_assign_cx();
    }
    if cg_on { return cg_throw(e, loc); }
    return node(N_THROW, 0, t_void, e as i64, 0, 0, loc);
}

recursive fn parse_cond_cx() -> u32 {
    let c = parse_bin(1);
    if !at(TK_QUESTION) { return c; }
    let loc = tloc();
    adv();
    var a: u32 = 0;
    if at(TK_COLON) {
        // GNU a ?: b
        a = 0;
    } else {
        let sp = paren_depth;
        paren_depth++;
        a = parse_expr_cx();
        paren_depth = sp;
    }
    expect(TK_COLON, "':'");
    let b = parse_assign_cx();
    return mk_cond_cx(c, a, b, loc);
}

// Binary operator precedence (higher binds tighter), 0 for none.
fn bin_prec_cx(k: i64) -> i64 {
    if (k == TK_GREATER || k == TK_GREATERGREATER || k == TK_GREATEREQUAL || k == TK_GREATERGREATEREQUAL) &&
        targ_depth > 0 && paren_depth == 0 { return 0; }
    return match k {
        TK_PIPEPIPE => 1, TK_AMPAMP => 2, TK_PIPE => 3, TK_CARET => 4, TK_AMP => 5,
        TK_EQUALEQUAL, TK_EXCLAIMEQUAL => 6,
        TK_LESS, TK_GREATER, TK_LESSEQUAL, TK_GREATEREQUAL => 7,
        TK_SPACESHIP => 8,
        TK_LESSLESS, TK_GREATERGREATER => 9,
        TK_PLUS, TK_MINUS => 10,
        TK_STAR, TK_SLASH, TK_PERCENT => 11,
        TK_PERIODSTAR, TK_ARROWSTAR => 12,
        _ => 0,
    };
}

recursive fn parse_bin(minp: i64) -> u32 {
    var l = parse_cast_cx();
    loop {
        let k = tk();
        let p = bin_prec_cx(k);
        if p == 0 || p < minp { break; }
        if tk_n(1) == TK_ELLIPSIS { break; }    // a fold-expression: (e op ...)
        let loc = tloc();
        adv();
        let r = parse_bin(p + 1);
        l = mk_binop(tok_op(k), bin_op(k), l, r, loc);
        if k == TK_PERIODSTAR || k == TK_ARROWSTAR { nodes[l].flags = nodes[l].flags | NF_LVALUE; }
    }
    return l;
}

// ( type-id ) cast-expression, or a unary-expression.
recursive fn parse_cast_cx() -> u32 {
    if at(TK_L_PAREN) && tk_n(1) != TK_L_BRACE && paren_type_ahead() {
        let loc = tloc();
        let sv = save();
        adv();
        let t = parse_type_id();
        if at(TK_R_PAREN) {
            adv();
            if at(TK_L_BRACE) {
                // (T){...}: a GNU compound literal
                let b = parse_braced();
                return mk_compound_lit(t, b, loc);
            }
            let e = parse_cast_cx();
            return mk_cast_cx(t, e, loc, CAST_C);
        }
        restore(sv);
    }
    return parse_unary_cx();
}

// After '(' at pc: a type-id followed by ')' (a cast), as opposed to a
// parenthesized expression?
recursive fn paren_type_ahead() -> bool {
    let sv = save();
    adv();
    let r = looks_like_type_id();
    var ok = false;
    if r {
        // the type-id must end at the matching ')'
        diag_suppress++;
        let t = parse_type_id();
        diag_suppress--;
        ok = at(TK_R_PAREN);
        if ok {
            // ( T ) followed by something that cannot start an operand is
            // not a cast: (x) + y where x is a type cannot happen, but
            // (T) alone before ')' or ';' ... is a parenthesized expression
            let k = tk_n(1);
            if k == TK_R_PAREN || k == TK_SEMI || k == TK_COMMA || k == TK_R_SQUARE || k == TK_R_BRACE || k == TK_EOF ||
               k == TK_COLON || k == TK_QUESTION || k == TK_EQUAL { ok = false; }
        }
    }
    restore(sv);
    return ok;
}

recursive fn parse_unary_cx() -> u32 {
    let k = tk();
    let loc = tloc();
    if k == TK_PLUSPLUS || k == TK_MINUSMINUS {
        adv();
        let e = parse_cast_cx();
        return mk_incdec_cx(e, if k == TK_PLUSPLUS { U_PREINC } else { U_PREDEC }, loc, true);
    }
    if k == TK_AMP {
        adv();
        let e = parse_cast_cx();
        return mk_addr_cx(e, loc);
    }
    if k == TK_STAR {
        adv();
        let e = parse_cast_cx();
        return mk_deref_cx(e, loc);
    }
    if k == TK_PLUS || k == TK_MINUS || k == TK_TILDE || k == TK_EXCLAIM {
        adv();
        let e = parse_cast_cx();
        return mk_unary_cx(k, e, loc);
    }
    if k == TK_AMPAMP && tk_n(1) == TK_IDENT {
        // GNU &&label
        adv();
        let name = tu_toks[pc].val;
        adv();
        let l = label_ref(name, loc);
        return node(N_LABELADDR, 0, t_voidptr, l, 0, 0, loc);
    }
    if k == TK_KW + KW_SIZEOF {
        adv();
        if at(TK_ELLIPSIS) {
            // sizeof...(pack)
            adv();
            let paren = accept(TK_L_PAREN);
            var n: i64 = -1;
            if at(TK_IDENT) { n = pack_size_of(tu_toks[pc].val); }
            if paren { skip_to(TK_R_PAREN); expect(TK_R_PAREN, "')'"); } else { adv(); }
            if n >= 0 {
                let r = int_node(n, t_ulong, loc);
                return r;
            }
            return dep_node(t_ulong, loc);
        }
        if at(TK_L_PAREN) && paren_is_type() {
            adv();
            let t = parse_type_id();
            expect(TK_R_PAREN, "')'");
            return mk_sizeof_cx(t, false, loc);
        }
        unevaluated++;
        let e = parse_unary_cx();
        unevaluated--;
        return mk_sizeof_cx(nodes[e].ty, false, loc);
    }
    if k == TK_KW + KW_ALIGNOF {
        adv();
        if at(TK_L_PAREN) && paren_is_type() {
            adv();
            let t = parse_type_id();
            expect(TK_R_PAREN, "')'");
            return mk_sizeof_cx(t, true, loc);
        }
        unevaluated++;
        let e = parse_unary_cx();
        unevaluated--;
        return mk_sizeof_cx(nodes[e].ty, true, loc);
    }
    if k == TK_KW + KW_NOEXCEPT {
        adv();
        expect(TK_L_PAREN, "'('");
        unevaluated++;
        let sp = paren_depth;
        paren_depth++;
        let e = parse_expr_cx();
        paren_depth = sp;
        unevaluated--;
        expect(TK_R_PAREN, "')'");
        if is_opq(e) || dependent_ctx() { return dep_node(t_bool, loc); }
        return int_node(0, t_bool, loc);
    }
    if k == TK_KW + KW_NEW || (k == TK_COLONCOLON && tk_n(1) == TK_KW + KW_NEW) { return parse_new(); }
    if k == TK_KW + KW_DELETE || (k == TK_COLONCOLON && tk_n(1) == TK_KW + KW_DELETE) { return parse_delete(); }
    if k == TK_KW + KW_EXTENSION { adv(); return parse_cast_cx(); }
    if k == TK_KW + KW_REAL || k == TK_KW + KW_IMAG {
        adv();
        let e = parse_cast_cx();
        if is_opq(e) { return e; }
        return mk_real_imag(e, k == TK_KW + KW_REAL, loc);
    }
    if k == TK_KW + KW_CO { adv(); let e = parse_cast_cx(); return opaque_node(loc); }
    return parse_postfix_cx(parse_primary_cx());
}

// After sizeof/alignof: ( type-id )?
recursive fn paren_is_type() -> bool {
    let sv = save();
    adv();
    let r = looks_like_type_id();
    var ok = false;
    if r {
        diag_suppress++;
        let t = parse_type_id();
        diag_suppress--;
        ok = at(TK_R_PAREN);
    }
    restore(sv);
    return ok;
}

recursive fn parse_postfix_cx(e0: u32) -> u32 {
    var e = e0;
    loop {
        let k = tk();
        let loc = tloc();
        if k == TK_L_SQUARE && tk_n(1) != TK_L_SQUARE {
            adv();
            let sp = paren_depth;
            paren_depth++;
            var i: u32 = 0;
            if at(TK_L_BRACE) { i = parse_braced(); } else { i = parse_expr_cx(); }
            paren_depth = sp;
            expect(TK_R_SQUARE, "']'");
            e = mk_index_cx(e, i, loc);
            continue;
        }
        if k == TK_L_PAREN {
            e = parse_call_cx(e);
            continue;
        }
        if k == TK_PERIOD || k == TK_ARROW {
            adv();
            e = parse_member_access(e, k == TK_ARROW, loc);
            continue;
        }
        if k == TK_PLUSPLUS || k == TK_MINUSMINUS {
            adv();
            e = mk_incdec_cx(e, if k == TK_PLUSPLUS { U_POSTINC } else { U_POSTDEC }, loc, false);
            continue;
        }
        break;
    }
    return e;
}

// Arguments of a call: ( args ) pushed to nscratch from mark.
recursive fn parse_args() -> i64 {
    adv();      // (
    let sp = paren_depth;
    paren_depth++;
    let mark = nscratch.len;
    while !at(TK_R_PAREN) && !at(TK_EOF) {
        var a: u32 = 0;
        let p0 = pc;
        let pm = pk_refs.len;
        if at(TK_L_BRACE) { a = parse_braced(); } else { a = parse_assign_cx(); }
        if at(TK_ELLIPSIS) {
            let ok, n = pk_count(pm);
            if ok {
                // D2: a pack expansion of bound packs
                adv();
                let p1 = pc;
                for i in n {
                    pc = p0;
                    let am = pk_activate(pm, i);
                    var b: u32 = 0;
                    if at(TK_L_BRACE) { b = parse_braced(); } else { b = parse_assign_cx(); }
                    pk_active.resize(am);
                    nscratch.push(b);
                }
                pc = p1;
                pk_refs.resize(pm);
                if !accept(TK_COMMA) { break; }
                continue;
            }
            pk_refs.resize(pm);
        }
        if accept(TK_ELLIPSIS) { nodes[a].flags = nodes[a].flags | NF_DEP; }
        nscratch.push(a);
        if !accept(TK_COMMA) { break; }
    }
    paren_depth = sp;
    expect(TK_R_PAREN, "')'");
    return mark;
}

recursive fn parse_call_cx(callee: u32) -> u32 {
    let loc = tloc();
    let mark = parse_args();
    let r = mk_call_cx(callee, mark, loc);
    nscratch.resize(mark);
    return r;
}

// a.member / p->member (with template, ~pseudo-destructor, operator names).
recursive fn parse_member_access(base: u32, arrow: bool, loc: u32) -> u32 {
    var qn = QN { .. };
    if at_kw(KW_TEMPLATE) { adv(); qn.tkw = true; }
    // the object's class scope: names after . are looked up there first
    var obj_ty = nodes[base].ty;
    if arrow {
        if is_pointer(obj_ty) { obj_ty = tbase(obj_ty); }
        else if is_record(obj_ty) && !is_opaque(obj_ty) {
            // an overloaded operator->: D1 resolves it below; the member
            // name is looked up in the result
            obj_ty = arrow_result(obj_ty);
        } else { obj_ty = t_unknown; }
    }
    let csc = if is_record(obj_ty) && !is_opq(base) { type_scope(obj_ty) } else { -1 };
    // ~T pseudo-destructor or destructor call
    if at(TK_TILDE) {
        adv();
        if at_kw(KW_DECLTYPE) { let t = parse_decltype(); }
        else {
            var dq = QN { .. };
            parse_qname(dq);
        }
        return dep_node(t_unknown, loc);
    }
    if (at(TK_IDENT) || at(TK_COLONCOLON)) && csc >= 0 && !qn.tkw {
        // a qualified member name (a.Base::f) or a plain one, looked up in the class
        if at(TK_IDENT) && tk_n(1) != TK_COLONCOLON {
            let name = tu_toks[pc].val;
            let mloc = tloc();
            adv();
            let s = class_lookup(csc, name);
            var targs: i32 = -1;
            if at(TK_LESS) && chain_has_template(s) { targs = parse_targs(); }
            if s < 0 {
                if has_dep_base(csc) || scopes[csc].flags & SCF_PATTERN != 0 || dependent_ctx() { return opaque_node(loc); }
                if diag_suppress == 0 { err_at(mloc, str("no member named '", ident_text(name as i64), "' in ", tname(obj_ty))); }
                return opaque_node(loc);
            }
            return mk_member_ref(base, arrow, s, targs, loc);
        }
    }
    // anything else: parse the name, opaque result
    let sv_scope = cur_scope;
    if csc >= 0 { cur_scope = csc; }
    diag_suppress++;
    if at_kw(KW_OPERATOR) { parse_operator_name(qn); }
    else { parse_qname(qn); }
    diag_suppress--;
    cur_scope = sv_scope;
    if csc >= 0 && qn.dep == 0 {
        lookup_qn(qn);
        if qn.sym >= 0 { return mk_member_ref(base, arrow, qn.sym as i64, qn.targs, loc); }
    }
    return opaque_node(loc);
}

// The class an overloaded operator-> leads to (its return type's pointee), or unknown.
recursive fn arrow_result(t: u32) -> u32 {
    let sc = type_scope(t);
    if sc < 0 { return t_unknown; }
    let s = class_lookup(sc, op_ids[OP_ARROW]);
    if s < 0 { return t_unknown; }
    let f = resolve(s);
    if f < 0 || syms[f].kind as i64 != SK_FUNC { return t_unknown; }
    let rt = nonref(types[syms[f].ty >> 4].base);
    if is_pointer(rt) { return tbase(rt); }
    return t_unknown;
}

// ---------------------------------------------------------------------------
// Primary expressions.

recursive fn parse_primary_cx() -> u32 {
    let k = tk();
    let loc = tloc();
    if k == TK_NUMBER {
        let t = tu_toks[pc];
        adv();
        if has_udl(t) { return opaque_node(loc); }
        return number_literal(t);
    }
    if k == TK_CHAR {
        let t = tu_toks[pc];
        adv();
        if has_udl(t) { return opaque_node(loc); }
        return char_literal_cx(t);
    }
    if k == TK_STRING {
        // adjacent literals; a ud-suffix makes a literal operator call
        var j = pc;
        var udl = false;
        while tu_toks[j].kind as i64 == TK_STRING { if has_udl(tu_toks[j]) { udl = true; } j++; }
        if udl { pc = j; return opaque_node(loc); }
        let s = string_literal();
        // C++: the elements are const
        let st = nodes[s].ty;
        nodes[s].ty = mk_array(with_quals(tbase(st), Q_CONST), types[st >> 4].n);
        strs[nodes[s].a].elem = strs[nodes[s].a].elem;
        return s;
    }
    if k == TK_KW + KW_TRUE || k == TK_KW + KW_FALSE {
        adv();
        return int_node(if k == TK_KW + KW_TRUE { 1 } else { 0 }, t_bool, loc);
    }
    if k == TK_KW + KW_NULLPTR {
        adv();
        let n = node_v(N_INT, 0, t_nullptr, 0, 0, 0, loc, 0);
        nodes[n].flags = NF_ICE;
        return n;
    }
    if k == TK_KW + KW_NULL_GNU {
        adv();
        return int_node(0, t_long, loc);
    }
    if k == TK_KW + KW_THIS {
        adv();
        return mk_this(loc);
    }
    if k == TK_L_PAREN {
        if tk_n(1) == TK_L_BRACE {
            // GNU statement expression
            adv();
            let body = parse_stmt_expr_body();
            expect(TK_R_PAREN, "')'");
            return body;
        }
        adv();
        // fold expressions: ( ... op e ) ( e op ... ) ( e op ... op e )
        if at(TK_ELLIPSIS) {
            adv();
            let sp0 = paren_depth;
            paren_depth++;
            let f = parse_fold_left(loc);
            paren_depth = sp0;
            return f;
        }
        let sp = paren_depth;
        paren_depth++;
        let p0 = pc;
        let pm = pk_refs.len;
        let e = parse_expr_cx();
        if (tok_op(tk()) != 0 || at(TK_COMMA)) && tk_n(1) == TK_ELLIPSIS {
            // e op ... [op e]
            let f = parse_fold_rest(e, p0, pm, loc);
            paren_depth = sp;
            return f;
        }
        paren_depth = sp;
        expect(TK_R_PAREN, "')'");
        nodes[e].flags = nodes[e].flags | NF_PAREN;
        return e;
    }
    if k == TK_L_SQUARE { return parse_lambda(); }
    if k == TK_L_BRACE { return parse_braced(); }
    if k >= TK_KW {
        let w = k - TK_KW;
        if w == KW_STATIC_CAST || w == KW_DYNAMIC_CAST || w == KW_REINTERPRET_CAST || w == KW_CONST_CAST {
            adv();
            expect(TK_LESS, "'<'");
            targ_depth++;
            let sp = paren_depth;
            paren_depth = 0;
            let t = parse_type_id();
            paren_depth = sp;
            targ_depth--;
            if !take_gt() { perr_expected("'>'"); }
            expect(TK_L_PAREN, "'('");
            let sp2 = paren_depth;
            paren_depth++;
            let e = parse_expr_cx();
            paren_depth = sp2;
            expect(TK_R_PAREN, "')'");
            let ck = match w { KW_STATIC_CAST => CAST_STATIC, KW_DYNAMIC_CAST => CAST_DYNAMIC, KW_REINTERPRET_CAST => CAST_REINTERPRET, _ => CAST_CONST };
            return mk_cast_cx(t, e, loc, ck);
        }
        if w == KW_TYPEID {
            adv();
            expect(TK_L_PAREN, "'('");
            let sp = paren_depth;
            paren_depth++;
            var tt: u32 = 0;
            var te: u32 = 0;
            if looks_like_type_id() && type_id_then(TK_R_PAREN, TK_R_PAREN) { tt = parse_type_id(); } else { te = parse_expr_cx(); }
            paren_depth = sp;
            expect(TK_R_PAREN, "')'");
            if cg_on && !dependent_ctx() && (tt != 0 || te != 0) { return cg_typeid(tt, te, loc); }
            return typeid_node(loc);
        }
        if w == KW_TRAIT { return parse_trait(); }
        if w == KW_FUNC {
            let name = ident_text(tu_toks[pc].val as i64);
            adv();
            return func_name_node(name, loc);
        }
        if w == KW_BUILTIN_X {
            let name = ident_text(tu_toks[pc].val as i64);
            adv();
            if at(TK_L_PAREN) { skip_group(); }
            if name == "__builtin_LINE" || name == "__builtin_COLUMN" { return int_node(0, t_uint, loc); }
            if name == "__builtin_source_location" { return dep_node(t_voidptr, loc); }
            return make_string_node("", loc);
        }
        if w == KW_VA_ARG {
            adv();
            expect(TK_L_PAREN, "'('");
            let e = parse_assign_cx();
            expect(TK_COMMA, "','");
            let t = parse_type_id();
            expect(TK_R_PAREN, "')'");
            if is_opq(e) || is_opaque(t) { return dep_node(t, loc); }
            let n = node(N_VAARG, 0, t, rv(e) as i64, 0, 0, loc);
            return n;
        }
        if w == KW_OFFSETOF {
            adv();
            expect(TK_L_PAREN, "'('");
            let t = parse_type_id();
            expect(TK_COMMA, "','");
            skip_to(TK_R_PAREN);
            expect(TK_R_PAREN, "')'");
            return dep_node(t_ulong, loc);
        }
        if w == KW_CHOOSE_EXPR || w == KW_CONVERTVECTOR || w == KW_BITCAST || w == KW_TYPES_COMPAT || w == KW_GENERIC {
            adv();
            if at(TK_L_PAREN) { skip_group(); }
            return opaque_node(loc);
        }
        if w == KW_TYPENAME || is_type_kw(w) || w == KW_DECLTYPE {
            // a functional cast: T(args), T{args}; typename X::y(args); decltype(e)
            if w == KW_DECLTYPE && decltype_then_cc() { return parse_id_expr(); }
            let t = parse_simple_type_for_cast();
            return parse_functional_cast(t, loc);
        }
        if w == KW_OPERATOR { return parse_id_expr(); }
        if w == KW_TEMPLATE && tk_n(1) == TK_IDENT { return parse_id_expr(); }
        if w == KW_REQUIRES || w == KW_CO { adv(); if at(TK_L_PAREN) { skip_group(); } if at(TK_L_BRACE) { skip_group(); } return opaque_node(loc); }
    }
    if k == TK_IDENT || k == TK_COLONCOLON || k == TK_TILDE { return parse_id_expr(); }
    perr_expected("an expression");
    if !at(TK_EOF) && !at(TK_SEMI) && !at(TK_R_PAREN) && !at(TK_R_BRACE) && !at(TK_R_SQUARE) && !at(TK_COMMA) { adv(); }
    return opaque_node(loc);
}

fn has_udl(t: Tok) -> bool {
    let s = src[t.spell..t.spell + t.val];
    if t.kind as i64 == TK_NUMBER {
        for c in s { if c == '_' { return true; } }
        // a hex digit is not a suffix; only _x suffixes are UDLs in practice
        return false;
    }
    return s.len > 0 && s[s.len - 1] != '"' && s[s.len - 1] != '\'';
}

fn char_literal_cx(t: Tok) -> u32 {
    let n = char_literal(t);
    let c = src[t.spell];
    if c == '\'' {
        // a plain character literal is a char (int if it has several characters)
        let v, u = char_value(t);
        var len = 0;
        var j = t.spell as i64 + 1;
        let e = t.spell as i64 + t.val as i64 - 1;
        while j < e { if src[j] == '\\' { j += 2; } else { j++; } len++; }
        if len <= 1 || src[t.spell + 1] == '\\' {
            nodes[n].ty = t_char;
            nodes[n].v = trunc_to(nodes[n].v, t_char);
        }
    } else if c == 'L' {
        nodes[n].ty = t_wchar_cxx;
    } else if c == 'u' && src[t.spell + 1] == '8' {
        nodes[n].ty = if opt_cxx_std >= 20 { t_char8 } else { t_char };
    }
    return n;
}

fn func_name_node(name: const u8[:], loc: u32) -> u32 {
    if cur_func_cx < 0 { return make_string_node("", loc); }
    return make_string_node(ident_text(syms[cur_func_cx].name as i64), loc);
}
var cur_func_cx: i64 = -1;

fn typeid_node(loc: u32) -> u32 {
    // std::type_info: an lvalue of class type std::type_info (unknown in D1 unless declared)
    let n = node(N_TYPEID, 0, t_unknown, 0, 0, 0, loc);
    nodes[n].flags = NF_LVALUE | NF_DEP;
    return n;
}

// A type for a functional cast: simple-type-specifiers (int, unsigned
// long, typename X::y, decltype(e), X<args>).
recursive fn parse_simple_type_for_cast() -> u32 {
    var ds = CDS { .. };
    var a = Attrs { .. };
    parse_cds(ds, a, DC_TYPEID);
    var t = finish_cds(ds);
    if t == 0 { t = t_unknown; }
    return t;
}

// T(args) or T{args} (or a bare type: an error unless sizeof etc. handled it).
recursive fn parse_functional_cast(t: u32, loc: u32) -> u32 {
    if at(TK_L_PAREN) {
        let mark = parse_args();
        let r = mk_construct(t, mark, loc, false);
        nscratch.resize(mark);
        return r;
    }
    if at(TK_L_BRACE) {
        let b = parse_braced();
        let mark = nscratch.len;
        let n = nodes[b].c as i64;
        for i in n { nscratch.push(nlist[nodes[b].v + i]); }
        let r = mk_construct(t, mark, loc, true);
        nscratch.resize(mark);
        return r;
    }
    perr_expected("'(' or '{'");
    return opaque_node(loc);
}

// { initializer-list }: an N_INITBRACE of the elements (designators and
// nested braces kept).
recursive fn parse_braced() -> u32 {
    let loc = tloc();
    adv();      // {
    let sp = paren_depth;
    paren_depth++;
    let mark = nscratch.len;
    var desig = false;
    while !at(TK_R_BRACE) && !at(TK_EOF) {
        if at(TK_PERIOD) && tk_n(1) == TK_IDENT {
            // a designator (C++20 / GNU): .x = v
            adv();
            adv();
            accept(TK_EQUAL);
            desig = true;
        } else if at(TK_L_SQUARE) && tk_n(1) != TK_L_SQUARE {
            skip_group();
            accept(TK_EQUAL);
            desig = true;
        }
        var e: u32 = 0;
        let p0 = pc;
        let pm = pk_refs.len;
        if at(TK_L_BRACE) { e = parse_braced(); } else { e = parse_assign_cx(); }
        if at(TK_ELLIPSIS) {
            let ok, n = pk_count(pm);
            if ok {
                adv();
                let p1 = pc;
                for i in n {
                    pc = p0;
                    let am = pk_activate(pm, i);
                    var b: u32 = 0;
                    if at(TK_L_BRACE) { b = parse_braced(); } else { b = parse_assign_cx(); }
                    pk_active.resize(am);
                    nscratch.push(b);
                }
                pc = p1;
                pk_refs.resize(pm);
                if !accept(TK_COMMA) { break; }
                continue;
            }
            pk_refs.resize(pm);
        }
        accept(TK_ELLIPSIS);
        nscratch.push(e);
        if !accept(TK_COMMA) { break; }
    }
    paren_depth = sp;
    expect(TK_R_BRACE, "'}'");
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    let n = node_v(N_INITBRACE, 0, t_unknown, 0, 0, count, loc, start);
    if desig { nodes[n].op = 3; }
    return n;
}

// A lambda-expression: its closure type is not modelled in D1.
recursive fn parse_lambda() -> u32 {
    let loc = tloc();
    skip_group();       // [captures]
    if at(TK_LESS) { skip_angles(); }
    var a = Attrs { .. };
    cx_attrs(a);
    if at(TK_L_PAREN) {
        // the parameters: parsed for their syntax, in a scope of their own
        var dummy = CD { .. };
        var variadic = false;
        let st, n = parse_cparams(variadic);
    }
    // mutable constexpr consteval noexcept attributes -> trailing
    loop {
        if at_kw(KW_MUTABLE) || at_kw(KW_CONSTEXPR) || at_kw(KW_CONSTEVAL) { adv(); continue; }
        if at_kw(KW_NOEXCEPT) { adv(); if at(TK_L_PAREN) { skip_group(); } continue; }
        if at_kw(KW_THROW) { adv(); if at(TK_L_PAREN) { skip_group(); } continue; }
        if at_attr_start() { cx_attrs(a); continue; }
        break;
    }
    if accept(TK_ARROW) { let t = parse_type_id(); }
    if at(TK_L_BRACE) { skip_group(); }
    return opaque_node(loc);
}

// Type trait expressions: __is_class(T), __is_same(T, U), __array_rank(T) ...
recursive fn parse_trait() -> u32 {
    let loc = tloc();
    let name = ident_text(tu_toks[pc].val as i64);
    adv();
    if !at(TK_L_PAREN) { return opaque_node(loc); }
    adv();
    let sp = paren_depth;
    paren_depth++;
    let mark = trait_args.len;
    var any_dep = false;
    while !at(TK_R_PAREN) && !at(TK_EOF) {
        if looks_like_type_id() && type_id_then(TK_COMMA, TK_R_PAREN) {
            let t = parse_type_id();
            trait_args.push(t);
            if is_opaque(t) { any_dep = true; }
        } else {
            let e = parse_assign_cx();
            if is_opq(e) { any_dep = true; }
            trait_args.push(nodes[e].ty);
        }
        accept(TK_ELLIPSIS);
        if !accept(TK_COMMA) { break; }
    }
    paren_depth = sp;
    expect(TK_R_PAREN, "')'");
    let rt = if name == "__array_rank" || name == "__array_extent" || name == "__datasizeof" { t_ulong } else { t_bool };
    if any_dep || dependent_ctx() {
        trait_args.resize(mark);
        return dep_node(rt, loc);
    }
    let ok, v = eval_trait(name, mark);
    trait_args.resize(mark);
    if !ok { return dep_node(rt, loc); }
    return int_node(v, rt, loc);
}
var trait_args: u32[>..<] = [];

// The traits D1 evaluates exactly (on complete non-template types);
// others are left opaque.
fn eval_trait(name: const u8[:], mark: i64) -> bool, i64 {
    let n = trait_args.len - mark;
    if n < 1 { return false, 0; }
    let t = trait_args[mark];
    let k = kind_of(t);
    if name == "__is_same" || name == "__is_same_as" {
        if n < 2 { return false, 0; }
        return true, if trait_args[mark] == trait_args[mark + 1] { 1 } else { 0 };
    }
    if name == "__is_void" { return true, if k == TY_VOID { 1 } else { 0 }; }
    if name == "__is_integral" { return true, if (k >= TY_BOOL && k <= TY_UINT128) { 1 } else { 0 }; }
    if name == "__is_floating_point" { return true, if is_float_kind(k) { 1 } else { 0 }; }
    if name == "__is_arithmetic" { return true, if (k >= TY_BOOL && k <= TY_UINT128) || is_float_kind(k) { 1 } else { 0 }; }
    if name == "__is_pointer" { return true, if k == TY_POINTER { 1 } else { 0 }; }
    if name == "__is_lvalue_reference" { return true, if k == TY_LREF { 1 } else { 0 }; }
    if name == "__is_rvalue_reference" { return true, if k == TY_RREF { 1 } else { 0 }; }
    if name == "__is_reference" { return true, if k == TY_LREF || k == TY_RREF { 1 } else { 0 }; }
    if name == "__is_array" { return true, if k == TY_ARRAY { 1 } else { 0 }; }
    if name == "__is_enum" { return true, if k == TY_ENUM { 1 } else { 0 }; }
    if name == "__is_union" { return true, if k == TY_UNION { 1 } else { 0 }; }
    if name == "__is_class" { return true, if k == TY_STRUCT { 1 } else { 0 }; }
    if name == "__is_function" { return true, if k == TY_FUNC { 1 } else { 0 }; }
    if name == "__is_const" { return true, if quals(t) & Q_CONST != 0 { 1 } else { 0 }; }
    if name == "__is_volatile" { return true, if quals(t) & Q_VOLATILE != 0 { 1 } else { 0 }; }
    if name == "__is_member_pointer" { return true, if k == TY_MEMPTR { 1 } else { 0 }; }
    if name == "__is_scoped_enum" { return true, if is_scoped_enum(t) { 1 } else { 0 }; }
    return false, 0;
}

// ---------------------------------------------------------------------------
// id-expressions.

recursive fn parse_id_expr() -> u32 {
    let loc = tloc();
    var qn = QN { .. };
    if !parse_qname(qn) {
        perr_expected("an expression");
        adv();
        return opaque_node(loc);
    }
    // a template-id of a function template, or X<args> of a class (a functional cast follows)
    if qn.dep != 0 {
        // a dependent name: T::x, T::template f<U>, typename-less X<T>::y
        if at(TK_L_PAREN) {
            let mark = parse_args();
            nscratch.resize(mark);
        }
        return dep_node(t_unknown, loc);
    }
    if qn.kind as i64 == QK_IDENT && !qn.has_targs && at(TK_LESS) {
        // name < ... : a template-id only if the name is a template
        lookup_qn(qn);
        if chain_has_template(qn.sym as i64) {
            qn.targs = parse_targs();
            qn.has_targs = true;
        }
    } else {
        lookup_qn(qn);
    }
    if qn.dep != 0 {
        // a member of a class whose bases are unknown
        if at(TK_L_PAREN) {
            let mark = parse_args();
            nscratch.resize(mark);
        }
        return dep_node(t_unknown, loc);
    }
    let s0 = qn.sym as i64;
    if s0 < 0 {
        if qn.kind as i64 == QK_IDENT && at(TK_L_PAREN) {
            // an unqualified call to an undeclared name: argument-dependent
            // lookup may still find it (D1 does not perform ADL)
            if !qn.qual {
                let mark = parse_args();
                if cg_on && !dependent_ctx() {
                    // code generation: C's builtins (__builtin_alloca ...)
                    let b = cg_builtin_call(qn.name, mark, loc);
                    if b != 0 { nscratch.resize(mark); return b; }
                }
                nscratch.resize(mark);
                if !dependent_ctx() && diag_suppress == 0 && !adl_could_find(mark) {
                    err_at(qn.loc, str("use of undeclared identifier '", ident_text(qn.name as i64), "'"));
                }
                return opaque_node(loc);
            }
        }
        let ec = enclosing_class(cur_scope);
        if ec >= 0 && (has_dep_base(ec) || scopes[ec].flags & SCF_PATTERN != 0) { return opaque_node(loc); }
        if dependent_ctx() || diag_suppress > 0 || lenient > 0 { return opaque_node(loc); }
        if qn.scope >= 0 && (scopes[qn.scope].flags & SCF_PATTERN != 0 || has_dep_base(qn.scope as i64)) { return opaque_node(loc); }
        err_at(qn.loc, str("use of undeclared identifier '", ident_text(qn.name as i64), "'"));
        return opaque_node(loc);
    }
    // a type: a functional cast
    let ts = chain_type(s0);
    let first = resolve(first_visible(s0));
    if ts >= 0 && (first == ts || first < 0 || (syms[first].kind as i64 != SK_VAR && syms[first].kind as i64 != SK_FUNC && syms[first].kind as i64 != SK_FIELD && syms[first].kind as i64 != SK_ENUMC)) {
        let tk0 = syms[ts].kind as i64;
        if tk0 != SK_TEMPLATE || tmpl_kind(ts) == TT_CLASS || tmpl_kind(ts) == TT_ALIAS || tmpl_kind(ts) == TT_PARAM {
            var t = qn_type(qn);
            if t == 0 { t = t_unknown; }
            if at(TK_L_PAREN) || at(TK_L_BRACE) { return parse_functional_cast(t, loc); }
            // a type where an expression was expected (sizeof T handled earlier)
            return dep_node(t, loc);
        }
    }
    return mk_name_ref(qn, s0, loc);
}

// D1 does not perform argument-dependent lookup; an unqualified call whose
// arguments have class (or enum, or opaque) types may name a function ADL
// finds, so no error is given for it.
fn adl_could_find(mark: i64) -> bool {
    for i in mark..nscratch.len {
        let t = nodes[nscratch[i]].ty;
        if is_opq(nscratch[i]) || is_record(t) || kind_of(t) == TY_ENUM || is_opaque(t) { return true; }
        if is_pointer(t) && (is_record(tbase(t)) || kind_of(tbase(t)) == TY_ENUM) { return true; }
    }
    return true;
}
