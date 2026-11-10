// goosecc D1: C++ statements and function bodies. The nodes are C's
// (ast.goose 6.4) plus try/catch; a declaration-statement is told from an
// expression-statement as C++ [stmt.ambig] says: what can be a
// declaration is one (decided by a tentative look at the tokens).

namespace cx;

import std;
import dictionary;
import .common;
import .types;
import .ast;
import .sema;
import .pp;
import .expr;
import .parse;
import .cx_core;
import .cx_names;
import .cx_decl;
import .cx_class;
import .cx_tmpl;
import .cx_decl2;
import .cx_expr;
import .cx_sema;
import .cx_over;

let N_TRY = 82;         // a = the compound statement, v/c = the handlers (N_CATCH)
let N_CATCH = 83;       // a = the exception variable (0: catch(...)), b = the handler, ty = the caught type
let N_RANGEFOR = 84;    // range-based for (D1: parsed, not lowered): a = range, b = body, c = loop variable

var ret_type: u32 = 0;      // the return type of the function being parsed

// Does a declaration start at pc (vs. an expression)?
recursive fn stmt_is_decl() -> bool {
    let k = tk();
    if k >= TK_KW {
        let w = k - TK_KW;
        if w == KW_TYPEDEF || w == KW_EXTERN || w == KW_STATIC || w == KW_REGISTER || w == KW_THREAD_LOCAL ||
           w == KW_INLINE || w == KW_STATIC_ASSERT || w == KW_USING || w == KW_NAMESPACE || w == KW_CONSTEXPR ||
           w == KW_FRIEND || w == KW_MUTABLE || w == KW_AUTO_TYPE || w == KW_TEMPLATE || w == KW_CONSTINIT ||
           w == KW_CONSTEVAL { return true; }
        if w == KW_STRUCT || w == KW_CLASS || w == KW_UNION || w == KW_ENUM { return true; }
        if w == KW_ATTRIBUTE || w == KW_ALIGNAS { return true; }
        if w == KW_EXTENSION { let sv = save(); adv(); let r = stmt_is_decl(); restore(sv); return r; }
        if w == KW_TYPEOF || w == KW_TYPEOF_UNQUAL || w == KW_TTRANS || w == KW_ATOMIC { return decl_after_name(); }
        if w == KW_TYPENAME || w == KW_DECLTYPE || is_type_kw(w) {
            // int x; vs. int(3); unsigned(x) + 1; decltype(x)::y z;
            if tk_n(1) == TK_L_PAREN && (w != KW_DECLTYPE && w != KW_TYPENAME) {
                return decl_after_type_paren();
            }
            if w == KW_DECLTYPE || w == KW_TYPENAME { return decl_after_name(); }
            return true;
        }
        return false;
    }
    if k == TK_L_SQUARE && tk_n(1) == TK_L_SQUARE { return true; }
    if k != TK_IDENT && k != TK_COLONCOLON { return false; }
    if k == TK_IDENT && tk_n(1) == TK_COLON { return false; }
    return decl_after_name();
}

// At a name: is it a type followed by a declarator?
recursive fn decl_after_name() -> bool {
    let sv = save();
    var ds = CDS { .. };
    var a = Attrs { .. };
    diag_suppress++;
    parse_cds(ds, a, DC_BLOCK);
    diag_suppress--;
    var r = false;
    if cds_has_type(ds) {
        r = declarator_follows();
    }
    restore(sv);
    return r;
}

// After decl-specifiers: does a declarator (or ';') follow? T(x) is a
// declaration; T(x).y, T(a, b) and T(1) are expressions.
recursive fn declarator_follows() -> bool {
    let k = tk();
    if k == TK_IDENT || k == TK_KW + KW_OPERATOR { return true; }
    if k == TK_SEMI { return true; }
    if k == TK_STAR || k == TK_AMP || k == TK_AMPAMP {
        // T * x vs. a * b: T is a type here, so a declaration
        return true;
    }
    if k == TK_COLONCOLON { return true; }
    if k == TK_L_SQUARE { return true; }    // auto [a, b] = ...
    if k == TK_L_PAREN {
        // T(x); T(*p); T(x)[3]; vs T(1); T(x).f(); T(a, b);
        let sv = save();
        adv();
        var depth = 1;
        var ok = true;
        // a parenthesized declarator: ptr-ops, then a name or a nested group
        while at(TK_STAR) || at(TK_AMP) || at(TK_AMPAMP) || at_kw(KW_CONST) || at_kw(KW_VOLATILE) { adv(); }
        // a member pointer declarator: ( C :: * name ), ( N :: C :: * name )
        if at(TK_IDENT) && tk_n(1) == TK_COLONCOLON {
            let sv2 = save();
            while at(TK_IDENT) && tk_n(1) == TK_COLONCOLON { adv(); adv(); }
            if at(TK_STAR) {
                adv();
                while at_kw(KW_CONST) || at_kw(KW_VOLATILE) { adv(); }
                if at(TK_IDENT) && tk_n(1) == TK_R_PAREN { restore(sv); return true; }
            }
            restore(sv2);
        }
        if at(TK_IDENT) && tk_n(1) != TK_COLONCOLON {
            adv();
            while at(TK_L_SQUARE) { skip_group(); }
            if at(TK_L_PAREN) { skip_group(); }
            ok = at(TK_R_PAREN);
        } else if at(TK_L_PAREN) {
            skip_group();
            ok = at(TK_R_PAREN);
        } else {
            ok = false;
        }
        if ok {
            adv();
            let k2 = tk();
            ok = k2 == TK_SEMI || k2 == TK_EQUAL || k2 == TK_COMMA || k2 == TK_L_SQUARE || k2 == TK_L_PAREN || k2 == TK_L_BRACE;
            if k2 == TK_L_PAREN {
                // T(f)(args): a function declaration, or a call of T(f)?
                ok = true;
            }
        }
        restore(sv);
        return ok;
    }
    return false;
}

// int(...) at the start of a statement: a declaration int(x); or a
// functional cast int(3) + 1;
recursive fn decl_after_type_paren() -> bool {
    let sv = save();
    adv();
    let r = declarator_follows();
    restore(sv);
    return r;
}

// ---------------------------------------------------------------------------
// Statements.

recursive fn parse_compound_cx() -> u32 {
    let loc = tloc();
    expect(TK_L_BRACE, "'{'");
    push_scope();
    let um = blk_using.len;
    let mark = nscratch.len;
    while !at(TK_R_BRACE) && !at(TK_EOF) {
        let before = pc;
        parse_block_item();
        if pc == before { adv(); }
    }
    let rloc = tloc();
    expect(TK_R_BRACE, "'}'");
    blk_using.resize(um);
    pop_scope();
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    return node_v(N_COMPOUND, 0, 0, 0, rloc as i64, count, loc, start);
}

recursive fn parse_block_item() {
    if at_kw(KW_LABEL) {
        adv();
        loop {
            if at(TK_IDENT) { let ls = label_ref(tu_toks[pc].val, tloc()); adv(); }
            if !accept(TK_COMMA) { break; }
        }
        expect(TK_SEMI, "';'");
        return;
    }
    if stmt_is_decl() {
        parse_decl_cx(DC_BLOCK);
        return;
    }
    let s = parse_stmt_cx();
    nscratch.push(s);
}

// A condition: an expression, or a declaration with an initializer
// (if (T x = e)). Pushes declarations to nscratch; returns the condition
// converted to bool.
recursive fn parse_condition() -> u32 {
    let loc = tloc();
    if stmt_is_decl() {
        var a = Attrs { .. };
        var ds = CDS { .. };
        parse_cds(ds, a, DC_COND);
        var base = finish_cds(ds);
        if base == 0 { base = t_int; }
        var d = CD { .. };
        parse_cdeclr(base, 0, d);
        let s = declare_var(d, ds, a, DC_COND);
        parse_var_init(s, d, DC_COND);
        let r = node(N_DECLREF, 0, nonref(syms[s].ty), s, 0, 0, loc);
        nodes[r].flags = NF_LVALUE;
        if is_opaque(syms[s].ty) { nodes[r].flags = nodes[r].flags | NF_DEP; }
        return cond_cx(r);
    }
    let e = parse_expr_cx();
    return cond_cx(e);
}

recursive fn parse_stmt_cx() -> u32 {
    let loc = tloc();
    let k = tk();
    if k == TK_L_BRACE { return parse_compound_cx(); }
    if k == TK_SEMI { adv(); return node(N_NULL, 0, 0, 0, 0, 0, loc); }
    if k == TK_IDENT && tk_n(1) == TK_COLON {
        let name = tu_toks[pc].val;
        adv();
        adv();
        let l = label_ref(name, loc);
        syms[l].flags = syms[l].flags | SF_DEFINED;
        syms[l].loc = loc;
        var la = Attrs { .. };
        cx_attrs(la);
        if at(TK_R_BRACE) {
            let ns = node(N_NULL, 0, 0, 0, 0, 0, loc);
            return node(N_LABEL, 0, 0, l, ns as i64, 0, loc);
        }
        if stmt_is_decl() {
            let st = node(N_NULL, 0, 0, 0, 0, 0, loc);
            nscratch.push(node(N_LABEL, 0, 0, l, st as i64, 0, loc));
            parse_decl_cx(DC_BLOCK);
            return node(N_NULL, 0, 0, 0, 0, 0, loc);
        }
        let st = parse_stmt_cx();
        return node(N_LABEL, 0, 0, l, st as i64, 0, loc);
    }
    if k == TK_L_SQUARE && tk_n(1) == TK_L_SQUARE {
        var a = Attrs { .. };
        cx_attrs(a);
        if accept(TK_SEMI) { return node(N_NULL, 0, 0, 0, 0, 0, loc); }
        return parse_stmt_cx();
    }
    if k < TK_KW || stmt_is_decl() {
        if stmt_is_decl() {
            let mark = nscratch.len;
            parse_decl_cx(DC_BLOCK);
            let count = nscratch.len - mark;
            let start = commit_list(mark);
            return node_v(N_COMPOUND, 0, 0, 0, 0, count, loc, start);
        }
        let e = parse_expr_cx();
        expect(TK_SEMI, "';' after expression");
        return node(N_EXPR, 0, 0, discard_cx(e) as i64, 0, 0, loc);
    }
    let w = k - TK_KW;
    if w == KW_IF {
        adv();
        if at_kw(KW_CONSTEXPR) { adv(); }
        if at(TK_EXCLAIM) && tk_n(1) == TK_KW + KW_CONSTEVAL { adv(); }
        if at_kw(KW_CONSTEVAL) {
            // if consteval { } else { }: the else branch at run time
            adv();
            let t = parse_stmt_cx();
            var e: u32 = 0;
            if accept_kw(KW_ELSE) { e = parse_stmt_cx(); }
            return node(N_IF, 0, 0, int_node(0, t_bool, loc) as i64, t as i64, e as i64, loc);
        }
        expect(TK_L_PAREN, "'('");
        push_scope();
        let mark = nscratch.len;
        let init = parse_init_stmt();
        let c = parse_condition();
        expect(TK_R_PAREN, "')'");
        let t = parse_stmt_cx();
        var e: u32 = 0;
        if accept_kw(KW_ELSE) { e = parse_stmt_cx(); }
        pop_scope();
        let n = node(N_IF, 0, 0, c as i64, t as i64, e as i64, loc);
        return wrap_decls(mark, n, loc);
    }
    if w == KW_WHILE {
        adv();
        expect(TK_L_PAREN, "'('");
        push_scope();
        let mark = nscratch.len;
        let c = parse_condition();
        expect(TK_R_PAREN, "')'");
        loop_depth++;
        break_depth++;
        let b = parse_stmt_cx();
        loop_depth--;
        break_depth--;
        pop_scope();
        let n = node(N_WHILE, 0, 0, c as i64, b as i64, 0, loc);
        return wrap_decls(mark, n, loc);
    }
    if w == KW_DO {
        adv();
        loop_depth++;
        break_depth++;
        let b = parse_stmt_cx();
        loop_depth--;
        break_depth--;
        if !accept_kw(KW_WHILE) { perr_expected("'while'"); return b; }
        expect(TK_L_PAREN, "'('");
        let c = cond_cx(parse_expr_cx());
        expect(TK_R_PAREN, "')'");
        expect(TK_SEMI, "';'");
        return node(N_DO, 0, 0, b as i64, c as i64, 0, loc);
    }
    if w == KW_FOR { return parse_for(); }
    if w == KW_SWITCH {
        adv();
        expect(TK_L_PAREN, "'('");
        push_scope();
        let mark0 = nscratch.len;
        let init = parse_init_stmt();
        var c: u32 = 0;
        if stmt_is_decl() {
            let cc = parse_condition();
            // parse_condition converted to bool: switch wants the value
            c = cc;
        } else {
            c = parse_expr_cx();
        }
        expect(TK_R_PAREN, "')'");
        var cv = c;
        if !is_opq(c) {
            let r = rv(c);
            if is_integer(nodes[r].ty) { cv = promote(r); } else { cv = r; }
        }
        let mark = switch_cases.len;
        switches.push(SwitchCtx { ty: nodes[cv].ty, mark: mark as! u32, dflt: false });
        break_depth++;
        let b = parse_stmt_cx();
        break_depth--;
        switches.pop();
        let count = switch_cases.len - mark;
        let start = nlist.len;
        for j in mark..switch_cases.len { nlist.push(switch_cases[j]); }
        switch_cases.resize(mark);
        pop_scope();
        let n = node_v(N_SWITCH, 0, 0, cv as i64, b as i64, count, loc, start);
        return wrap_decls(mark0, n, loc);
    }
    if w == KW_CASE {
        adv();
        let e = parse_cexpr();
        var hn: u32 = 0;
        if accept(TK_ELLIPSIS) {
            let e2 = parse_cexpr();
            let ok2, v2 = const_int(e2);
            hn = int_node(v2, t_int, loc);
        }
        expect(TK_COLON, "':' after 'case'");
        let ok, v0 = const_int(e);
        var st = t_int;
        if switches.len > 0 { st = switches[switches.len - 1].ty; }
        let v = if is_integer(st) { trunc_to(v0, st) } else { v0 };
        if hn != 0 && is_integer(st) { nodes[hn].ty = st; nodes[hn].v = trunc_to(nodes[hn].v, st); }
        let wide = is_integer(st) && type_size(st) > 8;
        let cn = node_v(N_CASE, 0, st, 0, if wide && !is_opq(e) { convert(rv(e), st) as i64 } else { 0 }, hn as i64, loc, v);
        if !ok { nodes[cn].flags = NF_DEP; }
        switch_cases.push(cn);
        let s = if at(TK_R_BRACE) { node(N_NULL, 0, 0, 0, 0, 0, loc) } else { parse_stmt_cx() };
        nodes[cn].a = s;
        return cn;
    }
    if w == KW_DEFAULT {
        adv();
        expect(TK_COLON, "':' after 'default'");
        let dn = node(N_DEFAULT, 0, 0, 0, 0, 0, loc);
        if switches.len > 0 { switches[switches.len - 1].dflt = true; }
        switch_cases.push(dn);
        let s = if at(TK_R_BRACE) { node(N_NULL, 0, 0, 0, 0, 0, loc) } else { parse_stmt_cx() };
        nodes[dn].a = s;
        return dn;
    }
    if w == KW_BREAK { adv(); expect(TK_SEMI, "';'"); return node(N_BREAK, 0, 0, 0, 0, 0, loc); }
    if w == KW_CONTINUE { adv(); expect(TK_SEMI, "';'"); return node(N_CONTINUE, 0, 0, 0, 0, 0, loc); }
    if w == KW_GOTO {
        adv();
        if accept(TK_STAR) {
            let e = parse_expr_cx();
            expect(TK_SEMI, "';'");
            return node(N_IGOTO, 0, 0, (if is_opq(e) { e } else { rv(e) }) as i64, 0, 0, loc);
        }
        if !at(TK_IDENT) { perr_expected("a label"); return node(N_NULL, 0, 0, 0, 0, 0, loc); }
        let l = label_ref(tu_toks[pc].val, tloc());
        syms[l].flags = syms[l].flags | SF_LABEL_USED;
        adv();
        expect(TK_SEMI, "';'");
        return node(N_GOTO, 0, 0, l, 0, 0, loc);
    }
    if w == KW_RETURN {
        adv();
        var e: u32 = 0;
        if !at(TK_SEMI) {
            var x: u32 = 0;
            if at(TK_L_BRACE) { x = parse_braced(); } else { x = parse_expr_cx(); }
            e = return_convert(x, loc);
        }
        expect(TK_SEMI, "';'");
        return node(N_RETURN, 0, ret_type, e as i64, 0, 0, loc);
    }
    if w == KW_TRY { return parse_try(); }
    if w == KW_ASM { return parse_asm_cx(); }
    if w == KW_ATTRIBUTE {
        var a = Attrs { .. };
        cx_attrs(a);
        if accept(TK_SEMI) { return node(N_NULL, 0, 0, 0, 0, 0, loc); }
        return parse_stmt_cx();
    }
    if w == KW_CO { skip_to(TK_SEMI); expect(TK_SEMI, "';'"); return node(N_NULL, 0, 0, 0, 0, 0, loc); }
    let e = parse_expr_cx();
    expect(TK_SEMI, "';' after expression");
    return node(N_EXPR, 0, 0, discard_cx(e) as i64, 0, 0, loc);
}

fn discard_cx(e: u32) -> u32 {
    if is_opq(e) || !cish_node(e) { return e; }
    return discard_value(e);
}

// The value of a return statement converted to the function's return type.
recursive fn return_convert(x: u32, loc: u32) -> u32 {
    let rt = ret_type;
    if cg_on && rt != 0 && !is_opaque(rt) && !is_void(rt) {
        if is_ref(rt) || is_record(rt) || nodes[x].kind as i64 == N_INITBRACE { return cg_return(x, rt, loc); }
        if kind_of(rt) == TY_MEMPTR { return conv_value(x, unqual(rt), loc); }
        if !is_opq(x) && is_record(nodes[x].ty) { return conv_value(x, unqual(rt), loc); }
        if is_pointer(rt) && !is_opq(x) {
            let c = cg_ptr_conv(rv(x), unqual(rt), loc);
            if c != 0 { return c; }
        }
    }
    if is_opq(x) || rt == 0 || is_opaque(rt) || is_ref(rt) || is_record(rt) || nodes[x].kind as i64 == N_INITBRACE { return x; }
    if is_void(rt) { return x; }
    if !cish(rt) || !cish_node(x) { return x; }
    if kind_of(nodes[x].ty) == TY_NULLPTR {
        if is_pointer(rt) { return icast(x, CK_NULL2PTR, unqual(rt)); }
        return x;
    }
    return assign_convert(rv(x), rt, loc, 3);
}

// if (init; cond) / switch (init; cond): the init-statement, if any.
recursive fn parse_init_stmt() -> u32 {
    // an init-statement is followed by ';' at depth 0 before the ')'
    var j = pc;
    var depth = 0;
    var has = false;
    loop {
        let k = tu_toks[j].kind as i64;
        if k == TK_EOF { break; }
        if k == TK_L_PAREN || k == TK_L_SQUARE || k == TK_L_BRACE { depth++; }
        if k == TK_R_PAREN || k == TK_R_SQUARE || k == TK_R_BRACE {
            if depth == 0 { break; }
            depth--;
        }
        if k == TK_SEMI && depth == 0 { has = true; break; }
        j++;
    }
    if !has { return 0; }
    if stmt_is_decl() {
        parse_decl_cx(DC_BLOCK);
        return 1;
    }
    let e = parse_expr_cx();
    expect(TK_SEMI, "';'");
    nscratch.push(node(N_EXPR, 0, 0, discard_cx(e) as i64, 0, 0, tloc()));
    return 1;
}

// Declarations made in a statement's header (if, while, switch): a
// compound statement holding them and the statement.
fn wrap_decls(mark: i64, n: u32, loc: u32) -> u32 {
    if nscratch.len == mark { return n; }
    nscratch.push(n);
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    return node_v(N_COMPOUND, 0, 0, 0, 0, count, loc, start);
}

recursive fn parse_for() -> u32 {
    let loc = tloc();
    adv();      // for
    expect(TK_L_PAREN, "'('");
    push_scope();
    // a range-based for: for (decl : range)
    if range_for_ahead() {
        let mark = nscratch.len;
        var a = Attrs { .. };
        var ds = CDS { .. };
        parse_cds(ds, a, DC_COND);
        var base = finish_cds(ds);
        if base == 0 { base = t_int; }
        var d = CD { .. };
        if at(TK_L_SQUARE) {
            // structured bindings: auto [a, b] : range
            skip_group();
        } else {
            parse_cdeclr(base, 0, d);
        }
        expect(TK_COLON, "':'");
        var r: u32 = 0;
        if at(TK_L_BRACE) { r = parse_braced(); } else { r = parse_expr_cx(); }
        expect(TK_R_PAREN, "')'");
        // the loop variable: its type from the range's elements when known
        var vt = d.ty;
        if has_auto(vt) { vt = range_elem_auto(vt, r); }
        var vs: i64 = 0;
        if d.qn.name != 0 {
            vs = csym(SK_VAR, d.qn.name, vt, d.loc);
            cxs[vs].dscope = cur_scope as! i32;
            bind_sym(vs, false);
        }
        loop_depth++;
        break_depth++;
        let b = parse_stmt_cx();
        loop_depth--;
        break_depth--;
        nscratch.resize(mark);
        pop_scope();
        let n = node(N_RANGEFOR, 0, 0, r as i64, b as i64, vs, loc);
        nodes[n].flags = NF_DEP;
        return n;
    }
    let mark = nscratch.len;
    var init: u32 = 0;
    if accept(TK_SEMI) {
    } else if stmt_is_decl() {
        parse_decl_cx(DC_BLOCK);
        let count = nscratch.len - mark;
        let start = commit_list(mark);
        init = node_v(N_COMPOUND, 0, 0, 0, 0, count, loc, start);
    } else {
        let e = parse_expr_cx();
        init = node(N_EXPR, 0, 0, discard_cx(e) as i64, 0, 0, loc);
        expect(TK_SEMI, "';'");
    }
    var c: u32 = 0;
    let cmark = nscratch.len;
    if !at(TK_SEMI) { c = parse_condition(); }
    let cdecls = nscratch.len - cmark;
    nscratch.resize(cmark);
    expect(TK_SEMI, "';'");
    var inc: u32 = 0;
    if !at(TK_R_PAREN) { inc = discard_cx(parse_expr_cx()); }
    expect(TK_R_PAREN, "')'");
    loop_depth++;
    break_depth++;
    let b = parse_stmt_cx();
    loop_depth--;
    break_depth--;
    pop_scope();
    let n = node_v(N_FOR, 0, 0, init as i64, c as i64, inc as i64, loc, b as i64);
    if cdecls > 0 { nodes[n].flags = NF_DEP; }
    return n;
}

// Is the for-statement's header `decl : range`?
fn range_for_ahead() -> bool {
    var j = pc;
    var depth = 0;
    loop {
        let k = tk_at(j);
        if k == TK_EOF || k == TK_SEMI { return false; }
        if k == TK_L_PAREN || k == TK_L_SQUARE || k == TK_L_BRACE { depth++; }
        if k == TK_R_PAREN || k == TK_R_SQUARE || k == TK_R_BRACE {
            if depth == 0 { return false; }
            depth--;
        }
        if k == TK_COLON && depth == 0 { return true; }
        if k == TK_QUESTION { return false; }
        j++;
    }
}

// The type of `auto x : range` for an array range.
fn range_elem_auto(t: u32, r: u32) -> u32 {
    if is_opq(r) { return t_unknown; }
    let rt = nodes[r].ty;
    if !is_array(rt) { return t_unknown; }
    let e = tbase(rt);
    let k = kind_of(t);
    if k == TY_AUTO { return unqual(e); }
    if k == TY_LREF && kind_of(tbase(t)) == TY_AUTO { return mk_lref(with_q(e, quals(tbase(t)))); }
    if k == TY_RREF { return mk_lref(e); }
    return t_unknown;
}

recursive fn parse_try() -> u32 {
    let loc = tloc();
    adv();      // try
    let body = parse_compound_cx();
    let mark = nscratch.len;
    while at_kw(KW_CATCH) {
        let hloc = tloc();
        adv();
        expect(TK_L_PAREN, "'('");
        push_scope();
        var vs: i64 = 0;
        var ct: u32 = 0;
        if accept(TK_ELLIPSIS) {
            vs = 0;
        } else {
            var a = Attrs { .. };
            var ds = CDS { .. };
            parse_cds(ds, a, DC_PARAM);
            var base = finish_cds(ds);
            if base == 0 { base = t_int; }
            var d = CD { .. };
            parse_cdeclr(base, 2, d);
            ct = d.ty;
            if d.qn.name != 0 {
                vs = csym(SK_VAR, d.qn.name, d.ty, d.loc);
                cxs[vs].dscope = cur_scope as! i32;
                bind_sym(vs, false);
            }
        }
        expect(TK_R_PAREN, "')'");
        let h = parse_compound_cx();
        pop_scope();
        if cg_on { nscratch.push(cg_catch(vs, ct, h, hloc, false)); continue; }
        nscratch.push(node(N_CATCH, 0, ct, vs, h as i64, 0, hloc));
    }
    if cg_on { return cg_try(body, mark, loc); }
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    return node_v(N_TRY, 0, 0, body as i64, 0, count, loc, start);
}

// asm statements: parsed for their syntax (D1 does not lower them in C++).
recursive fn parse_asm_cx() -> u32 {
    let loc = tloc();
    adv();
    while at_kw(KW_VOLATILE) || at_kw(KW_INLINE) || at_kw(KW_GOTO) { adv(); }
    if at(TK_L_PAREN) { skip_group(); }
    expect(TK_SEMI, "';'");
    let n = node(N_ASM, 2, 0, 0, 0, 0, loc);
    nodes[n].flags = NF_DEP;
    return n;
}

// ({ ... }): a GNU statement expression.
recursive fn parse_stmt_expr_body() -> u32 {
    let loc = tloc();
    let body = parse_compound_cx();
    // the value: the last statement's expression
    let c = nodes[body].c as i64;
    var ty = t_void;
    var dep = false;
    if c > 0 {
        let last = nlist[nodes[body].v + c - 1];
        if nodes[last].kind as i64 == N_EXPR {
            let e = nodes[last].a;
            ty = nodes[e].ty;
            if is_opq(e) { dep = true; }
            if !dep && is_lvalue(e) && cish_node(e) { nodes[last].a = rv(e); ty = nodes[nodes[last].a].ty; }
        }
    }
    if cg_on && !dep && c > 0 && is_record(ty) && !is_opaque(ty) && class_trivial_copy(rec_of(ty)) {
        // code generation: a class value
        let last = nlist[nodes[body].v + c - 1];
        let v = conv_value(nodes[last].a, unqual(ty), loc);
        if !is_opq(v) {
            nodes[last].a = v;
            return node(N_STMTEXPR, 0, unqual(ty), body as i64, 0, 0, loc);
        }
    }
    if dep || !cish(ty) && !is_void(ty) { return dep_node(ty, loc); }
    return node(N_STMTEXPR, 0, ty, body as i64, 0, 0, loc);
}

// ---------------------------------------------------------------------------
// Function bodies.

// Parses the body of function s at pc (ctor-initializers, the compound
// statement, a function-try-block): its N_FUNCDEF.
recursive fn parse_function_body(s: i64, params: i64, nparams: i64) -> u32 {
    let loc = syms[s].loc;
    let sv_func = cur_func_cx;
    let sv_this = this_type;
    let sv_ret = ret_type;
    let sv_cfunc = cur_func;
    let sv_ld = loop_depth;
    let sv_bd = break_depth;
    let sv_class = cur_class;
    cur_func_cx = s;
    cur_func = s;
    func_gen++;
    loop_depth = 0;
    break_depth = 0;
    cur_class = -1;
    ret_type = types[syms[s].ty >> 4].base;
    let member = cxs[s].flags & CF_MEMBER != 0 && cxs[s].flags & CF_STATIC == 0;
    this_type = 0;
    let sv_cgthis = cg_this;
    cg_this = -1;
    let sv_cgret = cg_ret;
    cg_ret = -1;
    if cg_on && pass_indirect(ret_type) { cg_ret = make_ret(s, ret_type, loc); }
    if member {
        let sc = cxs[s].dscope as i64;
        let ct = scope_class_type(sc);
        if ct != 0 {
            var q = 0;
            if cxs[s].flags & CF_CONST != 0 { q = Q_CONST; }
            this_type = mk_ptr(with_q(ct, q));
            if cg_on { cg_this = make_this(s, this_type, loc); }
        }
    }
    let lmark = label_syms.len;
    block_fn_depth++;
    push_scope();
    bind_params(params, nparams);
    var is_try = false;
    if at_kw(KW_TRY) { adv(); is_try = true; }
    var inits: u32 = 0;
    if at(TK_COLON) { inits = parse_ctor_inits(s); }
    var body: u32 = 0;
    if at(TK_L_BRACE) { body = parse_compound_cx(); }
    else { perr_expected("a function body"); }
    var hmark: i64 = -1;
    var tmark: i64 = -1;
    if is_try {
        let mark = nscratch.len;
        tmark = mark;
        let structor = cxs[s].flags & (CF_CTOR | CF_DTOR) != 0;
        while at_kw(KW_CATCH) {
            let hloc = tloc();
            adv();
            expect(TK_L_PAREN, "'('");
            push_scope();
            var vs: i64 = 0;
            var ct: u32 = 0;
            if accept(TK_ELLIPSIS) {} else {
                var a = Attrs { .. };
                var ds = CDS { .. };
                parse_cds(ds, a, DC_PARAM);
                var base = finish_cds(ds);
                if base == 0 { base = t_int; }
                var d = CD { .. };
                parse_cdeclr(base, 2, d);
                ct = d.ty;
                if d.qn.name != 0 {
                    vs = csym(SK_VAR, d.qn.name, d.ty, d.loc);
                    cxs[vs].dscope = cur_scope as! i32;
                    bind_sym(vs, false);
                }
            }
            expect(TK_R_PAREN, "')'");
            let h = parse_compound_cx();
            pop_scope();
            if cg_on { nscratch.push(cg_catch(vs, ct, h, hloc, structor)); continue; }
            nscratch.push(node(N_CATCH, 0, 0, 0, h as i64, 0, hloc));
        }
        if cg_on { hmark = mark; }
    }
    if is_try && !cg_on {
        let mark = tmark;
        let count = nscratch.len - mark;
        let start = commit_list(mark);
        let t = node_v(N_TRY, 0, 0, body as i64, 0, count, loc, start);
        let bm = nscratch.len;
        nscratch.push(t);
        let bstart = commit_list(bm);
        body = node_v(N_COMPOUND, 0, 0, 0, 0, 1, loc, bstart);
    }
    if cg_on && (cg_this >= 0 || hmark >= 0) && body != 0 { body = cg_wrap_body_try(s, body, inits, loc, hmark); }
    cg_this = sv_cgthis;
    cg_ret = sv_cgret;
    pop_scope();
    block_fn_depth--;
    for j in lmark..label_syms.len {
        let l = label_syms[j] as i64;
        if syms[l].flags & SF_DEFINED == 0 && diag_suppress == 0 {
            err_at(syms[l].loc, str("use of undeclared label '", ident_text(syms[l].name as i64), "'"));
        }
    }
    label_syms.resize(lmark);
    cur_func_cx = sv_func;
    this_type = sv_this;
    ret_type = sv_ret;
    cur_func = sv_cfunc;
    loop_depth = sv_ld;
    break_depth = sv_bd;
    cur_class = sv_class;
    let n = node_v(N_FUNCDEF, 0, syms[s].ty, s, body as i64, nparams, loc, params);
    nodes[n].c = nparams as! u32;
    syms[s].def = n as! i32;
    ctor_inits.insert(s as u64, inits);
    return n;
}
var ctor_inits = dictionary<u64, u32> {};   // constructor -> its mem-initializers (an N_INITBRACE-like list, 0 none)

// : mem-initializer-list. Each is (member or base) ( args ) / { args }:
// a list of N_CXX nodes (a = the member symbol or base type, v/c = args).
recursive fn parse_ctor_inits(s: i64) -> u32 {
    adv();      // :
    let mark = nscratch.len;
    loop {
        let loc = tloc();
        var target: i64 = -1;
        var bt: u32 = 0;
        if at_kw(KW_DECLTYPE) { bt = parse_decltype(); }
        else {
            var qn = QN { .. };
            if !parse_qname(qn) { perr_expected("a member or base name"); break; }
            // a member's name is looked up in the class (before the
            // parameters, which may have the same name)
            var ms: i64 = -1;
            if !qn.qual && qn.kind as i64 == QK_IDENT && !qn.has_targs && cxs[s].dscope >= 0 {
                var m = scope_find(cxs[s].dscope as i64, qn.name);
                while m >= 0 && syms[m].kind as i64 != SK_FIELD { m = cxs[m].nnext as i64; }
                ms = m;
            }
            if ms >= 0 { target = ms; }
            else {
                lookup_qn(qn);
                let t = qn_type(qn);
                if t != 0 { bt = t; }
                else if qn.sym >= 0 { target = resolve(qn.sym as i64); }
            }
        }
        var args: u32 = 0;
        if at(TK_L_PAREN) {
            let am = parse_args();
            let count = nscratch.len - am;
            let st = commit_list(am);
            args = node_v(N_INITBRACE, 0, t_unknown, 0, 0, count, loc, st);
            nodes[args].op = 1;
        } else if at(TK_L_BRACE) {
            args = parse_braced();
        } else {
            perr_expected("'(' or '{'");
            break;
        }
        accept(TK_ELLIPSIS);
        let n = node(N_CXX, 1, bt, target, args as i64, 0, loc);
        nscratch.push(n);
        if !accept(TK_COMMA) { break; }
    }
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    return node_v(N_INITBRACE, 2, 0, 0, 0, count, 0, start);
}

// A deferred member function body (after its class is complete).
recursive fn parse_member_body(s: i64, sc: i64) {
    if cxs[s].body == 0 { return; }
    let sv = save();
    let sv_scope = cur_scope;
    let sv_floor = local_floor;
    cur_scope = sc;
    // a friend function defined in a class is a namespace member whose
    // body sees the class scope
    pc = cxs[s].body as i64;
    gt_pos = -1;
    let st, n = fn_param_list(s);
    if inst_debug() { write_stderr(str("member_body ", s, " st=", st, " n=", n, " p0=", if n > 0 { nlist[st] as i64 } else { -1 }, " name=", if n > 0 { syms[nlist[st] as i64].name as i64 } else { -1 }, "\n")); }
    let f = parse_function_body(s, if st < 0 { 0 } else { st }, if st < 0 { 0 } else { n });
    if f != 0 {
        if block_fn_depth > 0 { fdefs_extra.push(f); } else { nscratch.push(f); }
    }
    cxs[s].flags = cxs[s].flags & ~CF_HAS_BODY_LATER;
    cur_scope = sv_scope;
    local_floor = sv_floor;
    restore(sv);
}
