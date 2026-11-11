// goosecc D2b: C++20 concepts and constraints (C++ [temp.constr],
// [expr.prim.req]).
//
// A concept is a template (TT_CONCEPT) whose tokens [t0, t1) are its
// constraint-expression. Constraints are kept as tokens too, like
// everything else a template holds: a template's requires-clause
// (tmpl_req), the type-constraints of its parameters (tparam_tc), a
// function's trailing requires-clause. Checking satisfaction means parsing
// those tokens again with the template parameters bound (subst_parse, what
// 3), in a mode that follows [temp.constr.op]: the operands of && and ||
// are evaluated one at a time, left to right, with short-circuiting (the
// operand skipped is never substituted: its end is known from the first,
// dependent parse, cons_end), and an atomic constraint whose substitution
// fails (errors at its own suppression level) is not satisfied rather than
// an error. A requires-expression of a template is likewise false when one
// of its requirements fails to substitute; outside templates its errors
// are errors (clang).
//
// Values are three-valued plus one: 1 satisfied, 0 not, -1 not known
// (something D2b does not compute: never guessed), -2 not evaluated (a
// dependent context).

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
import .cx_inst;

let TT_CONCEPT = 6;

var tmpl_req = dictionary<u64, u32> {};     // template record -> the first token of its requires-clause's expression
var tparam_tc = dictionary<u64, u32> {};    // template parameter (tps index) -> its type-constraint's first token
var cons_end = dictionary<u64, u32> {};     // the first token of a constraint operand -> the token after it
var req_tmpl = dictionary<u64, u32> {};     // a requires-expression (its `requires` token) first parsed in a template
var concept_cache = dictionary<u64, i32> {};    // (concept << 32 | arguments) -> 1, 0, -1 (unknown or being evaluated)
var fn_req = dictionary<u64, u32> {};       // a member function of an instantiated class -> its trailing requires-clause
var fn_req_val = dictionary<u64, i32> {};   // ... its satisfaction, once checked
var trail_req: i64 = 1;         // the trailing requires-clause of the declaration being parsed again (fspec_decl)
var trail_req_pos: i64 = 0;     // parse_simple_decl: the trailing requires-clause just parsed (0 none)
var cons_depth: i64 = 0;

fn cons_or3(v: i64, w: i64) -> i64 {
    if v == 1 || w == 1 { return 1; }
    if v == -2 || w == -2 { return -2; }
    if v == -1 || w == -1 { return -1; }
    return 0;
}
fn cons_and3(v: i64, w: i64) -> i64 {
    if v == 0 || w == 0 { return 0; }
    if v == -2 || w == -2 { return -2; }
    if v == -1 || w == -1 { return -1; }
    return 1;
}

// (keyed by token * 4 + level: 0 an operand, 1 a conjunction, 2 a disjunction,
// which may all start at the same token)
fn cons_note_end(p0: i64, lvl: i64) {
    let k = (p0 * 4 + lvl) as u64;
    if !cons_end.contains(k) { cons_end.insert(k, pc as! u32); }
}

// Skips the operand starting at pc when its end is known.
fn cons_skip(lvl: i64) -> bool {
    let g = cons_end.get((pc * 4 + lvl) as u64);
    if !g { return false; }
    var e: u32 = 0;
    e = g;
    pc = e as i64;
    gt_pos = -1;
    return true;
}

// constraint-logical-or-expression (clause: a requires-clause, whose
// operands are primary expressions; else a concept's constraint-expression).
recursive fn cons_or(clause: bool) -> i64 {
    let p0 = pc;
    var v = cons_and(clause);
    while at(TK_PIPEPIPE) {
        adv();
        if v == 1 && cons_skip(1) { continue; }
        let w = cons_and(clause);
        v = cons_or3(v, w);
    }
    cons_note_end(p0, 2);
    return v;
}

recursive fn cons_and(clause: bool) -> i64 {
    let p0 = pc;
    var v = cons_atom(clause);
    while at(TK_AMPAMP) {
        adv();
        if v == 0 && cons_skip(0) { continue; }
        let w = cons_atom(clause);
        v = cons_and3(v, w);
    }
    cons_note_end(p0, 1);
    return v;
}

// An operand: a parenthesized constraint (its && and || are part of the
// normal form) or an atomic constraint.
recursive fn cons_atom(clause: bool) -> i64 {
    let p0 = pc;
    var v: i64 = -2;
    if at(TK_L_PAREN) && cons_paren_group(clause) {
        adv();
        let sp = paren_depth;
        paren_depth++;
        v = cons_or(false);
        paren_depth = sp;
        expect(TK_R_PAREN, "')'");
    } else {
        v = cons_atomic(clause);
    }
    cons_note_end(p0, 0);
    return v;
}

// At '(': is the parenthesized group a constraint of its own (followed by
// && || or the end), not the start of a larger atomic expression? A fold
// expression is atomic.
fn cons_paren_group(clause: bool) -> bool {
    var j = pc;
    var d = 0;
    loop {
        let k = tk_at(j);
        if k == TK_EOF { return false; }
        if k == TK_L_PAREN || k == TK_L_SQUARE || k == TK_L_BRACE { d++; }
        else if k == TK_R_PAREN || k == TK_R_SQUARE || k == TK_R_BRACE { d--; if d == 0 { break; } }
        else if (k == TK_ELLIPSIS || k == TK_QUESTION || k == TK_COMMA) && d == 1 { return false; }
        j++;
    }
    if clause { return true; }
    let n = tk_at(j + 1);
    return n == TK_AMPAMP || n == TK_PIPEPIPE || n == TK_SEMI || n == TK_R_PAREN || n == TK_EOF;
}

// An atomic constraint: substituted and evaluated; a substitution failure
// makes it unsatisfied.
recursive fn cons_atomic(clause: bool) -> i64 {
    let loc = tloc();
    if dependent_ctx() {
        let e = if clause { parse_cast_cx() } else { parse_bin(3) };
        return -2;
    }
    let wl0 = diag_watch_level;
    let we0 = diag_watch_errors;
    diag_suppress++;
    diag_watch_level = diag_suppress;
    let e = if clause { parse_cast_cx() } else { parse_bin(3) };
    diag_suppress--;
    let errs = diag_watch_errors - we0;
    diag_watch_level = wl0;
    if errs > 0 { return 0; }
    if is_opq(e) { return -1; }
    let t = unqual(nonref(nodes[e].ty));
    if kind_of(t) != TY_BOOL {
        if diag_suppress == 0 || diag_suppress == diag_inst_level {
            err_at(loc, str("atomic constraint must be of type 'bool' (found ", ctname(t), ")"));
        }
        return 0;
    }
    let ok, v = const_int(e);
    if !ok {
        if diag_suppress == 0 || diag_suppress == diag_inst_level {
            err_at(loc, "substitution into constraint expression resulted in a non-constant expression");
        }
        return -1;
    }
    return if v != 0 { 1 } else { 0 };
}

// ---------------------------------------------------------------------------
// Declarations.

// template<params> concept Name = constraint-expression ; (at `concept`;
// t is the header's record, being parsed).
recursive fn parse_concept_def(t: i64) {
    let loc = tloc();
    adv();      // concept
    if at_kw(KW_BOOLX) { adv(); }      // the Concepts TS's `concept bool`
    if !at(TK_IDENT) { perr_expected("a concept name"); skip_to(TK_SEMI); accept(TK_SEMI); return; }
    let name = tu_toks[pc].val;
    adv();
    var a = Attrs { .. };
    cx_attrs(a);
    let s = csym(SK_TEMPLATE, name, 0, loc);
    cxs[s].tmpl = t as! i32;
    cxs[s].flags = CF_TEMPLATE;
    tmpls[t].kind = TT_CONCEPT as! u8;
    tmpls[t].sym = s as! i32;
    tmpls[t].scope = cur_scope as! i32;
    scope_add(cur_scope, s);
    if !expect(TK_EQUAL, "'='") { skip_to(TK_SEMI); accept(TK_SEMI); return; }
    tmpls[t].t0 = pc as! u32;
    let v = cons_or(false);
    tmpls[t].t1 = pc as! u32;
    if !at(TK_SEMI) { perr_expected("';'"); skip_to(TK_SEMI); }
    accept(TK_SEMI);
}

// requires constraint-logical-or-expression after a template header (pc at
// `requires`): parsed (dependent), its first token returned.
recursive fn parse_requires_clause() -> i64 {
    adv();      // requires
    let p = pc;
    let v = cons_or(true);
    return p;
}

// A function declarator's trailing requires-clause (pc at `requires`;
// start/count its parameters). In a function template's specialization
// being declared (fspec_decl) it is checked now (trail_req); in a member
// of an instantiated class it is kept for overload resolution
// (trail_req_pos, fn_req).
recursive fn parse_trailing_requires(start: i64, count: i64) {
    adv();      // requires
    let p = pc;
    trail_req_pos = p;
    push_scope();
    bind_params(start, count);
    if dependent_ctx() {
        let v = cons_or(true);
    } else if inst_spec_decl {
        let v = cons_or(true);
        trail_req = cons_and3(trail_req, v);
    } else if !cons_skip(2) {
        // first seen outside a template: checked like a template's
        let v = cons_or(true);
    }
    pop_scope();
}

// The requires-clause just parsed belongs to function s.
fn note_trailing_requires(s: i64) {
    if trail_req_pos == 0 || s < 0 { trail_req_pos = 0; return; }
    if !dependent_ctx() && !inst_spec_decl { fn_req.insert(s as u64, trail_req_pos as! u32); }
    trail_req_pos = 0;
}

// Is the name at pc a concept, used as a type-constraint (C T, C<A> T,
// C... T) rather than a placeholder (C auto)?
recursive fn type_constraint_ahead() -> bool {
    if !at(TK_IDENT) && !at(TK_COLONCOLON) { return false; }
    let sv = save();
    var qn = QN { .. };
    diag_suppress++;
    let ok = parse_qname(qn);
    var r = false;
    if ok && qn.kind as i64 == QK_IDENT {
        lookup_qn(qn);
        if concept_of(qn.sym as i64) >= 0 && !at_kw(KW_AUTO) && !at_kw(KW_DECLTYPE) { r = true; }
    }
    diag_suppress--;
    restore(sv);
    return r;
}

// The concept symbol in a lookup chain, -1.
fn concept_of(s0: i64) -> i64 {
    var s = s0;
    while s >= 0 {
        let r = resolve(s);
        if r >= 0 && syms[r].kind as i64 == SK_TEMPLATE && tmpl_kind(r) == TT_CONCEPT { return r; }
        s = cxs[s].nnext as i64;
    }
    return -1;
}

// ---------------------------------------------------------------------------
// Satisfaction.

// The value of the concept-id tsym<args>.
recursive fn concept_id_node(tsym: i64, args: i32, loc: u32) -> u32 {
    let t = cxs[tsym].tmpl as i64;
    if args_dependent(args) || !concept_args_known(args) { return dep_node(t_bool, loc); }
    let v = concept_sat(t, args);
    if v == 1 || v == 0 { return int_node(v, t_bool, loc); }
    return dep_node(t_bool, loc);
}

recursive fn concept_args_known(args: i32) -> bool {
    for i in tl_count(args as i64) {
        let a = tl_arg(args as i64, i);
        let k = a.kind as i64;
        if (k == TA_TYPE || k == TA_VALUE) && (a.ty == 0 || is_opaque(a.ty)) { return false; }
        if k == TA_TEMPLATE && a.v < 0 { return false; }
        if k == TA_PACK {
            if !concept_args_known(a.v as! i32) { return false; }
        }
    }
    return true;
}

// Is concept t satisfied by args (1, 0, -1 unknown)?
recursive fn concept_sat(t: i64, args0: i32) -> i64 {
    let args = complete_args(t, args0);
    let key = ((t as u64) << 32) | (args as u64);
    let g = concept_cache.get(key);
    if g { var c: i32 = 0; c = g; return c as i64; }
    if cons_depth > 200 || tmpls[t].t1 == 0 { return -1; }
    concept_cache.insert(key, -1);
    cons_depth++;
    let u0 = subst_parse(t, args, tmpls[t].t0 as i64, 3, 0);
    cons_depth--;
    let v = if subst_ok { subst_val } else { -1 };
    concept_cache.insert(key, v as! i32);
    return v;
}

// subst_parse what 3, the bindings in place: a concept's constraint
// expression, or template t's associated constraints (its parameters'
// type-constraints, then its requires-clause).
recursive fn cons_subst_eval(t: i64, args: i32) -> i64 {
    let std0 = targ_depth;
    let spd = paren_depth;
    targ_depth = 0;
    paren_depth = 0;
    var v: i64 = 1;
    if tmpls[t].kind as i64 == TT_CONCEPT {
        v = cons_or(false);
    } else {
        let n = tmpls[t].nparams as i64;
        for i in n {
            let pi = tmpls[t].params as i64 + i;
            let g = tparam_tc.get(pi as u64);
            if !g { continue; }
            var tc: u32 = 0;
            tc = g;
            if i >= tl_count(args as i64) { v = cons_and3(v, -1); continue; }
            let w = tc_eval(tc as i64, tl_arg(args as i64, i));
            v = cons_and3(v, w);
            if v == 0 { break; }
        }
        let gr = tmpl_req.get(t as u64);
        if gr && v != 0 {
            var rp: u32 = 0;
            rp = gr;
            pc = rp as i64;
            gt_pos = -1;
            let w = cons_or(true);
            v = cons_and3(v, w);
        }
    }
    targ_depth = std0;
    paren_depth = spd;
    return v;
}

// The type-constraint at token tc (C or C<args>) applied to argument a.
recursive fn tc_eval(tc: i64, a: TArg) -> i64 {
    if a.kind as i64 == TA_PACK {
        // every element of a pack
        var v: i64 = 1;
        let l = a.v as i64;
        for j in tl_count(l) {
            v = cons_and3(v, tc_eval(tc, tl_arg(l, j)));
            if v == 0 { break; }
        }
        return v;
    }
    pc = tc;
    gt_pos = -1;
    var qn = QN { .. };
    targ_depth++;
    let ok = parse_qname(qn);
    targ_depth--;
    if !ok { return -1; }
    lookup_qn(qn);
    let cs = concept_of(qn.sym as i64);
    if cs < 0 { return -1; }
    var first = a;
    if a.kind as i64 == TA_VALUE {
        // C auto N: the constraint is on N's type
        first = TArg { kind: TA_TYPE as! u8, rsv: 0, rsv2: 0, ty: a.ty, v: 0 };
    }
    return concept_with_first(cs, first, if qn.has_targs { qn.targs } else { -1 });
}

// C<first, rest...>.
recursive fn concept_with_first(cs: i64, first: TArg, rest: i32) -> i64 {
    let mark = targ_scratch.len;
    targ_scratch.push(first);
    for j in tl_count(rest as i64) { targ_scratch.push(tl_arg(rest as i64, j)); }
    let l = targ_intern(mark);
    if args_dependent(l) || !concept_args_known(l) { return -2; }
    return concept_sat(cxs[cs].tmpl as i64, l);
}

// Are template t's associated constraints satisfied by binds (one argument
// per parameter)? 1 when it has none.
recursive fn tmpl_satisfied(t: i64, binds: i32) -> i64 {
    if !tmpl_constrained(t) { return 1; }
    if !concept_args_known(binds) { return -1; }
    cons_depth++;
    let u0 = subst_parse(t, binds, tmpls[t].pos as i64, 3, 0);
    cons_depth--;
    if !subst_ok { return -1; }
    return subst_val;
}

fn tmpl_constrained(t: i64) -> bool {
    if tmpl_req.contains(t as u64) { return true; }
    for i in tmpls[t].nparams as i64 {
        if tparam_tc.contains((tmpls[t].params as i64 + i) as u64) { return true; }
    }
    return false;
}

// A member function of an instantiated class with a trailing
// requires-clause: is it satisfied (overload resolution)?
recursive fn fn_req_ok(f: i64) -> i64 {
    let g = fn_req.get(f as u64);
    if !g { return 1; }
    let gv = fn_req_val.get(f as u64);
    if gv { var c: i32 = 0; c = gv; return c as i64; }
    var p: u32 = 0;
    p = g;
    fn_req_val.insert(f as u64, -1);
    let sc = cxs[f].dscope as i64;
    let st = inst_enter(false);
    if sc >= 0 {
        cur_scope = sc;
        if scopes[sc].kind as i64 == CS_CLASS { cur_class = sc; }
    }
    pc = p as i64;
    let fp, fc = fn_param_list(f);
    if fp >= 0 { bind_params(fp, fc); }
    let v = cons_or(true);
    let bad = inst_leave(st);
    fn_req_val.insert(f as u64, v as! i32);
    return v;
}

// ---------------------------------------------------------------------------
// requires-expressions.

// requires ( parameters ) { requirements } at `requires`.
recursive fn parse_requires_expr() -> u32 {
    let loc = tloc();
    let p0 = pc;
    adv();      // requires
    let dep = dependent_ctx();
    if dep && !req_tmpl.contains(p0 as u64) { req_tmpl.insert(p0 as u64, 1); }
    let sfinae = req_tmpl.contains(p0 as u64);
    push_scope();
    if at(TK_L_PAREN) {
        var variadic = false;
        let start, count = parse_cparams(variadic);
        bind_params(start, count);
    }
    if !at(TK_L_BRACE) {
        perr_expected("'{'");
        pop_scope();
        return dep_node(t_bool, loc);
    }
    let lb = pc;
    adv();
    var v: i64 = if dep { -2 } else { 1 };
    while !at(TK_R_BRACE) && !at(TK_EOF) {
        let r = parse_requirement(dep, sfinae);
        if !dep { v = cons_and3(v, r); }
        if v == 0 {
            // the rest is not substituted
            pc = lb;
            gt_pos = -1;
            skip_group();
            pop_scope();
            return int_node(0, t_bool, loc);
        }
    }
    expect(TK_R_BRACE, "'}'");
    pop_scope();
    if v == 1 { return int_node(1, t_bool, loc); }
    return dep_node(t_bool, loc);
}

// One requirement up to and including its ';'.
recursive fn parse_requirement(dep: bool, sfinae: bool) -> i64 {
    let watch = !dep && sfinae;
    let wl0 = diag_watch_level;
    let we0 = diag_watch_errors;
    if watch {
        diag_suppress++;
        diag_watch_level = diag_suppress;
    }
    var v: i64 = if dep { -2 } else { 1 };
    if at_kw(KW_TYPENAME) {
        // a type-requirement
        let t = parse_type_id();
        if !dep && (t == 0 || is_opaque(t)) { v = -1; }
    } else if at(TK_L_BRACE) {
        // a compound requirement { e } noexcept -> type-constraint
        adv();
        unevaluated++;
        let sp = paren_depth;
        paren_depth++;
        let e = parse_cexpr_full();
        paren_depth = sp;
        unevaluated--;
        expect(TK_R_BRACE, "'}'");
        if !dep && is_opq(e) { v = -1; }
        if accept_kw(KW_NOEXCEPT) {
            if !dep && v == 1 && can_throw(e) { v = 0; }
        }
        if at(TK_ARROW) {
            adv();
            if dep || v != 1 {
                var qn = QN { .. };
                parse_qname(qn);
            } else {
                let tc = pc;
                var qn = QN { .. };
                targ_depth++;
                let ok = parse_qname(qn);
                targ_depth--;
                lookup_qn(qn);
                let cs = concept_of(qn.sym as i64);
                if !ok || cs < 0 {
                    if diag_suppress == 0 { err_at(tloc(), "expected concept name with optional arguments"); }
                    v = 0;
                } else {
                    let ty = decltype_paren(e);
                    let first = TArg { kind: TA_TYPE as! u8, rsv: 0, rsv2: 0, ty: ty, v: 0 };
                    let w = concept_with_first(cs, first, if qn.has_targs { qn.targs } else { -1 });
                    v = cons_and3(v, if w == -2 { -1 } else { w });
                }
            }
        }
    } else if at_kw(KW_REQUIRES) {
        // a nested requirement
        adv();
        let w = cons_or(false);
        if !dep { v = cons_and3(v, if w == -2 { -1 } else { w }); }
    } else {
        // a simple requirement
        unevaluated++;
        let e = parse_cexpr_full();
        unevaluated--;
        if !dep && is_opq(e) { v = -1; }
    }
    if watch {
        diag_suppress--;
        let errs = diag_watch_errors - we0;
        diag_watch_level = wl0;
        if errs > 0 { v = 0; }
    }
    if !at(TK_SEMI) {
        if !dep && v != 0 && diag_suppress == 0 { perr_expected("';'"); }
        skip_to(TK_SEMI);
    }
    accept(TK_SEMI);
    return v;
}

// decltype((e)): T& for an lvalue, T&& for an xvalue, T for a prvalue.
fn decltype_paren(e: u32) -> u32 {
    let ty = nodes[e].ty;
    if nodes[e].flags & NF_XVALUE != 0 { return mk_rref(ty); }
    if is_lvalue(e) { return mk_lref(ty); }
    return ty;
}
