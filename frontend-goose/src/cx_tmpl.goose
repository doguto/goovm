// goosecc D1: templates. Template headers and parameters, the template
// records of class, function, alias and variable templates, partial and
// explicit specializations, and what a template-id names.
//
// A template is kept as its parameters, the scope and token position of
// its definition, and the tokens of its declaration [t0, t1). Its pattern
// is parsed once, in a dependent context (tmpl_depth > 0): a class
// template's pattern is a class whose scope is marked SCF_PATTERN, a
// function template's a function whose type mentions TY_TPARAM types, and
// the bodies are not parsed (their tokens are kept). Uses of a template
// with concrete arguments: an alias template is substituted by parsing its
// type-id again with the parameters bound to the arguments; an explicit
// specialization is the class it defines; anything else is, in D1, an
// opaque specialization type (TY_DEPSPEC with concrete arguments), whose
// members are unknown and never checked (DESIGN.md 13: instantiation by
// re-parsing the pattern's tokens is stage D2).

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

var pending_tmpl: i64 = -1;     // the template record the next declaration defines, -1
var pending_explicit: bool = false;  // template<> : an explicit specialization follows
var pending_inst: bool = false;      // template X<..>; an explicit instantiation
var last_tmpl_sym: i64 = -1;
var spec_map = dictionary<u64, u32> {};   // (template record << 32 | argument list) -> the explicit specialization's type

// template-declaration, explicit specialization or explicit instantiation
// at `template` (or `extern template`).
recursive fn parse_template_decl(ctx: i64) {
    let tpos = pc;
    adv();      // template
    if !at(TK_LESS) {
        // an explicit instantiation: template class X<int>; template void f<int>(int);
        let sv_inst = pending_inst;
        pending_inst = true;
        parse_simple_decl(ctx);
        pending_inst = sv_inst;
        return;
    }
    adv();      // <
    if at_gt() {
        take_gt();
        // template<>: an explicit specialization (not a pattern)
        let sv = pending_explicit;
        pending_explicit = true;
        if at_kw(KW_TEMPLATE) { parse_template_decl(ctx); }
        else { parse_simple_decl_or_using(ctx); }
        pending_explicit = sv;
        return;
    }
    push_scope();
    tmpl_depth++;
    let first = tps.len;
    parse_tparams();
    let count = tps.len - first;
    // C++20 requires-clauses (not used by libstdc++ in C++17): skipped
    let t = tmpls.len;
    tmpls.push(Tmpl { kind: 0, depth: tmpl_depth as! u8, rsv: 0, sym: -1, params: first as! u32, nparams: count as! u32,
        scope: cur_scope as! i32, pos: tpos as! u32, t0: pc as! u32, t1: 0, pattern: -1, specs: -1, outer: -1,
        spec_args: -1, primary: -1, inst_scope: -1, def_t: -1, hdr_outer: -1, pat_t: -1 });
    let sv_pending = pending_tmpl;
    if at_kw(KW_TEMPLATE) {
        // template<...> template<...> ...: an out-of-line member template
        pending_tmpl = -1;
        parse_template_decl(ctx);
    } else {
        pending_tmpl = t;
        parse_simple_decl_or_using(ctx);
    }
    tmpls[t].t1 = pc as! u32;
    pending_tmpl = sv_pending;
    tmpl_depth--;
    pop_scope();
}

recursive fn parse_simple_decl_or_using(ctx: i64) {
    if at_kw(KW_USING) { parse_using(ctx); return; }
    if at_kw(KW_FRIEND) || (ctx == DC_CLASS && friend_after_attrs()) { parse_simple_decl(DC_FRIEND); return; }
    parse_simple_decl(ctx);
}

// template-parameter-list, up to and including the closing '>'.
recursive fn parse_tparams() {
    var index = 0;
    loop {
        if at_gt() || at(TK_EOF) { break; }
        var a = Attrs { .. };
        cx_attrs(a);
        let loc = tloc();
        var tp = TParam { kind: TPK_TYPE as! u8, pack: false, rsv: 0, name: 0, ty: 0, def0: 0, def1: 0, sym: -1 };
        if (at_kw(KW_CLASS) || at_kw(KW_TYPENAME)) && type_param_ahead() {
            adv();
            if accept(TK_ELLIPSIS) { tp.pack = true; }
            if at(TK_IDENT) { tp.name = tu_toks[pc].val; adv(); }
            let pt = mk_tparam(tmpl_depth, index, tp.name, tp.pack);
            tp.ty = pt;
            if at(TK_EQUAL) {
                adv();
                tp.def0 = pc as! u32;
                targ_depth++;
                diag_suppress++;
                let dt = parse_type_id();
                diag_suppress--;
                targ_depth--;
                tp.def1 = pc as! u32;
            }
            let s = csym(SK_TYPEDEF, tp.name, pt, loc);
            syms[s].sc = SC_TYPEDEF;
            cxs[s].flags = CF_TPARAM;
            if tp.name != 0 { bind_sym(s, false); }
            tp.sym = s as! i32;
        } else if at_kw(KW_TEMPLATE) {
            // template < ... > class name
            tp.kind = TPK_TEMPLATE as! u8;
            adv();
            if at(TK_LESS) {
                adv();
                push_scope();
                tmpl_depth++;
                let f0 = tps.len;
                parse_tparams();
                tps.resize(f0);
                tmpl_depth--;
                pop_scope();
            }
            if at_kw(KW_CLASS) || at_kw(KW_TYPENAME) { adv(); }
            if accept(TK_ELLIPSIS) { tp.pack = true; }
            if at(TK_IDENT) { tp.name = tu_toks[pc].val; adv(); }
            if at(TK_EQUAL) {
                adv();
                tp.def0 = pc as! u32;
                var qn = QN { .. };
                diag_suppress++;
                parse_qname(qn);
                diag_suppress--;
                tp.def1 = pc as! u32;
            }
            let s = csym(SK_TEMPLATE, tp.name, 0, loc);
            let tt = tmpls.len;
            tmpls.push(Tmpl { kind: TT_PARAM as! u8, depth: tmpl_depth as! u8, rsv: 0, sym: s as! i32, params: 0, nparams: 0,
                scope: cur_scope as! i32, pos: pc as! u32, t0: 0, t1: 0, pattern: -1, specs: -1, outer: -1, spec_args: -1,
                primary: -1, inst_scope: -1, def_t: -1, hdr_outer: -1, pat_t: -1 });
            cxs[s].tmpl = tt as! i32;
            cxs[s].flags = CF_TPARAM | CF_TEMPLATE;
            syms[s].v = ((tmpl_depth << 16) | index) as i64;
            if tp.name != 0 { bind_sym(s, false); }
            tp.sym = s as! i32;
        } else {
            // a non-type template parameter
            tp.kind = TPK_VALUE as! u8;
            var ds = CDS { .. };
            parse_cds(ds, a, DC_PARAM);
            var base = finish_cds(ds);
            if base == 0 { base = t_int; }
            var d = CD { .. };
            parse_cdeclr(base, 2, d);
            tp.pack = d.pack;
            tp.name = d.qn.name;
            var ty = d.ty;
            if is_array(ty) { ty = mk_ptr(tbase(ty)); } else if is_func(ty) { ty = mk_ptr(ty); }
            tp.ty = ty;
            if at(TK_EQUAL) {
                adv();
                tp.def0 = pc as! u32;
                targ_depth++;
                diag_suppress++;
                let e = parse_cexpr_noGT();
                diag_suppress--;
                targ_depth--;
                tp.def1 = pc as! u32;
            }
            let s = csym(SK_NTTP, tp.name, ty, loc);
            syms[s].v = ((tmpl_depth << 16) | index) as i64;
            cxs[s].flags = CF_TPARAM;
            if tp.name != 0 { bind_sym(s, false); }
            tp.sym = s as! i32;
        }
        tps.push(tp);
        index++;
        if !accept(TK_COMMA) { break; }
    }
    if !take_gt() { perr_expected("'>'"); }
}

// After `class`/`typename` in a template parameter list: a type parameter
// (vs. a non-type parameter of type `typename X::y` / `class X`)?
fn type_param_ahead() -> bool {
    let k1 = tk_n(1);
    if k1 == TK_ELLIPSIS || k1 == TK_COMMA || k1 == TK_EQUAL { return true; }
    if k1 == TK_GREATER || k1 == TK_GREATERGREATER { return true; }
    if k1 == TK_IDENT {
        let k2 = tk_n(2);
        return k2 == TK_COMMA || k2 == TK_EQUAL || k2 == TK_GREATER || k2 == TK_GREATERGREATER;
    }
    return false;
}

// ---------------------------------------------------------------------------
// Template records.

// Creates the template record's symbol for a class template named `name`
// in the current scope (pending_tmpl is its record), or finds the one
// already declared there.
fn class_template_sym(name: u32, is_union: bool, loc: u32) -> i64 {
    let prev = tag_in_scope(cur_scope, name, false);
    if prev >= 0 && syms[prev].kind as i64 == SK_TEMPLATE {
        merge_tmpl_defaults(cxs[prev].tmpl as i64, pending_tmpl);
        pending_tmpl = -1;
        return prev;
    }
    let t = pending_tmpl;
    pending_tmpl = -1;
    let s = csym(SK_TEMPLATE, name, 0, loc);
    cxs[s].tmpl = t as! i32;
    cxs[s].flags = CF_TEMPLATE;
    tmpls[t].kind = TT_CLASS as! u8;
    tmpls[t].sym = s as! i32;
    tmpls[t].scope = cur_scope as! i32;
    if cur_class >= 0 && scopes[cur_class].flags & SCF_PATTERN != 0 {
        tmpls[t].outer = scopes[cur_class].rec;
    }
    scope_add(cur_scope, s);
    last_tmpl_sym = s;
    return s;
}

// A redeclaration of template t0 with the header t1: default arguments
// accumulate ([temp.param]p10).
fn merge_tmpl_defaults(t0: i64, t1: i64) {
    if t0 < 0 || t1 < 0 || t0 == t1 || tmpls[t0].nparams != tmpls[t1].nparams { return; }
    for i in tmpls[t0].nparams as i64 {
        let a = tmpls[t0].params as i64 + i;
        let b = tmpls[t1].params as i64 + i;
        if tps[a].def0 == 0 && tps[b].def0 != 0 { tps[a].def0 = tps[b].def0; tps[a].def1 = tps[b].def1; }
    }
}

// A class template declaration without a body (template<class T> class X;).
fn declare_class_template(name: u32, is_union: bool, loc: u32, defining: bool) -> u32 {
    let s = class_template_sym(name, is_union, loc);
    return tmpl_injected(s);
}

// Starts the definition of class template tsym's pattern: the pattern
// class's symbol (its type is the pattern record).
fn class_template_def(tsym: i64, is_union: bool, loc: u32) -> i64 {
    merge_tmpl_defaults(cxs[tsym].tmpl as i64, pending_tmpl);
    let t = cxs[tsym].tmpl as i64;
    // D2: the definition's header (its parameter names, its tokens) when an
    // earlier declaration made the template record
    if pending_tmpl >= 0 && pending_tmpl != t { tmpls[t].def_t = pending_tmpl as! i32; }
    pending_tmpl = -1;
    let r = new_record_cx(syms[tsym].name, is_union, loc);
    let s = csym(SK_TAG, syms[tsym].name, records[r].ty << 4, loc);
    syms[s].v = records[r].ty as i64;
    // the class's scope is in the template's (an out-of-line member template
    // of a class is defined in that class)
    let parent = if cxs[tsym].dscope >= 0 { cxs[tsym].dscope as i64 } else { cur_scope };
    cxs[s].dscope = parent as! i32;
    cxs[s].tmpl = t as! i32;
    let sc = class_setup(r, s, parent);
    scopes[sc].flags = scopes[sc].flags | SCF_PATTERN;
    crecs[r].flags = crecs[r].flags | CR_PATTERN;
    // the injected-class-name refers to the template too
    let inj = scope_find(sc, syms[tsym].name);
    if inj >= 0 { cxs[inj].tmpl = t as! i32; }
    if tmpls[t].pattern < 0 || tmpls[t].spec_args < 0 {
        tmpls[t].pattern = r as! i32;
    }
    return s;
}

// The class a class template's name means inside its own definition: its
// pattern, or an opaque specialization when it has none (yet).
fn tmpl_injected(tsym: i64) -> u32 {
    let t = cxs[tsym].tmpl as i64;
    if t < 0 { return t_unknown; }
    if tmpls[t].kind as i64 == TT_CLASS && tmpls[t].pattern >= 0 {
        return records[tmpls[t].pattern].ty << 4;
    }
    return mk_depspec(tsym, own_args(t));
}

// The list of a template's own parameters as arguments.
fn own_args(t: i64) -> i32 {
    let mark = targ_scratch.len;
    let n = tmpls[t].nparams as i64;
    for i in n {
        let p = tps[tmpls[t].params as i64 + i];
        if p.kind as i64 == TPK_TYPE {
            targ_scratch.push(TArg { kind: TA_TYPE as! u8, rsv: 0, rsv2: 0, ty: if p.pack { mk_packexp(p.ty) } else { p.ty }, v: 0 });
        } else if p.kind as i64 == TPK_VALUE {
            let vt = mk_tparam(tmpls[t].depth as i64, i, 0, false);
            targ_scratch.push(TArg { kind: TA_VALUE as! u8, rsv: 0, rsv2: 0, ty: if p.pack { mk_packexp(vt) } else { vt }, v: -1 });
        } else {
            targ_scratch.push(TArg { kind: TA_TEMPLATE as! u8, rsv: 0, rsv2: 0, ty: 0, v: p.sym as i64 });
        }
    }
    return targ_intern(mark);
}

// Does the argument list involve a template parameter (an uninstantiated
// specialization with concrete arguments is opaque, not dependent)?
fn args_dependent(args: i32) -> bool { args_dependent_strict(args as i64) }

// The type template tsym names with arguments `args`.
recursive fn specialization(tsym: i64, args: i32) -> u32 {
    let t = cxs[tsym].tmpl as i64;
    if t < 0 { return t_unknown; }
    let k = tmpls[t].kind as i64;
    if k == TT_ALIAS { return alias_subst(t, args); }
    if k == TT_PARAM { return mk_depspec(tsym, args); }
    if k != TT_CLASS { return t_unknown; }
    if args == own_args(t) && tmpls[t].pattern >= 0 { return records[tmpls[t].pattern].ty << 4; }
    let full = complete_args(t, args);
    if full != args {
        let g0 = spec_map.get(((t as u64) << 32) | (full as u64));
        if g0 { return g0; }
        return inst_or_depspec(tsym, t, full);
    }
    // the pattern of a partial specialization written with the same
    // arguments (an out-of-line member: X<T*>::f)
    var l = tmpls[t].specs;
    while l >= 0 {
        let pt = ulinks[l].v as i64;
        if tmpls[pt].spec_args == args && tmpls[pt].pattern >= 0 { return records[tmpls[pt].pattern].ty << 4; }
        l = ulinks[l].next;
    }
    let g = spec_map.get(((t as u64) << 32) | (args as u64));
    if g { return g; }
    return inst_or_depspec(tsym, t, args);
}

// An alias template's type for `args`: its type-id parsed again with the
// parameters bound to the arguments, at its point of definition.
var alias_depth: i64 = 0;
recursive fn alias_subst(t: i64, args: i32) -> u32 {
    if tmpls[t].t1 == 0 { return t_unknown; }
    let full = complete_args(t, args);
    return subst_parse(t, full, tmpls[t].t0 as i64, 0, 0);
}

// Parses, at the tokens from `tok`, a type-id (what 0) or a constant
// expression (what 1, its value in subst_val) with template t's
// parameters bound to `args`, in the template's scope and as of its point
// of definition (two-phase lookup).
var subst_val: i64 = 0;
var subst_ok: bool = false;
recursive fn subst_parse(t: i64, args: i32, tok: i64, what: i64, upto: i64) -> u32 {
    if alias_depth > 32 { return t_unknown; }
    let n = if upto > 0 { upto } else { tmpls[t].nparams as i64 };
    let na = tl_count(args as i64);
    let sv = save();
    let s_scope = cur_scope;
    let s_floor = local_floor;
    let s_vis = vis_limit;
    let s_class = cur_class;
    let s_pending = pending_tmpl;
    let s_tdepth = tmpl_depth;
    alias_depth++;
    push_scope();
    local_floor = scope_depth;
    // enclosing templates' parameters stay dependent: only this template's are bound
    for i in n {
        let p = tps[tmpls[t].params as i64 + i];
        if p.name == 0 { continue; }
        var ok = i < na;
        var a = TArg { kind: 0, rsv: 0, rsv2: 0, ty: 0, v: 0 };
        if ok { a = tl_arg(args as i64, i); }
        if p.pack {
            // a pack binds the rest (as an opaque type if it is used)
            let s = csym(SK_TYPEDEF, p.name, t_unknown, 0);
            syms[s].sc = SC_TYPEDEF;
            bind_sym(s, false);
            continue;
        }
        if p.kind as i64 == TPK_TYPE {
            let s = csym(SK_TYPEDEF, p.name, if ok && a.kind as i64 == TA_TYPE { a.ty } else { t_unknown }, 0);
            syms[s].sc = SC_TYPEDEF;
            bind_sym(s, false);
        } else if p.kind as i64 == TPK_VALUE {
            let s = csym(SK_NTTP, p.name, p.ty, 0);
            let known = ok && a.kind as i64 == TA_VALUE && a.ty != 0 && !is_opaque(a.ty);
            syms[s].v = if known { a.v } else { 0 };
            cxs[s].flags = if known { CF_TPARAM | CF_SUBST } else { CF_TPARAM };
            if known { syms[s].ty = a.ty; }
            bind_sym(s, false);
        } else {
            let s = csym(SK_TEMPLATE, p.name, 0, 0);
            if ok && a.kind as i64 == TA_TEMPLATE && a.v >= 0 {
                syms[s].kind = SK_USING;
                cxs[s].target = a.v as! i32;
            }
            bind_sym(s, false);
        }
    }
    cur_scope = tmpls[t].scope as i64;
    cur_class = -1;
    pending_tmpl = -1;
    // two-phase lookup: what was declared before the tokens parsed (a
    // default argument of a later redeclaration sees what precedes it)
    if !args_dependent(args) { vis_limit = if tok > tmpls[t].pos as i64 { tok } else { tmpls[t].pos as i64 }; tmpl_depth = 0; }
    pc = tok;
    gt_pos = -1;
    diag_suppress++;
    var ty: u32 = 0;
    subst_ok = false;
    if what == 0 {
        ty = parse_type_id();
    } else {
        targ_depth++;
        let e = parse_cexpr_noGT();
        targ_depth--;
        ty = nodes[e].ty;
        let ok2, v = const_int(e);
        subst_ok = ok2;
        subst_val = v;
    }
    diag_suppress--;
    pop_scope();
    alias_depth--;
    tmpl_depth = s_tdepth;
    local_floor = s_floor;
    vis_limit = s_vis;
    cur_scope = s_scope;
    cur_class = s_class;
    pending_tmpl = s_pending;
    restore(sv);
    return ty;
}

// The argument list completed with the template's default arguments
// (when all given arguments are concrete; a dependent list is kept).
recursive fn complete_args(t: i64, args0: i32) -> i32 {
    let args = convert_value_args(t, args0);
    let n = tmpls[t].nparams as i64;
    let na = tl_count(args as i64);
    if na >= n || args_dependent(args) { return args; }
    var cur = args;
    var i = na;
    while i < n {
        let p = tps[tmpls[t].params as i64 + i];
        if p.pack || p.def0 == 0 { break; }
        var arg = TArg { kind: 0, rsv: 0, rsv2: 0, ty: 0, v: 0 };
        if p.kind as i64 == TPK_TYPE {
            let ty = subst_parse(t, cur, p.def0 as i64, 0, i);
            arg = TArg { kind: TA_TYPE as! u8, rsv: 0, rsv2: 0, ty: ty, v: 0 };
        } else if p.kind as i64 == TPK_VALUE {
            let ty = subst_parse(t, cur, p.def0 as i64, 1, i);
            if !subst_ok { break; }
            arg = TArg { kind: TA_VALUE as! u8, rsv: 0, rsv2: 0, ty: unqual(nonref(p.ty)), v: subst_val };
            if is_opaque(arg.ty) { arg.ty = unqual(nonref(ty)); }
        } else {
            break;
        }
        // the list so far plus this argument
        let mark = targ_scratch.len;
        for j in tl_count(cur as i64) { targ_scratch.push(tl_arg(cur as i64, j)); }
        targ_scratch.push(arg);
        cur = targ_intern(mark);
        i++;
    }
    return cur;
}
let CF_SUBST = 268435456;   // a non-type template parameter bound to a value (syms[s].v)

// Integral template arguments converted to their parameters' types
// ([temp.arg.nontype]: X<258> for a parameter of type unsigned is
// X<258u>; the mangled name says `Lj258E`).
fn convert_value_args(t: i64, args: i32) -> i32 {
    let n = tmpls[t].nparams as i64;
    let na = tl_count(args as i64);
    var changed = false;
    for i in na {
        if i >= n { break; }
        let p = tps[tmpls[t].params as i64 + i];
        if p.pack { break; }
        let a = tl_arg(args as i64, i);
        if p.kind as i64 != TPK_VALUE || a.kind as i64 != TA_VALUE || a.ty == 0 || is_opaque(a.ty) { continue; }
        let pt = unqual(nonref(p.ty));
        if pt == 0 || pt == a.ty || is_opaque(pt) || kind_of(pt) == TY_ENUM || !(is_integer(pt) || kind_of(pt) == TY_BOOL) { continue; }
        if !(is_integer(a.ty) || kind_of(a.ty) == TY_BOOL || kind_of(a.ty) == TY_ENUM) { continue; }
        changed = true;
    }
    if !changed { return args; }
    let mark = targ_scratch.len;
    for i in na {
        var a = tl_arg(args as i64, i);
        if i < n {
            let p = tps[tmpls[t].params as i64 + i];
            if !p.pack && p.kind as i64 == TPK_VALUE && a.kind as i64 == TA_VALUE && a.ty != 0 && !is_opaque(a.ty) {
                let pt = unqual(nonref(p.ty));
                if pt != 0 && pt != a.ty && !is_opaque(pt) && kind_of(pt) != TY_ENUM && (is_integer(pt) || kind_of(pt) == TY_BOOL) &&
                   (is_integer(a.ty) || kind_of(a.ty) == TY_BOOL || kind_of(a.ty) == TY_ENUM) {
                    a.v = trunc_to(a.v, pt);
                    a.ty = pt;
                }
            }
        }
        targ_scratch.push(a);
    }
    return targ_intern(mark);
}

// template<class T> class X<args> { }: a partial specialization (args
// dependent) or, after template<>, an explicit specialization.
recursive fn begin_class_specialization(qn: QN&, is_union: bool, loc: u32) -> i64 {
    lookup_qn(qn);
    var tsym: i64 = -1;
    var s = qn.sym as i64;
    while s >= 0 {
        let r = resolve(s);
        if r >= 0 && syms[r].kind as i64 == SK_TEMPLATE { tsym = r; break; }
        if r >= 0 && cxs[r].flags & CF_INJECTED != 0 && cxs[r].tmpl >= 0 { tsym = tmpls[cxs[r].tmpl].sym as i64; break; }
        s = cxs[s].nnext as i64;
    }
    if tsym >= 0 && !(pending_tmpl >= 0 && args_dependent(qn.targs)) {
        // D2: an explicit specialization of a specialization already named
        // (declared, not instantiated) defines that record
        let t0 = cxs[tsym].tmpl as i64;
        let full0 = complete_args(t0, qn.targs);
        let g = spec_map.get(((t0 as u64) << 32) | (full0 as u64));
        if g && is_record(g) {
            let r0 = rec_of(g);
            let sc0 = crecs[r0].scope as i64;
            if sc0 >= 0 && scopes[sc0].flags & SCF_INST_PENDING != 0 {
                pending_tmpl = -1;
                scopes[sc0].flags = scopes[sc0].flags & ~((SCF_INST_PENDING | SCF_INST) as! u8);
                let cs0 = crecs[r0].sym as i64;
                if dependent_ctx() { scopes[sc0].flags = scopes[sc0].flags | SCF_PATTERN; }
                return cs0;
            }
        }
    }
    let r = new_record_cx(qn.name, is_union, loc);
    let cs = csym(SK_TAG, qn.name, records[r].ty << 4, loc);
    syms[cs].v = records[r].ty as i64;
    let parent = if tsym >= 0 && cxs[tsym].dscope >= 0 { cxs[tsym].dscope as i64 } else { cur_scope };
    cxs[cs].dscope = parent as! i32;
    let sc = class_setup(r, cs, parent);
    if tsym < 0 { pending_tmpl = -1; return cs; }
    let t = cxs[tsym].tmpl as i64;
    if pending_tmpl >= 0 && args_dependent(qn.targs) {
        // a partial specialization: a pattern
        let pt = pending_tmpl;
        pending_tmpl = -1;
        tmpls[pt].kind = TT_CLASS as! u8;
        tmpls[pt].sym = tsym as! i32;
        tmpls[pt].pattern = r as! i32;
        tmpls[pt].spec_args = qn.targs;
        tmpls[pt].primary = t as! i32;
        tmpls[t].specs = link_add(tmpls[t].specs, pt);
        scopes[sc].flags = scopes[sc].flags | SCF_PATTERN;
        crecs[r].flags = crecs[r].flags | CR_PATTERN;
        cxs[cs].tmpl = pt as! i32;
        let inj = scope_find(sc, qn.name);
        if inj >= 0 { cxs[inj].tmpl = t as! i32; }
        return cs;
    }
    pending_tmpl = -1;
    // an explicit specialization: a real class
    let full = complete_args(t, qn.targs);
    spec_map.insert(((t as u64) << 32) | (full as u64), records[r].ty << 4);
    cxs[cs].flags = cxs[cs].flags | CF_SPEC;
    cxs[cs].tmpl = t as! i32;
    cxs[cs].targs = full;
    let inj = scope_find(sc, qn.name);
    if inj >= 0 { cxs[inj].tmpl = t as! i32; }
    if dependent_ctx() {
        scopes[sc].flags = scopes[sc].flags | SCF_PATTERN;
    }
    return cs;
}

// class X<args>; : an explicit specialization or instantiation declared
// without a body (nothing to do in D1).
fn note_spec_decl(qn: QN&) {
    pending_tmpl = -1;
}

// Starts a function template (or a member function template) named by d:
// the template symbol, filed in scope sc, chained with the functions of
// the same name. The pattern function is created by the caller.
fn func_template_sym(name: u32, sc: i64, loc: u32) -> i64 {
    let t = pending_tmpl;
    pending_tmpl = -1;
    let s = csym(SK_TEMPLATE, name, 0, loc);
    cxs[s].tmpl = t as! i32;
    cxs[s].flags = CF_TEMPLATE;
    tmpls[t].kind = TT_FUNC as! u8;
    tmpls[t].sym = s as! i32;
    tmpls[t].scope = sc as! i32;
    scope_add(sc, s);
    return s;
}
