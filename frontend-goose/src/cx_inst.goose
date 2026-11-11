// goosecc D2: template instantiation.
//
// A class template specialization with concrete arguments (X<int>) is a
// record from the moment it is named: its symbol, its class scope (filed
// under the template's scope, so that it mangles as X<int>) and its
// injected-class-name exist, with SCF_INST_PENDING on the scope. It is
// instantiated when a complete type is needed (a member is looked up, an
// object is defined, its size is asked for ...): the pattern (the primary
// template or the most specialized matching partial specialization) is
// parsed again from its tokens as the body of that record, with the
// template parameters bound to the arguments in a scope of their own
// (Scope.tps, kind CS_TPARAMS) that unqualified lookup visits after the
// class's members. Member function bodies are kept as tokens and parsed
// when the member is used (inst_use): the work-list `inst_work` is drained
// at the end of the translation unit, so that the parser never holds more
// than the instantiations a complete type needs on its native stack.
//
// Function templates: deduction (deduce_*), then the declaration parsed
// again with the deduced arguments bound (a specialization symbol, not
// filed in any scope), and its body on use like a member's.
//
// While instantiating, the parser's state is replaced (inst_enter) and
// restored (inst_leave): the token cursor, the scopes, the function being
// parsed, the template depth. Lookups see the namespace members declared
// before the token being parsed (VIS_PC, two-phase lookup); block-scope
// bindings of the code that triggered the instantiation are below
// local_floor and invisible.

namespace cx;

import std;
import os;
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
import .cx_layout;

let CF2_LAZY_BODY = 1;      // a member of an instantiation (or a function template specialization): body tokens kept, parsed on use
let CF2_INST_DONE = 2;      // its body was instantiated (or is being)
let CF2_DIRTY = 4;          // errors while instantiating it (suppressed): not trusted for code generation
let CF2_QUEUED = 8;         // in inst_work
let CF2_FSPEC = 16;         // a function template specialization (cxs.tmpl: the template, cxs.targs: the arguments)
let CF2_EXPLICIT = 128;     // an explicit specialization (template<>): its own definition, never instantiated

var inst_depth: i64 = 0;
var inst_work: u32[>..] = [];       // functions whose bodies are to be instantiated
var inst_work_done: i64 = 0;
var inst_pat = dictionary<u64, u64> {};    // instantiated record -> (pattern Tmpl << 32 | its argument list)
var inst_dirty = dictionary<u64, u32> {};  // records whose instantiation had errors
var inst_errors: i64 = 0;           // errors met (and suppressed) inside instantiations
var inst_report_mode: i64 = -1;     // GOOSECC_INST_ERRORS=1: report errors inside instantiations

var inst_debug_mode: i64 = -1;
fn inst_debug() -> bool {
    if inst_debug_mode < 0 {
        var v: u8[>..] = [];
        inst_debug_mode = if env("GOOSECC_DEBUG_INST", v) && v.len > 0 && v[0] == '1' { 1 } else { 0 };
    }
    return inst_debug_mode == 1;
}

fn inst_reporting() -> bool {
    if inst_report_mode < 0 {
        var v: u8[>..] = [];
        inst_report_mode = if env("GOOSECC_INST_ERRORS", v) && v.len > 0 {
            if v[0] == '1' || v[0] == '2' { 1 } else if v[0] == '0' { 2 } else { 0 }
        } else { 0 };
        if v.len > 0 && v[0] == '2' { diag_show_all = true; }
    }
    return inst_report_mode == 1;
}
// GOOSECC_INST_ERRORS=0: errors of instantiations are suppressed (D2's
// earlier behaviour, for comparisons)
fn inst_hard_errors() -> bool { inst_reporting(); return inst_report_mode != 2; }

// ---------------------------------------------------------------------------
// Entering and leaving an instantiation.

struct InstSave {
    sv: Save,
    scope: i64,
    cls: i64,
    access: i64,
    floor: i64,
    vis: i64,
    tdepth: i64,
    ptmpl: i64,
    pexpl: bool,
    pinst: bool,
    extc: bool,
    nest: i64,
    func_cx: i64,
    func: i64,
    this_t: u32,
    ret_t: u32,
    ld: i64,
    bd: i64,
    bfd: i64,
    targd: i64,
    pard: i64,
    uneval: i64,
    lenient0: i64,
    errs: i64,
    what: i64,
    supp: i64,
    level: i64,
    spec_t: i64,
    spec_b: i32,
    spec_res: i64,
    spec_decl: bool,
    body_now: bool,
    def_target: i64,
    var_t: i64,
    watch: i64,
    watch_errs: i64,
    nerr: i64,
}

// hard: errors inside are errors of the program (class and member
// instantiations); otherwise a substitution failure (SFINAE) suppressed and
// counted.
fn inst_enter(hard: bool) -> InstSave {
    let st = InstSave { sv: save(), scope: cur_scope, cls: cur_class, access: cur_access, floor: local_floor, vis: vis_limit,
        tdepth: tmpl_depth, ptmpl: pending_tmpl, pexpl: pending_explicit, pinst: pending_inst, extc: extern_c, nest: class_nest,
        func_cx: cur_func_cx, func: cur_func, this_t: this_type, ret_t: ret_type, ld: loop_depth, bd: break_depth,
        bfd: block_fn_depth, targd: targ_depth, pard: paren_depth, uneval: unevaluated, lenient0: lenient,
        errs: diag_inst_errors, what: inst_what, supp: diag_suppress, level: diag_inst_level,
        spec_t: inst_spec_tmpl, spec_b: inst_spec_binds, spec_res: inst_spec_result, spec_decl: inst_spec_decl,
        body_now: inst_body_now, def_target: inst_def_target, var_t: inst_var_tmpl, watch: diag_watch_level, watch_errs: diag_watch_errors, nerr: n_errors };
    diag_watch_level = -1;
    inst_var_tmpl = -1;
    inst_spec_tmpl = -1;
    inst_spec_result = -1;
    inst_spec_decl = false;
    inst_body_now = false;
    inst_def_target = -1;
    push_scope();
    local_floor = scope_depth;
    vis_limit = VIS_PC;
    cur_class = -1;
    tmpl_depth = 0;
    pending_tmpl = -1;
    pending_explicit = false;
    pending_inst = false;
    extern_c = false;
    class_nest = 0;
    cur_func_cx = -1;
    this_type = 0;
    ret_type = 0;
    loop_depth = 0;
    break_depth = 0;
    block_fn_depth = 0;
    targ_depth = 0;
    paren_depth = 0;
    unevaluated = 0;
    lenient = 0;
    gt_pos = -1;
    inst_depth++;
    diag_suppress = if inst_reporting() { 0 } else if hard && inst_hard_errors() { st.supp } else { 1 };
    diag_inst_level = diag_suppress;
    return st;
}

// Restores the state; true when errors happened inside.
fn inst_leave(st: InstSave) -> bool {
    inst_spec_tmpl = st.spec_t;
    inst_spec_binds = st.spec_b;
    inst_spec_result = st.spec_res;
    inst_spec_decl = st.spec_decl;
    inst_body_now = st.body_now;
    inst_def_target = st.def_target;
    inst_var_tmpl = st.var_t;
    diag_watch_level = st.watch;
    diag_watch_errors = st.watch_errs;
    let shown = diag_suppress == 0 && n_errors > st.nerr;
    diag_suppress = st.supp;
    diag_inst_level = st.level;
    inst_depth--;
    pop_scope();
    cur_scope = st.scope;
    cur_class = st.cls;
    cur_access = st.access;
    local_floor = st.floor;
    vis_limit = st.vis;
    tmpl_depth = st.tdepth;
    pending_tmpl = st.ptmpl;
    pending_explicit = st.pexpl;
    pending_inst = st.pinst;
    extern_c = st.extc;
    class_nest = st.nest;
    cur_func_cx = st.func_cx;
    cur_func = st.func;
    this_type = st.this_t;
    ret_type = st.ret_t;
    loop_depth = st.ld;
    break_depth = st.bd;
    block_fn_depth = st.bfd;
    targ_depth = st.targd;
    paren_depth = st.pard;
    unevaluated = st.uneval;
    lenient = st.lenient0;
    restore(st.sv);
    let bad = diag_inst_errors != st.errs;
    // an instantiation's errors are its own, not its trigger's
    diag_inst_errors = st.errs;
    if bad { inst_errors++; }
    if bad && (inst_reporting() || shown) && st.what >= 0 {
        var o: u8[>..] = [];
        loc_prefix(o, tloc() as i64);
        o.append("note: in instantiation of ");
        inst_what_text(o, st.what);
        o.append(" requested here\n");
        write_stderr(o);
    }
    return bad;
}
var inst_what: i64 = -1;    // the symbol being instantiated (notes)

// ---------------------------------------------------------------------------
// Class template specializations.

// May template t be instantiated with the (complete) argument list args?
fn can_instantiate(t: i64, args: i32) -> bool {
    if tmpls[t].kind as i64 != TT_CLASS || tmpls[t].t0 == 0 { return false; }
    let sc = tmpls[t].scope as i64;
    if sc >= 0 && scopes[sc].flags & (SCF_PATTERN | SCF_INST_PENDING) != 0 { return false; }
    if args_dependent_strict(args as i64) { return false; }
    let n = tl_count(args as i64);
    for i in n {
        let a = tl_arg(args as i64, i);
        let k = a.kind as i64;
        if k == TA_TYPE && (a.ty == 0 || is_opaque(a.ty)) { return false; }
        if k == TA_VALUE && (a.ty == 0 || is_opaque(a.ty)) { return false; }
        if k == TA_TEMPLATE && a.v < 0 { return false; }
        if k == TA_PACK { return false; }
    }
    // every parameter has an argument (or is a pack)
    let np = tmpls[t].nparams as i64;
    if n < np {
        let p = tps[tmpls[t].params as i64 + n];
        if !p.pack { return false; }
    }
    if n > np && np > 0 && !tps[tmpls[t].params as i64 + np - 1].pack { return false; }
    if n > 0 && np == 0 { return false; }
    return true;
}

// The class-key of a class template's pattern (KW_CLASS, KW_STRUCT, KW_UNION).
fn tmpl_class_key(t: i64) -> i64 {
    var j = tmpls[t].t0 as i64;
    let end = if tmpls[t].t1 > 0 { tmpls[t].t1 as i64 } else { j + 64 };
    while j < end && j < tu_toks.len {
        let k = tu_toks[j].kind as i64;
        if k == TK_KW + KW_STRUCT { return KW_STRUCT; }
        if k == TK_KW + KW_CLASS { return KW_CLASS; }
        if k == TK_KW + KW_UNION { return KW_UNION; }
        j++;
    }
    return KW_STRUCT;
}

// The record of specialization tsym<args> (args complete and concrete):
// declared, to be instantiated when a complete type is needed.
fn inst_class_type(tsym: i64, t: i64, args: i32) -> u32 {
    let name = syms[tsym].name;
    let loc = syms[tsym].loc;
    let w = tmpl_class_key(t);
    let r = new_record_cx(name, w == KW_UNION, loc);
    let ty = records[r].ty << 4;
    let cs = csym(SK_TAG, name, ty, loc);
    syms[cs].v = records[r].ty as i64;
    syms[cs].scope = 0;
    let parent = if cxs[tsym].dscope >= 0 { cxs[tsym].dscope as i64 } else { tmpls[t].scope as i64 };
    cxs[cs].dscope = parent as! i32;
    cxs[cs].flags = CF_SPEC;
    cxs[cs].tmpl = t as! i32;
    cxs[cs].targs = args;
    cxs[cs].pos = 0;
    let sc = class_setup(r, cs, parent);
    scopes[sc].flags = scopes[sc].flags | SCF_INST | SCF_INST_PENDING;
    if w == KW_CLASS { crecs[r].flags = crecs[r].flags | CR_CLASS_KW; }
    let inj = scope_find(sc, name);
    if inj >= 0 { cxs[inj].tmpl = t as! i32; syms[inj].scope = 0; cxs[inj].pos = 0; }
    spec_map.insert(((t as u64) << 32) | (args as u64), ty);
    return ty;
}

// The type of tsym<full>: its instantiation (declared), or an opaque
// specialization when it cannot be instantiated.
fn inst_or_depspec(tsym: i64, t: i64, full: i32) -> u32 {
    if inst_debug() { write_stderr(str("inst_or_depspec ", ident_text(syms[tsym].name as i64), " t=", t, " tsym=", tsym, " tmpls.sym=", tmpls[t].sym, " can=", can_instantiate(t, full), "\n")); }
    if tmpls[t].sym as i64 == tsym && can_instantiate(t, full) { return inst_class_type(tsym, t, full); }
    return mk_depspec(tsym, full);
}

recursive fn inst_scope_now(sc: i64) {
    let r = scopes[sc].rec as i64;
    if r >= 0 { inst_record(r); }
}

// A complete type is needed for t: instantiates a pending specialization.
recursive fn need_complete(t: u32) {
    var x = t;
    while kind_of(x) == TY_ARRAY { x = tbase(x); }
    if !is_record(x) { return; }
    let r = rec_of(x);
    if r >= crecs.len { return; }
    let sc = crecs[r].scope as i64;
    if sc >= 0 && scopes[sc].flags & SCF_INST_PENDING != 0 { inst_record(r); }
}

// Is class scope sc complete with all its members known (no dependent or
// unknown bases, not a template's pattern, not an instantiation that had
// errors)? A lookup that fails there is an error, not something unknown.
fn known_class_scope(sc: i64) -> bool {
    if sc < 0 || scopes[sc].kind as i64 != CS_CLASS { return false; }
    if scopes[sc].flags & (SCF_PATTERN | SCF_INST_PENDING) != 0 { return false; }
    let r = scopes[sc].rec as i64;
    if r < 0 || records[r].flags & RF_COMPLETE == 0 || records[r].flags & RF_BEING_DEFINED != 0 { return false; }
    if crecs[r].flags & CR_PATTERN != 0 { return false; }
    return !has_dep_base(sc);
}

// Is t (a record) an instantiation whose instantiation had errors (or that
// could not be instantiated)?
fn inst_is_dirty(t: u32) -> bool {
    if !is_record(t) { return false; }
    return inst_dirty.contains(rec_of(t) as u64);
}

// Instantiates the pending specialization r.
recursive fn inst_record(r: i64) {
    let sc = crecs[r].scope as i64;
    if sc < 0 || scopes[sc].flags & SCF_INST_PENDING == 0 { return; }
    if inst_depth > 400 { return; }
    if member_cls.contains(r as u64) { inst_member_class(r); return; }
    let cs = crecs[r].sym as i64;
    let t = cxs[cs].tmpl as i64;
    let args = cxs[cs].targs;
    let pat, pargs = select_pattern(t, args);
    if inst_debug() { write_stderr(str("inst_record r=", r, " ", ctname(records[r].ty << 4), " t=", t, " pat=", pat, " pattern=", if pat >= 0 { tmpls[pat].pattern } else { -9 }, "\n")); }
    if pat < 0 || tmpls[pat].pattern < 0 || tmpls[pat].t1 == 0 { return; }
    // the header and tokens of the pattern's definition
    let src = if tmpls[pat].def_t >= 0 { tmpls[pat].def_t as i64 } else { pat };
    if tmpls[src].t1 == 0 { return; }
    scopes[sc].flags = scopes[sc].flags & ~(SCF_INST_PENDING as! u8);
    scopes[sc].tps = tparam_scope(src, pargs) as! i32;
    inst_pat.insert(r as u64, ((pat as u64) << 32) | (pargs as u64));
    let w = tmpl_class_key(src);
    if head_has_final(src) { mark_final(r); }
    inst_what = cs;
    let st = inst_enter(true);
    cur_scope = sc;
    pc = class_head_end(src);
    records[r].pack = pack_now();
    parse_class_body(r, w);
    let bad = inst_leave(st);
    if bad { inst_dirty.insert(r as u64, 1); }
}

// Is the class-head of t's pattern `... Name final`?
fn head_has_final(t: i64) -> bool {
    let e = class_head_end(t);
    return e > 0 && tu_toks[e - 1].kind as i64 == TK_IDENT && tu_toks[e - 1].val == id_final;
}

// The token after the class-head of a class template's pattern: its ':' or '{'.
fn class_head_end(t: i64) -> i64 {
    var j = tmpls[t].t0 as i64;
    var angle = 0;
    loop {
        let k = tu_toks[j].kind as i64;
        if k == TK_EOF { return j; }
        if k == TK_L_PAREN || k == TK_L_SQUARE {
            // skip a balanced group
            var d = 0;
            loop {
                let k2 = tu_toks[j].kind as i64;
                if k2 == TK_EOF { return j; }
                if k2 == TK_L_PAREN || k2 == TK_L_SQUARE || k2 == TK_L_BRACE { d++; }
                if k2 == TK_R_PAREN || k2 == TK_R_SQUARE || k2 == TK_R_BRACE { d--; if d == 0 { break; } }
                j++;
            }
            j++;
            continue;
        }
        if k == TK_LESS { angle++; }
        else if k == TK_GREATER { angle--; }
        else if k == TK_GREATERGREATER { angle -= 2; }
        else if angle <= 0 && (k == TK_COLON || k == TK_L_BRACE) { return j; }
        j++;
    }
    return j;
}

// The scope binding template t's parameters to `binds` (one argument per
// parameter, a pack's as TA_PACK).
fn tparam_scope(t: i64, binds: i32) -> i64 {
    let ps = new_scope(CS_TPARAMS, -1, -1, 0);
    scopes[ps].flags = 0;
    let n = tmpls[t].nparams as i64;
    let na = tl_count(binds as i64);
    for i in n {
        let p = tps[tmpls[t].params as i64 + i];
        if p.name == 0 { continue; }
        let s = bound_param_sym(p, i < na, if i < na { tl_arg(binds as i64, i) } else { TArg { kind: 0, rsv: 0, rsv2: 0, ty: 0, v: 0 } });
        scope_add(ps, s);
    }
    return ps;
}

// A symbol binding template parameter p to argument a (ok: a is given).
fn bound_param_sym(p: TParam, ok: bool, a: TArg) -> i64 {
    var s: i64 = -1;
    if p.pack || (ok && a.kind as i64 == TA_PACK) {
        if p.kind as i64 == TPK_VALUE {
            s = csym(SK_NTTP, p.name, t_unknown, 0);
            cxs[s].flags = CF_TPARAM;
        } else {
            s = csym(SK_TYPEDEF, p.name, t_unknown, 0);
            syms[s].sc = SC_TYPEDEF;
        }
        cxs[s].flags2 = CF2_PACKBIND;
        syms[s].v = if ok && a.kind as i64 == TA_PACK { a.v } else { -1 };
    } else if p.kind as i64 == TPK_TYPE {
        s = csym(SK_TYPEDEF, p.name, if ok && a.kind as i64 == TA_TYPE { a.ty } else { t_unknown }, 0);
        syms[s].sc = SC_TYPEDEF;
    } else if p.kind as i64 == TPK_VALUE {
        s = csym(SK_NTTP, p.name, p.ty, 0);
        let known = ok && a.kind as i64 == TA_VALUE && a.ty != 0 && !is_opaque(a.ty);
        syms[s].v = if known { a.v } else { 0 };
        cxs[s].flags = if known { CF_TPARAM | CF_SUBST } else { CF_TPARAM };
        if known { syms[s].ty = a.ty; }
    } else {
        s = csym(SK_TEMPLATE, p.name, 0, 0);
        if ok && a.kind as i64 == TA_TEMPLATE && a.v >= 0 {
            syms[s].kind = SK_USING;
            cxs[s].target = a.v as! i32;
        }
    }
    syms[s].scope = 0;
    cxs[s].pos = 0;
    return s;
}
let CF2_PACKBIND = 32;      // a template parameter pack bound to a list (syms.v; -1 unknown)

// ---------------------------------------------------------------------------
// Choosing the pattern: partial specializations (C++ [temp.class.spec.match]).

// The pattern of t<args> and the arguments of its parameters.
recursive fn select_pattern(t: i64, args: i32) -> i64, i32 {
    var best: i64 = -1;
    var best_binds: i32 = -1;
    var ambiguous = false;
    var l = tmpls[t].specs;
    while l >= 0 {
        let pt = ulinks[l].v as i64;
        l = ulinks[l].next;
        if tmpls[pt].spec_args < 0 { continue; }
        let ok, binds = match_spec(pt, args);
        if !ok { continue; }
        if best < 0 { best = pt; best_binds = binds; continue; }
        let a = spec_at_least(pt, best);
        let b = spec_at_least(best, pt);
        if a && !b { best = pt; best_binds = binds; ambiguous = false; }
        else if a == b { ambiguous = true; }
    }
    if best >= 0 && !ambiguous { return best, best_binds; }
    if ambiguous { return -1, -1; }
    return t, primary_binds(t, args);
}

// The bindings of t's parameters for a (complete) argument list: a pack
// parameter takes the rest.
fn primary_binds(t: i64, args: i32) -> i32 {
    let n = tmpls[t].nparams as i64;
    var has_pack = false;
    for i in n { if tps[tmpls[t].params as i64 + i].pack { has_pack = true; } }
    if !has_pack { return args; }
    let na = tl_count(args as i64);
    let mark = targ_scratch.len;
    var i = 0;
    while i < n {
        let p = tps[tmpls[t].params as i64 + i];
        if p.pack {
            let m2 = targ_scratch.len;
            // the pack's elements: the rest (a trailing pack), pushed after the current list
            var j = i;
            let rest = na - (n - 1 - i);
            while j < rest { targ_scratch.push(tl_arg(args as i64, j)); j++; }
            let pl = targ_intern(m2);
            targ_scratch.push(TArg { kind: TA_PACK as! u8, rsv: 0, rsv2: 0, ty: 0, v: pl as i64 });
            i++;
            continue;
        }
        if i < na { targ_scratch.push(tl_arg(args as i64, i)); }
        i++;
    }
    return targ_intern(mark);
}

// Deduction state: the bindings of the parameters of the template being
// deduced (ded_tmpl, whose parameters have depth ded_depth), from ded_base.
var ded_args: TArg[>..<] = [];
var ded_base: i64 = 0;
var ded_depth: i64 = -1;
var ded_n: i64 = 0;

struct DedSave { base: i64, depth: i64, n: i64, t: i64 }
var ded_t: i64 = -1;
fn ded_begin(t: i64) -> DedSave {
    let s = DedSave { base: ded_base, depth: ded_depth, n: ded_n, t: ded_t };
    ded_t = t;
    ded_base = ded_args.len;
    ded_depth = tmpls[t].depth as i64;
    ded_n = tmpls[t].nparams as i64;
    for i in ded_n { ded_args.push(TArg { kind: 0, rsv: 0, rsv2: 0, ty: 0, v: 0 }); }
    return s;
}
fn ded_end(s: DedSave) {
    ded_args.resize(ded_base);
    ded_base = s.base;
    ded_depth = s.depth;
    ded_n = s.n;
    ded_t = s.t;
}

// The bindings as a list (false if some parameter is not deduced).
fn ded_list(t: i64) -> bool, i32 {
    let mark = targ_scratch.len;
    for i in ded_n {
        let a = ded_args[ded_base + i];
        if a.kind == 0 {
            let p = tps[tmpls[t].params as i64 + i];
            if p.pack {
                // an empty pack
                let m2 = targ_scratch.len;
                let pl = targ_intern(m2);
                targ_scratch.push(TArg { kind: TA_PACK as! u8, rsv: 0, rsv2: 0, ty: 0, v: pl as i64 });
                continue;
            }
            targ_scratch.resize(mark);
            return false, -1;
        }
        targ_scratch.push(a);
    }
    return true, targ_intern(mark);
}

// Does partial specialization pt match args? Its parameters' bindings.
recursive fn match_spec(pt: i64, args: i32) -> bool, i32 {
    let sv = ded_begin(pt);
    let ok = deduce_list(tmpls[pt].spec_args as i64, args as i64);
    var binds: i32 = -1;
    var full = false;
    if ok { full, binds = ded_list(pt); }
    ded_end(sv);
    if inst_debug() { write_stderr(str("match_spec pt=", pt, " deduced=", ok, " full=", full, "\n")); }
    if ok && full && !spec_args_check(pt, binds, args) {
        if inst_debug() { write_stderr(str("  spec_args_check failed pt=", pt, "\n")); }
        return false, -1;
    }
    return ok && full, binds;
}

// Is partial specialization a at least as specialized as b (b's arguments
// can be deduced from a's, a's parameters being unique types)?
recursive fn spec_at_least(a: i64, b: i64) -> bool {
    let la = synth_args(tmpls[a].spec_args as i64, tmpls[a].depth as i64);
    let sv = ded_begin(b);
    let ok = deduce_list(tmpls[b].spec_args as i64, la as i64);
    ded_end(sv);
    return ok;
}

// The argument list l with the template parameters of depth d replaced by
// unique synthesized types (depth 250).
recursive fn synth_args(l: i64, d: i64) -> i32 {
    let mark = targ_scratch.len;
    for i in tl_count(l) {
        var a = tl_arg(l, i);
        if a.ty != 0 { a.ty = retag(a.ty, d, 250); }
        targ_scratch.push(a);
    }
    return targ_intern(mark);
}

// A class template's pattern record as the template-id it is (X<T> with
// X's own parameters), 0 for another type.
fn pattern_as_depspec(t: u32) -> u32 {
    let r = rec_of(t);
    if r >= crecs.len || crecs[r].flags & CR_PATTERN == 0 { return 0; }
    let cs = crecs[r].sym as i64;
    if cs < 0 || cxs[cs].tmpl < 0 { return 0; }
    let tt = cxs[cs].tmpl as i64;
    if tmpls[tt].kind as i64 != TT_CLASS || tmpls[tt].pattern as i64 != r { return 0; }
    let ts = tmpls[tt].sym as i64;
    if ts < 0 { return 0; }
    // a partial specialization's pattern: X<its argument patterns>
    if tmpls[tt].spec_args >= 0 { return with_q(mk_depspec(ts, tmpls[tt].spec_args), quals(t)); }
    return with_q(mk_depspec(ts, own_args(tt)), quals(t));
}

// t with the template parameters of depth `from` renumbered to depth `to`.
recursive fn retag(t: u32, from: i64, to: i64) -> u32 {
    let k = kind_of(t);
    let q = quals(t);
    if k == TY_STRUCT || k == TY_UNION {
        let pd = pattern_as_depspec(t);
        if pd != 0 { return retag(pd, from, to); }
        return t;
    }
    if k == TY_TPARAM {
        let n = types[t >> 4].n;
        if n >> 16 != from { return t; }
        return with_q(qt(mk_type(TY_TPARAM, types[t >> 4].flags as i64, 0, (to << 16) | (n & 0xFFFF), 0, 0) as i64, 0), q);
    }
    if k == TY_POINTER { return with_q(mk_ptr(retag(tbase(t), from, to)), q); }
    if k == TY_LREF { return with_q(mk_lref(retag(tbase(t), from, to)), q); }
    if k == TY_RREF { return with_q(mk_rref(retag(tbase(t), from, to)), q); }
    if k == TY_ARRAY { return with_q(mk_array(retag(tbase(t), from, to), types[t >> 4].n), q); }
    if k == TY_PACKEXP { return with_q(mk_packexp(retag(tbase(t), from, to)), q); }
    if k == TY_DEPSPEC {
        let l = types[t >> 4].n;
        let nl = synth_args(l, from);
        if to != 250 { return t; }
        return with_q(mk_depspec(types[t >> 4].extra as i64, nl), q);
    }
    return t;
}

// ---------------------------------------------------------------------------
// Deduction (C++ [temp.deduct.type]).

fn ded_bind(idx: i64, a: TArg) -> bool {
    if idx >= ded_n { return false; }
    let cur = ded_args[ded_base + idx];
    if cur.kind == 0 { ded_args[ded_base + idx] = a; return true; }
    if cur.rsv == 1 { return true; }       // given explicitly: not deduced
    return cur.kind == a.kind && cur.ty == a.ty && cur.v == a.v;
}

// Is t a template parameter of the template being deduced? Its index.
fn ded_param(t: u32) -> i64 {
    if kind_of(t) != TY_TPARAM { return -1; }
    let n = types[t >> 4].n;
    if n >> 16 != ded_depth { return -1; }
    return n & 0xFFFF;
}

// Deduces from argument list `a` (concrete) against the pattern list `p`.
recursive fn deduce_list(p: i64, a: i64) -> bool {
    let np = tl_count(p);
    let na = tl_count(a);
    var i = 0;
    while i < np {
        let pa = tl_arg(p, i);
        if pa.ty != 0 && kind_of(pa.ty) == TY_PACKEXP {
            // P... : the rest of the arguments
            if i != np - 1 { return false; }
            let pat = tbase(pa.ty);
            let idx = ded_param(pat);
            if idx >= 0 && quals(pat) == 0 {
                let mark = targ_scratch.len;
                var j = i;
                while j < na {
                    let x = tl_arg(a, j);
                    if pa.kind as i64 == TA_TYPE && x.kind as i64 != TA_TYPE { targ_scratch.resize(mark); return false; }
                    if pa.kind as i64 == TA_VALUE && x.kind as i64 != TA_VALUE { targ_scratch.resize(mark); return false; }
                    targ_scratch.push(x);
                    j++;
                }
                let pl = targ_intern(mark);
                return ded_bind(idx, TArg { kind: TA_PACK as! u8, rsv: 0, rsv2: 0, ty: 0, v: pl as i64 });
            }
            // a pattern X<T>...: each argument against it
            var j = i;
            while j < na {
                if !deduce_arg(TArg { kind: pa.kind, rsv: 0, rsv2: 0, ty: pat, v: pa.v }, tl_arg(a, j)) { return false; }
                j++;
            }
            return true;
        }
        if i >= na { return false; }
        if !deduce_arg(pa, tl_arg(a, i)) { return false; }
        i++;
    }
    return np == na;
}

recursive fn deduce_arg(p: TArg, a: TArg) -> bool {
    let pk = p.kind as i64;
    let ak = a.kind as i64;
    if pk == TA_TYPE {
        if ak != TA_TYPE { return false; }
        return deduce_type(p.ty, a.ty);
    }
    if pk == TA_VALUE {
        if ak != TA_VALUE { return false; }
        if p.ty != 0 && kind_of(p.ty) == TY_TPARAM {
            let idx = ded_param(p.ty);
            if idx < 0 { return p.ty == a.ty && p.v == a.v; }
            return ded_bind(idx, a);
        }
        if p.ty != 0 && (kind_of(p.ty) == TY_DEPEXPR || is_opaque(p.ty)) { return true; }
        return p.v == a.v;
    }
    if pk == TA_TEMPLATE {
        if ak != TA_TEMPLATE { return false; }
        if p.v >= 0 && cxs[p.v].flags & CF_TPARAM != 0 {
            let sv = syms[p.v].v;
            if sv >> 16 == ded_depth { return ded_bind(sv & 0xFFFF, a); }
        }
        return p.v == a.v;
    }
    return false;
}

// Deduces from type a against the pattern p.
recursive fn deduce_type(p: u32, a: u32) -> bool {
    if p == a { return true; }
    let k = kind_of(p);
    if k == TY_TPARAM {
        let idx = ded_param(p);
        if idx < 0 { return false; }
        let pq = quals(p);
        let aq = quals(a);
        if pq & ~aq != 0 { return false; }
        let b = with_q(unqual(a), aq & ~pq);
        return ded_bind(idx, TArg { kind: TA_TYPE as! u8, rsv: 0, rsv2: 0, ty: b, v: 0 });
    }
    if k == TY_DEPNAME || k == TY_DEPEXPR || k == TY_UNKNOWN { return true; }   // non-deduced contexts
    if quals(p) != quals(a) { return false; }
    let ka = kind_of(a);
    if k == TY_STRUCT || k == TY_UNION {
        // X<T> written with the template's own parameters names its pattern
        let pd = pattern_as_depspec(p);
        if pd != 0 { return deduce_type(pd, a); }
    }
    if ka == TY_STRUCT || ka == TY_UNION {
        let ad = pattern_as_depspec(a);
        if ad != 0 { return deduce_type(p, ad); }
    }
    if k == TY_DEPSPEC {
        // X<P...> against a specialization X<A...>
        let ts = types[p >> 4].extra as i64;
        let pl = types[p >> 4].n;
        if ka == TY_DEPSPEC {
            if !same_template(ts, types[a >> 4].extra as i64) { return false; }
            return deduce_list(pl, types[a >> 4].n);
        }
        if ka != TY_STRUCT && ka != TY_UNION { return false; }
        let r = rec_of(a);
        if r >= crecs.len { return false; }
        let cs = crecs[r].sym as i64;
        if cs < 0 || cxs[cs].flags & CF_SPEC == 0 || cxs[cs].tmpl < 0 { return false; }
        let at = cxs[cs].tmpl as i64;
        if syms[ts].kind as i64 == SK_TEMPLATE && cxs[ts].flags & CF_TPARAM != 0 {
            // a template template parameter: TT<P...>
            let sv = syms[ts].v;
            if sv >> 16 == ded_depth {
                if !ded_bind(sv & 0xFFFF, TArg { kind: TA_TEMPLATE as! u8, rsv: 0, rsv2: 0, ty: 0, v: tmpls[at].sym as i64 }) { return false; }
                return deduce_list(pl, cxs[cs].targs as i64);
            }
            return false;
        }
        if !same_template(ts, tmpls[at].sym as i64) { return false; }
        return deduce_list(pl, cxs[cs].targs as i64);
    }
    if k != ka { return false; }
    if k == TY_POINTER || k == TY_LREF || k == TY_RREF || k == TY_COMPLEX || k == TY_VECTOR {
        return deduce_type(tbase(p), tbase(a));
    }
    if k == TY_ARRAY {
        let pn = types[p >> 4].n;
        let an = types[a >> 4].n;
        if pn <= -2 {
            // T[N]: the bound is a non-type parameter
            let dn = -2 - pn;
            if an < 0 { return false; }
            if dn >> 16 == ded_depth {
                let idx = dn & 0xFFFF;
                var vt = t_ulong;
                if ded_t >= 0 && idx < tmpls[ded_t].nparams as i64 {
                    let pp = tps[tmpls[ded_t].params as i64 + idx];
                    if pp.kind as i64 == TPK_VALUE && !is_opaque(pp.ty) { vt = unqual(nonref(pp.ty)); }
                }
                if !ded_bind(idx, TArg { kind: TA_VALUE as! u8, rsv: 0, rsv2: 0, ty: vt, v: trunc_to(an, vt) }) { return false; }
            }
            return deduce_type(tbase(p), tbase(a));
        }
        if pn != an && pn >= 0 { return false; }
        return deduce_type(tbase(p), tbase(a));
    }
    if k == TY_MEMPTR {
        return deduce_type(types[p >> 4].extra, types[a >> 4].extra) && deduce_type(tbase(p), tbase(a));
    }
    if k == TY_FUNC {
        let fp = types[p >> 4];
        let fa = types[a >> 4];
        if (fp.flags as i64) & (TF_VARIADIC | TF_MCONST | TF_MVOLATILE | TF_MLREF | TF_MRREF) !=
           (fa.flags as i64) & (TF_VARIADIC | TF_MCONST | TF_MVOLATILE | TF_MLREF | TF_MRREF) { return false; }
        if !deduce_type(fp.base, fa.base) { return false; }
        var i = 0;
        while i < fp.n {
            let pt = tparams[fp.extra + i];
            if kind_of(pt) == TY_PACKEXP && i == fp.n - 1 {
                // P... against the remaining parameters
                let pat = tbase(pt);
                let idx = ded_param(pat);
                let mark = targ_scratch.len;
                var j = i;
                while j < fa.n {
                    if idx >= 0 && quals(pat) == 0 { targ_scratch.push(TArg { kind: TA_TYPE as! u8, rsv: 0, rsv2: 0, ty: tparams[fa.extra + j], v: 0 }); }
                    else if !deduce_type(pat, tparams[fa.extra + j]) { targ_scratch.resize(mark); return false; }
                    j++;
                }
                if idx >= 0 && quals(pat) == 0 {
                    let pl = targ_intern(mark);
                    return ded_bind(idx, TArg { kind: TA_PACK as! u8, rsv: 0, rsv2: 0, ty: 0, v: pl as i64 });
                }
                return true;
            }
            if i >= fa.n { return false; }
            if !deduce_type(pt, tparams[fa.extra + i]) { return false; }
            i++;
        }
        return fp.n == fa.n;
    }
    return false;
}

fn same_template(a: i64, b: i64) -> bool {
    if a == b { return true; }
    let ra = resolve(a);
    let rb = resolve(b);
    if ra == rb { return true; }
    if ra < 0 || rb < 0 { return false; }
    return cxs[ra].tmpl >= 0 && cxs[ra].tmpl == cxs[rb].tmpl;
}

// ---------------------------------------------------------------------------
// Member function bodies, on use.

var inst_defs: u32[>..] = [];       // N_FUNCDEF / N_DECL items made by instantiation (top-level)
var inst_defs_taken: i64 = 0;       // how many of them the translation unit already holds
var friend_scope = dictionary<u64, u32> {};   // a friend function defined in an instantiated class -> that class scope

// f is used (called, its address taken, ...): its body is to be instantiated.
recursive fn inst_use(f: i64) {
    if f < 0 || f >= cxs.len || unevaluated > 0 { return; }
    if complete_base.count > 0 {
        // code generation's complete-object variant of a structor: its own
        let cb = complete_base.get(f as u64);
        if cb { inst_use(cb as i64); return; }
    }
    if inst_debug() { write_stderr(str("inst_use ", ident_text(syms[f].name as i64), " f=", f, " fl2=", cxs[f].flags2, "\n")); }
    if cxs[f].flags & CF_CTOR != 0 { vtable_use(cxs[f].dscope as i64); }
    if cxs[f].flags2 & (CF2_LAZY_BODY | CF2_QUEUED | CF2_INST_DONE) != CF2_LAZY_BODY { return; }
    cxs[f].flags2 = cxs[f].flags2 | CF2_QUEUED;
    inst_work.push(f as! u32);
}

// A constructor of class scope sc is used: its vtable will be, and with it
// the virtual functions (C++ [temp.inst]p11, clang's MarkVTableUsed).
var vtable_used = dictionary<u64, u32> {};
fn vtable_use(sc: i64) {
    if sc < 0 || scopes[sc].kind as i64 != CS_CLASS || scopes[sc].flags & SCF_INST == 0 { return; }
    let r = scopes[sc].rec as i64;
    if r < 0 || vtable_used.contains(r as u64) { return; }
    vtable_used.insert(r as u64, 1);
    let m = mem_range(r);
    for j in m.count {
        let s = cmem[m.first + j] as i64;
        if cxs[s].flags & CF_VIRTUAL != 0 && cxs[s].flags2 & (CF2_LAZY_BODY | CF2_QUEUED | CF2_INST_DONE) == CF2_LAZY_BODY {
            cxs[s].flags2 = cxs[s].flags2 | CF2_QUEUED;
            inst_work.push(s as! u32);
        }
    }
}

// Instantiates the bodies of the used functions (each may use more).
recursive fn inst_drain() {
    while inst_work_done < inst_work.len {
        let f = inst_work[inst_work_done] as i64;
        inst_work_done++;
        inst_body(f);
    }
}

// Moves what a definition parsed during an instantiation pushed to
// nscratch (from mark) to inst_defs.
fn take_defs(mark: i64) {
    if ce_capturing { nscratch.resize(mark); return; }     // a body parsed for the constant evaluator
    for i in mark..nscratch.len { inst_defs.push(nscratch[i]); }
    nscratch.resize(mark);
}

// The pattern's scope of an instantiated class scope sc (or of a class
// nested in one), -1.
recursive fn pattern_scope(sc: i64) -> i64 {
    if sc < 0 || scopes[sc].kind as i64 != CS_CLASS { return -1; }
    let r = scopes[sc].rec as i64;
    if r < 0 { return -1; }
    let g = inst_pat.get(r as u64);
    if g {
        let pat = (g >> 32) as i64;
        let pr = tmpls[pat].pattern as i64;
        if pr < 0 { return -1; }
        return crecs[pr].scope as i64;
    }
    // a class nested in an instantiation: the same class of the enclosing pattern
    let ps = pattern_scope(scopes[sc].parent as i64);
    if ps < 0 { return -1; }
    let cs = crecs[r].sym as i64;
    if cs < 0 { return -1; }
    var x = scope_find(ps, syms[cs].name);
    while x >= 0 {
        if syms[x].kind as i64 == SK_TAG && cxs[x].pos == cxs[cs].pos && is_record(syms[x].ty) {
            return crecs[rec_of(syms[x].ty)].scope as i64;
        }
        x = cxs[x].nnext as i64;
    }
    return -1;
}

// The pattern's symbol of a member s of an instantiated class, -1.
recursive fn pattern_member(s: i64) -> i64 {
    if cxs[s].pat != -1 { return if cxs[s].pat >= 0 { cxs[s].pat as i64 } else { -1 }; }
    cxs[s].pat = -2;
    let ps = pattern_scope(cxs[s].dscope as i64);
    if ps < 0 { return -1; }
    var x = scope_find(ps, syms[s].name);
    while x >= 0 {
        if syms[x].kind == syms[s].kind && cxs[x].pos == cxs[s].pos { cxs[s].pat = x as! i32; return x; }
        x = cxs[x].nnext as i64;
    }
    return -1;
}

// The arguments the class scope sc was instantiated with, for its
// pattern's parameters (-1 when sc is not an instantiation).
recursive fn inst_args_of(sc: i64) -> i64, i32 {
    var x = sc;
    while x >= 0 && scopes[x].kind as i64 == CS_CLASS {
        let r = scopes[x].rec as i64;
        if r >= 0 {
            let g = inst_pat.get(r as u64);
            if g { return (g >> 32) as i64, (g & 0xFFFFFFFF) as i32; }
        }
        x = scopes[x].parent as i64;
    }
    return -1, -1;
}

// Binds the parameters of header t to `binds` as block-scope names (and
// those of the headers enclosing it to outer_binds, for a member of a
// class template defined out of its class).
fn bind_header(t: i64, binds: i32) {
    let n = tmpls[t].nparams as i64;
    let na = tl_count(binds as i64);
    for i in n {
        let p = tps[tmpls[t].params as i64 + i];
        if p.name == 0 { continue; }
        let s = bound_param_sym(p, i < na, if i < na { tl_arg(binds as i64, i) } else { TArg { kind: 0, rsv: 0, rsv2: 0, ty: 0, v: 0 } });
        bind_sym(s, false);
    }
}

// The body of a used function: instantiated (once).
recursive fn inst_body(f: i64) {
    if cxs[f].flags2 & CF2_INST_DONE != 0 { return; }
    cxs[f].flags2 = cxs[f].flags2 | CF2_INST_DONE;
    if inst_debug() { write_stderr(str("inst_body ", ident_text(syms[f].name as i64), " f=", f, " body=", cxs[f].body, " fl2=", cxs[f].flags2, "\n")); }
    if inst_depth > 400 { return; }
    if syms[f].kind as i64 == SK_VAR { inst_var_def(f); return; }
    let mark = nscratch.len;
    if cxs[f].body != 0 && cxs[f].flags & CF_HAS_BODY_LATER != 0 && cxs[f].flags2 & CF2_FSPEC == 0 {
        // defined in its class
        let fsg = friend_scope.get(f as u64);
        let sc = if fsg { fsg as i64 } else { cxs[f].dscope as i64 };
        inst_what = f;
        let st = inst_enter(true);
        parse_member_body(f, sc);
        let bad = inst_leave(st);
        if bad { cxs[f].flags2 = cxs[f].flags2 | CF2_DIRTY; }
        take_defs(mark);
        return;
    }
    if cxs[f].flags2 & CF2_FSPEC != 0 { inst_fspec_body(f); return; }
    // defined out of its class: that definition parsed again for f
    let p = pattern_member(f);
    if p < 0 || cxs[p].odef < 0 { return; }
    let hdr = cxs[p].odef as i64;
    let pat, pargs = inst_args_of(cxs[f].dscope as i64);
    if pat < 0 { return; }
    inst_what = f;
    let st = inst_enter(true);
    bind_header(hdr, pargs);
    cur_scope = tmpls[hdr].scope as i64;
    pc = tmpls[hdr].t0 as i64;
    inst_def_target = f;
    parse_simple_decl(DC_NS);
    inst_def_target = -1;
    let bad = inst_leave(st);
    if bad { cxs[f].flags2 = cxs[f].flags2 | CF2_DIRTY; }
    take_defs(mark);
}

// A static data member of an instantiated class is used: its definition
// out of the class (template<class T> int X<T>::n = 0;) is instantiated.
fn inst_var_use(s: i64) {
    if cxs[s].flags2 & (CF2_INST_DONE | CF2_QUEUED) != 0 { return; }
    let sc = cxs[s].dscope as i64;
    if sc < 0 || scopes[sc].flags & SCF_INST == 0 { return; }
    cxs[s].flags2 = cxs[s].flags2 | CF2_QUEUED | CF2_LAZY_BODY;
    inst_work.push(s as! u32);
}

recursive fn inst_var_def(s: i64) {
    let p = pattern_member(s);
    if p < 0 || cxs[p].odef < 0 { return; }
    let hdr = cxs[p].odef as i64;
    let pat, pargs = inst_args_of(cxs[s].dscope as i64);
    if pat < 0 { return; }
    let mark = nscratch.len;
    let st = inst_enter(true);
    bind_header(hdr, pargs);
    cur_scope = tmpls[hdr].scope as i64;
    pc = tmpls[hdr].t0 as i64;
    parse_simple_decl(DC_NS);
    let bad = inst_leave(st);
    if bad { cxs[s].flags2 = cxs[s].flags2 | CF2_DIRTY; }
    take_defs(mark);
}

// After deduction: do partial specialization pt's arguments, substituted
// with its parameters' bindings, give args? Substitution failures (an
// alias template's unused argument such as void_t<typename T::x>,
// enable_if_t<false>) and non-deduced contexts (typename T::x) are checked
// by parsing the argument list again (C++ [temp.class.spec.match]p2-3).
recursive fn spec_args_check(pt: i64, binds: i32, args: i32) -> bool {
    let t0 = tmpls[pt].sargs_t as i64;
    if t0 <= 0 || !spec_args_need_check(pt, t0) { return true; }
    let l = subst_parse(pt, binds, t0, 2, 0);
    if subst_failed || subst_list < 0 { return false; }
    let prim = tmpls[pt].primary as i64;
    let full = if prim >= 0 && tmpls[prim].kind as i64 == TT_CLASS { complete_args(prim, subst_list) } else { subst_list };
    if full == args { return true; }
    if args_dependent(full) || tl_count(full as i64) != tl_count(args as i64) { return true; }
    for i in tl_count(args as i64) {
        let a = tl_arg(args as i64, i);
        let b = tl_arg(full as i64, i);
        if a.kind != b.kind { return false; }
        if a.kind as i64 == TA_TYPE {
            if a.ty != b.ty && !(is_opaque(a.ty) || is_opaque(b.ty)) { return false; }
        } else if a.kind as i64 == TA_VALUE {
            if a.v != b.v && a.ty != 0 && b.ty != 0 && !is_opaque(a.ty) && !is_opaque(b.ty) && !is_dep(a.ty) && !is_dep(b.ty) { return false; }
        } else if a.kind as i64 == TA_TEMPLATE {
            if a.v != b.v { return false; }
        }
    }
    return true;
}

// Does the argument list at token t0 (its '<') have parts deduction does
// not check: qualified names, decltype, nested template-ids (alias
// templates), expressions?
fn spec_args_need_check(pt: i64, t0: i64) -> bool {
    var j = t0 + 1;
    var depth = 1;
    loop {
        let k = tu_toks[j].kind as i64;
        if k == TK_EOF { return false; }
        if k == TK_LESS { depth++; }
        else if k == TK_GREATER { depth--; if depth == 0 { return false; } }
        else if k == TK_GREATERGREATER { depth -= 2; if depth <= 0 { return depth < 0; } }
        if k == TK_COLONCOLON || k == TK_LESS || k == TK_KW + KW_DECLTYPE || k == TK_KW + KW_SIZEOF { return true; }
        j++;
    }
    return false;
}

// clang's wording of what is instantiated: "template class 'X<int>'",
// "function template specialization 'f<int>'", "member function 'X<int>::f'".
fn inst_what_text(o: u8[>..]&, s: i64) {
    let k = syms[s].kind as i64;
    if k == SK_TAG {
        o.append("template class '");
        cx_type_text(o, syms[s].ty);
        o.push('\'');
        return;
    }
    if k == SK_FUNC && cxs[s].flags2 & CF2_FSPEC != 0 {
        o.append("function template specialization '");
        cx_scope_prefix(o, cxs[s].dscope as i64);
        o.append(ident_text(syms[s].name as i64));
        if cxs[s].targs >= 0 { cx_targs_text(o, cxs[s].targs as i64); }
        o.push('\'');
        return;
    }
    if k == SK_FUNC {
        o.append(if cxs[s].flags & CF_MEMBER != 0 { "member function '" } else { "function '" });
        cx_scope_prefix(o, cxs[s].dscope as i64);
        o.append(ident_text(syms[s].name as i64));
        o.push('\'');
        return;
    }
    if k == SK_VAR {
        o.append("static data member '");
        cx_scope_prefix(o, cxs[s].dscope as i64);
        o.append(ident_text(syms[s].name as i64));
        o.push('\'');
        return;
    }
    o.push('\'');
    o.append(ident_text(syms[s].name as i64));
    o.push('\'');
}

// ---------------------------------------------------------------------------
// Member classes of class templates defined out of their class
// (template<class T> class X<T>::Inner { ... }): the instantiation's
// member class declared by `class Inner;` is pending until it is needed
// complete, then the pattern's out-of-line definition is parsed again as
// its body with the enclosing arguments bound.

var member_cls = dictionary<u64, u32> {};

fn member_class_declared(s: i64) {
    if !is_record(syms[s].ty) { return; }
    let r = rec_of(syms[s].ty);
    let sc = crecs[r].scope as i64;
    if sc < 0 || records[r].flags & RF_COMPLETE != 0 { return; }
    member_cls.insert(r as u64, 1);
    scopes[sc].flags = scopes[sc].flags | SCF_INST_PENDING as! u8;
}

recursive fn inst_member_class(r: i64) {
    let sc = crecs[r].scope as i64;
    scopes[sc].flags = scopes[sc].flags & ~(SCF_INST_PENDING as! u8);
    member_cls.remove(r as u64);
    let cs = crecs[r].sym as i64;
    if cs < 0 { return; }
    let p = pattern_member(cs);
    if p < 0 || cxs[p].odef < 0 { return; }
    let hdr = cxs[p].odef as i64;
    if tmpls[hdr].t0 == 0 { return; }
    let pat, pargs = inst_args_of(cxs[cs].dscope as i64);
    if pat < 0 { return; }
    let w = tmpl_class_key(hdr);
    inst_what = cs;
    let st = inst_enter(true);
    bind_header(hdr, pargs);
    cur_scope = sc;
    pc = class_head_end(hdr);
    records[r].pack = pack_now();
    parse_class_body(r, w);
    let bad = inst_leave(st);
    if bad { inst_dirty.insert(r as u64, 1); }
}
