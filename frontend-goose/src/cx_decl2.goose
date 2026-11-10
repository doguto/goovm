// goosecc D1: C++ simple-declarations and what they declare (typedefs,
// functions and their redeclarations, variables, data members,
// bit-fields), namespaces, using-declarations and -directives, alias
// declarations, linkage specifications, static_assert, and the
// translation unit.

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
import .cx_layout;
import .cx_mangle;

var extern_c: bool = false;     // inside extern "C"
var fdefs_extra: u32[>..] = [];  // N_FUNCDEF of member functions parsed out of their place (local classes)
var fn_params = dictionary<u64, u64> {};   // function symbol -> (params start << 32 | count) in nlist

// The name a declarator declares under (scope keys): constructors,
// destructors, operators and conversion functions have fixed names.
fn decl_key(d: CD&, ctor: bool) -> u32 {
    let k = d.qn.kind as i64;
    if ctor { return id_ctor; }
    if k == QK_DTOR { return id_dtor; }
    if k == QK_OP { return op_ids[d.qn.op]; }
    if k == QK_CONV { return id_conv; }
    return d.qn.name;
}

// Is the declarator a constructor of the class whose scope is cls?
fn is_ctor_decl(d: CD&, cls: i64) -> bool {
    if d.qn.kind as i64 != QK_IDENT || cls < 0 { return false; }
    if scopes[cls].kind as i64 != CS_CLASS { return false; }
    return d.qn.name == scopes[cls].name && d.is_fn;
}

// Same parameters and method qualifiers (a redeclaration, not an overload)?
fn same_signature(a: u32, b: u32) -> bool {
    if a == b { return true; }
    if kind_of(a) != TY_FUNC || kind_of(b) != TY_FUNC { return false; }
    let ta = types[a >> 4];
    let tb = types[b >> 4];
    if ta.n != tb.n || ta.flags != tb.flags { return false; }
    for i in ta.n {
        let pa = tparams[ta.extra + i];
        let pb = tparams[tb.extra + i];
        if pa != pb && !(has_unknown(pa) && has_unknown(pb)) { return false; }
    }
    return true;
}

recursive fn has_unknown(t: u32) -> bool {
    let k = kind_of(t);
    if k == TY_UNKNOWN || k == TY_DEPEXPR { return true; }
    if k == TY_POINTER || k == TY_LREF || k == TY_RREF || k == TY_ARRAY { return has_unknown(tbase(t)); }
    return false;
}

// A function of the same name and signature declared in scope sc, or -1.
fn find_redecl(sc: i64, name: u32, ft: u32) -> i64 {
    var s = scope_find(sc, name);
    while s >= 0 {
        if syms[s].kind as i64 == SK_FUNC && same_signature(syms[s].ty, ft) { return s; }
        s = cxs[s].nnext as i64;
    }
    return -1;
}

// The class scope the current declaration is a member of, if any.
fn member_scope(d: CD&, ctx: i64) -> i64 {
    if d.qn.qual {
        if d.qn.scope >= 0 && scopes[d.qn.scope].kind as i64 == CS_CLASS { return d.qn.scope as i64; }
        return -1;
    }
    if ctx == DC_CLASS { return cur_class; }
    return -1;
}

// Declares the function d (or a redeclaration of it). Returns its symbol.
recursive fn declare_function(d: CD&, ds: CDS&, a: Attrs&, ctx: i64) -> i64 {
    let loc = d.loc;
    var target = cur_scope;
    var is_member = false;
    if d.qn.qual {
        if d.qn.scope >= 0 { target = d.qn.scope as i64; }
        else { target = -1; }
    } else if ctx == DC_FRIEND {
        target = enclosing_ns(cur_scope);
    } else if ctx == DC_BLOCK {
        target = -2;    // a block-scope declaration: bound locally, filed in the namespace
    }
    if target >= 0 && scopes[target].kind as i64 == CS_CLASS && ctx != DC_FRIEND { is_member = true; }
    let cls = if is_member { target } else { -1 };
    let ctor = is_ctor_decl(d, cls) || (d.qn.qual && cls >= 0 && d.qn.kind as i64 == QK_IDENT && d.qn.name == scopes[cls].name);
    let key = decl_key(d, ctor);
    var ft = d.ty;
    // a template?
    let tmpl = pending_tmpl;
    if inst_spec_tmpl >= 0 {
        // D2: a function template specialization's declaration
        return make_fspec(d, ds, key, ft, ctor, is_member, loc);
    }
    if tmpl >= 0 && (target >= 0 || target == -2) && !d.qn.qual {
        let fs = if target == -2 { enclosing_ns(cur_scope) } else { target };
        let old = find_fn_template(fs, key, ft, tmpl);
        if old >= 0 {
            // D2: a redeclaration of a function template (its definition, maybe)
            let ot = cxs[old].tmpl as i64;
            merge_tmpl_defaults(ot, tmpl);
            pending_tmpl = -1;
            tmpls[tmpl].kind = TT_FUNC as! u8;
            tmpls[tmpl].sym = old as! i32;
            if at(TK_L_BRACE) || at(TK_COLON) || at_kw(KW_TRY) { tmpls[ot].def_t = tmpl as! i32; }
            return tmpls[ot].pattern as i64;
        }
        let ts = func_template_sym(key, fs, loc);
        let pf = csym(SK_FUNC, key, ft, loc);
        cxs[pf].flags = (CF_PATTERN | (if is_member { CF_MEMBER } else { 0 })) as! u32;
        cxs[pf].dscope = fs as! i32;
        cxs[pf].tmpl = cxs[ts].tmpl;
        tmpls[cxs[ts].tmpl].pattern = pf as! i32;
        set_fn_flags(pf, d, ds, ctor, is_member);
        note_params(pf, d);
        return pf;
    }
    if tmpl >= 0 && d.qn.qual && target >= 0 {
        // D2: a member template defined out of its class
        let old = find_fn_template(target, key, ft, tmpl);
        if old >= 0 {
            pending_tmpl = -1;
            let ot = cxs[old].tmpl as i64;
            tmpls[tmpl].kind = TT_FUNC as! u8;
            tmpls[tmpl].sym = old as! i32;
            if at(TK_L_BRACE) || at(TK_COLON) || at_kw(KW_TRY) { tmpls[ot].def_t = tmpl as! i32; }
            return tmpls[ot].pattern as i64;
        }
    }
    if tmpl >= 0 { pending_tmpl = -1; }
    if inst_def_target >= 0 {
        // D2: the definition of an instantiated member (or specialization) parsed again
        let s0 = inst_def_target;
        inst_def_target = -1;
        note_params(s0, d);
        return s0;
    }
    var s: i64 = -1;
    if target >= 0 {
        s = find_redecl(target, key, ft);
        if s < 0 && d.qn.qual && cls >= 0 {
            // an out-of-line definition: match by name and parameter count
            // when the types D1 computed differ (opaque parameter types)
            s = find_by_arity(target, key, ft);
        }
    } else if target == -2 {
        let fs = enclosing_ns(cur_scope);
        s = find_redecl(fs, key, ft);
    }
    let created = s < 0;
    if s < 0 {
        s = csym(SK_FUNC, key, ft, loc);
        if target >= 0 { scope_add(target, s); }
        else if target == -2 {
            let fs = enclosing_ns(cur_scope);
            scope_add(fs, s);
            bind_sym(s, false);
        } else {
            cxs[s].dscope = -1;
            cxs[s].flags = cxs[s].flags | CF_PATTERN;
        }
        if is_member { cxs[s].access = cur_access as! u8; }
        if is_member && ctx == DC_CLASS { cmscratch.push(s as! u32); }
    } else if target == -2 {
        bind_sym(s, false);
    }
    set_fn_flags(s, d, ds, ctor, is_member || cxs[s].flags & CF_MEMBER != 0);
    note_main_decl(s, d);
    if d.qn.has_targs {
        // an explicit specialization of a function template (f<int>(...)):
        // a template entity in D1 (not lowered, not in the oracles)
        cxs[s].flags = cxs[s].flags | CF_SPEC | CF_PATTERN;
    }
    if ctx == DC_FRIEND && cxs[s].flags & CF_MEMBER == 0 && created {
        cxs[s].flags = cxs[s].flags | CF_FRIEND;
        if cur_class >= 0 { friend_class.insert(s as u64, cur_class as u32); }
    } else if ctx != DC_FRIEND && cxs[s].flags & CF_FRIEND != 0 {
        // declared at namespace scope too: found by ordinary lookup
        cxs[s].flags = cxs[s].flags & ~(CF_FRIEND as! u32);
    }
    if extern_c && !is_member && cxs[s].flags & CF_MEMBER == 0 { cxs[s].flags = cxs[s].flags | CF_EXTERN_C; }
    if dependent_ctx() || (target >= 0 && scopes[target].flags & SCF_PATTERN != 0) { cxs[s].flags = cxs[s].flags | CF_PATTERN; }
    if target >= 0 && scopes[target].flags & SCF_INST != 0 && cxs[s].flags & CF_PATTERN == 0 && !d.qn.qual {
        // D2: a member of an instantiation: defined in its class or out of it, instantiated on use
        cxs[s].flags2 = cxs[s].flags2 | CF2_LAZY_BODY;
    }
    if tmpl >= 0 && d.qn.qual && target >= 0 && scopes[target].flags & SCF_PATTERN != 0 && (at(TK_L_BRACE) || at(TK_COLON) || at_kw(KW_TRY)) {
        // D2: a member of a class template defined out of its class
        cxs[s].odef = tmpl as! i32;
    }
    record_attrs(s, a, 0);
    note_params(s, d);
    return s;
}
var inst_def_target: i64 = -1;  // D2: the function whose definition is being parsed again

// D2: the function template named `name` in scope sc whose pattern has the
// type ft and the template header of hdr's kinds, -1.
fn find_fn_template(sc: i64, name: u32, ft: u32, hdr: i64) -> i64 {
    var s = scope_find(sc, name);
    while s >= 0 {
        if syms[s].kind as i64 == SK_TEMPLATE && cxs[s].tmpl >= 0 && tmpls[cxs[s].tmpl].kind as i64 == TT_FUNC {
            let t = cxs[s].tmpl as i64;
            let pf = tmpls[t].pattern as i64;
            if pf >= 0 && tmpls[t].nparams == tmpls[hdr].nparams && same_header(t, hdr) && types_equiv(syms[pf].ty, ft, t, hdr) { return s; }
        }
        s = cxs[s].nnext as i64;
    }
    return -1;
}

// Are a and b the same type, as declared under template headers ha and hb
// (C++ [temp.over.link]: decltype expressions compared token by token,
// template parameters by position)?
recursive fn types_equiv(a: u32, b: u32, ha: i64, hb: i64) -> bool {
    if a == b { return true; }
    if quals(a) != quals(b) { return false; }
    let k = kind_of(a);
    if k != kind_of(b) { return false; }
    if k == TY_DEPEXPR { return tokens_equiv(types[a >> 4].n, types[b >> 4].n, ha, hb); }
    if k == TY_POINTER || k == TY_LREF || k == TY_RREF || k == TY_PACKEXP { return types_equiv(tbase(a), tbase(b), ha, hb); }
    if k == TY_ARRAY { return types[a >> 4].n == types[b >> 4].n && types_equiv(tbase(a), tbase(b), ha, hb); }
    if k == TY_FUNC {
        let fa = types[a >> 4];
        let fb = types[b >> 4];
        if fa.n != fb.n || fa.flags != fb.flags { return false; }
        if !types_equiv(fa.base, fb.base, ha, hb) { return false; }
        for i in fa.n { if !types_equiv(tparams[fa.extra + i], tparams[fb.extra + i], ha, hb) { return false; } }
        return true;
    }
    if k == TY_DEPNAME {
        if types[a >> 4].extra != types[b >> 4].extra || types[a >> 4].n != types[b >> 4].n { return false; }
        return types_equiv(tbase(a), tbase(b), ha, hb);
    }
    if k == TY_DEPSPEC {
        let la = types[a >> 4].n;
        let lb = types[b >> 4].n;
        if types[a >> 4].extra != types[b >> 4].extra || tl_count(la) != tl_count(lb) { return false; }
        for i in tl_count(la) {
            let x = tl_arg(la, i);
            let y = tl_arg(lb, i);
            if x.kind != y.kind { return false; }
            if x.ty != 0 || y.ty != 0 { if !types_equiv(x.ty, y.ty, ha, hb) { return false; } }
            if x.kind as i64 != TA_TYPE && x.v != y.v && kind_of(x.ty) != TY_DEPEXPR { return false; }
        }
        return true;
    }
    return false;
}

// The tokens of the parenthesized operands starting at token pa and pb
// (decltype( ... )) are the same, template parameter names mapped by position.
fn tokens_equiv(pa: i64, pb: i64, ha: i64, hb: i64) -> bool {
    var i = pa;
    var j = pb;
    var depth = 0;
    var n = 0;
    loop {
        if i >= tu_toks.len || j >= tu_toks.len { return false; }
        let x = tu_toks[i];
        let y = tu_toks[j];
        if x.kind != y.kind { return false; }
        let k = x.kind as i64;
        if k == TK_IDENT && x.val != y.val {
            let ia = tparam_index(ha, x.val);
            if ia < 0 || ia != tparam_index(hb, y.val) { return false; }
        } else if (k == TK_NUMBER || k == TK_STRING || k == TK_CHAR) && src[x.spell..x.spell + x.val] != src[y.spell..y.spell + y.val] { return false; }
        if k == TK_L_PAREN { depth++; }
        if k == TK_R_PAREN { depth--; if depth == 0 && n > 0 { return true; } }
        if k == TK_EOF { return false; }
        i++;
        j++;
        n++;
    }
    return false;
}

fn tparam_index(h: i64, name: u32) -> i64 {
    if h < 0 { return -1; }
    for i in tmpls[h].nparams as i64 { if tps[tmpls[h].params as i64 + i].name == name { return i; } }
    return -1;
}

fn same_header(a: i64, b: i64) -> bool {
    for i in tmpls[a].nparams as i64 {
        let x = tps[tmpls[a].params as i64 + i];
        let y = tps[tmpls[b].params as i64 + i];
        if x.kind != y.kind || x.pack != y.pack { return false; }
        if x.kind as i64 == TPK_VALUE && unqual(x.ty) != unqual(y.ty) { return false; }
    }
    return true;
}

fn find_by_arity(sc: i64, name: u32, ft: u32) -> i64 {
    var s = scope_find(sc, name);
    var found: i64 = -1;
    var count = 0;
    while s >= 0 {
        if syms[s].kind as i64 == SK_FUNC && kind_of(syms[s].ty) == TY_FUNC && types[syms[s].ty >> 4].n == types[ft >> 4].n {
            found = s;
            count++;
        }
        s = cxs[s].nnext as i64;
    }
    if count == 1 { return found; }
    return -1;
}

fn set_fn_flags(s: i64, d: CD&, ds: CDS&, ctor: bool, member: bool) {
    var f = cxs[s].flags;
    if member { f = f | CF_MEMBER; }
    if ctor { f = f | CF_CTOR; }
    let k = d.qn.kind as i64;
    if k == QK_DTOR { f = f | CF_DTOR; }
    if k == QK_CONV { f = f | CF_CONV; }
    if k == QK_OP { f = f | CF_OPERATOR; cxs[s].op = d.qn.op; }
    if ds.is_virtual { f = f | CF_VIRTUAL; }
    if ds.is_explicit { f = f | CF_EXPLICIT; }
    if ds.is_constexpr { f = f | CF_CONSTEXPR; }
    if (d.fquals as i64) & TF_MCONST != 0 { f = f | CF_CONST; }
    if member && ds.sc == SC_STATIC { f = f | CF_STATIC; }
    if d.pure { f = f | CF_PURE | CF_VIRTUAL; }
    if d.deleted { f = f | CF_DELETED; }
    if d.defaulted { f = f | CF_DEFAULTED; }
    if d.noexcept { f = f | CF_NOEXCEPT; }
    if d.excspec != 0 { note_excspec(s, d.excspec as i64, d.excpos as i64); }
    if d.virt == 1 { f = f | CF_OVERRIDE; }
    if d.virt == 2 { f = f | CF_FINAL; }
    cxs[s].flags = f;
    if ds.is_inline || ds.is_constexpr { syms[s].flags = syms[s].flags | SF_INLINE; }
    if !member && ds.sc == SC_STATIC { syms[s].sc = SC_STATIC as! u8; }
    if ds.noreturn { syms[s].flags = syms[s].flags | SF_NORETURN; }
}

// Notes a declaration whose name is written in the main file (the
// declaration oracle lists those, as libclang's isWrittenInMainFile).
fn note_main_decl(s: i64, d: CD&) {
    if !d.has_name { return; }
    let t = tu_toks[d.qn.start];
    // libclang's isWrittenInMainFile: not from a macro expansion or argument
    // a name substituted for a macro parameter keeps its spelling; the
    // token after it then comes from the macro's body
    let nx = tu_toks[d.qn.start as i64 + 1];
    let from_arg = !d.qn.qual && (nx.flags & F_MACRO != 0 || nx.xloc != nx.spell) && nx.kind as i64 != TK_EOF;
    if t.flags & F_MACRO == 0 && t.xloc == t.spell && !from_arg && file_of(t.spell as i64) == main_file_idx {
        cxs[s].flags = cxs[s].flags | CF_MAINDECL;
    }
    if cxs[s].pos as i64 > d.qn.start as i64 && syms[s].kind as i64 != SK_FUNC { cxs[s].pos = d.qn.start; }
}

// Keeps the parameters of a function's latest declaration (with the
// default arguments of earlier ones).
fn note_params(s: i64, d: CD&) {
    if d.params < 0 { return; }
    let g = fn_params.get(s as u64);
    if g {
        let ostart = (g >> 32) as i64;
        let on = (g & 0xFFFFFFFF) as i64;
        if on == d.nparams {
            for i in on {
                let op = nlist[ostart + i] as i64;
                let np = nlist[d.params + i] as i64;
                if cxs[np].body == 0 && cxs[op].body != 0 { cxs[np].body = cxs[op].body; cxs[np].body_end = cxs[op].body_end; }
            }
        }
    }
    fn_params.insert(s as u64, ((d.params as u64) << 32) | (d.nparams as u64));
}

fn fn_param_list(s: i64) -> i64, i64 {
    let g = fn_params.get(s as u64);
    if g { return (g >> 32) as i64, (g & 0xFFFFFFFF) as i64; }
    return -1, 0;
}

// A typedef / alias declaration.
fn declare_typedef(name: u32, ty: u32, loc: u32, ctx: i64) -> i64 {
    let s = csym(SK_TYPEDEF, name, ty, loc);
    syms[s].sc = SC_TYPEDEF;
    if ctx == DC_BLOCK || ctx == DC_COND {
        cxs[s].dscope = cur_scope as! i32;
        bind_sym(s, false);
    } else {
        scope_add(cur_scope, s);
        if ctx == DC_CLASS { cxs[s].access = cur_access as! u8; cxs[s].flags = CF_MEMBER; }
    }
    return s;
}

// The body of a function definition at pc ('{', ':' ctor-initializer,
// `try`, or = default / = delete handled by the caller): parsed now, or
// its tokens kept (class members, templates).
recursive fn function_body(s: i64, d: CD&, in_class: bool) {
    let b0 = pc;
    if inst_spec_decl {
        // D2: a specialization's declaration: the body is parsed when it is used
        skip_fn_body();
        return;
    }
    if inst_body_now {
        // D2: an instantiated definition
        inst_body_now = false;
        syms[s].flags = syms[s].flags | SF_DEFINED;
        let sv_scope0 = cur_scope;
        if d.qn.qual && d.qn.scope >= 0 { cur_scope = d.qn.scope as i64; }
        let n0 = parse_function_body(s, d.params, d.nparams);
        cur_scope = sv_scope0;
        if n0 != 0 { nscratch.push(n0); }
        return;
    }
    if in_class { cxs[s].flags = cxs[s].flags | CF_DEFINED_IN_CLASS; }
    let pattern = cxs[s].flags & CF_PATTERN != 0 || dependent_ctx() || (d.qn.qual && d.qn.dep != 0);
    if in_class || pattern {
        skip_fn_body();
        cxs[s].body = b0 as! u32;
        cxs[s].body_end = pc as! u32;
        cxs[s].flags = cxs[s].flags | CF_HAS_BODY_LATER;
        syms[s].flags = syms[s].flags | SF_DEFINED;
        if in_class && !pattern && cur_class >= 0 && scopes[cur_class].flags & SCF_INST != 0 {
            // D2: a member of an instantiation: its body is instantiated on use
            cxs[s].flags2 = cxs[s].flags2 | CF2_LAZY_BODY;
            if cxs[s].dscope as i64 != cur_class { friend_scope.insert(s as u64, cur_class as u32); }
            return;
        }
        if in_class && !pattern && cur_class >= 0 {
            deferred.push(s as! u32);
            deferred.push(cur_class as! u32);
        }
        return;
    }
    syms[s].flags = syms[s].flags | SF_DEFINED;
    // the body of a member (or namespace member) defined outside its scope
    // sees that scope
    let sv_scope = cur_scope;
    if d.qn.qual && d.qn.scope >= 0 { cur_scope = d.qn.scope as i64; }
    let n = parse_function_body(s, d.params, d.nparams);
    cur_scope = sv_scope;
    if n != 0 { nscratch.push(n); }
}

// Skips a function body: ctor-initializers, the compound statement, the
// handlers of a function-try-block.
fn skip_fn_body() {
    var is_try = false;
    if at_kw(KW_TRY) { adv(); is_try = true; }
    if at(TK_COLON) {
        adv();
        loop {
            // a mem-initializer-id: a (qualified) name, maybe with template arguments
            loop {
                let k = tk();
                if k == TK_IDENT || k == TK_COLONCOLON || k == TK_KW + KW_TEMPLATE || k == TK_KW + KW_DECLTYPE {
                    if k == TK_KW + KW_DECLTYPE { adv(); if at(TK_L_PAREN) { skip_group(); } continue; }
                    adv();
                    if at(TK_LESS) { skip_angles(); }
                    continue;
                }
                break;
            }
            if at(TK_L_PAREN) || at(TK_L_BRACE) { skip_group(); } else { break; }
            accept(TK_ELLIPSIS);
            if !accept(TK_COMMA) { break; }
        }
    }
    if at(TK_L_BRACE) { skip_group(); }
    if is_try {
        while at_kw(KW_CATCH) {
            adv();
            if at(TK_L_PAREN) { skip_group(); }
            if at(TK_L_BRACE) { skip_group(); }
        }
    }
}

// Skips < ... > (balanced, parentheses skipped as groups).
fn skip_angles() {
    var depth = 0;
    loop {
        let k = tk();
        if k == TK_EOF || k == TK_SEMI || k == TK_L_BRACE || k == TK_R_BRACE { return; }
        if k == TK_L_PAREN || k == TK_L_SQUARE { skip_group(); continue; }
        if k == TK_LESS { depth++; }
        if k == TK_GREATER { depth--; }
        if k == TK_GREATERGREATER { depth -= 2; }
        adv();
        if depth <= 0 { return; }
    }
}

// ---------------------------------------------------------------------------
// Declarations.

// A declaration at namespace or block scope (or a member: parse_member_decl).
recursive fn parse_decl_cx(ctx: i64) {
    if accept(TK_SEMI) { return; }
    if at_kw(KW_NAMESPACE) || (at_kw(KW_INLINE) && tk_n(1) == TK_KW + KW_NAMESPACE) { parse_namespace(); return; }
    if at_kw(KW_USING) { parse_using(ctx); return; }
    if at_kw(KW_TEMPLATE) { parse_template_decl(ctx); return; }
    if at_kw(KW_EXTERN) && tk_n(1) == TK_KW + KW_TEMPLATE {
        // extern template ...: an explicit instantiation declaration (no effect in D1)
        adv();
        parse_template_decl(ctx);
        return;
    }
    if at_kw(KW_EXTERN) && tk_n(1) == TK_STRING { parse_linkage_spec(ctx); return; }
    if at_kw(KW_STATIC_ASSERT) { parse_static_assert_cx(); return; }
    if at_kw(KW_EXPORT) { adv(); parse_decl_cx(ctx); return; }
    if at_kw(KW_ASM) && ctx == DC_NS {
        let loc = tloc();
        adv();
        expect(TK_L_PAREN, "'('");
        var s: u32 = 0;
        if at(TK_STRING) { s = string_literal(); }
        expect(TK_R_PAREN, "')'");
        expect(TK_SEMI, "';'");
        nscratch.push(node(N_ASM, 8, 0, s as i64, 0, 0, loc));
        return;
    }
    if at_kw(KW_EXTENSION) { adv(); parse_decl_cx(ctx); return; }
    parse_simple_decl(ctx);
}

// decl-specifiers, then init-declarators or a function definition.
recursive fn parse_simple_decl(ctx0: i64) {
    let ctx = ctx0;
    var a = Attrs { .. };
    cx_attrs(a);
    if deduction_guide_ahead() {
        // template<...> X(args) -> X<...>; : a deduction guide (no effect in D1)
        if pending_tmpl >= 0 { pending_tmpl = -1; }
        skip_to(TK_SEMI);
        expect(TK_SEMI, "';'");
        return;
    }
    var ds = CDS { .. };
    parse_cds(ds, a, if ctx == DC_FRIEND { DC_CLASS } else { ctx });
    let base0 = finish_cds(ds);
    if at(TK_SEMI) {
        adv();
        if !ds.any { return; }
        // struct X { ... }; enum E { ... }; class X; friend class X;
        if pending_tmpl >= 0 { pending_tmpl = -1; }
        if ds.tag_def && ctx == DC_CLASS && is_record(base0) && records[rec_of(base0)].name == 0 {
            // an anonymous struct or union member
            anon_member(base0);
        } else if ds.tag_def && ctx != DC_CLASS && is_record(base0) && records[rec_of(base0)].name == 0 && is_anon_union_obj(base0) {
            anon_union_obj(base0, ctx);
        }
        return;
    }
    var first = true;
    loop {
        var d = CD { .. };
        let dloc = tloc();
        if ctx == DC_CLASS && at(TK_COLON) {
            // an unnamed bit-field
            adv();
            let e = parse_cexpr();
            let ok, w = const_int(e);
            if base0 != 0 { add_field(0, base0, if ok { w } else { 1 }, dloc, a); }
            if !accept(TK_COMMA) { break; }
            continue;
        }
        var base = base0;
        if base == 0 { base = t_int; }
        let sv_init = init_ok;
        init_ok = (ctx == DC_NS || ctx == DC_BLOCK || ctx == DC_COND) && ds.sc != SC_TYPEDEF;
        parse_cdeclr(if base0 == 0 { t_void } else { base }, 0, d);
        init_ok = sv_init;
        if base0 == 0 && !no_type_ok(d, ctx) {
            error_at((if d.qn.loc != 0 { d.qn.loc } else { dloc }) as i64, "a type specifier is required for all declarations");
        }
        if d.qn.kind as i64 == QK_CONV && is_func(d.ty) { d.ty = func_with_ret(d.ty, d.qn.conv); }
        cx_attrs(a);
        parse_asm_label_cx(a);
        cx_attrs(a);
        // virt-specifiers, pure-specifier, = default / = delete
        loop {
            if at(TK_IDENT) && tu_toks[pc].val == id_override { d.virt = 1; adv(); continue; }
            if at(TK_IDENT) && tu_toks[pc].val == id_final && d.is_fn { d.virt = 2; adv(); continue; }
            break;
        }
        if d.is_fn && is_func(d.ty) && at(TK_EQUAL) {
            if tk_n(1) == TK_NUMBER && tk_n(2) != TK_L_PAREN { adv(); adv(); d.pure = true; }
            else if tk_n(1) == TK_KW + KW_DEFAULT { adv(); adv(); d.defaulted = true; }
            else if tk_n(1) == TK_KW + KW_DELETE { adv(); adv(); d.deleted = true; }
        }
        if ds.sc == SC_TYPEDEF {
            if pending_tmpl >= 0 { pending_tmpl = -1; }
            if d.qn.name != 0 { declare_typedef(d.qn.name, apply_type_attrs(d.ty, a, dloc), dloc, ctx); }
        } else if is_func(d.ty) && (d.is_fn || !is_opaque(d.ty)) && !(ctx == DC_BLOCK && !first_paren_decl(d)) {
            if pending_inst {
                // an explicit instantiation of a function template: nothing in D1
                if !accept(TK_COMMA) { break; }
                continue;
            }
            let s = declare_function(d, ds, a, ctx);
            if first && (at(TK_L_BRACE) || at(TK_COLON) || at_kw(KW_TRY)) {
                syms[s].loc = d.loc;
                function_body(s, d, ctx == DC_CLASS || ctx == DC_FRIEND);
                return;
            }
        } else if ctx == DC_CLASS && ds.sc != SC_STATIC && !d.qn.qual {
            // a data member (maybe a bit-field), with its default member initializer
            var width: i64 = -1;
            if at(TK_COLON) {
                adv();
                let e = parse_cexpr_noGT_init();
                let ok, w = const_int(e);
                width = if ok { w } else { 1 };
            }
            if d.qn.name != 0 || width >= 0 {
                let fs = add_field(d.qn.name, apply_type_attrs(d.ty, a, dloc), width, dloc, a);
                if ds.is_mutable && fs >= 0 { cxs[fs].flags = cxs[fs].flags | CF_MUTABLE; }
                if (at(TK_EQUAL) || at(TK_L_BRACE)) && fs >= 0 {
                    if accept(TK_EQUAL) {}
                    cxs[fs].body = pc as! u32;
                    if at(TK_L_BRACE) { skip_group(); } else { skip_expr(); }
                    cxs[fs].body_end = pc as! u32;
                }
            }
        } else {
            let s = declare_var(d, ds, a, ctx);
            if s >= 0 { note_main_decl(s, d); parse_var_init(s, d, ctx); }
        }
        first = false;
        if !accept(TK_COMMA) { break; }
    }
    if pending_tmpl >= 0 { pending_tmpl = -1; }
    expect(TK_SEMI, "';'");
}

// [explicit] X ( ... ) -> where X names a class template.
// A declarator without decl-specifier types is valid only for constructors,
// destructors and conversion functions (C++ [dcl.type]/2).
fn no_type_ok(d: CD&, ctx: i64) -> bool {
    let k = d.qn.kind as i64;
    if k == QK_DTOR || k == QK_CONV { return true; }
    if d.qn.dep != 0 || (d.qn.qual && d.qn.scope < 0) { return true; }
    if k != QK_IDENT || !d.is_fn { return false; }
    let cls = member_scope(d, ctx);
    if cls >= 0 && scopes[cls].kind as i64 == CS_CLASS { return d.qn.name == scopes[cls].name; }
    // friend X::X() resolved elsewhere; a namespace-scope declaration is not a constructor
    return false;
}

fn deduction_guide_ahead() -> bool {
    var j = pc;
    if tu_toks[j].kind as i64 == TK_KW + KW_EXPLICIT {
        j++;
        if tu_toks[j].kind as i64 == TK_L_PAREN { return false; }
    }
    if tu_toks[j].kind as i64 != TK_IDENT || tu_toks[j + 1].kind as i64 != TK_L_PAREN { return false; }
    let s = chain_nns_tmpl(unqual_lookup(tu_toks[j].val));
    if s < 0 || tmpl_kind(s) != TT_CLASS { return false; }
    // the matching ')' then '->'
    var k = j + 1;
    var depth = 0;
    loop {
        let kk = tu_toks[k].kind as i64;
        if kk == TK_EOF { return false; }
        if kk == TK_L_PAREN { depth++; }
        if kk == TK_R_PAREN { depth--; if depth == 0 { break; } }
        k++;
    }
    return tu_toks[k + 1].kind as i64 == TK_ARROW;
}

// In a block, `T f(args);` with args that are expressions declares a
// variable (C++'s most vexing parse goes the other way only when the
// parentheses can be a parameter list: parse_cdeclr already decided).
fn first_paren_decl(d: CD&) -> bool { true }

recursive fn parse_asm_label_cx(a: Attrs&) {
    if !at_kw(KW_ASM) { return; }
    adv();
    expect(TK_L_PAREN, "'('");
    if at(TK_STRING) {
        let s = string_literal();
        let sl = strs[nodes[s].a];
        a.asm_off = sl.start;
        a.asm_len = sl.len - 1;
    }
    expect(TK_R_PAREN, "')'");
}

// A non-static data member: a field of the class being defined, and its
// name in the class scope. Returns the member's symbol.
fn add_field(name: u32, ty: u32, width: i64, loc: u32, a: Attrs&) -> i64 {
    if cur_class < 0 { return -1; }
    let r = scopes[cur_class].rec as i64;
    let idx = cfscratch.len;
    var fl: u8 = 0;
    if a.misc & AM_PACKED != 0 { fl = fl | FF_PACKED; }
    cfscratch.push(Field { name: name, ty: ty, offset: 0, bitpos: 0, width: width as! i32, attr_align: a.aligned, flags: fl, rsv: 0, rsv2: 0, loc: loc });
    if width >= 0 { records[r].flags = records[r].flags | RF_HAS_BITFIELD; }
    if name == 0 { return -1; }
    let s = csym(SK_FIELD, name, ty, loc);
    syms[s].v = (idx - cur_fmark) as i64;     // the index among the class's fields
    cxs[s].flags = CF_MEMBER;
    cxs[s].access = cur_access as! u8;
    scope_add(cur_class, s);
    field_base.push(0);
    return s;
}
var field_base: u32[>..] = [];

// An anonymous struct or union member: a field of its type, its members
// visible in the enclosing class.
fn anon_member(t: u32) {
    var a = Attrs { .. };
    let fs = add_field(0, t, -1, tloc(), a);
    let ar = rec_of(t);
    cfscratch[cfscratch.len - 1].flags = cfscratch[cfscratch.len - 1].flags | FF_ANON;
    let asc = crecs[ar].scope as i64;
    // the anonymous class's members become names of the enclosing class
    for i in records[ar].count {
        let f = fields[records[ar].first + i];
        if f.name == 0 { continue; }
        let s = csym(SK_FIELD, f.name, f.ty, f.loc);
        syms[s].v = (cfscratch.len - 1 - cur_fmark) as i64;
        cxs[s].flags = CF_MEMBER | CF_ANON_PATH;
        cxs[s].target = (records[ar].first + i) as! i32;
        scope_add(cur_class, s);
    }
}
let CF_ANON_PATH = 536870912;   // a member of an anonymous struct/union member: cxs.target is the inner field

fn is_anon_union_obj(t: u32) -> bool { kind_of(t) == TY_UNION }

// static union { ... }; at namespace or block scope: an object whose
// members are names of the scope (C++ [class.union.anon]).
fn anon_union_obj(t: u32, ctx: i64) {
    let ar = rec_of(t);
    let s = csym(SK_VAR, 0, t, tloc());
    if ctx == DC_BLOCK { bind_sym(s, false); } else { scope_add(cur_scope, s); syms[s].flags = SF_FILESCOPE; syms[s].sc = SC_STATIC as! u8; }
    for i in records[ar].count {
        let f = fields[records[ar].first + i];
        if f.name == 0 { continue; }
        let m = csym(SK_FIELD, f.name, f.ty, f.loc);
        cxs[m].flags = CF_ANON_PATH;
        cxs[m].target = (records[ar].first + i) as! i32;
        cxs[m].vidx = s as! i32;
        if ctx == DC_BLOCK { bind_sym(m, false); } else { scope_add(cur_scope, m); }
    }
}

// A variable (or static data member, or its out-of-line definition).
var decl_is_extern: bool = false;    // the variable declaration being parsed says extern (code generation)
recursive fn declare_var(d: CD&, ds: CDS&, a: Attrs&, ctx: i64) -> i64 {
    decl_is_extern = ds.sc == SC_EXTERN;
    var ty = apply_type_attrs(d.ty, a, d.loc);
    // a constexpr variable is const (C++ [dcl.constexpr]p10)
    if ds.is_constexpr && !is_ref(ty) && !is_opaque(ty) { ty = with_q(ty, Q_CONST); }
    if ds.sc != SC_EXTERN && ctx != DC_CLASS && !is_ref(ty) && !dependent_ctx() { need_complete(ty); }
    if ctx != DC_NS { cur_init_prio = 65535; }
    let name = d.qn.name;
    if inst_var_tmpl >= 0 {
        // D2: a variable template specialization's declaration
        let vt = inst_var_tmpl;
        inst_var_tmpl = -1;
        pending_tmpl = -1;
        let s = csym(SK_VAR, name, ty, d.loc);
        syms[s].flags = SF_FILESCOPE | SF_INLINE;
        cxs[s].dscope = tmpls[vt].scope;
        cxs[s].flags = (CF_SPEC | (if ds.is_constexpr { CF_CONSTEXPR } else { 0 })) as! u32;
        if ctx == DC_CLASS { cxs[s].flags = cxs[s].flags | CF_MEMBER | CF_STATIC; }
        cxs[s].tmpl = vt as! i32;
        cxs[s].targs = inst_var_binds;
        inst_var_result = s;
        return s;
    }
    if (pending_tmpl >= 0 || pending_explicit) && d.qn.has_targs && !d.qn.qual {
        // D2: a partial or explicit specialization of a variable template
        let vs = var_template_of(name);
        if vs >= 0 {
            let vt = cxs[vs].tmpl as i64;
            if pending_tmpl >= 0 && args_dependent(d.qn.targs) {
                let pt = pending_tmpl;
                pending_tmpl = -1;
                tmpls[pt].kind = TT_VAR as! u8;
                tmpls[pt].sym = vs as! i32;
                tmpls[pt].spec_args = d.qn.targs;
                tmpls[pt].primary = vt as! i32;
                tmpls[vt].specs = link_add(tmpls[vt].specs, pt);
                let pv = csym(SK_VAR, name, ty, d.loc);
                cxs[pv].flags = CF_PATTERN;
                tmpls[pt].pattern = pv as! i32;
                return pv;
            }
            pending_tmpl = -1;
            let full = complete_args(vt, d.qn.targs);
            let s = csym(SK_VAR, name, ty, d.loc);
            syms[s].flags = SF_FILESCOPE;
            cxs[s].dscope = cur_scope as! i32;
            cxs[s].flags = (CF_SPEC | (if ds.is_constexpr { CF_CONSTEXPR } else { 0 })) as! u32;
            cxs[s].tmpl = vt as! i32;
            cxs[s].targs = full;
            if ds.is_inline || ds.is_constexpr { syms[s].flags = syms[s].flags | SF_INLINE; }
            var_specs.insert(((vt as u64) << 32) | (full as u64), s as! u32);
            return s;
        }
    }
    if pending_tmpl >= 0 {
        // a variable template (or a static data member of a class template)
        if !d.qn.qual {
            let t = pending_tmpl;
            pending_tmpl = -1;
            let ts = csym(SK_TEMPLATE, name, 0, d.loc);
            cxs[ts].tmpl = t as! i32;
            cxs[ts].flags = CF_TEMPLATE;
            tmpls[t].kind = TT_VAR as! u8;
            tmpls[t].sym = ts as! i32;
            scope_add(cur_scope, ts);
            let pv = csym(SK_VAR, name, ty, d.loc);
            cxs[pv].flags = CF_PATTERN;
            tmpls[t].pattern = pv as! i32;
            return pv;
        }
        if d.qn.qual && d.qn.scope >= 0 && scopes[d.qn.scope].flags & SCF_PATTERN != 0 {
            // D2: a static data member of a class template defined out of its class
            var s1 = scope_find(d.qn.scope as i64, name);
            while s1 >= 0 && syms[s1].kind as i64 != SK_VAR { s1 = cxs[s1].nnext as i64; }
            if s1 >= 0 { cxs[s1].odef = pending_tmpl as! i32; }
        }
        pending_tmpl = -1;
    }
    if pending_inst { return -1; }
    if d.qn.qual {
        // a static data member's definition (or a namespace member's)
        if d.qn.scope >= 0 {
            var s = scope_find(d.qn.scope as i64, name);
            while s >= 0 && syms[s].kind as i64 != SK_VAR { s = cxs[s].nnext as i64; }
            if s >= 0 {
                if !is_opaque(ty) { syms[s].ty = ty; }
                if dependent_ctx() { cxs[s].flags = cxs[s].flags | CF_PATTERN; }
                return s;
            }
            let ns = csym(SK_VAR, name, ty, d.loc);
            scope_add(d.qn.scope as i64, ns);
            syms[ns].flags = SF_FILESCOPE;
            if dependent_ctx() { cxs[ns].flags = cxs[ns].flags | CF_PATTERN; }
            return ns;
        }
        let ns = csym(SK_VAR, name, ty, d.loc);
        cxs[ns].flags = CF_PATTERN;
        return ns;
    }
    if ctx == DC_BLOCK || ctx == DC_COND {
        if ds.sc == SC_EXTERN {
            // a block-scope extern: the namespace's entity
            let fs = enclosing_ns(cur_scope);
            var s = scope_find(fs, name);
            while s >= 0 && syms[s].kind as i64 != SK_VAR { s = cxs[s].nnext as i64; }
            if s < 0 {
                s = csym(SK_VAR, name, ty, d.loc);
                scope_add(fs, s);
                syms[s].flags = SF_FILESCOPE;
                syms[s].sc = SC_EXTERN as! u8;
            }
            bind_sym(s, false);
            return s;
        }
        let s = csym(SK_VAR, name, ty, d.loc);
        cxs[s].dscope = cur_scope as! i32;
        syms[s].sc = ds.sc;
        if ds.sc == SC_STATIC { syms[s].flags = syms[s].flags | SF_FILESCOPE; }
        if ds.thread { syms[s].flags = syms[s].flags | SF_THREAD; }
        record_attrs(s, a, 0);
        if name != 0 { bind_sym(s, false); }
        if dependent_ctx() { cxs[s].flags = cxs[s].flags | CF_PATTERN; }
        return s;
    }
    // namespace scope, or a static data member
    var s = scope_find(cur_scope, name);
    while s >= 0 && syms[s].kind as i64 != SK_VAR { s = cxs[s].nnext as i64; }
    if s >= 0 && syms[s].kind as i64 == SK_VAR {
        if is_array(syms[s].ty) && types[syms[s].ty >> 4].n < 0 && !is_opaque(ty) { syms[s].ty = ty; }
    } else {
        s = csym(SK_VAR, name, ty, d.loc);
        scope_add(cur_scope, s);
    }
    syms[s].flags = syms[s].flags | SF_FILESCOPE;
    if ds.sc == SC_STATIC && ctx != DC_CLASS { syms[s].sc = SC_STATIC as! u8; }
    else if ds.sc == SC_EXTERN { if syms[s].sc as i64 != SC_STATIC { syms[s].sc = SC_EXTERN as! u8; } }
    if ds.thread { syms[s].flags = syms[s].flags | SF_THREAD; }
    if ds.is_inline || ds.is_constexpr { syms[s].flags = syms[s].flags | SF_INLINE; }
    if ds.is_constexpr { cxs[s].flags = cxs[s].flags | CF_CONSTEXPR; }
    if ctx == DC_CLASS {
        cxs[s].flags = cxs[s].flags | CF_MEMBER | CF_STATIC;
        cxs[s].access = cur_access as! u8;
    }
    if extern_c { cxs[s].flags = cxs[s].flags | CF_EXTERN_C; }
    if dependent_ctx() { cxs[s].flags = cxs[s].flags | CF_PATTERN; }
    record_attrs(s, a, 0);
    return s;
}

// ---------------------------------------------------------------------------
// Namespaces, using, linkage specifications, static_assert.

recursive fn parse_namespace() {
    let loc = tloc();
    var inline_ns = false;
    if at_kw(KW_INLINE) { inline_ns = true; adv(); }
    adv();      // namespace
    var a = Attrs { .. };
    cx_attrs(a);
    if at(TK_IDENT) && tk_n(1) == TK_EQUAL {
        // namespace alias
        let name = tu_toks[pc].val;
        adv();
        adv();
        var qn = QN { .. };
        parse_qname(qn);
        lookup_qn(qn);
        let s = csym(SK_NSALIAS, name, 0, loc);
        let t = chain_nns(qn.sym as i64);
        syms[s].v = if t >= 0 { sym_scope(t) } else { 0 };
        scope_add(cur_scope, s);
        expect(TK_SEMI, "';'");
        return;
    }
    // namespace A::B::inline C { }
    let save_scope = cur_scope;
    var nest = 0;
    loop {
        var this_inline = inline_ns;
        if nest > 0 && at_kw(KW_INLINE) { this_inline = true; adv(); }
        var name: u32 = 0;
        if at(TK_IDENT) { name = tu_toks[pc].val; adv(); }
        abi_tag_len = 0;
        cx_attrs(a);
        enter_namespace(name, this_inline, loc);
        if abi_tag_len > 0 && !ns_abi_tag.contains(cur_scope as u64) {
            ns_abi_tag.insert(cur_scope as u64, ((abi_tag_off as u64) << 32) | (abi_tag_len as u64));
        }
        nest++;
        inline_ns = false;
        if at(TK_COLONCOLON) { adv(); continue; }
        break;
    }
    cx_attrs(a);
    expect(TK_L_BRACE, "'{'");
    while !at(TK_R_BRACE) && !at(TK_EOF) {
        let before = pc;
        parse_decl_cx(DC_NS);
        if pc == before { adv(); }
    }
    expect(TK_R_BRACE, "'}'");
    cur_scope = save_scope;
}

// Opens (or reopens) namespace `name` in cur_scope: cur_scope becomes it.
fn enter_namespace(name: u32, inline_ns: bool, loc: u32) {
    if name == 0 {
        // the unnamed namespace: one per enclosing namespace, with an
        // implicit using-directive
        let key = anon_ns.get(cur_scope as u64);
        if key { cur_scope = key as i64; return; }
        let s = csym(SK_NAMESPACE, 0, 0, loc);
        let sc = new_scope(CS_NS, cur_scope, s, 0);
        scopes[sc].flags = scopes[sc].flags | SCF_ANON;
        syms[s].v = sc;
        cxs[s].dscope = cur_scope as! i32;
        scopes[cur_scope].using_ns = link_add(scopes[cur_scope].using_ns, sc);
        anon_ns.insert(cur_scope as u64, sc as! u32);
        cur_scope = sc;
        return;
    }
    var s = scope_find(cur_scope, name);
    while s >= 0 && syms[s].kind as i64 != SK_NAMESPACE { s = cxs[s].nnext as i64; }
    if s < 0 {
        // a namespace of an inline namespace in it is reopened through it
        var l = scopes[cur_scope].inl;
        while l >= 0 && s < 0 {
            var x = scope_find(ulinks[l].v as i64, name);
            while x >= 0 && syms[x].kind as i64 != SK_NAMESPACE { x = cxs[x].nnext as i64; }
            if x >= 0 { s = x; }
            l = ulinks[l].next;
        }
    }
    if s >= 0 {
        cur_scope = syms[s].v;
        return;
    }
    s = csym(SK_NAMESPACE, name, 0, loc);
    let sc = new_scope(CS_NS, cur_scope, s, name);
    syms[s].v = sc;
    scope_add(cur_scope, s);
    if inline_ns {
        scopes[sc].flags = scopes[sc].flags | SCF_INLINE;
        cxs[s].flags = cxs[s].flags | CF_INLINE_NS;
        scopes[cur_scope].inl = link_add(scopes[cur_scope].inl, sc);
    }
    cur_scope = sc;
}
var anon_ns = dictionary<u64, u32> {};
var reverted_kw = dictionary<u64, u32> {};
var any_reverted: bool = false;

// Block-scope using-directives: (scope depth, namespace scope) pairs.
var blk_using: u32[>..<] = [];

recursive fn parse_using(ctx: i64) {
    let loc = tloc();
    adv();      // using
    if at_kw(KW_NAMESPACE) {
        adv();
        var qn = QN { .. };
        parse_qname(qn);
        lookup_qn(qn);
        let t = chain_nns(qn.sym as i64);
        if t >= 0 {
            let ns = sym_scope(t);
            if ns >= 0 {
                if ctx == DC_BLOCK {
                    blk_using.push(scope_depth as! u32);
                    blk_using.push(ns as! u32);
                } else {
                    scopes[cur_scope].using_ns = link_add(scopes[cur_scope].using_ns, ns);
                }
            }
        } else if !dependent_ctx() && diag_suppress == 0 {
            err_at(qn.loc, "expected namespace name");
        }
        var a = Attrs { .. };
        cx_attrs(a);
        expect(TK_SEMI, "';'");
        return;
    }
    if at_kw(KW_ENUM) {
        // using enum E; (C++20)
        skip_to(TK_SEMI);
        expect(TK_SEMI, "';'");
        return;
    }
    if at(TK_IDENT) && (tk_n(1) == TK_EQUAL || (tk_n(1) == TK_L_SQUARE && tk_n(2) == TK_L_SQUARE) || tk_n(1) == TK_KW + KW_ATTRIBUTE) {
        // using X = type-id;
        let name = tu_toks[pc].val;
        adv();
        var a = Attrs { .. };
        cx_attrs(a);
        expect(TK_EQUAL, "'='");
        let t0 = pc;
        let ty = parse_type_id();
        if pending_tmpl >= 0 {
            // an alias template: its type-id's tokens are substituted at each use
            let t = pending_tmpl;
            pending_tmpl = -1;
            let ts = csym(SK_TEMPLATE, name, 0, loc);
            cxs[ts].tmpl = t as! i32;
            cxs[ts].flags = CF_TEMPLATE;
            tmpls[t].kind = TT_ALIAS as! u8;
            tmpls[t].sym = ts as! i32;
            tmpls[t].t0 = t0 as! u32;
            tmpls[t].t1 = pc as! u32;
            tmpls[t].scope = cur_scope as! i32;
            if ctx == DC_BLOCK { bind_sym(ts, false); } else { scope_add(cur_scope, ts); }
            if ctx == DC_CLASS { cxs[ts].flags = cxs[ts].flags | CF_MEMBER; }
        } else {
            declare_typedef(name, ty, loc, ctx);
        }
        expect(TK_SEMI, "';'");
        return;
    }
    // using-declarations: using a::b, c::d;
    loop {
        let tn = accept_kw(KW_TYPENAME);
        var qn = QN { .. };
        if !parse_qname(qn) { perr_expected("a name"); break; }
        let pack = accept(TK_ELLIPSIS);
        lookup_qn(qn);
        var name = qn.name;
        if qn.kind as i64 == QK_DTOR { name = id_dtor; }
        // inheriting constructors: using Base::Base
        let inherit_ctor = qn.qual && qn.scope >= 0 && scopes[qn.scope].kind as i64 == CS_CLASS && qn.kind as i64 == QK_IDENT &&
            qn.name == scopes[qn.scope].name;
        if inherit_ctor {
            if cur_class >= 0 { crecs[scopes[cur_class].rec].flags = crecs[scopes[cur_class].rec].flags | CR_USER_CTOR; }
        } else if qn.sym >= 0 {
            var s = qn.sym as i64;
            while s >= 0 {
                if visible(s) {
                    let u = csym(SK_USING, name, syms[resolve(s)].ty, loc);
                    cxs[u].target = resolve(s) as! i32;
                    if ctx == DC_BLOCK { bind_sym(u, false); }
                    else { scope_add(cur_scope, u); }
                    if ctx == DC_CLASS { cxs[u].access = cur_access as! u8; cxs[u].flags = CF_MEMBER; }
                }
                s = cxs[s].nnext as i64;
            }
        } else if qn.dep == 0 && !dependent_ctx() && diag_suppress == 0 && !(cur_class >= 0 && has_dep_base(cur_class)) {
            err_at(qn.loc, str("no member named '", ident_text(name as i64), "'"));
        } else if tn && qn.dep != 0 {
            // using typename Base<T>::type: a dependent type
            declare_typedef(name, mk_depname(qn.dep, qn.name, -1), loc, if ctx == DC_BLOCK { DC_BLOCK } else { ctx });
        } else if cur_class >= 0 {
            // a member of a dependent base: the name is dependent in this class
            let u = csym(SK_USING, name, t_unknown, loc);
            cxs[u].target = -1;
            cxs[u].flags = CF_MEMBER | CF_PATTERN;
            scope_add(cur_scope, u);
        }
        if !accept(TK_COMMA) { break; }
    }
    expect(TK_SEMI, "';'");
}

recursive fn parse_linkage_spec(ctx: i64) {
    adv();      // extern
    let t = tu_toks[pc];
    let lit = src[t.spell..t.spell + t.val];
    adv();
    let save = extern_c;
    extern_c = lit == "\"C\"";
    if at(TK_L_BRACE) {
        adv();
        while !at(TK_R_BRACE) && !at(TK_EOF) {
            let before = pc;
            parse_decl_cx(ctx);
            if pc == before { adv(); }
        }
        expect(TK_R_BRACE, "'}'");
    } else {
        parse_decl_cx(ctx);
    }
    extern_c = save;
}

recursive fn parse_static_assert_cx() {
    let loc = tloc();
    adv();
    expect(TK_L_PAREN, "'('");
    let sp = paren_depth;
    paren_depth = 1;
    let e = parse_assign_cx();
    paren_depth = sp;
    if accept(TK_COMMA) {
        if at(TK_STRING) { while at(TK_STRING) { adv(); } } else { skip_to(TK_R_PAREN); }
    }
    expect(TK_R_PAREN, "')'");
    expect(TK_SEMI, "';'");
    if is_opaque(nodes[e].ty) || dependent_ctx() { return; }
    let ok, v = const_int(e);
    if ok && v == 0 && diag_suppress == 0 && sa_checked(e) {
        err_at(loc, "static assertion failed");
    }
}

// ---------------------------------------------------------------------------
// The translation unit.

recursive fn parse_tu_cxx() {
    // clang's revertible type-trait keywords: libstdc++ names templates
    // __is_void, __is_pod ...; a trait keyword not followed by '(' is an
    // identifier (and after struct/class it stays one: Parser::TryKeywordIdentFallback)
    for t, i in tu_toks {
        let k = t.kind as i64;
        if (k == TK_KW + KW_TRAIT || k == TK_KW + KW_TTRANS) && i + 1 < tu_toks.len {
            let prev = if i > 0 { tu_toks[i - 1].kind as i64 } else { 0 };
            if tu_toks[i + 1].kind as i64 != TK_L_PAREN || prev == TK_KW + KW_STRUCT || prev == TK_KW + KW_CLASS {
                tu_toks[i].kind = TK_IDENT;
            }
            if prev == TK_KW + KW_STRUCT || prev == TK_KW + KW_CLASS {
                reverted_kw.insert(t.val as u64, 1);
                any_reverted = true;
            }
        }
    }
    if any_reverted {
        for t, i in tu_toks {
            if (t.kind as i64 == TK_KW + KW_TRAIT || t.kind as i64 == TK_KW + KW_TTRANS) && reverted_kw.contains(t.val as u64) {
                tu_toks[i].kind = TK_IDENT;
            }
        }
    }
    let mark = nscratch.len;
    while !at(TK_EOF) {
        if at(TK_R_BRACE) {
            err("extraneous closing brace ('}')");
            adv();
            continue;
        }
        let before = pc;
        parse_decl_cx(DC_NS);
        if pc == before { adv(); }
    }
    // D2: the bodies of the used members of instantiations and specializations
    inst_drain();
    for f in fdefs_extra { nscratch.push(f); }
    for f in inst_defs { nscratch.push(f); }
    inst_defs_taken = inst_defs.len;
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    tu_node = node_v(N_TU, 0, 0, 0, 0, count, 0, start);
}

// The function type ft returning `ret` instead.
fn func_with_ret(ft: u32, ret: u32) -> u32 {
    let f = types[ft >> 4];
    fn_scratch.clear();
    for i in f.n { fn_scratch.push(tparams[f.extra + i]); }
    return qt(mk_type(TY_FUNC, f.flags as i64, unqual_ret(ret), 0, 0, 0) as i64, 0);
}

// clang's builtin templates: __make_integer_seq<S, T, N>,
// __type_pack_element<N, Ts...> (opaque specializations in D1).
fn builtin_template(name: const u8[:]) {
    let t = tmpls.len;
    tmpls.push(Tmpl { kind: TT_CLASS as! u8, depth: 1, rsv: 0, sym: -1, params: 0, nparams: 0, scope: 0, pos: 0, t0: 0, t1: 0,
        pattern: -1, specs: -1, outer: -1, spec_args: -1, primary: -1, inst_scope: -1, def_t: -1, hdr_outer: -1, pat_t: -1 });
    let s = csym(SK_TEMPLATE, intern(name), 0, 0);
    cxs[s].tmpl = t as! i32;
    cxs[s].flags = CF_TEMPLATE;
    tmpls[t].sym = s as! i32;
    scope_add(0, s);
}

// The parser's start: the C++ types and the global namespace.
fn cx_init() {
    rec_inst_hook = true;
    id_this = intern("this");
    cx_types_init();
    names_init();
    cx_grow();
    crec_grow();
    // the builtin typedefs C's parse_init declared go to the global scope too
    for s, i in syms {
        if i > 0 && s.kind as i64 == SK_TYPEDEF && s.name != 0 { scope_add(0, i); }
        if i > 0 && s.kind as i64 == SK_TAG && s.name != 0 { scope_add(0, i); }
    }
    declare_std_types();
    builtin_template("__make_integer_seq");
    builtin_template("__type_pack_element");
}

// std::size_t, std::nullptr_t ... come from the headers; the global
// operator new/delete are implicitly declared (C++ [basic.stc.dynamic]p2).
fn declare_std_types() {
    implicit_alloc_fn(OP_NEW, t_voidptr, t_size);
    implicit_alloc_fn(OP_NEW_ARR, t_voidptr, t_size);
    implicit_alloc_fn(OP_DELETE, t_void, t_voidptr);
    implicit_alloc_fn(OP_DELETE_ARR, t_void, t_voidptr);
}

fn implicit_alloc_fn(op: i64, ret: u32, param: u32) {
    fn_scratch.clear();
    fn_scratch.push(param);
    let ft = qt(mk_type(TY_FUNC, 0, ret, 0, 0, 0) as i64, 0);
    let s = csym(SK_FUNC, op_ids[op], ft, 0);
    cxs[s].flags = CF_OPERATOR | CF_IMPLICIT;
    cxs[s].op = op as! u8;
    scope_add(0, s);
}
