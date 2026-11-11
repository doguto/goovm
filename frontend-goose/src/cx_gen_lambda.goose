// goosecc D3: lambda expressions in code generation ([expr.prim.lambda],
// as clang lowers them). A lambda is a local class (the closure type) with
// a field per capture, in the order of the captures (the explicit ones in
// the capture list's order, then the implicit ones in the order of their
// first use), its function call operator (const unless mutable; the
// return type deduced from the first return statement when not written)
// and, without captures, a conversion to a function pointer returning a
// static invoker. The lambda-expression is the aggregate initialization
// of a closure object from the captured entities.
//
// While the body is parsed, a name that refers to a local variable of an
// enclosing function (declared before the lambda: its symbol precedes the
// lambda's first) becomes a capture: a member of *this of the call
// operator, whose field index is fixed when the closure's fields are made
// after the body. `this` in the body is the captured `this`.
//
// Names (Itanium 5.1.8): in an inline function (or another lambda's call
// operator that is), Ul<params>E[<n>]_ with linkonce_odr linkage; else
// clang's internal $_<n>, numbered per enclosing function.
//
// Not yet: generic lambdas (auto parameters, template parameter lists),
// *this captures, pack captures.

namespace cx;

import std;
import dictionary;
import .common;
import .types;
import .ast;
import .sema;
import .parse;
import .cx_core;
import .cx_names;
import .cx_expr;
import .cx_sema;
import .cx_over;
import .cx_layout;
import .cx_mangle;
import .cx_gen_defs;

struct LamCtx { rec: i64, me: i64, def: i64, mut: bool, floor: i64, cap0: i64, fix0: i64, fnc: i64, init0: i64 }
var lams: LamCtx[>..<] = [];
// A capture: var (-1: this), by reference, the init-capture's initializer
// (0 none), its field's type, its name.
struct LamCap { v: i64, byref: bool, init: u32, ty: u32, name: u32 }
var lcaps: LamCap[>..<] = [];
var lfix: u32[>..<] = [];
var lstash: LamCap[>..<] = [];              // member nodes whose field index is a capture ordinal
var initcap_syms = dictionary<u64, u32> {};   // init-capture's variable -> its ordinal

// The lambdas made, for their names: (call operator, enclosing function,
// static invoker or -1, conversion function or -1, closure record).
struct LamInfo { op: i64, encl: i64, inv: i64, conv: i64, rec: i64, named: bool }
var lam_infos: LamInfo[>..] = [];

// The field type of capture of variable v (byref: a reference).
fn cap_field_type(v: i64, byref: bool) -> u32 {
    let t = nonref(syms[v].ty);
    if byref { return mk_lref(t); }
    return t;
}

// A reference to capture `ordinal` of the innermost lambda (in its call
// operator's body): (*this).field.
fn cap_ref(ordinal: i64, loc: u32) -> u32 {
    let L = lams[lams.len - 1];
    let c = lcaps[L.cap0 + ordinal];
    let obj = n_deref(rv(n_var(L.me, loc)), loc);
    let cq = quals(nodes[obj].ty) & Q_CONST;
    // (c = the closure's record + 1: the field is the capture's ordinal in
    // it until the walk, as the fields are made after the body)
    var n: u32 = 0;
    if c.byref {
        n = node(N_MEMBER, 0, nonref(c.ty), obj as i64, ordinal, L.rec + 1, loc);
        nodes[n].flags = (NF_LVALUE | NF_REFDEREF) as! u16;
    } else {
        n = node(N_MEMBER, 0, with_q(c.ty, quals(c.ty) | cq), obj as i64, ordinal, L.rec + 1, loc);
        nodes[n].flags = NF_LVALUE;
    }
    return n;
}

fn find_cap(vv: i64) -> i64 {
    let L = lams[lams.len - 1];
    for i in L.cap0..lcaps.len { if lcaps[i].v == vv && lcaps[i].init == 0 { return i - L.cap0; } }
    return -1;
}

// A name of variable s used in the body of the innermost lambda: a capture
// (or its constant value when it is not odr-used), or 0 when it is not an
// enclosing function's variable.
recursive fn cg_lambda_var(s: i64, loc: u32) -> u32 {
    if lams.len == 0 { return 0; }
    let L = lams[lams.len - 1];
    let ic = initcap_syms.get(s as u64);
    if ic {
        // an init-capture of this lambda; of an enclosing one: captured like a variable
        let ord = (ic & 0xFFFF) as i64;
        let li = (ic >> 16) as i64;
        if li == lams.len - 1 { return cap_ref(ord, loc); }
    }
    if syms[s].kind as i64 != SK_VAR || s >= L.floor { return 0; }
    if syms[s].flags & (SF_FILESCOPE | SF_THREAD) != 0 || cxs[s].flags & CF_MEMBER != 0 { return 0; }
    let sc = syms[s].sc as i64;
    if sc == SC_STATIC || sc == SC_EXTERN { return 0; }
    // a constant: not odr-used, its value
    let t = nonref(syms[s].ty);
    if !is_ref(syms[s].ty) && quals(t) & Q_CONST != 0 && (is_integer(t) || kind_of(t) == TY_ENUM) && s < cvar_init.len && cvar_init[s] != 0 {
        let ok, v = const_int(cvar_init[s]);
        if ok { return int_node(v, unqual(t), loc); }
    }
    var ord = find_cap(s);
    if ord < 0 {
        if L.def == 0 {
            if diag_suppress == 0 {
                err_at(loc, str("variable '", ident_text(syms[s].name as i64), "' cannot be implicitly captured in a lambda with no capture-default specified"));
            }
            return opaque_node(loc);
        }
        let byref = L.def == 2;
        lcaps.push(LamCap { v: s, byref: byref, init: 0, ty: cap_field_type(s, byref), name: syms[s].name });
        ord = lcaps.len - 1 - L.cap0;
    }
    return cap_ref(ord, loc);
}

// `this` in the body of the innermost lambda: the captured this (when the
// current `this` is the closure's), or 0.
fn cg_lambda_this(loc: u32) -> u32 {
    if lams.len == 0 { return 0; }
    let L = lams[lams.len - 1];
    if cg_this != L.me { return 0; }
    var ord = find_cap(-1);
    if ord < 0 {
        if L.def == 0 || lam_outer_this == 0 { return opaque_node(loc); }
        lcaps.push(LamCap { v: -1, byref: false, init: 0, ty: lam_outer_this, name: id_this });
        ord = lcaps.len - 1 - L.cap0;
    }
    return rv(cap_ref(ord, loc));
}
var lam_outer_this: u32 = 0;    // the type of `this` around the innermost lambda (0 none)

// A variable as an expression in the current context (an enclosing
// lambda's capture, else the variable).
recursive fn outer_var_ref(v: i64, loc: u32) -> u32 {
    let c = cg_lambda_var(v, loc);
    if c != 0 { return c; }
    let n = node(N_DECLREF, 0, nonref(syms[v].ty), v, 0, 0, loc);
    nodes[n].flags = (NF_LVALUE | (if is_ref(syms[v].ty) { NF_REFDEREF } else { 0 })) as! u16;
    syms[v].flags = syms[v].flags | SF_USED;
    return n;
}

// Skips the rest of a lambda D3 cannot make (after its parameters).
recursive fn lambda_skip_rest() {
    loop {
        if at_kw(KW_MUTABLE) || at_kw(KW_CONSTEXPR) || at_kw(KW_CONSTEVAL) { adv(); continue; }
        if at_kw(KW_NOEXCEPT) || at_kw(KW_THROW) { adv(); if at(TK_L_PAREN) { skip_group(); } continue; }
        if at_attr_start() { var a = Attrs { .. }; cx_attrs(a); continue; }
        break;
    }
    if accept(TK_ARROW) { let t = parse_type_id(); }
    if at(TK_L_BRACE) { skip_group(); }
}

// lambda-expression at '['.
recursive fn cg_parse_lambda() -> u32 {
    let loc = tloc();
    adv();      // [
    var def: i64 = 0;
    var fail = false;
    let cap0 = lcaps.len;
    let fix0 = lfix.len;
    let outer_this = this_type;
    // (its slot in lam_infos now: enclosing lambdas are named first)
    let li = lam_infos.len;
    lam_infos.push(LamInfo { op: -1, encl: cur_func_cx, inv: -1, conv: -1, rec: -1, named: false });
    // the capture list (explicit captures, in order)
    while !at(TK_R_SQUARE) && !at(TK_EOF) {
        if at(TK_AMP) && (tk_n(1) == TK_COMMA || tk_n(1) == TK_R_SQUARE) { adv(); def = 2; }
        else if at(TK_EQUAL) { adv(); def = 1; }
        else if at_kw(KW_THIS) {
            adv();
            if outer_this == 0 { fail = true; }
            else { lcaps.push(LamCap { v: -1, byref: false, init: 0, ty: outer_this, name: id_this }); }
        } else if at(TK_STAR) { adv(); adv(); fail = true; }   // *this
        else {
            let byref = accept(TK_AMP);
            if !at(TK_IDENT) { fail = true; skip_to(TK_R_SQUARE); break; }
            let name = tu_toks[pc].val;
            let nloc = tloc();
            adv();
            if at(TK_ELLIPSIS) { adv(); fail = true; }
            if at(TK_EQUAL) || at(TK_L_PAREN) || at(TK_L_BRACE) {
                // an init-capture: x = e / x(e) / x{e}
                var e: u32 = 0;
                if accept(TK_EQUAL) {
                    if at(TK_L_BRACE) { e = parse_braced(); } else { e = parse_assign_cx(); }
                } else if at(TK_L_PAREN) {
                    adv();
                    e = parse_assign_cx();
                    expect(TK_R_PAREN, "')'");
                } else {
                    e = parse_braced();
                    if nodes[e].kind as i64 == N_INITBRACE && nodes[e].c == 1 { e = nlist[nodes[e].v]; }
                }
                if is_opq(e) || nodes[e].kind as i64 == N_INITBRACE { fail = true; }
                else {
                    let ft = if byref { mk_lref(nodes[e].ty) } else { auto_decay(nodes[e].ty) };
                    lcaps.push(LamCap { v: -2, byref: byref, init: e, ty: ft, name: name });
                }
            } else {
                let ch = unqual_lookup_from(cur_scope, name);
                let v = if ch >= 0 { resolve(first_visible(ch)) } else { -1 };
                if v < 0 || syms[v].kind as i64 != SK_VAR {
                    if diag_suppress == 0 { err_at(nloc, str("use of undeclared identifier '", ident_text(name as i64), "'")); }
                    fail = true;
                } else {
                    lcaps.push(LamCap { v: v, byref: byref, init: 0, ty: cap_field_type(v, byref), name: name });
                }
            }
        }
        if !accept(TK_COMMA) { break; }
    }
    expect(TK_R_SQUARE, "']'");
    if at(TK_LESS) { skip_angles(); fail = true; }
    var a = Attrs { .. };
    cx_attrs(a);
    // the closure class
    let r = new_record_cx(0, false, loc);
    let cs = csym(SK_TAG, 0, records[r].ty << 4, loc);
    cxs[cs].dscope = cur_scope as! i32;
    let csc = class_setup(r, cs, cur_scope);
    let cls = records[r].ty << 4;
    // its scope for the parameters and init-captures
    push_scope();
    let floor = syms.len;
    for i in cap0..lcaps.len {
        if lcaps[i].v == -2 {
            let v = csym(SK_VAR, lcaps[i].name, lcaps[i].ty, loc);
            cxs[v].dscope = cur_scope as! i32;
            syms[v].scope = 1;
            bind_sym(v, false);
            initcap_syms.insert(v as u64, (((lams.len as u64) << 16) | ((i - cap0) as u64)) as! u32);
        }
    }
    var pst: i64 = 0;
    var pn: i64 = 0;
    var variadic = false;
    if at(TK_L_PAREN) {
        let st, n = parse_cparams(variadic);
        if st >= 0 { pst = st; pn = n; }
        for i in pn {
            let p = nlist[pst + i] as i64;
            if has_auto(syms[p].ty) || is_opaque(syms[p].ty) { fail = true; }
        }
    }
    var mut = false;
    var noexc = false;
    loop {
        if at_kw(KW_MUTABLE) { adv(); mut = true; continue; }
        if at_kw(KW_CONSTEXPR) || at_kw(KW_CONSTEVAL) { adv(); continue; }
        if at_kw(KW_NOEXCEPT) {
            adv();
            noexc = true;
            if at(TK_L_PAREN) { skip_group(); }
            continue;
        }
        if at_kw(KW_THROW) { adv(); if at(TK_L_PAREN) { skip_group(); } continue; }
        if at_attr_start() { cx_attrs(a); continue; }
        break;
    }
    var rt: u32 = 0;
    if accept(TK_ARROW) { rt = parse_type_id(); }
    if rt == 0 { rt = qt(mk_type(TY_AUTO, 0, 0, 0, 0, 0) as i64, 0); }
    if fail || is_opaque(rt) || !at(TK_L_BRACE) {
        if at(TK_L_BRACE) { skip_group(); }
        pop_scope();
        lcaps.resize(cap0);
        return opaque_node(loc);
    }
    // the function call operator
    fn_scratch.clear();
    for i in pn { fn_scratch.push(syms[nlist[pst + i] as i64].ty); }
    var tf: i64 = 0;
    if !mut { tf = tf | TF_MCONST; }
    if variadic { tf = tf | TF_VARIADIC; }
    let ft = qt(mk_type(TY_FUNC, tf, rt, 0, 0, 0) as i64, 0);
    let f = csym(SK_FUNC, op_ids[OP_CALL], ft, loc);
    cxs[f].dscope = csc as! i32;
    cxs[f].flags = (CF_MEMBER | CF_DEFINED_IN_CLASS | CF_OPERATOR | (if mut { 0 } else { CF_CONST }) | (if noexc { CF_NOEXCEPT } else { 0 })) as! u32;
    cxs[f].op = OP_CALL as! u8;
    syms[f].flags = SF_DEFINED | SF_INLINE;
    scope_add(csc, f);
    fn_params.insert(f as u64, ((pst as u64) << 32) | (pn as u64));
    let self_p = make_this(f, mk_ptr(with_q(cls, if mut { 0 } else { Q_CONST })), loc);
    lams.push(LamCtx { rec: r, me: self_p, def: def, mut: mut, floor: floor, cap0: cap0, fix0: fix0, fnc: f, init0: 0 });
    let sv_outer = lam_outer_this;
    lam_outer_this = outer_this;
    let fd = parse_function_body(f, pst, pn);
    lam_outer_this = sv_outer;
    lams.pop();
    // no return statement: void
    let fty = types[syms[f].ty >> 4];
    if kind_of(fty.base) == TY_AUTO { set_fn_return(f, t_void); }
    pop_scope();
    cg_extra.push(fd);
    // the fields: the captures, in order
    let first = fields.len;
    for i in cap0..lcaps.len {
        let c = lcaps[i];
        fields.push(Field { name: c.name, ty: c.ty, offset: 0, bitpos: 0, width: -1, attr_align: 0, flags: 0, rsv: 0, rsv2: 0, loc: loc });
    }
    records[r].first = first as! u32;
    records[r].count = (lcaps.len - cap0) as! u32;
    while crec_mems.len <= r { crec_mems.push(MemRange { first: 0, count: 0 }); }
    complete_class(r);
    // the closure object: each field from its entity (in this context)
    // (moved aside first: an enclosing lambda's captures these make go on lcaps)
    let mark = nscratch.len;
    let sm = lstash.len;
    for i in cap0..lcaps.len { lstash.push(lcaps[i]); }
    let ncap = lcaps.len - cap0;
    lcaps.resize(cap0);
    for i in sm..sm + ncap {
        let c = lstash[i];
        if c.v == -1 { nscratch.push(mk_this(loc)); }
        else if c.v == -2 { nscratch.push(c.init); }
        else { nscratch.push(outer_var_ref(c.v, loc)); }
    }
    lstash.resize(sm);
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    let obj = node_v(N_CTOR, 2, cls, 0, 0, count, loc, start);
    // without captures: the conversion to a function pointer
    var inv: i64 = -1;
    var conv: i64 = -1;
    if ncap == 0 && !variadic {
        inv, conv = lambda_fnptr(f, csc, cls, pst, pn, loc);
    }
    lam_infos[li] = LamInfo { op: f, encl: lam_infos[li].encl, inv: inv, conv: conv, rec: r, named: false };
    name_closure(li, r, f, lam_infos[li].encl);
    lam_fns.insert(f as u64, 1);
    if inv >= 0 { lam_fns.insert(inv as u64, 1); }
    if conv >= 0 { lam_fns.insert(conv as u64, 1); }
    return obj;
}

fn auto_decay(t0: u32) -> u32 {
    let u = unqual(nonref(t0));
    if is_array(u) { return mk_ptr(tbase(u)); }
    if is_func(u) { return mk_ptr(u); }
    return u;
}

// Function f's return type becomes t.
fn set_fn_return(f: i64, t: u32) {
    let ft = types[syms[f].ty >> 4];
    fn_scratch.clear();
    for i in ft.n { fn_scratch.push(tparams[ft.extra + i]); }
    syms[f].ty = qt(mk_type(TY_FUNC, ft.flags as i64, t, 0, 0, 0) as i64, quals(syms[f].ty));
}

// return e in a function whose return type is deduced (auto): the type
// from the first return statement.
recursive fn cg_deduce_return(x: u32, loc: u32) {
    let f = cur_func_cx;
    if f < 0 || is_opq(x) { return; }
    let t = deduce_auto(ret_type, x);
    if t == 0 || is_opaque(t) { return; }
    set_fn_return(f, t);
    ret_type = t;
    if pass_indirect(t) && cg_ret < 0 { cg_ret = make_ret(f, t, loc); }
}

// The static invoker and the conversion function of a lambda without
// captures (call operator f): `static R __invoke(P...)` calling f on a
// closure object, `operator R (*)(P...)() const` returning it.
recursive fn lambda_fnptr(f: i64, csc: i64, cls: u32, pst: i64, pn: i64, loc: u32) -> i64, i64 {
    let ft = types[syms[f].ty >> 4];
    let rt = ft.base;
    if pass_indirect(rt) || is_opaque(rt) { return -1, -1; }
    fn_scratch.clear();
    for i in ft.n { fn_scratch.push(tparams[ft.extra + i]); }
    let it = qt(mk_type(TY_FUNC, (ft.flags as i64) & TF_VARIADIC, rt, 0, 0, 0) as i64, 0);
    let inv = csym(SK_FUNC, intern("__invoke"), it, loc);
    cxs[inv].dscope = csc as! i32;
    cxs[inv].flags = (CF_MEMBER | CF_STATIC | CF_DEFINED_IN_CLASS | (cxs[f].flags & CF_NOEXCEPT)) as! u32;
    syms[inv].flags = SF_DEFINED | SF_INLINE;
    // its parameters
    let pm = nscratch.len;
    for i in pn {
        let p0 = nlist[pst + i] as i64;
        let p = csym(SK_VAR, syms[p0].name, syms[p0].ty, loc);
        syms[p].flags = SF_PARAM;
        syms[p].scope = 1;
        nscratch.push(p as! u32);
    }
    let ip = commit_list(pm);
    fn_params.insert(inv as u64, ((ip as u64) << 32) | (pn as u64));
    // { T __closure = {}; return __closure(args); }
    let bm = nscratch.len;
    let tmp = csym(SK_VAR, intern("__closure"), cls, loc);
    syms[tmp].scope = 1;
    nscratch.push(node(N_DECL, 0, cls, tmp, node(N_ZEROINIT, 0, cls, 0, 0, 0, loc) as i64, loc as i64, loc));
    let am = nscratch.len;
    for i in pn { nscratch.push(n_var(nlist[ip + i] as i64, loc)); }
    let c = lower_call(f, n_var(tmp, loc), am, loc, false);
    if is_opq(c) { nscratch.resize(bm); return -1, -1; }
    if is_void(rt) { nscratch.push(n_expr_stmt(c)); }
    else if is_ref(rt) { nscratch.push(node(N_RETURN, 0, rt, n_addr(c, loc) as i64, 0, 0, loc)); }
    else { nscratch.push(node(N_RETURN, 0, rt, c as i64, 0, 0, loc)); }
    let body = n_block(bm, loc);
    let ifd = node_v(N_FUNCDEF, 0, it, inv, body as i64, pn, loc, ip);
    syms[inv].def = ifd as! i32;
    cg_extra.push(ifd);
    // the conversion function
    let pt = mk_ptr(it);
    fn_scratch.clear();
    let ct = qt(mk_type(TY_FUNC, TF_MCONST, pt, 0, 0, 0) as i64, 0);
    let conv = csym(SK_FUNC, id_conv, ct, loc);
    cxs[conv].dscope = csc as! i32;
    cxs[conv].flags = (CF_MEMBER | CF_CONV | CF_CONST | CF_DEFINED_IN_CLASS | CF_NOEXCEPT) as! u32;
    syms[conv].flags = SF_DEFINED | SF_INLINE;
    scope_add(csc, conv);
    fn_params.insert(conv as u64, 0);
    let th = make_this(conv, mk_ptr(with_q(cls, Q_CONST)), loc);
    let cm = nscratch.len;
    let fp = icast(n_ref_fn(inv, loc), CK_FUNC2PTR, pt);
    nscratch.push(node(N_RETURN, 0, pt, fp as i64, 0, 0, loc));
    let cb = n_block(cm, loc);
    let cfd = node_v(N_FUNCDEF, 0, ct, conv, cb as i64, 0, loc, 0);
    syms[conv].def = cfd as! i32;
    cg_extra.push(cfd);
    let unused = th;
    return inv, conv;
}

// ---------------------------------------------------------------------------
// Names.

var lam_nums = dictionary<u64, u32> {};     // enclosing function (| 1 << 40: signature key) -> the next number
var lam_names: u8[>..] = [];                // the closures' names (<source-name> $_<n>, or Ul...E[n]_)
var lam_rec = dictionary<u64, u64> {};      // closure record -> lam_infos index << 40 | name offset << 16 | length
var lam_fns = dictionary<u64, u8> {};       // the lambdas' functions (named by name_lambdas)
var cm_buf: u8[>..] = [];

fn is_lambda_fn(s: i64) -> bool { lam_fns.contains(s as u64) }

// The function closure or local class r is in (-1: namespace scope or none).
fn local_encl(r: i64) -> i64 {
    let g = lam_rec.get(r as u64);
    if g { return lam_infos[(g >> 40) as i64].encl; }
    let h = local_cls.get(r as u64);
    if h { return (h >> 16) as i64; }
    return -1;
}

// Is function f a lambda's call operator?
fn is_lambda_op(f: i64) -> bool {
    if f < 0 || syms[f].kind as i64 != SK_FUNC || cxs[f].op as i64 != OP_CALL || cxs[f].dscope <= 0 { return false; }
    let r = scopes[cxs[f].dscope].rec as i64;
    return r >= 0 && lam_rec.contains(r as u64);
}

// The closure type's name for lambda li (call operator f, enclosing
// function encl): Itanium's Ul<params>E[<n>]_ in an inline function or a
// lambda, else clang's $_<n> (numbered per enclosing function).
fn name_closure(li: i64, r: i64, f: i64, encl: i64) {
    let ul = encl >= 0 && (fn_inline(encl) || is_lambda_op(encl));
    let off = lam_names.len;
    if ul {
        var sig: u8[>..] = [];
        let ft = types[syms[f].ty >> 4];
        if ft.n == 0 { sig.append("v"); }
        for k in ft.n {
            if mangle_special("", tparams[ft.extra + k]) { sig.append(mg); } else { sig.append("v"); }
        }
        let key = ((intern(sig) as u64) << 24) | ((encl as u64) & 0xFFFFFF) | (1 << 62);
        var n: i64 = 0;
        let g = lam_nums.get(key);
        if g { n = g as i64; }
        lam_nums.insert(key, (n + 1) as! u32);
        lam_names.append("Ul");
        lam_names.append(sig);
        lam_names.append("E");
        if n > 0 { format(lam_names, n - 1); }
        lam_names.append("_");
    }
    // ($_<n>: numbered when first used, as clang numbers them when it
    // first mangles them: lam_dollar_name)
    lam_rec.insert(r as u64, ((li as u64) << 40) | ((off as u64) << 16) | ((lam_names.len - off) as u64));
}

var lam_dnum = dictionary<u64, u32> {};    // a $_ closure -> its number
// A use of the closure of record r (a call of its functions, a
// specialization named with it): its $_<n> number now if it has none.
fn note_lambda_use(r: i64) {
    let g = lam_rec.get(r as u64);
    if !g || (g & 0xFFFF) != 0 || lam_dnum.contains(r as u64) { return; }
    let li = (g >> 40) as i64;
    let e = lam_infos[li].encl;
    let key = if e >= 0 { e as u64 } else { 0xFFFFFFFF };
    var n: i64 = 0;
    let h = lam_nums.get(key);
    if h { n = h as i64; }
    lam_nums.insert(key, (n + 1) as! u32);
    lam_dnum.insert(r as u64, n as! u32);
}

// Closures named in a call of function f (its class, its template arguments).
fn note_lambda_uses(f: i64) {
    if lam_rec.count == 0 || f < 0 || f >= cxs.len { return; }
    if cxs[f].dscope > 0 && scopes[cxs[f].dscope].kind as i64 == CS_CLASS && scopes[cxs[f].dscope].rec >= 0 { note_lambda_use(scopes[cxs[f].dscope].rec as i64); }
    if cxs[f].flags2 & CF2_FSPEC != 0 && cxs[f].targs >= 0 {
        let l = cxs[f].targs as i64;
        for i in tl_count(l) {
            let a = tl_arg(l, i);
            if a.kind as i64 != TA_TYPE { continue; }
            var t = a.ty;
            while is_pointer(t) || is_ref(t) { t = tbase(t); }
            if is_record(t) { note_lambda_use(rec_of(t)); }
        }
    }
}

// The closure name of record r (offset/length in lam_names; a $_ one
// written now).
fn closure_name(r: i64, out: u8[>..]&) {
    let g = lam_rec.get(r as u64);
    if !g { return; }
    let off = ((g >> 16) & 0xFFFFFF) as i64;
    let len = (g & 0xFFFF) as i64;
    if len > 0 { out.append(lam_names[off..off + len]); return; }
    note_lambda_use(r);
    var d: u8[>..] = [];
    d.append("$_");
    let n = lam_dnum.get(r as u64);
    if n { format(d, n as i64); }
    format(out, d.len);
    out.append(d);
}

// The enclosing function's part of a local name: Z<encoding>E (empty at
// namespace scope); false when the function has no name yet.
recursive fn encl_enc(e: i64, out: u8[>..]&) -> bool {
    if e < 0 { return true; }
    let ai = syms[e].attr;
    if ai != 0 && sym_attrs[ai].asm_len != 0 {
        let o = sym_attrs[ai].asm_label as i64;
        let lab = strbytes[o..o + sym_attrs[ai].asm_len as i64];
        out.append("Z");
        if lab.len >= 3 && lab[0] == '_' && lab[1] == 'Z' { out.append(lab[2..]); }
        else { format(out, lab.len); out.append(lab); }
        out.append("E");
        return true;
    }
    // not named yet: mangled now, the mangler's state set aside
    let m0 = mg_stack.len;
    let s0 = msub_stack.len;
    mg_stack.append(mg);
    for x in msubs { msub_stack.push(x); }
    let ml = mg.len;
    let sl = msubs.len;
    let fail0 = mg_fail;
    let ne0 = mg_name_end;
    let ft0 = mg_ft;
    let fs0 = mg_fsym;
    let st0 = mg_structor;
    mg_structor = 1;
    let ok = mangle_sym(e);
    out.append("Z");
    if ok && mg.len >= 2 && mg[0] == '_' && mg[1] == 'Z' { out.append(mg[2..]); } else { format(out, mg.len); out.append(mg); }
    out.append("E");
    mg.clear();
    mg.append(mg_stack[m0..m0 + ml]);
    msubs.clear();
    for i in sl { msubs.push(msub_stack[s0 + i]); }
    mg_stack.resize(m0);
    msub_stack.resize(s0);
    mg_fail = fail0;
    mg_name_end = ne0;
    mg_ft = ft0;
    mg_fsym = fs0;
    mg_structor = st0;
    return ok;
}
var mg_stack: u8[>..] = [];
var msub_stack: u64[>..] = [];

// The mangled name of closure record r (Z<encoding>E<closure-name>) in
// cm_buf; false when r is no closure or its function has no name yet.
recursive fn closure_mangled(r: i64) -> bool {
    let g = lam_rec.get(r as u64);
    if !g { return local_class_mangled(r); }
    let li = (g >> 40) as i64;
    cm_buf.clear();
    cm_name.clear();
    cm_disc.clear();
    let e = lam_infos[li].encl;
    if !encl_enc(e, cm_buf) { return false; }
    closure_name(r, cm_name);
    cm_enc_len = cm_buf.len;
    cm_buf.append(cm_name);
    if !(e >= 0 && cxl_link(e) == LK_LINKONCE && syms[e].sc as i64 != SC_STATIC) { cm_no_linkage = true; }
    return true;
}
// Local classes (a class defined in a function body): local names,
// Z <function encoding> E <name> [_<n>] (n: the earlier classes of that
// name in the function).
var local_cls = dictionary<u64, u64> {};    // record -> enclosing function << 16 | discriminator
var local_cls_list: u32[>..] = [];

fn note_local_class(r: i64, parent: i64) {
    if cur_func_cx < 0 || records[r].name == 0 { return; }
    var disc: i64 = 0;
    for x in local_cls_list {
        let gx = local_cls.get(x as u64);
        if gx && (gx >> 16) as i64 == cur_func_cx && records[x].name == records[r].name { disc++; }
    }
    local_cls.insert(r as u64, ((cur_func_cx as u64) << 16) | (disc as u64));
    local_cls_list.push(r as! u32);
}

recursive fn local_class_mangled(r: i64) -> bool {
    let g = local_cls.get(r as u64);
    if !g { return false; }
    let e = (g >> 16) as i64;
    let disc = (g & 0xFFFF) as i64;
    cm_buf.clear();
    cm_name.clear();
    if !encl_enc(e, cm_buf) { return false; }
    let nm = ident_text(records[r].name as i64);
    format(cm_name, nm.len);
    cm_name.append(nm);
    cm_disc.clear();
    if disc > 0 { if disc - 1 < 10 { format(cm_disc, "_", disc - 1); } else { format(cm_disc, "__", disc - 1, "_"); } }
    cm_enc_len = cm_buf.len;
    cm_buf.append(cm_name);
    cm_buf.append(cm_disc);
    if !(cxl_link(e) == LK_LINKONCE && syms[e].sc as i64 != SC_STATIC) { cm_no_linkage = true; }
    return true;
}

var cm_name: u8[>..] = [];      // (closure_mangled: the closure's own name, after cm_enc_len bytes of cm_buf)
var cm_disc: u8[>..] = [];      // ... a local class's discriminator (after cm_name in cm_buf)
var cm_enc_len: i64 = 0;
var cm_no_linkage = false;      // a closure type without linkage was mangled

// The names and linkage of the lambdas' functions (after name_syms):
// local to their enclosing function, with its linkage.
fn name_lambdas() {
    for i in lam_infos.len {
        if lam_infos[i].named || lam_infos[i].op < 0 { continue; }
        let L = lam_infos[i];
        if !closure_mangled(L.rec) { continue; }
        lam_infos[i].named = true;
        let linkonce = L.encl >= 0 && cxl_link(L.encl) == LK_LINKONCE && syms[L.encl].sc as i64 != SC_STATIC;
        let ft = types[syms[L.op].ty >> 4];
        var params: u8[>..] = [];
        if ft.n == 0 { params.append("v"); }
        for k in ft.n {
            if mangle_special("", tparams[ft.extra + k]) { params.append(mg); } else { params.append("v"); }
        }
        var cn: u8[>..] = [];
        var gv: u64 = 0;
        let g = lam_rec.get(L.rec as u64);
        if g { gv = g; }
        let off = ((gv >> 16) & 0xFFFFFF) as i64;
        let len = (gv & 0xFFFF) as i64;
        closure_name(L.rec, cn);
        var enc: u8[>..] = [];
        encl_enc(L.encl, enc);
        // operator(): [Z<enc>E]N[K]<closure>clE<params>
        var nm: u8[>..] = [];
        nm.append("_Z");
        nm.append(enc);
        nm.append("N");
        if cxs[L.op].flags & CF_CONST != 0 { nm.append("K"); }
        nm.append(cn);
        nm.append("clE");
        nm.append(params);
        lam_link(L.op, nm, linkonce);
        if L.inv >= 0 {
            var n2: u8[>..] = [];
            n2.append("_Z");
            n2.append(enc);
            n2.append("N");
            n2.append(cn);
            n2.append("8__invokeE");
            n2.append(params);
            lam_link(L.inv, n2, linkonce);
        }
        if L.conv >= 0 {
            var n3: u8[>..] = [];
            n3.append("_Z");
            n3.append(enc);
            n3.append("NK");
            n3.append(cn);
            n3.append("cv");
            if mangle_special("", types[syms[L.conv].ty >> 4].base) { n3.append(mg); }
            n3.append("Ev");
            lam_link(L.conv, n3, linkonce);
        }
    }
}

fn lam_link(f: i64, nm: u8[>..]&, linkonce: bool) {
    // the mangler's name when it has one (its substitutions count the
    // closure's name), else the one built here
    if mangle_sym(f) { set_label(f, mg); } else { set_label(f, nm); }
    cxl_grow();
    if linkonce {
        syms[f].sc = 0;
        set_link(f, LK_LINKONCE, CXL_COMDAT);
    } else {
        syms[f].sc = SC_STATIC as! u8;
    }
}
