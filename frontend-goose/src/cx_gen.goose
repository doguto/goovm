// goosecc D1: C++ code generation for a first subset ("C with classes").
//
// C++ constructs are expressed in C's AST (DESIGN.md 13.8), which the C
// lowering (gen_*.goose) compiles as it is. With code generation on
// (cg_on: -c / --emit-gir) the parser's semantic actions build these C
// nodes directly:
//
//   member functions   C functions with a leading `this` parameter (their
//                      ABI type: abi_type); calls pass the object's address
//   virtual calls      a load of the function pointer from the vtable
//                      (vtables and typeinfo are C arrays of pointers)
//   constructors       a declaration without initializer, then a call of
//                      the constructor on the object's address; bases,
//                      the vtable pointer, members and their default
//                      initializers in the constructor's prologue
//   destructors        C's cleanup attribute on the local variable; a
//                      destructor's epilogue destroys members and bases
//   references         pointers (types and uses rewritten in cg_finish)
//   new / delete       statement expressions calling operator new/delete
//   globals            a constructor function (.init_array) calling the
//                      constructors and registering the destructors with
//                      __cxa_atexit
//
// Names are the Itanium mangled names, given to the C lowering as asm
// labels. Inline functions are emitted on use, as internal functions.
// Anything outside the subset (templates instantiated implicitly,
// exceptions, temporaries with destructors, multiple polymorphic bases ...)
// is an opaque node, and cg_finish stops the compile with an error at
// the first one reachable from emitted code.

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
import .init;
import .builtins;
import .cx_core;
import .cx_names;
import .cx_decl;
import .cx_class;
import .cx_tmpl;
import .cx_decl2;
import .cx_expr;
import .cx_sema;
import .cx_over;
import .cx_layout;
import .cx_mangle;

let CF_DTOR_DELETING = 2147483648;  // the deleting destructor (D0) of a class with a virtual destructor

var cg_on: bool = false;        // C++ code generation: semantic actions build lowered C nodes
var cg_this: i64 = -1;          // the `this` parameter of the member function being parsed
var fn_this = dictionary<u64, u32> {};      // member function -> its `this` parameter symbol
var id_this: u32 = 0;

// ---------------------------------------------------------------------------
// ABI types: references are pointers; a member function takes `this` first.

var abi_types = dictionary<u64, u32> {};

recursive fn lower_ty(t: u32) -> u32 {
    let k = kind_of(t);
    if k == TY_LREF || k == TY_RREF { return mk_ptr(lower_ty(tbase(t))); }
    if k == TY_NULLPTR { return t_voidptr; }
    if k == TY_POINTER {
        let b = tbase(t);
        let lb = lower_ty(b);
        if lb == b { return t; }
        return with_q(mk_ptr(lb), quals(t));
    }
    if k == TY_FUNC {
        let f = types[t >> 4];
        var changed = false;
        let mark = abi_scratch.len;
        for i in f.n {
            let p = tparams[f.extra + i];
            let lp = lower_ty(p);
            if lp != p { changed = true; }
            abi_scratch.push(lp);
        }
        let ret = lower_ty(f.base);
        if ret != f.base { changed = true; }
        let fl = (f.flags as i64) & (TF_VARIADIC | TF_NORETURN | TF_NOPROTO);
        if !changed && (f.flags as i64) == fl { abi_scratch.resize(mark); return t; }
        fn_scratch.clear();
        for i in mark..abi_scratch.len { fn_scratch.push(abi_scratch[i]); }
        abi_scratch.resize(mark);
        return with_q(qt(mk_type(TY_FUNC, fl, ret, 0, 0, 0) as i64, 0), quals(t));
    }
    if k == TY_ARRAY {
        let e = tbase(t);
        let le = lower_ty(e);
        if le == e { return t; }
        return with_q(mk_array(le, types[t >> 4].n), quals(t));
    }
    return t;
}
var abi_scratch: u32[>..<] = [];

// The C type of function f: `this` first for a non-static member.
fn abi_type(f: i64) -> u32 {
    let g = abi_types.get(f as u64);
    if g { return g; }
    let ft = syms[f].ty;
    let lt = lower_ty(ft);
    var r = lt;
    if is_this_fn(f) {
        let lf = types[lt >> 4];
        let cls = scope_class_type(cxs[f].dscope as i64);
        var q: i64 = 0;
        if (types[ft >> 4].flags as i64) & TF_MCONST != 0 { q = Q_CONST; }
        let mark = abi_scratch.len;
        abi_scratch.push(mk_ptr(with_q(cls, q)));
        for i in lf.n { abi_scratch.push(tparams[lf.extra + i]); }
        fn_scratch.clear();
        for i in mark..abi_scratch.len { fn_scratch.push(abi_scratch[i]); }
        abi_scratch.resize(mark);
        r = qt(mk_type(TY_FUNC, (lf.flags as i64) & (TF_VARIADIC | TF_NORETURN), lf.base, 0, 0, 0) as i64, 0);
    }
    abi_types.insert(f as u64, r);
    return r;
}

fn is_this_fn(f: i64) -> bool { syms[f].kind as i64 == SK_FUNC && cxs[f].flags & CF_MEMBER != 0 && cxs[f].flags & CF_STATIC == 0 }

// ---------------------------------------------------------------------------
// Node helpers (C nodes).

fn n_ref_fn(f: i64, loc: u32) -> u32 {
    let n = node(N_DECLREF, 0, abi_type(f), f, 0, 0, loc);
    nodes[n].flags = NF_LVALUE;
    syms[f].flags = syms[f].flags | SF_USED;
    return n;
}

fn n_var(s: i64, loc: u32) -> u32 {
    let n = node(N_DECLREF, 0, nonref(syms[s].ty), s, 0, 0, loc);
    nodes[n].flags = (NF_LVALUE | (if is_ref(syms[s].ty) { NF_REFDEREF } else { 0 })) as! u16;
    return n;
}

fn n_addr(lv: u32, loc: u32) -> u32 { node(N_UNARY, U_ADDR, mk_ptr(nodes[lv].ty), lv as i64, 0, 0, loc) }

fn n_deref(p: u32, loc: u32) -> u32 {
    let n = node(N_UNARY, U_DEREF, tbase(nodes[p].ty), p as i64, 0, 0, loc);
    nodes[n].flags = NF_LVALUE;
    return n;
}

fn n_ptrcast(p: u32, to: u32, loc: u32) -> u32 {
    if nodes[p].ty == to { return p; }
    return node(N_ICAST, CK_BITCAST, to, p as i64, 0, 0, loc);
}

fn n_expr_stmt(e: u32) -> u32 { node(N_EXPR, 0, 0, e as i64, 0, 0, nodes[e].loc) }

fn n_null(loc: u32) -> u32 { node(N_NULL, 0, 0, 0, 0, 0, loc) }

// A compound statement of nscratch[mark..] (popped).
fn n_block(mark: i64, loc: u32) -> u32 {
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    return node_v(N_COMPOUND, 0, 0, 0, 0, count, loc, start);
}

// A call of f with the arguments in nscratch[mark..] (already converted to
// the ABI parameter types, `this` first); pops them.
fn n_call(f: i64, mark: i64, loc: u32) -> u32 {
    let callee = icast(n_ref_fn(f, loc), CK_FUNC2PTR, mk_ptr(abi_type(f)));
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    let at = abi_type(f);
    return node_v(N_CALL, 0, unqual(types[at >> 4].base), callee as i64, 0, count, loc, start);
}

// A call through a function pointer value fp (of type pointer to the ABI
// function type).
fn n_call_ptr(fp: u32, mark: i64, loc: u32) -> u32 {
    let ft = tbase(nodes[fp].ty);
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    return node_v(N_CALL, 0, unqual(types[ft >> 4].base), fp as i64, 0, count, loc, start);
}

// The address of glvalue `obj` as a pointer to class `cls` (a base class
// subobject when obj's class derives from it): `this` for a member call.
fn obj_addr_as(obj: u32, cls: u32, q: i64, loc: u32) -> u32 {
    var o = obj;
    if unqual(nodes[obj].ty) != unqual(cls) {
        let c = derived_to_base_lv(obj, cls, loc);
        if c == 0 { return 0; }
        o = c;
    }
    let a = n_addr(o, loc);
    return n_ptrcast(a, mk_ptr(with_q(unqual(cls), quals(nodes[o].ty) | q)), loc);
}

// A prvalue of class type as an object (a compound literal holding it).
fn materialize(e: u32, loc: u32) -> u32 {
    let t = unqual(nodes[e].ty);
    let s = csym(SK_VAR, 0, t, loc);
    syms[s].flags = SF_COMPLIT;
    let cl = node(N_COMPLIT, 0, t, e as i64, s, 0, loc);
    nodes[cl].flags = NF_LVALUE;
    return cl;
}

// ---------------------------------------------------------------------------
// Conversions for calls, initializations and returns.

// e converted to parameter type pt (C++ types; the result has the
// lowered type), or an opaque node.
recursive fn conv_arg(e: u32, pt: u32, loc: u32) -> u32 {
    if is_opq(e) && nodes[e].kind as i64 != N_FUNCREF && nodes[e].kind as i64 != N_INITBRACE { return opaque_node(loc); }
    if is_opaque(pt) { return opaque_node(loc); }
    if is_ref(pt) {
        let t = tbase(pt);
        if is_lvalue(e) && nodes[e].kind as i64 != N_INITBRACE {
            if unqual(nodes[e].ty) == unqual(t) { return n_ptrcast(n_addr(e, loc), lower_ty(mk_ptr(t)), loc); }
            if is_record(t) && is_record(nodes[e].ty) {
                let b = derived_to_base_lv(e, unqual(t), loc);
                if b != 0 { return n_ptrcast(n_addr(b, loc), lower_ty(mk_ptr(t)), loc); }
            }
        }
        // a temporary (a const or rvalue reference; trivially destructible types)
        if kind_of(pt) == TY_LREF && quals(t) & Q_CONST == 0 { return opaque_node(loc); }
        if is_record(t) && class_nontrivial_dtor(rec_of(t)) { return opaque_node(loc); }
        if is_record(t) && is_record(nodes[e].ty) && unqual(nodes[e].ty) == unqual(t) && nodes[e].kind as i64 != N_CTOR {
            // a class prvalue (a call result) bound to the reference
            return n_ptrcast(n_addr(materialize(e, loc), loc), lower_ty(mk_ptr(t)), loc);
        }
        let v = conv_value(e, unqual(t), loc);
        if is_opq(v) { return v; }
        return n_ptrcast(temp_addr(v, unqual(t), loc), lower_ty(mk_ptr(t)), loc);
    }
    return conv_value(e, unqual(pt), loc);
}

// A value of type t from e (a copy for a class: trivially copyable classes
// only; constructor calls build into a statement expression).
recursive fn conv_value(e: u32, t: u32, loc: u32) -> u32 {
    if is_opq(e) && nodes[e].kind as i64 != N_FUNCREF && nodes[e].kind as i64 != N_INITBRACE { return opaque_node(loc); }
    if nodes[e].kind as i64 == N_FUNCREF {
        let a = funcref_addr(e, loc);
        if is_opq(a) { return opaque_node(loc); }
        return conv_value(a, t, loc);
    }
    if is_record(t) {
        let r = rec_of(t);
        if !class_trivial_copy(r) { return opaque_node(loc); }
        if nodes[e].kind as i64 == N_CTOR { return ctor_value(e, loc); }
        if nodes[e].kind as i64 == N_INITBRACE {
            let bi = brace_init(t, e, loc);
            if bi == 0 { return opaque_node(loc); }
            return compound_value(bi, t, loc);
        }
        if unqual(nodes[e].ty) == unqual(t) {
            if is_lvalue(e) { return rv(e); }
            return e;
        }
        if is_record(nodes[e].ty) {
            let b = derived_to_base_lv(e, t, loc);
            if b != 0 && is_lvalue(b) { return rv(b); }
            return opaque_node(loc);
        }
        // a converting constructor
        let mark = nscratch.len;
        nscratch.push(e);
        let c = node(N_CTOR, 0, unqual(t), 0, 0, 1, loc);
        let st = commit_list(mark);
        nodes[c].v = st;
        return ctor_value(c, loc);
    }
    if nodes[e].kind as i64 == N_INITBRACE {
        let bi = brace_init(t, e, loc);
        if bi == 0 { return opaque_node(loc); }
        return bi;
    }
    if is_record(nodes[e].ty) {
        // a conversion function
        let c = user_conv(e, t, loc);
        if c == 0 { return opaque_node(loc); }
        return conv_value(c, t, loc);
    }
    if kind_of(nodes[e].ty) == TY_NULLPTR {
        if is_pointer(t) { return icast(e, CK_NULL2PTR, lower_ty(t)); }
        if kind_of(t) == TY_BOOL { return int_node(0, t_bool, loc); }
        return opaque_node(loc);
    }
    if !cish(t) || !cish_node(e) { return opaque_node(loc); }
    if kind_of(t) == TY_BOOL { return to_bool(e); }
    if is_pointer(t) {
        let c = cg_ptr_conv(rv(e), t, loc);
        if c != 0 { return c; }
    }
    return assign_convert(rv(e), t, loc, 2);
}

// A pointer to a derived class converted to a pointer to its base (the
// base subobject's offset added, a null pointer kept), or 0 when it is not
// such a conversion.
fn cg_ptr_conv(e: u32, to: u32, loc: u32) -> u32 {
    let ft = nodes[e].ty;
    if !is_pointer(ft) || !is_pointer(to) { return 0; }
    let a = unqual(tbase(ft));
    let b = unqual(tbase(to));
    if !is_record(a) || !is_record(b) || a == b { return 0; }
    let off = base_offset(a, b);
    if off < 0 { return 0; }
    if off == 0 { return node(N_ICAST, CK_BITCAST, unqual(to), e as i64, 0, 0, loc); }
    // ({ D *tmp = e; tmp ? (B *)((char *)tmp + off) : (B *)0; })
    let s = csym(SK_VAR, intern("__base_tmp"), unqual(ft), loc);
    syms[s].scope = 1;
    let mark = nscratch.len;
    nscratch.push(node(N_DECL, 0, unqual(ft), s, e as i64, loc as i64, loc));
    let v = rv(n_var(s, loc));
    let cp = node(N_ICAST, CK_BITCAST, mk_ptr(t_char), v as i64, 0, 0, loc);
    let add = node(N_BINARY, B_PTRADD, mk_ptr(t_char), cp as i64, int_node(off, t_long, loc) as i64, 0, loc);
    let bp = node(N_ICAST, CK_BITCAST, unqual(to), add as i64, 0, 0, loc);
    let z = node(N_ICAST, CK_NULL2PTR, unqual(to), int_node(0, t_int, loc) as i64, 0, 0, loc);
    let c = node(N_COND, 0, unqual(to), icast(rv(n_var(s, loc)), CK_PTR2BOOL, t_bool) as i64, bp as i64, z as i64, loc);
    nscratch.push(n_expr_stmt(c));
    let body = n_block(mark, loc);
    return node(N_STMTEXPR, 0, unqual(to), body as i64, 0, 0, loc);
}

// The address of a temporary holding value v (of type t): a compound
// literal, alive to the end of the enclosing block.
fn temp_addr(v: u32, t: u32, loc: u32) -> u32 {
    let s = csym(SK_VAR, 0, t, loc);
    syms[s].flags = SF_COMPLIT;
    if block_fn_depth == 0 { syms[s].sc = SC_STATIC as! u8; syms[s].flags = syms[s].flags | SF_FILESCOPE; }
    let cl = node(N_COMPLIT, 0, t, v as i64, s, 0, loc);
    nodes[cl].flags = NF_LVALUE;
    return n_addr(cl, loc);
}

// A class value built by a constructor call node (N_CTOR): a statement
// expression ({ T tmp; ctor(&tmp, args); tmp; }).
recursive fn ctor_value(c: u32, loc: u32) -> u32 {
    let t = nodes[c].ty;
    let s = csym(SK_VAR, intern("__ctor_tmp"), t, loc);
    syms[s].scope = 1;
    let mark = nscratch.len;
    // T(): value-initialization zeroes a class without a user-provided constructor
    var zi: u32 = 0;
    if nodes[c].c == 0 && !has_user_ctor(rec_of(t)) { zi = node(N_ZEROINIT, 0, unqual(t), 0, 0, 0, loc); }
    nscratch.push(node(N_DECL, 0, t, s, zi as i64, loc as i64, loc));
    let st = construct_stmt(s, c, loc);
    if st == 0 { nscratch.resize(mark); return opaque_node(loc); }
    nscratch.push(st);
    let v = rv(n_var(s, loc));
    nscratch.push(n_expr_stmt(v));
    let body = n_block(mark, loc);
    return node(N_STMTEXPR, 0, unqual(t), body as i64, 0, 0, loc);
}

fn compound_value(init: u32, t: u32, loc: u32) -> u32 {
    let s = csym(SK_VAR, 0, t, loc);
    syms[s].flags = SF_COMPLIT;
    if block_fn_depth == 0 { syms[s].sc = SC_STATIC as! u8; syms[s].flags = syms[s].flags | SF_FILESCOPE; }
    let cl = node(N_COMPLIT, 0, t, init as i64, s, 0, loc);
    nodes[cl].flags = NF_LVALUE;
    return rv(cl);
}

// e (of class type) converted by its class's conversion function to t, or 0.
recursive fn user_conv(e: u32, t: u32, loc: u32) -> u32 {
    let sc = type_scope(nodes[e].ty);
    if sc < 0 { return 0; }
    var s = class_lookup(sc, id_conv);
    var best: i64 = -1;
    while s >= 0 {
        let f = resolve(s);
        if f >= 0 && syms[f].kind as i64 == SK_FUNC && cxs[f].flags & CF_PATTERN == 0 {
            let rt = nonref(types[syms[f].ty >> 4].base);
            if unqual(rt) == unqual(t) { best = f; break; }
            if best < 0 && (is_arith(rt) || is_pointer(rt)) && (is_arith(t) || kind_of(t) == TY_BOOL) { best = f; }
        }
        s = cxs[s].nnext as i64;
    }
    if best < 0 { return 0; }
    var o = e;
    if !is_lvalue(o) { o = materialize(o, loc); }
    let mark = nscratch.len;
    return lower_call(best, o, mark, loc, true);
}

// A call's result: a reference result is the dereferenced pointer (an lvalue).
fn wrap_ref_result(c: u32, rt: u32) -> u32 {
    if is_ref(rt) {
        let d = n_deref(c, nodes[c].loc);
        nodes[d].ty = nonref(rt);
        if kind_of(rt) == TY_RREF { nodes[d].flags = nodes[d].flags | NF_XVALUE; }
        return d;
    }
    return c;
}

// A braced-init-list as a C initializer of t (an aggregate of C types, or
// a scalar), or 0.
recursive fn brace_init(t: u32, e: u32, loc: u32) -> u32 {
    if !c_initializable(t) { return 0; }
    let syn = to_syninit(e);
    if syn == 0 { return 0; }
    return init_value(0, unqual(t), syn, loc);
}

// Can t be initialized by C's rules (no constructors, virtual functions or
// bases anywhere in it)?
recursive fn c_initializable(t: u32) -> bool {
    if is_opaque(t) || is_ref(t) { return false; }
    if is_array(t) { return c_initializable(tbase(t)); }
    if is_record(t) {
        let r = rec_of(t);
        if crecs[r].nbases > 0 || crecs[r].flags & CR_DYNAMIC != 0 || has_user_ctor(r) || class_nontrivial_dtor(r) { return false; }
        let rec = records[r];
        let sc = crecs[r].scope as i64;
        for i in rec.first..rec.first + rec.count {
            let f = fields[i];
            if !c_initializable(f.ty) { return false; }
            if f.name != 0 && field_nsdmi(sc, f.name) != 0 { return false; }
        }
        return true;
    }
    return cish(t);
}

// N_INITBRACE -> C's syntactic list (N_SYNINIT) of C expressions, or 0.
recursive fn to_syninit(e: u32) -> u32 {
    let nd = nodes[e];
    if nd.kind as i64 == N_INITBRACE {
        if nd.op != 0 { return 0; }     // designators (D1 drops them while parsing)
        let mark = nscratch.len;
        for i in nd.c as i64 {
            let x = to_syninit(nlist[nd.v + i]);
            if x == 0 { nscratch.resize(mark); return 0; }
            nscratch.push(x);
        }
        let count = nscratch.len - mark;
        let start = commit_list(mark);
        return node_v(N_SYNINIT, 0, 0, 0, 0, count, nd.loc, start);
    }
    if is_opq(e) { return 0; }
    if kind_of(nd.ty) == TY_NULLPTR { return int_node(0, t_int, nd.loc); }
    if is_record(nd.ty) {
        if !class_trivial_copy(rec_of(nd.ty)) { return 0; }
        if nd.kind as i64 == N_CTOR { return ctor_value(e, nd.loc); }
        return e;
    }
    if !cish(nd.ty) { return 0; }
    return e;
}

// ---------------------------------------------------------------------------
// Calls of resolved functions.

// The call of f (resolved), object obj (a glvalue, 0 for none), arguments
// nscratch[mark..] (C++ expressions; popped). virt: dispatch through the
// vtable when f is virtual.
recursive fn lower_call(f: i64, obj: u32, mark: i64, loc: u32, virt: bool) -> u32 {
    let ft = types[syms[f].ty >> 4];
    if cxs[f].flags & (CF_DELETED | CF_PATTERN) != 0 || !by_value_ok(ft.base) { nscratch.resize(mark); return opaque_node(loc); }
    let nargs = nscratch.len - mark;
    // default arguments for the missing ones
    if nargs < ft.n {
        let st, pn = fn_param_list(f);
        if st < 0 || pn != ft.n { nscratch.resize(mark); return opaque_node(loc); }
        for i in nargs..ft.n {
            let p = nlist[st + i] as i64;
            if cxs[p].body == 0 { nscratch.resize(mark); return opaque_node(loc); }
            let d = default_arg(f, p);
            if d == 0 { nscratch.resize(mark); return opaque_node(loc); }
            nscratch.push(d);
        }
    }
    let n = nscratch.len - mark;
    // the converted arguments go above, then replace the originals
    let cm = nscratch.len;
    if is_this_fn(f) {
        if obj == 0 || !is_lvalue(obj) { nscratch.resize(mark); return opaque_node(loc); }
        let cls = scope_class_type(cxs[f].dscope as i64);
        let th = obj_addr_as(obj, cls, if cxs[f].flags & CF_CONST != 0 { Q_CONST } else { 0 }, loc);
        if th == 0 { nscratch.resize(mark); return opaque_node(loc); }
        nscratch.push(th);
    }
    for i in n {
        let a = nscratch[mark + i];
        var c: u32 = 0;
        if i < ft.n {
            let pt = tparams[ft.extra + i];
            if !by_value_ok(pt) { c = opaque_node(loc); } else { c = conv_arg(a, pt, loc); }
        } else {
            // the variadic part: C's default promotions
            if is_opq(a) || !cish_node(a) { c = opaque_node(loc); }
            else if kind_of(nodes[a].ty) == TY_NULLPTR { c = icast(a, CK_NULL2PTR, t_voidptr); }
            else { c = default_promote(rv(a)); }
        }
        if is_opq(c) { nscratch.resize(mark); return opaque_node(loc); }
        nscratch.push(c);
    }
    // move the converted ones down
    let total = nscratch.len - cm;
    for i in total { nscratch[mark + i] = nscratch[cm + i]; }
    nscratch.resize(mark + total);
    var call: u32 = 0;
    if virt && cxs[f].flags & CF_VIRTUAL != 0 && is_this_fn(f) {
        let fp = vfunc_ptr(f, nscratch[mark], 0, loc);
        if fp == 0 { nscratch.resize(mark); return opaque_node(loc); }
        call = n_call_ptr(fp, mark, loc);
    } else {
        call = n_call(f, mark, loc);
    }
    return wrap_ref_result(call, ft.base);
}

// A class passed or returned by value must be trivial for calls (Itanium:
// otherwise it goes by invisible reference).
fn by_value_ok(t: u32) -> bool {
    if !is_record(t) { return true; }
    if is_opaque(t) { return false; }
    return class_trivial_copy(rec_of(t));
}

// A default argument: its tokens parsed again in the function's declaring
// scope.
recursive fn default_arg(f: i64, p: i64) -> u32 {
    let sv = save();
    let s_scope = cur_scope;
    let s_class = cur_class;
    cur_scope = if cxs[f].dscope >= 0 { cxs[f].dscope as i64 } else { cur_scope };
    cur_class = -1;
    pc = cxs[p].body as i64;
    gt_pos = -1;
    var e: u32 = 0;
    if at(TK_L_BRACE) { e = parse_braced(); } else { e = parse_assign_cx(); }
    cur_scope = s_scope;
    cur_class = s_class;
    restore(sv);
    if is_opq(e) && nodes[e].kind as i64 != N_INITBRACE && nodes[e].kind as i64 != N_FUNCREF { return 0; }
    return e;
}

// The function pointer of virtual function f (slot + extra: 1 for the
// deleting destructor) for the object whose address (of f's class) is
// `th`: ((F**)*(void**)th)[slot].
fn vfunc_ptr(f: i64, th: u32, extra: i64, loc: u32) -> u32 {
    let cls = scope_class_type(cxs[f].dscope as i64);
    let r = rec_of(cls);
    let slot = vtable_slot(r, f);
    if slot < 0 { return 0; }
    var fpt = mk_ptr(abi_type(f));
    if extra != 0 { fpt = mk_ptr(abi_type(deleting_dtor(r))); }
    let pfp = mk_ptr(fpt);
    let vpp = n_ptrcast(th, mk_ptr(pfp), loc);       // F** *
    let vptr = rv(n_deref(vpp, loc));                // F**: the vtable's address point
    let idx = int_node(slot + extra, t_long, loc);
    let elem = node(N_BINARY, B_PTRADD, pfp, vptr as i64, idx as i64, 0, loc);
    return rv(n_deref(elem, loc));
}

// A resolved call in code generation (cx_over.build_call).
recursive fn cg_call(f: i64, obj0: u32, mark: i64, loc: u32, qualified: bool) -> u32 {
    var obj = obj0;
    if is_this_fn(f) && obj == 0 {
        if cg_this < 0 { nscratch.resize(mark); return opaque_node(loc); }
        obj = n_deref(cg_this_ref(loc), loc);
    }
    if !is_this_fn(f) { obj = 0; }
    if obj != 0 && !is_lvalue(obj) && is_record(nodes[obj].ty) && class_trivial_copy(rec_of(nodes[obj].ty)) {
        var v = obj;
        if nodes[v].kind as i64 == N_CTOR { v = ctor_value(v, loc); }
        if is_opq(v) { nscratch.resize(mark); return opaque_node(loc); }
        obj = materialize(v, loc);
    }
    return lower_call(f, obj, mark, loc, !qualified);
}

// `this` in a member function (an rvalue).
fn cg_this_ref(loc: u32) -> u32 {
    let n = node(N_DECLREF, 0, syms[cg_this].ty, cg_this, 0, 0, loc);
    nodes[n].flags = NF_LVALUE;
    return rv(n);
}

// The `this` parameter of member function s being defined.
fn make_this(s: i64, cls_ptr: u32, loc: u32) -> i64 {
    let g = fn_this.get(s as u64);
    if g { return g as i64; }
    let th = csym(SK_VAR, id_this, cls_ptr, loc);
    syms[th].flags = SF_PARAM;
    syms[th].scope = 1;
    fn_this.insert(s as u64, th as! u32);
    return th;
}

// A call of C's builtin `name` (not a library function: those are declared
// by the headers) with the arguments nscratch[mark..], or 0.
var cg_builtins = dictionary<u64, u32> {};
recursive fn cg_builtin_call(name: u32, mark: i64, loc: u32) -> u32 {
    let b = builtin_index(name);
    if b < 0 || is_library_name(ident_text(name as i64)) { return 0; }
    for i in mark..nscratch.len {
        let a = nscratch[i];
        if !cish_node(a) { return 0; }
        if kind_of(nodes[a].ty) == TY_NULLPTR { nscratch[i] = icast(a, CK_NULL2PTR, t_voidptr); }
    }
    var s: i64 = -1;
    let g = cg_builtins.get(name as u64);
    if g { s = g as i64; }
    else {
        var ty = builtin_type(b);
        if ty == 0 {
            fn_scratch.clear();
            ty = qt(mk_type(TY_FUNC, TF_NOPROTO, t_int, 0, 0, 0) as i64, 0);
        }
        s = new_sym(SK_BUILTIN, name, ty, loc);
        cx_grow();
        syms[s].v = b;
        syms[s].sc = SC_EXTERN as! u8;
        syms[s].flags = SF_FILESCOPE;
        if builtin_flags(b) & 1 != 0 { syms[s].flags = syms[s].flags | SF_NORETURN; }
        cg_builtins.insert(name as u64, s as! u32);
    }
    let callee = node(N_DECLREF, 0, syms[s].ty, s, 0, 0, loc);
    nodes[callee].flags = NF_LVALUE;
    let c = mk_call(callee, mark, loc);
    return c;
}

// ---------------------------------------------------------------------------
// Operators on classes.

// The call of operator `op` for operands l (and r; post: a postfix ++/--),
// or 0 when no candidate is found. Member candidates first, then those of
// the enclosing namespaces and of the operands' classes' namespaces.
recursive fn cg_operator(op: i64, l: u32, r: u32, loc: u32, post: bool) -> u32 {
    if is_opq(l) || (r != 0 && is_opq(r) && nodes[r].kind as i64 != N_INITBRACE) { return 0; }
    let name = op_ids[op];
    let mark = nscratch.len;
    if is_record(nodes[l].ty) {
        let sc = type_scope(nodes[l].ty);
        if sc >= 0 {
            let s = class_lookup(sc, name);
            if s >= 0 {
                if r != 0 { nscratch.push(r); }
                if post { nscratch.push(int_node(0, t_int, loc)); }
                let f = best_candidate(s, mark, true);
                if f >= 0 { return cg_call(f, l, mark, loc, false); }
                nscratch.resize(mark);
            }
        }
    }
    // non-member candidates
    var tried0: i64 = -2;
    for which in 3 {
        var sc: i64 = -1;
        if which == 0 { sc = enclosing_ns(cur_scope); }
        else if which == 1 { if is_record(nodes[l].ty) { sc = enclosing_ns(type_scope(nodes[l].ty)); } }
        else if r != 0 && is_record(nodes[r].ty) { sc = enclosing_ns(type_scope(nodes[r].ty)); }
        if sc < 0 || sc == tried0 { continue; }
        if which == 0 { tried0 = sc; }
        let s = if which == 0 { unqual_lookup_from(sc, name) } else { ns_lookup(sc, name, false) };
        if s < 0 { continue; }
        nscratch.push(l);
        if r != 0 { nscratch.push(r); }
        if post { nscratch.push(int_node(0, t_int, loc)); }
        let f = best_candidate(s, mark, false);
        if f >= 0 && cxs[f].flags & CF_MEMBER == 0 { return lower_call(f, 0, mark, loc, false); }
        nscratch.resize(mark);
    }
    return 0;
}

// a = b / a op= b with a class operand.
recursive fn cg_assign(op: i64, l: u32, r: u32, loc: u32, tok: i64) -> u32 {
    let o = cg_operator(tok_op(tok), l, r, loc, false);
    if o != 0 { return o; }
    if op != 0 || !is_record(nodes[l].ty) || !is_lvalue(l) { return 0; }
    let t = unqual(nodes[l].ty);
    if !class_trivial_copy(rec_of(t)) { return 0; }
    let v = conv_value(r, t, loc);
    if is_opq(v) { return 0; }
    let n = node(N_ASSIGN, 0, t, l as i64, v as i64, 0, loc);
    nodes[n].flags = NF_LVALUE;
    return n;
}

// ---------------------------------------------------------------------------
// Class facts for code generation.

recursive fn class_nontrivial_dtor(r: i64) -> bool {
    if crecs[r].flags & (CR_NONTRIVIAL_DTOR | CR_USER_DTOR) != 0 { return true; }
    let rec = records[r];
    for i in rec.first..rec.first + rec.count {
        let bt = base_elem_t(fields[i].ty);
        if is_record(bt) && !is_opaque(bt) && class_nontrivial_dtor(rec_of(bt)) { return true; }
    }
    let cr = crecs[r];
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if is_record(b.ty) && class_nontrivial_dtor(rec_of(b.ty)) { return true; }
    }
    return false;
}

// Trivially copyable and trivial for calls (no user-declared copy
// operations or destructor, no virtual functions, in it or its bases and
// members): passed, returned and copied as a C struct.
recursive fn class_trivial_copy(r: i64) -> bool {
    if r >= crecs.len || crecs[r].flags & CR_LAYOUT == 0 { return false; }
    if crecs[r].flags & (CR_DYNAMIC | CR_HAS_USER_COPY | CR_HAS_MOVE) != 0 { return false; }
    if class_nontrivial_dtor(r) { return false; }
    if find_copy_ctor(r) >= 0 { return false; }
    let rec = records[r];
    for i in rec.first..rec.first + rec.count {
        let ft = fields[i].ty;
        if is_ref(ft) || is_opaque(ft) { return false; }
        let bt = base_elem_t(ft);
        if is_record(bt) && !class_trivial_copy(rec_of(bt)) { return false; }
    }
    let cr = crecs[r];
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if b.flags & BF_VIRTUAL != 0 { return false; }
        if is_record(b.ty) && !class_trivial_copy(rec_of(b.ty)) { return false; }
    }
    return true;
}

// A user-declared copy or move constructor of r, or -1.
fn find_copy_ctor(r: i64) -> i64 {
    let sc = crecs[r].scope as i64;
    var s = scope_find(sc, id_ctor);
    let cls = records[r].ty << 4;
    while s >= 0 {
        let f = resolve(s);
        if f >= 0 && syms[f].kind as i64 == SK_FUNC && cxs[f].flags & CF_IMPLICIT == 0 {
            let ft = types[syms[f].ty >> 4];
            if ft.n >= 1 {
                let p0 = tparams[ft.extra];
                if is_ref(p0) && unqual(tbase(p0)) == cls && defaults_from(f, 1) {
                    // a defaulted one is trivial when the implicit one would be
                    if cxs[f].flags & CF_DEFAULTED == 0 { return f; }
                }
            }
        }
        s = cxs[s].nnext as i64;
    }
    return -1;
}

// Does constructing r by default need code (a vtable pointer, members or
// bases with constructors or default member initializers)?
recursive fn needs_default_init(r: i64) -> bool {
    if crecs[r].flags & CR_DYNAMIC != 0 { return true; }
    if has_user_ctor(r) { return true; }
    let rec = records[r];
    let sc = crecs[r].scope as i64;
    for i in rec.first..rec.first + rec.count {
        let f = fields[i];
        let bt = base_elem_t(f.ty);
        if is_record(bt) && !is_opaque(bt) && needs_default_init(rec_of(bt)) { return true; }
        if f.name != 0 && field_nsdmi(sc, f.name) != 0 { return true; }
    }
    let cr = crecs[r];
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if is_record(b.ty) && needs_default_init(rec_of(b.ty)) { return true; }
    }
    return false;
}

// A user-provided constructor (not implicit, not defaulted).
fn has_user_ctor(r: i64) -> bool {
    let sc = crecs[r].scope as i64;
    var s = scope_find(sc, id_ctor);
    while s >= 0 {
        let f = resolve(s);
        if f >= 0 && syms[f].kind as i64 == SK_FUNC && cxs[f].flags & (CF_IMPLICIT | CF_DEFAULTED) == 0 { return true; }
        s = cxs[s].nnext as i64;
    }
    return false;
}

// The member symbol of field `name` in class scope sc with a default member
// initializer (its tokens in cxs.body), or 0.
fn field_nsdmi(sc: i64, name: u32) -> i64 {
    var s = scope_find(sc, name);
    while s >= 0 {
        if syms[s].kind as i64 == SK_FIELD && cxs[s].body != 0 { return s; }
        s = cxs[s].nnext as i64;
    }
    return 0;
}

// ---------------------------------------------------------------------------
// Constructors and destructors.

// The constructor of class r for the arguments nscratch[mark..]: a
// function, -2 (no code: a class that needs no initialization), -3 (a
// trivial copy: an assignment), or -1 (D1 cannot).
fn pick_ctor(r: i64, mark: i64) -> i64 {
    let n = nscratch.len - mark;
    let cls = records[r].ty << 4;
    let sc = crecs[r].scope as i64;
    let s = scope_find(sc, id_ctor);
    if s >= 0 {
        let f = best_candidate(s, mark, true);
        if f >= 0 {
            if cxs[f].flags & CF_DEFAULTED == 0 { return f; }
            // a defaulted one: as the implicit one
        } else if has_user_ctor(r) {
            if n == 1 && is_record(nodes[nscratch[mark]].ty) && unqual(nodes[nscratch[mark]].ty) == cls && class_trivial_copy(r) { return -3; }
            return -1;
        }
    }
    if n == 0 {
        if !needs_default_init(r) { return -2; }
        return implicit_default_ctor(r);
    }
    if n == 1 {
        let a = nscratch[mark];
        if !is_opq(a) && is_record(nodes[a].ty) && unqual(nodes[a].ty) == cls && class_trivial_copy(r) { return -3; }
    }
    return -1;
}

// The statement constructing variable s from the constructor node c (an
// N_CTOR: v/c = arguments), 0 when D1 cannot.
recursive fn construct_stmt(s: i64, c: u32, loc: u32) -> u32 {
    let nd = nodes[c];
    let mark = nscratch.len;
    for i in nd.c as i64 { nscratch.push(nlist[nd.v + i]); }
    return construct_at(n_var(s, loc), mark, loc);
}

// Constructs the object at lvalue `obj` (class type) with the arguments
// nscratch[mark..] (popped): a statement, or 0.
recursive fn construct_at(obj: u32, mark: i64, loc: u32) -> u32 {
    let t = nodes[obj].ty;
    if !is_record(t) || is_opaque(t) { nscratch.resize(mark); return 0; }
    let r = rec_of(t);
    for i in mark..nscratch.len {
        let a = nscratch[i];
        if is_opq(a) && nodes[a].kind as i64 != N_INITBRACE && nodes[a].kind as i64 != N_FUNCREF { nscratch.resize(mark); return 0; }
    }
    let f = pick_ctor(r, mark);
    if f == -2 { nscratch.resize(mark); return n_null(loc); }
    if f == -3 {
        let src = nscratch[mark];
        nscratch.resize(mark);
        let a = node(N_ASSIGN, 0, unqual(t), obj as i64, (if is_lvalue(src) { rv(src) } else { src }) as i64, 0, loc);
        return n_expr_stmt(a);
    }
    if f < 0 { nscratch.resize(mark); return 0; }
    let call = lower_call(f, obj, mark, loc, false);
    if is_opq(call) { return 0; }
    return n_expr_stmt(call);
}

// The destructor of class r (user-declared or implicit), or -1 if trivial.
fn class_dtor(r: i64) -> i64 {
    let sc = crecs[r].scope as i64;
    let s = scope_find(sc, id_dtor);
    if s >= 0 {
        let f = resolve(s);
        if f >= 0 && syms[f].kind as i64 == SK_FUNC && cxs[f].flags & CF_DEFAULTED == 0 { return f; }
    }
    if !class_nontrivial_dtor(r) { return -1; }
    return implicit_dtor(r);
}

// The destructor call for the object at lvalue obj (a statement), 0 none.
fn destroy_stmt(obj: u32, loc: u32) -> u32 {
    let r = rec_of(nodes[obj].ty);
    let d = class_dtor(r);
    if d < 0 { return 0; }
    let mark = nscratch.len;
    let call = lower_call(d, obj, mark, loc, false);
    if is_opq(call) { return mark_bad_stmt(loc); }
    return n_expr_stmt(call);
}

fn mark_bad_stmt(loc: u32) -> u32 { n_expr_stmt(opaque_node(loc)) }

// ---------------------------------------------------------------------------
// Implicit special members (defined when used).

var implicit_ctors = dictionary<u64, u32> {};
var implicit_dtors = dictionary<u64, u32> {};
var deleting_dtors = dictionary<u64, u32> {};
var pending_bodies: u32[>..] = [];   // (function, kind) whose bodies are synthesized at the end: 1 ctor, 2 dtor, 3 deleting dtor

fn new_member_fn(r: i64, name: u32, flags: u32, loc: u32) -> i64 {
    fn_scratch.clear();
    let ft = qt(mk_type(TY_FUNC, 0, t_void, 0, 0, 0) as i64, 0);
    let s = csym(SK_FUNC, name, ft, loc);
    let sc = crecs[r].scope as i64;
    cxs[s].dscope = sc as! i32;
    cxs[s].flags = flags | CF_MEMBER | CF_IMPLICIT | CF_DEFINED_IN_CLASS;
    syms[s].flags = SF_INLINE | SF_DEFINED;
    return s;
}

fn implicit_default_ctor(r: i64) -> i64 {
    let g = implicit_ctors.get(r as u64);
    if g { return g as i64; }
    let s = new_member_fn(r, id_ctor, CF_CTOR, records[r].loc);
    implicit_ctors.insert(r as u64, s as! u32);
    pending_bodies.push(s as! u32);
    pending_bodies.push(1);
    return s;
}

fn implicit_dtor(r: i64) -> i64 {
    let g = implicit_dtors.get(r as u64);
    if g { return g as i64; }
    let s = new_member_fn(r, id_dtor, CF_DTOR, records[r].loc);
    // a destructor overriding a virtual one is virtual
    if crecs[r].flags & CR_DYNAMIC != 0 && dtor_virtual_in_bases(r) { cxs[s].flags = cxs[s].flags | CF_VIRTUAL; }
    implicit_dtors.insert(r as u64, s as! u32);
    pending_bodies.push(s as! u32);
    pending_bodies.push(2);
    return s;
}

recursive fn dtor_virtual_in_bases(r: i64) -> bool {
    let cr = crecs[r];
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if !is_record(b.ty) { continue; }
        let br = rec_of(b.ty);
        let s = scope_find(crecs[br].scope as i64, id_dtor);
        if s >= 0 && cxs[resolve(s)].flags & CF_VIRTUAL != 0 { return true; }
        let g = implicit_dtors.get(br as u64);
        if g { if cxs[g].flags & CF_VIRTUAL != 0 { return true; } }
        if dtor_virtual_in_bases(br) { return true; }
    }
    return false;
}

// The deleting destructor (D0) of class r: the destructor, then
// operator delete.
fn deleting_dtor(r: i64) -> i64 {
    let g = deleting_dtors.get(r as u64);
    if g { return g as i64; }
    let s = new_member_fn(r, id_dtor, CF_DTOR | CF_DTOR_DELETING, records[r].loc);
    deleting_dtors.insert(r as u64, s as! u32);
    pending_bodies.push(s as! u32);
    pending_bodies.push(3);
    return s;
}

// ---------------------------------------------------------------------------
// Constructor prologues and destructor epilogues (C statements pushed to
// stmt_buf), for user-declared and implicit ones. th: the `this` symbol.

var stmt_buf: u32[>..<] = [];

// The vtable pointer store for class r (dynamic): *(void***)this = &vtable[2].
fn vptr_store(r: i64, th: i64, loc: u32) -> u32 {
    let vt = vtable_sym(r);
    if vt < 0 { return 0; }
    let ppv = mk_ptr(t_voidptr);
    let this_v = rv(n_var(th, loc));
    let dst = n_deref(n_ptrcast(this_v, mk_ptr(ppv), loc), loc);        // the vptr (void** lvalue)
    let vtd = n_var(vt, loc);
    let base = icast(vtd, CK_ARRAY2PTR, ppv);
    let ap = node(N_BINARY, B_PTRADD, ppv, base as i64, int_node(2, t_long, loc) as i64, 0, loc);
    let a = node(N_ASSIGN, 0, ppv, dst as i64, ap as i64, 0, loc);
    return n_expr_stmt(a);
}

// this->member as an lvalue (field index fi of class r).
fn this_member(th: i64, r: i64, fi: i64, loc: u32) -> u32 {
    let this_v = rv(n_var(th, loc));
    let obj = n_deref(this_v, loc);
    let f = fields[fi];
    let n = node(N_MEMBER, 0, nonref(f.ty), obj as i64, fi, 0, loc);
    var fl = NF_LVALUE;
    if is_ref(f.ty) { fl = fl | NF_REFDEREF; }
    if f.width >= 0 { fl = fl | NF_BITFIELD; }
    nodes[n].flags = fl as! u16;
    return n;
}

// The base subobject (class bt) of *this as an lvalue.
fn this_base(th: i64, bt: u32, loc: u32) -> u32 {
    let this_v = rv(n_var(th, loc));
    let obj = n_deref(this_v, loc);
    return derived_to_base_lv(obj, bt, loc);
}

// The prologue of a constructor of r: bases, vptr, members (inits: the
// mem-initializers, an N_INITBRACE of N_CXX(op 1, ty = base type, a =
// member symbol, b = args) or 0). Returns false when D1 cannot.
recursive fn ctor_prologue(r: i64, th: i64, inits: u32, loc: u32) -> bool {
    let cr = crecs[r];
    let sc = cr.scope as i64;
    // a delegating constructor: X() : X(args)
    let cls = records[r].ty << 4;
    if inits != 0 && nodes[inits].c == 1 {
        let mi = nlist[nodes[inits].v];
        if nodes[mi].ty != 0 && unqual(nodes[mi].ty) == cls {
            let obj = n_deref(rv(n_var(th, loc)), loc);
            let mark = nscratch.len;
            push_init_args(nodes[mi].b);
            let st = construct_at(obj, mark, loc);
            if st == 0 { return false; }
            stmt_buf.push(st);
            return true;
        }
    }
    // the bases
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if b.flags & BF_VIRTUAL != 0 || !is_record(b.ty) { return false; }
        let mi = find_init(inits, -1, b.ty);
        let obj = this_base(th, b.ty, loc);
        if obj == 0 { return false; }
        let mark = nscratch.len;
        if mi != 0 { push_init_args(nodes[mi].b); }
        let st = construct_at(obj, mark, loc);
        if st == 0 { return false; }
        stmt_buf.push(st);
    }
    if cr.flags & CR_DYNAMIC != 0 {
        let vs = vptr_store(r, th, loc);
        if vs == 0 { return false; }
        stmt_buf.push(vs);
    }
    // the members, in order
    let rec = records[r];
    for i in rec.first..rec.first + rec.count {
        let f = fields[i];
        if f.name == 0 { continue; }
        let msym = member_sym(sc, f.name);
        let mi = find_init(inits, msym, 0);
        let lv = this_member(th, r, i, loc);
        let ft = f.ty;
        var args: u32 = 0;
        if mi != 0 { args = nodes[mi].b; }
        else if msym >= 0 && cxs[msym].body != 0 {
            // the default member initializer
            args = nsdmi_value(msym, sc, th);
            if args == 0 { return false; }
        }
        if is_array(ft) {
            let bt = base_elem_t(ft);
            if is_record(bt) && (needs_default_init(rec_of(bt)) || args != 0) { return false; }
            if args == 0 { continue; }
            let bi = brace_init(ft, args, loc);
            if bi == 0 { return false; }
            let tmp = compound_value(bi, unqual(ft), loc);
            // arrays are copied as a whole: memcpy-like struct copy is not C; one element at a time
            let n = types[ft >> 4].n;
            let src_lv = nodes[tmp].a;     // the compound literal (rv(complit) = ICAST(ARRAY2PTR))
            for j in n {
                let el = node(N_INDEX, 0, tbase(ft), icast(lv, CK_ARRAY2PTR, mk_ptr(tbase(ft))) as i64, int_node(j, t_long, loc) as i64, 0, loc);
                nodes[el].flags = NF_LVALUE;
                let sel = node(N_INDEX, 0, tbase(ft), icast(src_lv, CK_ARRAY2PTR, mk_ptr(tbase(ft))) as i64, int_node(j, t_long, loc) as i64, 0, loc);
                nodes[sel].flags = NF_LVALUE;
                stmt_buf.push(n_expr_stmt(node(N_ASSIGN, 0, unqual(tbase(ft)), el as i64, rv(sel) as i64, 0, loc)));
            }
            continue;
        }
        if is_record(ft) {
            let mark = nscratch.len;
            if args != 0 {
                if nodes[args].kind as i64 == N_INITBRACE && nodes[args].op == 0 && c_initializable(ft) && !has_user_ctor(rec_of(ft)) {
                    // an aggregate member initialized by a braced list
                    let bi = brace_init(ft, args, loc);
                    if bi == 0 { return false; }
                    stmt_buf.push(n_expr_stmt(node(N_ASSIGN, 0, unqual(ft), lv as i64, compound_value(bi, unqual(ft), loc) as i64, 0, loc)));
                    continue;
                }
                push_init_args(args);
            }
            let st = construct_at(lv, mark, loc);
            if st == 0 { return false; }
            stmt_buf.push(st);
            continue;
        }
        if args == 0 { continue; }
        // a scalar (or reference) member: its initial value
        let n = if nodes[args].kind as i64 == N_INITBRACE { nodes[args].c as i64 } else { 1 };
        if n == 0 {
            if is_ref(ft) { return false; }
            stmt_buf.push(n_expr_stmt(node(N_ASSIGN, 0, unqual(ft), lv as i64, node(N_ZEROINIT, 0, unqual(ft), 0, 0, 0, loc) as i64, 0, loc)));
            continue;
        }
        let e = if nodes[args].kind as i64 == N_INITBRACE { nlist[nodes[args].v] } else { args };
        if is_ref(ft) {
            let p = conv_arg(e, ft, loc);
            if is_opq(p) { return false; }
            // store the address: the member's own pointer slot
            let slot = node(N_MEMBER, 0, lower_ty(ft), nodes[lv].a as i64, i, 0, loc);
            nodes[slot].flags = NF_LVALUE;
            stmt_buf.push(n_expr_stmt(node(N_ASSIGN, 0, lower_ty(ft), slot as i64, p as i64, 0, loc)));
            continue;
        }
        let v = conv_value(e, unqual(ft), loc);
        if is_opq(v) { return false; }
        stmt_buf.push(n_expr_stmt(node(N_ASSIGN, 0, unqual(ft), lv as i64, v as i64, 0, loc)));
    }
    return true;
}

fn member_sym(sc: i64, name: u32) -> i64 {
    var s = scope_find(sc, name);
    while s >= 0 {
        if syms[s].kind as i64 == SK_FIELD { return s; }
        s = cxs[s].nnext as i64;
    }
    return -1;
}

// The mem-initializer for member msym (or base type bt), or 0.
fn find_init(inits: u32, msym: i64, bt: u32) -> u32 {
    if inits == 0 { return 0; }
    let n = nodes[inits].c as i64;
    for i in n {
        let mi = nlist[nodes[inits].v + i];
        if msym >= 0 && nodes[mi].a as i64 == msym { return mi; }
        if bt != 0 && nodes[mi].ty != 0 && unqual(nodes[mi].ty) == unqual(bt) { return mi; }
    }
    return 0;
}

fn push_init_args(args: u32) {
    if args == 0 { return; }
    if nodes[args].kind as i64 == N_INITBRACE {
        for i in nodes[args].c as i64 { nscratch.push(nlist[nodes[args].v + i]); }
    } else {
        nscratch.push(args);
    }
}

// A default member initializer's value, parsed in the class's scope with
// `this` the constructor's.
recursive fn nsdmi_value(m: i64, sc: i64, th: i64) -> u32 {
    let sv = save();
    let s_scope = cur_scope;
    let s_this = cg_this;
    let s_tt = this_type;
    cur_scope = sc;
    cg_this = th;
    this_type = syms[th].ty;
    pc = cxs[m].body as i64;
    gt_pos = -1;
    if at(TK_EQUAL) { adv(); }
    var e: u32 = 0;
    if at(TK_L_BRACE) { e = parse_braced(); } else { e = parse_assign_cx(); }
    cur_scope = s_scope;
    cg_this = s_this;
    this_type = s_tt;
    restore(sv);
    if is_opq(e) && nodes[e].kind as i64 != N_INITBRACE { return 0; }
    return e;
}

// The epilogue of a destructor of r: members in reverse order, then bases.
recursive fn dtor_epilogue(r: i64, th: i64, loc: u32) -> bool {
    let rec = records[r];
    var i = (rec.first + rec.count) as i64 - 1;
    while i >= rec.first as i64 {
        let f = fields[i];
        if f.name != 0 && is_record(f.ty) && !is_opaque(f.ty) {
            let st = destroy_stmt(this_member(th, r, i, loc), loc);
            if st != 0 { stmt_buf.push(st); }
        } else if f.name != 0 && is_array(f.ty) {
            let bt = base_elem_t(f.ty);
            if is_record(bt) && class_dtor(rec_of(bt)) >= 0 { return false; }
        }
        i--;
    }
    let cr = crecs[r];
    var b = cr.nbases as i64 - 1;
    while b >= 0 {
        let bb = cbases[cr.bases + b];
        if bb.flags & BF_VIRTUAL != 0 { return false; }
        if is_record(bb.ty) {
            let obj = this_base(th, bb.ty, loc);
            if obj == 0 { return false; }
            let st = destroy_stmt(obj, loc);
            if st != 0 { stmt_buf.push(st); }
        }
        b--;
    }
    return true;
}

// The body of member function s (parsed: body) with its constructor
// prologue or destructor epilogue (cx_stmt.parse_function_body).
recursive fn cg_wrap_body(s: i64, body: u32, inits: u32, loc: u32) -> u32 {
    let fl = cxs[s].flags;
    if fl & (CF_CTOR | CF_DTOR) == 0 || cg_this < 0 { return body; }
    let r = rec_of(scope_class_type(cxs[s].dscope as i64));
    let sm = stmt_buf.len;
    var ok = true;
    if fl & CF_CTOR != 0 {
        ok = ctor_prologue(r, cg_this, inits, loc);
    } else {
        if crecs[r].flags & CR_DYNAMIC != 0 {
            let vs = vptr_store(r, cg_this, loc);
            if vs == 0 { ok = false; } else { stmt_buf.push(vs); }
        }
    }
    let mark = nscratch.len;
    if fl & CF_CTOR != 0 {
        for i in sm..stmt_buf.len { nscratch.push(stmt_buf[i]); }
        stmt_buf.resize(sm);
        nscratch.push(body);
    } else {
        for i in sm..stmt_buf.len { nscratch.push(stmt_buf[i]); }
        stmt_buf.resize(sm);
        // a return in the body would skip the epilogue
        if has_return(body) { ok = false; }
        nscratch.push(body);
        let em = stmt_buf.len;
        if !dtor_epilogue(r, cg_this, loc) { ok = false; }
        for i in em..stmt_buf.len { nscratch.push(stmt_buf[i]); }
        stmt_buf.resize(em);
    }
    if !ok { nscratch.push(mark_bad_stmt(loc)); }
    return n_block(mark, loc);
}

// ---------------------------------------------------------------------------
// Variables.

var gi_stmts: u32[>..] = [];     // the dynamic initialization of namespace-scope variables, in order

// The N_DECL of variable s (block or namespace scope, ctx) with initializer
// `init` as written (form: 0 none, 1 =, 2 (), 3 {}) and conv as C's path
// converted it; pushes it to nscratch with the construction of a class
// object (cx_sema.parse_var_init).
recursive fn cg_decl(s: i64, init: u32, conv0: u32, form: i64, loc: u32, dloc: u32, ctx: i64) {
    var conv = conv0;
    let t = syms[s].ty;
    if ctx == DC_NS || cxs[s].flags & CF_MEMBER != 0 { syms[s].flags = syms[s].flags | SF_FILESCOPE; }
    let fs = syms[s].flags & SF_FILESCOPE != 0;
    if !decl_is_extern && syms[s].sc as i64 == SC_EXTERN { syms[s].sc = 0; }
    let is_extern = syms[s].sc as i64 == SC_EXTERN;
    let local = !fs && !is_extern;
    let static_local = fs && block_fn_depth > 0;
    var cst: u32 = 0;
    var has_dtor = false;
    if is_ref(t) {
        if init != 0 {
            var e = init;
            if nodes[e].kind as i64 == N_INITBRACE && nodes[e].c == 1 { e = nlist[nodes[e].v]; }
            conv = conv_arg(e, t, loc);
        }
    } else if is_record(t) && !is_opaque(t) && !is_extern {
        let r = rec_of(t);
        conv = 0;
        has_dtor = class_dtor(r) >= 0;
        if init != 0 && nodes[init].kind as i64 == N_INITBRACE && c_initializable(t) {
            // an aggregate: C's initializer
            let bi = brace_init(t, init, loc);
            conv = if bi != 0 { bi } else { opaque_node(loc) };
        } else if init != 0 && nodes[init].kind as i64 != N_CTOR && nodes[init].kind as i64 != N_INITBRACE &&
                  !is_opq(init) && is_record(nodes[init].ty) && unqual(nodes[init].ty) == unqual(t) && class_trivial_copy(r) {
            // a copy of a trivially copyable class: C's initialization
            conv = if is_lvalue(init) { rv(init) } else { init };
        } else {
            let mark = nscratch.len;
            if init != 0 {
                let k = nodes[init].kind as i64;
                if k == N_CTOR { for i in nodes[init].c as i64 { nscratch.push(nlist[nodes[init].v + i]); } }
                else if k == N_INITBRACE { for i in nodes[init].c as i64 { nscratch.push(nlist[nodes[init].v + i]); } }
                else { nscratch.push(init); }
            }
            // T x = T() / T x{}: value-initialization zeroes a class without a user-provided constructor
            if init != 0 && nodes[init].c == 0 && (nodes[init].kind as i64 == N_CTOR || nodes[init].kind as i64 == N_INITBRACE) && !has_user_ctor(r) {
                conv = node(N_ZEROINIT, 0, unqual(t), 0, 0, 0, loc);
            }
            let ob = n_var(s, loc);
            cst = construct_at(ob, mark, loc);
            if cst == 0 { cst = mark_bad_stmt(loc); }
            else if nodes[cst].kind as i64 == N_NULL { cst = 0; }
        }
        if is_array(t) { conv = opaque_node(loc); }
    } else if is_array(t) && is_record(base_elem_t(t)) && !is_opaque(base_elem_t(t)) {
        let br = rec_of(base_elem_t(t));
        if needs_default_init(br) || class_dtor(br) >= 0 { conv = opaque_node(loc); }
        else if init != 0 && nodes[init].kind as i64 == N_INITBRACE {
            let bi = brace_init(t, init, loc);
            conv = if bi != 0 { bi } else { opaque_node(loc) };
        }
    } else if init != 0 && nodes[init].kind as i64 == N_INITBRACE {
        let bi = brace_init(t, init, loc);
        conv = if bi != 0 { bi } else { opaque_node(loc) };
        if bi != 0 && is_array(t) && types[t >> 4].n < 0 { syms[s].ty = with_q(nodes[bi].ty, quals(t)); }
    } else if init != 0 && conv != 0 && is_pointer(t) && !is_opq(init) {
        let c = cg_ptr_conv(rv(init), unqual(t), loc);
        if c != 0 { conv = c; }
    } else if init != 0 && conv != 0 && !is_opq(init) && is_record(nodes[init].ty) && cish(t) {
        // a conversion function
        conv = conv_value(init, unqual(t), loc);
    }
    // the dynamic initialization of a namespace-scope (or static local) variable
    if !local && conv != 0 && !is_opq(conv) {
        nc_node = 0;
        if !const_init(conv) {
            if static_local { conv = opaque_node(loc); }
            else {
                let lhs = node(N_DECLREF, 0, lower_ty(t), s, 0, 0, loc);
                nodes[lhs].flags = NF_LVALUE;
                gi_stmts.push(n_expr_stmt(node(N_ASSIGN, 0, unqual(lower_ty(t)), lhs as i64, conv as i64, 0, loc)));
                conv = 0;
            }
        }
    }
    if !is_extern && (fs || init != 0) { syms[s].flags = syms[s].flags | SF_DEFINED; }
    if static_local && (cst != 0 || has_dtor) { conv = opaque_node(loc); cst = 0; }
    nscratch.push(node(N_DECL, 0, syms[s].ty, s, conv as i64, dloc as i64, loc));
    if ctx == DC_COND && cst != 0 { nscratch.push(mark_bad_stmt(loc)); return; }
    if local {
        if cst != 0 { nscratch.push(cst); }
        if has_dtor { note_dtor_cleanup(s); }
    } else if !static_local && !is_extern {
        if cst != 0 { gi_stmts.push(cst); }
        if has_dtor { gi_stmts.push(atexit_stmt(s, loc)); }
    }
}

// Registers the destructor of a local class object as its cleanup.
fn note_dtor_cleanup(s: i64) {
    let t = syms[s].ty;
    if !is_record(t) || is_opaque(t) { return; }
    let d = class_dtor(rec_of(t));
    if d < 0 { return; }
    let ai = get_attr(s);
    sym_attrs[ai].cleanup = d as! i32;
}

// __cxa_atexit((void (*)(void *))dtor, &obj, &__dso_handle).
var atexit_fn: i64 = -1;
var dso_handle: i64 = -1;
fn atexit_stmt(s: i64, loc: u32) -> u32 {
    let d = class_dtor(rec_of(syms[s].ty));
    if atexit_fn < 0 {
        let vfp = mk_ptr(fn_type1(t_void, t_voidptr));
        fn_scratch.clear();
        fn_scratch.push(vfp);
        fn_scratch.push(t_voidptr);
        fn_scratch.push(t_voidptr);
        let ft = qt(mk_type(TY_FUNC, 0, t_int, 0, 0, 0) as i64, 0);
        atexit_fn = csym(SK_FUNC, intern("__cxa_atexit"), ft, loc);
        cxs[atexit_fn].flags = CF_EXTERN_C;
        dso_handle = csym(SK_VAR, intern("__dso_handle"), t_char, loc);
        syms[dso_handle].flags = SF_FILESCOPE;
        syms[dso_handle].sc = SC_EXTERN as! u8;
        cxs[dso_handle].flags = CF_EXTERN_C;
        let ai = get_attr(dso_handle);
        sym_attrs[ai].vis = 1;
    }
    let mark = nscratch.len;
    let vfp = mk_ptr(fn_type1(t_void, t_voidptr));
    nscratch.push(node(N_ICAST, CK_BITCAST, vfp, icast(n_ref_fn(d, loc), CK_FUNC2PTR, mk_ptr(abi_type(d))) as i64, 0, 0, loc));
    nscratch.push(node(N_ICAST, CK_BITCAST, t_voidptr, n_addr(n_var(s, loc), loc) as i64, 0, 0, loc));
    nscratch.push(node(N_ICAST, CK_BITCAST, t_voidptr, n_addr(n_var(dso_handle, loc), loc) as i64, 0, 0, loc));
    return n_expr_stmt(n_call(atexit_fn, mark, loc));
}

fn fn_type1(ret: u32, p: u32) -> u32 {
    fn_scratch.clear();
    fn_scratch.push(p);
    return qt(mk_type(TY_FUNC, 0, ret, 0, 0, 0) as i64, 0);
}

// `return e;` in a function returning rt (a reference or a class).
recursive fn cg_return(x: u32, rt: u32, loc: u32) -> u32 {
    if is_ref(rt) { return conv_arg(x, rt, loc); }
    if is_record(rt) {
        if !by_value_ok(rt) { return opaque_node(loc); }
        return conv_value(x, unqual(rt), loc);
    }
    if nodes[x].kind as i64 == N_INITBRACE { return conv_value(x, unqual(rt), loc); }
    if is_pointer(rt) && !is_opq(x) {
        let c = cg_ptr_conv(rv(x), unqual(rt), loc);
        if c != 0 { return c; }
    }
    return x;
}

// ---------------------------------------------------------------------------
// new and delete.

fn global_alloc_fn(op: i64) -> i64 {
    var s = scope_find(0, op_ids[op]);
    while s >= 0 {
        let f = resolve(s);
        if f >= 0 && syms[f].kind as i64 == SK_FUNC && types[syms[f].ty >> 4].n == 1 { return f; }
        s = cxs[s].nnext as i64;
    }
    return -1;
}

// new T / new T(args) / new T{args} / new T[n].
recursive fn cg_new(t: u32, count: u32, init: u32, has_init: bool, loc: u32) -> u32 {
    if is_record(t) {
        let sc = type_scope(t);
        if sc >= 0 && (scope_find(sc, op_ids[OP_NEW]) >= 0 || scope_find(sc, op_ids[OP_NEW_ARR]) >= 0) { return opaque_node(loc); }
    }
    let pt = mk_ptr(unqual(t));
    if count != 0 {
        // arrays of types that need no construction or destruction
        let bt = base_elem_t(t);
        if is_record(bt) && (needs_default_init(rec_of(bt)) || class_dtor(rec_of(bt)) >= 0) { return opaque_node(loc); }
        if has_init && !(init == 0 || nodes[init].c == 0) { return opaque_node(loc); }
        let na = global_alloc_fn(OP_NEW_ARR);
        if na < 0 || is_opq(count) || !is_integer(nodes[count].ty) { return opaque_node(loc); }
        let sz = node(N_BINARY, B_MUL, t_size, assign_convert(rv(count), t_size, loc, 1) as i64, int_node(type_size(t), t_size, loc) as i64, 0, loc);
        let mark = nscratch.len;
        nscratch.push(sz);
        let c = lower_call(na, 0, mark, loc, false);
        if is_opq(c) { return c; }
        if has_init {
            // new T[n](): zeroed
            let ms = libc_memset();
            let am = nscratch.len;
            nscratch.push(c);
            nscratch.push(int_node(0, t_int, loc));
            nscratch.push(node(N_BINARY, B_MUL, t_size, assign_convert(rv(count), t_size, loc, 1) as i64, int_node(type_size(t), t_size, loc) as i64, 0, loc));
            let z = n_call(ms, am, loc);
            return node(N_ICAST, CK_BITCAST, pt, z as i64, 0, 0, loc);
        }
        return node(N_ICAST, CK_BITCAST, pt, c as i64, 0, 0, loc);
    }
    let nf = global_alloc_fn(OP_NEW);
    if nf < 0 { return opaque_node(loc); }
    // ({ T *p = (T *)operator new(sizeof(T)); <init *p>; p; })
    let mark0 = nscratch.len;
    nscratch.push(int_node(type_size(t), t_size, loc));
    let c = lower_call(nf, 0, mark0, loc, false);
    if is_opq(c) { return c; }
    let s = csym(SK_VAR, intern("__new_tmp"), pt, loc);
    syms[s].scope = 1;
    let mark = nscratch.len;
    nscratch.push(node(N_DECL, 0, pt, s, node(N_ICAST, CK_BITCAST, pt, c as i64, 0, 0, loc) as i64, loc as i64, loc));
    let obj = n_deref(rv(n_var(s, loc)), loc);
    if is_record(t) {
        let am = nscratch.len;
        if init != 0 {
            let k = nodes[init].kind as i64;
            if k == N_CTOR || k == N_INITBRACE { for i in nodes[init].c as i64 { nscratch.push(nlist[nodes[init].v + i]); } }
            else { nscratch.push(init); }
        }
        var st: u32 = 0;
        if init != 0 && nodes[init].kind as i64 == N_INITBRACE && c_initializable(t) {
            nscratch.resize(am);
            let bi = brace_init(t, init, loc);
            if bi == 0 { nscratch.resize(mark0); return opaque_node(loc); }
            st = n_expr_stmt(node(N_ASSIGN, 0, unqual(t), obj as i64, compound_value(bi, unqual(t), loc) as i64, 0, loc));
        } else {
            st = construct_at(obj, am, loc);
            if st == 0 { nscratch.resize(mark0); return opaque_node(loc); }
            // new T() value-initializes a class without a user-provided constructor
            if has_init && init != 0 && nodes[init].c == 0 && !has_user_ctor(rec_of(t)) {
                nscratch.push(n_expr_stmt(node(N_ASSIGN, 0, unqual(t), obj as i64, node(N_ZEROINIT, 0, unqual(t), 0, 0, 0, loc) as i64, 0, loc)));
            }
        }
        nscratch.push(st);
    } else if has_init {
        var v: u32 = 0;
        if init == 0 || (nodes[init].kind as i64 == N_INITBRACE && nodes[init].c == 0) { v = node(N_ZEROINIT, 0, unqual(t), 0, 0, 0, loc); }
        else if nodes[init].kind as i64 == N_ZEROINIT { v = init; }
        else {
            var e = init;
            if nodes[e].kind as i64 == N_INITBRACE && nodes[e].c == 1 { e = nlist[nodes[e].v]; }
            v = conv_value(e, unqual(t), loc);
        }
        if is_opq(v) { nscratch.resize(mark0); return opaque_node(loc); }
        nscratch.push(n_expr_stmt(node(N_ASSIGN, 0, unqual(t), obj as i64, v as i64, 0, loc)));
    }
    nscratch.push(n_expr_stmt(rv(n_var(s, loc))));
    let body = n_block(mark, loc);
    return node(N_STMTEXPR, 0, pt, body as i64, 0, 0, loc);
}

var memset_fn: i64 = -1;
fn libc_memset() -> i64 {
    if memset_fn < 0 {
        fn_scratch.clear();
        fn_scratch.push(t_voidptr);
        fn_scratch.push(t_int);
        fn_scratch.push(t_size);
        let ft = qt(mk_type(TY_FUNC, 0, t_voidptr, 0, 0, 0) as i64, 0);
        memset_fn = csym(SK_FUNC, intern("memset"), ft, 0);
        cxs[memset_fn].flags = CF_EXTERN_C;
    }
    return memset_fn;
}

// delete p / delete[] p.
recursive fn cg_delete(p0: u32, arr: bool, loc: u32) -> u32 {
    if is_opq(p0) || !is_pointer(nodes[p0].ty) { return opaque_node(loc); }
    let pt = unqual(nodes[p0].ty);
    let t = tbase(pt);
    var dtor: i64 = -1;
    if is_record(t) {
        if is_opaque(t) { return opaque_node(loc); }
        let r = rec_of(t);
        let sc = type_scope(t);
        if sc >= 0 && (scope_find(sc, op_ids[OP_DELETE]) >= 0 || scope_find(sc, op_ids[OP_DELETE_ARR]) >= 0) { return opaque_node(loc); }
        dtor = class_dtor(r);
        if arr && dtor >= 0 { return opaque_node(loc); }
    }
    let df = global_alloc_fn(if arr { OP_DELETE_ARR } else { OP_DELETE });
    if df < 0 { return opaque_node(loc); }
    // ({ T *q = p; if (q) { q->~T(); operator delete(q); } })
    let s = csym(SK_VAR, intern("__delete_tmp"), pt, loc);
    syms[s].scope = 1;
    let mark = nscratch.len;
    nscratch.push(node(N_DECL, 0, pt, s, p0 as i64, loc as i64, loc));
    let im = nscratch.len;
    if dtor >= 0 && cxs[dtor].flags & CF_VIRTUAL != 0 {
        // the deleting destructor, through the vtable
        let cls = scope_class_type(cxs[dtor].dscope as i64);
        let th = obj_addr_as(n_deref(rv(n_var(s, loc)), loc), cls, 0, loc);
        if th == 0 { nscratch.resize(mark); return opaque_node(loc); }
        let fp = vfunc_ptr(dtor, th, 1, loc);
        if fp == 0 { nscratch.resize(mark); return opaque_node(loc); }
        let am = nscratch.len;
        nscratch.push(obj_addr_as(n_deref(rv(n_var(s, loc)), loc), cls, 0, loc));
        nscratch.push(n_expr_stmt(n_call_ptr(fp, am, loc)));
    } else {
        if dtor >= 0 {
            let am = nscratch.len;
            let c = lower_call(dtor, n_deref(rv(n_var(s, loc)), loc), am, loc, false);
            if is_opq(c) { nscratch.resize(mark); return opaque_node(loc); }
            nscratch.push(n_expr_stmt(c));
        }
        let am = nscratch.len;
        nscratch.push(node(N_ICAST, CK_BITCAST, t_voidptr, rv(n_var(s, loc)) as i64, 0, 0, loc));
        let c = n_call(df, am, loc);
        nscratch.push(n_expr_stmt(c));
    }
    let then = n_block(im, loc);
    nscratch.push(node(N_IF, 0, 0, icast(rv(n_var(s, loc)), CK_PTR2BOOL, t_bool) as i64, then as i64, 0, loc));
    let body = n_block(mark, loc);
    return node(N_STMTEXPR, 0, t_void, body as i64, 0, 0, loc);
}

// ---------------------------------------------------------------------------
// Vtables and type information (Itanium C++ ABI 2.5, 2.9.5).

var vtables: u32[>..] = [];              // records whose vtable was asked for
var vtable_syms = dictionary<u64, u32> {};
var vslots: u32[>..] = [];
var vs_range = dictionary<u64, u64> {};  // record -> (first << 32 | count) in vslots; count 0xFFFFFFFF: D1 cannot

// The vtable slots of dynamic class r (function symbols; a virtual
// destructor takes two: the complete one, then the deleting one): first,
// count (-1: multiple or virtual polymorphic bases, which D1 does not do).
recursive fn vtable_slots(r: i64) -> i64, i64 {
    let g = vs_range.get(r as u64);
    if g {
        let c = (g & 0xFFFFFFFF) as i64;
        if c == 0xFFFFFFFF { return 0, -1; }
        return (g >> 32) as i64, c;
    }
    let cr = crecs[r];
    var prim: i64 = -1;
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if !is_record(b.ty) { continue; }
        let br = rec_of(b.ty);
        if crecs[br].flags & CR_DYNAMIC == 0 { continue; }
        if b.flags & BF_VIRTUAL != 0 || prim >= 0 || b.offset != 0 {
            vs_range.insert(r as u64, 0xFFFFFFFF);
            return 0, -1;
        }
        prim = br;
    }
    // the primary base's slots, then the overrides and the new ones
    let mark = slot_scratch.len;
    if prim >= 0 {
        let pf, pc = vtable_slots(prim);
        if pc < 0 { vs_range.insert(r as u64, 0xFFFFFFFF); return 0, -1; }
        for i in pc { slot_scratch.push(vslots[pf + i]); }
    }
    let m = mem_range(r);
    var own_dtor = false;
    for j in m.count {
        let f = cmem[m.first + j] as i64;
        if cxs[f].flags & CF_VIRTUAL == 0 || syms[f].kind as i64 != SK_FUNC { continue; }
        var found = false;
        for i in mark..slot_scratch.len {
            let g2 = slot_scratch[i] as i64;
            if cxs[g2].flags & CF_DTOR_DELETING != 0 { continue; }
            let both_dtor = cxs[f].flags & CF_DTOR != 0 && cxs[g2].flags & CF_DTOR != 0;
            if both_dtor || (cxs[f].flags & CF_DTOR == 0 && overrides(f, g2)) {
                slot_scratch[i] = f as! u32;
                if both_dtor { slot_scratch[i + 1] = deleting_dtor(r) as! u32; own_dtor = true; }
                found = true;
            }
        }
        if !found {
            slot_scratch.push(f as! u32);
            if cxs[f].flags & CF_DTOR != 0 { slot_scratch.push(deleting_dtor(r) as! u32); own_dtor = true; }
        }
    }
    // an inherited virtual destructor is overridden by the implicit one
    if !own_dtor {
        for i in mark..slot_scratch.len {
            let g2 = slot_scratch[i] as i64;
            if cxs[g2].flags & CF_DTOR != 0 && cxs[g2].flags & CF_DTOR_DELETING == 0 {
                let d = class_dtor(r);
                if d >= 0 {
                    slot_scratch[i] = d as! u32;
                    slot_scratch[i + 1] = deleting_dtor(r) as! u32;
                }
                break;
            }
        }
    }
    let first = vslots.len;
    for i in mark..slot_scratch.len { vslots.push(slot_scratch[i]); }
    let count = slot_scratch.len - mark;
    slot_scratch.resize(mark);
    vs_range.insert(r as u64, ((first as u64) << 32) | (count as u64));
    return first, count;
}
var slot_scratch: u32[>..<] = [];

// The slot index of virtual function f in the vtable of class r (from the
// address point), or -1.
fn vtable_slot(r: i64, f: i64) -> i64 {
    let first, count = vtable_slots(r);
    if count < 0 { return -1; }
    for i in count {
        let g = vslots[first + i] as i64;
        if g == f { return i; }
    }
    // an overridden function: the slot of its overrider
    for i in count {
        let g = vslots[first + i] as i64;
        if cxs[g].flags & CF_DTOR_DELETING != 0 { continue; }
        if (cxs[f].flags & CF_DTOR != 0 && cxs[g].flags & CF_DTOR != 0) || (cxs[f].flags & CF_DTOR == 0 && overrides(f, g)) { return i; }
    }
    return -1;
}

// The vtable variable of class r (its initializer is built in cg_finish).
fn vtable_sym(r: i64) -> i64 {
    let g = vtable_syms.get(r as u64);
    if g { return g as i64; }
    let first, count = vtable_slots(r);
    if count < 0 { return -1; }
    let vt = mk_array(t_voidptr, 2 + count);
    let s = csym(SK_VAR, intern("__vtable"), vt, records[r].loc);
    syms[s].sc = SC_STATIC as! u8;
    syms[s].flags = SF_FILESCOPE | SF_DEFINED;
    cxs[s].flags = CF_IMPLICIT;
    if !mangle_special("_ZTV", records[r].ty << 4) { return -1; }
    set_label(s, mg);
    vtable_syms.insert(r as u64, s as! u32);
    vtables.push(r as! u32);
    return s;
}

var typeinfos = dictionary<u64, u32> {};
var ext_syms = dictionary<u64, u32> {};

// An external variable (array of void *) named `name` (the type_info
// classes' vtables).
fn ext_array(name: const u8[:]) -> i64 {
    let id = intern(name);
    let g = ext_syms.get(id as u64);
    if g { return g as i64; }
    let s = csym(SK_VAR, id, mk_array(t_voidptr, -1), 0);
    syms[s].sc = SC_EXTERN as! u8;
    syms[s].flags = SF_FILESCOPE;
    cxs[s].flags = CF_EXTERN_C;
    ext_syms.insert(id as u64, s as! u32);
    return s;
}

fn void_addr_of(s: i64, idx: i64, loc: u32) -> u32 {
    let base = icast(n_var(s, loc), CK_ARRAY2PTR, mk_ptr(tbase(syms[s].ty)));
    var p = base;
    if idx != 0 { p = node(N_BINARY, B_PTRADD, mk_ptr(tbase(syms[s].ty)), base as i64, int_node(idx, t_long, loc) as i64, 0, loc); }
    return node(N_ICAST, CK_BITCAST, t_voidptr, p as i64, 0, 0, loc);
}

fn int_as_ptr(v: i64, loc: u32) -> u32 { node(N_ICAST, CK_INT2PTR, t_voidptr, int_node(v, t_long, loc) as i64, 0, 0, loc) }

// The type_info object of class r (_ZTI), with its name (_ZTS).
recursive fn typeinfo_sym(r: i64) -> i64 {
    let g = typeinfos.get(r as u64);
    if g { return g as i64; }
    let cls = records[r].ty << 4;
    let loc = records[r].loc;
    // the name: the mangled type
    if !mangle_special("", cls) { return -1; }
    let name_len = mg.len;
    let soff = strbytes.len;
    strbytes.append(mg);
    strbytes.push(0);
    let si = strs.len;
    strs.push(StrLit { start: soff as! u32, len: (name_len + 1) as! u32, elem: t_char });
    let nt = mk_array(t_char | (Q_CONST as! u32), name_len + 1);
    let ns = csym(SK_VAR, intern("__typeinfo_name"), nt, loc);
    syms[ns].sc = SC_STATIC as! u8;
    syms[ns].flags = SF_FILESCOPE | SF_DEFINED;
    cxs[ns].flags = CF_IMPLICIT;
    mangle_special("_ZTS", cls);
    set_label(ns, mg);
    let sn = node(N_STRING, 0, nt, si, 0, 0, loc);
    nodes[sn].flags = NF_LVALUE | NF_STRINIT;
    cg_extra.push(node(N_DECL, 0, nt, ns, sn as i64, loc as i64, loc));
    // the bases: none, one public non-virtual at offset 0, or several
    let cr = crecs[r];
    let mark = nscratch.len;
    var kind = 0;
    if cr.nbases == 1 && cbases[cr.bases].flags & BF_VIRTUAL == 0 && cbases[cr.bases].offset == 0 && cbases[cr.bases].access as i64 == 0 { kind = 1; }
    else if cr.nbases > 0 { kind = 2; }
    let vt = ext_array(if kind == 0 { "_ZTVN10__cxxabiv117__class_type_infoE" } else if kind == 1 { "_ZTVN10__cxxabiv120__si_class_type_infoE" }
                       else { "_ZTVN10__cxxabiv121__vmi_class_type_infoE" });
    nscratch.push(void_addr_of(vt, 2, loc));
    nscratch.push(void_addr_of(ns, 0, loc));
    if kind == 1 {
        let bt = typeinfo_sym(rec_of(cbases[cr.bases].ty));
        if bt < 0 { nscratch.resize(mark); return -1; }
        nscratch.push(void_addr_of(bt, 0, loc));
    } else if kind == 2 {
        // flags (u32), base count (u32), then per base: type_info *, offset << 8 | public 2 | virtual 1
        nscratch.push(int_as_ptr((cr.nbases as i64) << 32, loc));
        for i in cr.nbases {
            let b = cbases[cr.bases + i];
            if !is_record(b.ty) || b.flags & BF_VIRTUAL != 0 { nscratch.resize(mark); return -1; }
            let bt = typeinfo_sym(rec_of(b.ty));
            if bt < 0 { nscratch.resize(mark); return -1; }
            nscratch.push(void_addr_of(bt, 0, loc));
            nscratch.push(int_as_ptr((b.offset << 8) | (if b.access as i64 == 0 { 2 } else { 0 }), loc));
        }
    }
    let n = nscratch.len - mark;
    let tt = mk_array(t_voidptr, n);
    let s = csym(SK_VAR, intern("__typeinfo"), tt, loc);
    syms[s].sc = SC_STATIC as! u8;
    syms[s].flags = SF_FILESCOPE | SF_DEFINED;
    cxs[s].flags = CF_IMPLICIT;
    mangle_special("_ZTI", cls);
    set_label(s, mg);
    let start = commit_list(mark);
    let il = node_v(N_INITLIST, 0, tt, 0, 0, n, loc, start);
    cg_extra.push(node(N_DECL, 0, tt, s, il as i64, loc as i64, loc));
    typeinfos.insert(r as u64, s as! u32);
    return s;
}

// The initializer of the vtable of class r.
fn build_vtable(r: i64) {
    let s = vtable_sym(r);
    let loc = records[r].loc;
    let first, count = vtable_slots(r);
    let mark = nscratch.len;
    nscratch.push(node(N_ZEROINIT, 0, t_voidptr, 0, 0, 0, loc));      // offset to top
    let ti = typeinfo_sym(r);
    if ti < 0 { nscratch.push(int_as_ptr(0, loc)); } else { nscratch.push(void_addr_of(ti, 0, loc)); }
    for i in count {
        var f = vslots[first + i] as i64;
        if cxs[f].flags & CF_PURE != 0 {
            if pure_virtual < 0 {
                pure_virtual = csym(SK_FUNC, intern("__cxa_pure_virtual"), fn_type0(t_void), loc);
                cxs[pure_virtual].flags = CF_EXTERN_C;
            }
            f = pure_virtual;
        }
        let fr = icast(n_ref_fn(f, loc), CK_FUNC2PTR, mk_ptr(abi_type(f)));
        nscratch.push(node(N_ICAST, CK_BITCAST, t_voidptr, fr as i64, 0, 0, loc));
    }
    let n = nscratch.len - mark;
    let start = commit_list(mark);
    let il = node_v(N_INITLIST, 0, syms[s].ty, 0, 0, n, loc, start);
    cg_extra.push(node(N_DECL, 0, syms[s].ty, s, il as i64, loc as i64, loc));
}
var pure_virtual: i64 = -1;

fn fn_type0(ret: u32) -> u32 {
    fn_scratch.clear();
    return qt(mk_type(TY_FUNC, 0, ret, 0, 0, 0) as i64, 0);
}

// ---------------------------------------------------------------------------
// The end of the translation unit: implicit functions, vtables, the
// global initialization function, names and types for C's lowering, and
// the check that everything emitted is lowered.

var cg_extra: u32[>..] = [];        // more top-level items (N_FUNCDEF, N_DECL)

fn set_label(s: i64, name: const u8[:]) {
    let ai = get_attr(s);
    let off = strbytes.len;
    strbytes.append(name);
    sym_attrs[ai].asm_label = off as! u32;
    sym_attrs[ai].asm_len = name.len as! u32;
}

// The body of an implicit member function (pending_bodies kind).
recursive fn synth_body(f: i64, kind: i64) {
    let sc = cxs[f].dscope as i64;
    let cls = scope_class_type(sc);
    let r = rec_of(cls);
    let loc = records[r].loc;
    let th = make_this(f, mk_ptr(cls), loc);
    let sv = cg_this;
    cg_this = th;
    let mark = nscratch.len;
    let sm = stmt_buf.len;
    var ok = true;
    if kind == 1 {
        ok = ctor_prologue(r, th, 0, loc);
    } else if kind == 2 {
        if crecs[r].flags & CR_DYNAMIC != 0 {
            let vs = vptr_store(r, th, loc);
            if vs == 0 { ok = false; } else { stmt_buf.push(vs); }
        }
        if !dtor_epilogue(r, th, loc) { ok = false; }
    } else {
        // the deleting destructor
        let d = class_dtor(r);
        let am = nscratch.len;
        let c = lower_call(d, n_deref(rv(n_var(th, loc)), loc), am, loc, false);
        stmt_buf.push(n_expr_stmt(c));
        let df = global_alloc_fn(OP_DELETE);
        if df < 0 { ok = false; }
        else {
            let am2 = nscratch.len;
            nscratch.push(node(N_ICAST, CK_BITCAST, t_voidptr, rv(n_var(th, loc)) as i64, 0, 0, loc));
            stmt_buf.push(n_expr_stmt(n_call(df, am2, loc)));
        }
    }
    for i in sm..stmt_buf.len { nscratch.push(stmt_buf[i]); }
    stmt_buf.resize(sm);
    if !ok { nscratch.push(mark_bad_stmt(loc)); }
    let body = n_block(mark, loc);
    let n = node_v(N_FUNCDEF, 0, syms[f].ty, f, body as i64, 0, loc, 0);
    syms[f].def = n as! i32;
    cg_extra.push(n);
    cg_this = sv;
}

// Called after parsing in code generation mode; false on errors.
recursive fn cg_finish(main_file: const u8[:]) -> bool {
    // implicit members and vtables (each may ask for more)
    var vi = 0;
    var pi = 0;
    loop {
        var progress = false;
        while vi < vtables.len { build_vtable(vtables[vi] as i64); vi++; progress = true; }
        while pi < pending_bodies.len {
            synth_body(pending_bodies[pi] as i64, pending_bodies[pi + 1] as i64);
            pi += 2;
            progress = true;
        }
        if !progress { break; }
    }
    // the dynamic initialization of globals
    if gi_stmts.len > 0 {
        var b = 0;
        for c, i in main_file { if c == '/' { b = i + 1; } }
        var nm: u8[>..] = [];
        nm.append("_GLOBAL__sub_I_");
        nm.append(main_file[b..]);
        let f = csym(SK_FUNC, intern("__global_init"), fn_type0(t_void), 0);
        syms[f].sc = SC_STATIC as! u8;
        syms[f].flags = SF_DEFINED;
        cxs[f].flags = CF_IMPLICIT;
        set_label(f, nm);
        let ai = get_attr(f);
        sym_attrs[ai].flags = sym_attrs[ai].flags | AM_CTOR;
        let mark = nscratch.len;
        for st in gi_stmts { nscratch.push(st); }
        let body = n_block(mark, 0);
        let n = node_v(N_FUNCDEF, 0, syms[f].ty, f, body as i64, 0, 0, 0);
        syms[f].def = n as! i32;
        cg_extra.push(n);
    }
    // the translation unit with the extra items
    let tu = nodes[tu_node];
    let mark = nscratch.len;
    for i in tu.c as i64 { nscratch.push(nlist[tu.v + i]); }
    for x in cg_extra { nscratch.push(x); }
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    tu_node = node_v(N_TU, 0, 0, 0, 0, count, 0, start);
    // names and linkage
    name_syms();
    // what is emitted: checked and rewritten for C's lowering
    if !check_reachable() { return false; }
    // types: references become pointers, member functions take `this`
    lower_sym_types();
    return n_errors == 0;
}

// Mangled names as asm labels; inline functions internal.
fn name_syms() {
    cx_grow();
    for s in 1..syms.len {
        let k = syms[s].kind as i64;
        if k != SK_FUNC && k != SK_VAR { continue; }
        let fl = cxs[s].flags;
        if fl & (CF_PATTERN | CF_TEMPLATE | CF_TPARAM) != 0 { continue; }
        if syms[s].attr != 0 && sym_attrs[syms[s].attr].asm_len != 0 { continue; }
        if k == SK_VAR {
            if syms[s].flags & SF_COMPLIT != 0 || syms[s].name == 0 { continue; }
            if fl & CF_MEMBER != 0 { syms[s].sc = 0; syms[s].flags = syms[s].flags | SF_FILESCOPE; }
            if syms[s].flags & SF_FILESCOPE == 0 { continue; }
            // a static local: C's lowering names it
            if syms[s].scope > 0 && fl & CF_MEMBER == 0 { continue; }
        }
        let internal = internal_linkage(s) || (cxs[s].dscope > 0 && in_anon_ns(cxs[s].dscope as i64));
        if mangle_sym(s) {
            if syms[s].name == 0 || !same_text(mg, ident_text(syms[s].name as i64)) { set_label(s, mg); }
        } else {
            // a name D1 cannot mangle (local classes ...): an internal one
            var nm: u8[>..] = [];
            format(nm, "_ZL__goosecc_", s);
            set_label(s, nm);
            syms[s].sc = SC_STATIC as! u8;
        }
        if k == SK_FUNC {
            let inline = fl & (CF_DEFINED_IN_CLASS | CF_IMPLICIT | CF_CONSTEXPR) != 0 || syms[s].flags & SF_INLINE != 0;
            if fl & CF_MEMBER != 0 { syms[s].sc = if inline { SC_STATIC as! u8 } else { 0 }; }
            else if inline && fl & CF_EXTERN_C == 0 { syms[s].sc = SC_STATIC as! u8; }
        }
        if internal && syms[s].sc as i64 != SC_EXTERN { syms[s].sc = SC_STATIC as! u8; }
    }
}

fn same_text(a: const u8[:], b: const u8[:]) -> bool { a == b }

// The types of symbols for C's lowering.
fn lower_sym_types() {
    for s in 1..syms.len {
        let k = syms[s].kind as i64;
        if k == SK_FUNC {
            if s < cxs.len && cxs[s].flags & (CF_PATTERN | CF_TEMPLATE) != 0 { continue; }
            syms[s].ty = abi_type(s);
        } else if k == SK_VAR {
            syms[s].ty = lower_ty(syms[s].ty);
        }
    }
    for i in fields.len { fields[i].ty = lower_ty(fields[i].ty); }
}

// ---------------------------------------------------------------------------
// The reachable code: every function and variable the C lowering will
// emit, walked from the external definitions; references rewritten,
// unsupported constructs reported.

var cg_seen: u8[>..] = [];
var wk: u32[>..<] = [];
var var_decls = dictionary<u64, u32> {};   // file-scope variable -> its N_DECL
var n_bad: i64 = 0;

fn reach_fn(f: i64) {
    if syms[f].def < 0 { return; }
    let d = syms[f].def as u32;
    if nodes[d].kind as i64 != N_FUNCDEF { return; }
    wk.push(d);
}

fn reach_var(s: i64) {
    let g = var_decls.get(s as u64);
    if g { wk.push(g); }
}

fn check_reachable() -> bool {
    let tu = nodes[tu_node];
    for i in tu.c as i64 {
        let it = nlist[tu.v + i];
        let nd = nodes[it];
        if nd.kind as i64 == N_DECL && syms[nd.a].kind as i64 == SK_VAR { var_decls.insert(nd.a as u64, it); }
    }
    for i in tu.c as i64 {
        let it = nlist[tu.v + i];
        let nd = nodes[it];
        let s = nd.a as i64;
        if nd.kind as i64 == N_FUNCDEF {
            if syms[s].def as u32 != it { continue; }
            if syms[s].sc as i64 != SC_STATIC || cg_has_attr(s, AM_CTOR) || cg_has_attr(s, AM_USED) { wk.push(it); }
        } else if nd.kind as i64 == N_DECL && syms[s].kind as i64 == SK_VAR {
            if syms[s].sc as i64 != SC_STATIC && syms[s].flags & SF_FILESCOPE != 0 { wk.push(it); }
        }
    }
    while wk.len > 0 {
        let n = wk.pop();
        while cg_seen.len < nodes.len { cg_seen.push(0); }
        if cg_seen[n] != 0 { continue; }
        cg_seen[n] = 1;
        visit(n);
        if n_bad >= 20 { break; }
    }
    return n_bad == 0;
}

fn bad(n: u32) {
    n_bad++;
    if n_bad > 10 { return; }
    let k = nodes[n].kind as i64;
    var what = "this C++ construct";
    if k == N_THROW || k == N_TRY || k == N_CATCH { what = "exceptions"; }
    else if k == N_RANGEFOR { what = "range-based for"; }
    else if k == N_FUNCREF { what = "this use of a function name (templates, member pointers)"; }
    else if k == N_DYNCAST { what = "dynamic_cast"; }
    else if k == N_TYPEID { what = "typeid"; }
    else if k == N_INITBRACE { what = "this braced initializer"; }
    else if k == N_NEW || k == N_DELETE { what = "this new/delete"; }
    else if k == N_CTOR { what = "this temporary object"; }
    err_at(nodes[n].loc, str("goosecc: C++ code generation (D1) does not support ", what, " yet"));
    var dv: u8[>..] = [];
    if env("GOOSECC_DEBUG_CG", dv) {
        write_stderr(str("  (node kind ", k, " op ", nodes[n].op, " flags ", nodes[n].flags, " type ", tname(nodes[n].ty), ")\n"));
    }
}

fn kid(x: u32) { if x != 0 { wk.push(x); } }
fn kids_list(v: i64, c: u32) { for i in c as i64 { kid(nlist[v + i]); } }

// Is t (lowered) one of C's types?
recursive fn c_type_ok(t: u32) -> bool {
    let k = kind_of(t);
    if k >= TY_LREF { return false; }
    if k == TY_POINTER || k == TY_ARRAY || k == TY_COMPLEX || k == TY_VECTOR || k == TY_EXTVECTOR { return c_type_ok(tbase(t)); }
    if k == TY_FUNC {
        let f = types[t >> 4];
        if !c_type_ok(f.base) { return false; }
        for i in f.n { if !c_type_ok(tparams[f.extra + i]) { return false; } }
    }
    return true;
}

fn visit(n: u32) {
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k >= N_THIS && k <= N_RANGEFOR { bad(n); return; }
    if k == N_FUNCDEF {
        let f = nd.a as i64;
        let ft = types[syms[f].ty >> 4];
        if !by_value_ok(ft.base) { bad(n); return; }
        for i in ft.n { if !by_value_ok(tparams[ft.extra + i]) { bad(n); return; } }
        // `this` first
        if is_this_fn(f) {
            let thg = fn_this.get(f as u64);
            var th: u32 = 0;
            if thg { th = thg; } else { bad(n); return; }
            let mark = nscratch.len;
            nscratch.push(th);
            for i in nd.c { nscratch.push(nlist[nd.v + i]); }
            let count = nscratch.len - mark;
            let start = commit_list(mark);
            nodes[n].v = start;
            nodes[n].c = count as! u32;
        }
        nodes[n].ty = abi_type(f);
        for i in nodes[n].c as i64 {
            let p = nlist[nodes[n].v + i] as i64;
            if !c_type_ok(lower_ty(syms[p].ty)) { bad(n); return; }
        }
        kid(nd.b);
        return;
    }
    if nd.flags & NF_DEP != 0 { bad(n); return; }
    if nd.ty != 0 {
        if kind_of(nd.ty) == TY_NULLPTR && k == N_INT { nodes[n].ty = t_int; }
        else {
            let lt = lower_ty(nd.ty);
            if !c_type_ok(lt) { bad(n); return; }
            nodes[n].ty = lt;
        }
    }
    if k == N_DECLREF {
        let s = nd.a as i64;
        let sk = syms[s].kind as i64;
        if sk == SK_FUNC {
            if s < cxs.len && cxs[s].flags & (CF_PATTERN | CF_DELETED) != 0 { bad(n); return; }
            reach_fn(s);
        } else if sk == SK_VAR {
            if syms[s].flags & SF_FILESCOPE != 0 { reach_var(s); }
            if !c_type_ok(lower_ty(syms[s].ty)) { bad(n); return; }
            if nd.flags & NF_REFDEREF != 0 {
                let c = node(N_DECLREF, 0, lower_ty(syms[s].ty), s, 0, 0, nd.loc);
                nodes[c].flags = NF_LVALUE;
                deref_into(n, c);
            }
        } else if sk != SK_BUILTIN { bad(n); return; }
    } else if k == N_MEMBER {
        if nd.flags & NF_REFDEREF != 0 {
            let c = node(N_MEMBER, nd.op as i64, lower_ty(fields[nd.b].ty), nd.a as i64, nd.b as i64, 0, nd.loc);
            nodes[c].flags = NF_LVALUE;
            deref_into(n, c);
        }
    } else if k == N_ICAST && nd.op as i64 == CK_DERIVED2BASE {
        let off = nd.v;
        let e = nd.a;
        let bt = nodes[n].ty;
        if off == 0 {
            nodes[n].op = CK_NOOP as! u8;
            if !is_lvalue(e) {
                // an rvalue's base part: through a temporary
                let m = materialize(e, nd.loc);
                nodes[n].a = m;
            }
        } else {
            var o = e;
            if !is_lvalue(o) { o = materialize(o, nd.loc); }
            let a = n_addr(o, nd.loc);
            let cp = node(N_ICAST, CK_BITCAST, mk_ptr(t_char), a as i64, 0, 0, nd.loc);
            let add = node(N_BINARY, B_PTRADD, mk_ptr(t_char), cp as i64, int_node(off, t_long, nd.loc) as i64, 0, nd.loc);
            let bp = node(N_ICAST, CK_BITCAST, mk_ptr(bt), add as i64, 0, 0, nd.loc);
            nodes[n].kind = N_UNARY as! u8;
            nodes[n].op = U_DEREF as! u8;
            nodes[n].a = bp;
            nodes[n].v = 0;
            nodes[n].flags = NF_LVALUE;
        }
    } else if (k == N_ICAST || k == N_CAST) && nd.op as i64 >= CK_DERIVED2BASE {
        bad(n);
        return;
    } else if k == N_DECL {
        let s = nd.a as i64;
        if syms[s].attr != 0 && sym_attrs[syms[s].attr].cleanup >= 0 { reach_fn(sym_attrs[syms[s].attr].cleanup as i64); }
        if syms[s].kind as i64 == SK_VAR && !c_type_ok(lower_ty(syms[s].ty)) { bad(n); return; }
    } else if k == N_COMPLIT {
        let s = nd.b as i64;
        if s > 0 && !c_type_ok(lower_ty(syms[s].ty)) { bad(n); return; }
    } else if k == N_COND && nd.flags & NF_LVALUE != 0 && nd.b != 0 && is_lvalue(nd.b) && is_lvalue(nd.c) {
        // a C++ lvalue conditional: *(c ? &a : &b)
        let pt = mk_ptr(nodes[n].ty);
        let c2 = node(N_COND, 0, pt, nd.a as i64, n_addr(nd.b, nd.loc) as i64, n_addr(nd.c, nd.loc) as i64, nd.loc);
        to_deref(n, c2);
    } else if k == N_BINARY && nd.op as i64 == B_COMMA && nd.flags & NF_LVALUE != 0 && is_lvalue(nd.b) {
        // a C++ lvalue comma: *(a, &b)
        let pt = mk_ptr(nodes[n].ty);
        let c2 = node(N_BINARY, B_COMMA, pt, nd.a as i64, n_addr(nd.b, nd.loc) as i64, 0, nd.loc);
        to_deref(n, c2);
    }
    push_kids(n);
}

// Node n (an lvalue reference to an object through a pointer c) becomes *c.
fn deref_into(n: u32, c: u32) {
    let ld = node(N_ICAST, CK_LVAL2RVAL, nodes[c].ty, c as i64, 0, 0, nodes[n].loc);
    nodes[n].kind = N_UNARY as! u8;
    nodes[n].op = U_DEREF as! u8;
    nodes[n].a = ld;
    nodes[n].b = 0;
    nodes[n].c = 0;
    nodes[n].flags = nodes[n].flags & ~(NF_REFDEREF as! u16) | NF_LVALUE;
}

// Node n becomes *p (an lvalue).
fn to_deref(n: u32, p: u32) {
    nodes[n].kind = N_UNARY as! u8;
    nodes[n].op = U_DEREF as! u8;
    nodes[n].a = p;
    nodes[n].b = 0;
    nodes[n].c = 0;
    nodes[n].flags = NF_LVALUE;
}

fn push_kids(n: u32) {
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_UNARY || k == N_CAST || k == N_ICAST || k == N_MEMBER || k == N_STMTEXPR || k == N_VAARG || k == N_SWIZZLE ||
       k == N_CASE || k == N_DEFAULT || k == N_RETURN || k == N_EXPR || k == N_IGOTO || k == N_COMPLIT {
        kid(nd.a);
        return;
    }
    if k == N_BINARY || k == N_ASSIGN || k == N_INDEX || k == N_WHILE || k == N_DO || k == N_SWITCH { kid(nd.a); kid(nd.b); return; }
    if k == N_COND || k == N_IF { kid(nd.a); kid(nd.b); kid(nd.c); return; }
    if k == N_FOR { kid(nd.a); kid(nd.b); kid(nd.c); kid(nd.v as! u32); return; }
    if k == N_CALL { kid(nd.a); kids_list(nd.v, nd.c); return; }
    if k == N_INITLIST { kids_list(nd.v, nd.c); kid(nd.b); return; }
    if k == N_BUILTIN || k == N_COMPOUND || k == N_ASM { kids_list(nd.v, nd.c); return; }
    if k == N_DECL || k == N_LABEL || k == N_ASMOP { kid(nd.b); return; }
}

// Does statement n contain a return (not in a nested statement expression's
// function: there is none)?
recursive fn has_return(n: u32) -> bool {
    if n == 0 { return false; }
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_RETURN { return true; }
    if k == N_COMPOUND { for i in nd.c as i64 { if has_return(nlist[nd.v + i]) { return true; } } return false; }
    if k == N_IF { return has_return(nd.b) || has_return(nd.c); }
    if k == N_WHILE || k == N_SWITCH || k == N_LABEL { return has_return(nd.b); }
    if k == N_DO || k == N_CASE || k == N_DEFAULT { return has_return(nd.a); }
    if k == N_FOR { return has_return(nd.v as! u32); }
    if k == N_TRY { return true; }
    return false;
}

fn cg_has_attr(s: i64, m: u32) -> bool {
    let a = syms[s].attr;
    return a != 0 && sym_attrs[a].flags & m != 0;
}
