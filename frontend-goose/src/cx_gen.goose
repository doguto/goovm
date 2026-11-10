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
import .cx_gen_defs;
import .cx_gen_link;
import .cx_gen_eh;
import .cx_gen_class;
import .cx_gen_vt;
import .cx_gen_rtti;
import .cx_gen_new;
import .cx_gen_stmt;
import .cx_gen_lambda;
import .cx_gen_tls;

let CF_DTOR_DELETING = 2147483648;  // the deleting destructor (D0) of a class with a virtual destructor

var cg_on: bool = false;        // C++ code generation: semantic actions build lowered C nodes
var cg_base_variant = false;    // calls of constructors and destructors are of the base-object variant (C2/D2)
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
    if k == TY_MEMPTR {
        // Itanium: a data member pointer is the offset (null: -1), a member
        // function pointer the pair { ptr, adj }
        if is_func(tbase(t)) { return with_q(mfp_type(), quals(t)); }
        return with_q(t_long, quals(t));
    }
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

// The C type of function f: `this` first for a non-static member; a class
// passed by invisible reference is a pointer, a class returned by
// invisible reference a pointer parameter (before `this`) that the
// function returns (Itanium's sret).
fn abi_type(f: i64) -> u32 {
    let g = abi_types.get(f as u64);
    if g { return g; }
    let ft = syms[f].ty;
    let lt = lower_ty(ft);
    var r = lt;
    let fx = types[ft >> 4];
    var indirect = pass_indirect(fx.base) || needs_vtt(f);
    for i in fx.n { if pass_indirect(tparams[fx.extra + i]) { indirect = true; } }
    if indirect {
        let lf = types[lt >> 4];
        let mark = abi_scratch.len;
        var ret = lf.base;
        if pass_indirect(fx.base) {
            ret = mk_ptr(unqual(fx.base));
            abi_scratch.push(ret);
        }
        if is_this_fn(f) {
            let cls = scope_class_type(cxs[f].dscope as i64);
            var q: i64 = 0;
            if (types[ft >> 4].flags as i64) & TF_MCONST != 0 { q = Q_CONST; }
            abi_scratch.push(mk_ptr(with_q(cls, q)));
            if needs_vtt(f) { abi_scratch.push(mk_ptr(t_voidptr)); }
        }
        for i in lf.n {
            let p = tparams[lf.extra + i];
            abi_scratch.push(if pass_indirect(p) { mk_ptr(unqual(p)) } else { p });
        }
        fn_scratch.clear();
        for i in mark..abi_scratch.len { fn_scratch.push(abi_scratch[i]); }
        abi_scratch.resize(mark);
        r = qt(mk_type(TY_FUNC, (lf.flags as i64) & (TF_VARIADIC | TF_NORETURN), ret, 0, 0, 0) as i64, 0);
        abi_types.insert(f as u64, r);
        return r;
    }
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

// Is f the base-object variant of a constructor or destructor of a class
// with virtual bases (it takes the VTT after `this`)?
fn needs_vtt(f: i64) -> bool {
    if cxs[f].flags & (CF_CTOR | CF_DTOR) == 0 || cxs[f].flags & CF_DTOR_DELETING != 0 { return false; }
    if complete_base.count > 0 && complete_base.contains(f as u64) { return false; }
    let r = rec_of(scope_class_type(cxs[f].dscope as i64));
    return r < crecs.len && has_vb(r);
}
var cg_vtt_arg: u32 = 0;        // the VTT argument of the next call of a base-object structor (lower_call)
var fn_vtt = dictionary<u64, u32> {};

// The VTT parameter of structor s.
fn make_vtt(s: i64, loc: u32) -> i64 {
    let g = fn_vtt.get(s as u64);
    if g { return g as i64; }
    let p = csym(SK_VAR, intern("__vtt_parm"), mk_ptr(t_voidptr), loc);
    syms[p].flags = SF_PARAM;
    syms[p].scope = 1;
    fn_vtt.insert(s as u64, p as! u32);
    return p;
}

// The VTT argument for the base subobject (cls at off) of r: a sub-VTT of
// the VTT parameter, or of r's VTT in a complete-object structor.
fn vtt_arg(r: i64, cls: i64, off: i64, loc: u32) -> u32 {
    let k = vtt_sub_index(r, cls, off);
    let ppv = mk_ptr(t_voidptr);
    if cg_cur_vtt >= 0 {
        let v = rv(n_var(cg_cur_vtt, loc));
        if k == 0 { return v; }
        return node(N_BINARY, B_PTRADD, ppv, v as i64, int_node(k, t_long, loc) as i64, 0, loc);
    }
    let vs = vtt_sym(r);
    return void_addr_of_pp(vs, k, loc);
}

fn void_addr_of_pp(s: i64, idx: i64, loc: u32) -> u32 {
    let base = icast(n_var(s, loc), CK_ARRAY2PTR, mk_ptr(tbase(syms[s].ty)));
    var p = base;
    if idx != 0 { p = node(N_BINARY, B_PTRADD, mk_ptr(tbase(syms[s].ty)), base as i64, int_node(idx, t_long, loc) as i64, 0, loc); }
    return node(N_ICAST, CK_BITCAST, mk_ptr(t_voidptr), p as i64, 0, 0, loc);
}

fn is_this_fn(f: i64) -> bool { syms[f].kind as i64 == SK_FUNC && cxs[f].flags & CF_MEMBER != 0 && cxs[f].flags & CF_STATIC == 0 }

// ---------------------------------------------------------------------------
// Node helpers (C nodes).

fn n_ref_fn(f: i64, loc: u32) -> u32 {
    inst_use(f);
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

// A prvalue of class type as an object: a compound literal for a
// trivially copyable class, else a temporary destroyed at the end of the
// full-expression (or of the block, when cg_extend is set: bound to a
// reference variable).
recursive fn materialize(e: u32, loc: u32) -> u32 {
    let t = unqual(nodes[e].ty);
    if is_record(t) && !is_opaque(t) && !class_trivial_copy(rec_of(t)) { return xtemp_of(e, t, loc); }
    let s = csym(SK_VAR, 0, t, loc);
    syms[s].flags = SF_COMPLIT;
    let cl = node(N_COMPLIT, 0, t, e as i64, s, 0, loc);
    nodes[cl].flags = NF_LVALUE;
    return cl;
}
var cg_extend = false;

// A temporary of class t initialized from e (a class prvalue, or what
// constructs one): N_XTEMP, an lvalue.
recursive fn xtemp_of(e: u32, t: u32, loc: u32) -> u32 {
    let s = csym(SK_VAR, intern("__tmp"), unqual(t), loc);
    syms[s].flags = SF_COMPLIT;
    syms[s].scope = 1;
    let init = init_into(n_var(s, loc), e, loc);
    if init == 0 { return opaque_node(loc); }
    var d: i64 = -1;
    if is_record(t) { let x = class_dtor(rec_of(t)); if x >= 0 { d = complete_sym(x); } }
    let n = node(N_XTEMP, if cg_extend { XT_EXTENDED } else { 0 }, unqual(t), init as i64, s, if d >= 0 { d } else { 0 }, loc);
    nodes[n].flags = NF_LVALUE;
    if d >= 0 { n_xtemps++; }
    return n;
}

// Is e a class prvalue built in place (by a constructor or a call
// returning by invisible reference, or a conditional / comma of them)?
fn is_class_prv(e: u32) -> bool {
    let k = nodes[e].kind as i64;
    if is_lvalue(e) { return false; }
    if k == N_CTOR || k == N_XPRV { return true; }
    if !is_record(nodes[e].ty) { return false; }
    if k == N_COND || (k == N_BINARY && nodes[e].op as i64 == B_COMMA) || k == N_STMTEXPR { return true; }
    return false;
}

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
        // a temporary (const lvalue or rvalue references)
        if kind_of(pt) == TY_LREF && quals(t) & Q_CONST == 0 { return opaque_node(loc); }
        if is_record(t) && !is_opaque(t) {
            let ct = unqual(t);
            var src = e;
            if !(is_class_prv(e) && unqual(nodes[e].ty) == ct) { src = class_rv(e, ct, loc); }
            if is_opq(src) { return src; }
            if is_record(nodes[src].ty) && unqual(nodes[src].ty) != ct && is_lvalue(src) {
                let b = derived_to_base_lv(src, ct, loc);
                if b != 0 { return n_ptrcast(n_addr(b, loc), lower_ty(mk_ptr(t)), loc); }
            }
            let m = materialize(src, loc);
            if is_opq(m) { return m; }
            return n_ptrcast(n_addr(m, loc), lower_ty(mk_ptr(t)), loc);
        }
        let v = conv_value(e, unqual(t), loc);
        if is_opq(v) { return v; }
        return n_ptrcast(temp_addr(v, unqual(t), loc), lower_ty(mk_ptr(t)), loc);
    }
    if pass_indirect(pt) {
        // by invisible reference: a temporary the caller destroys at the end
        // of the full-expression
        let ct = unqual(pt);
        var src = e;
        if !(is_class_prv(e) && unqual(nodes[e].ty) == ct) { src = class_rv(e, ct, loc); }
        if is_opq(src) { return src; }
        let x = xtemp_of(src, ct, loc);
        if is_opq(x) { return x; }
        return n_addr(x, loc);
    }
    return conv_value(e, unqual(pt), loc);
}

// e as a class prvalue of class t: itself (a construction or a call of t),
// or a constructor call: a copy or move of an object of t (or of a class
// derived from it: sliced), or a converting constructor.
recursive fn class_rv(e: u32, t: u32, loc: u32) -> u32 {
    let k = nodes[e].kind as i64;
    if is_class_prv(e) && unqual(nodes[e].ty) == unqual(t) { return e; }
    if k == N_INITBRACE {
        if c_initializable(t) {
            let bi = brace_init(t, e, loc);
            if bi == 0 { return opaque_node(loc); }
            return compound_value(bi, t, loc);
        }
        let c = node_v(N_CTOR, 0, unqual(t), 0, 0, nodes[e].c as i64, loc, nodes[e].v);
        // list-initialization: an aggregate's (op 2), or a constructor's (op 1)
        nodes[c].op = if is_record(t) && is_aggregate_class(rec_of(t)) { 2 } else { 1 };
        return c;
    }
    let mark = nscratch.len;
    nscratch.push(e);
    let c = node(N_CTOR, 0, unqual(t), 0, 0, 1, loc);
    let st = commit_list(mark);
    nodes[c].v = st;
    return c;
}

// A value of type t from e (a copy for a class: trivially copyable classes
// are C values; others give a class prvalue, which init_into constructs
// in place and anything else materializes).
recursive fn conv_value(e: u32, t: u32, loc: u32) -> u32 {
    if is_opq(e) && nodes[e].kind as i64 != N_FUNCREF && nodes[e].kind as i64 != N_INITBRACE { return opaque_node(loc); }
    if nodes[e].kind as i64 == N_FUNCREF {
        let a = funcref_addr(e, loc);
        if is_opq(a) { return opaque_node(loc); }
        return conv_value(a, t, loc);
    }
    if is_record(t) {
        let r = rec_of(t);
        if is_opaque(t) { return opaque_node(loc); }
        if !class_trivial_copy(r) { return class_rv(e, t, loc); }
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
            if b == 0 {
                // a conversion function of the operand's class
                let c = user_conv(e, t, loc);
                if c != 0 { return conv_value(c, t, loc); }
            }
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
    if kind_of(t) == TY_MEMPTR {
        let c = cg_memptr_conv(e, t, loc, false);
        if c == 0 { return opaque_node(loc); }
        return c;
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
    if off == -2 { return cg_vbase_ptr(e, to, loc); }
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

// static_cast (or a C-style cast acting as one) between pointers to, or
// references to, classes related by inheritance: the base subobject's
// offset added (an upcast) or subtracted (a downcast; a null pointer kept),
// an opaque node when it cannot be done, 0 when it is not such a cast.
recursive fn cg_class_cast(t: u32, e: u32, loc: u32) -> u32 {
    if kind_of(t) == TY_MEMPTR {
        let c = cg_memptr_conv(e, t, loc, true);
        if c == 0 { return opaque_node(loc); }
        return c;
    }
    if is_ref(t) {
        let to = tbase(t);
        let ft = nodes[e].ty;
        if !is_record(to) || !is_record(ft) || unqual(to) == unqual(ft) || !is_lvalue(e) { return 0; }
        let xv = if kind_of(t) == TY_RREF { NF_XVALUE } else { 0 };
        let up = base_offset(unqual(ft), unqual(to));
        if up != -1 {
            let c = derived_to_base_lv(e, to, loc);
            if c == 0 { return opaque_node(loc); }
            nodes[c].flags = (nodes[c].flags | xv) as! u16;
            return c;
        }
        let off = base_offset(unqual(to), unqual(ft));
        if off == -1 { return 0; }
        if off < 0 { return opaque_node(loc); }
        let cp = node(N_ICAST, CK_BITCAST, mk_ptr(t_char), n_addr(e, loc) as i64, 0, 0, loc);
        var at = cp;
        if off != 0 { at = node(N_BINARY, B_PTRSUB, mk_ptr(t_char), cp as i64, int_node(off, t_long, loc) as i64, 0, loc); }
        let r = n_deref(node(N_ICAST, CK_BITCAST, mk_ptr(with_q(unqual(to), quals(to) | quals(ft))), at as i64, 0, 0, loc), loc);
        nodes[r].flags = (NF_LVALUE | xv) as! u16;
        return r;
    }
    if !is_pointer(t) { return 0; }
    let pv = rv(e);
    let ft = unqual(nodes[pv].ty);
    if !is_pointer(ft) { return 0; }
    let a = unqual(tbase(ft));
    let b = unqual(tbase(t));
    if !is_record(a) || !is_record(b) || a == b { return 0; }
    if base_offset(a, b) != -1 {
        let up = cg_ptr_conv(pv, unqual(t), loc);
        if up == 0 { return opaque_node(loc); }
        return up;
    }
    let off = base_offset(b, a);
    if off == -1 { return 0; }
    if off < 0 { return opaque_node(loc); }
    if off == 0 { return node(N_ICAST, CK_BITCAST, unqual(t), pv as i64, 0, 0, loc); }
    // ({ B *tmp = e; tmp ? (D *)((char *)tmp - off) : (D *)0; })
    let s = csym(SK_VAR, intern("__base_tmp"), ft, loc);
    syms[s].scope = 1;
    let mark = nscratch.len;
    nscratch.push(node(N_DECL, 0, ft, s, pv as i64, loc as i64, loc));
    let cp = node(N_ICAST, CK_BITCAST, mk_ptr(t_char), rv(n_var(s, loc)) as i64, 0, 0, loc);
    let sub = node(N_BINARY, B_PTRSUB, mk_ptr(t_char), cp as i64, int_node(off, t_long, loc) as i64, 0, loc);
    let dp = node(N_ICAST, CK_BITCAST, unqual(t), sub as i64, 0, 0, loc);
    let z = node(N_ICAST, CK_NULL2PTR, unqual(t), int_node(0, t_int, loc) as i64, 0, 0, loc);
    let c = node(N_COND, 0, unqual(t), icast(rv(n_var(s, loc)), CK_PTR2BOOL, t_bool) as i64, dp as i64, z as i64, loc);
    nscratch.push(n_expr_stmt(c));
    let body = n_block(mark, loc);
    return node(N_STMTEXPR, 0, unqual(t), body as i64, 0, 0, loc);
}

// A condition containing a call of a constexpr function that folds to a
// constant (a function of no parameters whose body returns a constant):
// rewritten to the constant, as clang's code generation folds it.
fn fold_cond(c: u32) {
    let v = fold_value(c, 0);
    if v < 0 || !has_cx_call(c, 0) { return; }
    let t = nodes[c].ty;
    let loc = nodes[c].loc;
    let i = int_node(v, t, loc);
    nodes[c] = nodes[i];
}

// The value (0 or 1, and small integers) of e, or -1.
recursive fn fold_value(e: u32, depth: i64) -> i64 {
    if depth > 8 { return -1; }
    let nd = nodes[e];
    let k = nd.kind as i64;
    if k == N_INT { return if nd.v >= 0 && nd.v < 0x7FFFFFFF { nd.v } else { -1 }; }
    if (k == N_ICAST || k == N_CAST) && (nd.op as i64 == CK_INT2BOOL || nd.op as i64 == CK_NOOP || nd.op as i64 == CK_INTEGRAL) {
        let v = fold_value(nd.a, depth + 1);
        if v < 0 { return -1; }
        if nd.op as i64 == CK_INT2BOOL || kind_of(nd.ty) == TY_BOOL { return if v != 0 { 1 } else { 0 }; }
        return v;
    }
    if k == N_UNARY && nd.op as i64 == U_NOT {
        let v = fold_value(nd.a, depth + 1);
        if v < 0 { return -1; }
        return if v == 0 { 1 } else { 0 };
    }
    if k == N_CALL && nd.c == 0 {
        var cn = nd.a;
        while (nodes[cn].kind as i64 == N_ICAST || nodes[cn].kind as i64 == N_CAST) && (nodes[cn].op as i64 == CK_FUNC2PTR || nodes[cn].op as i64 == CK_NOOP) { cn = nodes[cn].a; }
        if nodes[cn].kind as i64 != N_DECLREF { return -1; }
        let f = nodes[cn].a as i64;
        if f < 0 || syms[f].kind as i64 != SK_FUNC || f >= cxs.len || cxs[f].flags & CF_CONSTEXPR == 0 { return -1; }
        let d = syms[f].def;
        if d < 0 || nodes[d].kind as i64 != N_FUNCDEF || nodes[d].c != 0 { return -1; }
        let b = nodes[d].b;
        if b == 0 || nodes[b].kind as i64 != N_COMPOUND || nodes[b].c != 1 { return -1; }
        let r = nlist[nodes[b].v];
        if nodes[r].kind as i64 != N_RETURN || nodes[r].a == 0 { return -1; }
        return fold_value(nodes[r].a, depth + 1);
    }
    return -1;
}

recursive fn has_cx_call(e: u32, depth: i64) -> bool {
    if depth > 8 { return false; }
    let nd = nodes[e];
    let k = nd.kind as i64;
    if k == N_CALL { return true; }
    if k == N_ICAST || k == N_CAST || k == N_UNARY { return has_cx_call(nd.a, depth + 1); }
    return false;
}

// A pointer to a derived class converted to a pointer to a base reached
// through a virtual base: the virtual base's offset from the vtable, then
// the non-virtual offset; a null pointer kept.
fn cg_vbase_ptr(e: u32, to: u32, loc: u32) -> u32 {
    let ft = nodes[e].ty;
    let from = rec_of(unqual(tbase(ft)));
    path_vb = -1;
    path_nv = 0;
    path_found = false;
    first_path(from, rec_of(unqual(tbase(to))), -1, 0);
    if !path_found || path_vb < 0 { return 0; }
    let nv = path_nv;
    let vb = path_vb;
    let s = csym(SK_VAR, intern("__base_tmp"), unqual(ft), loc);
    syms[s].scope = 1;
    let mark = nscratch.len;
    nscratch.push(node(N_DECL, 0, unqual(ft), s, e as i64, loc as i64, loc));
    let cp = node(N_ICAST, CK_BITCAST, mk_ptr(t_char), rv(n_var(s, loc)) as i64, 0, 0, loc);
    let vo = vbase_off_load(rv(n_var(s, loc)), from, vb, loc);
    var add = node(N_BINARY, B_PTRADD, mk_ptr(t_char), cp as i64, vo as i64, 0, loc);
    if nv != 0 { add = node(N_BINARY, B_PTRADD, mk_ptr(t_char), add as i64, int_node(nv, t_long, loc) as i64, 0, loc); }
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

// The construction of class object dst (an lvalue) from e (an expression
// of its class, a constructor call, arguments in braces): an expression
// (void), or 0 when D3 cannot.
recursive fn init_into(dst: u32, e: u32, loc: u32) -> u32 {
    let t = nodes[dst].ty;
    let k = nodes[e].kind as i64;
    if k == N_XPRV {
        // the call constructs its result at dst
        let ph = nodes[e].b;
        let a = n_ptrcast(n_addr(dst, loc), nodes[ph].ty, loc);
        nodes[ph] = nodes[a];
        nodes[e].kind = N_NULL as! u8;      // used
        return node(N_ICAST, CK_TOVOID, t_void, nodes[e].a as i64, 0, 0, loc);
    }
    if !is_lvalue(e) && is_record(nodes[e].ty) && k == N_COND && nodes[e].b != 0 {
        let b = init_into(dst, nodes[e].b, loc);
        let c = init_into(dst, nodes[e].c, loc);
        if b == 0 || c == 0 { return 0; }
        return node(N_COND, 0, t_void, nodes[e].a as i64, b as i64, c as i64, loc);
    }
    if !is_lvalue(e) && is_record(nodes[e].ty) && k == N_BINARY && nodes[e].op as i64 == B_COMMA {
        let b = init_into(dst, nodes[e].b, loc);
        if b == 0 { return 0; }
        return node(N_BINARY, B_COMMA, t_void, nodes[e].a as i64, b as i64, 0, loc);
    }
    if k == N_INITBRACE && c_initializable(t) {
        let bi = brace_init(t, e, loc);
        if bi == 0 { return 0; }
        return node(N_ASSIGN, 0, unqual(t), dst as i64, compound_value(bi, unqual(t), loc) as i64, 0, loc);
    }
    if is_record(t) && ((k == N_CTOR && nodes[e].op == 2) || (k == N_INITBRACE && is_aggregate_class(rec_of(t)))) {
        return agg_init(dst, nodes[e].v, nodes[e].c as i64, loc);
    }
    let mark = nscratch.len;
    if k == N_CTOR || k == N_INITBRACE { for i in nodes[e].c as i64 { nscratch.push(nlist[nodes[e].v + i]); } }
    else { nscratch.push(e); }
    let zero = (k == N_CTOR || k == N_INITBRACE) && nodes[e].c == 0 && is_record(t) && !has_user_ctor(rec_of(t));
    let st = construct_at(dst, mark, loc);
    if st == 0 { return 0; }
    if zero {
        // T(): value-initialization zeroes a class without a user-provided constructor
        let m = nscratch.len;
        nscratch.push(n_expr_stmt(node(N_ASSIGN, 0, unqual(t), dst as i64, node(N_ZEROINIT, 0, unqual(t), 0, 0, 0, loc) as i64, 0, loc)));
        nscratch.push(st);
        let b = n_block(m, loc);
        return node(N_STMTEXPR, 0, t_void, b as i64, 0, 0, loc);
    }
    return stmt_expr(st, loc);
}

// Statement st as an expression (void).
fn stmt_expr(st: u32, loc: u32) -> u32 {
    let k = nodes[st].kind as i64;
    if k == N_EXPR { return nodes[st].a; }
    if k == N_NULL { return node(N_ICAST, CK_TOVOID, t_void, int_node(0, t_int, loc) as i64, 0, 0, loc); }
    let m = nscratch.len;
    nscratch.push(st);
    let b = n_block(m, loc);
    return node(N_STMTEXPR, 0, t_void, b as i64, 0, 0, loc);
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
    let syn = to_syninit_t(e, unqual(t));
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

// to_syninit for an initializer of type t (0: unknown): the elements of
// arrays and the members of structures in order get their types, so that
// member pointers are converted by C++'s rules (C's would not); with brace
// elision the types are not followed.
recursive fn to_syninit_t(e: u32, t: u32) -> u32 {
    let nd = nodes[e];
    if t == 0 { return to_syninit(e); }
    if nd.kind as i64 == N_INITBRACE {
        if nd.op != 0 { return 0; }
        let n = nd.c as i64;
        var typed = true;
        var rf: i64 = 0;
        var nf: i64 = 0;
        if is_array(t) {
        } else if is_record(t) && kind_of(t) == TY_STRUCT {
            let rec = records[rec_of(t)];
            rf = rec.first as i64;
            nf = rec.count as i64;
            // (unnamed bit-fields take no initializer)
            var named = 0;
            for i in rf..rf + nf { if fields[i].name != 0 { named++; } }
            if n > named { typed = false; }
        } else {
            typed = false;
        }
        let mark = nscratch.len;
        if typed {
            for i in n {
                let et = init_elem_type(t, i);
                // brace elision: a scalar for an aggregate
                let x = nlist[nd.v + i];
                if (is_array(et) || is_record(et)) && nodes[x].kind as i64 != N_INITBRACE && unqual(nodes[x].ty) != et { typed = false; break; }
            }
        }
        for i in n {
            let x = nlist[nd.v + i];
            let y = if typed { to_syninit_t(x, init_elem_type(t, i)) } else { to_syninit(x) };
            if y == 0 { nscratch.resize(mark); return 0; }
            nscratch.push(y);
        }
        let count = nscratch.len - mark;
        let start = commit_list(mark);
        return node_v(N_SYNINIT, 0, 0, 0, 0, count, nd.loc, start);
    }
    if kind_of(t) == TY_MEMPTR {
        let c = conv_value(e, t, nd.loc);
        if is_opq(c) { return 0; }
        return c;
    }
    return to_syninit(e);
}

// The type of element i of an initializer of array or structure type t.
fn init_elem_type(t: u32, i: i64) -> u32 {
    if is_array(t) { return unqual(tbase(t)); }
    let rec = records[rec_of(t)];
    var k = 0;
    for fi in rec.first..rec.first + rec.count {
        if fields[fi].name == 0 { continue; }
        if k == i { return unqual(fields[fi].ty); }
        k++;
    }
    return 0;
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
    if cxs[f].flags & (CF_DELETED | CF_PATTERN) != 0 || is_opaque(ft.base) { nscratch.resize(mark); return opaque_node(loc); }
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
    // a class returned by invisible reference: its destination first
    var dst: u32 = 0;
    if pass_indirect(ft.base) {
        dst = node(N_XDST, 0, mk_ptr(unqual(ft.base)), 0, 0, 0, loc);
        nscratch.push(dst);
    }
    var cf = f;
    if cxs[f].flags & (CF_CTOR | CF_DTOR) != 0 && !cg_base_variant { cf = complete_sym(f); }
    if is_this_fn(f) {
        if obj == 0 || !is_lvalue(obj) { nscratch.resize(mark); return opaque_node(loc); }
        let cls = scope_class_type(cxs[f].dscope as i64);
        let th = obj_addr_as(obj, cls, if cxs[f].flags & CF_CONST != 0 { Q_CONST } else { 0 }, loc);
        if th == 0 { nscratch.resize(mark); return opaque_node(loc); }
        nscratch.push(th);
        if needs_vtt(cf) {
            if cg_vtt_arg == 0 { nscratch.resize(mark); return opaque_node(loc); }
            nscratch.push(cg_vtt_arg);
            cg_vtt_arg = 0;
        }
    }
    for i in n {
        let a = nscratch[mark + i];
        var c: u32 = 0;
        if i < ft.n {
            let pt = tparams[ft.extra + i];
            c = conv_arg(a, pt, loc);
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
        let fp = vfunc_ptr(f, nscratch[mark + (if dst != 0 { 1 } else { 0 })], 0, loc);
        if fp == 0 { nscratch.resize(mark); return opaque_node(loc); }
        call = n_call_ptr(fp, mark, loc);
    } else {
        call = n_call(cf, mark, loc);
    }
    // a member pointer result keeps its C++ type (lowered with the rest in cg_finish)
    if kind_of(ft.base) == TY_MEMPTR { nodes[call].ty = unqual(ft.base); }
    if dst != 0 { return node(N_XPRV, 0, unqual(ft.base), call as i64, dst as i64, 0, loc); }
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
    let slot0 = vt_method_index(f, extra != 0);
    if slot0 < 0 { return 0; }
    let slot = slot0 - extra;
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
    if obj != 0 && !is_lvalue(obj) && is_record(nodes[obj].ty) && !is_opaque(nodes[obj].ty) {
        var v = obj;
        if class_trivial_copy(rec_of(nodes[obj].ty)) && nodes[v].kind as i64 == N_CTOR { v = ctor_value(v, loc); }
        if is_opq(v) { nscratch.resize(mark); return opaque_node(loc); }
        obj = materialize(v, loc);
        if is_opq(obj) { nscratch.resize(mark); return opaque_node(loc); }
    }
    return lower_call(f, obj, mark, loc, !qualified);
}

// `this` in a member function (an rvalue).
fn cg_this_ref(loc: u32) -> u32 {
    let lt = cg_lambda_this(loc);
    if lt != 0 { return lt; }
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
    // evaluated at run time: not a constant evaluation
    if ident_text(name as i64) == "__builtin_is_constant_evaluated" && nscratch.len == mark { return int_node(0, t_bool, loc); }
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

// c ?: b with both lvalues of one type (GNU): an lvalue,
// *({ T *p = &c; *p ? p : &b; }).
fn cg_elvis_lvalue(c: u32, b: u32, loc: u32) -> u32 {
    let t = nodes[c].ty;
    let pt = mk_ptr(t);
    let s = csym(SK_VAR, intern("__elvis_tmp"), pt, loc);
    syms[s].scope = 1;
    let mark = nscratch.len;
    nscratch.push(node(N_DECL, 0, pt, s, n_addr(c, loc) as i64, loc as i64, loc));
    let test = to_bool(rv(n_deref(rv(n_var(s, loc)), loc)));
    let sel = node(N_COND, 0, pt, test as i64, rv(n_var(s, loc)) as i64, n_addr(b, loc) as i64, loc);
    nscratch.push(n_expr_stmt(sel));
    let body = n_block(mark, loc);
    let se = node(N_STMTEXPR, 0, pt, body as i64, 0, 0, loc);
    return n_deref(se, loc);
}

// ---------------------------------------------------------------------------
// Member pointers (Itanium C++ ABI 2.3).

var mfp_rec: i64 = -1;
fn mfp_type() -> u32 {
    if mfp_rec < 0 {
        let r = new_record(intern("__member_fn_ptr"), false, 0);
        records[r].first = fields.len as! u32;
        fields.push(Field { name: intern("ptr"), ty: t_long, offset: 0, bitpos: 0, width: -1, attr_align: 0, flags: 0, rsv: 0, rsv2: 0, loc: 0 });
        fields.push(Field { name: intern("adj"), ty: t_long, offset: 8, bitpos: 64, width: -1, attr_align: 0, flags: 0, rsv: 0, rsv2: 0, loc: 0 });
        records[r].count = 2;
        layout_record(r);
        crec_grow();
        mfp_rec = r;
    }
    return records[mfp_rec].ty << 4;
}

// The null member pointer of type t: { 0, 0 } (functions), -1 (data).
fn memptr_null(t: u32, loc: u32) -> u32 {
    if is_func(tbase(t)) { return node(N_ZEROINIT, 0, unqual(t), 0, 0, 0, loc); }
    let n = int_node(-1, t_long, loc);
    nodes[n].ty = unqual(t);
    return n;
}

// Member pointer e converted to member pointer type t (Itanium 2.3): null
// (nullptr, a null constant), the same type, a member of a base to a member
// of the derived class (the base's offset added: to a data member's
// offset unless null, to a function's `this` adjustment) and, when
// explicit (static_cast), the reverse; 0 when it is not such a conversion,
// an opaque node when it cannot be done (virtual bases).
recursive fn cg_memptr_conv(e: u32, t: u32, loc: u32, explicit: bool) -> u32 {
    if is_opq(e) { return 0; }
    let et = unqual(nodes[e].ty);
    let v = if is_lvalue(e) { rv(e) } else { e };
    if kind_of(et) == TY_NULLPTR || (kind_of(et) != TY_MEMPTR && is_null_const(e)) { return memptr_null(t, loc); }
    if kind_of(et) != TY_MEMPTR { return 0; }
    if et == unqual(t) { return v; }
    let fn_mp = is_func(tbase(t));
    if is_func(tbase(et)) != fn_mp { return 0; }
    if unqual(tbase(et)) != unqual(tbase(t)) && !(fn_mp && tbase(et) == tbase(t)) {
        if !explicit || fn_mp || unqual(tbase(et)) != unqual(tbase(t)) { return 0; }
    }
    let sc = types[et >> 4].extra;
    let dc = types[t >> 4].extra;
    var off = base_offset(dc, sc);      // a member of base sc to one of derived dc
    var sign: i64 = 1;
    if off == -1 && explicit {
        off = base_offset(sc, dc);
        sign = -1;
    }
    if off == -1 { return 0; }
    if off < 0 { return opaque_node(loc); }
    if off == 0 { return node(N_ICAST, CK_NOOP, unqual(t), v as i64, 0, 0, loc); }
    // a constant (&X::m, null): folded, as clang does (a static's initializer stays constant)
    var cv = v;
    while (nodes[cv].kind as i64 == N_ICAST || nodes[cv].kind as i64 == N_CAST) && (nodes[cv].op as i64 == CK_NOOP || nodes[cv].op as i64 == CK_LVAL2RVAL) { cv = nodes[cv].a; }
    if !fn_mp && nodes[cv].kind as i64 == N_INT {
        let x = if nodes[cv].v == -1 { -1 } else { nodes[cv].v + sign * off };
        let n = int_node(x, t_long, loc);
        nodes[n].ty = unqual(t);
        return n;
    }
    if fn_mp && nodes[cv].kind as i64 == N_COMPLIT && nodes[nodes[cv].a].kind as i64 == N_INITLIST && nodes[nodes[cv].a].c == 2 {
        let il = nodes[cv].a;
        let adj = nlist[nodes[il].v + 1];
        if nodes[adj].kind as i64 == N_INT {
            let m0 = nscratch.len;
            nscratch.push(nlist[nodes[il].v]);
            nscratch.push(int_node(nodes[adj].v + sign * off, t_long, loc));
            let start = commit_list(m0);
            let nl = node_v(N_INITLIST, 0, mfp_type(), 0, 0, 2, loc, start);
            let r = compound_value(nl, mfp_type(), loc);
            nodes[r].ty = unqual(t);
            return r;
        }
    }
    let mark = nscratch.len;
    if fn_mp {
        // ({ struct mfp m = e; m.adj += off; m })
        let s = csym(SK_VAR, intern("__mfp"), mfp_type(), loc);
        syms[s].scope = 1;
        nscratch.push(node(N_DECL, 0, mfp_type(), s, v as i64, loc as i64, loc));
        let adj = mfp_field(n_var(s, loc), 1, loc);
        let sum = node(N_BINARY, B_ADD, t_long, rv(mfp_field(n_var(s, loc), 1, loc)) as i64, int_node(sign * off, t_long, loc) as i64, 0, loc);
        nscratch.push(n_expr_stmt(node(N_ASSIGN, 0, t_long, adj as i64, sum as i64, 0, loc)));
        nscratch.push(n_expr_stmt(rv(n_var(s, loc))));
    } else {
        // ({ long o = e; o == -1 ? -1 : o + off })
        let s = csym(SK_VAR, intern("__mpd"), t_long, loc);
        syms[s].scope = 1;
        nscratch.push(node(N_DECL, 0, t_long, s, node(N_ICAST, CK_NOOP, t_long, v as i64, 0, 0, loc) as i64, loc as i64, loc));
        let isnull = node(N_BINARY, B_EQ, t_int, rv(n_var(s, loc)) as i64, int_node(-1, t_long, loc) as i64, 0, loc);
        let sum = node(N_BINARY, B_ADD, t_long, rv(n_var(s, loc)) as i64, int_node(sign * off, t_long, loc) as i64, 0, loc);
        nscratch.push(n_expr_stmt(node(N_COND, 0, t_long, isnull as i64, int_node(-1, t_long, loc) as i64, sum as i64, loc)));
    }
    let body = n_block(mark, loc);
    return node(N_STMTEXPR, 0, unqual(t), body as i64, 0, 0, loc);
}

// l == r / l != r with a member pointer operand (Itanium: data members
// compare their offsets; member functions ptr == ptr && (ptr == 0 || adj == adj)).
recursive fn cg_memptr_cmp(op: i64, l0: u32, r0: u32, loc: u32) -> u32 {
    if op != B_EQ && op != B_NE { return dep_node(t_unknown, loc); }
    let tl = unqual(nodes[l0].ty);
    let tr = unqual(nodes[r0].ty);
    var t = tl;
    if kind_of(tl) != TY_MEMPTR { t = tr; }
    else if kind_of(tr) == TY_MEMPTR && tl != tr {
        // the common type: the member of the derived class
        if base_offset(types[tr >> 4].extra, types[tl >> 4].extra) != -1 { t = tr; }
    }
    let l = cg_memptr_conv(l0, t, loc, false);
    let r = cg_memptr_conv(r0, t, loc, false);
    if l == 0 || r == 0 || is_opq(l) || is_opq(r) { return dep_node(t_unknown, loc); }
    if !is_func(tbase(t)) {
        let a = node(N_ICAST, CK_NOOP, t_long, l as i64, 0, 0, loc);
        let b = node(N_ICAST, CK_NOOP, t_long, r as i64, 0, 0, loc);
        return node(N_BINARY, op, t_bool, a as i64, b as i64, 0, loc);
    }
    let mark = nscratch.len;
    let sa = csym(SK_VAR, intern("__mfp"), mfp_type(), loc);
    syms[sa].scope = 1;
    let sb = csym(SK_VAR, intern("__mfp"), mfp_type(), loc);
    syms[sb].scope = 1;
    nscratch.push(node(N_DECL, 0, mfp_type(), sa, l as i64, loc as i64, loc));
    nscratch.push(node(N_DECL, 0, mfp_type(), sb, r as i64, loc as i64, loc));
    let peq = node(N_BINARY, B_EQ, t_int, rv(mfp_field(n_var(sa, loc), 0, loc)) as i64, rv(mfp_field(n_var(sb, loc), 0, loc)) as i64, 0, loc);
    let pz = node(N_BINARY, B_EQ, t_int, rv(mfp_field(n_var(sa, loc), 0, loc)) as i64, int_node(0, t_long, loc) as i64, 0, loc);
    let aeq = node(N_BINARY, B_EQ, t_int, rv(mfp_field(n_var(sa, loc), 1, loc)) as i64, rv(mfp_field(n_var(sb, loc), 1, loc)) as i64, 0, loc);
    let any = node(N_BINARY, B_LOR, t_int, pz as i64, aeq as i64, 0, loc);
    var res = node(N_BINARY, B_LAND, t_int, peq as i64, any as i64, 0, loc);
    if op == B_NE { res = node(N_UNARY, U_NOT, t_int, res as i64, 0, 0, loc); }
    nscratch.push(n_expr_stmt(icast(res, CK_INT2BOOL, t_bool)));
    let body = n_block(mark, loc);
    return node(N_STMTEXPR, 0, t_bool, body as i64, 0, 0, loc);
}

// A member pointer as a condition: ptr != 0 (functions), != -1 (data).
fn cg_memptr_bool(v: u32) -> u32 {
    let loc = nodes[v].loc;
    let mt = types[nodes[v].ty >> 4];
    if is_func(mt.base) {
        mfp_type();
        let s = csym(SK_VAR, intern("__mfp"), mfp_type(), loc);
        syms[s].scope = 1;
        let mark = nscratch.len;
        nscratch.push(node(N_DECL, 0, mfp_type(), s, v as i64, loc as i64, loc));
        nscratch.push(n_expr_stmt(icast(rv(mfp_field(n_var(s, loc), 0, loc)), CK_INT2BOOL, t_bool)));
        let body = n_block(mark, loc);
        return node(N_STMTEXPR, 0, t_bool, body as i64, 0, 0, loc);
    }
    return node(N_BINARY, B_NE, t_bool, v as i64, int_node(-1, t_long, loc) as i64, 0, loc);
}

fn mfp_field(v: u32, i: i64, loc: u32) -> u32 {
    let n = node(N_MEMBER, 0, t_long, v as i64, records[mfp_rec].first as i64 + i, 0, loc);
    nodes[n].flags = nodes[v].flags & NF_LVALUE;
    return n;
}

// &C::m for a member (s0: the found chain, cls: C): a member pointer value, or 0.
recursive fn cg_member_addr(e: u32, loc: u32) -> u32 {
    let k = nodes[e].kind as i64;
    if k == N_CXX && nodes[e].op == 6 {
        // a data member: its offset in its class
        let s = nodes[e].a as i64;
        let fi = field_index(s);
        if fi < 0 || fields[fi].width >= 0 { return 0; }
        let cls = scope_class_type(cxs[s].dscope as i64);
        let n = int_node(fields[fi].offset, t_long, loc);
        nodes[n].ty = mk_memptr(fields[fi].ty, cls);
        return n;
    }
    if k != N_FUNCREF || nodes[e].op == 0 { return 0; }
    // a member function: the single non-static one of the set
    var s = nodes[e].a as i64;
    var f: i64 = -1;
    var count = 0;
    while s >= 0 {
        let x = resolve(s);
        if x >= 0 && (syms[x].kind as i64 == SK_FUNC || syms[x].kind as i64 == SK_TEMPLATE) { f = x; count++; }
        s = cxs[s].nnext as i64;
    }
    if count != 1 || syms[f].kind as i64 != SK_FUNC || !is_this_fn(f) { return 0; }
    let cls = scope_class_type(cxs[f].dscope as i64);
    let mt = mk_memptr(syms[f].ty, cls);
    var ptr: u32 = 0;
    if cxs[f].flags & CF_VIRTUAL != 0 {
        let slot = vt_method_index(f, false);
        if slot < 0 { return 0; }
        ptr = int_node(1 + slot * 8, t_long, loc);
    } else {
        ptr = node(N_ICAST, CK_PTR2INT, t_long, icast(n_ref_fn(f, loc), CK_FUNC2PTR, mk_ptr(abi_type(f))) as i64, 0, 0, loc);
    }
    let mark = nscratch.len;
    nscratch.push(ptr);
    nscratch.push(int_node(0, t_long, loc));
    let start = commit_list(mark);
    let mty = mfp_type();
    let il = node_v(N_INITLIST, 0, mty, 0, 0, 2, loc, start);
    let v = compound_value(il, mty, loc);
    nodes[v].ty = mt;
    return v;
}

// obj.*mp / ptr->*mp.
recursive fn cg_memptr_access(l: u32, mp: u32, arrow: bool, loc: u32) -> u32 {
    if is_opq(l) || is_opq(mp) || kind_of(nodes[mp].ty) != TY_MEMPTR { return dep_node(t_unknown, loc); }
    var obj = l;
    if arrow { obj = mk_deref_cx(l, loc); }
    if is_opq(obj) || !is_record(nodes[obj].ty) { return dep_node(t_unknown, loc); }
    let mt = types[nodes[mp].ty >> 4];
    let cls = mt.extra;
    if unqual(nodes[obj].ty) != unqual(cls) {
        let b = derived_to_base_lv(obj, unqual(cls), loc);
        if b == 0 { return dep_node(t_unknown, loc); }
        obj = b;
    }
    if !is_lvalue(obj) { obj = materialize(obj, loc); }
    if is_func(mt.base) {
        // bound to a call: N_CXX op 5, a = object, b = the member pointer
        let n = node(N_CXX, 5, mt.base, obj as i64, mp as i64, 0, loc);
        return n;
    }
    // *(T *)((char *)&obj + mp)
    let cp = node(N_ICAST, CK_BITCAST, mk_ptr(t_char), n_addr(obj, loc) as i64, 0, 0, loc);
    let add = node(N_BINARY, B_PTRADD, mk_ptr(t_char), cp as i64, rv(mp) as i64, 0, loc);
    let t = with_q(mt.base, quals(nodes[obj].ty) & (Q_CONST | Q_VOLATILE));
    let tp = node(N_ICAST, CK_BITCAST, mk_ptr(t), add as i64, 0, 0, loc);
    return n_deref(tp, loc);
}

// (obj.*pmf)(args): this = (char *)&obj + adj; the function is ptr, or,
// when ptr is odd, the vtable entry at ptr - 1.
recursive fn cg_memfn_call(b: u32, mark: i64, loc: u32) -> u32 {
    let obj = nodes[b].a;
    let mp = nodes[b].b;
    let ft = nodes[b].ty;
    let f = types[ft >> 4];
    if !by_value_ok(f.base) || is_ref(f.base) { nscratch.resize(mark); return opaque_node(loc); }
    let nargs = nscratch.len - mark;
    if nargs != f.n && f.flags & TF_VARIADIC == 0 { nscratch.resize(mark); return opaque_node(loc); }
    let cls = types[nodes[mp].ty >> 4].extra;
    let mty = mfp_type();
    // the C function type: this first
    var q: i64 = 0;
    if (f.flags as i64) & TF_MCONST != 0 { q = Q_CONST; }
    let lf = types[lower_ty(ft) >> 4];
    let am = abi_scratch.len;
    abi_scratch.push(mk_ptr(with_q(unqual(cls), q)));
    for i in lf.n { abi_scratch.push(tparams[lf.extra + i]); }
    fn_scratch.clear();
    for i in am..abi_scratch.len { fn_scratch.push(abi_scratch[i]); }
    abi_scratch.resize(am);
    let cft = qt(mk_type(TY_FUNC, (lf.flags as i64) & TF_VARIADIC, lf.base, 0, 0, 0) as i64, 0);
    let fpt = mk_ptr(cft);
    // ({ struct mfp m = mp; char *t = (char *)&obj + m.adj;
    //    fp = m.ptr & 1 ? *(F *)(*(char **)t + m.ptr - 1) : (F)m.ptr; fp(t, args) })
    let ms = csym(SK_VAR, intern("__mfp"), mty, loc);
    syms[ms].scope = 1;
    let ts = csym(SK_VAR, intern("__this"), mk_ptr(t_char), loc);
    syms[ts].scope = 1;
    // the converted arguments (kept in stmt_buf while the rest is built)
    let sb = stmt_buf.len;
    for i in nargs {
        let a = nscratch[mark + i];
        var c: u32 = 0;
        if i < f.n { c = conv_arg(a, tparams[f.extra + i], loc); }
        else if is_opq(a) || !cish_node(a) { c = opaque_node(loc); }
        else { c = default_promote(rv(a)); }
        if is_opq(c) { stmt_buf.resize(sb); nscratch.resize(mark); return opaque_node(loc); }
        stmt_buf.push(c);
    }
    nscratch.resize(mark);
    let bmark = nscratch.len;
    let mv = if is_lvalue(mp) { rv(mp) } else { mp };
    nscratch.push(node(N_DECL, 0, mty, ms, mv as i64, loc as i64, loc));
    let adj = rv(mfp_field(n_var(ms, loc), 1, loc));
    let cp = node(N_ICAST, CK_BITCAST, mk_ptr(t_char), n_addr(obj, loc) as i64, 0, 0, loc);
    let tv = node(N_BINARY, B_PTRADD, mk_ptr(t_char), cp as i64, adj as i64, 0, loc);
    nscratch.push(node(N_DECL, 0, mk_ptr(t_char), ts, tv as i64, loc as i64, loc));
    let ptrv = rv(mfp_field(n_var(ms, loc), 0, loc));
    let odd = node(N_BINARY, B_AND, t_long, ptrv as i64, int_node(1, t_long, loc) as i64, 0, loc);
    let test = icast(odd, CK_INT2BOOL, t_bool);
    // virtual: *(F *)(*(char **)t + ptr - 1)
    let vtp = rv(n_deref(node(N_ICAST, CK_BITCAST, mk_ptr(mk_ptr(t_char)), rv(n_var(ts, loc)) as i64, 0, 0, loc), loc));
    let off = node(N_BINARY, B_SUB, t_long, rv(mfp_field(n_var(ms, loc), 0, loc)) as i64, int_node(1, t_long, loc) as i64, 0, loc);
    let ep = node(N_BINARY, B_PTRADD, mk_ptr(t_char), vtp as i64, off as i64, 0, loc);
    let vf = rv(n_deref(node(N_ICAST, CK_BITCAST, mk_ptr(fpt), ep as i64, 0, 0, loc), loc));
    let nf = node(N_ICAST, CK_INT2PTR, fpt, rv(mfp_field(n_var(ms, loc), 0, loc)) as i64, 0, 0, loc);
    let fp = node(N_COND, 0, fpt, test as i64, vf as i64, nf as i64, loc);
    let am2 = nscratch.len;
    nscratch.push(node(N_ICAST, CK_BITCAST, mk_ptr(with_q(unqual(cls), q)), rv(n_var(ts, loc)) as i64, 0, 0, loc));
    for i in sb..stmt_buf.len { nscratch.push(stmt_buf[i]); }
    stmt_buf.resize(sb);
    let call = n_call_ptr(fp, am2, loc);
    let res = wrap_ref_result(call, f.base);
    nscratch.push(n_expr_stmt(res));
    let body = n_block(bmark, loc);
    let t = nodes[res].ty;
    return node(N_STMTEXPR, 0, if is_void(t) { t_void } else { unqual(t) }, body as i64, 0, 0, loc);
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
        else if which == 1 { sc = adl_ns(nodes[l].ty); }
        else if r != 0 { sc = adl_ns(nodes[r].ty); }
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

// The namespace of a class or enumeration type (argument-dependent lookup
// of operators), or -1.
fn adl_ns(t0: u32) -> i64 {
    let t = nonref(t0);
    if is_record(t) || kind_of(t) == TY_ENUM {
        let sc = type_scope(t);
        if sc >= 0 { return enclosing_ns(sc); }
    }
    return -1;
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
    // a copy or a move of an object of the class (or of a derived class):
    // a user-provided constructor, else the implicit one
    if n == 1 && !is_opq(nscratch[mark]) && is_record(nodes[nscratch[mark]].ty) && nodes[nscratch[mark]].kind as i64 != N_CTOR &&
       (unqual(nodes[nscratch[mark]].ty) == cls || base_offset(unqual(nodes[nscratch[mark]].ty), cls) >= 0) {
        let a = nscratch[mark];
        if s >= 0 {
            let f = best_candidate(s, mark, true);
            if f >= 0 && user_provided(f) && cxs[f].flags & CF_DELETED == 0 && first_param_ref(f, cls) != 0 { return f; }
        }
        let rvalue = !is_lvalue(a) || nodes[a].flags & NF_XVALUE != 0;
        let c = copy_ctor_of(r, rvalue);
        if c == -1 { return -3; }
        if c == -2 { return -1; }
        return c;
    }
    // a copy with the implicit (trivial) copy constructor
    if n == 1 && is_record(nodes[nscratch[mark]].ty) && unqual(nodes[nscratch[mark]].ty) == cls && !is_opq(nscratch[mark]) &&
       nodes[nscratch[mark]].kind as i64 != N_CTOR && class_trivial_copy(r) { return -3; }
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
    if nd.kind as i64 == N_CTOR && nd.op == 2 {
        // T{args} of an aggregate
        let x = agg_init(n_var(s, loc), nd.v, nd.c as i64, loc);
        if x == 0 { return 0; }
        return n_expr_stmt(x);
    }
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
    if nscratch.len - mark == 1 {
        let a0 = nscratch[mark];
        if is_class_prv(a0) && unqual(nodes[a0].ty) == unqual(t) && !(nodes[a0].kind as i64 == N_CTOR && nodes[a0].c == 0 && class_trivial_copy(r)) {
            // copy elision: the prvalue is constructed in place
            nscratch.resize(mark);
            let x = init_into(obj, a0, loc);
            if x == 0 { return 0; }
            return n_expr_stmt(x);
        }
    }
    let f = pick_ctor(r, mark);
    if f == -2 { nscratch.resize(mark); return n_null(loc); }
    if f == -3 {
        var src = nscratch[mark];
        nscratch.resize(mark);
        if is_record(nodes[src].ty) && unqual(nodes[src].ty) != unqual(t) {
            if !is_lvalue(src) { src = materialize(src, loc); }
            let b = derived_to_base_lv(src, unqual(t), loc);
            if b == 0 { return 0; }
            src = b;
        }
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

// The vtable pointer stores of class r's object at `this` (clang's
// InitializeVTablePointers), pushed to stmt_buf: the address points of
// the complete object's vtable group, or in a base-object constructor or
// destructor of a class with virtual bases, from the VTT (cg_cur_vtt), with
// the locations of virtual base subobjects from the vtable.
var cg_cur_vtt: i64 = -1;       // the VTT parameter of the structor being built (-1: complete or none)
var vp_list: VtAP[>..<] = [];   // (class, offset, nearest vbase << 32 | offset from it) of the vptrs
var vp_nvb: i64[>..<] = [];
var vp_vis: u32[>..<] = [];

fn vptr_stores(r: i64, th: i64, loc: u32) -> bool {
    let vt = vtable_sym(r);
    if vt < 0 { return false; }
    let g = vt_class(r);
    if !group_ok(g) { return false; }
    vp_list.clear();
    vp_nvb.clear();
    vp_vis.clear();
    vptrs_of(r, 0, -1, 0, false, r);
    let ppv = mk_ptr(t_voidptr);
    let use_vtt = cg_cur_vtt >= 0 && has_vb(r);
    for i in vp_list.len {
        let V = vp_list[i];
        let nvb = vp_nvb[i];
        let cls = V.cls as i64;
        var val: u32 = 0;
        if use_vtt && (has_vb(cls) || nvb >= 0) {
            let k = vtt_svp_index(r, cls, V.off);
            let vtt = rv(n_var(cg_cur_vtt, loc));
            let e = node(N_BINARY, B_PTRADD, ppv, vtt as i64, int_node(k, t_long, loc) as i64, 0, loc);
            val = rv(n_deref(node(N_ICAST, CK_BITCAST, mk_ptr(ppv), e as i64, 0, 0, loc), loc));
        } else {
            let ap = vt_address_point(g, cls, V.off);
            if ap < 0 { return false; }
            let base = icast(n_var(vt, loc), CK_ARRAY2PTR, mk_ptr(tbase(syms[vt].ty)));
            let e = node(N_BINARY, B_PTRADD, mk_ptr(tbase(syms[vt].ty)), base as i64, int_node(ap, t_long, loc) as i64, 0, loc);
            val = node(N_ICAST, CK_BITCAST, ppv, e as i64, 0, 0, loc);
        }
        // where: this + offset, or through the virtual base's offset
        let cp = node(N_ICAST, CK_BITCAST, mk_ptr(t_char), rv(n_var(th, loc)) as i64, 0, 0, loc);
        var at = cp;
        if use_vtt && nvb >= 0 {
            let vo = vbase_off_load(rv(n_var(th, loc)), r, nvb, loc);
            at = node(N_BINARY, B_PTRADD, mk_ptr(t_char), cp as i64, vo as i64, 0, loc);
            if V.idx != 0 { at = node(N_BINARY, B_PTRADD, mk_ptr(t_char), at as i64, int_node(V.idx, t_long, loc) as i64, 0, loc); }
        } else if V.off != 0 {
            at = node(N_BINARY, B_PTRADD, mk_ptr(t_char), cp as i64, int_node(V.off, t_long, loc) as i64, 0, loc);
        }
        let dst = n_deref(node(N_ICAST, CK_BITCAST, mk_ptr(ppv), at as i64, 0, 0, loc), loc);
        stmt_buf.push(n_expr_stmt(node(N_ASSIGN, 0, ppv, dst as i64, val as i64, 0, loc)));
    }
    return true;
}

// clang's getVTablePointers.
recursive fn vptrs_of(cls: i64, off: i64, nvb: i64, off_nvb: i64, nv_primary: bool, vtable_cls: i64) {
    if !nv_primary {
        vp_list.push(VtAP { cls: cls as! i32, rsv: 0, off: off, idx: off_nvb });
        vp_nvb.push(nvb);
    }
    for i in vt_nbases(cls) {
        let br = vt_base_rec(cls, i);
        if !vt_dyn(br) { continue; }
        if vt_base_virtual(cls, i) {
            var seen = false;
            for x in vp_vis { if x as i64 == br { seen = true; } }
            if seen { continue; }
            vp_vis.push(br as! u32);
            vptrs_of(br, vt_vbo(vtable_cls, br), br, 0, false, vtable_cls);
        } else {
            let o = vt_base_off(cls, i);
            vptrs_of(br, off + o, nvb, off_nvb + o, vt_prim(cls) == br && !vt_prim_virtual(cls), vtable_cls);
        }
    }
}

// The offset of virtual base v in the object of class r at pointer p
// (from its vtable): *(long *)(*(char **)p + vbase offset offset).
fn vbase_off_load(p: u32, r: i64, v: i64, loc: u32) -> u32 {
    let vbo = class_vbo(r, v);
    let vptr = rv(n_deref(node(N_ICAST, CK_BITCAST, mk_ptr(mk_ptr(t_char)), p as i64, 0, 0, loc), loc));
    let e = node(N_BINARY, B_PTRADD, mk_ptr(t_char), vptr as i64, int_node(vbo, t_long, loc) as i64, 0, loc);
    return rv(n_deref(node(N_ICAST, CK_BITCAST, mk_ptr(t_long), e as i64, 0, 0, loc), loc));
}

// A glvalue of class `from` converted to its base `to` through a virtual
// base (cx_over.derived_to_base_lv): the last virtual base on the path
// from the vtable, then the non-virtual offset; 0 when not a base.
fn cg_vbase_lv(e: u32, to: u32, loc: u32) -> u32 {
    let from = rec_of(nodes[e].ty);
    let tr = rec_of(to);
    path_vb = -1;
    path_nv = 0;
    path_found = false;
    first_path(from, tr, -1, 0);
    if !path_found || path_vb < 0 { return 0; }
    var o = e;
    if !is_lvalue(o) { o = materialize(o, loc); }
    let pa = n_addr(o, loc);
    let cp = node(N_ICAST, CK_BITCAST, mk_ptr(t_char), pa as i64, 0, 0, loc);
    let vo = vbase_off_load(pa, from, path_vb, loc);
    var at = node(N_BINARY, B_PTRADD, mk_ptr(t_char), cp as i64, vo as i64, 0, loc);
    if path_nv != 0 { at = node(N_BINARY, B_PTRADD, mk_ptr(t_char), at as i64, int_node(path_nv, t_long, loc) as i64, 0, loc); }
    let r = n_deref(node(N_ICAST, CK_BITCAST, mk_ptr(with_q(unqual(to), quals(nodes[e].ty))), at as i64, 0, 0, loc), loc);
    nodes[r].flags = nodes[r].flags | (nodes[e].flags & NF_XVALUE);
    return r;
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
            let sv = cg_base_variant;
            cg_base_variant = !cg_complete;
            if !cg_complete && cg_cur_vtt >= 0 { cg_vtt_arg = rv(n_var(cg_cur_vtt, loc)); }
            let st = construct_at(obj, mark, loc);
            cg_base_variant = sv;
            cg_vtt_arg = 0;
            if st == 0 { return false; }
            stmt_buf.push(st);
            let d = destroy_stmt(n_deref(rv(n_var(th, loc)), loc), loc);
            if d != 0 { stmt_buf.push(node(N_XPUSH, XP_STMT | XP_EHONLY, 0, d as i64, 0, 0, loc)); }
            return true;
        }
    }
    // the virtual bases (the complete object's constructor only), in
    // depth-first left-to-right order
    if cg_complete && has_vb(r) {
        let vm = vbs.len;
        vb_scratch_mark = vm;
        collect_vbases(r);
        let ve = vbs.len;
        for j in vm..ve {
            let vt = vbs[j];
            let vr = rec_of(vt);
            let off = vt_vbo(r, vr);
            let mi = find_init(inits, -1, vt);
            let obj = this_at(th, vt, off, loc);
            let mark = nscratch.len;
            if mi != 0 { push_init_args(nodes[mi].b); }
            if has_vb(vr) { cg_vtt_arg = vtt_arg(r, vr, off, loc); }
            let sv = cg_base_variant;
            cg_base_variant = true;
            let st = construct_at(obj, mark, loc);
            cg_base_variant = sv;
            cg_vtt_arg = 0;
            if st == 0 { vbs.resize(vm); return false; }
            stmt_buf.push(st);
            let ds = vbase_destroy(r, th, vr, loc);
            if ds != 0 { stmt_buf.push(node(N_XPUSH, XP_STMT | XP_EHONLY, 0, ds as i64, 0, 0, loc)); }
        }
        vbs.resize(vm);
    }
    // the bases
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if !is_record(b.ty) { return false; }
        if b.flags & BF_VIRTUAL != 0 { continue; }
        let mi = find_init(inits, -1, b.ty);
        let obj = this_base(th, b.ty, loc);
        if obj == 0 { return false; }
        let mark = nscratch.len;
        if mi != 0 { push_init_args(nodes[mi].b); }
        if has_vb(rec_of(b.ty)) { cg_vtt_arg = vtt_arg(r, rec_of(b.ty), b.offset, loc); }
        let sv = cg_base_variant;
        cg_base_variant = true;
        let st = construct_at(obj, mark, loc);
        cg_base_variant = sv;
        cg_vtt_arg = 0;
        if st == 0 { return false; }
        stmt_buf.push(st);
        // destroyed if what follows throws
        let ds = base_destroy(th, b.ty, loc);
        if ds != 0 { stmt_buf.push(node(N_XPUSH, XP_STMT | XP_EHONLY, 0, ds as i64, 0, 0, loc)); }
    }
    if cr.flags & CR_DYNAMIC != 0 {
        if !vptr_stores(r, th, loc) { return false; }
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
            if is_record(bt) && args != 0 { return false; }
            if is_record(bt) && needs_default_init(rec_of(bt)) {
                let lp = arr_loop(lv, false, loc);
                if lp == 0 { return false; }
                stmt_buf.push(lp);
                member_eh_cleanup(th, r, i, loc);
                continue;
            }
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
            member_eh_cleanup(th, r, i, loc);
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

// The destruction of base class subobject bt of *this (the base-object
// variant, D2), or 0.
var cg_complete = true;          // the structor being built is the complete-object variant

// The complete-object variant (C1 / D1) of structor s of class r with
// virtual bases: C1 constructs the virtual bases, then does what C2 does
// with the complete object's vtables; D1 calls D2 with the VTT, then
// destroys the virtual bases.
fn complete_variant_body(s: i64, r: i64, body: u32, inits: u32, loc: u32) {
    let a = complete_sym(s);
    fn_this.insert(a as u64, cg_this as! u32);
    let sv_vtt = cg_cur_vtt;
    let sv_complete = cg_complete;
    cg_cur_vtt = -1;
    cg_complete = true;
    let sm = stmt_buf.len;
    var ok = true;
    if cxs[s].flags & CF_CTOR != 0 {
        ok = ctor_prologue(r, cg_this, inits, loc);
    } else {
        // the virtual bases, destroyed after the base-object destructor
        let vm = vbs.len;
        vb_scratch_mark = vm;
        collect_vbases(r);
        let ve = vbs.len;
        for j in vm..ve {
            let ds = vbase_destroy(r, cg_this, rec_of(vbs[j]), loc);
            if ds != 0 { stmt_buf.push(node(N_XPUSH, XP_STMT, 0, ds as i64, 0, 0, loc)); }
        }
        vbs.resize(vm);
        let am = nscratch.len;
        cg_vtt_arg = vtt_arg(r, r, 0, loc);
        let sv = cg_base_variant;
        cg_base_variant = true;
        let c = lower_call(s, n_deref(rv(n_var(cg_this, loc)), loc), am, loc, false);
        cg_base_variant = sv;
        cg_vtt_arg = 0;
        if is_opq(c) { ok = false; } else { stmt_buf.push(n_expr_stmt(c)); }
    }
    cg_cur_vtt = sv_vtt;
    cg_complete = sv_complete;
    let mark = nscratch.len;
    for i in sm..stmt_buf.len { nscratch.push(stmt_buf[i]); }
    stmt_buf.resize(sm);
    if cxs[s].flags & CF_CTOR != 0 { nscratch.push(body); }
    if !ok { nscratch.push(mark_bad_stmt(loc)); }
    let b = n_block(mark, loc);
    // the same parameters
    var np: i64 = 0;
    var ps: i64 = 0;
    let st, n = fn_param_list(s);
    if st >= 0 { np = n; ps = st; }
    let fd = node_v(N_FUNCDEF, 0, syms[a].ty, a, b as i64, np, loc, ps);
    syms[a].def = fd as! i32;
    syms[a].flags = syms[a].flags | SF_DEFINED;
    cg_extra.push(fd);
}

fn base_destroy(th: i64, bt: u32, loc: u32) -> u32 {
    if !is_record(bt) || is_opaque(bt) || class_dtor(rec_of(bt)) < 0 { return 0; }
    let obj = this_base(th, bt, loc);
    if obj == 0 { return 0; }
    let tn = n_deref(rv(n_var(th, loc)), loc);
    let r = rec_of(nodes[tn].ty);
    let br = rec_of(bt);
    if has_vb(br) { cg_vtt_arg = vtt_arg(r, br, vt_nvbase_off(r, br), loc); }
    let sv = cg_base_variant;
    cg_base_variant = true;
    let st = destroy_stmt(obj, loc);
    cg_base_variant = sv;
    cg_vtt_arg = 0;
    return st;
}

// The destruction of virtual base vr of *this (complete object of r).
fn vbase_destroy(r: i64, th: i64, vr: i64, loc: u32) -> u32 {
    if class_dtor(vr) < 0 { return 0; }
    let off = vt_vbo(r, vr);
    let obj = this_at(th, records[vr].ty << 4, off, loc);
    if has_vb(vr) { cg_vtt_arg = vtt_arg(r, vr, off, loc); }
    let sv = cg_base_variant;
    cg_base_variant = true;
    let st = destroy_stmt(obj, loc);
    cg_base_variant = sv;
    cg_vtt_arg = 0;
    return st;
}

// The subobject of class type bt at offset off of *this (an lvalue).
fn this_at(th: i64, bt: u32, off: i64, loc: u32) -> u32 {
    let cp = node(N_ICAST, CK_BITCAST, mk_ptr(t_char), rv(n_var(th, loc)) as i64, 0, 0, loc);
    var at = cp;
    if off != 0 { at = node(N_BINARY, B_PTRADD, mk_ptr(t_char), cp as i64, int_node(off, t_long, loc) as i64, 0, loc); }
    return n_deref(node(N_ICAST, CK_BITCAST, mk_ptr(unqual(bt)), at as i64, 0, 0, loc), loc);
}

// The destruction of member fi of *this (class r), or 0.
fn member_destroy(th: i64, r: i64, fi: i64, loc: u32) -> u32 {
    let f = fields[fi];
    if f.name == 0 { return 0; }
    if is_record(f.ty) && !is_opaque(f.ty) { return destroy_stmt(this_member(th, r, fi, loc), loc); }
    if is_array(f.ty) {
        let bt = base_elem_t(f.ty);
        if is_record(bt) && !is_opaque(bt) && class_dtor(rec_of(bt)) >= 0 {
            let lp = arr_loop(this_member(th, r, fi, loc), true, loc);
            if lp == 0 { return mark_bad_stmt(loc); }
            return lp;
        }
    }
    return 0;
}

// A constructed member's destruction if the rest of the constructor throws.
fn member_eh_cleanup(th: i64, r: i64, fi: i64, loc: u32) {
    let d = member_destroy(th, r, fi, loc);
    if d != 0 { stmt_buf.push(node(N_XPUSH, XP_STMT | XP_EHONLY, 0, d as i64, 0, 0, loc)); }
}

// The destruction of r's members (in reverse order) and bases (in reverse)
// as cleanups at the start of a destructor's body: pushed in construction
// order, so that they run after the body on every exit, innermost first.
recursive fn dtor_cleanups(r: i64, th: i64, loc: u32) -> bool {
    let cr = crecs[r];
    for i in cr.nbases {
        let bb = cbases[cr.bases + i];
        if bb.flags & BF_VIRTUAL != 0 { continue; }
        let ds = base_destroy(th, bb.ty, loc);
        if ds != 0 { stmt_buf.push(node(N_XPUSH, XP_STMT, 0, ds as i64, 0, 0, loc)); }
    }
    let rec = records[r];
    for i in rec.first..rec.first + rec.count {
        let d = member_destroy(th, r, i as i64, loc);
        if d != 0 { stmt_buf.push(node(N_XPUSH, XP_STMT, 0, d as i64, 0, 0, loc)); }
    }
    return true;
}

// The body of member function s (parsed: body) with its constructor
// prologue or destructor cleanups (cx_stmt.parse_function_body). A
// function-try-block (handlers nscratch[hmark..], hmark >= 0) encloses the
// prologue and the destructor's cleanups too.
recursive fn cg_wrap_body(s: i64, body: u32, inits: u32, loc: u32) -> u32 { return cg_wrap_body_try(s, body, inits, loc, -1); }

recursive fn cg_wrap_body_try(s: i64, body: u32, inits: u32, loc: u32, hmark: i64) -> u32 {
    let fl = cxs[s].flags;
    if fl & (CF_CTOR | CF_DTOR) == 0 || cg_this < 0 {
        if hmark < 0 { return body; }
        let t = cg_try(body, hmark, loc);
        let m = nscratch.len;
        nscratch.push(t);
        return n_block(m, loc);
    }
    let r = rec_of(scope_class_type(cxs[s].dscope as i64));
    if has_vb(r) && hmark < 0 {
        // the complete-object variant is a function of its own
        complete_variant_body(s, r, body, inits, loc);
    }
    let sv_vtt = cg_cur_vtt;
    let sv_complete = cg_complete;
    cg_cur_vtt = if has_vb(r) { make_vtt(s, loc) } else { -1 };
    cg_complete = !has_vb(r);
    let sm = stmt_buf.len;
    var ok = true;
    if fl & CF_CTOR != 0 {
        ok = ctor_prologue(r, cg_this, inits, loc);
    } else {
        if crecs[r].flags & CR_DYNAMIC != 0 {
            if !vptr_stores(r, cg_this, loc) { ok = false; }
        }
        if !dtor_cleanups(r, cg_this, loc) { ok = false; }
    }
    cg_cur_vtt = sv_vtt;
    cg_complete = sv_complete;
    // the handlers stay below the statements while these are collected
    let mark = nscratch.len;
    for i in sm..stmt_buf.len { nscratch.push(stmt_buf[i]); }
    stmt_buf.resize(sm);
    nscratch.push(body);
    if !ok { nscratch.push(mark_bad_stmt(loc)); }
    let inner = n_block(mark, loc);
    if hmark < 0 { return inner; }
    let t = cg_try(inner, hmark, loc);
    let m2 = nscratch.len;
    nscratch.push(t);
    return n_block(m2, loc);
}

// ---------------------------------------------------------------------------
// Variables.

var gi_stmts: u32[>..] = [];     // the dynamic initialization of namespace-scope variables, in order
var gi_prio: u32[>..] = [];      // their init_priority (65535: none)
var cur_init_prio: i64 = 65535;  // init_priority(N) of the declaration being parsed

fn gi_push(st: u32, prio: i64) {
    gi_stmts.push(st);
    gi_prio.push(prio as! u32);
}

// The N_DECL of variable s (block or namespace scope, ctx) with initializer
// `init` as written (form: 0 none, 1 =, 2 (), 3 {}) and conv as C's path
// converted it; pushes it to nscratch with the construction of a class
// object (cx_sema.parse_var_init).
recursive fn cg_decl(s: i64, init: u32, conv0: u32, form: i64, loc: u32, dloc: u32, ctx: i64) {
    var conv = conv0;
    let t = syms[s].ty;
    let prio = cur_init_prio;
    cur_init_prio = 65535;
    if ctx == DC_NS || cxs[s].flags & CF_MEMBER != 0 { syms[s].flags = syms[s].flags | SF_FILESCOPE; }
    // a static local: no linkage (C's lowering names it function.name)
    // (a block-scope thread_local has static storage too)
    if ctx != DC_NS && cxs[s].flags & CF_MEMBER == 0 && block_fn_depth > 0 && syms[s].flags & SF_THREAD != 0 && syms[s].sc as i64 != SC_EXTERN {
        syms[s].sc = SC_STATIC as! u8;
    }
    let static_local = ctx != DC_NS && cxs[s].flags & CF_MEMBER == 0 && block_fn_depth > 0 && syms[s].sc as i64 == SC_STATIC;
    let tls = syms[s].flags & SF_THREAD != 0;
    if static_local { syms[s].flags = syms[s].flags & ~SF_FILESCOPE; }
    let fs = syms[s].flags & SF_FILESCOPE != 0;
    if !decl_is_extern && syms[s].sc as i64 == SC_EXTERN { syms[s].sc = 0; }
    // (extern with an initializer is a definition)
    let is_extern = syms[s].sc as i64 == SC_EXTERN && init == 0;
    let local = !fs && syms[s].sc as i64 != SC_EXTERN && !static_local;
    var cst: u32 = 0;
    var has_dtor = false;
    if is_ref(t) {
        if init != 0 {
            var e = init;
            if nodes[e].kind as i64 == N_INITBRACE && nodes[e].c == 1 { e = nlist[nodes[e].v]; }
            // a temporary bound to it lives as long as it (a local)
            let sv = cg_extend;
            cg_extend = local;
            conv = conv_arg(e, t, loc);
            cg_extend = sv;
        }
    } else if is_record(t) && !is_opaque(t) && !is_extern {
        let r = rec_of(t);
        conv = 0;
        has_dtor = class_dtor(r) >= 0;
        if init != 0 && nodes[init].kind as i64 == N_CTOR && nodes[init].op == 2 && unqual(nodes[init].ty) == unqual(t) {
            // T x = T{args} of an aggregate: aggregate initialization of x
            if c_initializable(t) {
                let ib = node_v(N_INITBRACE, 0, unqual(t), 0, 0, nodes[init].c as i64, loc, nodes[init].v);
                let bi = brace_init(t, ib, loc);
                conv = if bi != 0 { bi } else { opaque_node(loc) };
            } else {
                let a = agg_init(n_var(s, loc), nodes[init].v, nodes[init].c as i64, loc);
                cst = if a == 0 { mark_bad_stmt(loc) } else { n_expr_stmt(a) };
            }
        } else if init != 0 && nodes[init].kind as i64 == N_INITBRACE && c_initializable(t) {
            // an aggregate: C's initializer
            let bi = brace_init(t, init, loc);
            conv = if bi != 0 { bi } else { opaque_node(loc) };
        } else if init != 0 && nodes[init].kind as i64 == N_INITBRACE && nodes[init].op == 0 && is_aggregate_class(r) && !is_array(t) {
            // an aggregate whose members need code
            let a = agg_init(n_var(s, loc), nodes[init].v, nodes[init].c as i64, loc);
            cst = if a == 0 { mark_bad_stmt(loc) } else { n_expr_stmt(a) };
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
    } else if is_array(t) && is_record(base_elem_t(t)) && !is_opaque(base_elem_t(t)) && !is_extern {
        let br = rec_of(base_elem_t(t));
        has_dtor = class_dtor(br) >= 0;
        conv = 0;
        if init != 0 && nodes[init].kind as i64 == N_INITBRACE && c_initializable(t) {
            let bi = brace_init(t, init, loc);
            conv = if bi != 0 { bi } else { opaque_node(loc) };
            if bi != 0 && types[t >> 4].n < 0 { syms[s].ty = with_q(nodes[bi].ty, quals(t)); }
        } else if init != 0 && nodes[init].kind as i64 == N_INITBRACE && kind_of(t) == TY_ARRAY {
            // each element from its initializer, the rest by default
            let n = nodes[init].c as i64;
            if types[t >> 4].n < 0 { syms[s].ty = with_q(mk_array(tbase(t), n), quals(t)); }
            let at = syms[s].ty;
            let et = tbase(at);
            if is_array(et) || n > types[at >> 4].n { conv = opaque_node(loc); }
            else {
                let mark = nscratch.len;
                for i in types[at >> 4].n {
                    let el = node(N_INDEX, 0, et, icast(n_var(s, loc), CK_ARRAY2PTR, mk_ptr(et)) as i64, int_node(i, t_long, loc) as i64, 0, loc);
                    nodes[el].flags = NF_LVALUE;
                    let am = nscratch.len;
                    if i < n {
                        let x = nlist[nodes[init].v + i];
                        let xk = nodes[x].kind as i64;
                        if xk == N_CTOR || xk == N_INITBRACE { for j in nodes[x].c as i64 { nscratch.push(nlist[nodes[x].v + j]); } }
                        else { nscratch.push(x); }
                    }
                    var st = construct_at(el, am, loc);
                    if st == 0 { st = mark_bad_stmt(loc); }
                    nscratch.push(st);
                }
                cst = n_block(mark, loc);
            }
        } else if init != 0 {
            conv = opaque_node(loc);
        } else if needs_default_init(br) {
            cst = arr_loop(n_var(s, loc), false, loc);
        }
    } else if init != 0 && nodes[init].kind as i64 == N_INITBRACE {
        let bi = brace_init(t, init, loc);
        conv = if bi != 0 { bi } else { opaque_node(loc) };
        if bi != 0 && is_array(t) && types[t >> 4].n < 0 { syms[s].ty = with_q(nodes[bi].ty, quals(t)); }
    } else if init != 0 && kind_of(t) == TY_MEMPTR && !is_opq(init) {
        conv = conv_value(init, unqual(t), loc);
    } else if init != 0 && conv != 0 && is_pointer(t) && !is_opq(init) && !is_record(nodes[init].ty) {
        let c = cg_ptr_conv(rv(init), unqual(t), loc);
        if c != 0 { conv = c; }
    } else if init != 0 && conv != 0 && !is_opq(init) && is_record(nodes[init].ty) && cish(t) {
        // a conversion function
        conv = conv_value(init, unqual(t), loc);
    }
    // the dynamic initialization of a namespace-scope (or static local) variable
    var dyn: u32 = 0;
    if !local && conv != 0 && !is_opq(conv) {
        nc_node = 0;
        if !const_init(conv) {
            let lhs = node(N_DECLREF, 0, lower_ty(t), s, 0, 0, loc);
            nodes[lhs].flags = NF_LVALUE;
            dyn = n_expr_stmt(node(N_ASSIGN, 0, unqual(lower_ty(t)), lhs as i64, conv as i64, 0, loc));
            if !static_local && tls { tls_push(s, dyn, false, loc); }
            else if !static_local { gi_push(dyn, prio); }
            conv = 0;
        }
    }
    if !is_extern && (fs || init != 0) { syms[s].flags = syms[s].flags | SF_DEFINED; }
    // clang: constant data with relocations in .data.rel.ro (cx_comdats)
    if !local && !is_extern && quals(base_elem_q(t)) & Q_CONST != 0 && dyn == 0 && cst == 0 {
        cxl_grow();
        cxl[s].flags = cxl[s].flags | (CXL_RELRO as! u8);
    }
    nscratch.push(node(N_DECL, 0, syms[s].ty, s, conv as i64, dloc as i64, loc));
    if static_local { note_static_local(s); }
    if static_local && tls && (dyn != 0 || cst != 0 || has_dtor) {
        // a thread_local: once per thread, no locking:
        // if (guard == 0) { init; __cxa_thread_atexit; guard = 1; }
        let g = csym(SK_VAR, intern("__guard"), t_char, loc);
        syms[g].sc = SC_STATIC as! u8;
        syms[g].scope = syms[s].scope;
        syms[g].flags = syms[g].flags | SF_THREAD;
        guard_of.insert(s as u64, g as! u32);
        nscratch.push(node(N_DECL, 0, t_char, g, 0, loc as i64, loc));
        let mark = nscratch.len;
        if dyn != 0 { nscratch.push(dyn); }
        if cst != 0 { nscratch.push(cst); }
        if has_dtor { nscratch.push(thread_atexit_stmt(s, loc)); }
        nscratch.push(n_expr_stmt(node(N_ASSIGN, 0, t_char, n_var(g, loc) as i64, int_node(1, t_char, loc) as i64, 0, loc)));
        let init = n_block(mark, loc);
        let test = node(N_BINARY, B_EQ, t_int, icast(rv(n_var(g, loc)), CK_INTEGRAL, t_int) as i64, int_node(0, t_int, loc) as i64, 0, loc);
        nscratch.push(node(N_IF, 0, 0, test as i64, init as i64, 0, loc));
        return;
    }
    if static_local && (dyn != 0 || cst != 0 || has_dtor) {
        // once (Itanium 3.3.2): if (guard byte == 0 && __cxa_guard_acquire(&guard)) {
        //   [EH: __cxa_guard_abort(&guard)] init; atexit; __cxa_guard_release(&guard); }
        let g = csym(SK_VAR, intern("__guard"), t_long, loc);
        syms[g].sc = SC_STATIC as! u8;
        syms[g].scope = syms[s].scope;
        guard_of.insert(s as u64, g as! u32);
        nscratch.push(node(N_DECL, 0, t_long, g, 0, loc as i64, loc));
        let mark = nscratch.len;
        let im = nscratch.len;
        let am = nscratch.len;
        nscratch.push(guard_addr(g, loc));
        let abort = n_expr_stmt(n_call(rt_fn("__cxa_guard_abort", t_void, 1, t_voidptr, 0, 0, true, false), am, loc));
        nscratch.push(node(N_XPUSH, XP_STMT | XP_EHONLY, 0, abort as i64, 0, 0, loc));
        if dyn != 0 { nscratch.push(dyn); }
        if cst != 0 { nscratch.push(cst); }
        nscratch.push(n_block(im, loc));
        if has_dtor { nscratch.push(atexit_stmt(s, loc)); }
        let rm = nscratch.len;
        nscratch.push(guard_addr(g, loc));
        nscratch.push(n_expr_stmt(n_call(rt_fn("__cxa_guard_release", t_void, 1, t_voidptr, 0, 0, true, false), rm, loc)));
        let init = n_block(mark, loc);
        let qm = nscratch.len;
        nscratch.push(guard_addr(g, loc));
        let acq = n_call(rt_fn("__cxa_guard_acquire", t_int, 1, t_voidptr, 0, 0, true, false), qm, loc);
        let acq_if = node(N_IF, 0, 0, icast(acq, CK_INT2BOOL, t_bool) as i64, init as i64, 0, loc);
        let byte = n_deref(node(N_ICAST, CK_BITCAST, mk_ptr(t_char), n_addr(n_var(g, loc), loc) as i64, 0, 0, loc), loc);
        let test = node(N_BINARY, B_EQ, t_int, icast(rv(byte), CK_INTEGRAL, t_int) as i64, int_node(0, t_int, loc) as i64, 0, loc);
        nscratch.push(node(N_IF, 0, 0, test as i64, acq_if as i64, 0, loc));
        return;
    }
    if ctx == DC_COND && cst != 0 { nscratch.push(mark_bad_stmt(loc)); return; }
    if local {
        if cst != 0 { nscratch.push(cst); }
        if has_dtor { push_dtor_cleanup(s, loc); }
    } else if !static_local && !is_extern && tls {
        if cst != 0 || has_dtor { tls_push(s, cst, has_dtor, loc); }
    } else if !static_local && !is_extern {
        if cst != 0 { gi_push(cst, prio); }
        if has_dtor { gi_push(atexit_stmt(s, loc), prio); }
    }
}

fn guard_addr(g: i64, loc: u32) -> u32 { node(N_ICAST, CK_BITCAST, t_voidptr, n_addr(n_var(g, loc), loc) as i64, 0, 0, loc) }

// The elements of the array at lvalue arr (of class type, or arrays of
// them) constructed by default (dtor: destroyed, in reverse order): a for
// loop over them as one array, or 0 when D1 cannot.
fn arr_loop(arr: u32, dtor: bool, loc: u32) -> u32 {
    let t = nodes[arr].ty;
    if kind_of(t) != TY_ARRAY { return 0; }
    let et = base_elem_t(t);
    var total: i64 = 1;
    var x = t;
    while kind_of(x) == TY_ARRAY { total = total * types[x >> 4].n; x = tbase(x); }
    if total <= 0 { return n_null(loc); }
    let i = csym(SK_VAR, intern("__i"), t_long, loc);
    syms[i].scope = 1;
    let base = n_ptrcast(n_addr(arr, loc), mk_ptr(et), loc);
    let el = node(N_INDEX, 0, et, base as i64, rv(n_var(i, loc)) as i64, 0, loc);
    nodes[el].flags = NF_LVALUE;
    var body: u32 = 0;
    if dtor { body = destroy_stmt(el, loc); }
    else {
        let mark = nscratch.len;
        body = construct_at(el, mark, loc);
    }
    if body == 0 { return 0; }
    var init: u32 = 0;
    var cond: u32 = 0;
    var inc: u32 = 0;
    if dtor {
        // for (long i = total; i-- > 0;)
        init = node(N_DECL, 0, t_long, i, int_node(total, t_long, loc) as i64, loc as i64, loc);
        let dec = node(N_UNARY, U_POSTDEC, t_long, n_var(i, loc) as i64, 0, 0, loc);
        cond = node(N_BINARY, B_GT, t_int, dec as i64, int_node(0, t_long, loc) as i64, 0, loc);
    } else {
        // for (long i = 0; i < total; ++i)
        init = node(N_DECL, 0, t_long, i, int_node(0, t_long, loc) as i64, loc as i64, loc);
        cond = node(N_BINARY, B_LT, t_int, rv(n_var(i, loc)) as i64, int_node(total, t_long, loc) as i64, 0, loc);
        inc = node(N_UNARY, U_PREINC, t_long, n_var(i, loc) as i64, 0, 0, loc);
    }
    return node_v(N_FOR, 0, 0, init as i64, cond as i64, inc as i64, loc, body as i64);
}

// The destroying function of an array type (a cleanup and __cxa_atexit
// target): void f(T (*p)[N]) { destroy (*p)[N-1] ... (*p)[0] }.
var arr_dtors = dictionary<u64, u32> {};
fn arr_dtor_fn(t: u32, loc: u32) -> i64 {
    let g = arr_dtors.get(unqual(t) as u64);
    if g { return g as i64; }
    let pt = mk_ptr(unqual(t));
    let ft = fn_type1(t_void, pt);
    let f = csym(SK_FUNC, intern("__array_dtor"), ft, loc);
    syms[f].sc = SC_STATIC as! u8;
    syms[f].flags = SF_DEFINED;
    cxs[f].flags = CF_IMPLICIT;
    label_numbered(f, "__goosecc_array_dtor_");
    let p = csym(SK_VAR, intern("p"), pt, loc);
    syms[p].flags = SF_PARAM;
    syms[p].scope = 1;
    let lp = arr_loop(n_deref(rv(n_var(p, loc)), loc), true, loc);
    let mark = nscratch.len;
    nscratch.push(if lp == 0 { mark_bad_stmt(loc) } else { lp });
    let body = n_block(mark, loc);
    let pm = nscratch.len;
    nscratch.push(p as! u32);
    let ps = commit_list(pm);
    let n = node_v(N_FUNCDEF, 0, ft, f, body as i64, 1, loc, ps);
    syms[f].def = n as! i32;
    cg_extra.push(n);
    arr_dtors.insert(unqual(t) as u64, f as! u32);
    return f;
}

// The destructor of a local class object (or array of them) as a cleanup
// for the rest of its block (after its construction).
fn push_dtor_cleanup(s: i64, loc: u32) {
    let t = syms[s].ty;
    var f: i64 = -1;
    if is_array(t) {
        let et = base_elem_t(t);
        if !is_record(et) || is_opaque(et) || class_dtor(rec_of(et)) < 0 { return; }
        f = arr_dtor_fn(t, syms[s].loc);
    } else {
        if !is_record(t) || is_opaque(t) { return; }
        let d = class_dtor(rec_of(t));
        if d < 0 { return; }
        f = complete_sym(d);
    }
    nscratch.push(node(N_XPUSH, XP_CALL, 0, s, 0, f, loc));
}

fn note_dtor_cleanup(s: i64) {
    let t = syms[s].ty;
    if is_array(t) {
        let et = base_elem_t(t);
        if !is_record(et) || is_opaque(et) || class_dtor(rec_of(et)) < 0 { return; }
        let f = arr_dtor_fn(t, syms[s].loc);
        let ai = get_attr(s);
        sym_attrs[ai].cleanup = f as! i32;
        return;
    }
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
    let d = if is_array(syms[s].ty) { arr_dtor_fn(syms[s].ty, loc) } else { complete_sym(class_dtor(rec_of(syms[s].ty))) };
    if atexit_fn < 0 {
        let vfp = mk_ptr(fn_type1(t_void, t_voidptr));
        fn_scratch.clear();
        fn_scratch.push(vfp);
        fn_scratch.push(t_voidptr);
        fn_scratch.push(t_voidptr);
        let ft = qt(mk_type(TY_FUNC, 0, t_int, 0, 0, 0) as i64, 0);
        atexit_fn = csym(SK_FUNC, intern("__cxa_atexit"), ft, loc);
        cxs[atexit_fn].flags = CF_EXTERN_C;
    }
    let dh = dso_handle_sym(loc);
    let mark = nscratch.len;
    let vfp = mk_ptr(fn_type1(t_void, t_voidptr));
    nscratch.push(node(N_ICAST, CK_BITCAST, vfp, icast(n_ref_fn(d, loc), CK_FUNC2PTR, mk_ptr(abi_type(d))) as i64, 0, 0, loc));
    nscratch.push(node(N_ICAST, CK_BITCAST, t_voidptr, n_addr(n_var(s, loc), loc) as i64, 0, 0, loc));
    nscratch.push(node(N_ICAST, CK_BITCAST, t_voidptr, n_addr(n_var(dh, loc), loc) as i64, 0, 0, loc));
    return n_expr_stmt(n_call(atexit_fn, mark, loc));
}

// __dso_handle (external, hidden).
fn dso_handle_sym(loc: u32) -> i64 {
    if dso_handle < 0 {
        dso_handle = csym(SK_VAR, intern("__dso_handle"), t_char, loc);
        syms[dso_handle].flags = SF_FILESCOPE;
        syms[dso_handle].sc = SC_EXTERN as! u8;
        cxs[dso_handle].flags = CF_EXTERN_C;
        let ai = get_attr(dso_handle);
        sym_attrs[ai].vis = 1;
    }
    return dso_handle;
}

fn fn_type1(ret: u32, p: u32) -> u32 {
    fn_scratch.clear();
    fn_scratch.push(p);
    return qt(mk_type(TY_FUNC, 0, ret, 0, 0, 0) as i64, 0);
}

// `return e;` in a function returning rt (a reference or a class).
recursive fn cg_return(x: u32, rt: u32, loc: u32) -> u32 {
    if is_ref(rt) { return conv_arg(x, rt, loc); }
    if is_record(rt) && pass_indirect(rt) {
        // constructed in the return slot (*__ret), which is returned
        if cg_ret < 0 || (is_opq(x) && nodes[x].kind as i64 != N_INITBRACE) { return opaque_node(loc); }
        let ct = unqual(rt);
        let slot = n_deref(rv(n_var(cg_ret, loc)), loc);
        nodes[slot].ty = ct;
        let v = local_of(x, ct);
        if v >= 0 {
            // a local variable: moved, unless it is the NRVO variable (cg_finish)
            let xv = n_var(v, loc);
            nodes[xv].flags = nodes[xv].flags | NF_XVALUE;
            let init = init_into(slot, class_rv(xv, ct, loc), loc);
            if init == 0 { return opaque_node(loc); }
            if syms[v].flags & SF_PARAM != 0 {
                return node(N_BINARY, B_COMMA, mk_ptr(ct), init as i64, rv(n_var(cg_ret, loc)) as i64, 0, loc);
            }
            return node(N_XNRET, 0, mk_ptr(ct), v, init as i64, cg_ret, loc);
        }
        var src = x;
        if !(is_class_prv(x) && unqual(nodes[x].ty) == ct) { src = class_rv(x, ct, loc); }
        if is_opq(src) { return src; }
        let init = init_into(slot, src, loc);
        if init == 0 { return opaque_node(loc); }
        return node(N_BINARY, B_COMMA, mk_ptr(ct), init as i64, rv(n_var(cg_ret, loc)) as i64, 0, loc);
    }
    if is_record(rt) { return conv_value(x, unqual(rt), loc); }
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
recursive fn cg_new(t: u32, count: u32, init: u32, has_init: bool, loc: u32, place: u32, global: bool) -> u32 {
    return cg_new2(t, count, init, has_init, loc, place, global);
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
recursive fn cg_delete(p0: u32, arr: bool, loc: u32, global: bool) -> u32 {
    return cg_delete2(p0, arr, loc, global);
}

// ---------------------------------------------------------------------------
// Vtables and type information (Itanium C++ ABI 2.5, 2.9.5).

var vtables: u32[>..] = [];              // records whose vtable was asked for
var vtable_syms = dictionary<u64, u32> {};
// The vtable variable of class r (its linkage and initializer are decided
// in cg_finish, when the key function's definition is known).
fn vtable_sym(r: i64) -> i64 {
    let g = vtable_syms.get(r as u64);
    if g { return g as i64; }
    let grp = vt_class(r);
    if !group_ok(grp) { return -1; }
    let vt = mk_array(with_q(t_voidptr, Q_CONST), vgroups[grp].nc as i64);
    let s = csym(SK_VAR, intern("__vtable"), vt, records[r].loc);
    syms[s].flags = SF_FILESCOPE | SF_DEFINED;
    cxs[s].flags = CF_IMPLICIT;
    if !mangle_special("_ZTV", records[r].ty << 4) { return -1; }
    set_label(s, mg);
    vtable_syms.insert(r as u64, s as! u32);
    vtables.push(r as! u32);
    return s;
}

var typeinfos = dictionary<u64, u32> {};
var ti_names = dictionary<u64, u32> {};
var ti_classes: u32[>..] = [];
var ext_syms = dictionary<u64, u32> {};

// An external variable (array of void *) named `name` (the type_info
// classes' vtables, the runtime's typeinfo of fundamental types).
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

// The kind of class r's type_info: 0 __class_type_info, 1 __si_class_type_info
// (one public non-virtual base at offset 0), 2 __vmi_class_type_info.
fn ti_kind(r: i64) -> i64 {
    let cr = crecs[r];
    if cr.nbases == 0 { return 0; }
    let b = cbases[cr.bases];
    if cr.nbases == 1 && b.flags & BF_VIRTUAL == 0 && b.offset == 0 && b.access as i64 == 0 { return 1; }
    return 2;
}

// The type_info object of class r (_ZTI), with its name (_ZTS): the
// symbols now, their linkage and contents in cg_finish (finish_typeinfo).
fn typeinfo_sym(r: i64) -> i64 {
    let g = typeinfos.get(r as u64);
    if g { return g as i64; }
    let cls = records[r].ty << 4;
    let loc = records[r].loc;
    if !mangle_special("", cls) { return -1; }
    let name_len = mg.len;
    let nt = mk_array(t_char | (Q_CONST as! u32), name_len + 1);
    let ns = csym(SK_VAR, intern("__typeinfo_name"), nt, loc);
    syms[ns].flags = SF_FILESCOPE | SF_DEFINED;
    cxs[ns].flags = CF_IMPLICIT;
    mangle_special("_ZTS", cls);
    set_label(ns, mg);
    let k = ti_kind(r);
    let n = if k == 0 { 2 } else if k == 1 { 3 } else { 3 + 2 * (crecs[r].nbases as i64) };
    let tt = mk_array(with_q(t_voidptr, Q_CONST), n);
    let s = csym(SK_VAR, intern("__typeinfo"), tt, loc);
    syms[s].flags = SF_FILESCOPE | SF_DEFINED;
    cxs[s].flags = CF_IMPLICIT;
    mangle_special("_ZTI", cls);
    set_label(s, mg);
    typeinfos.insert(r as u64, s as! u32);
    ti_names.insert(r as u64, ns as! u32);
    ti_classes.push(r as! u32);
    return s;
}

// The linkage and contents of class r's type_info and name.
fn finish_typeinfo(r: i64) {
    var s: i64 = -1;
    var ns: i64 = -1;
    let g1 = typeinfos.get(r as u64);
    if g1 { s = g1 as i64; }
    let g2 = ti_names.get(r as u64);
    if g2 { ns = g2 as i64; }
    if s < 0 || ns < 0 { return; }
    let cls = records[r].ty << 4;
    let loc = records[r].loc;
    let dynamic = crecs[r].flags & CR_DYNAMIC != 0;
    var link = vt_kind(r);
    if !dynamic && link != 0 { link = 1; }
    set_data_link(ns, link, false);
    set_data_link(s, link, true);
    if link == 3 { return; }
    // the name: the mangled type
    mangle_special("", cls);
    let name_len = mg.len;
    let soff = strbytes.len;
    strbytes.append(mg);
    strbytes.push(0);
    let si = strs.len;
    strs.push(StrLit { start: soff as! u32, len: (name_len + 1) as! u32, elem: t_char });
    let sn = node(N_STRING, 0, syms[ns].ty, si, 0, 0, loc);
    nodes[sn].flags = NF_LVALUE | NF_STRINIT;
    cg_extra.push(node(N_DECL, 0, syms[ns].ty, ns, sn as i64, loc as i64, loc));
    let cr = crecs[r];
    let kind = ti_kind(r);
    let mark = nscratch.len;
    let vt = ext_array(if kind == 0 { "_ZTVN10__cxxabiv117__class_type_infoE" } else if kind == 1 { "_ZTVN10__cxxabiv120__si_class_type_infoE" }
                       else { "_ZTVN10__cxxabiv121__vmi_class_type_infoE" });
    nscratch.push(void_addr_of(vt, 2, loc));
    nscratch.push(void_addr_of(ns, 0, loc));
    if kind == 1 {
        let bt = typeinfo_sym(rec_of(cbases[cr.bases].ty));
        nscratch.push(void_addr_of(bt, 0, loc));
    } else if kind == 2 {
        // flags (u32: non-diamond repeat 1, diamond 2), base count (u32), then
        // per base: type_info *, offset << 8 | public 2 | virtual 1
        nscratch.push(int_as_ptr(((cr.nbases as i64) << 32) | vmi_flags(r), loc));
        for i in cr.nbases {
            let b = cbases[cr.bases + i];
            let bt = typeinfo_sym(rec_of(b.ty));
            nscratch.push(void_addr_of(bt, 0, loc));
            var off = b.offset;
            if b.flags & BF_VIRTUAL != 0 { off = class_vbo(r, rec_of(b.ty)); }
            nscratch.push(int_as_ptr((off << 8) | (if b.access as i64 == 0 { 2 } else { 0 }) | (if b.flags & BF_VIRTUAL != 0 { 1 } else { 0 }), loc));
        }
    }
    let n = nscratch.len - mark;
    let start = commit_list(mark);
    let il = node_v(N_INITLIST, 0, syms[s].ty, 0, 0, n, loc, start);
    cg_extra.push(node(N_DECL, 0, syms[s].ty, s, il as i64, loc as i64, loc));
}

// The vmi flags of class r (clang's ComputeVMIClassTypeInfoFlags): 1 when
// a base class is repeated other than as one virtual base (non-diamond
// repeat), 2 when a virtual base is reached more than once (diamond).
fn vmi_flags(r: i64) -> i64 {
    let mark = rec_scratch.len;
    var f: i64 = 0;
    let cr = crecs[r];
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if is_record(b.ty) { f = f | vmi_flags_base(rec_of(b.ty), b.flags & BF_VIRTUAL != 0, mark); }
    }
    rec_scratch.resize(mark);
    return f;
}
var rec_scratch: u32[>..<] = [];

fn vmi_seen(br: i64, tag: u32, mark: i64) -> bool {
    for j in mark..rec_scratch.len { if rec_scratch[j] == ((br as! u32) | tag) { return true; } }
    return false;
}

recursive fn vmi_flags_base(br: i64, virt: bool, mark: i64) -> i64 {
    var f: i64 = 0;
    let V: u32 = 0x80000000;
    if virt {
        if vmi_seen(br, V, mark) { f = f | 2; }
        else {
            rec_scratch.push((br as! u32) | V);
            if vmi_seen(br, 0, mark) { f = f | 1; }
        }
    } else {
        if vmi_seen(br, 0, mark) { f = f | 1; }
        else {
            rec_scratch.push(br as! u32);
            if vmi_seen(br, V, mark) { f = f | 1; }
        }
    }
    let cr = crecs[br];
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if is_record(b.ty) { f = f | vmi_flags_base(rec_of(b.ty), b.flags & BF_VIRTUAL != 0, mark); }
    }
    return f;
}

// The initializer of the vtable of class r, with its VTT and construction
// vtables when it has virtual bases.
fn build_vtable(r: i64) {
    let s = vtable_sym(r);
    let loc = records[r].loc;
    set_class_data_link(s, r, true, true);
    if syms[s].sc as i64 == SC_EXTERN {
        // the VTT lives with the vtable
        if has_vb(r) { set_class_data_link(vtt_sym(r), r, true, true); }
        return;
    }
    let g = vt_class(r);
    let il = group_init(g, syms[s].ty, loc);
    cg_extra.push(node(N_DECL, 0, syms[s].ty, s, il as i64, loc as i64, loc));
    if has_vb(r) {
        build_vtt(r, s, loc);
        // emitted with the vtable
        let tv = vtt_sym(r);
        note_cx_use(s, tv);
        reach_var(tv);
    }
}

// Is destructor f (a variant) virtual?
fn dtor_is_virtual(f: i64) -> bool {
    if cxs[f].flags & CF_DTOR_DELETING != 0 { return true; }
    var b = f;
    let g = complete_base.get(f as u64);
    if g { b = g as i64; }
    let cr = rec_of(scope_class_type(cxs[b].dscope as i64));
    if cr >= crecs.len || crecs[cr].flags & CR_DYNAMIC == 0 { return false; }
    if !group_ok(vt_class(cr)) { return false; }
    return vt_method_index(b, false) >= 0;
}

// The components of group g as an initializer of type t.
fn group_init(g: i64, t: u32, loc: u32) -> u32 {
    let G = vgroups[g];
    let mark = nscratch.len;
    for i in G.c0..G.c0 + G.nc {
        let c = vg_comps[i];
        let k = c.kind as i64;
        if k == VC_VCALL || k == VC_VBASE || k == VC_TOP {
            if c.val == 0 { nscratch.push(node(N_ZEROINIT, 0, t_voidptr, 0, 0, 0, loc)); } else { nscratch.push(int_as_ptr(c.val, loc)); }
            continue;
        }
        if k == VC_RTTI {
            let ti = if opt_rtti { typeinfo_sym(c.fsym) } else { -1 };
            if ti < 0 { nscratch.push(int_as_ptr(0, loc)); } else { nscratch.push(void_addr_of(ti, 0, loc)); }
            continue;
        }
        if k == VC_UNUSED { nscratch.push(node(N_ZEROINIT, 0, t_voidptr, 0, 0, 0, loc)); continue; }
        var f = c.fsym;
        if cxs[f].flags & CF_PURE != 0 || cxs[f].flags & CF_DELETED != 0 {
            let nm = if cxs[f].flags & CF_PURE != 0 { "__cxa_pure_virtual" } else { "__cxa_deleted_virtual" };
            f = rt_fn(nm, t_void, 0, 0, 0, 0, false, false);
        } else {
            var mangled = f;
            if k == VC_CDTOR { f = complete_sym(f); }
            if k == VC_DDTOR { f = deleting_dtor(method_class(f)); mangled = f; }
            if c.thunk >= 0 {
                let th = vg_cthunks[g_cth[g] as i64 + c.thunk as i64];
                if th.this_nv != 0 || th.this_vc != 0 || th.ret_nv != 0 || th.ret_vb != 0 {
                    let ts = thunk_sym(f, mangled, th, loc);
                    if ts >= 0 { f = ts; }
                }
            }
        }
        let fr = icast(n_ref_fn(f, loc), CK_FUNC2PTR, mk_ptr(abi_type(f)));
        nscratch.push(node(N_ICAST, CK_BITCAST, t_voidptr, fr as i64, 0, 0, loc));
    }
    let n = nscratch.len - mark;
    let start = commit_list(mark);
    return node_v(N_INITLIST, 0, t, 0, 0, n, loc, start);
}

// The VTT of class r (_ZTT) and the construction vtables it points into (_ZTC).
var ctor_vts = dictionary<u64, u32> {};     // construction group -> its variable
fn build_vtt(r: i64, vt: i64, loc: u32) {
    let vi = vtt_of(r);
    let v = vtt_infos[vi];
    let s = vtt_sym(r);
    let tt = syms[s].ty;
    set_class_data_link(s, r, true, true);
    let mark = nscratch.len;
    let cg = vt_class(r);
    for i in v.e0..v.e0 + v.ne {
        let E = vtt_ents[i];
        var gs = vt;
        if E.grp != cg {
            let gg = ctor_vts.get(E.grp as u64);
            if gg { gs = gg as i64; }
            else {
                gs = ctor_vtable(r, E.grp, loc);
                ctor_vts.insert(E.grp as u64, gs as! u32);
            }
        }
        let ap = vt_address_point(E.grp, E.cls as i64, E.off);
        nscratch.push(void_addr_of(gs, if ap < 0 { 0 } else { ap }, loc));
    }
    let n = nscratch.len - mark;
    let start = commit_list(mark);
    let il = node_v(N_INITLIST, 0, tt, 0, 0, n, loc, start);
    cg_extra.push(node(N_DECL, 0, tt, s, il as i64, loc as i64, loc));
}
var vtt_syms = dictionary<u64, u32> {};

// The VTT variable of class r (it is emitted with the vtable).
fn vtt_sym(r: i64) -> i64 {
    let g = vtt_syms.get(r as u64);
    if g { return g as i64; }
    let vi = vtt_of(r);
    let v = vtt_infos[vi];
    let tt = mk_array(with_q(t_voidptr, Q_CONST), v.ne as i64);
    let s = csym(SK_VAR, intern("__vtt"), tt, records[r].loc);
    syms[s].flags = SF_FILESCOPE | SF_DEFINED;
    cxs[s].flags = CF_IMPLICIT;
    mangle_special("_ZTT", records[r].ty << 4);
    set_label(s, mg);
    vtt_syms.insert(r as u64, s as! u32);
    vtable_sym(r);
    return s;
}

// The construction vtable of group g (md-in-r): _ZTC <r> <offset> _ <md>.
fn ctor_vtable(r: i64, g: i64, loc: u32) -> i64 {
    let G = vgroups[g];
    let t = mk_array(with_q(t_voidptr, Q_CONST), G.nc as i64);
    let s = csym(SK_VAR, intern("__ctor_vtable"), t, loc);
    syms[s].flags = SF_FILESCOPE | SF_DEFINED;
    cxs[s].flags = CF_IMPLICIT;
    var nm: u8[>..] = [];
    mangle_special("_ZTC", records[r].ty << 4);
    nm.append(mg);
    format(nm, G.md_off, "_");
    mangle_special("", records[G.md].ty << 4);
    nm.append(mg);
    set_label(s, nm);
    set_class_data_link(s, r, true, true);
    let il = group_init(g, t, loc);
    cg_extra.push(node(N_DECL, 0, t, s, il as i64, loc as i64, loc));
    return s;
}

// ---------------------------------------------------------------------------
// Thunks: a function adjusting `this` (and the result) around a call of
// the overrider, named _ZTh / _ZTv / _ZTc, with the overrider's linkage,
// defined where the overrider is.

var thunk_keys: VtThunk[>..] = [];
var thunk_syms: u32[>..] = [];
var thunk_targets: u32[>..] = [];

fn thunk_sym(target: i64, mangled: i64, t: VtThunk, loc: u32) -> i64 {
    for k, i in thunk_keys {
        if thunk_targets[i] as i64 == target && k.this_nv == t.this_nv && k.this_vc == t.this_vc && k.ret_nv == t.ret_nv && k.ret_vb == t.ret_vb {
            return thunk_syms[i] as i64;
        }
    }
    if types[syms[target].ty >> 4].flags & TF_VARIADIC != 0 { return -1; }
    if !mangle_thunk(mangled, t) { return -1; }
    let ts = csym(SK_FUNC, syms[target].name, syms[target].ty, loc);
    cxs[ts] = cxs[target];
    cxs[ts].nnext = -1;
    cxs[ts].flags = cxs[ts].flags & ~(CF_CTOR | CF_DTOR | CF_DTOR_DELETING);
    abi_types.insert(ts as u64, abi_type(target));
    set_label(ts, thunk_name);
    thunk_keys.push(t);
    thunk_syms.push(ts as! u32);
    thunk_targets.push(target as! u32);
    // the linkage of the target
    cxl_grow();
    var b = target;
    let cb = complete_base.get(target as u64);
    if cb { b = cb as i64; }
    let inline = fn_inline(b) || cxs[b].flags & (CF_IMPLICIT | CF_DTOR_DELETING) != 0;
    let defined_here = syms[b].def >= 0 || cxs[b].flags & (CF_IMPLICIT | CF_DTOR_DELETING) != 0 || syms[resolve(b)].def >= 0;
    if !defined_here {
        syms[ts].sc = SC_EXTERN as! u8;
        syms[ts].flags = SF_FILESCOPE;
        return ts;
    }
    syms[ts].sc = 0;
    syms[ts].flags = SF_FILESCOPE | SF_DEFINED;
    if inline { set_link(ts, LK_LINKONCE, CXL_COMDAT); }
    if syms[b].sc as i64 == SC_STATIC || (cxs[b].dscope > 0 && in_anon_ns(cxs[b].dscope as i64)) { syms[ts].sc = SC_STATIC as! u8; }
    thunk_body(ts, target, t, loc);
    return ts;
}

// The body of thunk ts calling target with adjustment t.
fn thunk_body(ts: i64, target: i64, t: VtThunk, loc: u32) {
    let ft = types[syms[target].ty >> 4];
    let cls = scope_class_type(cxs[target].dscope as i64);
    var q: i64 = 0;
    if (ft.flags as i64) & TF_MCONST != 0 { q = Q_CONST; }
    let th = make_this(ts, mk_ptr(with_q(cls, q)), loc);
    var ret: i64 = -1;
    if pass_indirect(ft.base) { ret = make_ret(ts, ft.base, loc); }
    let pm = nscratch.len;
    for i in ft.n {
        let p = csym(SK_VAR, 0, tparams[ft.extra + i], loc);
        syms[p].flags = SF_PARAM;
        syms[p].scope = 1;
        nscratch.push(p as! u32);
    }
    let np = nscratch.len - pm;
    let ps = commit_list(pm);
    // this' = this + nv; this'' = this' + *(this' vtable + vc)
    let cp = node(N_ICAST, CK_BITCAST, mk_ptr(t_char), rv(n_var(th, loc)) as i64, 0, 0, loc);
    var adj = cp;
    if t.this_nv != 0 { adj = node(N_BINARY, B_PTRADD, mk_ptr(t_char), adj as i64, int_node(t.this_nv, t_long, loc) as i64, 0, loc); }
    let bm = nscratch.len;
    let ap = csym(SK_VAR, intern("__this_adj"), mk_ptr(t_char), loc);
    syms[ap].scope = 1;
    nscratch.push(node(N_DECL, 0, mk_ptr(t_char), ap, adj as i64, loc as i64, loc));
    if t.this_vc != 0 {
        let vp = rv(n_deref(node(N_ICAST, CK_BITCAST, mk_ptr(mk_ptr(t_char)), rv(n_var(ap, loc)) as i64, 0, 0, loc), loc));
        let e = node(N_BINARY, B_PTRADD, mk_ptr(t_char), vp as i64, int_node(t.this_vc, t_long, loc) as i64, 0, loc);
        let off = rv(n_deref(node(N_ICAST, CK_BITCAST, mk_ptr(t_long), e as i64, 0, 0, loc), loc));
        let sum = node(N_BINARY, B_PTRADD, mk_ptr(t_char), rv(n_var(ap, loc)) as i64, off as i64, 0, loc);
        nscratch.push(n_expr_stmt(node(N_ASSIGN, 0, mk_ptr(t_char), n_var(ap, loc) as i64, sum as i64, 0, loc)));
    }
    // the call: [return slot] this' [parameters as they are]
    let am = nscratch.len;
    if ret >= 0 { nscratch.push(rv(n_var(ret, loc))); }
    nscratch.push(node(N_ICAST, CK_BITCAST, mk_ptr(with_q(cls, q)), rv(n_var(ap, loc)) as i64, 0, 0, loc));
    for i in np {
        let p = nlist[ps + i] as i64;
        let pt = syms[p].ty;
        let lt = if pass_indirect(pt) { mk_ptr(unqual(pt)) } else { lower_ty(pt) };
        let d = node(N_DECLREF, 0, lt, p, 0, 0, loc);
        nodes[d].flags = NF_LVALUE;
        nscratch.push(rv(d));
    }
    let callee = icast(n_ref_fn(target, loc), CK_FUNC2PTR, mk_ptr(abi_type(target)));
    let cnt = nscratch.len - am;
    let cst = commit_list(am);
    let at = abi_type(target);
    let rt = unqual(types[at >> 4].base);
    let call = node_v(N_CALL, 0, rt, callee as i64, 0, cnt, loc, cst);
    if is_void(rt) {
        nscratch.push(n_expr_stmt(call));
        nscratch.push(node(N_RETURN, 0, 0, 0, 0, 0, loc));
    } else if t.ret_nv != 0 || t.ret_vb != 0 {
        // the covariant result: (char *)r [+ its vbase offset] + nv, null stays null
        let rs = csym(SK_VAR, intern("__ret_adj"), rt, loc);
        syms[rs].scope = 1;
        nscratch.push(node(N_DECL, 0, rt, rs, call as i64, loc as i64, loc));
        let rc = node(N_ICAST, CK_BITCAST, mk_ptr(t_char), rv(n_var(rs, loc)) as i64, 0, 0, loc);
        var e = rc;
        if t.ret_vb != 0 {
            let vp = rv(n_deref(node(N_ICAST, CK_BITCAST, mk_ptr(mk_ptr(t_char)), rv(n_var(rs, loc)) as i64, 0, 0, loc), loc));
            let x = node(N_BINARY, B_PTRADD, mk_ptr(t_char), vp as i64, int_node(t.ret_vb, t_long, loc) as i64, 0, loc);
            let off = rv(n_deref(node(N_ICAST, CK_BITCAST, mk_ptr(t_long), x as i64, 0, 0, loc), loc));
            e = node(N_BINARY, B_PTRADD, mk_ptr(t_char), e as i64, off as i64, 0, loc);
        }
        if t.ret_nv != 0 { e = node(N_BINARY, B_PTRADD, mk_ptr(t_char), e as i64, int_node(t.ret_nv, t_long, loc) as i64, 0, loc); }
        var v = node(N_ICAST, CK_BITCAST, rt, e as i64, 0, 0, loc);
        if is_pointer(types[syms[target].ty >> 4].base) {
            let test = icast(rv(n_var(rs, loc)), CK_PTR2BOOL, t_bool);
            v = node(N_COND, 0, rt, test as i64, v as i64, rv(n_var(rs, loc)) as i64, loc);
        }
        nscratch.push(node(N_RETURN, 0, rt, v as i64, 0, 0, loc));
    } else {
        nscratch.push(node(N_RETURN, 0, rt, call as i64, 0, 0, loc));
    }
    let body = n_block(bm, loc);
    let n = node_v(N_FUNCDEF, 0, syms[ts].ty, ts, body as i64, np, loc, ps);
    syms[ts].def = n as! i32;
    cg_extra.push(n);
}

// The thunks of the virtual functions defined here (clang emits them with
// the function, whether or not this unit has the vtable).
// clang's EmitThunks: the thunks of the most derived class's vtable that
// call a virtual member function, with its definition (each round: the
// definitions made since). An inline function keeps its thunks (they are
// emitted when it is).
var mthunk_seen = dictionary<u64, u8> {};
fn emit_method_thunks() {
    let tu = nodes[tu_node];
    for i in tu.c as i64 {
        let it = nlist[tu.v + i];
        if nodes[it].kind as i64 != N_FUNCDEF { continue; }
        let f = nodes[it].a as i64;
        if f >= cxs.len || cxs[f].flags & CF_MEMBER == 0 || cxs[f].flags & CF_STATIC != 0 { continue; }
        if cxs[f].flags & (CF_CTOR | CF_DTOR_DELETING) != 0 { continue; }
        if syms[f].def as u32 != it || complete_base.contains(f as u64) { continue; }
        if mthunk_seen.contains(f as u64) { continue; }
        mthunk_seen.insert(f as u64, 1);
        if cxs[f].dscope <= 0 { continue; }
        let cls = scope_class_type(cxs[f].dscope as i64);
        if cls == 0 { continue; }
        let r = rec_of(cls);
        if r >= crecs.len || crecs[r].flags & CR_LAYOUT == 0 || crecs[r].flags & CR_DYNAMIC == 0 { continue; }
        let g = vt_class(r);
        if !group_ok(g) { continue; }
        let G = vgroups[g];
        for j in G.th0..G.th0 + G.nth {
            let t = vg_mthunks[j];
            if t.method as i64 != f { continue; }
            if cxs[f].flags & CF_DTOR != 0 {
                let c = complete_sym(f);
                keep_thunk(f, c, thunk_sym(c, f, t, nodes[it].loc));
                let d = deleting_dtor(r);
                keep_thunk(f, d, thunk_sym(d, d, t, nodes[it].loc));
            } else {
                keep_thunk(f, f, thunk_sym(f, f, t, nodes[it].loc));
            }
        }
    }
}

fn keep_thunk(f: i64, target: i64, ts: i64) {
    if ts < 0 || cxl_link(ts) != LK_LINKONCE { return; }
    note_cx_use(f, ts);
    if target != f { note_cx_use(target, ts); }
}

// What function f's definition keeps (note_cx_use) is reached with it.
fn reach_uses(f: i64) {
    let h = cx_use_head.get(f as u64);
    if !h { return; }
    var i = h as i64 - 1;
    while i >= 0 {
        let v = cx_uses[i].v as i64;
        i = cx_uses[i].next as i64;
        if syms[v].kind as i64 == SK_FUNC { reach_fn(v); } else { reach_var(v); }
    }
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

fn label_numbered(s: i64, prefix: const u8[:]) {
    var nm: u8[>..] = [];
    format(nm, prefix, s);
    set_label(s, nm);
}

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
    let sv_vtt = cg_cur_vtt;
    let sv_complete = cg_complete;
    cg_cur_vtt = -1;
    cg_complete = true;
    if (kind == 1 || kind == 2) && has_vb(r) {
        let empty = n_block(nscratch.len, loc);
        complete_variant_body(f, r, empty, 0, loc);
        cg_cur_vtt = make_vtt(f, loc);
        cg_complete = false;
    }
    if (kind == 4 || kind == 5) && has_vb(r) {
        // the complete object's copy or move constructor: its own body
        let a = complete_sym(f);
        fn_this.insert(a as u64, th as! u32);
        let sm1 = stmt_buf.len;
        let ok1 = synth_special(f, kind, r, th, loc);
        let m1 = nscratch.len;
        for i in sm1..stmt_buf.len { nscratch.push(stmt_buf[i]); }
        stmt_buf.resize(sm1);
        if !ok1 { nscratch.push(mark_bad_stmt(loc)); }
        let b1 = n_block(m1, loc);
        var np1: i64 = 0;
        var ps1: i64 = 0;
        let pg1 = implicit_params.get(f as u64);
        if pg1 {
            let pm = nscratch.len;
            nscratch.push(pg1);
            ps1 = commit_list(pm);
            np1 = 1;
        }
        let fd = node_v(N_FUNCDEF, 0, syms[a].ty, a, b1 as i64, np1, loc, ps1);
        syms[a].def = fd as! i32;
        syms[a].flags = syms[a].flags | SF_DEFINED;
        cg_extra.push(fd);
        cg_cur_vtt = make_vtt(f, loc);
        cg_complete = false;
    }
    if kind == 1 {
        ok = ctor_prologue(r, th, 0, loc);
    } else if kind == 2 {
        if crecs[r].flags & CR_DYNAMIC != 0 {
            if !vptr_stores(r, th, loc) { ok = false; }
        }
        if !dtor_cleanups(r, th, loc) { ok = false; }
    } else if kind >= 4 {
        ok = synth_special(f, kind, r, th, loc);
    } else {
        // the deleting destructor: the complete one, then operator delete
        // (sized since C++14)
        let d = class_dtor(r);
        let am = nscratch.len;
        let c = lower_call(d, n_deref(rv(n_var(th, loc)), loc), am, loc, false);   // (the complete variant)
        stmt_buf.push(n_expr_stmt(c));
        // the class's operator delete (in it or its bases), else the global
        // one (sized since C++14; aligned for over-aligned classes)
        let al = type_align(cls);
        let aligned = al > NEW_ALIGN && align_val_type() != 0;
        let chain = alloc_chain(cls, OP_DELETE, false);
        let class_scope = chain >= 0 && cxs[chain].dscope > 0;
        if class_scope || aligned {
            let df, takes = usual_dealloc(chain, !class_scope && opt_cxx_std >= 14, aligned);
            let vp = node(N_ICAST, CK_BITCAST, t_voidptr, rv(n_var(th, loc)) as i64, 0, 0, loc);
            let dc = if df >= 0 { dealloc_call(df, takes, vp, int_node(type_size(cls), t_size, loc), al, loc) } else { opaque_node(loc) };
            if is_opq(dc) { ok = false; } else { stmt_buf.push(n_expr_stmt(dc)); }
        } else {
            let am2 = nscratch.len;
            nscratch.push(node(N_ICAST, CK_BITCAST, t_voidptr, rv(n_var(th, loc)) as i64, 0, 0, loc));
            var df: i64 = -1;
            if opt_cxx_std >= 14 {
                df = rt_fn("_ZdlPvm", t_void, 2, t_voidptr, t_size, 0, true, false);
                nscratch.push(int_node(type_size(cls), t_size, loc));
            } else {
                df = rt_fn("_ZdlPv", t_void, 1, t_voidptr, 0, 0, true, false);
            }
            stmt_buf.push(n_expr_stmt(n_call(df, am2, loc)));
        }
    }
    cg_cur_vtt = sv_vtt;
    cg_complete = sv_complete;
    for i in sm..stmt_buf.len { nscratch.push(stmt_buf[i]); }
    stmt_buf.resize(sm);
    if !ok { nscratch.push(mark_bad_stmt(loc)); }
    let body = n_block(mark, loc);
    var np: i64 = 0;
    var pstart: i64 = 0;
    let pg = implicit_params.get(f as u64);
    if pg && kind >= 4 {
        let pm = nscratch.len;
        nscratch.push(pg);
        pstart = commit_list(pm);
        np = 1;
    }
    let n = node_v(N_FUNCDEF, 0, syms[f].ty, f, body as i64, np, loc, pstart);
    syms[f].def = n as! i32;
    cg_extra.push(n);
    cg_this = sv;
}

// Called after parsing in code generation mode; false on errors.
recursive fn cg_finish(main_file: const u8[:]) -> bool {
    var dv: u8[>..] = [];
    cg_debug = env("GOOSECC_DEBUG_CG", dv);
    if cg_debug { write_stderr("cg_finish\n"); }
    // the vtables of the classes whose key function is defined here
    for r in crecs.len {
        if crecs[r].flags & CR_DYNAMIC == 0 || crecs[r].flags & (CR_PATTERN | CR_LAYOUT) != CR_LAYOUT { continue; }
        if records[r].flags & RF_COMPLETE == 0 { continue; }
        if vt_kind(r) == 2 { vtable_sym(r); }
    }
    // Rounds: implicit members, vtables, typeinfo and instantiations (each
    // may ask for more); names and linkage; the walk of what is emitted,
    // which may materialize temporaries and so ask for more again.
    let tu0 = tu_node;
    var vi = 0;
    var pi = 0;
    var ti = 0;
    var round = 0;
    var extra_seen = 0;
    loop {
        let before = syms.len;
        loop {
            var progress = false;
            // D2: bodies of instantiated functions used by what was synthesized
            inst_drain();
            while inst_defs_taken < inst_defs.len { cg_extra.push(inst_defs[inst_defs_taken]); inst_defs_taken++; progress = true; }
            while vi < vtables.len { if cg_debug { write_stderr(str("vtable ", vtables[vi], "\n")); } build_vtable(vtables[vi] as i64); vi++; progress = true; }
            while pi < pending_bodies.len {
                if cg_debug { write_stderr(str("synth ", pending_bodies[pi], " kind ", pending_bodies[pi + 1], "\n")); }
                synth_body(pending_bodies[pi] as i64, pending_bodies[pi + 1] as i64);
                pi += 2;
                progress = true;
            }
            if cg_debug { write_stderr("typeinfos\n"); }
            while ti < ti_classes.len { finish_typeinfo(ti_classes[ti] as i64); ti++; progress = true; }
            if !progress { break; }
        }
        if round == 0 {
            // the dynamic initialization of globals: a function per init_priority
            // (clang: _GLOBAL__I_000101 ..., then _GLOBAL__sub_I_<file>)
            var done_prio: i64 = -1;
            loop {
                var p: i64 = 65536;
                for x in gi_prio { if x as i64 > done_prio && (x as i64) < p { p = x as i64; } }
                if p > 65535 { break; }
                done_prio = p;
                gi_function(main_file, p);
            }
            tls_finish();
        }
        // the translation unit with the extra items
        let tu = nodes[tu0];
        let mark = nscratch.len;
        for i in tu.c as i64 { nscratch.push(nlist[tu.v + i]); }
        for x in cg_extra { nscratch.push(x); }
        let count = nscratch.len - mark;
        let start = commit_list(mark);
        tu_node = node_v(N_TU, 0, 0, 0, 0, count, 0, start);
        // (thunk bodies made here are in the next round's unit)
        emit_method_thunks();
        // names and linkage
        if cg_debug { write_stderr(str("cg_finish round ", round, " syms ", syms.len, "\n")); }
        name_syms();
        note_nothrow_all();
        if cg_debug { write_stderr("named\n"); }
        if round == 0 {
            // the named return value optimization
            for f in ret_fns {
                let fd = syms[f].def;
                if fd >= 0 && nodes[fd].kind as i64 == N_FUNCDEF { nrvo_function(f as i64, fd as u32); }
            }
            if !check_reachable() { return false; }
        } else {
            // what the last walk asked for: the new definitions it reached
            for f in reach_wanted { if syms[f].def >= 0 { reach_fn(f as i64); } }
            for i in extra_seen..cg_extra.len {
                let it = cg_extra[i];
                if nodes[it].kind as i64 == N_DECL && syms[nodes[it].a].kind as i64 == SK_VAR { var_decls.insert(nodes[it].a as u64, it); }
            }
            let wv = reach_wanted_vars.len;
            for i in wv {
                let g = var_decls.get(reach_wanted_vars[i] as u64);
                if g { wk.push(g); }
            }
            if !walk_reachable() { return false; }
        }
        extra_seen = cg_extra.len;
        round++;
        if syms.len == before && vi == vtables.len && pi == pending_bodies.len && ti == ti_classes.len && inst_defs_taken == inst_defs.len { break; }
        if round > 50 { break; }
    }
    // types: references become pointers, member functions take `this`
    lower_sym_types();
    return n_errors == 0;
}

fn gi_function(main_file: const u8[:], prio: i64) {
    var nm: u8[>..] = [];
    if prio == 65535 {
        var b = 0;
        for c, i in main_file { if c == '/' { b = i + 1; } }
        nm.append("_GLOBAL__sub_I_");
        nm.append(main_file[b..]);
    } else {
        nm.append("_GLOBAL__I_");
        var digits: u8[>..] = [];
        format(digits, prio);
        for i in 6 - digits.len { nm.push('0'); }
        nm.append(digits);
    }
    let f = csym(SK_FUNC, intern("__global_init"), fn_type0(t_void), 0);
    syms[f].sc = SC_STATIC as! u8;
    syms[f].flags = SF_DEFINED;
    cxs[f].flags = CF_IMPLICIT;
    set_label(f, nm);
    let ai = get_attr(f);
    sym_attrs[ai].flags = sym_attrs[ai].flags | AM_CTOR;
    sym_attrs[ai].ctor_prio = prio as! u16;
    let mark = nscratch.len;
    for st, i in gi_stmts { if gi_prio[i] as i64 == prio { nscratch.push(st); } }
    let body = n_block(mark, 0);
    let n = node_v(N_FUNCDEF, 0, syms[f].ty, f, body as i64, 0, 0, 0);
    syms[f].def = n as! i32;
    cg_extra.push(n);
}

// The types of symbols for C's lowering.
fn lower_sym_types() {
    for s in 1..syms.len {
        let k = syms[s].kind as i64;
        if k == SK_FUNC {
            if s < cxs.len && cxs[s].flags & (CF_PATTERN | CF_TEMPLATE) != 0 { continue; }
            syms[s].ty = abi_type(s);
        } else if k == SK_VAR {
            if indirect_params.count > 0 && indirect_params.contains(s as u64) { syms[s].ty = mk_ptr(unqual(syms[s].ty)); }
            else { syms[s].ty = lower_ty(syms[s].ty); }
        }
    }
    for i in fields.len { fields[i].ty = lower_ty(fields[i].ty); }
}

// ---------------------------------------------------------------------------
// The reachable code: every function and variable the C lowering will
// emit, walked from the external definitions; references rewritten,
// unsupported constructs reported.

var cg_seen: u8[>..] = [];
var reach_wanted: u32[>..] = [];
var cg_debug = false;       // functions reached before their bodies were synthesized
var wk: u32[>..<] = [];
var var_decls = dictionary<u64, u32> {};   // file-scope variable -> its N_DECL
var n_bad: i64 = 0;

recursive fn reach_fn(f: i64) {
    if syms[f].def < 0 {
        let b = complete_base.get(f as u64);
        if b { reach_fn(b as i64); }
        else { reach_wanted.push(f as! u32); }
        return;
    }
    let d = syms[f].def as u32;
    if nodes[d].kind as i64 != N_FUNCDEF { return; }
    wk.push(d);
}

fn reach_var(s: i64) {
    let g = var_decls.get(s as u64);
    if g { wk.push(g); } else { reach_wanted_vars.push(s as! u32); }
}
var reach_wanted_vars: u32[>..] = [];

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
            if (syms[s].sc as i64 != SC_STATIC && cxl_link(s) != LK_LINKONCE) || cg_has_attr(s, AM_CTOR) || cg_has_attr(s, AM_USED) { wk.push(it); }
        } else if nd.kind as i64 == N_DECL && syms[s].kind as i64 == SK_VAR {
            if syms[s].sc as i64 != SC_STATIC && cxl_link(s) != LK_LINKONCE && syms[s].flags & SF_FILESCOPE != 0 && (nd.b != 0 || syms[s].flags & (SF_DEFINED | SF_TENTATIVE) != 0) { wk.push(it); }
        }
    }
    return walk_reachable();
}

fn walk_reachable() -> bool {
    while wk.len > 0 {
        let e = wk.pop();
        let n = e & 0x7FFFFFFF;
        visit_cond = e >> 31 != 0;
        kid_cond = visit_cond;
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
        if k == N_FUNCDEF {
            let fs = nodes[n].a as i64;
            let ai = syms[fs].attr;
            if ai != 0 && sym_attrs[ai].asm_len != 0 {
                let o = sym_attrs[ai].asm_label as i64;
                write_stderr(str("  function ", strbytes[o..o + sym_attrs[ai].asm_len as i64], "\n"));
            }
        }
    }
}

fn kid(x: u32) { if x != 0 { wk.push(x | (if kid_cond { 0x80000000 } else { 0 })); } }
fn kid_c(x: u32, c: bool) {
    let sv = kid_cond;
    kid_cond = c;
    kid(x);
    kid_cond = sv;
}
// the walk's conditional context: the node is in an operand of ?:, && or ||
// of its full-expression (a temporary made there is destroyed only if it
// was made)
var visit_cond = false;
var kid_cond = false;
var indirect_params = dictionary<u64, u32> {};
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

recursive fn visit(n: u32) {
    let nd = nodes[n];
    let k = nd.kind as i64;
    // clang folds the conditions it can evaluate (ConstantFoldsToSimpleInteger),
    // calls of constexpr functions too: `if (std::__is_constant_evaluated())`
    if k == N_IF || k == N_COND || (k == N_BINARY && (nd.op as i64 == B_LAND || nd.op as i64 == B_LOR)) {
        if nd.a != 0 { fold_cond(nd.a); }
    }
    if (k == N_XPRV || (k == N_CTOR && is_record(nd.ty) && !is_opaque(nd.ty) && !class_trivial_copy(rec_of(nd.ty)))) {
        // a class prvalue no object was initialized from: a temporary
        let x = xtemp_of(n_copy(n), nd.ty, nd.loc);
        if is_opq(x) { bad(n); return; }
        nodes[n] = nodes[x];
        if visit_cond { nodes[n].op = ((nodes[n].op as i64) | XT_COND) as! u8; }
        visit(n);
        return;
    }
    if k == N_XNRET {
        // the NRVO variable is the return slot already: the flag that keeps
        // it from being destroyed; another variable is copied (moved)
        let v = nd.a as i64;
        let fl = nrvo_flags.get(v as u64);
        var e: u32 = 0;
        if fl {
            let lhs = n_var(fl as i64, nd.loc);
            e = node(N_ASSIGN, 0, t_bool, lhs as i64, int_node(1, t_bool, nd.loc) as i64, 0, nd.loc);
        } else {
            e = nd.b;
        }
        let r = rv(n_var(nd.c as i64, nd.loc));
        let cm = node(N_BINARY, B_COMMA, nodes[r].ty, e as i64, r as i64, 0, nd.loc);
        nodes[n] = nodes[cm];
        visit(n);
        return;
    }
    if k == N_XTEMP && visit_cond { nodes[n].op = ((nodes[n].op as i64) | XT_COND) as! u8; }
    if k == N_CTOR && is_record(nd.ty) && !is_opaque(nd.ty) && class_trivial_copy(rec_of(nd.ty)) {
        // a temporary of a trivially copyable class used as a value
        let v = ctor_value(n, nd.loc);
        if !is_opq(v) {
            nodes[n] = nodes[v];
            push_kids(n);
            return;
        }
    }
    if k >= N_THIS && k <= N_RANGEFOR { bad(n); return; }
    if k == N_FUNCDEF {
        let f = nd.a as i64;
        let ft = types[syms[f].ty >> 4];
        for i in nd.c {
            let p = nlist[nd.v + i];
            if pass_indirect(syms[p].ty) { indirect_params.insert(p as u64, 1); }
        }
        let rg = fn_ret.get(f as u64);
        var rs: u32 = 0;
        if rg { rs = rg; }
        if pass_indirect(ft.base) && rs == 0 { bad(n); return; }
        // the return slot, `this`, the parameters
        if is_this_fn(f) || rs != 0 {
            var th: u32 = 0;
            if is_this_fn(f) {
                let thg = fn_this.get(f as u64);
                if thg { th = thg; } else { bad(n); return; }
            }
            let mark = nscratch.len;
            if rs != 0 { nscratch.push(rs); }
            if th != 0 { nscratch.push(th); }
            if needs_vtt(f) {
                let vg = fn_vtt.get(f as u64);
                if !vg { nscratch.resize(mark); bad(n); return; }
                nscratch.push(vg);
            }
            for i in nd.c { nscratch.push(nlist[nd.v + i]); }
            let count = nscratch.len - mark;
            let start = commit_list(mark);
            nodes[n].v = start;
            nodes[n].c = count as! u32;
        }
        nodes[n].ty = abi_type(f);
        // clang: a virtual destructor emitted uses its class's vtable (and so its VTT)
        if cxs[f].flags & CF_DTOR != 0 && dtor_is_virtual(f) {
            let cr = rec_of(scope_class_type(cxs[f].dscope as i64));
            if cr < crecs.len {
                let v = vtable_sym(cr);
                if v >= 0 { note_cx_use(f, v); }
            }
        }
        reach_uses(f);
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
            if syms[s].flags & SF_THREAD != 0 && nd.c != 1 && tls_use_wrapper(s) {
                // a thread_local through its wrapper (cx_gen_tls)
                tls_use(n);
                visit(n);
                return;
            }
            if syms[s].flags & SF_FILESCOPE != 0 { reach_var(s); }
            if !c_type_ok(lower_ty(syms[s].ty)) { bad(n); return; }
            if indirect_params.count > 0 && indirect_params.contains(s as u64) && !is_pointer(nd.ty) {
                // a parameter passed by invisible reference: through its pointer
                let c = node(N_DECLREF, 0, mk_ptr(unqual(syms[s].ty)), s, 0, 0, nd.loc);
                nodes[c].flags = NF_LVALUE;
                deref_into(n, c);
            } else if nd.flags & NF_REFDEREF != 0 {
                let c = node(N_DECLREF, 0, lower_ty(syms[s].ty), s, 0, 0, nd.loc);
                nodes[c].flags = NF_LVALUE;
                deref_into(n, c);
            }
        } else if sk != SK_BUILTIN { bad(n); return; }
    } else if k == N_MEMBER {
        if nd.c != 0 {
            // a lambda's capture: its field in the closure (cx_gen_lambda.cap_ref)
            nodes[n].b = records[nd.c - 1].first + nd.b;
            nodes[n].c = 0;
            visit(n);
            return;
        }
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
    } else if k == N_XTEMP {
        if nd.c != 0 { reach_fn(nd.c as i64); }
        let s = nd.b as i64;
        if !c_type_ok(lower_ty(syms[s].ty)) { bad(n); return; }
    } else if k == N_XPUSH {
        if (nd.op as i64) & XP_CALL != 0 { reach_fn(nd.c as i64); }
    } else if k == N_XCATCH {
        if nd.c != 0 { reach_var(nd.c as i64); }
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

// A copy of node n.
fn n_copy(n: u32) -> u32 {
    let c = nodes.len as! u32;
    nodes.push(nodes[n]);
    return c;
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
    if k >= N_COMPOUND && k <= N_ASMOP || k == N_STMTEXPR || (k >= N_XPUSH && k <= N_XCATCH) { kid_cond = false; }
    if k == N_COND {
        kid(nd.a);
        kid_c(nd.b, true);
        kid_c(nd.c, true);
        return;
    }
    if k == N_BINARY && (nd.op as i64 == B_LAND || nd.op as i64 == B_LOR) {
        kid(nd.a);
        kid_c(nd.b, true);
        return;
    }
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
    if k == N_XTEMP { kid(nd.a); return; }
    if k == N_XPUSH { if (nd.op as i64) & XP_STMT != 0 { kid(nd.a); } return; }
    if k == N_XTRY { kid(nd.a); kids_list(nd.v, nd.c); return; }
    if k == N_XCATCH { kid(nd.b); kid(nd.v as! u32); return; }
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
