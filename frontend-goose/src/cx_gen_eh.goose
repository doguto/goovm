// goosecc D3: C++ exceptions in code generation: throw expressions, try
// blocks and handlers (lowered to N_XTRY / N_XCATCH, cx_eh.goose does the
// landing pads), exception specifications, the C++ runtime's functions,
// and the typeinfo objects of the thrown and caught types. As clang does
// (CGException.cpp, ItaniumCXXABI.cpp):
//
//   throw e   ({ void *x = __cxa_allocate_exception(sizeof(T));
//              { [EH only: __cxa_free_exception(x)] <construct *(T *)x from e>; }
//              __cxa_throw(x, &typeinfo(T), T's destructor or 0); })
//   throw;    __cxa_rethrow()
//   catch     the adjusted pointer from __cxa_begin_catch (a class with a
//             non-trivial copy constructor: __cxa_get_exception_ptr, the
//             copy, then __cxa_begin_catch); __cxa_end_catch on every exit

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

// ---------------------------------------------------------------------------
// Exception specifications (cx_decl's declarators: excspec).

var excspecs = dictionary<u64, u64> {};     // function -> kind | position << 8

fn note_excspec(s: i64, kind: i64, pos: i64) {
    excspecs.insert(s as u64, (kind as u64) | ((pos as u64) << 8));
}

// 0 none, 1 non-throwing, 2 noexcept(false), 3 throw(types)
fn excspec_kind(s: i64) -> i64 {
    let g = excspecs.get(s as u64);
    if g { return (g & 255) as i64; }
    let c = syms[s].canon as i64;
    if c >= 0 && c != s {
        let h = excspecs.get(c as u64);
        if h { return (h & 255) as i64; }
    }
    return 0;
}

// Does function s never throw (noexcept, throw(), or a destructor or
// deallocation function without an exception specification)?
fn fn_nothrow(s: i64) -> bool {
    let k = excspec_kind(s);
    if k == 1 { return true; }
    if k == 2 || k == 3 { return false; }
    if cxs[s].flags & CF_NOEXCEPT != 0 { return true; }
    if cxs[s].flags & CF_DTOR != 0 { return true; }
    if cxs[s].flags & CF_OPERATOR != 0 && (cxs[s].op as i64 == OP_DELETE || cxs[s].op as i64 == OP_DELETE_ARR) { return true; }
    return false;
}

// The exception flags of every function for the lowering.
fn note_nothrow_all() {
    cxl_grow();
    for s in 1..syms.len {
        if syms[s].kind as i64 != SK_FUNC { continue; }
        if s >= cxs.len { continue; }
        if fn_nothrow(s) { cxl[s].flags = cxl[s].flags | ((CXL_NOEXCEPT | CXL_NOUNWIND) as! u8); }
    }
    // the runtime's non-throwing functions
    for x in rt_nothrow { cxl[x].flags = cxl[x].flags | (CXL_NOUNWIND as! u8); }
}

// ---------------------------------------------------------------------------
// The C++ runtime's functions (extern "C").

var rt_syms = dictionary<u64, u32> {};
var rt_nothrow: u32[>..] = [];

fn rt_fn(name: const u8[:], ret: u32, np: i64, p0: u32, p1: u32, p2: u32, nothrow: bool, noret: bool) -> i64 {
    let id = intern(name);
    let g = rt_syms.get(id as u64);
    if g { return g as i64; }
    fn_scratch.clear();
    if np > 0 { fn_scratch.push(p0); }
    if np > 1 { fn_scratch.push(p1); }
    if np > 2 { fn_scratch.push(p2); }
    let ft = qt(mk_type(TY_FUNC, if noret { TF_NORETURN } else { 0 }, ret, 0, 0, 0) as i64, 0);
    let s = csym(SK_FUNC, id, ft, 0);
    syms[s].sc = SC_EXTERN as! u8;
    syms[s].flags = (SF_FILESCOPE | (if noret { SF_NORETURN } else { 0 })) as! u32;
    cxs[s].flags = CF_EXTERN_C;
    rt_syms.insert(id as u64, s as! u32);
    if nothrow { rt_nothrow.push(s as! u32); }
    return s;
}

fn rt_alloc_exn() -> i64 { rt_fn("__cxa_allocate_exception", t_voidptr, 1, t_size, 0, 0, true, false) }
fn rt_free_exn() -> i64 { rt_fn("__cxa_free_exception", t_void, 1, t_voidptr, 0, 0, true, false) }
fn rt_throw() -> i64 {
    let dt = mk_ptr(fn_type1(t_void, t_voidptr));
    return rt_fn("__cxa_throw", t_void, 3, t_voidptr, t_voidptr, dt, false, true);
}
fn rt_rethrow() -> i64 { rt_fn("__cxa_rethrow", t_void, 0, 0, 0, 0, false, true) }

// A call of runtime function f with the arguments nscratch[mark..] (C types).
fn rt_call(f: i64, mark: i64, loc: u32) -> u32 { n_call(f, mark, loc) }

// ---------------------------------------------------------------------------
// typeinfo objects of types (Itanium 2.9.5).

// Is t (unqualified) a fundamental type whose typeinfo the runtime defines?
fn fundamental_ti(t: u32) -> bool {
    let k = kind_of(t);
    if k >= TY_VOID && k <= TY_LDOUBLE { return true; }
    if k == TY_FLOAT128 || k == TY_NULLPTR { return true; }
    return false;
}

var ptr_tis = dictionary<u64, u32> {};

// The typeinfo variable of type t (exceptions: the thrown or caught type,
// cv-unqualified at the top), or -1 when D3 cannot make it yet.
recursive fn typeinfo_var(t0: u32) -> i64 {
    let t = unqual(t0);
    if is_opaque(t) { return -1; }
    if is_record(t) { return typeinfo_sym(rec_of(t)); }
    if fundamental_ti(t) {
        if !mangle_special("_ZTI", t) { return -1; }
        return ext_array(mg);
    }
    if kind_of(t) == TY_POINTER {
        let p = tbase(t);
        // the runtime has P and PK of the fundamental types
        if fundamental_ti(unqual(p)) && quals(p) & (Q_VOLATILE | Q_RESTRICT) == 0 {
            if !mangle_special("_ZTI", t) { return -1; }
            return ext_array(mg);
        }
        let g = ptr_tis.get(t as u64);
        if g { return g as i64; }
        let pti = typeinfo_var(p);
        if pti < 0 { return -1; }
        // __pointer_type_info { vptr, name, flags, pointee }
        let loc: u32 = 0;
        let ns = typeinfo_name_sym(t, 1, -1);
        if ns < 0 { return -1; }
        var flags: i64 = 0;
        if quals(p) & Q_CONST != 0 { flags = flags | 1; }
        if quals(p) & Q_VOLATILE != 0 { flags = flags | 2; }
        if quals(p) & Q_RESTRICT != 0 { flags = flags | 4; }
        if is_record(unqual(p)) && !is_complete(unqual(p)) { flags = flags | 8; }
        let mark = nscratch.len;
        nscratch.push(void_addr_of(ext_array("_ZTVN10__cxxabiv119__pointer_type_infoE"), 2, loc));
        nscratch.push(void_addr_of(ns, 0, loc));
        nscratch.push(int_as_ptr(flags, loc));
        nscratch.push(void_addr_of(pti, 0, loc));
        let s = ti_var(t, mark, 1, -1);
        ptr_tis.insert(t as u64, s as! u32);
        return s;
    }
    if kind_of(t) == TY_ENUM {
        let g = ptr_tis.get(t as u64);
        if g { return g as i64; }
        let ns = typeinfo_name_sym(t, 1, -1);
        if ns < 0 { return -1; }
        let mark = nscratch.len;
        nscratch.push(void_addr_of(ext_array("_ZTVN10__cxxabiv116__enum_type_infoE"), 2, 0));
        nscratch.push(void_addr_of(ns, 0, 0));
        let s = ti_var(t, mark, 1, -1);
        ptr_tis.insert(t as u64, s as! u32);
        return s;
    }
    return -1;
}

// The _ZTS name variable of type t (link: 0 internal, 1 linkonce_odr,
// 2 strong, 3 undefined; r: the class, -1 none).
fn typeinfo_name_sym(t: u32, link: i64, r: i64) -> i64 {
    if !mangle_special("", t) { return -1; }
    let name_len = mg.len;
    let soff = strbytes.len;
    strbytes.append(mg);
    strbytes.push(0);
    let si = strs.len;
    strs.push(StrLit { start: soff as! u32, len: (name_len + 1) as! u32, elem: t_char });
    let nt = mk_array(t_char | (Q_CONST as! u32), name_len + 1);
    let ns = csym(SK_VAR, intern("__typeinfo_name"), nt, 0);
    syms[ns].flags = SF_FILESCOPE | SF_DEFINED;
    cxs[ns].flags = CF_IMPLICIT;
    mangle_special("_ZTS", t);
    set_label(ns, mg);
    set_data_link(ns, link, false);
    if link != 3 {
        let sn = node(N_STRING, 0, nt, si, 0, 0, 0);
        nodes[sn].flags = NF_LVALUE | NF_STRINIT;
        cg_extra.push(node(N_DECL, 0, nt, ns, sn as i64, 0, 0));
    }
    return ns;
}

// The _ZTI variable of type t holding nscratch[mark..] (popped).
fn ti_var(t: u32, mark: i64, link: i64, r: i64) -> i64 {
    let n = nscratch.len - mark;
    let tt = mk_array(with_q(t_voidptr, Q_CONST), n);
    let s = csym(SK_VAR, intern("__typeinfo"), tt, 0);
    syms[s].flags = SF_FILESCOPE | SF_DEFINED;
    cxs[s].flags = CF_IMPLICIT;
    mangle_special("_ZTI", t);
    set_label(s, mg);
    set_data_link(s, link, true);
    if link == 3 { nscratch.resize(mark); return s; }
    let start = commit_list(mark);
    let il = node_v(N_INITLIST, 0, tt, 0, 0, n, 0, start);
    cg_extra.push(node(N_DECL, 0, tt, s, il as i64, 0, 0));
    return s;
}

// Linkage of a C++ ABI data object (link as above).
fn set_data_link(s: i64, link: i64, relro: bool) {
    let rf = if relro { CXL_RELRO } else { 0 };
    if link == 0 { syms[s].sc = SC_STATIC as! u8; set_link(s, LK_DEFAULT, rf); }
    else if link == 1 { syms[s].sc = 0; set_link(s, LK_LINKONCE, rf | CXL_COMDAT); }
    else if link == 2 { syms[s].sc = 0; set_link(s, LK_DEFAULT, rf); }
    else { syms[s].sc = SC_EXTERN as! u8; syms[s].flags = syms[s].flags & ~(SF_DEFINED as! u32); }
}

// ---------------------------------------------------------------------------
// throw.

// The type of the exception object for operand e: arrays and functions
// decay, references and top-level cv are dropped.
fn exn_type(e: u32) -> u32 {
    let t = unqual(nodes[e].ty);
    if is_array(t) { return mk_ptr(tbase(t)); }
    if is_func(t) { return mk_ptr(t); }
    return t;
}

recursive fn cg_throw(e: u32, loc: u32) -> u32 {
    if e == 0 {
        let mark = nscratch.len;
        let c = rt_call(rt_rethrow(), mark, loc);
        return c;
    }
    if is_opq(e) && nodes[e].kind as i64 != N_INITBRACE { return opaque_node(loc); }
    let t = exn_type(e);
    if is_opaque(t) || is_void(t) { return opaque_node(loc); }
    let ti = typeinfo_var(t);
    if ti < 0 { return opaque_node(loc); }
    let pt = mk_ptr(t);
    // void *x = __cxa_allocate_exception(sizeof(T))
    let xs = csym(SK_VAR, intern("__exn"), t_voidptr, loc);
    syms[xs].scope = 1;
    let am = nscratch.len;
    nscratch.push(int_node(type_size(t), t_size, loc));
    let alloc = rt_call(rt_alloc_exn(), am, loc);
    let mark = nscratch.len;
    nscratch.push(node(N_DECL, 0, t_voidptr, xs, alloc as i64, loc as i64, loc));
    // { [EH: free] init }
    let obj = n_deref(node(N_ICAST, CK_BITCAST, pt, rv(n_var(xs, loc)) as i64, 0, 0, loc), loc);
    var init: u32 = 0;
    if is_record(t) {
        init = init_into(obj, e, loc);
    } else {
        var v: u32 = 0;
        if is_array(nodes[e].ty) || is_func(nodes[e].ty) { v = conv_value(e, t, loc); }
        else { v = conv_value(e, t, loc); }
        if !is_opq(v) { init = node(N_ASSIGN, 0, t, obj as i64, v as i64, 0, loc); }
    }
    if init == 0 || is_opq(init) { nscratch.resize(mark); return opaque_node(loc); }
    let im = nscratch.len;
    let fm = nscratch.len;
    nscratch.push(rv(n_var(xs, loc)));
    let free = n_expr_stmt(rt_call(rt_free_exn(), fm, loc));
    nscratch.push(node(N_XPUSH, XP_STMT | XP_EHONLY, 0, free as i64, 0, 0, loc));
    nscratch.push(n_expr_stmt(init));
    nscratch.push(n_block(im, loc));
    // __cxa_throw(x, &typeinfo, dtor)
    let tm = nscratch.len;
    nscratch.push(rv(n_var(xs, loc)));
    nscratch.push(void_addr_of_any(ti, loc));
    let dt = mk_ptr(fn_type1(t_void, t_voidptr));
    var d: i64 = -1;
    if is_record(t) { d = class_dtor(rec_of(t)); }
    if d >= 0 {
        let c = complete_sym(d);
        nscratch.push(node(N_ICAST, CK_BITCAST, dt, icast(n_ref_fn(c, loc), CK_FUNC2PTR, mk_ptr(abi_type(c))) as i64, 0, 0, loc));
    } else {
        nscratch.push(node(N_ICAST, CK_NULL2PTR, dt, int_node(0, t_int, loc) as i64, 0, 0, loc));
    }
    nscratch.push(n_expr_stmt(rt_call(rt_throw(), tm, loc)));
    let body = n_block(mark, loc);
    return node(N_STMTEXPR, 0, t_void, body as i64, 0, 0, loc);
}

// The address of variable s as void * (an array decays).
fn void_addr_of_any(s: i64, loc: u32) -> u32 {
    if is_array(syms[s].ty) { return void_addr_of(s, 0, loc); }
    return node(N_ICAST, CK_BITCAST, t_voidptr, n_addr(n_var(s, loc), loc) as i64, 0, 0, loc);
}

// ---------------------------------------------------------------------------
// try and catch.

// A handler: the variable vs (0 none) of caught type ct (0: catch (...)),
// the handler's compound statement h. rethrow: a constructor's or
// destructor's function-try-block.
recursive fn cg_catch(vs0: i64, ct: u32, h: u32, loc: u32, rethrow: bool) -> u32 {
    var op: i64 = if rethrow { XC_RETHROW } else { 0 };
    if ct == 0 {
        return node_v(N_XCATCH, op, 0, 0, h as i64, 0, loc, 0);
    }
    // the type a handler matches: references and top-level cv dropped
    let t = unqual(nonref(ct));
    if is_opaque(t) { return opaque_node(loc); }
    let ti = typeinfo_var(if is_array(t) { mk_ptr(tbase(t)) } else if is_func(t) { mk_ptr(t) } else { t });
    if ti < 0 { return opaque_node(loc); }
    var init: u32 = 0;
    var body = h;
    var vs = vs0;
    if vs == 0 && !is_ref(ct) && is_record(t) && !class_trivial_copy(rec_of(t)) {
        // an unnamed class parameter is still copied (and destroyed)
        vs = csym(SK_VAR, intern("__exn_param"), t, loc);
        syms[vs].scope = 1;
    }
    if vs > 0 {
        let x = node(N_XEXN, 0, t_voidptr, 0, 0, 0, loc);
        if is_ref(ct) {
            // bound to the exception object (a pointer caught by reference: TODO)
            let p = node(N_ICAST, CK_BITCAST, mk_ptr(nonref(ct)), x as i64, 0, 0, loc);
            init = node(N_DECL, 0, syms[vs].ty, vs, p as i64, loc as i64, loc);
        } else if is_pointer(t) {
            // the adjusted pointer is the caught pointer's value
            let p = node(N_ICAST, CK_BITCAST, t, x as i64, 0, 0, loc);
            init = node(N_DECL, 0, syms[vs].ty, vs, p as i64, loc as i64, loc);
        } else if is_record(t) && !class_trivial_copy(rec_of(t)) {
            // copied by its constructor, then destroyed at the end of the handler
            op = op | XC_COPY;
            let src = n_deref(node(N_ICAST, CK_BITCAST, mk_ptr(with_q(t, Q_CONST)), x as i64, 0, 0, loc), loc);
            let mark = nscratch.len;
            nscratch.push(node(N_DECL, 0, syms[vs].ty, vs, 0, loc as i64, loc));
            let cm = nscratch.len;
            nscratch.push(src);
            let st = construct_at(n_var(vs, loc), cm, loc);
            if st == 0 { nscratch.resize(mark); return opaque_node(loc); }
            nscratch.push(st);
            init = n_block(mark, loc);
            let d = class_dtor(rec_of(t));
            if d >= 0 {
                let bm = nscratch.len;
                nscratch.push(node(N_XPUSH, XP_CALL, 0, vs, 0, complete_sym(d), loc));
                nscratch.push(h);
                body = n_block(bm, loc);
            }
        } else {
            // a scalar or a trivially copyable class: a copy
            let src = n_deref(node(N_ICAST, CK_BITCAST, mk_ptr(t), x as i64, 0, 0, loc), loc);
            init = node(N_DECL, 0, syms[vs].ty, vs, rv(src) as i64, loc as i64, loc);
        }
    }
    return node_v(N_XCATCH, op, t, vs, body as i64, ti, loc, init as i64);
}

// try { body } with handlers nscratch[mark..] (N_XCATCH nodes; popped).
fn cg_try(body: u32, mark: i64, loc: u32) -> u32 {
    for i in mark..nscratch.len { if is_opq(nscratch[i]) { nscratch.resize(mark); return n_expr_stmt(opaque_node(loc)); } }
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    return node_v(N_XTRY, 0, 0, body as i64, 0, count, loc, start);
}
