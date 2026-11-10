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

// Does function s never throw (noexcept, throw(), a destructor or
// deallocation function without an exception specification, or an
// implicit or defaulted special member whose implicit exception
// specification is non-throwing)?
recursive fn fn_nothrow(s: i64) -> bool {
    let k = excspec_kind(s);
    if k == 1 { return true; }
    if k == 2 || k == 3 { return false; }
    if cxs[s].flags & CF_NOEXCEPT != 0 { return true; }
    if cxs[s].flags & CF_DTOR != 0 { return true; }
    if cxs[s].flags & CF_OPERATOR != 0 && (cxs[s].op as i64 == OP_DELETE || cxs[s].op as i64 == OP_DELETE_ARR) { return true; }
    if cxs[s].flags & (CF_IMPLICIT | CF_DEFAULTED) != 0 && cxs[s].flags & CF_MEMBER != 0 {
        let sk = special_kind(s);
        if sk > 0 {
            let cls = scope_class_type(cxs[s].dscope as i64);
            if cls != 0 && is_complete(cls) { return subobjects_nothrow(rec_of(cls), sk); }
        }
    }
    return false;
}

// The kind of special member f: 1 default constructor, 4 copy constructor,
// 5 move constructor, 6 copy assignment, 7 move assignment, 0 other.
fn special_kind(f: i64) -> i64 {
    let cls = scope_class_type(cxs[f].dscope as i64);
    if cls == 0 { return 0; }
    let ft = types[syms[f].ty >> 4];
    if cxs[f].flags & CF_CTOR != 0 {
        if ft.n == 0 || defaults_from(f, 0) { return 1; }
        let p0 = tparams[ft.extra];
        if !is_ref(p0) || unqual(tbase(p0)) != unqual(cls) { return 0; }
        if ft.n > 1 && !defaults_from(f, 1) { return 0; }
        return if kind_of(p0) == TY_RREF { 5 } else { 4 };
    }
    if cxs[f].flags & CF_OPERATOR != 0 && cxs[f].op as i64 == OP_EQUAL && ft.n == 1 {
        let p0 = tparams[ft.extra];
        if !is_ref(p0) || unqual(tbase(p0)) != unqual(cls) { return 0; }
        return if kind_of(p0) == TY_RREF { 7 } else { 6 };
    }
    return 0;
}

// The implicit exception specification ([except.spec]p8): is every
// function the special member of kind k of class r calls for its bases
// and members non-throwing (and, for the default constructor, every
// default member initializer)?
var subnt_memo = dictionary<u64, u8> {};
recursive fn subobjects_nothrow(r: i64, k: i64) -> bool {
    let key = ((r as u64) << 3) | (k as u64);
    let g = subnt_memo.get(key);
    if g { return g == 1; }
    subnt_memo.insert(key, 2);      // (a cycle: throwing)
    var ok = true;
    let cr = crecs[r];
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if !is_record(b.ty) || is_opaque(b.ty) { ok = false; break; }
        if !class_op_nothrow(rec_of(b.ty), k) { ok = false; break; }
    }
    if ok {
        let rec = records[r];
        let sc = cr.scope as i64;
        for i in rec.first..rec.first + rec.count {
            let f = fields[i];
            if f.name == 0 { continue; }
            if k == 1 && field_nsdmi(sc, f.name) != 0 {
                if nsdmi_may_throw(field_nsdmi(sc, f.name), f.ty) { ok = false; break; }
                continue;
            }
            let bt = base_elem_t(f.ty);
            if is_ref(f.ty) || !is_record(bt) { continue; }
            if is_opaque(bt) { ok = false; break; }
            if !class_op_nothrow(rec_of(bt), k) { ok = false; break; }
        }
    }
    subnt_memo.insert(key, if ok { 1 } else { 2 });
    return ok;
}

// Is the special member of kind k that class r's subobject uses non-throwing?
recursive fn class_op_nothrow(r: i64, k: i64) -> bool {
    if crecs[r].flags & CR_LAYOUT == 0 { return false; }
    let i = sm(r);
    if k == 1 {
        let d = default_ctor_of(r);
        if d >= 0 && user_provided(d) { return fn_nothrow(d); }
        if d == -2 { return true; }     // deleted: not called
        return subobjects_nothrow(r, 1);
    }
    var kk = k;
    if k == 5 && i.flags & SM_HAS_MOVE == 0 { kk = 4; }
    if k == 7 && i.flags & SM_HAS_MASG == 0 { kk = 6; }
    if kk == 4 {
        if i.flags & SM_COPY_DEL != 0 { return true; }
        if i.copy >= 0 && user_provided(i.copy as i64) { return fn_nothrow(i.copy as i64); }
        if i.flags & SM_TRIV_COPY != 0 { return true; }
        return subobjects_nothrow(r, 4);
    }
    if kk == 5 {
        if i.flags & SM_MOVE_DEL != 0 { return true; }
        if i.move >= 0 && user_provided(i.move as i64) { return fn_nothrow(i.move as i64); }
        if i.flags & SM_TRIV_MOVE != 0 { return true; }
        return subobjects_nothrow(r, 5);
    }
    if kk == 6 {
        if i.casg >= 0 && user_provided(i.casg as i64) { return fn_nothrow(i.casg as i64); }
        if i.flags & SM_TRIV_CASG != 0 { return true; }
        return subobjects_nothrow(r, 6);
    }
    if i.masg >= 0 && user_provided(i.masg as i64) { return fn_nothrow(i.masg as i64); }
    if i.flags & SM_TRIV_MASG != 0 { return true; }
    return subobjects_nothrow(r, 7);
}

// The default constructor of class r (all parameters with defaults), -1
// when it has none declared, -2 when it is deleted.
fn default_ctor_of(r: i64) -> i64 {
    var s = scope_find(crecs[r].scope as i64, id_ctor);
    while s >= 0 {
        let f = resolve(s);
        if f >= 0 && syms[f].kind as i64 == SK_FUNC && cxs[f].flags & CF_CTOR != 0 {
            let ft = types[syms[f].ty >> 4];
            if ft.n == 0 || defaults_from(f, 0) {
                if cxs[f].flags & CF_DELETED != 0 { return -2; }
                return f;
            }
        }
        s = cxs[s].nnext as i64;
    }
    return -1;
}

// May the default member initializer of member m (its tokens) throw? A
// conservative look at the tokens: no call, new, throw, typeid or
// dynamic_cast, and not a class type initialized by a constructor.
fn nsdmi_may_throw(m: i64, t: u32) -> bool {
    if is_record(base_elem_t(t)) { return true; }
    var i = cxs[m].body as i64;
    var depth: i64 = 0;
    var prev: i64 = 0;
    var n = 0;
    while i < tu_toks.len {
        let k = tu_toks[i].kind as i64;
        if k == TK_EOF { break; }
        if depth == 0 && n > 0 && (k == TK_SEMI || k == TK_COMMA || k == TK_R_BRACE) { break; }
        if k == TK_L_PAREN || k == TK_L_BRACE || k == TK_L_SQUARE {
            if n > 0 && (prev == TK_IDENT || prev == TK_GREATER || prev == TK_R_PAREN || prev == TK_R_SQUARE) { return true; }
            depth++;
        }
        if k == TK_R_PAREN || k == TK_R_SQUARE || k == TK_R_BRACE { depth--; }
        if k == TK_KW + KW_NEW || k == TK_KW + KW_THROW || k == TK_KW + KW_TYPEID || k == TK_KW + KW_DYNAMIC_CAST { return true; }
        prev = k;
        n++;
        i++;
        if n > 10000 { return true; }
    }
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
