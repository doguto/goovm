// goosecc D3: thread_local variables (Itanium 3.3.6, as clang emits them):
//
//   - a namespace-scope thread_local with dynamic initialization or a
//     destructor is initialized per thread by __tls_init (internal; once per
//     thread: the __tls_guard byte), which constructs it and registers its
//     destructor with __cxa_thread_atexit; _ZTH<name> is an alias of
//     __tls_init
//   - every thread_local with external linkage defined here has a wrapper
//     _ZTW<name> (weak_odr hidden): it calls _ZTH<name> when the variable
//     has dynamic initialization (an extern one's: when _ZTH<name>, a weak
//     reference, is defined) and returns its address; a use of a
//     thread_local that may need dynamic initialization or destruction (or
//     is defined elsewhere) goes through the wrapper
//   - a block-scope thread_local with dynamic initialization: a guard byte
//     of its own (thread_local, _ZGV...), no locking

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
import .cx_gen_eh;

var tls_stmts: u32[>..] = [];                // __tls_init's statements, in order
var tls_dyn = dictionary<u64, u8> {};        // namespace-scope thread_locals with dynamic init / destructors
var tls_wrap = dictionary<u64, u32> {};      // variable -> its wrapper
var tls_wrappers: u32[>..] = [];              // (variable, wrapper) pairs, for their names
var tls_th = dictionary<u64, u32> {};        // variable -> its _ZTH symbol
var tls_init_fn: i64 = -1;
var tls_guard: i64 = -1;
var cxa_thread_atexit: i64 = -1;

// The registration of variable s's destructor for this thread.
fn thread_atexit_stmt(s: i64, loc: u32) -> u32 {
    let d = if is_array(syms[s].ty) { arr_dtor_fn(syms[s].ty, loc) } else { complete_sym(class_dtor(rec_of(syms[s].ty))) };
    if cxa_thread_atexit < 0 {
        let vfp = mk_ptr(fn_type1(t_void, t_voidptr));
        fn_scratch.clear();
        fn_scratch.push(vfp);
        fn_scratch.push(t_voidptr);
        fn_scratch.push(t_voidptr);
        let ft = qt(mk_type(TY_FUNC, 0, t_int, 0, 0, 0) as i64, 0);
        cxa_thread_atexit = csym(SK_FUNC, intern("__cxa_thread_atexit"), ft, loc);
        cxs[cxa_thread_atexit].flags = CF_EXTERN_C;
        rt_nothrow.push(cxa_thread_atexit as! u32);
    }
    let dh = dso_handle_sym(loc);
    let mark = nscratch.len;
    let vfp = mk_ptr(fn_type1(t_void, t_voidptr));
    nscratch.push(node(N_ICAST, CK_BITCAST, vfp, icast(n_ref_fn(d, loc), CK_FUNC2PTR, mk_ptr(abi_type(d))) as i64, 0, 0, loc));
    nscratch.push(node(N_ICAST, CK_BITCAST, t_voidptr, n_addr(tls_direct(s, loc), loc) as i64, 0, 0, loc));
    nscratch.push(node(N_ICAST, CK_BITCAST, t_voidptr, n_addr(n_var(dh, loc), loc) as i64, 0, 0, loc));
    return n_expr_stmt(n_call(cxa_thread_atexit, mark, loc));
}

// A reference to thread_local s itself (not through its wrapper).
fn tls_direct(s: i64, loc: u32) -> u32 {
    let n = n_var(s, loc);
    nodes[n].c = 1;
    return n;
}

// A namespace-scope thread_local's dynamic initialization (statement st,
// 0 none) and its destructor's registration.
fn tls_push(s: i64, st: u32, dtor: bool, loc: u32) {
    if st != 0 { tls_stmts.push(st); }
    if dtor { tls_stmts.push(thread_atexit_stmt(s, loc)); }
    tls_dyn.insert(s as u64, 1);
}

// Does a use of thread_local s go through its wrapper?
fn tls_use_wrapper(s: i64) -> bool {
    if syms[s].flags & SF_THREAD == 0 || syms[s].flags & SF_FILESCOPE == 0 || syms[s].scope > 0 && cxs[s].flags & CF_MEMBER == 0 { return false; }
    if syms[s].sc as i64 == SC_STATIC || (cxs[s].dscope > 0 && in_anon_ns(cxs[s].dscope as i64)) { return false; }
    if syms[s].flags & SF_DEFINED == 0 { return true; }
    return tls_dyn.contains(s as u64);
}

// The wrapper of thread_local s (made on first use).
fn tls_wrapper(s: i64, loc: u32) -> i64 {
    let g = tls_wrap.get(s as u64);
    if g { return g as i64; }
    let pt = mk_ptr(syms[s].ty);
    fn_scratch.clear();
    let ft = qt(mk_type(TY_FUNC, 0, pt, 0, 0, 0) as i64, 0);
    let w = csym(SK_FUNC, intern("__tls_wrapper"), ft, loc);
    syms[w].flags = SF_FILESCOPE | SF_DEFINED;
    cxs[w].flags = CF_IMPLICIT | CF_NOEXCEPT;
    cxs[w].dscope = 0;
    tls_wrap.insert(s as u64, w as! u32);
    lam_fns.insert(w as u64, 1);
    tls_wrappers.push(s as! u32);
    tls_wrappers.push(w as! u32);
    let mark = nscratch.len;
    let defined = syms[s].flags & SF_DEFINED != 0;
    if !defined || tls_dyn.contains(s as u64) {
        // _ZTH<name>: __tls_init's alias here, a weak reference for an extern one
        let th = csym(SK_FUNC, intern("__tls_init_ref"), fn_type0(t_void), loc);
        syms[th].flags = SF_FILESCOPE;
        cxs[th].flags = CF_IMPLICIT;
        cxs[th].dscope = 0;
        tls_th.insert(s as u64, th as! u32);
        lam_fns.insert(th as u64, 1);
        let cm = nscratch.len;
        let call = n_expr_stmt(n_call(th, cm, loc));
        if defined {
            syms[th].flags = syms[th].flags | SF_DEFINED;
            nscratch.push(call);
        } else {
            syms[th].sc = SC_EXTERN as! u8;
            syms[th].flags = syms[th].flags | SF_WEAK;
            let fp = icast(n_ref_fn(th, loc), CK_FUNC2PTR, mk_ptr(abi_type(th)));
            nscratch.push(node(N_IF, 0, 0, icast(fp, CK_PTR2BOOL, t_bool) as i64, call as i64, 0, loc));
        }
    }
    nscratch.push(node(N_RETURN, 0, pt, n_addr(tls_direct(s, loc), loc) as i64, 0, 0, loc));
    let body = n_block(mark, loc);
    let fd = node_v(N_FUNCDEF, 0, ft, w, body as i64, 0, loc, 0);
    syms[w].def = fd as! i32;
    cg_extra.push(fd);
    cxl_grow();
    set_link(w, LK_WEAKODR, CXL_COMDAT | CXL_HIDDEN);
    return w;
}

// A use of thread_local s (an N_DECLREF n): through its wrapper when needed.
fn tls_use(n: u32) {
    let s = nodes[n].a as i64;
    if nodes[n].c == 1 || !tls_use_wrapper(s) { return; }
    let w = tls_wrapper(s, nodes[n].loc);
    let m = nscratch.len;
    let c = n_call(w, m, nodes[n].loc);
    let d = n_deref(c, nodes[n].loc);
    nodes[d].flags = nodes[n].flags & ~(NF_REFDEREF as! u16);
    nodes[n] = nodes[d];
}

// After the unit is parsed: __tls_init, the wrappers of the thread_locals
// with external linkage defined here.
fn tls_finish() {
    if tls_stmts.len > 0 && tls_init_fn < 0 {
        let loc: u32 = 0;
        tls_guard = csym(SK_VAR, intern("__tls_guard"), t_char, loc);
        syms[tls_guard].flags = SF_FILESCOPE | SF_DEFINED | SF_THREAD;
        syms[tls_guard].sc = SC_STATIC as! u8;
        cxs[tls_guard].flags = CF_IMPLICIT | CF_EXTERN_C;
        cg_extra.push(node(N_DECL, 0, t_char, tls_guard, 0, 0, loc));
        lam_fns.insert(tls_guard as u64, 1);
        tls_init_fn = csym(SK_FUNC, intern("__tls_init"), fn_type0(t_void), loc);
        syms[tls_init_fn].flags = SF_DEFINED;
        syms[tls_init_fn].sc = SC_STATIC as! u8;
        cxs[tls_init_fn].flags = CF_IMPLICIT | CF_EXTERN_C;
        lam_fns.insert(tls_init_fn as u64, 1);     // (named __tls_init, not mangled)
        // if (!__tls_guard) { __tls_guard = 1; inits }
        let mark = nscratch.len;
        let gv = tls_direct(tls_guard, loc);
        nscratch.push(n_expr_stmt(node(N_ASSIGN, 0, t_char, gv as i64, int_node(1, t_char, loc) as i64, 0, loc)));
        for x in tls_stmts { nscratch.push(x); }
        let then = n_block(mark, loc);
        let bm = nscratch.len;
        let test = node(N_BINARY, B_EQ, t_int, icast(rv(tls_direct(tls_guard, loc)), CK_INTEGRAL, t_int) as i64, int_node(0, t_int, loc) as i64, 0, loc);
        nscratch.push(node(N_IF, 0, 0, test as i64, then as i64, 0, loc));
        let body = n_block(bm, loc);
        let fd = node_v(N_FUNCDEF, 0, syms[tls_init_fn].ty, tls_init_fn, body as i64, 0, loc, 0);
        syms[tls_init_fn].def = fd as! i32;
        cg_extra.push(fd);
    }
    // the wrappers of the external thread_locals defined here
    for s in 1..syms.len {
        if syms[s].kind as i64 != SK_VAR || syms[s].flags & (SF_THREAD | SF_DEFINED | SF_FILESCOPE) != (SF_THREAD | SF_DEFINED | SF_FILESCOPE) { continue; }
        if s >= cxs.len || (syms[s].scope > 0 && cxs[s].flags & CF_MEMBER == 0) || s == tls_guard { continue; }
        if syms[s].sc as i64 == SC_STATIC || (cxs[s].dscope > 0 && in_anon_ns(cxs[s].dscope as i64)) { continue; }
        if cxs[s].flags & CF_IMPLICIT != 0 { continue; }
        tls_wrapper(s, syms[s].loc);
    }
    // _ZTH<name> of the ones initialized here: aliases of __tls_init
    for i in 0..tls_wrappers.len / 2 {
        let s = tls_wrappers[2 * i] as i64;
        let w = tls_wrappers[2 * i + 1] as i64;
        let g = tls_th.get(s as u64);
        if !g || syms[s].flags & SF_DEFINED == 0 || tls_init_fn < 0 { continue; }
        cxl_grow();
        cxl[g].alias = tls_init_fn as! i32;
        cxl[g].flags = cxl[g].flags | (CXL_OWNLINK as! u8);
        note_cx_use(w, tls_init_fn);
    }
}

// The names of the wrappers and _ZTH symbols (after name_syms):
// _ZTW / _ZTH <the variable's name>.
fn name_tls() {
    for i in 0..tls_wrappers.len / 2 {
        let s = tls_wrappers[2 * i] as i64;
        let w = tls_wrappers[2 * i + 1] as i64;
        var vn: u8[>..] = [];
        let ai = syms[s].attr;
        if ai != 0 && sym_attrs[ai].asm_len != 0 {
            let o = sym_attrs[ai].asm_label as i64;
            let lab = strbytes[o..o + sym_attrs[ai].asm_len as i64];
            if lab.len >= 2 && lab[0] == '_' && lab[1] == 'Z' { vn.append(lab[2..]); } else { format(vn, lab.len); vn.append(lab); }
        } else {
            let nm = ident_text(syms[s].name as i64);
            format(vn, nm.len);
            vn.append(nm);
        }
        var wn: u8[>..] = [];
        wn.append("_ZTW");
        wn.append(vn);
        set_label(w, wn);
        let g = tls_th.get(s as u64);
        if g {
            var hn: u8[>..] = [];
            hn.append("_ZTH");
            hn.append(vn);
            set_label(g as i64, hn);
        }
    }
}
