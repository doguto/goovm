// goosecc D3: new and delete expressions in code generation, as clang
// emits them (CGExprCXX.cpp EmitCXXNewExpr / EmitCXXDeleteExpr, the
// Itanium array cookie of ItaniumCXXABI.cpp):
//
//   new T(args)     ({ T *p = (T *)operator new(sizeof(T) [, align] [, placement...]);
//                      { [EH only: operator delete(p, ...)] <init *p>; } p; })
//   new T[n]        the size n * sizeof(T) (+ the cookie), -1 when it overflows
//                   or n is negative (operator new throws bad_alloc); a
//                   cookie (Itanium 2.7: the count, before the elements)
//                   when T has a non-trivial destructor or the usual
//                   operator delete[] takes the size; the elements
//                   initialized in order, the constructed ones destroyed
//                   (in reverse) if one throws
//   nothrow new     null-checked (when the type is not POD or there is an
//                   initializer); reserved placement new: no call
//   delete p        ({ T *q = p; if (q) { q->~T(); operator delete(q [, sizeof(T)] [, align]); } })
//                   a virtual destructor: the deleting destructor (D0) through the vtable
//   delete[] p      the elements destroyed from the last, then operator
//                   delete[](p - cookie [, size])
//
// The allocation and deallocation functions: the class's (unless ::new
// / ::delete), else the global ones; aligned forms (std::align_val_t) for
// types with new-extended alignment (> 16); the usual deallocation function
// ([expr.delete]p10: at class scope the one without std::size_t, globally
// the sized one for complete types, for arrays only with a cookie).

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

let NEW_ALIGN = 16;        // __STDCPP_DEFAULT_NEW_ALIGNMENT__ (x86-64)

// std::align_val_t (0 when <new> was not included).
var alv_type: u32 = 0;
var alv_done = false;
fn align_val_type() -> u32 {
    if alv_done { return alv_type; }
    alv_done = true;
    let st = ns_lookup(0, id_std, true);
    if st < 0 { return 0; }
    let ns = sym_scope(st);
    if ns < 0 { return 0; }
    let s = resolve(ns_lookup(ns, intern("align_val_t"), false));
    if s < 0 || kind_of(syms[s].ty) != TY_ENUM { return 0; }
    alv_type = unqual(syms[s].ty);
    return alv_type;
}

// The global operator new / new[] / delete / delete[] declarations (op),
// implicitly declared ([basic.stc.dynamic]p2) when no header did.
fn global_alloc_chain(op: i64) -> i64 {
    implicit_alloc_decls();
    return scope_find(0, op_ids[op]);
}

var implicit_alloc_done = false;
fn implicit_alloc_decls() {
    if implicit_alloc_done { return; }
    implicit_alloc_done = true;
    implicit_alloc(OP_NEW, t_voidptr, t_size, 0, false);
    implicit_alloc(OP_NEW_ARR, t_voidptr, t_size, 0, false);
    implicit_alloc(OP_DELETE, t_void, t_voidptr, 0, true);
    implicit_alloc(OP_DELETE_ARR, t_void, t_voidptr, 0, true);
    implicit_alloc(OP_DELETE, t_void, t_voidptr, t_size, true);
    implicit_alloc(OP_DELETE_ARR, t_void, t_voidptr, t_size, true);
}

fn implicit_alloc(op: i64, ret: u32, p0: u32, p1: u32, noexc: bool) {
    if scope_find(0, op_ids[op]) >= 0 {
        // only what is missing: an existing declaration of the same type wins
        var s = scope_find(0, op_ids[op]);
        while s >= 0 {
            let f = resolve(s);
            if f >= 0 && syms[f].kind as i64 == SK_FUNC {
                let ft = types[syms[f].ty >> 4];
                if ft.n == (if p1 != 0 { 2 } else { 1 }) { return; }
            }
            s = cxs[s].nnext as i64;
        }
    }
    fn_scratch.clear();
    fn_scratch.push(p0);
    if p1 != 0 { fn_scratch.push(p1); }
    let ft = qt(mk_type(TY_FUNC, 0, ret, 0, 0, 0) as i64, 0);
    let s = csym(SK_FUNC, op_ids[op], ft, 0);
    syms[s].sc = SC_EXTERN as! u8;
    syms[s].flags = SF_FILESCOPE;
    cxs[s].flags = (CF_OPERATOR | (if noexc { CF_NOEXCEPT } else { 0 })) as! u32;
    cxs[s].op = op as! u8;
    cxs[s].dscope = 0;
    scope_add(0, s);
}

// The allocation (or deallocation) functions: the class's when it declares
// some (in it or its bases), unless `global`.
fn alloc_chain(cls: u32, op: i64, global: bool) -> i64 {
    if !global && cls != 0 && is_record(cls) && !is_opaque(cls) {
        let sc = type_scope(cls);
        if sc >= 0 {
            let s = class_lookup(sc, op_ids[op]);
            if s >= 0 { return s; }
        }
    }
    return global_alloc_chain(op);
}

// Is f the reserved placement form operator new(size_t, void *) /
// new[](size_t, void *) (or delete(void *, void *)) of the global namespace?
fn reserved_placement(f: i64) -> bool {
    if cxs[f].dscope > 0 { return false; }
    let ft = types[syms[f].ty >> 4];
    if ft.n != 2 { return false; }
    let p1 = tparams[ft.extra + 1];
    return is_pointer(p1) && is_void(tbase(p1));
}

// A usual deallocation function of chain s ([basic.stc.dynamic.deallocation]):
// (void *[, std::size_t][, std::align_val_t]); with a size when `sized`
// is preferred (the other one when there is only that), aligned when
// `aligned` (falling back to the unaligned ones). Returns the function and
// what it takes (1: size, 2: alignment), or -1.
fn usual_dealloc(s0: i64, sized: bool, aligned: bool) -> i64, i64 {
    let at = align_val_type();
    var best: i64 = -1;
    var best_k: i64 = 0;
    var best_score: i64 = -1;
    var s = s0;
    while s >= 0 {
        let f = resolve(s);
        s = cxs[s].nnext as i64;
        if f < 0 || syms[f].kind as i64 != SK_FUNC || cxs[f].flags & CF_DELETED != 0 { continue; }
        let ft = types[syms[f].ty >> 4];
        if ft.n < 1 || ft.n > 3 || ft.flags & TF_VARIADIC != 0 { continue; }
        if !is_pointer(tparams[ft.extra]) || !is_void(tbase(tparams[ft.extra])) { continue; }
        var k: i64 = 0;
        var ok = true;
        var i = 1;
        while i < ft.n {
            let p = unqual(tparams[ft.extra + i]);
            if p == t_size && k == 0 && i == 1 { k = k | 1; }
            else if at != 0 && p == at && k & 2 == 0 { k = k | 2; }
            else { ok = false; }
            i++;
        }
        if !ok { continue; }
        var score: i64 = 0;
        if (k & 2 != 0) == aligned { score = score + 4; }
        if (k & 1 != 0) == sized { score = score + 2; }
        if score > best_score { best = f; best_k = k; best_score = score; }
    }
    if best >= 0 && !aligned && best_k & 2 != 0 { return -1, 0; }
    return best, best_k;
}

// The deallocation function matching a placement allocation function `nf`
// (the same parameter types after the first), or -1.
fn placement_dealloc(s0: i64, nf: i64) -> i64 {
    let nt = types[syms[nf].ty >> 4];
    var s = s0;
    while s >= 0 {
        let f = resolve(s);
        s = cxs[s].nnext as i64;
        if f < 0 || syms[f].kind as i64 != SK_FUNC { continue; }
        let ft = types[syms[f].ty >> 4];
        if ft.n != nt.n || ft.flags & TF_VARIADIC != (nt.flags & TF_VARIADIC) { continue; }
        var same = true;
        for i in 1..ft.n { if unqual(tparams[ft.extra + i]) != unqual(tparams[nt.extra + i]) { same = false; } }
        if same { return f; }
    }
    return -1;
}

// The call of deallocation function df (takes: 1 size, 2 alignment) for
// pointer value p (void *), size value sz (or 0), alignment al.
fn dealloc_call(df: i64, takes: i64, p: u32, sz: u32, al: i64, loc: u32) -> u32 {
    let mark = nscratch.len;
    nscratch.push(p);
    if takes & 1 != 0 { nscratch.push(if sz != 0 { sz } else { int_node(0, t_size, loc) }); }
    if takes & 2 != 0 { nscratch.push(int_node(al, align_val_type(), loc)); }
    return lower_call(df, 0, mark, loc, false);
}

// A value as size_t.
fn size_v(e: u32, loc: u32) -> u32 { assign_convert(rv(e), t_size, loc, 1) }

// new-expression: type t (the element type of new T[count] when count !=
// 0), initializer init (has_init: (args) or {args} was written), placement
// arguments `place` (an N_INITBRACE list, 0 none), ::new when global.
recursive fn cg_new2(t0: u32, count: u32, init: u32, has_init: bool, loc: u32, place: u32, global: bool) -> u32 {
    let t = unqual(t0);
    if is_opaque(t) || is_ref(t) || is_func(t) || (is_record(t) && !is_complete(t)) { return opaque_node(loc); }
    if count != 0 && (is_opq(count) || !(is_integer(nodes[count].ty) || kind_of(nodes[count].ty) == TY_ENUM)) { return opaque_node(loc); }
    let arr = count != 0;
    let bt = unqual(base_elem_t(t));
    let cls = if is_record(bt) { bt } else { 0 };
    let es = type_size(t);
    let per = if es > 0 && type_size(bt) > 0 { es / type_size(bt) } else { 1 };   // base elements per element
    let al = type_align(t);
    let aligned = al > NEW_ALIGN && align_val_type() != 0;
    let nop = if arr { OP_NEW_ARR } else { OP_NEW };
    let chain = alloc_chain(cls, nop, global);
    if chain < 0 { return opaque_node(loc); }
    let np = if place != 0 { nodes[place].c as i64 } else { 0 };
    // the allocation function: with the alignment first when over-aligned
    var nf: i64 = -1;
    var pass_align = false;
    for attempt in 2 {
        if attempt == 0 && !aligned { continue; }
        let mark = nscratch.len;
        nscratch.push(int_node(0, t_size, loc));
        if attempt == 0 { nscratch.push(int_node(al, align_val_type(), loc)); }
        for i in np { nscratch.push(nlist[nodes[place].v + i]); }
        let f = best_candidate(chain, mark, false);
        nscratch.resize(mark);
        if f >= 0 { nf = f; pass_align = attempt == 0; break; }
    }
    if nf < 0 { return opaque_node(loc); }
    let reserved = np == 1 && reserved_placement(nf);
    // the deallocation function for the cleanup and the cookie
    let dop = if arr { OP_DELETE_ARR } else { OP_DELETE };
    let dchain = alloc_chain(cls, dop, global);
    var df: i64 = -1;
    var dtakes: i64 = 0;
    let class_scope_dealloc = dchain >= 0 && cxs[dchain].dscope > 0;
    if dchain >= 0 && !reserved {
        if np == 0 {
            // usual: at class scope without size; globally sized (arrays: with a cookie, decided below)
            let f, k = usual_dealloc(dchain, !class_scope_dealloc, pass_align);
            df = f;
            dtakes = k;
        } else if np > 0 {
            df = placement_dealloc(dchain, nf);
            dtakes = 0;
        }
    }
    // the cookie: a destructed element type, or a usual operator delete[] taking the size
    var cookie: i64 = 0;
    if arr && !reserved {
        var want = cls != 0 && class_dtor(rec_of(cls)) >= 0;
        if !want && np == 0 && df >= 0 && dtakes & 1 != 0 && class_scope_dealloc { want = true; }
        if want {
            cookie = 8;
            let ea = type_align(bt);
            if ea > cookie { cookie = ea; }
        }
    }
    if arr && np == 0 && !class_scope_dealloc && dchain >= 0 && !reserved {
        // global array delete: sized only with a cookie
        let f, k = usual_dealloc(dchain, cookie != 0, pass_align);
        df = f;
        dtakes = k;
    }
    let pt = mk_ptr(t);
    let mark = nscratch.len;
    // the element count (arrays) and the size
    var ns: i64 = -1;
    var sz: u32 = 0;
    var const_n: i64 = -1;
    if arr {
        let ok, v = const_int(count);
        if ok && v >= 0 && !is_unsigned_type_and_huge(count, v) { const_n = v; }
        // a signed count: its own slot first (negative: the size overflows)
        let ct = promoted_type_of(unqual(nodes[count].ty));
        var cs: i64 = -1;
        if !is_unsigned_int_type(ct) {
            cs = csym(SK_VAR, intern("__count_v"), ct, loc);
            syms[cs].scope = 1;
            nscratch.push(node(N_DECL, 0, ct, cs, assign_convert(rv(count), ct, loc, 1) as i64, loc as i64, loc));
        }
        ns = csym(SK_VAR, intern("__count"), t_size, loc);
        syms[ns].scope = 1;
        let cv = if cs >= 0 { size_v(n_var(cs, loc), loc) } else { size_v(count, loc) };
        nscratch.push(node(N_DECL, 0, t_size, ns, cv as i64, loc as i64, loc));
        count_signed_slot = cs;
        if const_n >= 0 {
            sz = int_node(const_n * es + cookie, t_size, loc);
        } else {
            // n > (SIZE_MAX - cookie) / es (a negative signed n too): -1
            let um: u64 = 0xFFFFFFFFFFFFFFFF;
            let mx: u64 = (um - (cookie as u64)) / (if es > 0 { es as u64 } else { 1 });
            let maxn = mx as! i64;
            var over = node(N_BINARY, B_GT, t_int, rv(n_var(ns, loc)) as i64, int_node(maxn, t_size, loc) as i64, 0, loc);
            let cs = count_signed_slot;
            if cs >= 0 {
                let neg = node(N_BINARY, B_LT, t_int, rv(n_var(cs, loc)) as i64, int_node(0, syms[cs].ty, loc) as i64, 0, loc);
                over = node(N_BINARY, B_LOR, t_int, neg as i64, over as i64, 0, loc);
            }
            let prod = node(N_BINARY, B_MUL, t_size, rv(n_var(ns, loc)) as i64, int_node(es, t_size, loc) as i64, 0, loc);
            let total = if cookie != 0 { node(N_BINARY, B_ADD, t_size, prod as i64, int_node(cookie, t_size, loc) as i64, 0, loc) } else { prod };
            sz = node(N_COND, 0, t_size, over as i64, int_node(-1, t_size, loc) as i64, total as i64, loc);
        }
    } else {
        sz = int_node(es, t_size, loc);
    }
    // the allocation: void *raw = operator new(size [, align] [, placement])
    let raw = csym(SK_VAR, intern("__new_raw"), t_voidptr, loc);
    syms[raw].scope = 1;
    var rawv: u32 = 0;
    if reserved {
        rawv = conv_value(nlist[nodes[place].v], t_voidptr, loc);
    } else {
        let am = nscratch.len;
        nscratch.push(sz);
        if pass_align { nscratch.push(int_node(al, align_val_type(), loc)); }
        for i in np { nscratch.push(nlist[nodes[place].v + i]); }
        rawv = lower_call(nf, 0, am, loc, false);
    }
    if is_opq(rawv) { nscratch.resize(mark); return opaque_node(loc); }
    nscratch.push(node(N_DECL, 0, t_voidptr, raw, node(N_ICAST, CK_BITCAST, t_voidptr, rawv as i64, 0, 0, loc) as i64, loc as i64, loc));
    // the result
    let res = csym(SK_VAR, intern("__new_tmp"), pt, loc);
    syms[res].scope = 1;
    // null-checked: a non-throwing allocation function (not the reserved placement one)
    let nothrow_alloc = !reserved && fn_nothrow(nf);
    let pod = !(cls != 0 && (needs_default_init(rec_of(cls)) || class_dtor(rec_of(cls)) >= 0));
    let null_check = nothrow_alloc && (!pod || has_init);
    nscratch.push(node(N_DECL, 0, pt, res, node(N_ICAST, CK_NULL2PTR, pt, int_node(0, t_int, loc) as i64, 0, 0, loc) as i64, loc as i64, loc));
    let bm = nscratch.len;
    // [EH only: operator delete(raw, ...)] while the object is initialized
    if df >= 0 && new_init_may_throw(t, init, has_init, arr) {
        var dc: u32 = 0;
        if np > 0 {
            let dm = nscratch.len;
            nscratch.push(rv(n_var(raw, loc)));
            for i in np { nscratch.push(nlist[nodes[place].v + i]); }
            dc = lower_call(df, 0, dm, loc, false);
        } else {
            var szv: u32 = 0;
            if dtakes & 1 != 0 {
                if arr && const_n >= 0 { szv = int_node(const_n * es + cookie, t_size, loc); }
                else if arr { szv = node(N_BINARY, B_ADD, t_size, node(N_BINARY, B_MUL, t_size, rv(n_var(ns, loc)) as i64, int_node(es, t_size, loc) as i64, 0, loc) as i64, int_node(cookie, t_size, loc) as i64, 0, loc); }
                else { szv = int_node(es, t_size, loc); }
            }
            dc = dealloc_call(df, dtakes, rv(n_var(raw, loc)), szv, al, loc);
        }
        if is_opq(dc) { nscratch.resize(mark); return opaque_node(loc); }
        nscratch.push(node(N_XPUSH, XP_STMT | XP_EHONLY, 0, n_expr_stmt(dc) as i64, 0, 0, loc));
    }
    // the cookie, then the object(s)
    var objp: u32 = 0;
    if cookie != 0 {
        let cp = node(N_ICAST, CK_BITCAST, mk_ptr(t_char), rv(n_var(raw, loc)) as i64, 0, 0, loc);
        let cnt_at = node(N_BINARY, B_PTRADD, mk_ptr(t_char), cp as i64, int_node(cookie - 8, t_long, loc) as i64, 0, loc);
        let slot = n_deref(node(N_ICAST, CK_BITCAST, mk_ptr(t_size), cnt_at as i64, 0, 0, loc), loc);
        let total = node(N_BINARY, B_MUL, t_size, rv(n_var(ns, loc)) as i64, int_node(per, t_size, loc) as i64, 0, loc);
        nscratch.push(n_expr_stmt(node(N_ASSIGN, 0, t_size, slot as i64, total as i64, 0, loc)));
        let cp2 = node(N_ICAST, CK_BITCAST, mk_ptr(t_char), rv(n_var(raw, loc)) as i64, 0, 0, loc);
        objp = node(N_BINARY, B_PTRADD, mk_ptr(t_char), cp2 as i64, int_node(cookie, t_long, loc) as i64, 0, loc);
    } else {
        objp = rv(n_var(raw, loc));
    }
    nscratch.push(n_expr_stmt(node(N_ASSIGN, 0, pt, n_var(res, loc) as i64, node(N_ICAST, CK_BITCAST, pt, objp as i64, 0, 0, loc) as i64, 0, loc)));
    var ok = true;
    if arr {
        ok = new_array_init(res, ns, const_n, t, per, init, has_init, loc);
    } else {
        let obj = n_deref(rv(n_var(res, loc)), loc);
        var st: u32 = 0;
        if !has_init {
            if cls != 0 { st = construct_at(obj, nscratch.len, loc); if st == 0 { ok = false; } }
        } else {
            var x = init;
            if x != 0 && nodes[x].kind as i64 == N_CTOR && nodes[x].op != 2 && cls != 0 {
                // new T(args): the constructor
                let cm = nscratch.len;
                for i in nodes[x].c as i64 { nscratch.push(nlist[nodes[x].v + i]); }
                st = construct_at(obj, cm, loc);
                if st != 0 && nodes[x].c == 0 && !has_user_ctor(rec_of(cls)) {
                    let zm = nscratch.len;
                    nscratch.push(n_expr_stmt(node(N_ASSIGN, 0, t, obj as i64, node(N_ZEROINIT, 0, t, 0, 0, 0, loc) as i64, 0, loc)));
                    nscratch.push(st);
                    st = n_block(zm, loc);
                }
            } else if x != 0 && nodes[x].kind as i64 == N_CTOR && nodes[x].op == 2 {
                let ib = node_v(N_INITBRACE, 0, t, 0, 0, nodes[x].c as i64, loc, nodes[x].v);
                st = member_init(obj, ib, 0, loc);
            } else if x == 0 || nodes[x].kind as i64 == N_ZEROINIT {
                st = member_init(obj, 0, 0, loc);
            } else if nodes[x].kind as i64 == N_INITBRACE && !is_record(t) && nodes[x].c == 1 {
                st = member_init(obj, nlist[nodes[x].v], 0, loc);
            } else if nodes[x].kind as i64 == N_INITBRACE && !is_record(t) && nodes[x].c == 0 {
                st = member_init(obj, 0, 0, loc);
            } else {
                st = member_init(obj, x, 0, loc);
            }
            if st == 0 { ok = false; }
        }
        if st != 0 { nscratch.push(st); }
    }
    if !ok { nscratch.resize(mark); return opaque_node(loc); }
    let initb = n_block(bm, loc);
    if null_check {
        nscratch.push(node(N_IF, 0, 0, icast(rv(n_var(raw, loc)), CK_PTR2BOOL, t_bool) as i64, initb as i64, 0, loc));
    } else {
        nscratch.push(initb);
    }
    nscratch.push(n_expr_stmt(rv(n_var(res, loc))));
    let body = n_block(mark, loc);
    return node(N_STMTEXPR, 0, pt, body as i64, 0, 0, loc);
}

fn is_unsigned_type_and_huge(e: u32, v: i64) -> bool { is_unsigned_int_type(nodes[e].ty) && v < 0 }
fn is_unsigned_int_type(t: u32) -> bool { is_integer(t) && !is_signed(unqual(t)) }

var count_signed_slot: i64 = -1;     // the signed count's slot of the new-expression being built

// May the initialization of a new-expression's object throw (so that the
// operator delete cleanup matters)?
fn new_init_may_throw(t: u32, init: u32, has_init: bool, arr: bool) -> bool {
    let bt = base_elem_t(t);
    if is_record(bt) { return true; }
    if !has_init || init == 0 { return false; }
    return !is_pod_init(init);
}
fn is_pod_init(e: u32) -> bool {
    let k = nodes[e].kind as i64;
    return k == N_INT || k == N_ZEROINIT || k == N_FLOAT || (k == N_INITBRACE && nodes[e].c == 0);
}

// The elements of new T[n] at res (count in slot ns, const_n when
// constant, per base elements in each): statements to nscratch.
recursive fn new_array_init(res: i64, ns: i64, const_n: i64, t: u32, per: i64, init: u32, has_init: bool, loc: u32) -> bool {
    let bt = unqual(base_elem_t(t));
    let cls = is_record(bt);
    let pb = mk_ptr(bt);
    // the base elements: (bt *)res, total = n * per
    let total_s = csym(SK_VAR, intern("__total"), t_size, loc);
    syms[total_s].scope = 1;
    nscratch.push(node(N_DECL, 0, t_size, total_s, node(N_BINARY, B_MUL, t_size, rv(n_var(ns, loc)) as i64, int_node(per, t_size, loc) as i64, 0, loc) as i64, loc as i64, loc));
    // the list's elements (per element of the first dimension: only one-dimensional lists)
    var nlist_el: i64 = 0;
    var lst: u32 = 0;
    if has_init && init != 0 && nodes[init].kind as i64 == N_INITBRACE && nodes[init].c > 0 {
        if per != 1 { return false; }
        lst = init;
        nlist_el = nodes[init].c as i64;
    }
    if has_init && init != 0 && nodes[init].kind as i64 == N_CTOR && nodes[init].c > 0 { return false; }
    if nlist_el > 0 && const_n >= 0 && const_n < nlist_el { return false; }
    if nlist_el > 0 && const_n < 0 {
        // fewer elements than the list: std::bad_array_new_length
        let bad = rt_fn("__cxa_throw_bad_array_new_length", t_void, 0, 0, 0, 0, false, true);
        let bm = nscratch.len;
        let c = n_expr_stmt(rt_call(bad, bm, loc));
        let lt = node(N_BINARY, B_LT, t_int, rv(n_var(ns, loc)) as i64, int_node(nlist_el, t_size, loc) as i64, 0, loc);
        nscratch.push(node(N_IF, 0, 0, lt as i64, c as i64, 0, loc));
    }
    let base = node(N_ICAST, CK_BITCAST, pb, rv(n_var(res, loc)) as i64, 0, 0, loc);
    let bs = csym(SK_VAR, intern("__elems"), pb, loc);
    syms[bs].scope = 1;
    nscratch.push(node(N_DECL, 0, pb, bs, base as i64, loc as i64, loc));
    // __i: the elements constructed so far (their destruction if one throws)
    let i = csym(SK_VAR, intern("__i"), t_size, loc);
    syms[i].scope = 1;
    nscratch.push(node(N_DECL, 0, t_size, i, int_node(0, t_size, loc) as i64, loc as i64, loc));
    if cls && class_dtor(rec_of(bt)) >= 0 {
        // EH only: while (__i) __elems[--__i].~T();
        let el = node(N_INDEX, 0, bt, rv(n_var(bs, loc)) as i64, node(N_UNARY, U_PREDEC, t_size, n_var(i, loc) as i64, 0, 0, loc) as i64, 0, loc);
        nodes[el].flags = NF_LVALUE;
        let d = destroy_stmt(el, loc);
        if d == 0 { return false; }
        let w = node(N_WHILE, 0, 0, icast(rv(n_var(i, loc)), CK_INT2BOOL, t_bool) as i64, d as i64, 0, loc);
        nscratch.push(node(N_XPUSH, XP_STMT | XP_EHONLY, 0, w as i64, 0, 0, loc));
    }
    // the listed elements
    for k in nlist_el {
        let el = node(N_INDEX, 0, bt, rv(n_var(bs, loc)) as i64, rv(n_var(i, loc)) as i64, 0, loc);
        nodes[el].flags = NF_LVALUE;
        let st = member_init(el, nlist[nodes[lst].v + k], 0, loc);
        if st == 0 { return false; }
        nscratch.push(st);
        nscratch.push(n_expr_stmt(node(N_UNARY, U_PREINC, t_size, n_var(i, loc) as i64, 0, 0, loc)));
    }
    // the rest: default-initialized (no initializer) or value-initialized
    let value = has_init;
    if !cls {
        if value {
            // memset(&elems[i], 0, (total - i) * sizeof(T))
            let ms = libc_memset();
            let am = nscratch.len;
            let at = node(N_BINARY, B_PTRADD, pb, rv(n_var(bs, loc)) as i64, rv(n_var(i, loc)) as i64, 0, loc);
            nscratch.push(node(N_ICAST, CK_BITCAST, t_voidptr, at as i64, 0, 0, loc));
            nscratch.push(int_node(0, t_int, loc));
            let left = node(N_BINARY, B_SUB, t_size, rv(n_var(total_s, loc)) as i64, rv(n_var(i, loc)) as i64, 0, loc);
            nscratch.push(node(N_BINARY, B_MUL, t_size, left as i64, int_node(type_size(bt), t_size, loc) as i64, 0, loc));
            nscratch.push(n_expr_stmt(n_call(ms, am, loc)));
        }
        return true;
    }
    if !value && !needs_default_init(rec_of(bt)) { return true; }
    let el = node(N_INDEX, 0, bt, rv(n_var(bs, loc)) as i64, rv(n_var(i, loc)) as i64, 0, loc);
    nodes[el].flags = NF_LVALUE;
    var st: u32 = 0;
    if value { st = member_init(el, 0, 0, loc); }
    else { st = construct_at(el, nscratch.len, loc); }
    if st == 0 { return false; }
    // for (; __i < __total; ++__i) <init elems[__i]>
    let bm = nscratch.len;
    nscratch.push(st);
    let body = n_block(bm, loc);
    let cond = node(N_BINARY, B_LT, t_int, rv(n_var(i, loc)) as i64, rv(n_var(total_s, loc)) as i64, 0, loc);
    let inc = node(N_UNARY, U_PREINC, t_size, n_var(i, loc) as i64, 0, 0, loc);
    nscratch.push(node_v(N_FOR, 0, 0, 0, cond as i64, inc as i64, loc, body as i64));
    return true;
}

// obj.~T / p->~T: bound to its call (N_CXX op 9, a = the object, a glvalue).
recursive fn cg_dtor_ref(base: u32, arrow: bool, loc: u32) -> u32 {
    var obj = base;
    if arrow {
        let p = rv(base);
        if !is_pointer(nodes[p].ty) { return opaque_node(loc); }
        obj = n_deref(p, loc);
    }
    return node(N_CXX, 9, t_void, obj as i64, 0, 0, loc);
}

// (obj.~T)(): the destructor (complete object, virtual when it is), or
// nothing for a scalar (a pseudo-destructor call).
recursive fn cg_dtor_call(b: u32, mark: i64, loc: u32) -> u32 {
    let obj = nodes[b].a;
    if nscratch.len != mark { nscratch.resize(mark); return opaque_node(loc); }
    let t = nodes[obj].ty;
    if !is_record(t) {
        if is_opaque(t) { return opaque_node(loc); }
        return node(N_CAST, CK_TOVOID, t_void, obj as i64, 0, 0, loc);
    }
    if !is_complete(t) { return opaque_node(loc); }
    let d = class_dtor(rec_of(t));
    if d < 0 { return node(N_CAST, CK_TOVOID, t_void, n_addr(obj, loc) as i64, 0, 0, loc); }
    return lower_call(d, obj, mark, loc, true);
}

// delete p / delete[] p (::delete when global).
recursive fn cg_delete2(p0: u32, arr: bool, loc: u32, global: bool) -> u32 {
    if is_opq(p0) || !is_pointer(nodes[p0].ty) { return opaque_node(loc); }
    let pt = unqual(nodes[p0].ty);
    let t = unqual(tbase(pt));
    if is_void(t) || is_func(t) || is_opaque(t) || (is_record(t) && !is_complete(t)) { return opaque_node(loc); }
    let bt = unqual(base_elem_t(t));
    let cls = if is_record(bt) { bt } else { 0 };
    var dtor: i64 = -1;
    if cls != 0 { dtor = class_dtor(rec_of(cls)); }
    let es = type_size(t);
    let al = type_align(t);
    let aligned = al > NEW_ALIGN && align_val_type() != 0;
    let virt = !arr && dtor >= 0 && dtor_is_virtual(dtor);
    let dop = if arr { OP_DELETE_ARR } else { OP_DELETE };
    let dchain = alloc_chain(cls, dop, global);
    if dchain < 0 { return opaque_node(loc); }
    let class_scope = cxs[dchain].dscope > 0;
    // the cookie (delete[]): as for the new-expression
    var cookie: i64 = 0;
    if arr {
        var want = cls != 0 && dtor >= 0;
        if !want && class_scope {
            let f, k = usual_dealloc(dchain, false, aligned);
            if f >= 0 && k & 1 != 0 { want = true; }
        }
        if want {
            cookie = 8;
            let ea = type_align(bt);
            if ea > cookie { cookie = ea; }
        }
    }
    let sized_pref = if arr { cookie != 0 && !class_scope } else { !class_scope };
    let df, dtakes = usual_dealloc(dchain, sized_pref, aligned);
    if df < 0 && !virt { return opaque_node(loc); }
    // ({ T *q = p; if (q) { ... } })
    let s = csym(SK_VAR, intern("__delete_tmp"), pt, loc);
    syms[s].scope = 1;
    let mark = nscratch.len;
    nscratch.push(node(N_DECL, 0, pt, s, p0 as i64, loc as i64, loc));
    let im = nscratch.len;
    if virt && !global {
        // the deleting destructor, through the vtable
        let dcls = scope_class_type(cxs[dtor].dscope as i64);
        let th = obj_addr_as(n_deref(rv(n_var(s, loc)), loc), dcls, 0, loc);
        if th == 0 { nscratch.resize(mark); return opaque_node(loc); }
        let fp = vfunc_ptr(dtor, th, 1, loc);
        if fp == 0 { nscratch.resize(mark); return opaque_node(loc); }
        let am = nscratch.len;
        nscratch.push(obj_addr_as(n_deref(rv(n_var(s, loc)), loc), dcls, 0, loc));
        nscratch.push(n_expr_stmt(n_call_ptr(fp, am, loc)));
    } else if virt {
        // ::delete: the complete object (offset to top), its destructor
        // through the vtable, then the global operator delete
        let cp = node(N_ICAST, CK_BITCAST, mk_ptr(t_char), rv(n_var(s, loc)) as i64, 0, 0, loc);
        let ot = vtable_entry(rv(n_var(s, loc)), -2, t_long, loc);
        let whole = csym(SK_VAR, intern("__delete_obj"), t_voidptr, loc);
        syms[whole].scope = 1;
        nscratch.push(node(N_DECL, 0, t_voidptr, whole, node(N_ICAST, CK_BITCAST, t_voidptr, node(N_BINARY, B_PTRADD, mk_ptr(t_char), cp as i64, ot as i64, 0, loc) as i64, 0, 0, loc) as i64, loc as i64, loc));
        let dcls = scope_class_type(cxs[dtor].dscope as i64);
        let th = obj_addr_as(n_deref(rv(n_var(s, loc)), loc), dcls, 0, loc);
        let fp = if th != 0 { vfunc_ptr(dtor, th, 0, loc) } else { 0 };
        if fp == 0 || df < 0 { nscratch.resize(mark); return opaque_node(loc); }
        let am = nscratch.len;
        nscratch.push(obj_addr_as(n_deref(rv(n_var(s, loc)), loc), dcls, 0, loc));
        nscratch.push(n_expr_stmt(n_call_ptr(fp, am, loc)));
        let dc = dealloc_call(df, dtakes, rv(n_var(whole, loc)), int_node(es, t_size, loc), al, loc);   // (clang: the static type's size)
        if is_opq(dc) { nscratch.resize(mark); return opaque_node(loc); }
        nscratch.push(n_expr_stmt(dc));
    } else if arr {
        // the elements from the last, then operator delete[](p - cookie [, size])
        let pb = mk_ptr(bt);
        let raw = csym(SK_VAR, intern("__delete_raw"), t_voidptr, loc);
        syms[raw].scope = 1;
        let cp = node(N_ICAST, CK_BITCAST, mk_ptr(t_char), rv(n_var(s, loc)) as i64, 0, 0, loc);
        let rp = if cookie != 0 { node(N_BINARY, B_PTRSUB, mk_ptr(t_char), cp as i64, int_node(cookie, t_long, loc) as i64, 0, loc) } else { cp };
        nscratch.push(node(N_DECL, 0, t_voidptr, raw, node(N_ICAST, CK_BITCAST, t_voidptr, rp as i64, 0, 0, loc) as i64, loc as i64, loc));
        var cnt: i64 = -1;
        if cookie != 0 {
            cnt = csym(SK_VAR, intern("__count"), t_size, loc);
            syms[cnt].scope = 1;
            let cp2 = node(N_ICAST, CK_BITCAST, mk_ptr(t_char), rv(n_var(s, loc)) as i64, 0, 0, loc);
            let at = node(N_BINARY, B_PTRSUB, mk_ptr(t_char), cp2 as i64, int_node(8, t_long, loc) as i64, 0, loc);
            let v = rv(n_deref(node(N_ICAST, CK_BITCAST, mk_ptr(t_size), at as i64, 0, 0, loc), loc));
            nscratch.push(node(N_DECL, 0, t_size, cnt, v as i64, loc as i64, loc));
        }
        if dtor >= 0 && cnt >= 0 {
            // EH: operator delete[] if a destructor throws (destructors are noexcept: no code)
            let i = csym(SK_VAR, intern("__i"), t_size, loc);
            syms[i].scope = 1;
            nscratch.push(node(N_DECL, 0, t_size, i, rv(n_var(cnt, loc)) as i64, loc as i64, loc));
            let el = node(N_INDEX, 0, bt, node(N_ICAST, CK_BITCAST, pb, rv(n_var(s, loc)) as i64, 0, 0, loc) as i64,
                node(N_UNARY, U_PREDEC, t_size, n_var(i, loc) as i64, 0, 0, loc) as i64, 0, loc);
            nodes[el].flags = NF_LVALUE;
            let d = destroy_stmt(el, loc);
            if d == 0 { nscratch.resize(mark); return opaque_node(loc); }
            nscratch.push(node(N_WHILE, 0, 0, icast(rv(n_var(i, loc)), CK_INT2BOOL, t_bool) as i64, d as i64, 0, loc));
        }
        var szv: u32 = 0;
        if dtakes & 1 != 0 && cnt >= 0 {
            let per = if type_size(bt) > 0 { 1 } else { 1 };
            szv = node(N_BINARY, B_ADD, t_size, node(N_BINARY, B_MUL, t_size, rv(n_var(cnt, loc)) as i64, int_node(type_size(bt) * per, t_size, loc) as i64, 0, loc) as i64,
                int_node(cookie, t_size, loc) as i64, 0, loc);
        }
        let dc = dealloc_call(df, dtakes, rv(n_var(raw, loc)), szv, al, loc);
        if is_opq(dc) { nscratch.resize(mark); return opaque_node(loc); }
        nscratch.push(n_expr_stmt(dc));
    } else {
        let vp = node(N_ICAST, CK_BITCAST, t_voidptr, rv(n_var(s, loc)) as i64, 0, 0, loc);
        let dc = dealloc_call(df, dtakes, vp, int_node(es, t_size, loc), al, loc);
        if is_opq(dc) { nscratch.resize(mark); return opaque_node(loc); }
        if dtor >= 0 {
            // operator delete runs even if the destructor throws (EH only)
            let dm = nscratch.len;
            nscratch.push(node(N_XPUSH, XP_STMT | XP_EHONLY, 0, n_expr_stmt(dc) as i64, 0, 0, loc));
            let am = nscratch.len;
            let c = lower_call(dtor, n_deref(rv(n_var(s, loc)), loc), am, loc, false);
            if is_opq(c) { nscratch.resize(mark); return opaque_node(loc); }
            nscratch.push(n_expr_stmt(c));
            let ib = n_block(dm, loc);
            nscratch.push(ib);
            let vp2 = node(N_ICAST, CK_BITCAST, t_voidptr, rv(n_var(s, loc)) as i64, 0, 0, loc);
            let dc2 = dealloc_call(df, dtakes, vp2, int_node(es, t_size, loc), al, loc);
            nscratch.push(n_expr_stmt(dc2));
        } else {
            nscratch.push(n_expr_stmt(dc));
        }
    }
    let then = n_block(im, loc);
    nscratch.push(node(N_IF, 0, 0, icast(rv(n_var(s, loc)), CK_PTR2BOOL, t_bool) as i64, then as i64, 0, loc));
    let body = n_block(mark, loc);
    return node(N_STMTEXPR, 0, t_void, body as i64, 0, 0, loc);
}
