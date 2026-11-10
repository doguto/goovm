// goosecc D3: the special members of classes for code generation: which
// copy and move constructors, assignment operators and destructors a class
// has (user-declared or implicit, C++ [class.copy]), which are trivial, and
// whether the class is passed and returned by invisible reference (clang's
// canPassInRegisters for the Itanium ABI). The implicit ones that are not
// trivial are defined when used (linkonce_odr, as clang emits them).

namespace cx;

import std;
import dictionary;
import .common;
import .types;
import .ast;
import .sema;
import .cx_core;
import .cx_layout;
import .cx_gen_defs;

// SmInfo.flags
let SM_DONE = 1;
let SM_TRIV_COPY = 2;       // the copy constructor is trivial
let SM_TRIV_MOVE = 4;       // the move constructor (or the copy constructor used for moves) is trivial
let SM_TRIV_CASG = 8;       // copy assignment trivial
let SM_TRIV_MASG = 16;      // move assignment trivial
let SM_TRIV_DTOR = 32;
let SM_HAS_MOVE = 64;       // a move constructor is declared (user or implicit)
let SM_HAS_MASG = 128;      // a move assignment is declared (user or implicit)
let SM_COPY_DEL = 256;      // the copy constructor is deleted (implicitly or explicitly)
let SM_MOVE_DEL = 512;
let SM_INDIRECT = 1024;     // passed and returned by invisible reference
let SM_BUSY = 2048;

struct SmInfo { flags: u32, copy: i32, move: i32, casg: i32, masg: i32 }
var sminfo: SmInfo[>..] = [];

fn sm_grow(r: i64) {
    while sminfo.len <= r { sminfo.push(SmInfo { flags: 0, copy: -1, move: -1, casg: -1, masg: -1 }); }
}

// Is the first parameter of f a reference to class cls (kind: 1 lvalue
// reference, 2 rvalue reference), with defaults for the rest?
fn first_param_ref(f: i64, cls: u32) -> i64 {
    let ft = types[syms[f].ty >> 4];
    if ft.n < 1 { return 0; }
    let p0 = tparams[ft.extra];
    if !is_ref(p0) || unqual(tbase(p0)) != unqual(cls) { return 0; }
    if !defaults_from(f, 1) { return 0; }
    return if kind_of(p0) == TY_RREF { 2 } else { 1 };
}

// Does the special member f count as user-provided (not implicit, not
// defaulted on its first declaration)?
fn user_provided(f: i64) -> bool { cxs[f].flags & (CF_IMPLICIT | CF_DEFAULTED) == 0 }

// The facts of class r.
recursive fn sm(r: i64) -> SmInfo {
    sm_grow(r);
    if sminfo[r].flags & SM_DONE != 0 || sminfo[r].flags & SM_BUSY != 0 { return sminfo[r]; }
    sminfo[r].flags = SM_BUSY;
    let cls = records[r].ty << 4;
    let sc = crecs[r].scope as i64;
    var copy: i64 = -1;
    var move: i64 = -1;
    var casg: i64 = -1;
    var masg: i64 = -1;
    var copy_del = false;
    var move_del = false;
    var casg_del = false;
    var masg_del = false;
    // the user-declared ones
    var s = scope_find(sc, id_ctor);
    while s >= 0 {
        let f = resolve(s);
        if f >= 0 && syms[f].kind as i64 == SK_FUNC && cxs[f].flags & CF_IMPLICIT == 0 {
            let k = first_param_ref(f, cls);
            if k == 1 && copy < 0 { copy = f; copy_del = cxs[f].flags & CF_DELETED != 0; }
            if k == 2 && move < 0 { move = f; move_del = cxs[f].flags & CF_DELETED != 0; }
        }
        s = cxs[s].nnext as i64;
    }
    s = scope_find(sc, op_ids[OP_EQUAL]);
    while s >= 0 {
        let f = resolve(s);
        if f >= 0 && syms[f].kind as i64 == SK_FUNC && cxs[f].flags & CF_IMPLICIT == 0 && types[syms[f].ty >> 4].n == 1 {
            let p0 = tparams[types[syms[f].ty >> 4].extra];
            if is_ref(p0) && unqual(tbase(p0)) == unqual(cls) {
                if kind_of(p0) == TY_RREF { if masg < 0 { masg = f; masg_del = cxs[f].flags & CF_DELETED != 0; } }
                else if casg < 0 { casg = f; casg_del = cxs[f].flags & CF_DELETED != 0; }
            } else if unqual(p0) == unqual(cls) && casg < 0 {
                // operator=(X): a copy assignment
                casg = f;
            }
        }
        s = cxs[s].nnext as i64;
    }
    let dt = scope_find(sc, id_dtor);
    var udtor: i64 = -1;
    if dt >= 0 {
        let f = resolve(dt);
        if f >= 0 && syms[f].kind as i64 == SK_FUNC && cxs[f].flags & CF_IMPLICIT == 0 { udtor = f; }
    }
    // implicit declarations ([class.copy.ctor]p8, [class.copy.assign]p4)
    let has_move = move >= 0 || (copy < 0 && casg < 0 && masg < 0 && udtor < 0);
    let has_masg = masg >= 0 || (copy < 0 && casg < 0 && move < 0 && udtor < 0);
    if copy < 0 && (move >= 0 || masg >= 0) { copy_del = true; }
    if casg < 0 && (move >= 0 || masg >= 0) { casg_del = true; }
    // triviality ([class.copy.ctor]p11): not user-provided, no virtual
    // functions or bases, and the same for every base and member
    let dynamic = crecs[r].flags & CR_DYNAMIC != 0;
    var sub_copy = true;
    var sub_move = true;
    var sub_casg = true;
    var sub_masg = true;
    var sub_dtor = true;
    var sub_copy_del = false;
    let cr = crecs[r];
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if b.flags & BF_VIRTUAL != 0 { sub_copy = false; sub_move = false; sub_casg = false; sub_masg = false; }
        if !is_record(b.ty) || is_opaque(b.ty) { continue; }
        let bi = sm(rec_of(b.ty));
        if bi.flags & SM_TRIV_COPY == 0 { sub_copy = false; }
        if bi.flags & SM_TRIV_MOVE == 0 { sub_move = false; }
        if bi.flags & SM_TRIV_CASG == 0 { sub_casg = false; }
        if bi.flags & SM_TRIV_MASG == 0 { sub_masg = false; }
        if bi.flags & SM_TRIV_DTOR == 0 { sub_dtor = false; }
        if bi.flags & SM_COPY_DEL != 0 { sub_copy_del = true; }
    }
    let rec = records[r];
    for i in rec.first..rec.first + rec.count {
        let ft = fields[i].ty;
        if is_ref(ft) { sub_casg = false; sub_masg = false; continue; }
        let bt = base_elem_t(ft);
        if !is_record(bt) || is_opaque(bt) { continue; }
        let mi = sm(rec_of(bt));
        if mi.flags & SM_TRIV_COPY == 0 { sub_copy = false; }
        if mi.flags & SM_TRIV_MOVE == 0 { sub_move = false; }
        if mi.flags & SM_TRIV_CASG == 0 { sub_casg = false; }
        if mi.flags & SM_TRIV_MASG == 0 { sub_masg = false; }
        if mi.flags & SM_TRIV_DTOR == 0 { sub_dtor = false; }
        if mi.flags & SM_COPY_DEL != 0 { sub_copy_del = true; }
    }
    if sub_copy_del && copy < 0 { copy_del = true; }
    var f: u32 = SM_DONE;
    if !dynamic && sub_copy && (copy < 0 || !user_provided(copy)) { f = f | SM_TRIV_COPY; }
    if has_move {
        if !dynamic && sub_move && (move < 0 || !user_provided(move)) { f = f | SM_TRIV_MOVE; }
        f = f | SM_HAS_MOVE;
    } else if f & SM_TRIV_COPY != 0 {
        f = f | SM_TRIV_MOVE;
    }
    if !dynamic && sub_casg && (casg < 0 || !user_provided(casg)) { f = f | SM_TRIV_CASG; }
    if has_masg {
        if !dynamic && sub_masg && (masg < 0 || !user_provided(masg)) { f = f | SM_TRIV_MASG; }
        f = f | SM_HAS_MASG;
    } else if f & SM_TRIV_CASG != 0 {
        f = f | SM_TRIV_MASG;
    }
    let virt_dtor = udtor >= 0 && cxs[udtor].flags & CF_VIRTUAL != 0;
    if sub_dtor && (udtor < 0 || !user_provided(udtor)) && !virt_dtor && !dtor_virtual_in_bases(r) { f = f | SM_TRIV_DTOR; }
    if copy_del { f = f | SM_COPY_DEL; }
    if move_del { f = f | SM_MOVE_DEL; }
    // passed by invisible reference unless its copy (or move) constructors
    // and destructor are all trivial or deleted, with one not deleted
    var direct = f & SM_TRIV_DTOR != 0;
    if direct {
        var any = false;
        if !copy_del { if f & SM_TRIV_COPY == 0 { direct = false; } any = true; }
        if has_move && !move_del { if f & SM_TRIV_MOVE == 0 { direct = false; } any = true; }
        if !any { direct = false; }
    }
    if !direct { f = f | SM_INDIRECT; }
    sminfo[r] = SmInfo { flags: f, copy: copy as! i32, move: move as! i32, casg: casg as! i32, masg: masg as! i32 };
    return sminfo[r];
}

fn sm_flag(r: i64, m: u32) -> bool { sm(r).flags & m != 0 }

// Is class type t passed and returned by invisible reference?
fn pass_indirect(t: u32) -> bool {
    if !is_record(t) || is_opaque(t) { return false; }
    let r = rec_of(t);
    if r >= crecs.len || crecs[r].flags & CR_LAYOUT == 0 { return false; }
    return sm_flag(r, SM_INDIRECT);
}

// ---------------------------------------------------------------------------
// Implicit copy and move constructors and assignment operators (defined
// when used, by synth_body: kinds 4 copy ctor, 5 move ctor, 6 copy
// assignment, 7 move assignment).

var implicit_sm = dictionary<u64, u32> {};

// The implicit special member of kind k of class r (a symbol with its
// C++ type: X(const X&), X(X&&), X& operator=(const X&), X& operator=(X&&)).
fn implicit_special(r: i64, k: i64) -> i64 {
    let key = ((r as u64) << 3) | (k as u64);
    let g = implicit_sm.get(key);
    if g { return g as i64; }
    let cls = records[r].ty << 4;
    let ctor = k == 4 || k == 5;
    let pt = if k == 4 || k == 6 { mk_lref(with_q(cls, Q_CONST)) } else { mk_rref(cls) };
    fn_scratch.clear();
    fn_scratch.push(pt);
    let ret = if ctor { t_void } else { mk_lref(cls) };
    let ft = qt(mk_type(TY_FUNC, 0, ret, 0, 0, 0) as i64, 0);
    let s = csym(SK_FUNC, if ctor { id_ctor } else { op_ids[OP_EQUAL] }, ft, records[r].loc);
    cxs[s].dscope = crecs[r].scope as! i32;
    cxs[s].flags = (CF_MEMBER | CF_IMPLICIT | CF_DEFINED_IN_CLASS | (if ctor { CF_CTOR } else { CF_OPERATOR })) as! u32;
    if !ctor { cxs[s].op = OP_EQUAL as! u8; }
    syms[s].flags = SF_INLINE | SF_DEFINED;
    // its parameter
    let p = csym(SK_VAR, intern("__src"), pt, records[r].loc);
    syms[p].flags = SF_PARAM;
    syms[p].scope = 1;
    implicit_params.insert(s as u64, p as! u32);
    implicit_sm.insert(key, s as! u32);
    pending_bodies.push(s as! u32);
    pending_bodies.push(k as! u32);
    return s;
}
var implicit_params = dictionary<u64, u32> {};

// The constructor that copies (rvalue: moves) an object of class r, or -1
// when it is trivial (a copy of the bytes), -2 when there is none.
fn copy_ctor_of(r: i64, rvalue: bool) -> i64 {
    let i = sm(r);
    if rvalue && i.flags & SM_HAS_MOVE != 0 {
        if i.flags & SM_MOVE_DEL != 0 { return -2; }
        if i.move >= 0 { if user_provided(i.move as i64) { return i.move as i64; } }
        if i.flags & SM_TRIV_MOVE != 0 { return -1; }
        return implicit_special(r, 5);
    }
    if i.flags & SM_COPY_DEL != 0 { return -2; }
    if i.copy >= 0 && user_provided(i.copy as i64) { return i.copy as i64; }
    if i.flags & SM_TRIV_COPY != 0 { return -1; }
    return implicit_special(r, 4);
}

// The assignment operator that copies (rvalue: moves) into class r, or -1
// when it is trivial, -2 when there is none.
fn assign_op_of(r: i64, rvalue: bool) -> i64 {
    let i = sm(r);
    if rvalue && i.flags & SM_HAS_MASG != 0 {
        if i.masg >= 0 && user_provided(i.masg as i64) { return i.masg as i64; }
        if i.flags & SM_TRIV_MASG != 0 { return -1; }
        return implicit_special(r, 7);
    }
    if i.casg >= 0 && user_provided(i.casg as i64) { return i.casg as i64; }
    if i.flags & SM_TRIV_CASG != 0 { return -1; }
    return implicit_special(r, 6);
}

// ---------------------------------------------------------------------------
// The bodies of the implicit copy and move constructors and assignment
// operators (statements to stmt_buf; th: `this`, src: the source object
// (an lvalue), move: moved member by member).

// src's member fi (an lvalue; for a move an xvalue).
fn src_member(src: u32, fi: i64, move: bool, loc: u32) -> u32 {
    let f = fields[fi];
    let n = node(N_MEMBER, 0, nonref(f.ty), src as i64, fi, 0, loc);
    var fl = NF_LVALUE;
    if is_ref(f.ty) { fl = fl | NF_REFDEREF; }
    if f.width >= 0 { fl = fl | NF_BITFIELD; }
    if move && !is_ref(f.ty) { fl = fl | NF_XVALUE; }
    nodes[n].flags = fl as! u16;
    nodes[n].ty = with_q(nodes[n].ty, quals(nodes[src].ty) & Q_CONST);
    return n;
}

// The construction (assign: assignment) of dst from src, both lvalues of
// type t (a class, an array or a scalar): a statement, or 0.
recursive fn copy_into(dst: u32, src: u32, move: bool, assign: bool, loc: u32) -> u32 {
    let t = nodes[dst].ty;
    if is_array(t) {
        // element by element
        let et = tbase(t);
        let n = types[t >> 4].n;
        if n <= 0 { return n_null(loc); }
        let i = csym(SK_VAR, intern("__i"), t_long, loc);
        syms[i].scope = 1;
        let de = node(N_INDEX, 0, et, icast(dst, CK_ARRAY2PTR, mk_ptr(et)) as i64, rv(n_var(i, loc)) as i64, 0, loc);
        nodes[de].flags = NF_LVALUE;
        let se = node(N_INDEX, 0, with_q(et, quals(nodes[src].ty) & Q_CONST), icast(src, CK_ARRAY2PTR, mk_ptr(et)) as i64, rv(n_var(i, loc)) as i64, 0, loc);
        nodes[se].flags = (NF_LVALUE | (if move { NF_XVALUE } else { 0 })) as! u16;
        let body = copy_into(de, se, move, assign, loc);
        if body == 0 { return 0; }
        let init = node(N_DECL, 0, t_long, i, int_node(0, t_long, loc) as i64, loc as i64, loc);
        let cond = node(N_BINARY, B_LT, t_int, rv(n_var(i, loc)) as i64, int_node(n, t_long, loc) as i64, 0, loc);
        let inc = node(N_UNARY, U_PREINC, t_long, n_var(i, loc) as i64, 0, 0, loc);
        return node_v(N_FOR, 0, 0, init as i64, cond as i64, inc as i64, loc, body as i64);
    }
    if is_record(t) && !is_opaque(t) {
        let r = rec_of(t);
        if assign {
            let op = assign_op_of(r, move);
            if op == -2 { return 0; }
            if op == -1 { return n_expr_stmt(node(N_ASSIGN, 0, unqual(t), dst as i64, rv(src) as i64, 0, loc)); }
            let mark = nscratch.len;
            nscratch.push(src);
            let c = lower_call(op, dst, mark, loc, false);
            if is_opq(c) { return 0; }
            return n_expr_stmt(c);
        }
        let mark = nscratch.len;
        nscratch.push(src);
        return construct_at(dst, mark, loc);
    }
    return n_expr_stmt(node(N_ASSIGN, 0, unqual(t), dst as i64, rv(src) as i64, 0, loc));
}

// The implicit copy or move constructor (k 4, 5) or assignment (6, 7) of
// class r: its statements; false when D3 cannot.
recursive fn synth_special(f: i64, k: i64, r: i64, th: i64, loc: u32) -> bool {
    let pg = implicit_params.get(f as u64);
    if !pg { return false; }
    let p = pg as i64;
    let move = k == 5 || k == 7;
    let assign = k == 6 || k == 7;
    let src = n_var(p, loc);       // *__src (a reference parameter)
    let cr = crecs[r];
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if b.flags & BF_VIRTUAL != 0 || !is_record(b.ty) { return false; }
        let dobj = this_base(th, b.ty, loc);
        let sb = derived_to_base_lv(src, unqual(b.ty), loc);
        if dobj == 0 || sb == 0 { return false; }
        nodes[sb].ty = with_q(nodes[sb].ty, quals(nodes[src].ty) & Q_CONST);
        if move { nodes[sb].flags = nodes[sb].flags | NF_XVALUE; }
        let sv = cg_base_variant;
        cg_base_variant = true;
        let st = copy_into(dobj, sb, move, assign, loc);
        cg_base_variant = sv;
        if st == 0 { return false; }
        stmt_buf.push(st);
        if !assign {
            let ds = base_destroy(th, b.ty, loc);
            if ds != 0 { stmt_buf.push(node(N_XPUSH, XP_STMT | XP_EHONLY, 0, ds as i64, 0, 0, loc)); }
        }
    }
    if !assign && crecs[r].flags & CR_DYNAMIC != 0 {
        if !vptr_stores(r, th, loc) { return false; }
    }
    let rec = records[r];
    for i in rec.first..rec.first + rec.count {
        let fd = fields[i];
        if fd.name == 0 && fd.width >= 0 { continue; }     // unnamed bit-field
        if is_ref(fd.ty) {
            if assign { return false; }
            // the reference itself: its pointer
            let dslot = node(N_MEMBER, 0, lower_ty(fd.ty), nodes[this_member(th, r, i, loc)].a as i64, i, 0, loc);
            nodes[dslot].flags = NF_LVALUE;
            let sobj = n_var(p, loc);
            let sslot = node(N_MEMBER, 0, lower_ty(fd.ty), sobj as i64, i, 0, loc);
            nodes[sslot].flags = NF_LVALUE;
            stmt_buf.push(n_expr_stmt(node(N_ASSIGN, 0, lower_ty(fd.ty), dslot as i64, rv(sslot) as i64, 0, loc)));
            continue;
        }
        let dm = this_member(th, r, i, loc);
        let sm2 = src_member(n_var(p, loc), i, move, loc);
        let st = copy_into(dm, sm2, move, assign, loc);
        if st == 0 { return false; }
        stmt_buf.push(st);
        if !assign { member_eh_cleanup(th, r, i, loc); }
    }
    if assign {
        // return *this
        let rt = n_deref(rv(n_var(th, loc)), loc);
        stmt_buf.push(node(N_RETURN, 0, types[syms[f].ty >> 4].base, n_addr(rt, loc) as i64, 0, 0, loc));
    }
    return true;
}

// ---------------------------------------------------------------------------
// The return slot of functions returning a class by invisible reference,
// and the named return value optimization (clang's Sema::computeNRVO
// through Scope::updateNRVOCandidate / applyNRVO, as gen_stmt.goose does
// for C): a local variable that every return statement in its scope
// returns lives in the return slot; a flag set by the return keeps it from
// being destroyed then.

var fn_ret = dictionary<u64, u32> {};      // function -> its return slot parameter
var cg_ret: i64 = -1;                       // the one of the function being parsed
var nrvo_flags = dictionary<u64, u32> {};  // NRVO variable -> its flag
var ret_fns: u32[>..] = [];

fn make_ret(f: i64, rt: u32, loc: u32) -> i64 {
    let g = fn_ret.get(f as u64);
    if g { return g as i64; }
    let p = csym(SK_VAR, intern("__ret"), mk_ptr(unqual(rt)), loc);
    syms[p].flags = SF_PARAM;
    syms[p].scope = 1;
    fn_ret.insert(f as u64, p as! u32);
    ret_fns.push(f as! u32);
    return p;
}

// The local variable (or parameter) of class ct that x names, or -1.
fn local_of(x: u32, ct: u32) -> i64 {
    if nodes[x].kind as i64 != N_DECLREF || !is_lvalue(x) { return -1; }
    let s = nodes[x].a as i64;
    if syms[s].kind as i64 != SK_VAR || is_ref(syms[s].ty) { return -1; }
    if syms[s].flags & (SF_FILESCOPE | SF_COMPLIT | SF_THREAD) != 0 { return -1; }
    if syms[s].sc as i64 == SC_STATIC || syms[s].sc as i64 == SC_EXTERN { return -1; }
    if s < cxs.len && cxs[s].flags & CF_MEMBER != 0 { return -1; }
    if unqual(syms[s].ty) != unqual(ct) || quals(syms[s].ty) & Q_VOLATILE != 0 { return -1; }
    return s;
}

struct NvS { id: u32, nrvo: i64 }
var nvs: NvS[>..] = [];
struct NvSl { scope: u32, sym: i64, live: bool }
var nvsl: NvSl[>..] = [];
var nvd = dictionary<u64, u32> {};
var nv_id: u32 = 0;
var nv_found: u32[>..] = [];
var nv_pushes: u32[>..] = [];               // the XP_CALL cleanups seen (their variables may be NRVO)

fn nv2_push() {
    nv_id++;
    nvs.push(NvS { id: nv_id, nrvo: -2 });
}

fn nv2_pop() {
    let S = nvs.pop();
    if S.nrvo >= 0 {
        let d = nvd.get(S.nrvo as u64);
        if d && d == S.id { nv_found.push(S.nrvo as! u32); }
    }
    if S.nrvo != -2 && nvs.len > 0 { nvs[nvs.len - 1].nrvo = S.nrvo; }
}

fn nv2_return(e: u32) {
    var vd: i64 = -1;
    if e != 0 && nodes[e].kind as i64 == N_XNRET { vd = nodes[e].a as i64; }
    var can = false;
    var k = nvs.len - 1;
    while k >= 0 {
        let id = nvs[k].id;
        var found = false;
        for i in 0..nvsl.len {
            if nvsl[i].scope != id || !nvsl[i].live { continue; }
            if nvsl[i].sym == vd { found = true; } else { nvsl[i].live = false; }
        }
        can = can || found;
        k--;
    }
    nvs[nvs.len - 1].nrvo = if can { vd } else { -1 };
}

recursive fn nv2_sub(n: u32) {
    if n == 0 { return; }
    if nodes[n].kind as i64 == N_COMPOUND { nv2_walk(n); return; }
    nv2_push();
    nv2_walk(n);
    nv2_pop();
}

recursive fn nv2_walk(n: u32) {
    if n == 0 { return; }
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_COMPOUND {
        nv2_push();
        for i in nd.c as i64 { nv2_walk(nlist[nd.v + i]); }
        nv2_pop();
    } else if k == N_DECL {
        let s = nd.a as i64;
        if syms[s].kind as i64 == SK_VAR && syms[s].flags & SF_PARAM == 0 {
            let id = nvs[nvs.len - 1].id;
            nvsl.push(NvSl { scope: id, sym: s, live: true });
            nvd.insert(s as u64, id);
        }
    } else if k == N_XPUSH {
        if (nd.op as i64) & XP_CALL != 0 { nv_pushes.push(n); }
    } else if k == N_IF {
        nv2_push();
        nv2_sub(nd.b);
        nv2_sub(nd.c);
        nv2_pop();
    } else if k == N_WHILE || k == N_SWITCH {
        nv2_push();
        nv2_sub(nd.b);
        nv2_pop();
    } else if k == N_DO {
        nv2_push();
        nv2_sub(nd.a);
        nv2_pop();
    } else if k == N_FOR {
        nv2_push();
        if nd.a != 0 { nv2_walk(nd.a); }
        nv2_sub(nd.v as! u32);
        nv2_pop();
    } else if k == N_CASE || k == N_DEFAULT {
        nv2_walk(nd.a);
    } else if k == N_LABEL {
        nv2_walk(nd.b);
    } else if k == N_XTRY {
        nv2_sub(nd.a);
        for i in nd.c as i64 { nv2_sub(nodes[nlist[nd.v + i]].b); }
    } else if k == N_RETURN {
        nv2_return(nd.a);
    }
}

// The NRVO variables of function f (defined by fd) returning a class by
// invisible reference: their flags, declared at the top of the body, and
// their destructors made conditional on them.
fn nrvo_function(f: i64, fd: u32) {
    nvs.clear();
    nvsl.clear();
    if nvd.count > 0 { nvd.clear(); }
    nv_found.clear();
    nv_pushes.clear();
    let body = nodes[fd].b;
    if body == 0 { return; }
    nv2_push();
    let bn = nodes[body];
    if bn.kind as i64 == N_COMPOUND { for i in bn.c as i64 { nv2_walk(nlist[bn.v + i]); } } else { nv2_walk(body); }
    nv2_pop();
    if nv_found.len == 0 { return; }
    let loc = nodes[fd].loc;
    let mark = nscratch.len;
    for v in nv_found {
        cxl_grow();
        cxl[v].flags = cxl[v].flags | (CXL_NRVO as! u8);
        let fl = csym(SK_VAR, intern("__nrvo"), t_bool, loc);
        syms[fl].scope = 1;
        nrvo_flags.insert(v as u64, fl as! u32);
        nscratch.push(node(N_DECL, 0, t_bool, fl, int_node(0, t_bool, loc) as i64, loc as i64, loc));
        // the destructor only when it was not returned
        for x in nv_pushes {
            if nodes[x].a != v { continue; }
            let call = n_expr_stmt(dtor_call_of(v as i64, nodes[x].c as i64, loc));
            let test = node(N_UNARY, U_NOT, t_int, to_bool(rv(n_var(fl, loc))) as i64, 0, 0, loc);
            let iff = node(N_IF, 0, 0, test as i64, call as i64, 0, loc);
            nodes[x].op = XP_STMT as! u8;
            nodes[x].a = iff;
        }
    }
    if bn.kind as i64 != N_COMPOUND { nscratch.resize(mark); return; }
    for i in bn.c as i64 { nscratch.push(nlist[bn.v + i]); }
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    nodes[body].v = start;
    nodes[body].c = count as! u32;
}

// d(&v): the call of destructor (or array destructor function) d.
fn dtor_call_of(v: i64, d: i64, loc: u32) -> u32 {
    let mark = nscratch.len;
    if is_this_fn(d) { return lower_call(d, n_var(v, loc), mark, loc, false); }
    nscratch.push(n_addr(n_var(v, loc), loc));
    return n_call(d, mark, loc);
}

// ---------------------------------------------------------------------------
// Aggregate initialization of classes whose members need code (C++
// [dcl.init.aggr]): bases, then members in order, each from its
// initializer or value-initialized; a member already constructed is
// destroyed if a later one throws.

fn is_aggregate_class(r: i64) -> bool {
    if crecs[r].flags & CR_DYNAMIC != 0 { return false; }
    if opt_cxx_std >= 20 { if crecs[r].flags & CR_USER_CTOR != 0 { return false; } }
    else if has_user_ctor(r) { return false; }
    let cr = crecs[r];
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if b.flags & BF_VIRTUAL != 0 || b.access as i64 != AC_PUBLIC { return false; }
        if opt_cxx_std < 17 { return false; }
    }
    let sc = crecs[r].scope as i64;
    let rec = records[r];
    for i in rec.first..rec.first + rec.count {
        let f = fields[i];
        if f.name == 0 { continue; }
        let m = member_sym(sc, f.name);
        if m >= 0 && cxs[m].access as i64 != AC_PUBLIC { return false; }
    }
    return true;
}

// The aggregate initialization of dst (an lvalue of an aggregate class)
// from the initializers nlist[v..v + c): an expression, or 0.
recursive fn agg_init(dst: u32, v: i64, c: i64, loc: u32) -> u32 {
    let t = unqual(nodes[dst].ty);
    let r = rec_of(t);
    let mark = nscratch.len;
    var i: i64 = 0;
    let cr = crecs[r];
    for bi in cr.nbases {
        let b = cbases[cr.bases + bi];
        let obj = derived_to_base_lv(dst, unqual(b.ty), loc);
        if obj == 0 { nscratch.resize(mark); return 0; }
        let x = if i < c { nlist[v + i] } else { 0 };
        i++;
        let st = member_init(obj, x, 0, loc);
        if st == 0 { nscratch.resize(mark); return 0; }
        nscratch.push(st);
        let d = destroy_stmt(obj, loc);
        if d != 0 { nscratch.push(node(N_XPUSH, XP_STMT | XP_EHONLY, 0, d as i64, 0, 0, loc)); }
    }
    let rec = records[r];
    let union = records[r].flags & RF_UNION != 0;
    for fi in rec.first..rec.first + rec.count {
        let f = fields[fi];
        if f.name == 0 && f.width >= 0 { continue; }
        if union && i > 0 { break; }
        let x = if i < c { nlist[v + i] } else { 0 };
        i++;
        if union && x == 0 { break; }
        let lv = node(N_MEMBER, 0, nonref(f.ty), dst as i64, fi, 0, loc);
        var fl = NF_LVALUE;
        if f.width >= 0 { fl = fl | NF_BITFIELD; }
        nodes[lv].flags = fl as! u16;
        let st = member_init(lv, x, if is_ref(f.ty) { f.ty } else { 0 }, loc);
        if st == 0 { nscratch.resize(mark); return 0; }
        nscratch.push(st);
        if is_record(f.ty) || is_array(f.ty) {
            let d = if is_record(f.ty) { destroy_stmt(lv, loc) } else { 0 };
            if d != 0 { nscratch.push(node(N_XPUSH, XP_STMT | XP_EHONLY, 0, d as i64, 0, 0, loc)); }
        }
    }
    let b = n_block(mark, loc);
    return node(N_STMTEXPR, 0, t_void, b as i64, 0, 0, loc);
}

// The initialization of lv (a member or element) from x (0: value-
// initialization; rt: the member's reference type, 0 none): a statement,
// or 0.
recursive fn member_init(lv: u32, x: u32, rt: u32, loc: u32) -> u32 {
    let ft = unqual(nodes[lv].ty);
    if rt != 0 {
        if x == 0 { return 0; }
        let p = conv_arg(x, rt, loc);
        if is_opq(p) { return 0; }
        let slot = node(N_MEMBER, 0, lower_ty(rt), nodes[lv].a as i64, nodes[lv].b as i64, 0, loc);
        nodes[slot].flags = NF_LVALUE;
        return n_expr_stmt(node(N_ASSIGN, 0, lower_ty(rt), slot as i64, p as i64, 0, loc));
    }
    if is_record(ft) && !is_opaque(ft) {
        let r = rec_of(ft);
        if x == 0 || (nodes[x].kind as i64 == N_INITBRACE && nodes[x].c == 0 && !is_aggregate_class(r)) {
            // value-initialization
            let mark = nscratch.len;
            let st = construct_at(lv, mark, loc);
            if st == 0 { return 0; }
            if has_user_ctor(r) { return st; }
            let m = nscratch.len;
            nscratch.push(n_expr_stmt(node(N_ASSIGN, 0, ft, lv as i64, node(N_ZEROINIT, 0, ft, 0, 0, 0, loc) as i64, 0, loc)));
            nscratch.push(st);
            return n_block(m, loc);
        }
        if nodes[x].kind as i64 == N_INITBRACE {
            if c_initializable(ft) {
                let bi = brace_init(ft, x, loc);
                if bi == 0 { return 0; }
                return n_expr_stmt(node(N_ASSIGN, 0, ft, lv as i64, compound_value(bi, ft, loc) as i64, 0, loc));
            }
            if is_aggregate_class(r) {
                let a = agg_init(lv, nodes[x].v, nodes[x].c as i64, loc);
                if a == 0 { return 0; }
                return n_expr_stmt(a);
            }
            let mark = nscratch.len;
            for j in nodes[x].c as i64 { nscratch.push(nlist[nodes[x].v + j]); }
            return construct_at(lv, mark, loc);
        }
        let e = init_into(lv, class_rv(x, ft, loc), loc);
        if e == 0 { return 0; }
        return n_expr_stmt(e);
    }
    if is_array(ft) {
        let et = tbase(ft);
        let n = types[ft >> 4].n;
        if x != 0 && nodes[x].kind as i64 != N_INITBRACE {
            // a string literal for a char array, or a copy
            if c_initializable(ft) && nodes[x].kind as i64 == N_STRING {
                nodes[x].flags = nodes[x].flags | NF_STRINIT;
                nodes[x].ty = ft;
                return n_expr_stmt(node(N_ASSIGN, 0, ft, lv as i64, compound_value(x, ft, loc) as i64, 0, loc));
            }
            return 0;
        }
        let mark = nscratch.len;
        let cnt = if x == 0 { 0 } else { nodes[x].c as i64 };
        for j in n {
            if j >= cnt && !(is_record(base_elem_t(et)) && !is_opaque(base_elem_t(et))) {
                let el0 = node(N_INDEX, 0, et, icast(lv, CK_ARRAY2PTR, mk_ptr(et)) as i64, int_node(j, t_long, loc) as i64, 0, loc);
                nodes[el0].flags = NF_LVALUE;
                if is_array(et) { break; }
                nscratch.push(n_expr_stmt(node(N_ASSIGN, 0, unqual(et), el0 as i64, node(N_ZEROINIT, 0, unqual(et), 0, 0, 0, loc) as i64, 0, loc)));
                continue;
            }
            let el = node(N_INDEX, 0, et, icast(lv, CK_ARRAY2PTR, mk_ptr(et)) as i64, int_node(j, t_long, loc) as i64, 0, loc);
            nodes[el].flags = NF_LVALUE;
            let xi = if j < cnt { nlist[nodes[x].v + j] } else { 0 };
            let st = member_init(el, xi, 0, loc);
            if st == 0 { nscratch.resize(mark); return 0; }
            nscratch.push(st);
        }
        return n_block(mark, loc);
    }
    if x == 0 { return n_expr_stmt(node(N_ASSIGN, 0, ft, lv as i64, node(N_ZEROINIT, 0, ft, 0, 0, 0, loc) as i64, 0, loc)); }
    var e = x;
    if nodes[e].kind as i64 == N_INITBRACE {
        if nodes[e].c == 0 { return n_expr_stmt(node(N_ASSIGN, 0, ft, lv as i64, node(N_ZEROINIT, 0, ft, 0, 0, 0, loc) as i64, 0, loc)); }
        e = nlist[nodes[e].v];
    }
    let val = conv_value(e, ft, loc);
    if is_opq(val) { return 0; }
    return n_expr_stmt(node(N_ASSIGN, 0, ft, lv as i64, val as i64, 0, loc));
}
