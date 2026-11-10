// goosecc D1: the semantics of C++ expressions. Operands of the C
// fundamental and pointer types go through C's checks and conversions
// (expr.goose), with C++'s result types (bool comparisons, const string
// literals); class operands go through overload resolution (cx_over.goose);
// anything opaque gives an opaque node.

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
import .init;
import .cx_core;
import .cx_names;
import .cx_decl;
import .cx_class;
import .cx_tmpl;
import .cx_decl2;
import .cx_expr;

let CAST_C = 0;
let CAST_STATIC = 1;
let CAST_DYNAMIC = 2;
let CAST_REINTERPRET = 3;
let CAST_CONST = 4;
let CAST_FUNCTIONAL = 5;

// Types C's semantic functions handle as C does.
recursive fn cish(t: u32) -> bool {
    let k = kind_of(t);
    if k == TY_POINTER { return cish_ptr(tbase(t)); }
    if k == TY_ARRAY || k == TY_VLA {
        // arrays of classes decay to pointers C handles
        return cish_ptr(tbase(t)) && (cish(tbase(t)) || is_record(tbase(t)));
    }
    if k == TY_FUNC { return true; }
    if k == TY_MEMPTR { return cg_on; }     // code generation: copied, stored and initialized as C values
    return (k >= TY_VOID && k <= TY_COMPLEX) || k == TY_ENUM || k == TY_VECTOR || k == TY_EXTVECTOR;
}
fn cish_ptr(t: u32) -> bool {
    let k = kind_of(t);
    return k != TY_UNKNOWN && !(k >= TY_TPARAM && k <= TY_DEPEXPR) && k != TY_PACKEXP;
}
fn cish_node(n: u32) -> bool { !is_opq(n) && cish(nodes[n].ty) }

fn is_cmp_or_logic(op: i64) -> bool {
    return op == B_LT || op == B_GT || op == B_LE || op == B_GE || op == B_EQ || op == B_NE || op == B_LAND || op == B_LOR;
}

// a op b. op_cx: the OP_* of the operator (for overloading), op_c: C's B_*.
recursive fn mk_binop(op_cx: i64, op_c: i64, l0: u32, r0: u32, loc: u32) -> u32 {
    var l = l0;
    var r = r0;
    if is_opq(l) || is_opq(r) { return dep_node(t_unknown, loc); }
    // (.* is the only binary operator without an OP_ code: C's bin_op maps it to B_REM)
    if cg_on && (op_cx == OP_ARROWSTAR || op_cx == 0) { return cg_memptr_access(l, r, op_cx == OP_ARROWSTAR, loc); }
    if op_cx == OP_ARROWSTAR || op_cx == 0 && op_c == 0 { return dep_node(t_unknown, loc); }
    let tl = nodes[l].ty;
    let tr = nodes[r].ty;
    if is_record(tl) || is_record(tr) || is_scoped_enum_op(tl, tr, op_c) {
        let o = overloaded_binop(op_cx, l, r, loc);
        if o != 0 { return o; }
        if op_c == B_COMMA { return node(N_BINARY, B_COMMA, tr, discard_value(l) as i64, r as i64, 0, loc); }
        // D2: the built-in operator, class operands converted by their conversion functions
        let want = if op_c == B_LAND || op_c == B_LOR { t_bool } else { 0 };
        let l2 = if is_record(tl) { builtin_conv_operand(l, want) } else { l };
        let r2 = if is_record(tr) { builtin_conv_operand(r, want) } else { r };
        if l2 != 0 && r2 != 0 && !is_record(nodes[l2].ty) && !is_record(nodes[r2].ty) { return mk_binop(op_cx, op_c, l2, r2, loc); }
        return dep_node(t_unknown, loc);
    }
    if kind_of(tl) == TY_NULLPTR && kind_of(tr) == TY_NULLPTR { return dep_node(t_bool, loc); }
    if kind_of(tl) == TY_MEMPTR || kind_of(tr) == TY_MEMPTR { return dep_node(t_unknown, loc); }
    if kind_of(tl) == TY_NULLPTR && is_pointer(nonref_decay(tr)) { l = icast(l, CK_NULL2PTR, nonref_decay(tr)); }
    if kind_of(tr) == TY_NULLPTR && is_pointer(nonref_decay(tl)) { r = icast(r, CK_NULL2PTR, nonref_decay(tl)); }
    if !cish_node(l) || !cish_node(r) { return dep_node(t_unknown, loc); }
    if op_c == B_COMMA {
        // C++: the result is the right operand, with its value category
        let n = node(N_BINARY, B_COMMA, nodes[r].ty, discard_value(l) as i64, r as i64, 0, loc);
        nodes[n].flags = nodes[r].flags & (NF_LVALUE | NF_XVALUE | NF_BITFIELD);
        return n;
    }
    if op_c == B_LAND || op_c == B_LOR {
        let a = to_bool(l);
        let b = to_bool(r);
        return node(N_BINARY, op_c, t_bool, a as i64, b as i64, 0, loc);
    }
    let n = mk_binary(op_c, l, r, loc);
    if is_cmp_or_logic(op_c) { nodes[n].ty = t_bool; }
    return n;
}

fn is_scoped_enum_op(a: u32, b: u32, op: i64) -> bool { false }

fn nonref_decay(t: u32) -> u32 {
    let u = nonref(t);
    if is_array(u) { return mk_ptr(tbase(u)); }
    if is_func(u) { return mk_ptr(u); }
    return u;
}

// The contextual conversion to bool (C++ [conv]p4).
recursive fn to_bool(e: u32) -> u32 {
    if is_opq(e) { return e; }
    let r = rv(e);
    let t = nodes[r].ty;
    if kind_of(t) == TY_BOOL { return r; }
    if is_integer(t) { return icast(r, CK_INT2BOOL, t_bool); }
    if is_real_float(t) { return icast(r, CK_FLOAT2BOOL, t_bool); }
    if is_pointer(t) { return icast(r, CK_PTR2BOOL, t_bool); }
    if kind_of(t) == TY_NULLPTR { return int_node(0, t_bool, nodes[e].loc); }
    if cg_on && kind_of(t) == TY_MEMPTR { return cg_memptr_bool(r); }
    if is_record(t) { return conv_to_bool(e); }
    return r;
}

// The condition of if/while/for/?:, converted to bool.
recursive fn cond_cx(e: u32) -> u32 { to_bool(e) }

recursive fn mk_assign_cx(op: i64, l: u32, r: u32, loc: u32, tok: i64) -> u32 {
    if is_opq(l) || is_opq(r) { return dep_node(t_unknown, loc); }
    let tl = nodes[l].ty;
    if is_record(tl) || is_record(nodes[r].ty) || nodes[r].kind as i64 == N_INITBRACE {
        let o = overloaded_assign(op, l, r, loc, tok);
        if o != 0 { return o; }
        if !is_record(tl) && is_record(nodes[r].ty) {
            // D2: a class value assigned to a scalar: its conversion function
            let c = ics_user(r, unqual(tl), CV_COPY, false, false);
            if c.kind as i64 == ICS_USER && c.user >= 0 {
                let x = apply_user_conv(r, c.user as i64, tl);
                if x != 0 && !is_opq(x) { return mk_assign_cx(op, l, x, loc, tok); }
            }
        }
        if is_record(tl) && op == 0 && !cg_on && is_lvalue(l) {
            // D2: the implicit copy or move assignment X& operator=(const X&) / (X&&)
            let c = ics_of(r, mk_lref(with_q(unqual(tl), Q_CONST)), CV_COPY);
            if c.kind as i64 != ICS_BAD && c.flags & IF_UNKNOWN == 0 {
                let n = node(N_CXX, 0, tl, 0, 0, 0, loc);
                nodes[n].flags = NF_LVALUE;
                return n;
            }
        }
        return dep_node(tl, loc);
    }
    var rr = r;
    if kind_of(nodes[r].ty) == TY_NULLPTR && (is_pointer(tl) || kind_of(tl) == TY_MEMPTR) {
        rr = icast(r, CK_NULL2PTR, unqual(tl));
    }
    if !cish_node(l) || !cish_node(rr) { return dep_node(tl, loc); }
    if kind_of(tl) == TY_MEMPTR {
        // code generation: a member pointer stored as a C value
        if op != 0 { return dep_node(tl, loc); }
        let v = conv_value(rr, unqual(tl), loc);
        if is_opq(v) { return dep_node(tl, loc); }
        let n = node(N_ASSIGN, 0, unqual(tl), l as i64, v as i64, 0, loc);
        nodes[n].flags = NF_LVALUE;
        return n;
    }
    if cg_on && op == 0 && is_pointer(tl) {
        let c = cg_ptr_conv(rv(rr), unqual(tl), loc);
        if c != 0 { rr = c; }
    }
    let n = mk_assign(op, l, rr, loc);
    // C++: an assignment is an lvalue (the left operand)
    nodes[n].flags = nodes[n].flags | NF_LVALUE;
    nodes[n].ty = tl;
    return n;
}

recursive fn mk_cond_cx(c: u32, a: u32, b: u32, loc: u32) -> u32 {
    if is_opq(c) || (a != 0 && is_opq(a)) || is_opq(b) { return dep_node(t_unknown, loc); }
    if nodes[b].kind as i64 == N_THROW || (a != 0 && nodes[a].kind as i64 == N_THROW) {
        // one arm throws: the other's type and category
        let other = if nodes[b].kind as i64 == N_THROW { a } else { b };
        if other == 0 || !cish_node(other) { return dep_node(if other == 0 { t_void } else { nodes[other].ty }, loc); }
        let n = node(N_COND, 0, nodes[other].ty, to_bool(c) as i64, (if a == 0 { 0 } else { a }) as i64, b as i64, loc);
        nodes[n].flags = nodes[other].flags & NF_LVALUE;
        return n;
    }
    let ta = if a == 0 { nodes[c].ty } else { nodes[a].ty };
    let tb = nodes[b].ty;
    if is_record(ta) || is_record(tb) {
        if a != 0 && unqual(ta) == unqual(tb) {
            let n = node(N_COND, 0, unqual(ta), to_bool(c) as i64, a as i64, b as i64, loc);
            nodes[n].flags = nodes[a].flags & nodes[b].flags & NF_LVALUE;
            return n;
        }
        return dep_node(t_unknown, loc);
    }
    var aa = a;
    var bb = b;
    if a != 0 && kind_of(ta) == TY_NULLPTR && is_pointer(nonref_decay(tb)) { aa = icast(a, CK_NULL2PTR, nonref_decay(tb)); }
    if kind_of(tb) == TY_NULLPTR && is_pointer(nonref_decay(ta)) { bb = icast(b, CK_NULL2PTR, nonref_decay(ta)); }
    if (aa != 0 && !cish_node(aa)) || !cish_node(bb) || !cish_node(c) { return dep_node(t_unknown, loc); }
    if aa != 0 && is_lvalue(aa) && is_lvalue(bb) && unqual(nodes[aa].ty) == unqual(nodes[bb].ty) && nodes[aa].ty == nodes[bb].ty &&
       !is_array(nodes[aa].ty) && !is_func(nodes[aa].ty) {
        // both lvalues of one type: an lvalue (C++ [expr.cond]p4)
        let n = node(N_COND, 0, nodes[aa].ty, to_bool(c) as i64, aa as i64, bb as i64, loc);
        nodes[n].flags = NF_LVALUE;
        return n;
    }
    if cg_on && aa == 0 && is_lvalue(c) && is_lvalue(bb) && nodes[c].ty == nodes[bb].ty && !is_array(nodes[c].ty) && !is_func(nodes[c].ty) {
        return cg_elvis_lvalue(c, bb, loc);
    }
    let n = mk_cond(if aa == 0 { c } else { to_bool(c) }, aa, bb, loc);
    return n;
}

recursive fn mk_cast_cx(t: u32, e0: u32, loc: u32, kind: i64) -> u32 {
    var e = e0;
    if is_opaque(t) || is_opq(e) {
        if nodes[e].kind as i64 == N_FUNCREF && !is_opaque(t) {
            // a cast of an overload set: the function of the target type
            let c = ics_overload_set(e, t);
            if c.kind as i64 != ICS_BAD { let a = funcref_addr(e, loc); if !is_opq(a) { return mk_cast_cx(t, a, loc, kind); } }
        }
        let n = dep_node(nonref(t), loc);
        if is_ref(t) { nodes[n].flags = nodes[n].flags | NF_LVALUE; }
        return n;
    }
    if kind == CAST_DYNAMIC {
        // the type is known; the run-time check is code generation's
        need_complete(nonref(t));
        if is_pointer(t) { need_complete(tbase(t)); }
        let n = node(N_DYNCAST, 0, nonref(t), e as i64, 0, 0, loc);
        if is_ref(t) { nodes[n].flags = (NF_LVALUE | (if kind_of(t) == TY_RREF { NF_XVALUE } else { 0 })) as! u16; }
        return n;
    }
    let ft = nodes[e].ty;
    if is_ref(t) {
        let to = tbase(t);
        let xv = if kind_of(t) == TY_RREF { NF_XVALUE } else { 0 };
        need_complete(to);
        if is_record(ft) { need_complete(ft); }
        // the same type (cv may be added, or dropped by const_cast / C casts)
        if unqual(ft) == unqual(to) || ((kind == CAST_REINTERPRET || kind == CAST_CONST) && is_lvalue(e)) {
            var x = e;
            if !is_lvalue(e) { x = materialize_rv(e, loc); }
            let n = node(N_CAST, CK_NOOP, to, x as i64, 0, 0, loc);
            nodes[n].flags = (NF_LVALUE | xv) as! u16;
            return n;
        }
        if is_record(to) && is_record(ft) {
            // to a base (any cast), or down to a derived class (static_cast and C casts)
            let up = base_offset(unqual(ft), unqual(to));
            if up >= 0 {
                let c = derived_to_base_lv(e, to, loc);
                if c != 0 { nodes[c].flags = (nodes[c].flags | xv) as! u16; return c; }
            }
            let down = base_offset(unqual(to), unqual(ft));
            if down >= 0 && (kind == CAST_STATIC || kind == CAST_C || kind == CAST_FUNCTIONAL) {
                let n = node_v(N_ICAST, CK_DERIVED2BASE, with_q(unqual(to), quals(to) | quals(ft)), e as i64, 0, 0, loc, 0 - down);
                nodes[n].flags = (NF_LVALUE | xv) as! u16;
                return n;
            }
        }
        if kind == CAST_C && is_lvalue(e) {
            // a C cast to an unrelated reference: reinterpret
            let n = node(N_CAST, CK_NOOP, to, e as i64, 0, 0, loc);
            nodes[n].flags = (NF_LVALUE | xv) as! u16;
            return n;
        }
        // const T& / T&& from a value of another type: a temporary of T
        if (quals(to) & Q_CONST != 0 || xv != 0) && !is_record(to) {
            let v = mk_cast_cx(unqual(to), e, loc, kind);
            if is_opq(v) { return dep_node(to, loc); }
            let n = node(N_CAST, CK_NOOP, to, materialize_rv(v, loc) as i64, 0, 0, loc);
            nodes[n].flags = (NF_LVALUE | xv) as! u16;
            return n;
        }
        return dep_node(to, loc);
    }
    if is_void(t) { return node(N_CAST, CK_TOVOID, t_void, e as i64, 0, 0, loc); }
    if is_record(t) || is_record(ft) {
        need_complete(t);
        if is_record(ft) { need_complete(ft); }
        let o = cast_to_class(t, e, loc);
        if o != 0 { return o; }
        if is_record(ft) && !is_record(t) {
            // a conversion function (explicit ones too: direct-initialization)
            let c = ics_user(e, unqual(t), 0, false, false);
            if c.kind as i64 == ICS_USER && c.user >= 0 {
                let x = apply_user_conv(e, c.user as i64, t);
                if x != 0 && !is_opq(x) { return mk_cast_cx(t, x, loc, kind); }
            }
        }
        return dep_node(t, loc);
    }
    if kind_of(ft) == TY_NULLPTR {
        if is_pointer(t) || kind_of(t) == TY_MEMPTR { return icast(e, CK_NULL2PTR, t); }
        if is_integer(t) || kind_of(t) == TY_BOOL { return int_node(0, t, loc); }
        if kind_of(t) == TY_NULLPTR { return rv_cx(e); }
        return dep_node(t, loc);
    }
    if is_array(ft) || is_func(ft) { e = decay_cx(e); }
    let ft2 = nodes[e].ty;
    // class pointers: to a base or down to a derived class, the offset applied
    if is_pointer(t) && is_pointer(ft2) && is_record(tbase(t)) && is_record(tbase(ft2)) && kind != CAST_REINTERPRET &&
       unqual(tbase(t)) != unqual(tbase(ft2)) {
        let a = unqual(tbase(ft2));
        let b = unqual(tbase(t));
        need_complete(a);
        need_complete(b);
        var off = base_offset(a, b);
        if off < 0 {
            let d = base_offset(b, a);
            if d >= 0 && kind != CAST_CONST { off = 0 - d; }
            else { off = 0; }
        }
        if off != 0 { return ptr_offset_cast(rv_cx(e), unqual(t), off, loc); }
    }
    if kind_of(t) == TY_MEMPTR || kind_of(ft2) == TY_MEMPTR {
        if unqual(t) == unqual(ft2) { return rv_cx(e); }
        return dep_node(t, loc);
    }
    if !cish(t) || !cish_node(e) { return dep_node(t, loc); }
    return mk_cast(unqual(t), e, loc);
}

fn rv_cx(e: u32) -> u32 { if is_lvalue(e) { return rv(e); } return e; }
fn decay_cx(e: u32) -> u32 {
    let t = nodes[e].ty;
    if is_array(t) { return icast(e, CK_ARRAY2PTR, mk_ptr(tbase(t))); }
    if is_func(t) { return icast(e, CK_FUNC2PTR, mk_ptr(t)); }
    return e;
}

// A prvalue as an object (a reference cast binds it).
fn materialize_rv(e: u32, loc: u32) -> u32 {
    if is_lvalue(e) { return e; }
    let t = unqual(nodes[e].ty);
    let s = csym(SK_VAR, 0, t, loc);
    syms[s].flags = SF_COMPLIT;
    if block_fn_depth == 0 { syms[s].sc = SC_STATIC as! u8; syms[s].flags = syms[s].flags | SF_FILESCOPE; }
    let cl = node(N_COMPLIT, 0, t, e as i64, s, 0, loc);
    nodes[cl].flags = NF_LVALUE;
    return cl;
}

// Pointer p (a prvalue) converted to pointer type `to` with off added to
// the address, a null pointer kept:
// ({ T *tmp = p; tmp ? (U *)((char *)tmp + off) : (U *)0; })
fn ptr_offset_cast(p: u32, to: u32, off: i64, loc: u32) -> u32 {
    let ft = unqual(nodes[p].ty);
    let s = csym(SK_VAR, intern("__base_tmp"), ft, loc);
    syms[s].scope = 1;
    let mark = nscratch.len;
    nscratch.push(node(N_DECL, 0, ft, s, p as i64, loc as i64, loc));
    let v = node(N_DECLREF, 0, ft, s, 0, 0, loc);
    nodes[v].flags = NF_LVALUE;
    let cp = node(N_ICAST, CK_BITCAST, mk_ptr(t_char), rv(v) as i64, 0, 0, loc);
    let add = node(N_BINARY, B_PTRADD, mk_ptr(t_char), cp as i64, int_node(off, t_long, loc) as i64, 0, loc);
    let bp = node(N_ICAST, CK_BITCAST, to, add as i64, 0, 0, loc);
    let z = node(N_ICAST, CK_NULL2PTR, to, int_node(0, t_int, loc) as i64, 0, 0, loc);
    let v2 = node(N_DECLREF, 0, ft, s, 0, 0, loc);
    nodes[v2].flags = NF_LVALUE;
    let c = node(N_COND, 0, to, icast(rv(v2), CK_PTR2BOOL, t_bool) as i64, bp as i64, z as i64, loc);
    nscratch.push(node(N_EXPR, 0, 0, c as i64, 0, 0, loc));
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    let body = node_v(N_COMPOUND, 0, 0, 0, 0, count, loc, start);
    return node(N_STMTEXPR, 0, to, body as i64, 0, 0, loc);
}

recursive fn mk_incdec_cx(e: u32, op: i64, loc: u32, pre: bool) -> u32 {
    if is_opq(e) { return dep_node(t_unknown, loc); }
    if is_record(nodes[e].ty) || kind_of(nodes[e].ty) == TY_ENUM && is_scoped_enum(nodes[e].ty) {
        let o = overloaded_unop(if op == U_PREINC || op == U_POSTINC { OP_PLUSPLUS } else { OP_MINUSMINUS }, e, loc, !pre);
        if o != 0 { return o; }
        return dep_node(t_unknown, loc);
    }
    if !cish_node(e) { return dep_node(t_unknown, loc); }
    let n = mk_incdec(e, op, loc);
    if pre { nodes[n].flags = nodes[n].flags | NF_LVALUE; }
    return n;
}

recursive fn mk_addr_cx(e: u32, loc: u32) -> u32 {
    if cg_on {
        let mp = cg_member_addr(e, loc);
        if mp != 0 { return mp; }
    }
    if nodes[e].kind as i64 == N_FUNCREF { return funcref_addr(e, loc); }
    if is_opq(e) { return dep_node(t_unknown, loc); }
    if is_record(nodes[e].ty) {
        let o = overloaded_unop(OP_AMP, e, loc, false);
        if o != 0 { return o; }
    }
    if !is_lvalue(e) { return dep_node(t_unknown, loc); }
    let t = nodes[e].ty;
    let n = node(N_UNARY, U_ADDR, mk_ptr(t), e as i64, 0, 0, loc);
    return n;
}

recursive fn mk_deref_cx(e: u32, loc: u32) -> u32 {
    if is_opq(e) { return dep_node(t_unknown, loc); }
    if is_record(nodes[e].ty) {
        let o = overloaded_unop(OP_STAR, e, loc, false);
        if o != 0 { return o; }
        return dep_node(t_unknown, loc);
    }
    let r = rv(e);
    let t = nodes[r].ty;
    if !is_pointer(t) { return dep_node(t_unknown, loc); }
    if !cish_ptr(tbase(t)) { return dep_node(t_unknown, loc); }
    let n = node(N_UNARY, U_DEREF, tbase(t), r as i64, 0, 0, loc);
    nodes[n].flags = NF_LVALUE;
    return n;
}

recursive fn mk_unary_cx(k: i64, e: u32, loc: u32) -> u32 {
    if is_opq(e) { return dep_node(if k == TK_EXCLAIM { t_bool } else { t_unknown }, loc); }
    if is_record(nodes[e].ty) {
        let op = match k { TK_PLUS => OP_PLUS, TK_MINUS => OP_MINUS, TK_TILDE => OP_TILDE, _ => OP_EXCLAIM };
        let o = overloaded_unop(op, e, loc, false);
        if o != 0 { return o; }
        if k == TK_EXCLAIM { let b = conv_to_bool(e); if b != 0 && !is_opq(b) { return node(N_UNARY, U_NOT, t_bool, b as i64, 0, 0, loc); } }
        let e2 = builtin_conv_operand(e, 0);
        if e2 != 0 && !is_record(nodes[e2].ty) { return mk_unary_cx(k, e2, loc); }
        return dep_node(if k == TK_EXCLAIM { t_bool } else { t_unknown }, loc);
    }
    if k == TK_EXCLAIM {
        let b = to_bool(e);
        if is_opq(b) { return dep_node(t_bool, loc); }
        return node(N_UNARY, U_NOT, t_bool, b as i64, 0, 0, loc);
    }
    if kind_of(nodes[e].ty) == TY_ENUM && is_scoped_enum(nodes[e].ty) { return dep_node(t_unknown, loc); }
    if !cish_node(e) { return dep_node(t_unknown, loc); }
    let op = match k { TK_PLUS => U_PLUS, TK_MINUS => U_NEG, _ => U_BITNOT };
    return mk_unary_arith(op, e, loc);
}

recursive fn mk_sizeof_cx(t0: u32, is_align: bool, loc: u32) -> u32 {
    let t = nonref(t0);
    if is_opaque(t) || t == 0 { return dep_node(t_ulong, loc); }
    need_complete(t);
    if is_record(t) && records[rec_of(t)].size < 0 { return dep_node(t_ulong, loc); }
    if !is_complete(t) && !is_void(t) && !is_func(t) { return dep_node(t_ulong, loc); }
    if is_record(t) || is_array(t) && is_record(base_elem(t)) {
        let v = if is_align { type_align(t) } else { type_size(t) };
        if v < 0 { return dep_node(t_ulong, loc); }
        let n = node_v(N_SIZEOF, if is_align { 1 } else { 0 }, t_ulong, 0, t as i64, 0, loc, v);
        nodes[n].flags = NF_ICE;
        return n;
    }
    return mk_sizeof_type(t, is_align, loc);
}

fn base_elem(t: u32) -> u32 {
    var x = t;
    while is_array(x) { x = tbase(x); }
    return x;
}

recursive fn mk_index_cx(base: u32, idx: u32, loc: u32) -> u32 {
    if is_opq(base) || is_opq(idx) { return dep_node(t_unknown, loc); }
    if is_record(nodes[base].ty) {
        let o = overloaded_subscript(base, idx, loc);
        if o != 0 { return o; }
        return dep_node(t_unknown, loc);
    }
    if !cish_node(base) || !cish_node(idx) { return dep_node(t_unknown, loc); }
    return mk_index(base, idx, loc);
}

fn mk_this(loc: u32) -> u32 {
    if this_type == 0 { return dep_node(t_unknown, loc); }
    if cg_on && cg_this >= 0 { return cg_this_ref(loc); }
    let n = node(N_THIS, 0, this_type, 0, 0, 0, loc);
    if is_opaque(tbase(this_type)) || is_dep(tbase(this_type)) { nodes[n].flags = NF_DEP; }
    return n;
}
var this_type: u32 = 0;     // inside a member function: the type of `this`

// A name used as an expression (it was looked up: s0 is its chain).
recursive fn mk_name_ref(qn: QN&, s0: i64, loc: u32) -> u32 {
    let s = resolve(first_visible(s0));
    if s < 0 { return opaque_node(loc); }
    let k = syms[s].kind as i64;
    if k == SK_VAR {
        let t = syms[s].ty;
        if is_opaque(t) || cxs[s].flags & CF_PATTERN != 0 && dependent_ctx() {
            let n = dep_node(nonref(t), loc);
            nodes[n].flags = nodes[n].flags | NF_LVALUE;
            return n;
        }
        if kind_of(t) == TY_AUTO { return opaque_node(loc); }
        let n = node(N_DECLREF, 0, nonref(t), s, 0, 0, loc);
        nodes[n].flags = (NF_LVALUE | (if is_ref(t) { NF_REFDEREF } else { 0 })) as! u16;
        syms[s].flags = syms[s].flags | SF_USED;
        if cxs[s].flags & CF_MEMBER != 0 && cxs[s].flags & CF_STATIC != 0 { note_static_member_use(s); }
        return n;
    }
    if k == SK_ENUMC {
        if cxs[s].flags & CF_PATTERN != 0 { return dep_node(syms[s].ty, loc); }
        let n = node_v(N_INT, 0, syms[s].ty, 0, 0, 0, loc, syms[s].v);
        nodes[n].flags = NF_ICE;
        return n;
    }
    if k == SK_NTTP {
        if cxs[s].flags & CF_SUBST != 0 { return int_node(syms[s].v, unqual(nonref(syms[s].ty)), loc); }
        let n = dep_node(syms[s].ty, loc);
        nodes[n].op = 2;        // a template parameter (a = its symbol): canonical as an argument
        nodes[n].a = s as! u32;
        return n;
    }
    if k == SK_FUNC || k == SK_TEMPLATE {
        if k == SK_TEMPLATE && tmpl_kind(s) == TT_VAR { return dep_node(t_unknown, loc); }
        let n = node(N_FUNCREF, 0, t_unknown, s0, 0, (if qn.has_targs { qn.targs + 1 } else { 0 }) as i64, loc);
        nodes[n].op = if qn.qual { 1 } else { 0 };
        return n;
    }
    if k == SK_FIELD {
        // a member named in a member function: this->member
        if this_type != 0 && !is_opaque(this_type) {
            let th = mk_this(loc);
            return mk_member_ref(th, true, s, -1, loc);
        }
        // X::m outside a member function: sizeof(X::m), &X::m
        let n = dep_node(nonref(syms[s].ty), loc);
        if cg_on && qn.qual { nodes[n].op = 6; nodes[n].a = s as! u32; }
        return n;
    }
    return opaque_node(loc);
}

fn note_static_member_use(s: i64) { inst_var_use(s); }

// The field index of member symbol s (SK_FIELD).
fn field_index(s: i64) -> i64 {
    let sc = cxs[s].dscope as i64;
    if sc < 0 { return -1; }
    let r = scopes[sc].rec as i64;
    if r < 0 { return -1; }
    return records[r].first as i64 + syms[s].v;
}

// obj.member / ptr->member for a found member chain s.
recursive fn mk_member_ref(base: u32, arrow: bool, s0: i64, targs: i32, loc: u32) -> u32 {
    let s = resolve(first_visible(s0));
    if s < 0 { return opaque_node(loc); }
    let k = syms[s].kind as i64;
    var obj = base;
    if arrow {
        if is_opq(base) || !is_pointer(nodes[rv_maybe(base)].ty) {
            if is_record(nodes[base].ty) && !is_opq(base) {
                // operator->: (base.operator->())->member
                let o = overloaded_arrow(base, loc);
                if o == 0 { return opaque_node(loc); }
                obj = mk_deref_cx(o, loc);
            } else {
                return opaque_node(loc);
            }
        } else {
            obj = mk_deref_cx(base, loc);
        }
    }
    if is_opq(obj) { return opaque_node(loc); }
    if k == SK_FIELD {
        if cxs[s].flags & CF_ANON_PATH != 0 { return dep_node(nonref(syms[s].ty), loc); }
        let fi = field_index(s);
        if fi < 0 { return opaque_node(loc); }
        // the member's class may be a base of the object's class
        let owner = scope_class_type(cxs[s].dscope as i64);
        var o = obj;
        if owner != 0 && unqual(nodes[obj].ty) != owner {
            let c = derived_to_base_lv(obj, owner, loc);
            if c == 0 { return opaque_node(loc); }
            o = c;
        }
        let ft = fields[fi].ty;
        if is_opaque(ft) { return dep_node(nonref(ft), loc); }
        var t = nonref(ft);
        if !is_ref(ft) && cxs[s].flags & CF_MUTABLE == 0 { t = with_q(t, quals(nodes[o].ty) & (Q_CONST | Q_VOLATILE)); }
        let n = node(N_MEMBER, 0, t, o as i64, fi, 0, loc);
        var fl = nodes[o].flags & (NF_LVALUE | NF_XVALUE);
        if is_ref(ft) { fl = NF_LVALUE | NF_REFDEREF; }
        if fields[fi].width >= 0 { fl = fl | NF_BITFIELD; }
        nodes[n].flags = fl;
        return n;
    }
    if k == SK_FUNC || k == SK_TEMPLATE {
        let n = node(N_FUNCREF, 0, t_unknown, s0, obj as i64, (targs + 1) as i64, loc);
        return n;
    }
    if k == SK_VAR {
        let t = syms[s].ty;
        let n = node(N_DECLREF, 0, nonref(t), s, 0, 0, loc);
        nodes[n].flags = (NF_LVALUE | (if is_ref(t) { NF_REFDEREF } else { 0 })) as! u16;
        return n;
    }
    if k == SK_ENUMC { return int_node(syms[s].v, syms[s].ty, loc); }
    return opaque_node(loc);
}

fn rv_maybe(n: u32) -> u32 { n }

// T(args) / T{args}: a functional cast, value-initialization or a
// constructor call.
recursive fn mk_construct(t: u32, mark: i64, loc: u32, braces: bool) -> u32 {
    let n = nscratch.len - mark;
    if is_opaque(t) { return dep_node(t, loc); }
    for i in mark..nscratch.len { if is_opq(nscratch[i]) { return dep_node(t, loc); } }
    if is_record(t) { return construct_class(t, mark, loc, braces); }
    if n == 0 { return node(N_ZEROINIT, 0, unqual(t), 0, 0, 0, loc); }
    if n == 1 {
        let e = nscratch[mark];
        return mk_cast_cx(t, e, loc, CAST_FUNCTIONAL);
    }
    return dep_node(t, loc);
}

// new-expression.
recursive fn parse_new() -> u32 {
    let loc = tloc();
    accept(TK_COLONCOLON);
    adv();      // new
    var placement = false;
    var t: u32 = 0;
    if at(TK_L_PAREN) {
        // ( placement ) or ( type-id )
        let sv = save();
        adv();
        if looks_like_type_id() {
            let tt = parse_type_id();
            if at(TK_R_PAREN) { adv(); t = tt; }
            else { restore(sv); }
        } else { restore(sv); }
        if t == 0 {
            let mark = parse_args();
            nscratch.resize(mark);
            placement = true;
        }
    }
    var count: u32 = 0;
    if t == 0 {
        if at(TK_L_PAREN) {
            adv();
            t = parse_type_id();
            expect(TK_R_PAREN, "')'");
        } else {
            // new-type-id: type-specifiers, ptr-operators, [expr][const]...
            var ds = CDS { .. };
            var a = Attrs { .. };
            parse_cds(ds, a, DC_TYPEID);
            var base = finish_cds(ds);
            if base == 0 { base = t_unknown; }
            var d = CD { .. };
            base = ptr_ops(base, d);
            t = base;
            if at(TK_L_SQUARE) {
                adv();
                count = parse_expr_cx();
                expect(TK_R_SQUARE, "']'");
                while at(TK_L_SQUARE) {
                    adv();
                    let e = parse_cexpr();
                    let ok, v = const_int(e);
                    expect(TK_R_SQUARE, "']'");
                    t = mk_array(t, if ok { v } else { 1 });
                }
            }
        }
    }
    var init: u32 = 0;
    var has_init = false;
    if at(TK_L_PAREN) {
        has_init = true;
        let mark = parse_args();
        init = mk_construct(t, mark, loc, false);
        nscratch.resize(mark);
    } else if at(TK_L_BRACE) {
        has_init = true;
        init = parse_braced();
    }
    if is_opaque(t) || placement || (count != 0 && is_opq(count)) || (init != 0 && is_opq(init) && !(cg_on && nodes[init].kind as i64 == N_INITBRACE)) {
        return dep_node(if is_opaque(t) { t_unknown } else { mk_ptr(t) }, loc);
    }
    if cg_on { return cg_new(t, count, init, has_init, loc); }
    let n = node(N_NEW, if count != 0 { 1 } else { 0 }, mk_ptr(t), init as i64, count as i64, if has_init { 1 } else { 0 }, loc);
    return n;
}

recursive fn parse_delete() -> u32 {
    let loc = tloc();
    accept(TK_COLONCOLON);
    adv();      // delete
    var arr = false;
    if at(TK_L_SQUARE) && tk_n(1) == TK_R_SQUARE { adv(); adv(); arr = true; }
    let e = parse_cast_cx();
    if is_opq(e) { return dep_node(t_void, loc); }
    if cg_on { return cg_delete(rv(e), arr, loc); }
    return node(N_DELETE, if arr { 1 } else { 0 }, t_void, rv(e) as i64, 0, 0, loc);
}

recursive fn mk_compound_lit(t: u32, b: u32, loc: u32) -> u32 {
    let n = dep_node(t, loc);
    nodes[n].flags = nodes[n].flags | NF_LVALUE;
    return n;
}

// ---------------------------------------------------------------------------
// Type-id detection.

// Does a type-id start at pc (C++ [temp.res], [dcl.ambig.res]: when it
// could be a type-id, it is one)?
recursive fn looks_like_type_id() -> bool {
    let k = tk();
    if k >= TK_KW {
        let w = k - TK_KW;
        if w == KW_DECLTYPE { return !decltype_then_cc(); }
        if w == KW_TYPENAME { return true; }
        if w == KW_CONST || w == KW_VOLATILE || w == KW_STRUCT || w == KW_CLASS || w == KW_UNION || w == KW_ENUM { return true; }
        if w == KW_TYPEOF || w == KW_TYPEOF_UNQUAL || w == KW_TTRANS || w == KW_ATOMIC { return true; }
        if is_type_kw(w) {
            // int(3) is an expression; int() and int(*)() are types
            if tk_n(1) == TK_L_PAREN {
                let k2 = tk_n(2);
                if k2 == TK_R_PAREN || k2 == TK_STAR || k2 == TK_AMP || k2 == TK_ELLIPSIS { return true; }
                if k2 >= TK_KW && is_type_kw(k2 - TK_KW) { return true; }
                return false;
            }
            if tk_n(1) == TK_L_BRACE { return false; }
            return true;
        }
        return false;
    }
    if k != TK_IDENT && k != TK_COLONCOLON { return false; }
    let sv = save();
    var qn = QN { .. };
    diag_suppress++;
    let ok = parse_qname(qn);
    var r = false;
    if ok && qn.kind as i64 == QK_IDENT {
        if qn.dep == 0 {
            if !qn.has_targs && at(TK_LESS) {
                lookup_qn(qn);
                if chain_has_template(qn.sym as i64) { qn.targs = parse_targs(); qn.has_targs = true; }
            } else {
                lookup_qn(qn);
            }
            let ts = chain_type(qn.sym as i64);
            let first = if qn.sym >= 0 { resolve(first_visible(qn.sym as i64)) } else { -1 };
            if ts >= 0 && (first == ts || first < 0 || !is_value_kind(syms[first].kind as i64)) {
                let t = qn_type(qn);
                r = t != 0;
            }
            if !r && qn.sym < 0 && !qn.has_targs && lenient > 0 && unknown_name_is_type(qn, DC_PARAM) { r = true; }
        }
        if r {
            if at(TK_L_BRACE) { r = false; }
            else if at(TK_L_PAREN) {
                let k2 = tk_n(1);
                r = k2 == TK_R_PAREN || k2 == TK_STAR || k2 == TK_AMP || k2 == TK_AMPAMP || k2 == TK_ELLIPSIS ||
                    (k2 >= TK_KW && is_type_kw(k2 - TK_KW)) || (k2 == TK_IDENT && name_is_type_at(pc + 1));
            }
        }
    }
    diag_suppress--;
    restore(sv);
    return r;
}

fn is_value_kind(k: i64) -> bool { k == SK_VAR || k == SK_FUNC || k == SK_ENUMC || k == SK_FIELD || k == SK_NTTP }

fn decltype_is_id(e: u32) -> bool {
    let k = nodes[e].kind as i64;
    return (k == N_DECLREF || k == N_MEMBER) && nodes[e].flags & NF_PAREN == 0;
}

fn ty_decl_of(e: u32) -> u32 {
    let k = nodes[e].kind as i64;
    if k == N_DECLREF { return syms[nodes[e].a].ty; }
    if k == N_MEMBER { return fields[nodes[e].b].ty; }
    return nodes[e].ty;
}

// ---------------------------------------------------------------------------
// Variable initializers.

// The initializer of variable s (at pc after its declarator), and its N_DECL.
recursive fn parse_var_init(s: i64, d: CD&, ctx: i64) {
    let loc = d.loc;
    var init: u32 = 0;
    var form = 0;       // 0 none, 1 =, 2 (args), 3 {list}
    if at(TK_EQUAL) {
        adv();
        form = 1;
        if at(TK_L_BRACE) { init = parse_braced(); form = 3; } else { init = parse_assign_cx(); }
    } else if at(TK_L_PAREN) {
        form = 2;
        let mark = parse_args();
        init = mk_construct_init(syms[s].ty, mark, loc);
        nscratch.resize(mark);
    } else if at(TK_L_BRACE) {
        form = 3;
        init = parse_braced();
    }
    // auto: the initializer's type
    let t = syms[s].ty;
    if init != 0 && has_auto(t) {
        syms[s].ty = deduce_auto(t, init);
    }
    if ctx == DC_CLASS || cxs[s].flags & CF_PATTERN != 0 || dependent_ctx() {
        // a static data member's in-class initializer: still a constant
        if init != 0 && is_integer(syms[s].ty) && quals(syms[s].ty) & Q_CONST != 0 && cish_node(init) && !is_opq(init) {
            cvar_note(s, assign_convert(rv(init), syms[s].ty, loc, 1));
        }
        return;
    }
    let conv = if init != 0 { init_convert(s, init, form, loc) } else { default_init(s, loc) };
    // const integral (and enum) variables are usable in constant expressions
    if conv != 0 && !is_opq(conv) && (is_integer(syms[s].ty) || kind_of(syms[s].ty) == TY_BOOL) && quals(syms[s].ty) & Q_CONST != 0 &&
       nodes[conv].kind as i64 != N_INITBRACE {
        cvar_note(s, conv);
    }
    if cg_on && (ctx == DC_BLOCK || ctx == DC_NS || ctx == DC_COND) {
        cg_decl(s, init, conv, form, loc, d.loc, ctx);
        return;
    }
    syms[s].flags = syms[s].flags | (if init != 0 { SF_DEFINED } else { 0 });
    let n = node(N_DECL, 0, syms[s].ty, s, conv as i64, d.loc as i64, loc);
    nscratch.push(n);
}

recursive fn has_auto(t: u32) -> bool {
    let k = kind_of(t);
    if k == TY_AUTO { return true; }
    if k == TY_POINTER || k == TY_LREF || k == TY_RREF { return has_auto(tbase(t)); }
    return false;
}

// auto deduction from an initializer (C++ [dcl.type.auto.deduct]).
recursive fn deduce_auto(t: u32, init: u32) -> u32 {
    if is_opq(init) || nodes[init].kind as i64 == N_INITBRACE { return t_unknown; }
    let it = nodes[init].ty;
    let k = kind_of(t);
    if k == TY_AUTO {
        if types[t >> 4].n == 1 {
            // decltype(auto)
            if is_lvalue(init) && nodes[init].flags & NF_XVALUE == 0 && !decltype_is_id(init) { return mk_lref(it); }
            return it;
        }
        let u = unqual(it);
        let d = if is_array(u) { mk_ptr(tbase(u)) } else if is_func(u) { mk_ptr(u) } else { u };
        return with_q(d, quals(t));
    }
    if k == TY_LREF {
        let inner = tbase(t);
        if kind_of(inner) == TY_AUTO { return mk_lref(with_q(it, quals(inner))); }
        return t_unknown;
    }
    if k == TY_RREF {
        // auto&&: a forwarding reference
        if is_lvalue(init) && nodes[init].flags & NF_XVALUE == 0 { return mk_lref(it); }
        return mk_rref(unqual(it));
    }
    if k == TY_POINTER && kind_of(tbase(t)) == TY_AUTO {
        let u = unqual(it);
        let d = if is_array(u) { mk_ptr(tbase(u)) } else { u };
        if is_pointer(d) { return with_q(d, quals(t)); }
    }
    return t_unknown;
}

fn cvar_note(s: i64, init: u32) {
    cv_define(s, 0, init);
}
