// goosecc D3: statements C++ adds, in code generation: the range-based
// for, desugared as [stmt.ranged]:
//
//   { auto &&__range = range;
//     auto __begin = begin-expr, __end = end-expr;
//     for (; __begin != __end; ++__begin) { decl = *__begin; body } }
//
// begin-expr / end-expr: for an array __range and __range + N; for a
// class with members begin and end, __range.begin() and __range.end();
// otherwise begin(__range) and end(__range) found in the range type's
// namespace.

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

// A local variable of the desugaring (not visible by name), declared and
// initialized from init (copy-initialization): its statements to nscratch.
recursive fn rf_local(name: const u8[:], t: u32, init: u32, loc: u32) -> i64 {
    let s = csym(SK_VAR, intern(name), t, loc);
    cxs[s].dscope = cur_scope as! i32;
    syms[s].scope = 1;
    let conv = init_convert(s, init, 1, loc);
    cg_decl(s, init, conv, 1, loc, loc, DC_BLOCK);
    return s;
}

// The type `auto x = e` deduces (decayed, top-level cv dropped).
fn auto_value_type(e: u32) -> u32 {
    let u = unqual(nonref(nodes[e].ty));
    if is_array(u) { return mk_ptr(tbase(u)); }
    if is_func(u) { return mk_ptr(u); }
    return u;
}

// begin(__range) / end(__range) for a class type: the members, else the
// functions of the class's namespace; 0 when there are none.
recursive fn rf_call(rs: i64, rt: u32, name: const u8[:], loc: u32) -> u32 {
    let id = intern(name);
    if is_record(rt) {
        let sc = type_scope(rt);
        if sc >= 0 {
            let m = class_lookup(sc, id);
            if m >= 0 {
                let callee = mk_member_ref(n_var(rs, loc), false, m, -1, loc);
                if is_opq(callee) && nodes[callee].kind as i64 != N_FUNCREF { return 0; }
                let mark = nscratch.len;
                return mk_call_cx(callee, mark, loc);
            }
        }
    }
    let ns = adl_ns(rt);
    if ns < 0 { return 0; }
    let f = ns_lookup(ns, id, false);
    if f < 0 { return 0; }
    let mark = nscratch.len;
    nscratch.push(n_var(rs, loc));
    let best = best_candidate(f, mark, false);
    if best < 0 { nscratch.resize(mark); return 0; }
    return lower_call(best, 0, mark, loc, false);
}

// for (decl : range) body, from after the ')': the declared type dt and
// name of the loop variable; parses the body. A statement, or 0 (nothing
// parsed) when D3 cannot set it up.
recursive fn cg_range_for(dt: u32, name: u32, dloc: u32, r: u32, loc: u32) -> u32 {
    let mark = nscratch.len;
    // auto &&__range = range
    let lv = is_lvalue(r) && nodes[r].flags & NF_XVALUE == 0;
    let rty = if lv { mk_lref(nodes[r].ty) } else { mk_rref(unqual(nodes[r].ty)) };
    let rs = rf_local("__range", rty, r, loc);
    let rt = nonref(syms[rs].ty);
    var be: u32 = 0;
    var ee: u32 = 0;
    if is_array(rt) && types[rt >> 4].n >= 0 {
        be = rv(n_var(rs, loc));
        ee = mk_binop(OP_PLUS, B_ADD, n_var(rs, loc), int_node(types[rt >> 4].n, t_long, loc), loc);
    } else {
        be = rf_call(rs, rt, "begin", loc);
        ee = rf_call(rs, rt, "end", loc);
    }
    if be == 0 || ee == 0 || is_opq(be) || is_opq(ee) { nscratch.resize(mark); return 0; }
    let bs = rf_local("__begin", auto_value_type(be), be, loc);
    let es = rf_local("__end", auto_value_type(ee), ee, loc);
    // the loop variable: decl = *__begin
    let init = mk_deref_cx(n_var(bs, loc), loc);
    var vt = dt;
    if has_auto(vt) { vt = deduce_auto(vt, init); }
    if is_opq(init) || is_opaque(vt) { nscratch.resize(mark); return 0; }
    let vs = csym(SK_VAR, name, vt, dloc);
    cxs[vs].dscope = cur_scope as! i32;
    bind_sym(vs, false);
    let bm = nscratch.len;
    let conv = init_convert(vs, init, 1, dloc);
    cg_decl(vs, init, conv, 1, dloc, dloc, DC_BLOCK);
    loop_depth++;
    break_depth++;
    let b = parse_stmt_cx();
    loop_depth--;
    break_depth--;
    nscratch.push(b);
    let body = n_block(bm, loc);
    let cond = cond_cx(mk_binop(OP_NE, B_NE, n_var(bs, loc), n_var(es, loc), loc));
    let inc = mk_incdec_cx(n_var(bs, loc), U_PREINC, loc, true);
    nscratch.push(node_v(N_FOR, 0, 0, 0, cond as i64, inc as i64, loc, body as i64));
    return n_block(mark, loc);
}

