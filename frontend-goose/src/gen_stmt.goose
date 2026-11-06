// goosecc B2: statements and function bodies. Control flow follows clang's
// -O0 shapes (if.then / for.cond / for.body / for.inc ...), conditions are
// branched on directly (short-circuit operators become branches), and a
// statement after a terminator that contains no label is skipped, as clang
// does. Scopes keep a cleanup stack for VLA stack restores and
// __attribute__((cleanup)).

namespace gen;

import std;
import dictionary;
import .common;
import .types;
import .ast;
import .sema;
import .parse;

var f_global: u32 = 0;
// The targets of break and continue: the block, and the cleanup depth there.
struct Target { blk: u32, depth: u32 }
var brk_to: Target[>..<] = [];
var cont_to: Target[>..<] = [];

// Cleanups: kind 1 = stackrestore(saved), kind 2 = call fn(&var)
struct Cleanup { kind: u8, val: u32, sym: i64, fsym: i64 }
var cleanups: Cleanup[>..<] = [];
var cleanup_marks: u32[>..<] = [];

// Per function: N_CASE / N_DEFAULT node -> its block (fk(FM_CASE, node)),
// label -> the cleanup depth where it is defined (fk(FM_LABEL, label)).
let FM_CASE = 1;
let FM_LABEL = 2;
var fmap = dictionary<u64, u32> {};
fn fk(table: u64, key: u32) -> u64 { (table << 32) | (key as u64) }
var f_addr_labels: u32[>..<] = [];          // labels whose address is taken
var f_igoto: u32 = NONE;                    // the indirect-goto block
var f_igoto_vals: u32[>..<] = [];           // (address, predecessor block) pairs

fn case_block(n: u32) -> u32 {
    let r = fmap.get(fk(FM_CASE, n));
    if r { return r; }
    return NONE;
}

fn label_block(l: i64) -> u32 {
    ensure_sym_tables();
    if sym_gen[l].addr == NONE { sym_gen[l].addr = new_block(); }
    return sym_gen[l].addr;
}

fn add_addr_label(l: i64) {
    for x in f_addr_labels { if x as i64 == l { return; } }
    f_addr_labels.push(l as! u32);
}

fn push_cleanup_scope() { cleanup_marks.push(cleanups.len as! u32); }

// Leaves the innermost scope (emitting its cleanups if `emit_them` and the
// code is reachable).
fn pop_cleanup_scope(emit_them: bool) {
    let mark = cleanup_marks.pop() as i64;
    if emit_them && has_insert() { run_cleanups(mark); }
    cleanups.resize(mark);
}

// Emits the cleanups above depth `mark`, innermost first.
fn run_cleanups(mark: i64) {
    var i = cleanups.len - 1;
    while i >= mark {
        let c = cleanups[i];
        if c.kind == 1 {
            emit(GIR_STACKRESTORE, GIR_T_VOID, 0, 0, 0, c.val, 0, 0);
        } else {
            let fg = func_global(c.fsym);
            let addr = var_addr(c.sym);
            let s = m_opnds.len as! u32;
            op_ref(addr);
            op_imm(0);
            emit(GIR_CALL, GIR_T_VOID, 0, 0, 0, gref(fg), s, 1);
        }
        i--;
    }
}

// Cleanup-function calls only (on return: the frame goes away anyway).
fn run_call_cleanups() {
    var i = cleanups.len - 1;
    while i >= 0 {
        let c = cleanups[i];
        if c.kind == 2 {
            let fg = func_global(c.fsym);
            let addr = var_addr(c.sym);
            let s = m_opnds.len as! u32;
            op_ref(addr);
            op_imm(0);
            emit(GIR_CALL, GIR_T_VOID, 0, 0, 0, gref(fg), s, 1);
        }
        i--;
    }
}

// Does statement n contain a label (or a case) that code may jump to?
recursive fn contains_label(n: u32) -> bool {
    if n == 0 { return false; }
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_LABEL || k == N_CASE || k == N_DEFAULT { return true; }
    if k == N_COMPOUND {
        for i in nd.c { if contains_label(nlist[nd.v + i]) { return true; } }
        return false;
    }
    if k == N_IF { return contains_label(nd.b) || contains_label(nd.c); }
    if k == N_WHILE { return contains_label(nd.b); }
    if k == N_DO { return contains_label(nd.a); }
    if k == N_FOR { return contains_label(nd.v as! u32); }
    if k == N_SWITCH { return contains_label_noswitch(nd.b); }
    if k == N_STMTEXPR { return contains_label(nd.a); }
    return false;
}

// Labels only (cases of a nested switch belong to it).
recursive fn contains_label_noswitch(n: u32) -> bool {
    if n == 0 { return false; }
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_LABEL { return true; }
    if k == N_CASE || k == N_DEFAULT { return contains_label_noswitch(nd.a); }
    if k == N_COMPOUND {
        for i in nd.c { if contains_label_noswitch(nlist[nd.v + i]) { return true; } }
        return false;
    }
    if k == N_IF { return contains_label_noswitch(nd.b) || contains_label_noswitch(nd.c); }
    if k == N_WHILE { return contains_label_noswitch(nd.b); }
    if k == N_DO { return contains_label_noswitch(nd.a); }
    if k == N_FOR { return contains_label_noswitch(nd.v as! u32); }
    if k == N_SWITCH { return contains_label_noswitch(nd.b); }
    return false;
}


fn gen_label(l: i64) {
    let b = label_block(l);
    start_block(b);
    fmap.insert(fk(FM_LABEL, l as! u32), cleanups.len as! u32);
}

recursive fn gen_stmt(n: u32) {
    if n == 0 { return; }
    let nd = nodes[n];
    let k = nd.kind as i64;
    if !has_insert() && !contains_label(n) {
        // unreachable code: skipped, except declarations of statics and VLAs
        // in it still matter for later code (no: they are only reachable
        // through labels, which this statement has none of)
        if k != N_DECL && k != N_COMPOUND { return; }
        if k == N_COMPOUND {
            var any = false;
            for i in nd.c { if nkind(nlist[nd.v + i]) == N_DECL { any = true; } }
            if !any { return; }
        }
    }
    // a stop point at the statement's first token (not for compound
    // statements, labels and case labels, as in clang)
    if k == N_EXPR { set_loc(begin_loc(nd.a)); }
    else if k == N_DECL { set_loc(if nd.c != 0 { nd.c } else { nd.loc }); }
    else if k != N_COMPOUND && k != N_CASE && k != N_DEFAULT && k != N_LABEL && k != N_NULL { set_loc(nd.loc); }
    if k == N_COMPOUND {
        push_cleanup_scope();
        scope_enter(n);
        for i in nd.c { gen_stmt(nlist[nd.v + i]); }
        // what follows the block (its cleanups, the branch out) is at the '}'
        if nd.b != 0 { set_loc(nd.b); }
        scope_leave();
        pop_cleanup_scope(true);
        return;
    }
    if k == N_EXPR {
        if !has_insert() && !contains_label(n) { return; }
        ex_ignore(nd.a);
        return;
    }
    if k == N_DECL { gen_local_decl(n); return; }
    if k == N_NULL || k == N_TYPEDEF || k == N_TAGDEF || k == N_STATICASSERT {
        if k == N_TYPEDEF && is_vm_any(nodes[n].ty) && has_insert() { eval_vm_type(syms[nd.a].ty); }
        return;
    }
    if k == N_IF { gen_if(n); return; }
    if k == N_WHILE { gen_while(n); return; }
    if k == N_DO { gen_do(n); return; }
    if k == N_FOR { gen_for(n); return; }
    if k == N_SWITCH { gen_switch(n); return; }
    if k == N_CASE || k == N_DEFAULT {
        let r = fmap.get(fk(FM_CASE, n));
        if r { start_block(r); }
        if k == N_CASE && nd.c != 0 {
            // GNU range expanded into blocks of its own: same block
        }
        gen_stmt(nd.a);
        return;
    }
    if k == N_LABEL {
        gen_label(nd.a as i64);
        gen_stmt(nd.b);
        return;
    }
    if k == N_GOTO {
        // a jump back to before a VLA (or a cleanup variable) leaves its scope
        let d = fmap.get(fk(FM_LABEL, nd.a));
        if d && (d as i64) < cleanups.len { run_cleanups(d as i64); }
        br(label_block(nd.a as i64));
        return;
    }
    if k == N_IGOTO {
        let p = ex_val(nd.a);
        if f_igoto == NONE { f_igoto = new_block(); }
        if has_insert() {
            f_igoto_vals.push(p);
            f_igoto_vals.push(cur_blk as! u32);
            br(f_igoto);
        }
        return;
    }
    if k == N_BREAK {
        if brk_to.len == 0 { return; }
        let bt = brk_to[brk_to.len - 1];
        run_cleanups(bt.depth as i64);
        br(bt.blk);
        return;
    }
    if k == N_CONTINUE {
        if cont_to.len == 0 { return; }
        let ct = cont_to[cont_to.len - 1];
        run_cleanups(ct.depth as i64);
        br(ct.blk);
        return;
    }
    if k == N_RETURN { gen_return(n); return; }
    if k == N_ASM { gen_asm(n); return; }
    if k == N_FUNCDEF { return; }
    bug("gen_stmt", n);
}

recursive fn is_vm_any(q: u32) -> bool {
    let k = kind_of(q);
    if k == TY_VLA { return true; }
    if k == TY_ARRAY || k == TY_POINTER { return is_vm_any(tbase(q)); }
    return false;
}

// Debug scopes per compound statement (lexical blocks).
fn scope_enter(n: u32) { dbg_scope_enter(n); }
fn scope_leave() { dbg_scope_leave(); }

recursive fn gen_if(n: u32) {
    let nd = nodes[n];
    let ok, cv = const_bool(nd.a);
    if ok {
        // a constant condition: only the arm that runs (unless the other has labels)
        let live = if cv { nd.b } else { nd.c };
        let dead = if cv { nd.c } else { nd.b };
        if !contains_label(dead) {
            gen_stmt(live);
            return;
        }
    }
    let tb = new_block();
    let end = new_block();
    let eb = if nd.c != 0 { new_block() } else { end };
    // the condition branches at the condition
    let saved = if dbg_on() { push_loc(expr_loc(nd.a)) } else { 0 };
    let lc = dbg_loopcond;
    dbg_loopcond = false;
    ex_cond(nd.a, tb, eb);
    dbg_loopcond = lc;
    if dbg_on() { pop_loc(saved); }
    start_block(tb);
    gen_stmt(nd.b);
    if nd.c != 0 {
        if has_insert() { br(end); }
        start_block(eb);
        gen_stmt(nd.c);
        // the branch out of the else arm has no location (clang)
        if has_insert() {
            let s2 = cur_dbg;
            pop_loc(0);
            br(end);
            pop_loc(s2);
        }
    }
    if has_insert() { br(end); }
    start_block(end);
}

fn push_loop(brk: u32, cont: u32) {
    brk_to.push(Target { blk: brk, depth: cleanups.len as! u32 });
    cont_to.push(Target { blk: cont, depth: cleanups.len as! u32 });
}
fn pop_loop() {
    brk_to.pop();
    cont_to.pop();
}

recursive fn gen_while(n: u32) {
    let nd = nodes[n];
    let cond = new_block();
    let body = new_block();
    let end = new_block();
    start_block(cond);
    let lc = dbg_loopcond;
    dbg_loopcond = true;
    ex_cond(nd.a, body, end);
    dbg_loopcond = lc;
    start_block(body);
    push_loop(end, cond);
    gen_stmt(nd.b);
    pop_loop();
    set_loc(nd.loc);
    if has_insert() { br(cond); }
    start_block(end);
}

recursive fn gen_do(n: u32) {
    let nd = nodes[n];
    let body = new_block();
    let cond = new_block();
    let end = new_block();
    start_block(body);
    push_loop(end, cond);
    gen_stmt(nd.a);
    pop_loop();
    start_block(cond);
    let lc = dbg_loopcond;
    dbg_loopcond = true;
    ex_cond(nd.b, body, end);
    dbg_loopcond = lc;
    start_block(end);
}

recursive fn gen_for(n: u32) {
    let nd = nodes[n];
    push_cleanup_scope();
    if nd.a != 0 { gen_stmt(nd.a); }
    let cond = new_block();
    let body = new_block();
    let inc = new_block();
    let end = new_block();
    start_block(cond);
    set_loc(nd.loc);
    let lc = dbg_loopcond;
    dbg_loopcond = true;
    if nd.b != 0 { ex_cond(nd.b, body, end); } else { br(body); }
    dbg_loopcond = lc;
    start_block(body);
    push_loop(end, if nd.c != 0 { inc } else { cond });
    gen_stmt(nd.v as! u32);
    pop_loop();
    start_block(inc);
    if nd.c != 0 {
        set_loc(begin_loc(nd.c));
        ex_ignore(nd.c);
    }
    set_loc(nd.loc);
    if has_insert() { br(cond); }
    start_block(end);
    pop_cleanup_scope(true);
}

recursive fn gen_switch(n: u32) {
    let nd = nodes[n];
    let cq = nty(nd.a);
    let v = ex_val(nd.a);
    let t = vtype(v);
    let end = new_block();
    var dflt = end;
    // blocks of the cases
    let ncases = nd.c as i64;
    var range_checks = false;
    for i in ncases {
        let cn = nlist[nd.v + i];
        let b = new_block();
        fmap.insert(fk(FM_CASE, cn), b);
        if nkind(cn) == N_DEFAULT { dflt = b; }
        else if nodes[cn].c != 0 {
            let lo = nodes[cn].v;
            let hi = nodes[nodes[cn].c].v;
            let span = (hi as! u64) - (lo as! u64);
            if span >= 64 { range_checks = true; }
        }
    }
    // GNU case ranges of 64 values or more are tested before the default
    var dtarget = dflt;
    if range_checks { dtarget = new_block(); }
    let s = m_opnds.len as! u32;
    op_blk(dtarget);
    var np: u32 = 0;
    let wide = tcls(t) == C_INT2;
    for i in ncases {
        let cn = nlist[nd.v + i];
        if nkind(cn) == N_DEFAULT { continue; }
        let b = case_block(cn);
        let lo = nodes[cn].v;
        if nodes[cn].c != 0 {
            let hi = nodes[nodes[cn].c].v;
            let span = (hi as! u64) - (lo as! u64);
            if span >= 64 { continue; }
            var x = lo as! u64;
            loop {
                op_ref(case_const(x as! i64, t, cq));
                op_blk(b);
                np++;
                if x == hi as! u64 { break; }
                x = x + 1;
            }
            continue;
        }
        op_ref(case_value(cn, t, cq));
        op_blk(b);
        np++;
    }
    if is_const(v) {
        // a constant condition: still a switch (the back-end compares)
    }
    emit(GIR_SWITCH, GIR_T_VOID, 0, 0, t, v, s, np);
    cur_blk = -1;
    let sw_t = t;
    if range_checks {
        start_block(dtarget);
        for i in ncases {
            let cn = nlist[nd.v + i];
            if nkind(cn) == N_DEFAULT || nodes[cn].c == 0 { continue; }
            let lo = nodes[cn].v;
            let hi = nodes[nodes[cn].c].v;
            let span = (hi as! u64) - (lo as! u64);
            if span < 64 { continue; }
            let d = ins_bin(GIR_SUB, sw_t, v, case_const(lo, sw_t, cq));
            let c = ins_icmp(GIR_ULE, sw_t, d, case_const(hi - lo, sw_t, cq));
            let next = new_block();
            condbr(c, case_block(cn), next);
            start_block(next);
        }
        br(dflt);
    }
    brk_to.push(Target { blk: end, depth: cleanups.len as! u32 });
    gen_stmt(nd.b);
    brk_to.pop();
    if has_insert() { br(end); }
    start_block(end);
}

// A case value: 128-bit ones are refolded from the case expression.
fn case_value(cn: u32, t: u32, cq: u32) -> u32 {
    let nd = nodes[cn];
    if tcls(t) == C_INT2 && nd.b != 0 {
        let ok, lo, hi = fold_int128(nd.b);
        if ok { return c_wide(lo, hi, t); }
    }
    return case_const(nd.v, t, cq);
}

fn case_const(v: i64, t: u32, cq: u32) -> u32 {
    if tcls(t) == C_INT2 {
        let signed = is_signed(cq);
        return c_wide(v as! u64, if signed && v < 0 { 0xFFFFFFFFFFFFFFFF } else { 0 as u64 }, t);
    }
    return c_int(v as! u64, t);
}

// ------------------------------------------------------------ declarations

recursive fn gen_local_decl(n: u32) {
    let nd = nodes[n];
    let s = nd.a as i64;
    let sy = syms[s];
    if sy.kind != SK_VAR { return; }
    if sy.sc == SC_EXTERN || sy.flags & SF_LOCALLINK != 0 { return; }
    let q = sy.ty;
    if sy.sc == SC_STATIC || sy.flags & SF_THREAD != 0 {
        // a static local: defined here (its initializer may name labels)
        ensure_sym_tables();
        let g = var_global(s);
        if glob_gen[g].state != 2 {
            sym_gen[s].init = nd.b;
            emit_var(g);
        }
        return;
    }
    if !has_insert() && !is_vm_any(q) {
        // unreachable: the storage still exists for jumps into the scope
        ensure_sym_tables();
        if sym_gen[s].addr == NONE { sym_gen[s].addr = alloca(type_size(q), local_align(s, q)); }
        return;
    }
    ensure_sym_tables();
    if kind_of(q) == TY_VLA {
        // a VLA: dynamic stack allocation, restored at the end of the scope
        if cleanup_marks.len > 0 {
            let mark = cleanup_marks[cleanup_marks.len - 1] as i64;
            var have = false;
            for i in mark..cleanups.len { if cleanups[i].kind == 1 { have = true; } }
            if !have {
                let sp = emit(GIR_STACKSAVE, GIR_T_PTR, 0, 0, 0, 0, 0, 0);
                cleanups.push(Cleanup { kind: 1, val: sp, sym: -1, fsym: -1 });
            }
        }
        eval_vm_type(q);
        let size = size_val(q);
        var al = local_align(s, q);
        if al < 16 { al = 16; }
        let p = emit(GIR_DYNALLOCA, GIR_T_PTR, 0, 0, 0, size, al as! u32, 0);
        sym_gen[s].addr = p;
        return;
    }
    if is_vm_any(q) { eval_vm_type(q); }
    var p = sym_gen[s].addr;
    if p == NONE {
        p = alloca(type_size(q), local_align(s, q));
        sym_gen[s].addr = p;
    }
    if nd.b != 0 {
        // the initialization is at the variable
        let saved = if dbg_on() { push_loc(nd.loc) } else { 0 };
        init_object(p, q, nd.b);
        if dbg_on() { pop_loc(saved); }
        if quals(q) & Q_CONST != 0 && is_pointer(q) {
            while sym_gen.len <= s { sym_gen.push(SymGen { addr: NONE, glob: NONE, init: 0, decl: 0, linit: 0 }); }
            sym_gen[s].linit = nd.b;
        }
    }
    let a = sy.attr;
    if a != 0 && sym_attrs[a].cleanup >= 0 {
        cleanups.push(Cleanup { kind: 2, val: 0, sym: s, fsym: sym_attrs[a].cleanup as i64 });
    }
}

// Initializes local aggregate (or any) object at p from init node n.
recursive fn init_local(p: u32, q: u32, n: u32) {
    let nd = nodes[n];
    let k = nd.kind as i64;
    let size = type_size(q);
    if k == N_ZEROINIT {
        mem_set(p, c_i8(0), size, false);
        return;
    }
    if k == N_STRING {
        let si = nd.a;
        let b = str_bytes(si);
        var n_copy = b.len;
        if n_copy > size { n_copy = size; }
        if n_copy > 0 {
            let g = string_global(si);
            mem_copy(p, gref(g), n_copy, false);
        }
        if size > n_copy { mem_set(gep(p, n_copy), c_i8(0), size - n_copy, false); }
        return;
    }
    if k != N_INITLIST {
        store_any(q, n, p);
        return;
    }
    let tk = kind_of(q);
    if tk != TY_STRUCT && tk != TY_UNION && tk != TY_ARRAY {
        // a scalar, complex or vector in braces
        if tk == TY_COMPLEX {
            let et = cplx_elem(q);
            if nd.c == 0 { mem_set(p, c_i8(0), size, false); return; }
            let r = ex_val(nlist[nd.v]);
            var i = c_zero(vty(et));
            if nd.c > 1 { i = ex_val(nlist[nd.v + 1]); }
            store_cplx(q, r, i, p, false);
            return;
        }
        if is_vector(q) {
            init_vector(p, q, n);
            return;
        }
        if nd.c == 0 { mem_set(p, c_i8(0), size, false); return; }
        store_any(q, nlist[nd.v], p);
        return;
    }
    // a constant initializer of some size: copy from a private constant
    if size >= 32 && is_const_init(n, q) {
        let g = const_init_global(q, n);
        mem_copy(p, gref(g), size, false);
        return;
    }
    // zero everything first unless every byte is written
    if !covers_all(q, n) { mem_set(p, c_i8(0), size, false); }
    if tk == TY_STRUCT {
        let r = rec_of(q);
        var ci = 0;
        let first = records[r].first as i64;
        let cnt = records[r].count as i64;
        for i in first..first + cnt {
            let f = fields[i];
            if f.width >= 0 && f.name == 0 { continue; }
            if ci >= nd.c as i64 { break; }
            let child = nlist[nd.v + ci];
            ci++;
            if nkind(child) == N_ZEROINIT { continue; }
            if f.width >= 0 {
                if f.width == 0 { continue; }
                let v = ex_val(child);
                bf_store(LV { addr: p, fld: i as! i32, vol: false, q: f.ty }, conv(v, nty(child), f.ty));
                continue;
            }
            init_local(gep(p, f.offset), f.ty, child);
        }
        return;
    }
    if tk == TY_UNION {
        if nd.a == 0 || nd.c == 0 { return; }
        let fi = records[rec_of(q)].first as i64 + nd.a as i64 - 1;
        let f = fields[fi];
        let child = nlist[nd.v];
        if nkind(child) == N_ZEROINIT { return; }
        if f.width >= 0 {
            if f.width == 0 { return; }
            let v = ex_val(child);
            bf_store(LV { addr: p, fld: fi as! i32, vol: false, q: f.ty }, conv(v, nty(child), f.ty));
            return;
        }
        init_local(gep(p, f.offset), f.ty, child);
        return;
    }
    // array
    let et = tbase(q);
    let es = type_size(et);
    for i in nd.c {
        let child = nlist[nd.v + i];
        if nkind(child) == N_ZEROINIT { continue; }
        init_local(gep(p, i * es), et, child);
    }
    if nd.b != 0 && nkind(nd.b) != N_ZEROINIT {
        let n_el = types[q >> 4].n;
        for i in (nd.c as i64)..n_el { init_local(gep(p, i * es), et, nd.b); }
    }
}

recursive fn init_vector(p: u32, q: u32, n: u32) {
    let nd = nodes[n];
    let et = tbase(q);
    let es = type_size(et);
    mem_set(p, c_i8(0), type_size(q), false);
    var pos: i64 = 0;
    for i in nd.c {
        let child = nlist[nd.v + i];
        let ct = nty(child);
        if is_vector(ct) {
            store_any(ct, child, gep(p, pos));
            pos += type_size(ct);
        } else {
            let v = ex_val(child);
            store_c(et, conv(v, ct, et), gep(p, pos), false);
            pos += es;
        }
    }
}

// Does the initializer write every byte of the object (no padding, no
// implicit zeros)?
recursive fn covers_all(q: u32, n: u32) -> bool {
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_ZEROINIT { return false; }
    if k == N_STRING { return true; }
    if k != N_INITLIST { return true; }
    let tk = kind_of(q);
    if tk == TY_STRUCT {
        let r = rec_of(q);
        if records[r].flags & RF_HAS_BITFIELD != 0 { return false; }
        var ci = 0;
        var end: i64 = 0;
        let first = records[r].first as i64;
        let cnt = records[r].count as i64;
        for i in first..first + cnt {
            let f = fields[i];
            if ci >= nd.c as i64 { return false; }
            if f.offset != end { return false; }
            if !covers_all(f.ty, nlist[nd.v + ci]) { return false; }
            end = f.offset + type_size(f.ty);
            ci++;
        }
        return end == type_size(q);
    }
    if tk == TY_UNION { return false; }
    if tk == TY_ARRAY {
        let n_el = types[q >> 4].n;
        if nd.c as i64 != n_el { return false; }
        let et = tbase(q);
        for i in nd.c { if !covers_all(et, nlist[nd.v + i]) { return false; } }
        return true;
    }
    return true;
}

// Is the initializer constant (foldable) everywhere, with no addresses?
recursive fn is_const_init(n: u32, q: u32) -> bool {
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_ZEROINIT || k == N_STRING { return true; }
    if k == N_INITLIST {
        let tk = kind_of(q);
        if tk == TY_STRUCT {
            let r = rec_of(q);
            var ci = 0;
            let first = records[r].first as i64;
            let cnt = records[r].count as i64;
            for i in first..first + cnt {
                let f = fields[i];
                if f.width >= 0 && f.name == 0 { continue; }
                if ci >= nd.c as i64 { break; }
                if !is_const_init(nlist[nd.v + ci], f.ty) { return false; }
                ci++;
            }
            return true;
        }
        if tk == TY_UNION {
            if nd.a == 0 || nd.c == 0 { return true; }
            let f = fields[records[rec_of(q)].first + nd.a - 1];
            return is_const_init(nlist[nd.v], f.ty);
        }
        if tk == TY_ARRAY {
            let et = tbase(q);
            for i in nd.c { if !is_const_init(nlist[nd.v + i], et) { return false; } }
            if nd.b != 0 && !is_const_init(nd.b, et) { return false; }
            return true;
        }
        if tk == TY_COMPLEX || is_vector(q) {
            for i in nd.c { if !is_const_init(nlist[nd.v + i], nty(nlist[nd.v + i])) { return false; } }
            return true;
        }
        if nd.c > 0 { return is_const_init(nlist[nd.v], q); }
        return true;
    }
    if is_integer(q) {
        let ok, v = fold_int(n);
        return ok && pure_const(n);
    }
    if is_real_float(q) && kind_of(q) != TY_FLOAT128 {
        let ok, x = static_f80(n);
        return ok && pure_const(n);
    }
    return false;
}

var n_const_inits: i64 = 0;

// A private constant global holding the initializer (clang's __const.f.x).
fn const_init_global(q: u32, n: u32) -> u32 {
    var g: u32 = 0;
    {
        var nm: u8[>..] = [];
        nm.append("__const.");
        nm.append(ident_text(link_name(f_sym) as i64));
        format(nm, ".", n_const_inits);
        g = new_global(nm, G_VAR, GF_INTERNAL | GF_DEFINED | GF_CONST | GF_LOCALREF, type_align(q) as! u32);
    }
    n_const_inits++;
    let size = type_size(q);
    ensure_glob_tables();
    glob_gen[g].state = 2;
    m_globals[g].size = size as! u32;
    let at = m_data.len;
    data_grow(size);
    m_globals[g].data = at as! u32;
    let r0 = m_drelocs.len;
    sinit(g, at, 0, q, n);
    sort_relocs(r0);
    return g;
}

// ------------------------------------------------------------ functions

var f_args_run: u32 = 0;
var f_nargs: u32 = 0;
var f_ret_ty: u32 = 0;

fn abi_word(a: Abi) -> u32 {
    if a.kind == AK_BYVAL {
        var lg: u32 = 0;
        while ((1 as u32) << lg) < a.align { lg++; }
        return ABI_BYVAL | a.size | (lg << 24);
    }
    return 0;
}

fn ret_gir_type(a: Abi) -> u32 {
    if a.kind == AK_DIRECT { return a.t0; }
    if a.kind == AK_COERCE {
        if a.n == 1 { return a.t0; }
        return ty_pair(a.t0, a.t1, a.off1);
    }
    if a.kind == AK_SRET { return GIR_T_PTR; }
    return GIR_T_VOID;
}

fn gen_function(fd: u32) {
    let nd = nodes[fd];
    let s = nd.a as i64;
    let g = func_global(s);
    glob_gen[g].state = 2;
    m_globals[g].kind = G_FUNC;
    m_globals[g].flags = link_flags(s, true) | GF_DEFINED;
    let sec = sym_section(s);
    if sec != 0 { m_globals[g].section = get_section(strbytes[sec..sec + sym_attrs[syms[s].attr].sec_len], SF_EXEC, 1); }
    let ft = syms[s].ty;
    let fty = types[ft >> 4];
    let ai = fn_abi(ft);
    fn_begin();
    ensure_sym_tables();
    f_sym = s;
    f_global = g;
    f_flags = 0;
    f_ret = abis[ai];
    f_ret_q = unqual(fty.base);
    f_sret = NONE;
    f_addr_labels.clear();
    f_igoto = NONE;
    f_igoto_vals.clear();
    f_arg_types.clear();
    if fmap.count > 0 { fmap.clear(); }   // clear walks every slot
    cleanups.clear();
    cleanup_marks.clear();
    dbg_function_begin(s, nd.loc);
    last_loc = nd.loc;
    // GIR arguments: (type, ABI word) pairs
    let types_mark = m_types.len;
    let ret_t = ret_gir_type(f_ret);
    // the parts' struct types are made before the run starts
    let run = m_opnds.len as! u32;
    var na: u32 = 0;
    if f_ret.kind == AK_SRET {
        op_imm(GIR_T_PTR);
        op_imm(ABI_SRET);
        f_arg_types.push(GIR_T_PTR);
        f_sret = KARG | na;
        na++;
    }
    let np = nd.c as i64;
    for i in np {
        if i >= fty.n { break; }
        let a = abis[ai + 1 + i];
        if a.kind == AK_DIRECT || a.kind == AK_BYVAL {
            op_imm(a.t0);
            op_imm(abi_word(a));
            f_arg_types.push(a.t0);
            na++;
        } else if a.kind == AK_COERCE {
            op_imm(a.t0);
            op_imm(0);
            f_arg_types.push(a.t0);
            na++;
            if a.n == 2 {
                op_imm(a.t1);
                op_imm(0);
                f_arg_types.push(a.t1);
                na++;
            }
        }
    }
    f_args_run = run;
    f_nargs = na;
    f_ret_ty = ret_t;
    // the parameters' storage
    var argi: u32 = if f_ret.kind == AK_SRET { 1 } else { 0 };
    for i in np {
        let p = nlist[nd.v + i] as i64;
        let pq = syms[p].ty;
        if i >= fty.n {
            sym_gen[p].addr = alloca(type_size(pq), type_align(pq));
            continue;
        }
        let a = abis[ai + 1 + i];
        let proto_q = unqual(tparams[fty.extra + i]);
        if a.kind == AK_BYVAL {
            sym_gen[p].addr = KARG | argi;
            argi++;
            continue;
        }
        if a.kind == AK_IGNORE {
            sym_gen[p].addr = alloca(type_size(pq), type_align(pq));
            continue;
        }
        if a.kind == AK_DIRECT {
            let slot = alloca(type_size(pq), local_align(p, pq));
            sym_gen[p].addr = slot;
            var v = KARG | argi;
            argi++;
            if unqual(pq) != proto_q && vkind(pq) == VK_SCALAR { v = conv(v, proto_q, unqual(pq)); }
            store_c(unqual(pq), v, slot, false);
            continue;
        }
        // coerced: the parts are stored into a slot big enough for them
        var size = type_size(pq);
        let need = a.off1 as i64 + (if a.n == 2 { tsize(a.t1) as i64 } else { tsize(a.t0) as i64 + a.off0 as i64 });
        var al = local_align(p, pq);
        if al < 8 { al = 8; }
        if need > size { size = need; }
        let slot = alloca(size, al);
        sym_gen[p].addr = slot;
        ins_store(a.t0, KARG | argi, gep(slot, a.off0 as i64), false);
        argi++;
        if a.n == 2 {
            ins_store(a.t1, KARG | argi, gep(slot, a.off1 as i64), false);
            argi++;
        }
    }
    // variably modified parameter types (int a[n][m]: m is evaluated here)
    for i in np {
        let p = nlist[nd.v + i] as i64;
        if syms[p].v != 0 && kind_of(syms[p].v as! u32) == TY_VLA { eval_vm_type(syms[p].v as! u32); }
        else if is_vm_any(syms[p].ty) { eval_vm_type(syms[p].ty); }
    }
    // the prologue has no location; the body starts at its '{'
    set_loc(nodes[nd.b].loc);
    push_cleanup_scope();
    gen_stmt(nd.b);
    pop_cleanup_scope(true);
    if has_insert() {
        // falling off the end (main returns 0)
        set_loc(fn_end_loc(nd.b));
        let is_main = ident_text(syms[s].name as i64) == "main" && is_internal_sym(s) == false;
        if f_ret.kind == AK_SRET { emit_term(GIR_RET, f_sret, 0, 0); }
        else if f_ret.kind == AK_IGNORE { emit_term(GIR_RET, NONE, 0, 0); }
        else if is_main && kind_of(f_ret_q) == TY_INT { emit_term(GIR_RET, c_i32(0), 0, 0); }
        else { emit_term(GIR_RET, c_zero(ret_t), 0, 0); }
    }
    finish_igoto();
    var flags = f_flags;
    if fty.flags & TF_VARIADIC != 0 { flags = flags | FN_VARARG; }
    if is_internal_sym(s) || fn_local_inline(s) { flags = flags | FN_INTERNAL; }
    var al: u32 = 4;
    let a = syms[s].attr;
    if a != 0 && sym_attrs[a].align > 16 {
        var lg: u32 = 0;
        while ((1 as u32) << lg) < sym_attrs[a].align { lg++; }
        al = lg;
    }
    flags = flags | (al << FN_ALIGN_SHIFT);
    let dbg = dbg_function_end();
    fn_finish(g, flags, f_nargs, f_args_run, f_ret_ty, dbg);
    f_sym = -1;
}

fn fn_end_loc(body: u32) -> u32 {
    let b = nodes[body];
    return if b.b != 0 { b.b } else { b.loc };
}

fn finish_igoto() {
    if f_igoto == NONE { return; }
    if has_insert() { emit_term(GIR_UNREACHABLE, 0, 0, 0); }
    start_block(f_igoto);
    var p = c_null();
    let npairs = f_igoto_vals.len / 2;
    if npairs > 0 {
        let s = m_opnds.len as! u32;
        for i in npairs {
            op_ref(f_igoto_vals[2 * i]);
            op_blk(f_igoto_vals[2 * i + 1]);
        }
        p = emit(GIR_PHI, GIR_T_PTR, 0, 0, 0, 0, s, npairs as! u32);
    }
    let s2 = m_opnds.len as! u32;
    for l in f_addr_labels { op_blk(label_block(l as i64)); }
    emit_term(GIR_INDIRECTBR, p, s2, f_addr_labels.len as! u32);
}
