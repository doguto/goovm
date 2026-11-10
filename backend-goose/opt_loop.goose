// Loop passes of the middle-end (milestone E2): trip counts, loop deletion,
// loop unrolling (opt.goose).
//
// A loop is a natural loop of its header h (the blocks that reach a back
// edge's source without passing h), with a preheader (one block outside the
// loop that only branches to h). The trip count is found when the loop has
// one exiting block, the header or the latch, that ends in a branch on an
// integer or pointer compare of an induction variable (a PHI of h: init
// from the preheader, iv + constant from the latch, or a constant GEP of
// it) with a value from outside the loop, and init and that bound are
// constants (pointers: constant offsets from one base): the exit is then
// simulated, at most LP_MAXTRIP times.
//
// Loop deletion (LLVM's LoopDeletion): a loop without effects (no stores,
// calls that may write, volatile accesses, ...) whose values are not used
// after it, with one exit block, that terminates (a known trip count, or a
// mustprogress function: C++), is replaced by a branch to its exit.

let LP_MAXTRIP: u32 = 4096;

var lp_mark: u32[>..] = [];
var lp_ep: u32 = 0;
var lp_body: u32[>..] = [];
var lp_hdrs: u32[>..] = [];
var lp_pre: u32 = 0;            // the loop's preheader (NIL: none)
var lp_latch: u32 = 0;          // its only latch (NIL: several)
var lp_exit: u32 = 0;           // its only exit block (NIL: several)
var lp_exiting: u32 = 0;        // its only exiting block (NIL: several)
var lp_trip: u32 = 0;           // after loop_trip: the number of times the exiting block runs
var lp_iv: u32 = 0;             //   the induction variable (header PHI), its start, its step
var lp_init: u32 = 0;
var lp_step: u64 = 0;

inline fn in_loop(b: u32) -> bool { lp_mark[b] == lp_ep }

// The headers of the function's loops, inner loops (later in RPO) first.
fn loop_headers() {
    lp_hdrs.clear();
    for h in rpo {
        if h == 0 || b_fl[h] & BF_LP != 0 { continue; }
        for k in p_start[h]..p_start[h + 1] {
            let p = p_list[k];
            if rpo_num[p] != NIL && dominates(h, p) {
                lp_hdrs.push(h);
                break;
            }
        }
    }
    // (reverse: inner first)
    var a: i64 = 0;
    var e: i64 = lp_hdrs.len - 1;
    while a < e {
        let t = lp_hdrs[a];
        lp_hdrs[a] = lp_hdrs[e];
        lp_hdrs[e] = t;
        a++;
        e--;
    }
}

// Marks the loop of header h (lp_mark == lp_ep), fills lp_body, lp_pre,
// lp_latch, lp_exit, lp_exiting. False if h heads no loop.
fn loop_collect(h: u32) -> bool {
    if lp_mark.len < cfg_nb { lp_mark.resize(cfg_nb, 0); }
    lp_ep++;
    lp_body.clear();
    lp_mark[h] = lp_ep;
    lp_body.push(h);
    lp_pre = NIL;
    lp_latch = NIL;
    var npre = 0;
    var nlatch = 0;
    tmp_stack.clear();
    for k in p_start[h]..p_start[h + 1] {
        let p = p_list[k];
        if rpo_num[p] == NIL { continue; }
        if dominates(h, p) {
            if lp_latch != p { nlatch++; }
            lp_latch = p;
            if lp_mark[p] != lp_ep {
                lp_mark[p] = lp_ep;
                lp_body.push(p);
                tmp_stack.push(p);
            }
        } else {
            if lp_pre != p { npre++; }
            lp_pre = p;
        }
    }
    if nlatch == 0 { return false; }
    if nlatch != 1 { lp_latch = NIL; }
    while tmp_stack.len != 0 {
        let b = tmp_stack.pop();
        for k in p_start[b]..p_start[b + 1] {
            let q = p_list[k];
            if rpo_num[q] == NIL || lp_mark[q] == lp_ep { continue; }
            lp_mark[q] = lp_ep;
            lp_body.push(q);
            tmp_stack.push(q);
        }
    }
    if npre != 1 || s_start[lp_pre + 1] - s_start[lp_pre] != 1 || block_invoke(lp_pre) != NIL { lp_pre = NIL; }
    lp_exit = NIL;
    lp_exiting = NIL;
    var nexit = 0;
    var nexiting = 0;
    for b in lp_body {
        var out = false;
        for k in s_start[b]..s_start[b + 1] {
            let s = s_list[k];
            if in_loop(s) { continue; }
            out = true;
            if lp_exit != s { nexit++; }
            lp_exit = s;
        }
        if out {
            nexiting++;
            lp_exiting = b;
        }
    }
    if nexit != 1 { lp_exit = NIL; }
    if nexiting != 1 { lp_exiting = NIL; }
    return true;
}

// Whether value v is defined outside the loop (or is not an instruction).
fn lp_invariant(v0: u32) -> bool {
    let v = res(v0);
    if !is_inst(v) { return true; }
    return o_blk[v] == NIL || !in_loop(o_blk[v]);
}

// (base, offset) of an integer constant or a constant-offset pointer; base
// NIL for an integer. ok false otherwise.
fn lp_point(v: u32) -> bool, u32, i64 {
    let k, x = ci(res(v));
    if k { return true, NIL, x as! i64; }
    if otype(res(v)) != GIR_T_PTR { return false, NIL, 0; }
    let b, off, known = aa_decompose(v);
    if !known { return false, NIL, 0; }
    return true, b, off;
}

// The trip count of the collected loop (loop_collect first): true with
// lp_trip, lp_iv, lp_init, lp_step when it is known.
fn loop_trip(h: u32) -> bool {
    let x = lp_exiting;
    if x == NIL || lp_pre == NIL || lp_latch == NIL { return false; }
    if x != h && x != lp_latch { return false; }
    let T = o_ins[b_last[x]];
    if T.op != GIR_CONDBR { return false; }
    let exit_on_true = !in_loop(T.b);
    let c = res(T.a);
    if !is_inst(c) || o_ins[c].op != GIR_ICMP { return false; }
    let C = o_ins[c];
    var pred: u32 = C.sub;
    var a = res(C.a);
    var bnd = res(C.b);
    // the induction side first
    if lp_invariant(a) {
        let t = a;
        a = bnd;
        bnd = t;
        pred = swap_pred(pred);
    }
    if !lp_invariant(bnd) || lp_invariant(a) { return false; }
    // a is the IV (a header PHI) or its next value
    var iv: u32 = NIL;
    var next = false;
    if is_inst(a) && o_ins[a].op == GIR_PHI && o_blk[a] == h { iv = a; }
    else {
        let A = o_ins[a];
        if A.op == GIR_ADD || A.op == GIR_GEP {
            let base = res(A.a);
            if is_inst(base) && o_ins[base].op == GIR_PHI && o_blk[base] == h {
                iv = base;
                next = true;
            }
        }
    }
    if iv == NIL { return false; }
    let P = o_ins[iv];
    if P.c != 2 { return false; }
    var init: u32 = NIL;
    var nv: u32 = NIL;
    for k in 0..2 {
        let pb = o_ops[P.b + 2 * k + 1];
        if pb == lp_pre { init = res(o_ops[P.b + 2 * k]); }
        if pb == lp_latch { nv = res(o_ops[P.b + 2 * k]); }
    }
    if init == NIL || nv == NIL || !is_inst(nv) { return false; }
    let N = o_ins[nv];
    var step: u64 = 0;
    if N.op == GIR_ADD && res(N.a) == iv {
        let k, s = ci(res(N.b));
        if !k { return false; }
        step = s;
    } else if N.op == GIR_GEP && res(N.a) == iv && N.c == 0 {
        step = o_ops[N.b] as u64 | (o_ops[N.b + 1] as u64 << 32);
    } else {
        return false;
    }
    if next && a != nv { return false; }
    let bits: u32 = if otype(iv) == GIR_T_PTR { 64 } else { bits_of(otype(iv)) };
    if bits > 64 || bits == 0 { return false; }
    let ok1, b1, x1 = lp_point(init);
    let ok2, b2, x2 = lp_point(bnd);
    if !ok1 || !ok2 || b1 != b2 { return false; }
    let m = wmask(bits);
    var v: u64 = (x1 as! u64) & m;
    if next { v = (v + step) & m; }
    let bv: u64 = (x2 as! u64) & m;
    var n: u32 = 0;
    while n < LP_MAXTRIP {
        n++;
        let r = fold_icmp(pred, bits, v, bv);
        if r == exit_on_true {
            lp_trip = n;
            lp_iv = iv;
            lp_init = init;
            lp_step = step;
            return true;
        }
        v = (v + step) & m;
    }
    return false;
}
// ---------------------------------------------------------- deletion

fn loop_delete() -> bool {
    if o_pinned { return false; }
    ensure_cfg();
    loop_headers();
    var any = false;
    for h in lp_hdrs {
        if rpo_num[h] == NIL { continue; }
        if loop_delete_one(h) {
            any = true;
            ensure_cfg();
            if remove_unreachable() { ensure_cfg(); }
        }
    }
    return any;
}

fn loop_delete_one(h: u32) -> bool {
    if !loop_collect(h) || lp_pre == NIL || lp_exit == NIL { return false; }
    let E = lp_exit;
    if b_fl[E] & BF_LP != 0 { return false; }
    // no effects
    for b in lp_body {
        var i = b_first[b];
        while i != NIL {
            let I = o_ins[i];
            let op: u32 = I.op;
            if op != GIR_BR && op != GIR_CONDBR && op != GIR_SWITCH && (has_effect(I) || writes_mem(I)) { return false; }
            if op == GIR_LOAD && I.flags & (IF_VOLATILE | IF_ORD_MASK) != 0 { return false; }
            i = o_nxt[i];
        }
    }
    // E's PHIs: one loop-invariant value from all the exiting edges
    var i = b_first[E];
    while i != NIL && o_ins[i].op == GIR_PHI {
        let I = o_ins[i];
        var v: u32 = NIL;
        for k in 0..I.c {
            if !in_loop(o_ops[I.b + 2 * k + 1]) { continue; }
            let x = res(o_ops[I.b + 2 * k]);
            if v != NIL && v != x { return false; }
            v = x;
        }
        if v != NIL && !lp_invariant(v) { return false; }
        i = o_nxt[i];
    }
    // no other use of the loop's values outside it
    resolve_all();
    build_uses();
    for b in lp_body {
        var j = b_first[b];
        while j != NIL {
            for q in u_start[j]..u_start[j + 1] {
                let u = u_list[q];
                if o_blk[u] == NIL || in_loop(o_blk[u]) { continue; }
                return false;
            }
            j = o_nxt[j];
        }
    }
    // it ends
    if o_f.flags & FN_MUSTPROGRESS == 0 && !loop_trip(h) { return false; }
    // the preheader goes to the exit; E's PHIs take their value from it
    var ph = b_first[E];
    while ph != NIL && o_ins[ph].op == GIR_PHI {
        let I = o_ins[ph];
        var v: u32 = NIL;
        var n: u32 = 0;
        let s = new_run(2 * I.c + 2);
        for k in 0..I.c {
            let p = o_ops[I.b + 2 * k + 1];
            if in_loop(p) {
                v = res(o_ops[I.b + 2 * k]);
                continue;
            }
            o_ops[s + 2 * n] = o_ops[I.b + 2 * k];
            o_ops[s + 2 * n + 1] = p;
            n++;
        }
        o_ops[s + 2 * n] = v;
        o_ops[s + 2 * n + 1] = lp_pre;
        o_ins[ph].b = s;
        o_ins[ph].c = n + 1;
        ph = o_nxt[ph];
    }
    o_ins[b_last[lp_pre]].a = E;
    o_cfg_ok = false;
    return true;
}
