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

// ---------------------------------------------------------- full unrolling
//
// (LLVM's LoopFullUnroll) A loop with a known trip count whose copies fit
// the threshold (150 instructions at -O1/-O2, 300 at -O3; none for optsize)
// is replaced by that many copies of its body in sequence: copy k's header
// PHIs take copy k-1's values from the latch, copy 0's take the preheader's;
// the exit test of copy k branches straight to copy k+1 (to the exit block
// after the last copy), and the values used after the loop are the last
// copy's. Only innermost loops whose one exiting block is the latch (a
// rotated loop) are unrolled.

var ur_map: u32[>..] = [];      // original instruction -> its copy in the current copy
var ur_bmap: u32[>..] = [];     // original block -> its copy
var ur_prev: u32[>..] = [];     // header PHI -> its value at the end of the previous copy
var ur_last: u32[>..] = [];     // loop value -> its value in the last copy
var ur_tmp: u32[>..] = [];

fn unroll_threshold() -> u32 {
    if o_f.flags & (FN_OPTSIZE | FN_MINSIZE) != 0 || opt_sz != 0 { return 0; }
    return if opt_lv >= 3 { 300 } else { 150 };
}

fn loop_unroll() -> bool {
    if o_pinned { return false; }
    let thr = unroll_threshold();
    if thr == 0 { return false; }
    ensure_cfg();
    loop_headers();
    var any = false;
    var k: i64 = 0;
    while k < lp_hdrs.len {
        let h = lp_hdrs[k];
        k++;
        if rpo_num[h] == NIL { continue; }
        if unroll_full(h, thr) {
            any = true;
            ensure_cfg();
            // (the other headers' loops are intact; RPO numbers changed)
        }
    }
    return any;
}

// The value v of the loop in the current copy.
inline fn ur_val(v0: u32) -> u32 {
    let v = res(v0);
    if is_inst(v) && v < ur_map.len && ur_map[v] != NIL { return ur_map[v]; }
    return v;
}

fn unroll_full(h: u32, thr: u32) -> bool {
    if !loop_collect(h) || lp_pre == NIL || lp_latch == NIL || lp_exit == NIL || lp_exiting != lp_latch { return false; }
    // innermost only: no other header in the body
    for b in lp_body {
        if b == h { continue; }
        for q in p_start[b]..p_start[b + 1] {
            let p = p_list[q];
            if rpo_num[p] != NIL && dominates(b, p) && in_loop(p) { return false; }
        }
    }
    let E = lp_exit;
    if b_fl[E] & BF_LP != 0 { return false; }
    // size; nothing that cannot be copied
    var size: u32 = 0;
    for b in lp_body {
        if b_fl[b] & BF_LP != 0 { return false; }
        var i = b_first[b];
        while i != NIL {
            let op: u32 = o_ins[i].op;
            if op == GIR_ALLOCA || op == GIR_DYNALLOCA || op == GIR_LANDINGPAD || op == GIR_INDIRECTBR
               || op == GIR_SWITCH || op == GIR_ASM || op == GIR_SJLJ_SETJMP { return false; }
            if op == GIR_CALL && o_ins[i].flags & IF_INVOKE != 0 { return false; }
            if op != GIR_PHI && op != GIR_BR { size++; }
            i = o_nxt[i];
        }
    }
    if !loop_trip(h) { return false; }
    let n = lp_trip;
    if n < 1 || n * size > thr || n > 64 { return false; }
    resolve_all();
    build_uses();
    let L = lp_latch;
    let n0: u32 = o_ins.len as! u32;
    if ur_map.len < n0 { ur_map.resize(n0, NIL); }
    for x in 0..n0 { ur_map[x] = NIL; }
    if ur_bmap.len < cfg_nb { ur_bmap.resize(cfg_nb, NIL); }
    // the header PHIs: their latch values per copy
    ur_tmp.clear();
    var i = b_first[h];
    while i != NIL && o_ins[i].op == GIR_PHI {
        ur_tmp.push(i);
        i = o_nxt[i];
    }
    let nphi = ur_tmp.len;
    ur_prev.clear();
    for ph in ur_tmp {
        let I = o_ins[ph];
        var lv: u32 = NIL;
        for q in 0..I.c { if o_ops[I.b + 2 * q + 1] == L { lv = res(o_ops[I.b + 2 * q]); } }
        if lv == NIL { return false; }
        ur_prev.push(lv);
    }
    // copy 0 is the loop itself: its header PHIs keep only the preheader's entry
    var last_latch = L;
    // copies 1 .. n-1
    for c in 1..n {
        // block copies (in the body's order), linked after the previous latch in layout
        for b in lp_body { ur_bmap[b] = new_block(); }
        // instruction copies
        for b in lp_body {
            let nb = ur_bmap[b];
            var j = b_first[b];
            while j != NIL {
                let I = o_ins[j];
                if b == h && I.op == GIR_PHI {
                    // (not copied: the previous copy's latch value, below)
                    j = o_nxt[j];
                    continue;
                }
                let x = new_inst(I);
                ur_map[j] = x;
                link_end(nb, x);
                j = o_nxt[j];
            }
        }
        // header PHIs of this copy: the previous copy's latch values
        for q in 0..nphi {
            let ph = ur_tmp[q];
            let pv = ur_prev[q];
            // (in copy c, uses of the PHI read pv as it was in copy c - 1)
            ur_map[ph] = pv;
        }
        // operands and successors of the copies
        for b in lp_body {
            var x = b_first[ur_bmap[b]];
            while x != NIL {
                ur_fix(x);
                x = o_nxt[x];
            }
        }
        // the previous copy's latch goes straight into this copy's header
        ur_retarget(last_latch, ur_bmap[h]);
        // the values at this copy's latch for the next copy
        for q in 0..nphi {
            let ph = ur_tmp[q];
            let I = o_ins[ph];
            var lv: u32 = NIL;
            for k in 0..I.c { if o_ops[I.b + 2 * k + 1] == L { lv = res(o_ops[I.b + 2 * k]); } }
            ur_prev[q] = ur_val(lv);
        }
        // layout: the copy after the previous latch's place
        var lb = last_latch;
        for b in lp_body {
            let nb = ur_bmap[b];
            b_lnext[nb] = b_lnext[lb];
            b_lnext[lb] = nb;
            lb = nb;
        }
        last_latch = ur_bmap[L];
        // values of the last copy (for the uses after the loop)
        if c == n - 1 {
            ur_last.clear();
            ur_last.resize(n0, NIL);
            for b in lp_body {
                var j = b_first[b];
                while j != NIL {
                    ur_last[j] = ur_val(j);
                    j = o_nxt[j];
                }
            }
        }
    }
    if n == 1 {
        ur_last.clear();
        ur_last.resize(n0, NIL);
        for b in lp_body {
            var j = b_first[b];
            while j != NIL {
                ur_last[j] = j;
                j = o_nxt[j];
            }
        }
    }
    // the last latch leaves for the exit
    let T = b_last[last_latch];
    o_ins[T].op = GIR_BR as! u8;
    o_ins[T].a = E;
    o_ins[T].b = 0;
    o_ins[T].c = 0;
    // copy 0's header PHIs: only the preheader's value
    phi_remove_pred(h, L);
    // the exit's PHIs and the other uses after the loop: the last copy's values
    var e = b_first[E];
    while e != NIL && o_ins[e].op == GIR_PHI {
        let I = o_ins[e];
        for q in 0..I.c {
            if o_ops[I.b + 2 * q + 1] == L {
                let v = res(o_ops[I.b + 2 * q]);
                o_ops[I.b + 2 * q + 1] = last_latch;
                if is_inst(v) && v < n0 && ur_last[v] != NIL { o_ops[I.b + 2 * q] = ur_last[v]; }
            }
        }
        e = o_nxt[e];
    }
    for b in lp_body {
        var j = b_first[b];
        while j != NIL {
            let lv = ur_last[j];
            if lv != j && lv != NIL {
                for q in u_start[j]..u_start[j + 1] {
                    let u = u_list[q];
                    if o_blk[u] == NIL || u >= n0 { continue; }
                    let ub = o_blk[u];
                    if ub < lp_mark.len as! u32 && in_loop(ub) || ub == E && o_ins[u].op == GIR_PHI { continue; }
                    each_slot(u) { s =>
                        if res(vget(u, s)) == j { vset(u, s, lv); }
                    };
                }
            }
            j = o_nxt[j];
        }
    }
    o_cfg_ok = false;
    return true;
}
// The operands of copy x mapped to the current copy, its successors to the
// copies of the blocks (the runs of PHIs, GEPs and calls copied first: the
// copy shares them with the original).
fn ur_fix(x: u32) {
    let I = o_ins[x];
    let op: u32 = I.op;
    if op == GIR_PHI || op == GIR_GEP || op == GIR_CALL {
        let n: u32 = if op == GIR_GEP { 2 + 2 * I.c } else { 2 * I.c };
        let s = new_run(n);
        for k in 0..n { o_ops[s + k] = o_ops[I.b + k]; }
        o_ins[x].b = s;
    }
    each_slot(x) { sl =>
        let v = vget(x, sl);
        vset(x, sl, ur_val(v));
    };
    if op == GIR_BR { o_ins[x].a = ur_blk(I.a); }
    else if op == GIR_CONDBR {
        o_ins[x].b = ur_blk(I.b);
        o_ins[x].c = ur_blk(I.c);
    } else if op == GIR_PHI {
        let s = o_ins[x].b;
        for k in 0..I.c { o_ops[s + 2 * k + 1] = ur_blk(o_ops[s + 2 * k + 1]); }
    }
}
inline fn ur_blk(b: u32) -> u32 {
    if b < lp_mark.len as! u32 && in_loop(b) { return ur_bmap[b]; }
    return b;
}
// Latch t (its exit test) becomes a branch to block to.
fn ur_retarget(latch: u32, to: u32) {
    let T = b_last[latch];
    o_ins[T].op = GIR_BR as! u8;
    o_ins[T].a = to;
    o_ins[T].b = 0;
    o_ins[T].c = 0;
}
