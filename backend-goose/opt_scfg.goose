// CFG simplification on the OIR (opt.goose): branches on constants and
// conditional branches to one block become plain branches, unreachable
// blocks go, a block is merged into its only predecessor when that one
// only branches to it, and the predecessors of a block that only branches
// on are sent to its target (trivial jump threading). Functions with pinned
// blocks (block addresses) only get the branch folding.

var sc_changed = false;
var sc_tmp: u32[>..] = [];

// Branches whose outcome is known (build_cfg first).
fn fold_branches() -> bool {
    var any = false;
    for b in rpo {
        let t = b_last[b];
        if t == NIL { continue; }
        let I = o_ins[t];
        if I.op == GIR_CONDBR {
            let c = res(I.a);
            if I.b == I.c {
                phi_remove_one(I.b, b);
                to_br(t, I.b);
                any = true;
            } else {
                let k, v = ci(c);
                if k {
                    let taken = if v != 0 { I.b } else { I.c };
                    let other = if v != 0 { I.c } else { I.b };
                    phi_remove_one(other, b);
                    to_br(t, taken);
                    any = true;
                }
            }
        } else if I.op == GIR_SWITCH {
            let c = res(I.a);
            let k, v = ci(c);
            if !k && I.c != 0 {
                // (E2) cases that go to the default are dropped; one case
                // left: a conditional branch (LLVM's SimplifyCFG)
                let d = o_ops[I.b];
                var w: u32 = 0;
                for q in 0..I.c {
                    let s = o_ops[I.b + 2 + 2 * q];
                    if s == d {
                        phi_remove_one(d, b);
                        o_cfg_ok = false;
                        any = true;
                        continue;
                    }
                    o_ops[I.b + 1 + 2 * w] = o_ops[I.b + 1 + 2 * q];
                    o_ops[I.b + 2 + 2 * w] = s;
                    w++;
                }
                o_ins[t].c = w;
                if w == 1 {
                    let e = new_inst(Inst { op: GIR_ICMP as! u8, sub: GIR_EQ as! u8, flags: 0, ty: GIR_T_I1,
                                            aux: otype(c) as! u16, a: c, b: o_ops[I.b + 1], c: 0, dbg: I.dbg });
                    link_before(t, e);
                    let ct = o_ops[I.b + 2];
                    o_ins[t].op = GIR_CONDBR as! u8;
                    o_ins[t].a = e;
                    o_ins[t].b = ct;
                    o_ins[t].c = d;
                    o_ins[t].sub = 0;
                    o_ins[t].aux = 0;
                    o_cfg_ok = false;
                    any = true;
                }
                if w == 0 { to_br(t, d); }
                continue;
            }
            var taken = o_ops[I.b];
            if k {
                for q in 0..I.c {
                    if cval(o_ops[I.b + 1 + 2 * q]) == v {
                        taken = o_ops[I.b + 2 + 2 * q];
                        break;
                    }
                }
            }
            // every edge but one into `taken` goes
            var kept = false;
            if o_ops[I.b] == taken { kept = true; } else { phi_remove_one(o_ops[I.b], b); }
            for q in 0..I.c {
                let s = o_ops[I.b + 2 + 2 * q];
                if s == taken && !kept { kept = true; } else { phi_remove_one(s, b); }
            }
            to_br(t, taken);
            any = true;
        }
    }
    return any;
}
fn to_br(t: u32, target: u32) {
    o_cfg_ok = false;
    o_ins[t].op = GIR_BR as! u8;
    o_ins[t].a = target;
    o_ins[t].b = 0;
    o_ins[t].c = 0;
    o_ins[t].sub = 0;
}

// Merges blocks into their only predecessor (build_cfg first; the
// predecessor counts stay valid while merging).
fn merge_blocks() -> bool {
    var any = false;
    for b in rpo {
        if !live_block(b) { continue; }
        loop {
            let t = b_last[b];
            if t == NIL || o_ins[t].op != GIR_BR || block_invoke(b) != NIL { break; }
            let s = o_ins[t].a;
            if s == b || s == 0 || b_fl[s] & (BF_LP | BF_DEAD | BF_ADDR) != 0 || p_start[s + 1] - p_start[s] != 1 { break; }
            // PHIs of a block with one predecessor are their value
            var i = b_first[s];
            while i != NIL && o_ins[i].op == GIR_PHI {
                let nx = o_nxt[i];
                replace(i, res(o_ops[o_ins[i].b]));
                i = nx;
            }
            unlink(t);
            o_cfg_ok = false;
            // move s's instructions to the end of b
            i = b_first[s];
            while i != NIL {
                let nx = o_nxt[i];
                o_prv[i] = NIL;
                o_nxt[i] = NIL;
                o_blk[i] = NIL;
                link_end(b, i);
                i = nx;
            }
            b_first[s] = NIL;
            b_last[s] = NIL;
            b_fl[s] |= BF_DEAD;
            // s's successors now come from b
            sc_tmp.clear();
            succs_into(b, sc_tmp);
            for x in sc_tmp { phi_rename_pred(x, s, b); }
            any = true;
        }
    }
    return any;
}

// Sends the predecessors of blocks that are only `br T` (no PHIs) straight to
// T where T's PHIs allow it (build_cfg first).
var fe_dirty: u32[>..] = [];
var fe_epoch: u32 = 0;
fn forward_empty() -> bool {
    var any = false;
    if fe_dirty.len < cfg_nb { fe_dirty.resize(cfg_nb, 0); }
    fe_epoch++;
    for e in rpo {
        // (a block that gained predecessors this round has a stale predecessor list)
        if e == 0 || b_fl[e] & (BF_LP | BF_DEAD | BF_ADDR) != 0 || fe_dirty[e] == fe_epoch { continue; }
        let t = b_first[e];
        if t == NIL || t != b_last[e] || o_ins[t].op != GIR_BR { continue; }
        let tg = o_ins[t].a;
        if tg == e { continue; }
        var all = true;
        var done = false;
        for k in p_start[e]..p_start[e + 1] {
            let p = p_list[k];
            if k > p_start[e] && p_list[k - 1] == p { continue; }   // (edges from one block are adjacent)
            if !redirect(p, e, tg) { all = false; }
            else {
                done = true;
                fe_dirty[tg] = fe_epoch;
            }
        }
        if done { any = true; }
        if all && done { phi_remove_pred(tg, e); }
    }
    return any;
}
// Redirects the edges p -> e to e's target tg (adding PHI entries in tg);
// false if tg's PHIs disagree with that or p's terminator cannot be changed.
fn redirect(p: u32, e: u32, tg: u32) -> bool {
    if !live_block(p) || p == e { return false; }
    let pt = b_last[p];
    let op: u32 = o_ins[pt].op;
    if op != GIR_BR && op != GIR_CONDBR && op != GIR_SWITCH { return false; }
    let iv = block_invoke(p);
    if iv != NIL && o_ops[o_ins[iv].b + 2 * o_ins[iv].c] == e { return false; }
    // PHIs of tg: p's existing entries must agree with e's
    var i = b_first[tg];
    while i != NIL && o_ins[i].op == GIR_PHI {
        let ve = phi_in(i, e);
        let vp = phi_in(i, p);
        if ve == NIL { return false; }
        if vp != NIL && res(vp) != res(ve) { return false; }
        i = o_nxt[i];
    }
    // count and redirect the edges
    var n: u32 = 0;
    if op == GIR_BR {
        if o_ins[pt].a == e { o_ins[pt].a = tg; n++; }
    } else if op == GIR_CONDBR {
        if o_ins[pt].b == e { o_ins[pt].b = tg; n++; }
        if o_ins[pt].c == e { o_ins[pt].c = tg; n++; }
    } else {
        let s = o_ins[pt].b;
        if o_ops[s] == e { o_ops[s] = tg; n++; }
        for q in 0..o_ins[pt].c {
            if o_ops[s + 2 + 2 * q] == e { o_ops[s + 2 + 2 * q] = tg; n++; }
        }
    }
    if n == 0 { return false; }
    o_cfg_ok = false;
    // n entries for p in each PHI of tg (e's value)
    i = b_first[tg];
    while i != NIL && o_ins[i].op == GIR_PHI {
        let I = o_ins[i];
        let ve = phi_in(i, e);
        let ns = new_run(2 * (I.c + n));
        for q in 0..2 * I.c { o_ops[ns + q] = o_ops[I.b + q]; }
        for q in 0..n {
            o_ops[ns + 2 * (I.c + q)] = ve;
            o_ops[ns + 2 * (I.c + q) + 1] = p;
        }
        o_ins[i].b = ns;
        o_ins[i].c = I.c + n;
        i = o_nxt[i];
    }
    return true;
}

// If-conversion of small triangles and diamonds (LLVM's
// SpeculativelyExecuteBB and FoldTwoEntryPHINode): `condbr c, T, J` where T
// is only reached from here, computes a few cheap values and branches to J
// (or `condbr c, T, F` with T and F both such blocks branching to J) becomes
// the hoisted instructions and one select per PHI of J whose incoming values
// differ, and the branch goes straight to J. Only integer and pointer PHIs
// (their select is a cmov); a branch that is hard to predict then costs
// nothing. (build_cfg first.)
let SPEC_MAX: u32 = 4;          // speculated instructions per conversion
let SEL_MAX: u32 = 2;           // selects per conversion
fn spec_op(I: Inst) -> bool {
    let op: u32 = I.op;
    if !(op >= GIR_ADD && op <= GIR_MUL || op >= GIR_AND && op <= GIR_BITCAST || op == GIR_GEP) { return false; }
    return int_ty(I.ty) && bits_of(I.ty) <= 64;
}
// The number of instructions block b (only reached from a) would speculate,
// or NIL if it cannot be.
fn spec_block(b: u32, a: u32) -> u32 {
    if b == a || b == 0 || b_fl[b] & (BF_LP | BF_DEAD | BF_ADDR) != 0 { return NIL; }
    if p_start[b + 1] - p_start[b] != 1 || p_list[p_start[b]] != a { return NIL; }
    let t = b_last[b];
    if t == NIL || o_ins[t].op != GIR_BR { return NIL; }
    var n: u32 = 0;
    var i = b_first[b];
    while i != t {
        if !spec_op(o_ins[i]) { return NIL; }
        n++;
        if n > SPEC_MAX { return NIL; }
        i = o_nxt[i];
    }
    return n;
}
// Moves block b's instructions but its terminator before instruction at.
fn spec_hoist(b: u32, at: u32) {
    let t = b_last[b];
    var i = b_first[b];
    while i != t {
        let nx = o_nxt[i];
        unlink(i);
        link_before(at, i);
        i = nx;
    }
}
// Whether an instruction of block b (if on) but its terminator uses value v.
fn spec_uses(b: u32, on: bool, v: u32) -> bool {
    if !on { return false; }
    let t = b_last[b];
    var i = b_first[b];
    var u = false;
    while i != t {
        each_slot(i) { s =>
            if res(vget(i, s)) == v { u = true; }
        };
        i = o_nxt[i];
    }
    return u;
}
// In PHI i, the entries from p1 and p2 become one entry (v, a).
fn phi_merge2(i: u32, p1: u32, p2: u32, v: u32, a: u32) {
    let I = o_ins[i];
    var n: u32 = 0;
    var done = false;
    for k in 0..I.c {
        let p = o_ops[I.b + 2 * k + 1];
        if p == p1 || p == p2 {
            if done { continue; }
            done = true;
            o_ops[I.b + 2 * n] = v;
            o_ops[I.b + 2 * n + 1] = a;
        } else {
            o_ops[I.b + 2 * n] = o_ops[I.b + 2 * k];
            o_ops[I.b + 2 * n + 1] = p;
        }
        n++;
    }
    o_ins[i].c = n;
}
fn fold_selects() -> bool {
    var any = false;
    for a in rpo {
        let t = b_last[a];
        if t == NIL || o_ins[t].op != GIR_CONDBR || block_invoke(a) != NIL { continue; }
        let x = o_ins[t].b;
        let y = o_ins[t].c;
        if x == y { continue; }
        let nx = spec_block(x, a);
        let ny = spec_block(y, a);
        var J: u32 = NIL;
        var px = a;     // J's predecessor on the true side
        var py = a;
        if nx != NIL && o_ins[b_last[x]].a == y {
            J = y;
            px = x;
        } else if ny != NIL && o_ins[b_last[y]].a == x {
            J = x;
            py = y;
        } else if nx != NIL && ny != NIL && o_ins[b_last[x]].a == o_ins[b_last[y]].a && nx + ny <= SPEC_MAX {
            J = o_ins[b_last[x]].a;
            px = x;
            py = y;
        }
        if J == NIL || J == a || J == x && px == x || J == y && py == y || b_fl[J] & BF_LP != 0 { continue; }
        // J's PHIs: one entry from each side; the differing ones become selects
        var ns: u32 = 0;
        var ok = true;
        var i = b_first[J];
        while i != NIL && o_ins[i].op == GIR_PHI {
            let vx = phi_in(i, px);
            let vy = phi_in(i, py);
            if vx == NIL || vy == NIL { ok = false; break; }
            if res(vx) != res(vy) {
                let pt = o_ins[i].ty;
                // (E2) FP values when the condition is an FP compare (a
                // select of its operands is maxss / minss)
                let c0 = res(o_ins[t].a);
                let fp = (pt == GIR_T_F32 || pt == GIR_T_F64) && is_inst(c0) && o_ins[c0].op == GIR_FCMP;
                if !(int_ty(pt) && bits_of(pt) <= 64) && !fp { ok = false; break; }
                ns++;
            }
            i = o_nxt[i];
        }
        if !ok || ns > SEL_MAX { continue; }
        // (before the compare that feeds the branch when it is right there,
        // so that the compare sets the flags for the select)
        let c = res(o_ins[t].a);
        var at = t;
        if is_inst(c) && o_nxt[c] == t && (o_ins[c].op == GIR_ICMP || o_ins[c].op == GIR_FCMP) && !spec_uses(x, px != a, c)
           && !spec_uses(y, py != a, c) {
            at = c;
        }
        if px != a { spec_hoist(x, at); }
        if py != a { spec_hoist(y, at); }
        i = b_first[J];
        while i != NIL && o_ins[i].op == GIR_PHI {
            let vx = res(phi_in(i, px));
            let vy = res(phi_in(i, py));
            var v = vx;
            if vx != vy {
                v = new_inst(Inst { op: GIR_SELECT as! u8, sub: 0, flags: 0, ty: o_ins[i].ty, aux: 0, a: c, b: vx,
                                    c: vy, dbg: o_ins[t].dbg });
                link_before(t, v);
            }
            phi_merge2(i, px, py, v, a);
            i = o_nxt[i];
        }
        // (the speculated blocks are unreachable now: remove_unreachable
        // deletes them; their PHI entries in J are gone already)
        to_br(t, J);
        any = true;
    }
    return any;
}

// The whole simplification, until nothing changes (at most a few rounds).
fn simplify_cfg() -> bool {
    var any = false;
    for round in 4 {
        ensure_cfg();
        var ch = false;
        if fold_branches() { ch = true; }
        if ch {
            ensure_cfg();
            remove_unreachable();
            ensure_cfg();
        }
        if !o_pinned {
            if merge_blocks() {
                ch = true;
                ensure_cfg();
            }
            if forward_empty() {
                ch = true;
                ensure_cfg();
                remove_unreachable();
            }
            ensure_cfg();
            if thread_phis() {
                ch = true;
                ensure_cfg();
                remove_unreachable();
            }
            ensure_cfg();
            if !opt_off("select") && fold_selects() {
                ch = true;
                ensure_cfg();
                remove_unreachable();
            }
        }
        if !ch { break; }
        any = true;
    }
    return any;
}

// Jump threading of a branch on a PHI: a block M of only PHIs and `condbr P,
// X, Y` with P one of its PHIs (what `while (a && b)` leaves: P = phi
// [false, A], [b, B]) sends each predecessor whose incoming P is a constant
// straight to X or Y. M's PHIs may only be used by that branch and as
// incoming values from M in X's and Y's PHIs (they then get the
// predecessor's value). (build_cfg first.)
var th_mark: u8[>..] = [];      // per instruction: 1 = a PHI of a candidate block, 2 = used elsewhere
fn thread_phis() -> bool {
    var cand = false;
    if th_mark.len < o_ins.len { th_mark.resize(o_ins.len, 0); }
    for m in rpo {
        if thread_cand(m) == NIL { continue; }
        cand = true;
        var i = b_first[m];
        while o_ins[i].op == GIR_PHI {
            th_mark[i] = 1;
            i = o_nxt[i];
        }
    }
    if !cand { return false; }
    // one scan for the uses of the candidates' PHIs (no use lists)
    for u0 in 0..o_ins.len {
        let u: u32 = u0 as! u32;
        if o_blk[u] == NIL { continue; }
        each_slot(u) { sl =>
            let v = res(vget(u, sl));
            if is_inst(v) && v < th_mark.len && th_mark[v] != 0 && !thread_use_ok(v, u, sl) { th_mark[v] = 2; }
        };
    }
    var any = false;
    for m in rpo {
        let P = thread_cand(m);
        if P == NIL { continue; }
        var ok = true;
        var i = b_first[m];
        while o_ins[i].op == GIR_PHI {
            if th_mark[i] == 2 { ok = false; }
            th_mark[i] = 0;
            i = o_nxt[i];
        }
        if !ok { continue; }
        let t = b_last[m];
        let X = o_ins[t].b;
        let Y = o_ins[t].c;
        if X == m || Y == m || X == Y { continue; }
        // the predecessors with a constant P (distinct blocks; one edge each)
        for k in p_start[m]..p_start[m + 1] {
            let a = p_list[k];
            if k > p_start[m] && p_list[k - 1] == a { continue; }
            if k + 1 < p_start[m + 1] && p_list[k + 1] == a { continue; }   // (several edges: skip)
            let v = phi_in(P, a);
            let kc, c = ci(res(v));
            if !kc { continue; }
            let T = if c != 0 { X } else { Y };
            if thread_edge(a, m, T) { any = true; }
        }
    }
    return any;
}
// P if block m is a candidate (only PHIs and a condbr on one of them), else NIL.
fn thread_cand(m: u32) -> u32 {
    if m == 0 || b_fl[m] & (BF_LP | BF_DEAD | BF_ADDR) != 0 { return NIL; }
    let t = b_last[m];
    if t == NIL || o_ins[t].op != GIR_CONDBR || block_invoke(m) != NIL { return NIL; }
    let c = res(o_ins[t].a);
    if !is_inst(c) || o_blk[c] != m || o_ins[c].op != GIR_PHI { return NIL; }
    var i = b_first[m];
    while i != t {
        if o_ins[i].op != GIR_PHI { return NIL; }
        i = o_nxt[i];
    }
    return c;
}
// Whether the use of PHI v (of candidate block m) by instruction u at slot
// sl is allowed: m's branch, or a PHI of X or Y taking v as the value from m.
fn thread_use_ok(v: u32, u: u32, sl: u32) -> bool {
    let m = o_blk[v];
    let t = b_last[m];
    if u == t { return true; }
    let U = o_ins[u];
    if U.op != GIR_PHI || o_blk[u] != o_ins[t].b && o_blk[u] != o_ins[t].c || sl < SLOT_RUN { return false; }
    return o_ops[(sl & ~SLOT_RUN) + 1] == m;
}
// Redirects the edge a -> m to T (m ends in a branch to T among others).
fn thread_edge(a: u32, m: u32, T: u32) -> bool {
    if !live_block(a) || a == m { return false; }
    let at = b_last[a];
    let op: u32 = o_ins[at].op;
    if op != GIR_BR && op != GIR_CONDBR { return false; }
    let iv = block_invoke(a);
    if iv != NIL { return false; }
    // T's PHIs: the value of the edge m -> T as seen from a
    var i = b_first[T];
    while i != NIL && o_ins[i].op == GIR_PHI {
        let vm = phi_in(i, m);
        if vm == NIL { return false; }
        var va = res(vm);
        if is_inst(va) && o_blk[va] == m && o_ins[va].op == GIR_PHI { va = res(phi_in(va, a)); }
        let old = phi_in(i, a);
        if old != NIL && res(old) != va { return false; }
        i = o_nxt[i];
    }
    if op == GIR_CONDBR && (o_ins[at].b == T || o_ins[at].c == T) { return false; }   // (keep it simple)
    // T gets an entry for a; m loses a's
    i = b_first[T];
    while i != NIL && o_ins[i].op == GIR_PHI {
        let I = o_ins[i];
        var va = res(phi_in(i, m));
        if is_inst(va) && o_blk[va] == m && o_ins[va].op == GIR_PHI { va = res(phi_in(va, a)); }
        let ns = new_run(2 * (I.c + 1));
        for q in 0..2 * I.c { o_ops[ns + q] = o_ops[I.b + q]; }
        o_ops[ns + 2 * I.c] = va;
        o_ops[ns + 2 * I.c + 1] = a;
        o_ins[i].b = ns;
        o_ins[i].c = I.c + 1;
        i = o_nxt[i];
    }
    phi_remove_one(m, a);
    if op == GIR_BR { o_ins[at].a = T; }
    else if o_ins[at].b == m { o_ins[at].b = T; }
    else { o_ins[at].c = T; }
    o_cfg_ok = false;
    return true;
}
