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
            if !k && I.c != 0 { continue; }
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
            if s == b || s == 0 || b_fl[s] & (BF_LP | BF_DEAD) != 0 || p_start[s + 1] - p_start[s] != 1 { break; }
            // PHIs of a block with one predecessor are their value
            var i = b_first[s];
            while i != NIL && o_ins[i].op == GIR_PHI {
                let nx = o_nxt[i];
                replace(i, res(o_ops[o_ins[i].b]));
                i = nx;
            }
            unlink(t);
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
        if e == 0 || b_fl[e] & (BF_LP | BF_DEAD) != 0 || fe_dirty[e] == fe_epoch { continue; }
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

// The whole simplification, until nothing changes (at most a few rounds).
fn simplify_cfg() -> bool {
    var any = false;
    for round in 4 {
        build_cfg();
        var ch = false;
        if fold_branches() { ch = true; }
        if ch {
            build_cfg();
            remove_unreachable();
            build_cfg();
        }
        if !o_pinned {
            if merge_blocks() {
                ch = true;
                build_cfg();
            }
            if forward_empty() {
                ch = true;
                build_cfg();
                remove_unreachable();
            }
        }
        if !ch { break; }
        any = true;
    }
    return any;
}
