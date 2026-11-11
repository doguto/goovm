// CFG analyses of the OIR function (opt.goose): successor and predecessor
// lists (CSR arrays, one entry per CFG edge), reverse post-order,
// dominators (Cooper, Harvey and Kennedy's iterative algorithm on the RPO),
// the dominator tree with pre-order intervals, dominance frontiers, natural
// loops, and the removal of unreachable blocks. All of it is recomputed
// (build_cfg) after a pass that changes the CFG.

var s_start: u32[>..] = [];     // per block: its successors s_list[s_start[b] .. s_start[b + 1])
var s_list: u32[>..] = [];
var p_start: u32[>..] = [];     // per block: its predecessors (one per edge)
var p_list: u32[>..] = [];
var p_cnt: u32[>..] = [];
var rpo: u32[>..] = [];         // reachable blocks in reverse post-order
var rpo_num: u32[>..] = [];     // per block: its position in rpo, NIL = unreachable
var idom: u32[>..] = [];
var dt_first: u32[>..] = [];    // dominator tree: first child, next sibling
var dt_next: u32[>..] = [];
var dt_pre: u32[>..] = [];      // pre-order number; subtree = [dt_pre, dt_end)
var dt_end: u32[>..] = [];
var dt_order: u32[>..] = [];    // blocks in dominator-tree pre-order
var df_head: u32[>..] = [];     // dominance frontier of each block: linked list
var df_blk: u32[>..] = [];
var df_nxt: u32[>..] = [];
var lp_depth: u8[>..] = [];     // loop nesting depth of each block (saturating)
var cfg_nb: u32 = 0;
var tmp_stack: u32[>..] = [];
var tmp_pos: u32[>..] = [];

// The invoke of block b (the CALL before its terminator), NIL if none.
fn block_invoke(b: u32) -> u32 {
    let t = b_last[b];
    if t == NIL { return NIL; }
    let p = o_prv[t];
    if p != NIL && o_ins[p].op == GIR_CALL && o_ins[p].flags & IF_INVOKE != 0 { return p; }
    return NIL;
}
// Appends the successors of b (one per edge) to out.
fn succs_into(b: u32, out: u32[>..]&) {
    let t = b_last[b];
    if t == NIL { return; }
    let I = o_ins[t];
    let op: u32 = I.op;
    if op == GIR_BR { out.push(I.a); }
    else if op == GIR_CONDBR {
        out.push(I.b);
        out.push(I.c);
    } else if op == GIR_SWITCH {
        out.push(o_ops[I.b]);
        for k in 0..I.c { out.push(o_ops[I.b + 2 + 2 * k]); }
    } else if op == GIR_INDIRECTBR {
        for k in 0..I.c { out.push(o_ops[I.b + k]); }
    }
    let iv = block_invoke(b);
    if iv != NIL { out.push(o_ops[o_ins[iv].b + 2 * o_ins[iv].c]); }
}
inline fn live_block(b: u32) -> bool { b_fl[b] & BF_DEAD == 0 }

// The CFG analyses, if the CFG changed since they were made.
fn ensure_cfg() { if !o_cfg_ok { build_cfg(); } }

// Successor and predecessor lists, RPO, dominators and the dominator tree of
// the current OIR function.
fn build_cfg() {
    o_cfg_ok = true;
    let nb: u32 = b_first.len as! u32;
    cfg_nb = nb;
    s_start.clear();
    s_list.clear();
    for b in 0..nb {
        s_start.push(s_list.len as! u32);
        if live_block(b) { succs_into(b, s_list); }
    }
    s_start.push(s_list.len as! u32);
    p_cnt.clear();
    p_cnt.resize(nb + 1, 0);
    for b in 0..nb {
        for k in s_start[b]..s_start[b + 1] { p_cnt[s_list[k]]++; }
    }
    p_start.clear();
    var acc: u32 = 0;
    for b in 0..nb {
        p_start.push(acc);
        acc += p_cnt[b];
        p_cnt[b] = 0;
    }
    p_start.push(acc);
    p_list.clear();
    p_list.resize(acc, 0);
    for b in 0..nb {
        for k in s_start[b]..s_start[b + 1] {
            let s = s_list[k];
            p_list[p_start[s] + p_cnt[s]] = b;
            p_cnt[s]++;
        }
    }
    build_rpo();
    build_dom();
}

// Reverse post-order of the blocks reachable from block 0 (iterative DFS).
fn build_rpo() {
    let nb = cfg_nb;
    rpo_num.clear();
    rpo_num.resize(nb, NIL);
    tmp_pos.clear();
    tmp_pos.resize(nb, 0);
    tmp_stack.clear();
    rpo.clear();
    // post-order into rpo, then reversed
    tmp_stack.push(0);
    rpo_num[0] = 0;          // (visited mark until numbered)
    tmp_pos[0] = s_start[0];
    while tmp_stack.len != 0 {
        let b = tmp_stack[tmp_stack.len - 1];
        let k = tmp_pos[b];
        if k < s_start[b + 1] {
            tmp_pos[b] = k + 1;
            let s = s_list[k];
            if rpo_num[s] == NIL {
                rpo_num[s] = 0;
                tmp_pos[s] = s_start[s];
                tmp_stack.push(s);
            }
        } else {
            tmp_stack.pop();
            rpo.push(b);
        }
    }
    reverse(rpo);
    for b, k in rpo { rpo_num[b] = k as! u32; }
}

fn dom_intersect(a0: u32, b0: u32) -> u32 {
    var a = a0;
    var b = b0;
    while a != b {
        while rpo_num[a] > rpo_num[b] { a = idom[a]; }
        while rpo_num[b] > rpo_num[a] { b = idom[b]; }
    }
    return a;
}
fn build_dom() {
    let nb = cfg_nb;
    idom.clear();
    idom.resize(nb, NIL);
    idom[0] = 0;
    var changed = true;
    while changed {
        changed = false;
        for b in rpo {
            if b == 0 { continue; }
            var nd: u32 = NIL;
            for k in p_start[b]..p_start[b + 1] {
                let p = p_list[k];
                if rpo_num[p] == NIL || idom[p] == NIL { continue; }
                nd = if nd == NIL { p } else { dom_intersect(p, nd) };
            }
            if idom[b] != nd {
                idom[b] = nd;
                changed = true;
            }
        }
    }
    // the tree, in RPO order of children
    dt_first.clear();
    dt_first.resize(nb, NIL);
    dt_next.clear();
    dt_next.resize(nb, NIL);
    var k: i64 = rpo.len - 1;
    while k >= 1 {
        let b = rpo[k];
        let p = idom[b];
        dt_next[b] = dt_first[p];
        dt_first[p] = b;
        k--;
    }
    dt_pre.clear();
    dt_pre.resize(nb, NIL);
    dt_end.clear();
    dt_end.resize(nb, NIL);
    dt_order.clear();
    // pre-order with an explicit stack: an entry b | 0x80000000 closes b
    tmp_stack.clear();
    tmp_stack.push(0);
    while tmp_stack.len != 0 {
        let e = tmp_stack.pop();
        if e & 0x80000000 != 0 {
            dt_end[e & 0x7FFFFFFF] = dt_order.len as! u32;
            continue;
        }
        dt_pre[e] = dt_order.len as! u32;
        dt_order.push(e);
        tmp_stack.push(e | 0x80000000);
        var c = dt_first[e];
        while c != NIL {
            tmp_stack.push(c);
            c = dt_next[c];
        }
    }
}
// Whether block a dominates block b (both reachable).
inline fn dominates(a: u32, b: u32) -> bool { dt_pre[a] <= dt_pre[b] && dt_pre[b] < dt_end[a] }

// Dominance frontiers (df_head lists).
var df_last: u32[>..] = [];
fn build_df() {
    let nb = cfg_nb;
    df_head.clear();
    df_head.resize(nb, NIL);
    df_last.clear();
    df_last.resize(nb, NIL);
    df_blk.clear();
    df_nxt.clear();
    for b in rpo {
        if p_start[b + 1] - p_start[b] < 2 { continue; }
        let d = idom[b];
        for k in p_start[b]..p_start[b + 1] {
            var r = p_list[k];
            if rpo_num[r] == NIL { continue; }
            while r != d {
                if df_last[r] == b { break; }
                df_last[r] = b;
                df_blk.push(b);
                df_nxt.push(df_head[r]);
                df_head[r] = (df_blk.len - 1) as! u32;
                r = idom[r];
            }
        }
    }
}

// Loop nesting depth per block: natural loops of the back edges (an edge
// p -> h with h dominating p), body found backwards from p.
fn build_loops() {
    let nb = cfg_nb;
    lp_depth.clear();
    lp_depth.resize(nb, 0);
    for h in rpo {
        for k in p_start[h]..p_start[h + 1] {
            let p = p_list[k];
            if rpo_num[p] == NIL || !dominates(h, p) { continue; }
            loop_body(h, p);
        }
    }
}
var lb_mark: u32[>..] = [];
var lb_epoch: u32 = 0;
// Marks the body of the loop of back edge p -> h (adds 1 to their depth).
fn loop_body(h: u32, p: u32) {
    if lb_mark.len < cfg_nb { lb_mark.resize(cfg_nb, 0); }
    lb_epoch++;
    tmp_stack.clear();
    lb_mark[h] = lb_epoch;
    if lp_depth[h] != 255 { lp_depth[h]++; }
    if lb_mark[p] != lb_epoch {
        lb_mark[p] = lb_epoch;
        if lp_depth[p] != 255 { lp_depth[p]++; }
        tmp_stack.push(p);
    }
    while tmp_stack.len != 0 {
        let b = tmp_stack.pop();
        for k in p_start[b]..p_start[b + 1] {
            let q = p_list[k];
            if rpo_num[q] == NIL || lb_mark[q] == lb_epoch { continue; }
            lb_mark[q] = lb_epoch;
            if lp_depth[q] != 255 { lp_depth[q]++; }
            tmp_stack.push(q);
        }
    }
}

// ------------------------------------------------------------- PHI edits

// Removes the entries of block p from the PHIs of block s.
fn phi_remove_pred(s: u32, p: u32) {
    var i = b_first[s];
    while i != NIL && o_ins[i].op == GIR_PHI {
        let I = o_ins[i];
        var n: u32 = 0;
        for k in 0..I.c {
            if o_ops[I.b + 2 * k + 1] == p { continue; }
            o_ops[I.b + 2 * n] = o_ops[I.b + 2 * k];
            o_ops[I.b + 2 * n + 1] = o_ops[I.b + 2 * k + 1];
            n++;
        }
        o_ins[i].c = n;
        i = o_nxt[i];
    }
}
// Removes one entry of block p from the PHIs of block s (an edge of several
// from p went away).
fn phi_remove_one(s: u32, p: u32) {
    var i = b_first[s];
    while i != NIL && o_ins[i].op == GIR_PHI {
        let I = o_ins[i];
        var n: u32 = 0;
        var done = false;
        for k in 0..I.c {
            if !done && o_ops[I.b + 2 * k + 1] == p {
                done = true;
                continue;
            }
            o_ops[I.b + 2 * n] = o_ops[I.b + 2 * k];
            o_ops[I.b + 2 * n + 1] = o_ops[I.b + 2 * k + 1];
            n++;
        }
        o_ins[i].c = n;
        i = o_nxt[i];
    }
}
// Renames predecessor `from` to `to` in the PHIs of block s.
fn phi_rename_pred(s: u32, from: u32, to: u32) {
    var i = b_first[s];
    while i != NIL && o_ins[i].op == GIR_PHI {
        let I = o_ins[i];
        for k in 0..I.c {
            if o_ops[I.b + 2 * k + 1] == from { o_ops[I.b + 2 * k + 1] = to; }
        }
        i = o_nxt[i];
    }
}
// The incoming value of PHI i for predecessor p (NIL: none).
fn phi_in(i: u32, p: u32) -> u32 {
    let I = o_ins[i];
    for k in 0..I.c {
        if o_ops[I.b + 2 * k + 1] == p { return o_ops[I.b + 2 * k]; }
    }
    return NIL;
}

// Deletes the blocks that block 0 does not reach (build_cfg first): their
// instructions are unlinked and their PHI entries removed. In a function
// whose blocks are pinned the block stays, holding an UNREACHABLE.
fn remove_unreachable() -> bool {
    var any = false;
    for b in 0..cfg_nb {
        if !live_block(b) || rpo_num[b] != NIL { continue; }
        any = true;
        o_cfg_ok = false;
        for k in s_start[b]..s_start[b + 1] {
            let s = s_list[k];
            if rpo_num[s] != NIL { phi_remove_pred(s, b); }
        }
        var i = b_first[b];
        while i != NIL {
            let n = o_nxt[i];
            o_blk[i] = NIL;
            i = n;
        }
        b_first[b] = NIL;
        b_last[b] = NIL;
        if b_fl[b] & BF_ADDR != 0 {
            // (a block whose address is taken stays, empty)
            let u = new_inst(Inst { op: GIR_UNREACHABLE, sub: 0, flags: 0, ty: GIR_T_VOID, aux: 0, a: 0, b: 0, c: 0, dbg: 0 });
            link_end(b, u);
        } else {
            b_fl[b] |= BF_DEAD;
        }
    }
    return any;
}
