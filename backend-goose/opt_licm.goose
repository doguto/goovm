// Loop-invariant code motion on the OIR (opt.goose): every natural loop
// gets a preheader (a block that only branches to the header, entered from
// all the edges that come from outside the loop), then the pure
// instructions of the loop whose operands are all defined outside it move
// to the preheader, inner loops first, so an invariant leaves a nest level
// by level. Division only by a constant that cannot trap. Loads only when
// the loop writes no memory and the load either is in the header (which
// runs whenever the preheader does) or reads an alloca or a global (always
// addressable).

var lc_hdr: u32[>..] = [];
var lc_mark: u32[>..] = [];
var lc_epoch: u32 = 0;
var lc_tmp: u32[>..] = [];

// Whether instruction I may be executed in the preheader (no trap, no effect).
fn licm_op(I: Inst) -> bool {
    let op: u32 = I.op;
    if op >= GIR_SDIV && op <= GIR_UREM {
        let k, v = ci(res(I.b));
        if !k || v == 0 { return false; }
        if (op == GIR_SDIV || op == GIR_SREM) && v == wmask(bits_of(I.ty)) { return false; }
        return true;
    }
    if op >= GIR_ADD && op <= GIR_BITCAST { return true; }
    if op == GIR_GEP { return true; }
    if op >= GIR_FADD && op <= GIR_UITOFP { return true; }
    if op == GIR_FABS || op == GIR_COPYSIGN || op == GIR_FSQRT { return true; }
    if op >= GIR_CTLZ && op <= GIR_BITREVERSE { return true; }
    return false;
}
// Whether p certainly points to addressable memory (an alloca, a global, a
// constant-offset GEP of one).
fn always_addr(p0: u32) -> bool {
    var p = res(p0);
    loop {
        if gir_kind(p) == GIR_V_GLOBAL { return true; }
        if !is_inst(p) { return false; }
        let I = o_ins[p];
        if I.op == GIR_ALLOCA { return true; }
        if I.op != GIR_GEP || I.c != 0 { return false; }
        p = res(I.a);
    }
    return false;
}

fn licm() -> bool {
    if o_pinned { return false; }
    ensure_cfg();
    // 1. preheaders
    lc_hdr.clear();
    for h in rpo {
        var back = 0;
        var outside = 0;
        var outp: u32 = NIL;
        for k in p_start[h]..p_start[h + 1] {
            let p = p_list[k];
            if rpo_num[p] == NIL { continue; }
            if dominates(h, p) { back++; } else {
                if outp != p { outside++; }
                outp = p;
            }
        }
        if back == 0 || h == 0 || b_fl[h] & BF_LP != 0 { continue; }
        lc_hdr.push(h);
    }
    if lc_hdr.len == 0 { return false; }
    var made = false;
    for h in lc_hdr {
        if licm_preheader(h) { made = true; }
    }
    if made { ensure_cfg(); }
    // 2. hoisting, inner loops (later headers in RPO) first
    var moved = false;
    lc_hdr.clear();
    for h in rpo {
        if h == 0 || b_fl[h] & BF_LP != 0 { continue; }
        var back = false;
        for k in p_start[h]..p_start[h + 1] {
            let p = p_list[k];
            if rpo_num[p] != NIL && dominates(h, p) { back = true; }
        }
        if back { lc_hdr.push(h); }
    }
    if lc_mark.len < cfg_nb { lc_mark.resize(cfg_nb, 0); }
    var q: i64 = lc_hdr.len - 1;
    while q >= 0 {
        if licm_loop(lc_hdr[q]) { moved = true; }
        q--;
    }
    return made || moved;
}

// Makes sure loop header h has a preheader (build_cfg first; the CFG lists
// go stale). Returns whether a block was made.
fn licm_preheader(h: u32) -> bool {
    lc_tmp.clear();
    for k in p_start[h]..p_start[h + 1] {
        let p = p_list[k];
        if rpo_num[p] == NIL || dominates(h, p) { continue; }
        if lc_tmp.len == 0 || lc_tmp[lc_tmp.len - 1] != p { lc_tmp.push(p); }
    }
    if lc_tmp.len == 0 { return false; }
    if lc_tmp.len == 1 {
        let p = lc_tmp[0];
        if s_start[p + 1] - s_start[p] == 1 && block_invoke(p) == NIL { return false; }
    }
    for p in lc_tmp {
        let t = b_last[p];
        let op: u32 = o_ins[t].op;
        if op != GIR_BR && op != GIR_CONDBR && op != GIR_SWITCH { return false; }
        let iv = block_invoke(p);
        if iv != NIL && o_ops[o_ins[iv].b + 2 * o_ins[iv].c] == h { return false; }
    }
    let ph = new_block();
    let br = new_inst(Inst { op: GIR_BR as! u8, sub: 0, flags: 0, ty: GIR_T_VOID, aux: 0, a: h, b: 0, c: 0, dbg: 0 });
    link_end(ph, br);
    // the outside edges go to the preheader
    for p in lc_tmp {
        let t = b_last[p];
        let op: u32 = o_ins[t].op;
        if op == GIR_BR { o_ins[t].a = ph; }
        else if op == GIR_CONDBR {
            if o_ins[t].b == h { o_ins[t].b = ph; }
            if o_ins[t].c == h { o_ins[t].c = ph; }
        } else {
            let s = o_ins[t].b;
            if o_ops[s] == h { o_ops[s] = ph; }
            for k in 0..o_ins[t].c { if o_ops[s + 2 + 2 * k] == h { o_ops[s + 2 + 2 * k] = ph; } }
        }
    }
    // the header's PHIs: the outside entries become one (from the preheader),
    // through a PHI of the preheader if they differ
    var i = b_first[h];
    while i != NIL && o_ins[i].op == GIR_PHI {
        let I = o_ins[i];
        var nin: u32 = 0;
        var nout: u32 = 0;
        var same: u32 = NIL;
        var diff = false;
        for k in 0..I.c {
            let p = o_ops[I.b + 2 * k + 1];
            if lc_is_out(p) {
                let v = res(o_ops[I.b + 2 * k]);
                if same == NIL { same = v; } else if same != v { diff = true; }
                nout++;
            } else {
                nin++;
            }
        }
        var v = same;
        if diff {
            let s = new_run(2 * nout);
            var n: u32 = 0;
            for k in 0..I.c {
                let p = o_ops[I.b + 2 * k + 1];
                if !lc_is_out(p) { continue; }
                o_ops[s + 2 * n] = o_ops[I.b + 2 * k];
                o_ops[s + 2 * n + 1] = p;
                n++;
            }
            let np = new_inst(Inst { op: GIR_PHI as! u8, sub: 0, flags: 0, ty: I.ty, aux: 0, a: 0, b: s, c: nout, dbg: 0 });
            link_start(ph, np);
            v = np;
        }
        let s2 = new_run(2 * (nin + 1));
        var n: u32 = 0;
        for k in 0..I.c {
            let p = o_ops[I.b + 2 * k + 1];
            if lc_is_out(p) { continue; }
            o_ops[s2 + 2 * n] = o_ops[I.b + 2 * k];
            o_ops[s2 + 2 * n + 1] = p;
            n++;
        }
        o_ops[s2 + 2 * n] = v;
        o_ops[s2 + 2 * n + 1] = ph;
        o_ins[i].b = s2;
        o_ins[i].c = nin + 1;
        i = o_nxt[i];
    }
    // layout: the preheader right before the header
    var b: u32 = 0;
    while b != NIL && b_lnext[b] != h { b = b_lnext[b]; }
    if b == NIL {
        b_lnext[ph] = b_lnext[h];
        b_lnext[h] = ph;
    } else {
        b_lnext[b] = ph;
        b_lnext[ph] = h;
    }
    return true;
}
fn lc_is_out(p: u32) -> bool {
    for x in lc_tmp { if x == p { return true; } }
    return false;
}

// Hoists the invariants of the loop of header h into its preheader.
fn licm_loop(h: u32) -> bool {
    lc_epoch++;
    let ep = lc_epoch;
    // the body (from the back edges' sources backwards)
    tmp_stack.clear();
    lc_mark[h] = ep;
    var pre: u32 = NIL;
    for k in p_start[h]..p_start[h + 1] {
        let p = p_list[k];
        if rpo_num[p] == NIL { continue; }
        if !dominates(h, p) {
            pre = p;
            continue;
        }
        if lc_mark[p] != ep {
            lc_mark[p] = ep;
            tmp_stack.push(p);
        }
    }
    while tmp_stack.len != 0 {
        let b = tmp_stack.pop();
        for k in p_start[b]..p_start[b + 1] {
            let q = p_list[k];
            if rpo_num[q] == NIL || lc_mark[q] == ep { continue; }
            lc_mark[q] = ep;
            tmp_stack.push(q);
        }
    }
    if pre == NIL || s_start[pre + 1] - s_start[pre] != 1 { return false; }
    let pt = b_last[pre];
    // does the loop write memory?
    var writes = false;
    for b in rpo {
        if lc_mark[b] != ep { continue; }
        var i = b_first[b];
        while i != NIL {
            if writes_mem(o_ins[i]) { writes = true; }
            i = o_nxt[i];
        }
    }
    var moved = false;
    for b in rpo {
        if lc_mark[b] != ep { continue; }
        var i = b_first[b];
        while i != NIL {
            let nx = o_nxt[i];
            let I = o_ins[i];
            var ok = false;
            if I.op == GIR_LOAD {
                ok = !writes && I.flags & (IF_VOLATILE | IF_ORD_MASK) == 0 && (b == h || always_addr(I.a));
            } else {
                ok = licm_op(I);
            }
            if ok {
                vslots(i);
                for s in vs {
                    let v = res(vget(i, s));
                    if is_inst(v) && o_blk[v] != NIL && lc_mark[o_blk[v]] == ep { ok = false; }
                }
            }
            if ok {
                unlink(i);
                link_before(pt, i);
                moved = true;
            }
            i = nx;
        }
    }
    return moved;
}

// Loop rotation in the layout: a loop whose header ends in a conditional
// branch (one successor in the loop, one out) and whose only latch ends in a
// branch to the header gets its header placed right after the latch. The
// latch then falls through into the header's test, whose branch back into
// the loop is the only taken branch of an iteration (the preheader jumps to
// the test once). (build_cfg first.)
fn rotate_layout() -> bool {
    if o_pinned { return false; }
    if lc_mark.len < cfg_nb { lc_mark.resize(cfg_nb, 0); }
    var any = false;
    for h in rpo {
        if h == 0 || b_fl[h] & BF_LP != 0 { continue; }
        var latch: u32 = NIL;
        var nl = 0;
        for k in p_start[h]..p_start[h + 1] {
            let p = p_list[k];
            if rpo_num[p] != NIL && dominates(h, p) {
                if latch != p { nl++; }
                latch = p;
            }
        }
        if nl != 1 || latch == h { continue; }
        let lt = b_last[latch];
        if o_ins[lt].op != GIR_BR || block_invoke(latch) != NIL { continue; }
        let ht = b_last[h];
        if o_ins[ht].op != GIR_CONDBR || block_invoke(h) != NIL { continue; }
        // one successor in the loop: the body is what reaches the latch
        lc_epoch++;
        let ep = lc_epoch;
        lc_mark[h] = ep;
        tmp_stack.clear();
        lc_mark[latch] = ep;
        tmp_stack.push(latch);
        while tmp_stack.len != 0 {
            let b = tmp_stack.pop();
            for k in p_start[b]..p_start[b + 1] {
                let q = p_list[k];
                if rpo_num[q] == NIL || lc_mark[q] == ep { continue; }
                lc_mark[q] = ep;
                tmp_stack.push(q);
            }
        }
        let s1 = o_ins[ht].b;
        let s2 = o_ins[ht].c;
        if (lc_mark[s1] == ep) == (lc_mark[s2] == ep) { continue; }
        if b_lnext[latch] == h { continue; }   // (already)
        // unlink h from the layout and put it after the latch
        var b: u32 = 0;
        while b != NIL && b_lnext[b] != h { b = b_lnext[b]; }
        if b == NIL { continue; }
        b_lnext[b] = b_lnext[h];
        b_lnext[h] = b_lnext[latch];
        b_lnext[latch] = h;
        any = true;
    }
    return any;
}
