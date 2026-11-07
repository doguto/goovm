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
            } else if I.op == GIR_GEP && licm_split_gep(i, pt, ep) {
                moved = true;
            }
            i = nx;
        }
    }
    return moved;
}

// A GEP in the loop with an invariant base: its invariant terms (and the
// invariant halves of i64 additions in its terms) move to a GEP in the
// preheader, which becomes its base. (`a + (i*n + j)*4` -> row = a + i*n*4
// outside, row + j*4 inside.)
var sg_inv: u32[>..] = [];
var sg_var: u32[>..] = [];
fn licm_split_gep(i: u32, pt: u32, ep: u32) -> bool {
    let I = o_ins[i];
    let base = res(I.a);
    if is_inst(base) && o_blk[base] != NIL && lc_mark[o_blk[base]] == ep { return false; }
    sg_inv.clear();
    sg_var.clear();
    for k in 0..I.c {
        let x = res(o_ops[I.b + 2 + 2 * k]);
        let sc = o_ops[I.b + 3 + 2 * k];
        if !(is_inst(x) && o_blk[x] != NIL && lc_mark[o_blk[x]] == ep) {
            sg_inv.push(x);
            sg_inv.push(sc);
            continue;
        }
        let X = o_ins[x];
        if X.op == GIR_ADD && X.ty == GIR_T_I64 {
            let a = res(X.a);
            let b = res(X.b);
            let ia = !(is_inst(a) && o_blk[a] != NIL && lc_mark[o_blk[a]] == ep);
            let ib = !(is_inst(b) && o_blk[b] != NIL && lc_mark[o_blk[b]] == ep);
            if ia != ib {
                sg_inv.push(if ia { a } else { b });
                sg_inv.push(sc);
                sg_var.push(if ia { b } else { a });
                sg_var.push(sc);
                continue;
            }
        }
        sg_var.push(x);
        sg_var.push(sc);
    }
    if sg_inv.len == 0 || sg_var.len == 0 { return false; }
    let ni: u32 = (sg_inv.len / 2) as! u32;
    let nv: u32 = (sg_var.len / 2) as! u32;
    if ni > 2 { return false; }
    let r1 = new_run(2 + 2 * ni);
    o_ops[r1] = o_ops[I.b];
    o_ops[r1 + 1] = o_ops[I.b + 1];
    for k in 0..2 * ni { o_ops[r1 + 2 + k] = sg_inv[k]; }
    let g = new_inst(Inst { op: GIR_GEP as! u8, sub: 0, flags: 0, ty: GIR_T_PTR, aux: 0, a: base, b: r1, c: ni, dbg: I.dbg });
    link_before(pt, g);
    let r2 = new_run(2 + 2 * nv);
    o_ops[r2] = 0;
    o_ops[r2 + 1] = 0;
    for k in 0..2 * nv { o_ops[r2 + 2 + k] = sg_var[k]; }
    o_ins[i].a = g;
    o_ins[i].b = r2;
    o_ins[i].c = nv;
    return true;
}

// Loop rotation (LLVM's LoopRotate, for small headers): a loop whose header
// H holds only PHIs, a few cheap instructions and the exit test `condbr c,
// B, E` (B in the loop, E outside), entered from one block P and with one
// latch L that ends in `br H`, gets a copy H' of the test on the entry edge:
// P goes to H', H' to B or E, and H is entered only from L, so
// merge_blocks folds it into the latch. The loop becomes a guarded
// do-while: one taken branch per iteration and none on entry (with the test
// at the top, a loop that runs once or twice paid a jump to the test on
// every entry). The values H defines that are used outside H are repaired by
// demotion: an alloca stored in H and in H' and loaded at those uses, which
// mem2reg promotes again with the PHIs the new CFG needs. (The caller runs
// mem2reg; build_cfg first.)
let ROT_MAX: u32 = 4;           // instructions a header may have besides PHIs and the test
let ROT_LOOPS: u32 = 32;        // rotations per function
var rot_map: u32[>..] = [];     // per instruction of H: its value on the entry edge
var rot_mark: u32[>..] = [];    // loop membership (epoch)
var rot_epoch: u32 = 0;
var rot_vals: u32[>..] = [];    // H's values
fn rotate_loops() -> bool {
    if o_pinned { return false; }
    ensure_cfg();
    resolve_all();
    if rot_mark.len < cfg_nb { rot_mark.resize(cfg_nb, 0); }
    // (headers first, as the RPO lists them now; the CFG analyses go stale
    // as loops are rotated, but each rotation only reads its own loop)
    // (inner loops first: their headers come later in the RPO)
    lc_hdr.clear();
    var k = rpo.len;
    while k > 0 {
        k--;
        let h = rpo[k];
        if h == 0 || b_fl[h] & (BF_LP | BF_DEAD) != 0 || p_start[h + 1] - p_start[h] < 2 { continue; }
        lc_hdr.push(h);
    }
    var n: u32 = 0;
    build_uses();
    for H in lc_hdr {
        if n >= ROT_LOOPS { break; }
        if rot_map.len < o_ins.len { rot_map.resize(o_ins.len, NIL); }
        if rotate_one(H) {
            n++;
            // (the CFG and the uses are rebuilt for the next loop)
            ensure_cfg();
            if rot_mark.len < cfg_nb { rot_mark.resize(cfg_nb, 0); }
            build_uses();
        }
    }
    return n != 0;
}
fn rotate_one(H: u32) -> bool {
    if b_fl[H] & (BF_LP | BF_DEAD) != 0 { return false; }
    // one latch, and the outside edges through one preheader (made here if
    // there are several: SimplifyCFG sends the edges of empty blocks straight
    // to the header)
    var nback: u32 = 0;
    var nout: u32 = 0;
    for k in p_start[H]..p_start[H + 1] {
        let p = p_list[k];
        if rpo_num[p] == NIL { return false; }
        if dominates(H, p) { nback++; } else { nout++; }
    }
    if nback != 1 || nout == 0 { return false; }
    if nout > 1 {
        if !licm_preheader(H) { return false; }
        ensure_cfg();
        if rot_mark.len < cfg_nb { rot_mark.resize(cfg_nb, 0); }
        if rot_map.len < o_ins.len { rot_map.resize(o_ins.len, NIL); }
        build_uses();
    }
    if p_start[H + 1] - p_start[H] != 2 { return false; }
    let q0 = p_list[p_start[H]];
    let q1 = p_list[p_start[H] + 1];
    if rpo_num[q0] == NIL || rpo_num[q1] == NIL || q0 == q1 { return false; }
    var P: u32 = NIL;
    var L: u32 = NIL;
    if dominates(H, q0) && !dominates(H, q1) { L = q0; P = q1; }
    else if dominates(H, q1) && !dominates(H, q0) { L = q1; P = q0; }
    else { return false; }
    let lt = b_last[L];
    if lt == NIL || o_ins[lt].op != GIR_BR || L == H { return false; }
    let pt = b_last[P];
    if pt == NIL || block_invoke(P) != NIL { return false; }
    let pop: u32 = o_ins[pt].op;
    if pop != GIR_BR && pop != GIR_CONDBR { return false; }
    let t = b_last[H];
    if t == NIL || o_ins[t].op != GIR_CONDBR || o_ins[t].b == o_ins[t].c { return false; }
    // loop body: backwards from L to H
    rot_epoch++;
    rot_mark[H] = rot_epoch;
    tmp_stack.clear();
    if rot_mark[L] != rot_epoch {
        rot_mark[L] = rot_epoch;
        tmp_stack.push(L);
    }
    while tmp_stack.len != 0 {
        let b = tmp_stack.pop();
        for k in p_start[b]..p_start[b + 1] {
            let q = p_list[k];
            if rpo_num[q] == NIL || rot_mark[q] == rot_epoch { continue; }
            rot_mark[q] = rot_epoch;
            tmp_stack.push(q);
        }
    }
    let x = o_ins[t].b;
    let y = o_ins[t].c;
    let xin = rot_mark[x] == rot_epoch;
    let yin = rot_mark[y] == rot_epoch;
    if xin == yin { return false; }
    let E = if xin { y } else { x };
    let B = if xin { x } else { y };
    if b_fl[E] & BF_LP != 0 || b_fl[B] & BF_LP != 0 || B == H || E == P { return false; }
    // H: PHIs, a few cheap instructions, the test; the values used outside H
    // must be promotable again
    rot_vals.clear();
    var ni: u32 = 0;
    var i = b_first[H];
    while i != t {
        let I = o_ins[i];
        if I.op != GIR_PHI {
            if !spec_op(I) || I.op == GIR_GEP { return false; }
            ni++;
            if ni > ROT_MAX { return false; }
        }
        rot_vals.push(i);
        i = o_nxt[i];
    }
    for v in rot_vals {
        if rot_used_out(v, H) && (!int_ty(o_ins[v].ty) || bits_of(o_ins[v].ty) > 64) { return false; }
    }
    // H' = the test on the entry edge
    let H2 = new_block();
    for v in rot_vals {
        if o_ins[v].op == GIR_PHI {
            rot_map[v] = res(phi_in(v, P));
            continue;
        }
        let c = new_inst(o_ins[v]);
        each_slot(c) { s =>
            vset(c, s, rot_in(res(vget(c, s)), H));
        };
        link_end(H2, c);
        rot_map[v] = c;
    }
    let ct = new_inst(o_ins[t]);
    o_ins[ct].a = rot_in(res(o_ins[t].a), H);
    link_end(H2, ct);
    // demotion of the values used outside H
    for v in rot_vals {
        if !rot_used_out(v, H) { continue; }
        let ty: u32 = o_ins[v].ty;
        let a = new_inst(Inst { op: GIR_ALLOCA as! u8, sub: 0, flags: 0, ty: GIR_T_PTR, aux: 0, a: store_of(ty),
                                b: M.types[ty].align, c: 0, dbg: o_ins[t].dbg });
        link_start(0, a);
        rot_store(v, ty, a, t);
        rot_store(rot_map[v], ty, a, ct);
        for k in u_start[v]..u_start[v + 1] {
            let u = u_list[k];
            if o_blk[u] == NIL || o_blk[u] == H2 { continue; }
            let U = o_ins[u];
            if o_blk[u] == H && U.op != GIR_PHI { continue; }
            if U.op == GIR_PHI {
                for e in 0..U.c {
                    let p = o_ops[U.b + 2 * e + 1];
                    if res(o_ops[U.b + 2 * e]) != v || p == H { continue; }
                    o_ops[U.b + 2 * e] = rot_load(a, ty, b_last[p]);
                }
            } else {
                var ld: u32 = NIL;
                each_slot(u) { s =>
                    if res(vget(u, s)) == v {
                        if ld == NIL { ld = rot_load(a, ty, u); }
                        vset(u, s, ld);
                    }
                };
            }
        }
    }
    // H' enters B and E like H
    rot_phis(B, H, H2);
    rot_phis(E, H, H2);
    // P goes to H' instead of H
    if pop == GIR_BR { o_ins[pt].a = H2; }
    else {
        if o_ins[pt].b == H { o_ins[pt].b = H2; }
        if o_ins[pt].c == H { o_ins[pt].c = H2; }
    }
    phi_remove_pred(H, P);
    b_lnext[H2] = b_lnext[P];
    b_lnext[P] = H2;
    return true;
}
// v (an operand of a copy of H's instruction) on the entry edge.
fn rot_in(v: u32, H: u32) -> u32 {
    if is_inst(v) && o_blk[v] == H { return rot_map[v]; }
    return v;
}
// Whether value v of H is used outside H: by an instruction of another block
// or as a PHI's incoming value on an edge that does not leave H (H's own
// PHIs included: the edge from the latch, which H no longer dominates).
fn rot_used_out(v: u32, H: u32) -> bool {
    for k in u_start[v]..u_start[v + 1] {
        let u = u_list[k];
        if o_blk[u] == NIL { continue; }
        let U = o_ins[u];
        if U.op != GIR_PHI {
            if o_blk[u] != H { return true; }
            continue;
        }
        for e in 0..U.c {
            if res(o_ops[U.b + 2 * e]) == v && o_ops[U.b + 2 * e + 1] != H { return true; }
        }
    }
    return false;
}
fn rot_store(v: u32, ty: u32, a: u32, at: u32) {
    let s = new_inst(Inst { op: GIR_STORE as! u8, sub: 0, flags: 0, ty: GIR_T_VOID, aux: ty as! u16, a: v, b: a, c: 0,
                            dbg: o_ins[at].dbg });
    link_before(at, s);
}
fn rot_load(a: u32, ty: u32, at: u32) -> u32 {
    let l = new_inst(Inst { op: GIR_LOAD as! u8, sub: 0, flags: 0, ty: ty as! u16, aux: 0, a: a, b: 0, c: 0,
                            dbg: o_ins[at].dbg });
    link_before(at, l);
    return l;
}
// The PHIs of block s get an entry for H2: H's value, mapped to the entry edge.
fn rot_phis(s: u32, H: u32, H2: u32) {
    var i = b_first[s];
    while i != NIL && o_ins[i].op == GIR_PHI {
        let I = o_ins[i];
        let w = res(phi_in(i, H));
        let ns = new_run(2 * (I.c + 1));
        for q in 0..2 * I.c { o_ops[ns + q] = o_ops[I.b + q]; }
        o_ops[ns + 2 * I.c] = rot_in(w, H);
        o_ops[ns + 2 * I.c + 1] = H2;
        o_ins[i].b = ns;
        o_ins[i].c = I.c + 1;
        i = o_nxt[i];
    }
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
