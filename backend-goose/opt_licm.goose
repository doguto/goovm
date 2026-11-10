// Loop-invariant code motion on the OIR (opt.goose): every natural loop
// gets a preheader (a block that only branches to the header, entered from
// all the edges that come from outside the loop), then the pure
// instructions of the loop whose operands are all defined outside it move
// to the preheader, inner loops first, so an invariant leaves a nest level
// by level. Division only by a constant that cannot trap. Loads (E2) when
// no memory write of the loop may alias them (opt_aa.goose) and the load
// either is in the header (which runs whenever the preheader does) or reads
// an alloca or a global (always addressable).

var lc_hdr: u32[>..] = [];
var lc_mark: u32[>..] = [];
var lc_epoch: u32 = 0;
var lc_tmp: u32[>..] = [];
var lc_w: u32[>..] = [];        // the memory writes of the loop being hoisted from
let LC_MAXW: i64 = 256;

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
// Whether sz bytes at p are certainly addressable memory: inside an alloca
// or a defined global variable, at a constant offset (a load from there may
// run speculatively).
fn always_addr(p0: u32, sz: u32) -> bool {
    let b, off, known = aa_decompose(p0);
    if !known || off < 0 { return false; }
    var size: i64 = -1;
    if gir_kind(b) == GIR_V_GLOBAL {
        let G = M.globals[gir_idx(b)];
        if G.kind == G_VAR && G.flags & (GF_DEFINED | GF_COMMON) != 0 && G.flags & GF_WEAK == 0 { size = G.size; }
    } else if is_inst(b) && o_ins[b].op == GIR_ALLOCA {
        size = o_ins[b].a;
    }
    return size >= 0 && off + sz as i64 <= size;
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
    aa_prepare();
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
    // the loop's memory writes (any: one the alias analysis cannot place)
    var any_write = false;
    lc_w.clear();
    for b in rpo {
        if lc_mark[b] != ep { continue; }
        var i = b_first[b];
        while i != NIL {
            let W = o_ins[i];
            if writes_mem(W) {
                let op: u32 = W.op;
                if (op == GIR_STORE || op == GIR_MEMCPY || op == GIR_MEMSET) && W.flags & (IF_VOLATILE | IF_ORD_MASK) == 0
                   || op == GIR_CALL {
                    lc_w.push(i);
                } else {
                    any_write = true;
                }
            }
            i = o_nxt[i];
        }
    }
    if lc_w.len > LC_MAXW { any_write = true; }
    var moved = false;
    for b in rpo {
        if lc_mark[b] != ep { continue; }
        var i = b_first[b];
        while i != NIL {
            let nx = o_nxt[i];
            let I = o_ins[i];
            var ok = false;
            if I.op == GIR_LOAD {
                ok = !any_write && I.flags & (IF_VOLATILE | IF_ORD_MASK) == 0 && (b == h || always_addr(I.a, store_of(I.ty)));
                if ok {
                    let p = res(I.a);
                    let sz = store_of(I.ty);
                    for w in lc_w {
                        if aa_clobbers(w, p, sz, I.b) { ok = false; break; }
                    }
                }
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

// Scalar promotion of globals in loops (the part of LLVM's LICM promotion
// that GlobalsAA makes possible): an internal global whose address is never
// taken (only loaded and stored directly, in the whole module) cannot be
// touched through a pointer, so in a loop without calls and inline asm its
// loads and stores are of a value that only the loop changes. The global is
// demoted to an alloca for the loop (loaded in the preheader, stored back on
// every exit edge), which mem2reg turns into a register. Stores are added on
// the exits only when a store of the loop dominates every exiting block (no
// store where the program had none on that path: another thread may own the
// global then). The caller runs mem2reg.
var gp_ok: u8[>..] = [];        // per global: internal, never address-taken
var gp_ty: u32[>..] = [];       // per global: the one type of its accesses in the loop, NIL
var gp_st: u32[>..] = [];       // per global: NIL no store, GV_MANY no store that dominates the exits, else a store's block
var gp_list: u32[>..] = [];
var gp_exit: u32[>..] = [];     // exit edges (from, to)
var gp_eblk: u32[>..] = [];     // per exit edge: the block made on it
fn gp_scan() {
    let ng = M.globals.len;
    gp_ok.clear();
    gp_ok.resize(ng, 0);
    for G in M.globals {
        if G.kind == G_ALIAS { return; }   // (an alias may name the global's memory)
    }
    for g in 0..ng {
        let G = M.globals[g];
        if G.kind == G_VAR && G.flags & GF_DEFINED != 0 && G.flags & GF_INTERNAL != 0
           && G.flags & (GF_TLS | GF_CONST) == 0 {
            gp_ok[g] = 1;
        }
    }
    for x in M.opnds {
        if gir_kind(x) == GIR_V_GLOBAL && gir_idx(x) < ng { gp_ok[gir_idx(x)] = 0; }
    }
    for d in M.drelocs {
        if d.target < ng { gp_ok[d.target] = 0; }
    }
    for I in M.insts {
        let op: u32 = I.op;
        let m: u32 = if op < GIR_NOPS { OP_VAL[op] } else { 7 };
        if m & OV_A != 0 && gir_kind(I.a) == GIR_V_GLOBAL && op != GIR_LOAD && gir_idx(I.a) < ng { gp_ok[gir_idx(I.a)] = 0; }
        if m & OV_B != 0 && gir_kind(I.b) == GIR_V_GLOBAL && op != GIR_STORE && gir_idx(I.b) < ng { gp_ok[gir_idx(I.b)] = 0; }
        if m & OV_C != 0 && gir_kind(I.c) == GIR_V_GLOBAL && gir_idx(I.c) < ng { gp_ok[gir_idx(I.c)] = 0; }
        if op == GIR_BLOCKADDR && I.a < ng { gp_ok[I.a] = 0; }
    }
}
fn promote_globals() -> bool {
    if o_pinned || gp_ok.len != M.globals.len { return false; }
    ensure_cfg();
    if lc_mark.len < cfg_nb { lc_mark.resize(cfg_nb, 0); }
    if gp_ty.len < M.globals.len {
        gp_ty.resize(M.globals.len, NIL);
        gp_st.resize(M.globals.len, NIL);
    }
    lc_hdr.clear();
    for h in rpo {
        if h == 0 { continue; }
        for k in p_start[h]..p_start[h + 1] {
            let p = p_list[k];
            if rpo_num[p] != NIL && dominates(h, p) {
                lc_hdr.push(h);
                break;
            }
        }
    }
    // (preheaders: SimplifyCFG removes the empty ones LICM made)
    var made = false;
    for h in lc_hdr {
        if b_fl[h] & BF_LP == 0 && licm_preheader(h) { made = true; }
    }
    if made {
        ensure_cfg();
        if lc_mark.len < cfg_nb { lc_mark.resize(cfg_nb, 0); }
    }
    var any = false;
    for h in lc_hdr {
        if gp_loop(h) {
            any = true;
            ensure_cfg();
            if lc_mark.len < cfg_nb { lc_mark.resize(cfg_nb, 0); }
        }
    }
    return any;
}
// Whether a block that dominates b (b included) stores to global g.
fn gp_pre_store(b0: u32, g: u32) -> bool {
    return pre_store_ptr(b0, (3 as u32) << 30 | g);
}
fn pre_store_ptr(b0: u32, gref: u32) -> bool {
    var b = b0;
    var n = 0;
    while b != NIL && n < 1000 {
        var i = b_first[b];
        while i != NIL {
            let I = o_ins[i];
            if I.op == GIR_STORE && res(I.b) == gref && I.flags & (IF_VOLATILE | IF_ORD_MASK) == 0 { return true; }
            i = o_nxt[i];
        }
        if b == 0 { break; }
        b = idom[b];
        n++;
    }
    return false;
}
// ------------------------------------------------- memory promotion (E2)
// LLVM's LICM scalar promotion with alias analysis: a location p (a
// loop-invariant pointer, typically a global or a field through an invariant
// pointer) that the loop loads and stores with one type, when no other memory
// access of the loop may alias it (opt_aa.goose: TBAA, bases, offsets) and no
// call may read or write it, lives in an alloca in the loop (mem2reg makes it
// a register): loaded in the preheader, stored back on the exits. The load
// in the preheader needs p to be addressable there (an in-bounds constant
// offset of an alloca or a global, or an access of p in the header, which
// runs whenever the preheader does); the stores on the exits need a store
// that runs whenever the loop is left (one that dominates the exiting
// blocks, or one before the loop).
var pm_ptr: u32[>..] = [];      // candidates: pointer, type, TBAA node, flags (1 stored, 2 bad, 4 header access)
var pm_ty: u32[>..] = [];
var pm_tag: u32[>..] = [];
var pm_fl: u32[>..] = [];
var pm_mem: u32[>..] = [];      // the loop's memory instructions
fn promote_mem() -> bool {
    if o_pinned { return false; }
    ensure_cfg();
    aa_prepare();
    if lc_mark.len < cfg_nb { lc_mark.resize(cfg_nb, 0); }
    lc_hdr.clear();
    for h in rpo {
        if h == 0 || b_fl[h] & BF_LP != 0 { continue; }
        for k in p_start[h]..p_start[h + 1] {
            let p = p_list[k];
            if rpo_num[p] != NIL && dominates(h, p) {
                lc_hdr.push(h);
                break;
            }
        }
    }
    var made = false;
    for h in lc_hdr {
        if licm_preheader(h) { made = true; }
    }
    if made {
        ensure_cfg();
        if lc_mark.len < cfg_nb { lc_mark.resize(cfg_nb, 0); }
    }
    var any = false;
    // inner loops first
    var q: i64 = lc_hdr.len - 1;
    while q >= 0 {
        let h = lc_hdr[q];
        q--;
        if pm_loop(h) {
            any = true;
            ensure_cfg();
            if lc_mark.len < cfg_nb { lc_mark.resize(cfg_nb, 0); }
        }
    }
    return any;
}
fn pm_find(p: u32) -> i64 {
    for k in 0..pm_ptr.len { if pm_ptr[k] == p { return k; } }
    return -1;
}
fn pm_loop(h: u32) -> bool {
    lc_epoch++;
    let ep = lc_epoch;
    tmp_stack.clear();
    lc_mark[h] = ep;
    var pre: u32 = NIL;
    var npre = 0;
    for k in p_start[h]..p_start[h + 1] {
        let p = p_list[k];
        if rpo_num[p] == NIL { return false; }
        if !dominates(h, p) {
            pre = p;
            npre++;
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
            let qq = p_list[k];
            if rpo_num[qq] == NIL || lc_mark[qq] == ep { continue; }
            lc_mark[qq] = ep;
            tmp_stack.push(qq);
        }
    }
    if npre != 1 || s_start[pre + 1] - s_start[pre] != 1 || block_invoke(pre) != NIL { return false; }
    gp_exit.clear();
    for b in rpo {
        if lc_mark[b] != ep { continue; }
        for k in s_start[b]..s_start[b + 1] {
            let x = s_list[k];
            if lc_mark[x] == ep { continue; }
            if b_fl[x] & BF_LP != 0 || block_invoke(b) != NIL { return false; }
            let tb = b_last[b];
            if o_ins[tb].op == GIR_CONDBR && o_ins[tb].b == o_ins[tb].c { return false; }
            if o_ins[tb].op != GIR_BR && o_ins[tb].op != GIR_CONDBR { return false; }
            gp_exit.push(b);
            gp_exit.push(x);
        }
    }
    if gp_exit.len == 0 { return false; }
    // memory instructions and candidates
    pm_ptr.clear();
    pm_ty.clear();
    pm_tag.clear();
    pm_fl.clear();
    pm_mem.clear();
    for b in rpo {
        if lc_mark[b] != ep { continue; }
        var i = b_first[b];
        while i != NIL {
            let I = o_ins[i];
            let op: u32 = I.op;
            if op == GIR_LOAD || op == GIR_STORE {
                if I.flags & (IF_VOLATILE | IF_ORD_MASK) != 0 { return false; }
                pm_mem.push(i);
                let p = if op == GIR_LOAD { res(I.a) } else { res(I.b) };
                let t: u32 = if op == GIR_LOAD { I.ty } else { I.aux };
                let tag = if op == GIR_LOAD { I.b } else { I.c };
                let inv = !is_inst(p) || o_blk[p] == NIL || lc_mark[o_blk[p]] != ep;
                let isal = is_inst(p) && o_ins[p].op == GIR_ALLOCA;
                if inv && !isal && gir_kind(p) != GIR_V_CONST {
                    var k = pm_find(p);
                    if k < 0 {
                        pm_ptr.push(p);
                        pm_ty.push(t);
                        pm_tag.push(tag);
                        pm_fl.push(0);
                        k = pm_ptr.len - 1;
                    }
                    if pm_ty[k] != t || !promotable_type(t) { pm_fl[k] |= 2; }
                    if pm_tag[k] != tag { pm_tag[k] = 0; }
                    if op == GIR_STORE {
                        pm_fl[k] |= 1;
                        if gp_dom_exits(b) { pm_fl[k] |= 8; }
                        if res(I.a) == p { pm_fl[k] |= 2; }
                    }
                    if b == h { pm_fl[k] |= 4; }
                }
            } else if op == GIR_CALL || op == GIR_MEMCPY || op == GIR_MEMSET {
                pm_mem.push(i);
            } else if writes_mem(I) {
                return false;
            }
            i = o_nxt[i];
        }
    }
    if pm_ptr.len == 0 || pm_mem.len > 512 { return false; }
    var n: i64 = 0;
    var any_st = false;
    for k in 0..pm_ptr.len {
        let p = pm_ptr[k];
        let t = pm_ty[k];
        if pm_fl[k] & 2 != 0 { continue; }
        let sz = store_of(t);
        let tag = pm_tag[k];
        var ok = true;
        for m in pm_mem {
            let I = o_ins[m];
            let op: u32 = I.op;
            if op == GIR_LOAD || op == GIR_STORE {
                let q = if op == GIR_LOAD { res(I.a) } else { res(I.b) };
                if q == p { continue; }
                let qt: u32 = if op == GIR_LOAD { I.ty } else { I.aux };
                let qtag = if op == GIR_LOAD { I.b } else { I.c };
                if aa_alias(q, store_of(qt), qtag, p, sz, tag) { ok = false; break; }
                // (the stored value being p itself: p escapes through memory)
                if op == GIR_STORE && res(I.a) == p { ok = false; break; }
            } else if op == GIR_CALL {
                if aa_call_mod(m, p) || aa_call_ref(m, p) { ok = false; break; }
                for a in 0..I.c { if res(o_ops[I.b + 2 * a]) == p { ok = false; } }
                if !ok { break; }
            } else {
                if aa_clobbers(m, p, sz, tag) { ok = false; break; }
                if op == GIR_MEMCPY && aa_alias(res(I.b), I.c, 0, p, sz, tag) { ok = false; break; }
            }
        }
        if !ok { continue; }
        // addressable in the preheader; stores safe on the exits
        if pm_fl[k] & 4 == 0 && !always_addr(p, sz) { continue; }
        if pm_fl[k] & 1 != 0 && pm_fl[k] & 8 == 0 && !pre_store_ptr(pre, p) { continue; }
        pm_ptr[n] = p;
        pm_ty[n] = t;
        pm_fl[n] = pm_fl[k];
        n++;
        if pm_fl[k] & 1 != 0 { any_st = true; }
    }
    if n == 0 { return false; }
    let dbg = o_ins[b_last[pre]].dbg;
    gp_eblk.clear();
    if any_st {
        var e: i64 = 0;
        while e < gp_exit.len {
            let b = gp_exit[e];
            let x = gp_exit[e + 1];
            e += 2;
            let nb = new_block();
            let br = new_inst(Inst { op: GIR_BR as! u8, sub: 0, flags: 0, ty: GIR_T_VOID, aux: 0, a: x, b: 0, c: 0, dbg: dbg });
            link_end(nb, br);
            let bt = b_last[b];
            if o_ins[bt].op == GIR_BR { o_ins[bt].a = nb; }
            else if o_ins[bt].b == x { o_ins[bt].b = nb; }
            else { o_ins[bt].c = nb; }
            phi_rename_pred(x, b, nb);
            b_lnext[nb] = b_lnext[b];
            b_lnext[b] = nb;
            gp_eblk.push(nb);
        }
        o_cfg_ok = false;
    }
    for k in 0..n { gp_promote_ptr(pm_ptr[k], pm_ty[k], ep, pre, pm_fl[k] & 1 != 0); }
    return true;
}

// Whether block b dominates every exiting block of the loop (gp_exit).
fn gp_dom_exits(b: u32) -> bool {
    var e: i64 = 0;
    while e < gp_exit.len {
        if !dominates(b, gp_exit[e]) { return false; }
        e += 2;
    }
    return true;
}
fn gp_loop(h: u32) -> bool {
    lc_epoch++;
    let ep = lc_epoch;
    tmp_stack.clear();
    lc_mark[h] = ep;
    var pre: u32 = NIL;
    var npre = 0;
    for k in p_start[h]..p_start[h + 1] {
        let p = p_list[k];
        if rpo_num[p] == NIL { return false; }
        if !dominates(h, p) {
            pre = p;
            npre++;
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
    if npre != 1 || s_start[pre + 1] - s_start[pre] != 1 || block_invoke(pre) != NIL { return false; }
    // exit edges (one per pair: a block may branch twice to the same exit)
    gp_exit.clear();
    for b in rpo {
        if lc_mark[b] != ep { continue; }
        for k in s_start[b]..s_start[b + 1] {
            let x = s_list[k];
            if lc_mark[x] == ep { continue; }
            if b_fl[x] & BF_LP != 0 || block_invoke(b) != NIL { return false; }
            let tb = b_last[b];
            if o_ins[tb].op == GIR_CONDBR && o_ins[tb].b == o_ins[tb].c { return false; }
            if o_ins[tb].op != GIR_BR && o_ins[tb].op != GIR_CONDBR { return false; }
            gp_exit.push(b);
            gp_exit.push(x);
        }
    }
    // the accesses; no calls, no asm
    gp_list.clear();
    for b in rpo {
        if lc_mark[b] != ep { continue; }
        var i = b_first[b];
        while i != NIL {
            let I = o_ins[i];
            let op: u32 = I.op;
            if op == GIR_CALL || op == GIR_ASM || op == GIR_SJLJ_SETJMP || op == GIR_SJLJ_LONGJMP || op == GIR_LANDINGPAD
               || op == GIR_VASTART || op == GIR_A64 && a64_effect(I.sub) {
                for g in gp_list {
                    gp_ty[g] = NIL;
                    gp_st[g] = NIL;
                }
                return false;
            }
            var g: u32 = NIL;
            var t: u32 = NIL;
            if op == GIR_LOAD && gir_kind(res(I.a)) == GIR_V_GLOBAL {
                g = gir_idx(res(I.a));
                t = I.ty;
            } else if op == GIR_STORE && gir_kind(res(I.b)) == GIR_V_GLOBAL {
                g = gir_idx(res(I.b));
                t = I.aux;
            }
            if g != NIL && g < gp_ok.len && gp_ok[g] != 0 {
                if I.flags & (IF_VOLATILE | IF_ORD_MASK) != 0 || !promotable_type(t) { t = GV_MANY; }
                if gp_ty[g] == NIL {
                    gp_list.push(g);
                    gp_ty[g] = t;
                } else if gp_ty[g] != t {
                    gp_ty[g] = GV_MANY;
                }
                if op == GIR_STORE {
                    if gp_dom_exits(b) { gp_st[g] = b; } else if gp_st[g] == NIL { gp_st[g] = GV_MANY; }
                }
            }
            i = o_nxt[i];
        }
    }
    // which globals; exit blocks once for all of them
    var n: u32 = 0;
    var any_st = false;
    for g in gp_list {
        // (E2) a store in the function before the loop (in a block that
        // dominates the preheader) makes the stores on the exits safe too:
        // the global is written whenever the loop runs, so no other thread
        // may use it then without a race
        if gp_st[g] == GV_MANY && gp_pre_store(pre, g) { gp_st[g] = pre; }
        let ok = gp_ty[g] != GV_MANY && gp_st[g] != GV_MANY;
        if !ok {
            gp_ty[g] = NIL;
            gp_st[g] = NIL;
            continue;
        }
        gp_list[n] = g;
        n++;
        if gp_st[g] != NIL { any_st = true; }
    }
    gp_list.resize(n, 0);
    if n == 0 { return false; }
    let dbg = o_ins[b_last[pre]].dbg;
    gp_eblk.clear();
    if any_st {
        var e: i64 = 0;
        while e < gp_exit.len {
            let b = gp_exit[e];
            let x = gp_exit[e + 1];
            e += 2;
            let nb = new_block();
            let br = new_inst(Inst { op: GIR_BR as! u8, sub: 0, flags: 0, ty: GIR_T_VOID, aux: 0, a: x, b: 0, c: 0, dbg: dbg });
            link_end(nb, br);
            let bt = b_last[b];
            if o_ins[bt].op == GIR_BR { o_ins[bt].a = nb; }
            else if o_ins[bt].b == x { o_ins[bt].b = nb; }
            else { o_ins[bt].c = nb; }
            phi_rename_pred(x, b, nb);
            b_lnext[nb] = b_lnext[b];
            b_lnext[b] = nb;
            gp_eblk.push(nb);
        }
        o_cfg_ok = false;
    }
    for g in gp_list {
        gp_promote(g, gp_ty[g], ep, pre, gp_st[g] != NIL);
        gp_ty[g] = NIL;
        gp_st[g] = NIL;
    }
    return true;
}
fn gp_promote(g: u32, t: u32, ep: u32, pre: u32, stores: bool) {
    gp_promote_ptr((3 as u32) << 30 | g, t, ep, pre, stores);
}
fn gp_promote_ptr(gref: u32, t: u32, ep: u32, pre: u32, stores: bool) {
    let pt = b_last[pre];
    let a = new_inst(Inst { op: GIR_ALLOCA as! u8, sub: 0, flags: 0, ty: GIR_T_PTR, aux: 0, a: store_of(t),
                            b: M.types[t].align, c: 0, dbg: o_ins[pt].dbg });
    link_start(0, a);
    let v0 = rot_load(gref, t, pt);
    rot_store(v0, t, a, pt);
    for b in rpo {
        if lc_mark[b] != ep { continue; }
        var i = b_first[b];
        while i != NIL {
            let I = o_ins[i];
            if I.op == GIR_LOAD && res(I.a) == gref { o_ins[i].a = a; }
            else if I.op == GIR_STORE && res(I.b) == gref { o_ins[i].b = a; }
            i = o_nxt[i];
        }
    }
    if !stores { return; }
    for nb in gp_eblk {
        let br = b_last[nb];
        let v = rot_load(a, t, br);
        rot_store(v, t, gref, br);
    }
}
