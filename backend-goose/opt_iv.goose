// Induction-variable widening on the OIR (opt.goose), the part of LLVM's
// IndVarSimplify that matters for array code: clang computes an index in
// i32 and sign-extends it for every access (`a[i * n + j]`). Signed overflow
// being undefined (nsw), a sign extension of an nsw add, subtract or
// multiply by a constant becomes that operation in i64 on extended
// operands, and an i32 loop counter `i = phi [init, i + c]` whose
// extensions are used gets an i64 twin, which also takes over its signed
// and equality compares. LICM then hoists the invariant parts of the index
// (GEP splitting in opt_licm.goose), leaving `base[j]` in the loop.

var iv_wl: u32[>..] = [];

// Sign extension of x (i32) to i64 before `at`: a constant, or a new SEXT.
fn iv_sext(at: u32, x: u32) -> u32 {
    let k, v = ci(x);
    if k { return int_const(GIR_T_I64, sx(v, 32) as! u64); }
    return ins_cast(at, GIR_SEXT, GIR_T_I64, x, GIR_T_I32);
}

// Distributes sign extensions over nsw arithmetic (build_uses first).
fn iv_distribute() -> bool {
    var any = false;
    iv_wl.clear();
    for i in 0..o_ins.len {
        if o_blk[i] != NIL && o_ins[i].op == GIR_SEXT && o_ins[i].ty == GIR_T_I64 && o_ins[i].aux == GIR_T_I32 {
            iv_wl.push(i as! u32);
        }
    }
    var k: i64 = 0;
    while k < iv_wl.len {
        let s = iv_wl[k];
        k++;
        let y = res(o_ins[s].a);
        if !is_inst(y) || o_blk[y] == NIL { continue; }
        let Y = o_ins[y];
        let op: u32 = Y.op;
        if Y.flags & IF_NSW == 0 || Y.ty != GIR_T_I32 { continue; }
        if op != GIR_ADD && op != GIR_SUB && op != GIR_MUL && op != GIR_SHL { continue; }
        let a = res(Y.a);
        let b = res(Y.b);
        let ka, va = ci(a);
        let kb, vb = ci(b);
        // worth it when y has no other uses than extensions, or an operand is
        // a constant
        if y < u_start.len - 1 && !ka && !kb {
            var other = false;
            for q in u_start[y]..u_start[y + 1] {
                let u = u_list[q];
                if o_blk[u] != NIL && !(o_ins[u].op == GIR_SEXT && o_ins[u].ty == GIR_T_I64) { other = true; }
            }
            if other { continue; }
        }
        if op == GIR_SHL && !kb { continue; }
        var na: u32 = 0;
        var nb: u32 = 0;
        if op == GIR_SHL {
            na = iv_sext(s, a);
            nb = int_const(GIR_T_I64, vb & 63);
        } else {
            na = iv_sext(s, a);
            nb = iv_sext(s, b);
        }
        o_ins[s].op = op as! u8;
        o_ins[s].aux = 0;
        o_ins[s].a = na;
        o_ins[s].b = nb;
        o_ins[s].flags = IF_NSW;
        if is_inst(na) && o_ins[na].op == GIR_SEXT { iv_wl.push(na); }
        if is_inst(nb) && o_ins[nb].op == GIR_SEXT { iv_wl.push(nb); }
        any = true;
    }
    return any;
}

// The i64 twins of the loops' i32 counters (preheaders made by licm; build_cfg
// and build_uses first).
fn iv_widen() -> bool {
    var any = false;
    if lc_mark.len < cfg_nb { lc_mark.resize(cfg_nb, 0); }
    for h in rpo {
        if h == 0 || b_fl[h] & BF_LP != 0 || b_first[h] == NIL || o_ins[b_first[h]].op != GIR_PHI { continue; }
        // preheader and single latch
        var pre: u32 = NIL;
        var latch: u32 = NIL;
        var bad = false;
        for k in p_start[h]..p_start[h + 1] {
            let p = p_list[k];
            if rpo_num[p] == NIL { continue; }
            if dominates(h, p) {
                if latch != NIL && latch != p { bad = true; }
                latch = p;
            } else {
                if pre != NIL && pre != p { bad = true; }
                pre = p;
            }
        }
        if bad || pre == NIL || latch == NIL || s_start[pre + 1] - s_start[pre] != 1 { continue; }
        // the loop body
        lc_epoch++;
        let ep = lc_epoch;
        lc_mark[h] = ep;
        tmp_stack.clear();
        if lc_mark[latch] != ep {
            lc_mark[latch] = ep;
            tmp_stack.push(latch);
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
        let pt = b_last[pre];
        var i = b_first[h];
        while i != NIL && o_ins[i].op == GIR_PHI {
            let nx = o_nxt[i];
            if iv_widen_one(i, h, pre, latch, pt, ep) { any = true; }
            i = nx;
        }
    }
    return any;
}
fn iv_inloop(v: u32, ep: u32) -> bool { is_inst(v) && o_blk[v] != NIL && lc_mark[o_blk[v]] == ep }

fn iv_widen_one(iv: u32, h: u32, pre: u32, latch: u32, pt: u32, ep: u32) -> bool {
    let I = o_ins[iv];
    if I.ty != GIR_T_I32 || I.c != 2 || iv >= u_start.len - 1 { return false; }
    let init = res(phi_in(iv, pre));
    let nx = res(phi_in(iv, latch));
    if !is_inst(nx) || nx >= u_start.len - 1 || o_blk[nx] == NIL { return false; }
    let N = o_ins[nx];
    if N.op != GIR_ADD || N.flags & IF_NSW == 0 { return false; }
    var c: u32 = NIL;
    if res(N.a) == iv { c = res(N.b); } else if res(N.b) == iv { c = res(N.a); }
    let kc, vc = ci(c);
    if c == NIL || !kc { return false; }
    // extensions of iv or nx to widen
    var nsext = 0;
    for q in u_start[iv]..u_start[iv + 1] {
        let u = u_list[q];
        if o_blk[u] != NIL && o_ins[u].op == GIR_SEXT && o_ins[u].ty == GIR_T_I64 { nsext++; }
    }
    for q in u_start[nx]..u_start[nx + 1] {
        let u = u_list[q];
        if o_blk[u] != NIL && o_ins[u].op == GIR_SEXT && o_ins[u].ty == GIR_T_I64 { nsext++; }
    }
    if nsext == 0 { return false; }
    // the twin: phi [sext init, nx64], nx64 = iv64 + c
    let init64 = iv_sext(pt, init);
    let s = new_run(4);
    let iv64 = new_inst(Inst { op: GIR_PHI as! u8, sub: 0, flags: 0, ty: GIR_T_I64, aux: 0, a: 0, b: s, c: 2, dbg: 0 });
    link_start(h, iv64);
    let nx64 = new_inst(Inst { op: GIR_ADD as! u8, sub: 0, flags: IF_NSW, ty: GIR_T_I64, aux: 0, a: iv64,
                               b: int_const(GIR_T_I64, sx(vc, 32) as! u64), c: 0, dbg: N.dbg });
    link_after(nx, nx64);
    o_ops[s] = init64;
    o_ops[s + 1] = pre;
    o_ops[s + 2] = nx64;
    o_ops[s + 3] = latch;
    // the uses
    for pass in 2 {
        let v = if pass == 0 { iv } else { nx };
        let w = if pass == 0 { iv64 } else { nx64 };
        for q in u_start[v]..u_start[v + 1] {
            let u = u_list[q];
            if o_blk[u] == NIL || u == nx64 || u == nx && pass == 0 { continue; }
            let U = o_ins[u];
            if U.op == GIR_SEXT && U.ty == GIR_T_I64 {
                replace(u, w);
            } else if U.op == GIR_ICMP && U.aux == GIR_T_I32 && (U.sub == GIR_EQ || U.sub == GIR_NE || U.sub >= GIR_SGT)
                      && lc_mark[o_blk[u]] == ep {
                // a compare in the loop with an invariant (defined before the
                // loop, so it dominates the preheader): in i64
                let other = if res(U.a) == v { res(U.b) } else { res(U.a) };
                if iv_inloop(other, ep) || res(U.a) == res(U.b) { continue; }
                let o64 = iv_sext(pt, other);
                if res(U.a) == v {
                    o_ins[u].a = w;
                    o_ins[u].b = o64;
                } else {
                    o_ins[u].a = o64;
                    o_ins[u].b = w;
                }
                o_ins[u].aux = GIR_T_I64;
            }
        }
    }
    return true;
}

fn indvars() -> bool {
    if o_pinned { return false; }
    var any = false;
    for round in 3 {
        resolve_all();
        dce();
        build_uses();
        if !iv_distribute() { break; }
        any = true;
    }
    resolve_all();
    dce();
    build_uses();
    ensure_cfg();
    if iv_widen() { any = true; }
    return any;
}
