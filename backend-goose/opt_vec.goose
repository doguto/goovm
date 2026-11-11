// Loop vectorization (milestone E2; LLVM's LoopVectorize for the loops it
// handles most often) on the OIR (opt.goose), for 16-byte vectors (SSE2,
// the x86-64 baseline; lowerv.goose has the instruction selection).
//
// A loop is vectorized when it is innermost and one block (the header is
// the latch: a rotated loop after if-conversion), its exit test is
// `iv.next <s/<u/!= n` with iv a PHI that counts up by one from init and n
// invariant, and every other PHI is a reduction (r = r op x with op add,
// and, or, xor on i32 or i64; r used by nothing else in the loop). Every
// value the loop computes has one lane width, which gives the vector
// factor VF = 16 / width; loads and stores are of consecutive elements (a
// GEP of an invariant base indexed by the IV, scaled by the element size)
// or loads of invariant addresses; the operations are integer add, sub,
// and, or, xor, mul (16 and 32 bits), shifts by a constant, FP add, sub,
// mul, div, neg, abs. Two accesses of one base must use the same index and
// offset; accesses of bases the alias analysis cannot separate get a
// run-time check that their ranges do not overlap. Values used after the
// loop are only the IV's next value and the reductions' results.
//
// The vector loop runs (n - init) & -VF iterations of VF lanes each, then
// the reductions are added up across lanes and the original loop runs the
// rest:
//
//   P:    br VCHK
//   VCHK: tc = n - init; ok = n > init && tc >= VF && checks; condbr ok, VPH, SPH
//   VPH:  vtc = tc & -VF; splats of the invariants; reduction start vectors
//   VB:   vi = phi [0, VPH], [vi + VF, VB]; the vector body; condbr vi + VF == vtc, VMID, VB
//   VMID: reductions across lanes; iend = init + vtc; condbr vtc == tc, X, SPH
//   SPH:  iv and reduction PHIs: from VCHK (init, the start values) or VMID
//   H:    the original loop, from SPH
//   X:    the exit (a block of its own), with PHIs of the values used after the loop

var vz_map: u32[>..] = [];      // loop instruction -> its vector value in VB, NIL
var vz_h: u32 = 0;               // the loop
var vz_kind: u8[>..] = [];      // loop instruction -> VZ_*
let VZ_NONE: u8 = 0;
let VZ_VEC: u8 = 1;             // a vector value
let VZ_ADDR: u8 = 2;            // a consecutive address (GEP of the IV)
let VZ_IV: u8 = 3;
let VZ_IVNEXT: u8 = 4;
let VZ_RED: u8 = 5;             // a reduction PHI
let VZ_REDOP: u8 = 6;           // its operation
let VZ_CMP: u8 = 7;             // the exit compare
let VZ_SCAL: u8 = 8;            // a scalar computed in the loop from invariants only (a load of an invariant address)
let VZ_IVX: u8 = 9;             // an extension of the IV (for addresses only)
var vz_red: u32[>..] = [];      // reduction PHIs
var vz_chk: u32[>..] = [];      // pairs of accesses that need a run-time check
var vz_acc: u32[>..] = [];      // the loop's loads and stores
var vz_splat: u32[>..] = [];    // invariant value -> its splat (pairs: value, splat)
var vz_esz: u32 = 0;
var vz_vf: u32 = 0;

fn vectorize_loops() -> bool {
    if o_pinned || opt_lv < 2 || o_f.flags & FN_MINSIZE != 0 || opt_sz >= 2 { return false; }
    loop_preheaders();
    loop_headers();
    var any = false;
    var k: i64 = 0;
    while k < lp_hdrs.len {
        let h = lp_hdrs[k];
        k++;
        if rpo_num[h] == NIL { continue; }
        resolve_all();
        build_uses();
        aa_prepare();
        if vec_loop(h) {
            any = true;
            ensure_cfg();
        }
    }
    return any;
}

// The lane size of type t if a vector of it can be built (int 8..64, f32, f64).
fn vz_lane(t: u32) -> u32 {
    if t == GIR_T_F32 { return 4; }
    if t == GIR_T_F64 { return 8; }
    if cls_of(t) == C_INT && t != GIR_T_I1 {
        let b = bits_of(t);
        if b == 8 || b == 16 || b == 32 || b == 64 { return b / 8; }
    }
    return 0;
}
inline fn vz_in(v: u32, h: u32) -> bool { is_inst(v) && o_blk[v] == h }

// The IV value of a GEP index term (iv, sext/zext of iv), or NIL.
fn vz_iv_of(v0: u32, iv: u32) -> u32 {
    let v = res(v0);
    if v == iv { return iv; }
    if is_inst(v) && (o_ins[v].op == GIR_SEXT || o_ins[v].op == GIR_ZEXT) && res(o_ins[v].a) == iv { return iv; }
    return NIL;
}

fn vec_loop(h: u32) -> bool {
    if !loop_collect(h) || lp_body.len != 1 || lp_pre == NIL || lp_exit == NIL || lp_exiting != h || lp_latch != h {
        return false;
    }
    if b_fl[lp_exit] & BF_LP != 0 || b_fl[h] & BF_VECD != 0 || o_ins[b_last[lp_pre]].op != GIR_BR { return false; }
    vz_h = h;
    let T = o_ins[b_last[h]];
    if T.op != GIR_CONDBR { return false; }
    let back_true = T.b == h;
    let n0: u32 = o_ins.len as! u32;
    if vz_map.len < n0 {
        vz_map.resize(n0, NIL);
        vz_kind.resize(n0, 0);
    }
    var i = b_first[h];
    while i != NIL {
        vz_map[i] = NIL;
        vz_kind[i] = VZ_NONE;
        i = o_nxt[i];
    }
    // the exit test: iv.next pred n, continuing on true
    let c = res(T.a);
    if !vz_in(c, h) || o_ins[c].op != GIR_ICMP { return false; }
    let C = o_ins[c];
    var pred: u32 = C.sub;
    var lhs = res(C.a);
    var nb = res(C.b);
    if vz_in(nb, h) {
        let t = lhs;
        lhs = nb;
        nb = t;
        pred = swap_pred(pred);
    }
    if vz_in(nb, h) || !vz_in(lhs, h) { return false; }
    if !back_true { pred = inv_pred(pred); }
    if pred != GIR_SLT && pred != GIR_ULT && pred != GIR_NE { return false; }
    let L = o_ins[lhs];
    if L.op != GIR_ADD { return false; }
    let iv = res(L.a);
    let ks, step = ci(res(L.b));
    if !ks || step != 1 || !vz_in(iv, h) || o_ins[iv].op != GIR_PHI { return false; }
    let ivt: u32 = o_ins[iv].ty;
    if ivt != GIR_T_I32 && ivt != GIR_T_I64 { return false; }
    // the PHIs: the IV and reductions
    vz_red.clear();
    var init: u32 = NIL;
    i = b_first[h];
    while i != NIL && o_ins[i].op == GIR_PHI {
        let P = o_ins[i];
        if P.c != 2 { return false; }
        var pv: u32 = NIL;
        var lv: u32 = NIL;
        for q in 0..2 {
            if o_ops[P.b + 2 * q + 1] == lp_pre { pv = res(o_ops[P.b + 2 * q]); } else { lv = res(o_ops[P.b + 2 * q]); }
        }
        if pv == NIL || lv == NIL { return false; }
        if i == iv {
            if lv != lhs { return false; }
            init = pv;
            vz_kind[i] = VZ_IV;
        } else {
            // r = phi [r0, P], [r op x, H], the op's other operand not r
            if !vz_in(lv, h) { return false; }
            let R = o_ins[lv];
            let rop: u32 = R.op;
            if rop != GIR_ADD && rop != GIR_AND && rop != GIR_OR && rop != GIR_XOR { return false; }
            if P.ty != GIR_T_I32 && P.ty != GIR_T_I64 { return false; }
            if res(R.a) != i && res(R.b) != i || res(R.a) == i && res(R.b) == i { return false; }
            if u_start[i + 1] - u_start[i] != 1 { return false; }     // (only the op uses r)
            // (and in the loop only r uses the op: a partial value is no
            // scalar's value; r = r + 1 used by the body is a second IV)
            for q in u_start[lv]..u_start[lv + 1] {
                let u = u_list[q];
                if u != i && o_blk[u] == h { return false; }
            }
            vz_kind[i] = VZ_RED;
            vz_kind[lv] = VZ_REDOP;
            vz_red.push(i);
        }
        i = o_nxt[i];
    }
    if init == NIL { return false; }
    vz_kind[lhs] = VZ_IVNEXT;
    vz_kind[c] = VZ_CMP;
    // the body: lane width, addresses, operations
    vz_esz = 0;
    vz_acc.clear();
    while i != NIL {
        let I = o_ins[i];
        let op: u32 = I.op;
        if i == b_last[h] { break; }
        if vz_kind[i] != VZ_NONE { i = o_nxt[i]; continue; }
        if op == GIR_GEP {
            // a consecutive address, or an invariant-only one (left scalar)
            if I.c == 1 && !vz_in(res(I.a), h) && vz_iv_of(o_ops[I.b + 2], iv) != NIL {
                vz_kind[i] = VZ_ADDR;
            } else if I.c == 0 && !vz_in(res(I.a), h) {
                vz_kind[i] = VZ_SCAL;
            } else {
                return false;
            }
        } else if op == GIR_SEXT || op == GIR_ZEXT {
            // (an index extension of the IV: only for addresses)
            if res(I.a) != iv { return false; }
            vz_kind[i] = VZ_IVX;
        } else if op == GIR_LOAD || op == GIR_STORE {
            if I.flags & (IF_VOLATILE | IF_ORD_MASK) != 0 { return false; }
            let p = res(if op == GIR_LOAD { I.a } else { I.b });
            let t: u32 = if op == GIR_LOAD { I.ty } else { I.aux };
            let w = vz_lane(t);
            if w == 0 { return false; }
            if vz_in(p, h) && vz_kind[p] == VZ_ADDR {
                if o_ops[o_ins[p].b + 3] != w { return false; }   // (scale = element size)
                if vz_esz == 0 { vz_esz = w; } else if vz_esz != w { return false; }
                vz_kind[i] = if op == GIR_LOAD { VZ_VEC } else { VZ_NONE };
                vz_acc.push(i);
            } else if op == GIR_LOAD && (!vz_in(p, h) || vz_kind[p] == VZ_SCAL && o_ins[p].op == GIR_GEP) {
                vz_kind[i] = VZ_SCAL;    // (invariant address: one scalar load, splat)
                vz_acc.push(i);
            } else {
                return false;
            }
        } else if op >= GIR_ADD && op <= GIR_ASHR || op >= GIR_FADD && op <= GIR_FDIV || op == GIR_FNEG || op == GIR_FABS {
            let w = vz_lane(I.ty);
            if w == 0 { return false; }
            if vz_esz == 0 { vz_esz = w; } else if vz_esz != w { return false; }
            let lfp = cls_of(I.ty) == C_FP;
            if op >= GIR_SDIV && op <= GIR_UREM { return false; }
            if op == GIR_MUL && (w == 1 || w == 8) { return false; }
            if op >= GIR_SHL && op <= GIR_ASHR {
                let kc, sc = ci(res(I.b));
                if !kc || w == 1 || op == GIR_ASHR && w == 8 || sc >= (8 * w) as u64 { return false; }
            }
            if lfp && op < GIR_FADD { return false; }
            vz_kind[i] = VZ_VEC;
        } else if op == GIR_BITCAST {
            if vz_lane(I.ty) != vz_lane(I.aux) || vz_lane(I.ty) == 0 { return false; }
            vz_kind[i] = VZ_VEC;
        } else {
            return false;
        }
        i = o_nxt[i];
    }
    if vz_esz == 0 { return false; }
    // reductions: of the lane width, not FP
    for r in vz_red {
        if store_of(o_ins[r].ty) != vz_esz || vz_esz < 4 { return false; }
    }
    vz_vf = 16 / vz_esz;
    // operands: a vector operand must be a vector value, the IV only in addresses
    i = b_first[h];
    while i != NIL {
        let I = o_ins[i];
        let k = vz_kind[i];
        if k == VZ_VEC || k == VZ_REDOP || i != b_last[h] && k == VZ_NONE && I.op == GIR_STORE {
            var bad = false;
            each_slot(i) { s =>
                let v = res(vget(i, s));
                if vz_in(v, h) {
                    let kv = vz_kind[v];
                    if kv == VZ_IV || kv == VZ_IVNEXT || kv == VZ_CMP || kv == VZ_IVX { bad = true; }
                    if (kv == VZ_ADDR || kv == VZ_SCAL && o_ins[v].op != GIR_LOAD) && !(I.op == GIR_LOAD && s == SLOT_A || I.op == GIR_STORE && s == SLOT_B) {
                        bad = true;
                    }
                }
            };
            if bad { return false; }
            if k == VZ_REDOP {
                // (the reduction's other operand must be a vector value or invariant)
            }
        }
        // values used outside the loop: the IV's next value and the reductions' results only
        for q in u_start[i]..u_start[i + 1] {
            let u = u_list[q];
            if o_blk[u] == NIL || o_blk[u] == h { continue; }
            if k != VZ_IVNEXT && k != VZ_REDOP { return false; }
        }
        i = o_nxt[i];
    }
    // memory dependences
    vz_chk.clear();
    for a in vz_acc {
        if o_ins[a].op != GIR_STORE { continue; }
        let pa = res(o_ins[a].b);
        for b in vz_acc {
            if b == a { continue; }
            let B = o_ins[b];
            let pb = res(if B.op == GIR_LOAD { B.a } else { B.b });
            if vz_same_access(pa, pb) || vz_far_access(pa, pb) { continue; }
            let ba = res(o_ins[pa].a);
            let bb = if is_inst(pb) && vz_kind[pb] == VZ_ADDR { res(o_ins[pb].a) } else { pb };
            if ba == bb { return false; }       // (another index or offset of the same base)
            let ta = o_ins[a].c;
            let tb = if B.op == GIR_LOAD { B.b } else { B.c };
            if !aa_alias(ba, 0, ta, bb, 0, tb) { continue; }
            // (an invariant address against the stores: checked like a range of one element)
            if vz_chk.len >= 16 { return false; }
            vz_chk.push(a);
            vz_chk.push(b);
        }
    }
    vz_build(h, iv, init, nb, pred, ivt);
    return true;
}
// Whether two addresses are the same element of each iteration.
fn vz_same_access(pa: u32, pb: u32) -> bool {
    if pa == pb { return true; }
    if !is_inst(pa) || !is_inst(pb) { return false; }
    let A = o_ins[pa];
    let B = o_ins[pb];
    if A.op != GIR_GEP || B.op != GIR_GEP || A.c != B.c { return false; }
    if res(A.a) != res(B.a) { return false; }
    for k in 0..2 + 2 * A.c {
        var x = o_ops[A.b + k];
        var y = o_ops[B.b + k];
        if k >= 2 && k % 2 == 0 {
            x = res(x);
            y = res(y);
            // (sext iv and zext iv of one iv count as one index when both are the same op)
        }
        if x != y { return false; }
    }
    return true;
}

// Whether two addresses of one base and the same index terms are at least
// a vector apart (constant offsets differing by 16 bytes or more): no lane
// of one vector access touches the other's in the same vector iteration,
// and the vector iterations keep their order.
fn vz_far_access(pa: u32, pb: u32) -> bool {
    if !is_inst(pa) || !is_inst(pb) { return false; }
    let A = o_ins[pa];
    let B = o_ins[pb];
    if A.op != GIR_GEP || B.op != GIR_GEP || A.c != B.c || res(A.a) != res(B.a) { return false; }
    for k in 2..2 + 2 * A.c {
        var x = o_ops[A.b + k];
        var y = o_ops[B.b + k];
        if k % 2 == 0 {
            x = res(x);
            y = res(y);
        }
        if x != y { return false; }
    }
    let oa = (o_ops[A.b] as u64 | (o_ops[A.b + 1] as u64 << 32)) as! i64;
    let ob = (o_ops[B.b] as u64 | (o_ops[B.b + 1] as u64 << 32)) as! i64;
    let d = if oa > ob { oa - ob } else { ob - oa };
    return d >= 16;
}

// ------------------------------------------------------------- building
fn vz_new(b: u32, op: u32, ty: u32, a: u32, bb: u32, c: u32, dbg: u32) -> u32 {
    let x = new_inst(Inst { op: op as! u8, sub: 0, flags: 0, ty: ty as! u16, aux: 0, a: a, b: bb, c: c, dbg: dbg });
    link_end(b, x);
    return x;
}
fn vz_br(b: u32, to: u32) {
    let x = new_inst(Inst { op: GIR_BR as! u8, sub: 0, flags: 0, ty: GIR_T_VOID, aux: 0, a: to, b: 0, c: 0, dbg: 0 });
    link_end(b, x);
}
fn vz_condbr(b: u32, cnd: u32, t: u32, f: u32) {
    let x = new_inst(Inst { op: GIR_CONDBR as! u8, sub: 0, flags: 0, ty: GIR_T_VOID, aux: 0, a: cnd, b: t, c: f, dbg: 0 });
    link_end(b, x);
}
fn vz_icmp(b: u32, p: u32, t: u32, x: u32, y: u32) -> u32 {
    let c = new_inst(Inst { op: GIR_ICMP as! u8, sub: p as! u8, flags: 0, ty: GIR_T_I1, aux: t as! u16, a: x, b: y, c: 0,
                            dbg: 0 });
    link_end(b, c);
    return c;
}
fn vz_phi2(b: u32, ty: u32, v1: u32, b1: u32, v2: u32, b2: u32) -> u32 {
    let s = new_run(4);
    o_ops[s] = v1;
    o_ops[s + 1] = b1;
    o_ops[s + 2] = v2;
    o_ops[s + 3] = b2;
    let p = new_inst(Inst { op: GIR_PHI as! u8, sub: 0, flags: 0, ty: ty as! u16, aux: 0, a: 0, b: s, c: 2, dbg: 0 });
    link_start(b, p);
    return p;
}
// A shuffle of v (type vt) with lanes m[k] (GIR_NONE: undefined).
fn vz_shuffle(b: u32, vt: u32, v: u32, m0: u32, m1: u32, m2: u32, m3: u32) -> u32 {
    let n = M.types[vt].n;
    let s = new_run(n);
    for k in 0..n { o_ops[s + k] = GIR_NONE; }
    o_ops[s] = m0;
    if n > 1 { o_ops[s + 1] = m1; }
    if n > 2 { o_ops[s + 2] = m2; }
    if n > 3 { o_ops[s + 3] = m3; }
    let x = new_inst(Inst { op: GIR_SHUFFLE as! u8, sub: 0, flags: 0, ty: vt as! u16, aux: vt as! u16, a: v,
                            b: undef_of(vt), c: s, dbg: 0 });
    link_end(b, x);
    return x;
}
// The splat of scalar v (type t) as a vector of type vt, built in block b
// (VPH): insertelement into lane 0, then a shuffle of lane 0 (32 and 64-bit
// lanes) or, for narrower lanes, the scalar widened by multiplication.
fn vz_splat_of(b: u32, v: u32, t: u32, vt: u32) -> u32 {
    for k in 0..vz_splat.len / 2 { if vz_splat[2 * k] == v { return vz_splat[2 * k + 1]; } }
    let es = store_of(t);
    var r: u32 = NIL;
    if es >= 4 {
        let ins = vz_new(b, GIR_INSERTELT, vt, undef_of(vt), v, int_const(GIR_T_I32, 0), 0);
        r = vz_shuffle(b, vt, ins, 0, 0, 0, 0);
    } else {
        // i8 / i16: the value replicated into an i32 (x * 0x01010101 or
        // 0x00010001 of its zero extension), splat as <4 x i32>, bitcast
        let z = vz_new(b, GIR_ZEXT, GIR_T_I32, v, 0, 0, 0);
        o_ins[z].aux = t as! u16;
        let m = vz_new(b, GIR_MUL, GIR_T_I32, z, int_const(GIR_T_I32, if es == 1 { 0x01010101 } else { 0x00010001 }), 0, 0);
        let v4 = vec_type(4, GIR_T_I32);
        let ins = vz_new(b, GIR_INSERTELT, v4, undef_of(v4), m, int_const(GIR_T_I32, 0), 0);
        let sp = vz_shuffle(b, v4, ins, 0, 0, 0, 0);
        r = vz_new(b, GIR_BITCAST, vt, sp, 0, 0, 0);
        o_ins[r].aux = v4 as! u16;
    }
    vz_splat.push(v);
    vz_splat.push(r);
    return r;
}

fn vz_build(h: u32, iv: u32, init: u32, n: u32, pred: u32, ivt: u32) {
    let P = lp_pre;
    let E = lp_exit;
    let vf = vz_vf;
    let dbg = o_ins[b_last[h]].dbg;
    let VCHK = new_block();
    let VPH = new_block();
    let VB = new_block();
    let VMID = new_block();
    let SPH = new_block();
    let X = new_block();
    vz_splat.clear();
    b_fl[h] |= BF_VECD;
    // layout: P, VCHK, VPH, VB, VMID, SPH, H, X, (what followed H)
    vz_link_after(P, VCHK);
    vz_link_after(VCHK, VPH);
    vz_link_after(VPH, VB);
    vz_link_after(VB, VMID);
    vz_link_after(VMID, SPH);
    b_lnext[X] = b_lnext[h];
    b_lnext[h] = X;
    o_ins[b_last[P]].a = VCHK;
    // VCHK: the trip count and the checks
    let tc = vz_new(VCHK, GIR_SUB, ivt, n, init, 0, dbg);
    let gt = vz_icmp(VCHK, if pred == GIR_ULT { GIR_UGT } else { GIR_SGT }, ivt, n, init);
    let big = vz_icmp(VCHK, GIR_UGE, ivt, tc, int_const(ivt, vf as u64));
    var ok = vz_new(VCHK, GIR_AND, GIR_T_I1, gt, big, 0, dbg);
    var q: i64 = 0;
    while q < vz_chk.len {
        let a = vz_chk[q];
        let b = vz_chk[q + 1];
        q += 2;
        let sa, ea = vz_range(VCHK, a, init, n, ivt);
        let sb, eb = vz_range(VCHK, b, init, n, ivt);
        let c1 = vz_icmp(VCHK, GIR_ULE, GIR_T_PTR, ea, sb);
        let c2 = vz_icmp(VCHK, GIR_ULE, GIR_T_PTR, eb, sa);
        let c3 = vz_new(VCHK, GIR_OR, GIR_T_I1, c1, c2, 0, dbg);
        ok = vz_new(VCHK, GIR_AND, GIR_T_I1, ok, c3, 0, dbg);
    }
    vz_condbr(VCHK, ok, VPH, SPH);
    // VPH: the vector trip count, the reductions' start vectors
    let vtc = vz_new(VPH, GIR_AND, ivt, tc, int_const(ivt, wmask(bits_of(ivt)) & ~((vf - 1) as u64)), 0, dbg);
    // VB: the vector loop
    let vi_n = new_inst(Inst { op: GIR_ADD as! u8, sub: 0, flags: 0, ty: ivt as! u16, aux: 0, a: 0, b: int_const(ivt, vf as u64),
                               c: 0, dbg: dbg });
    let vi = vz_phi2(VB, ivt, int_const(ivt, 0), VPH, vi_n, VB);
    o_ins[vi_n].a = vi;
    let idx = vz_new(VB, GIR_ADD, ivt, init, vi, 0, dbg);
    // reductions: vector PHIs
    for r in vz_red {
        let rt: u32 = o_ins[r].ty;
        let vt = vec_type(vf, rt);
        let R = o_ins[r];
        var r0: u32 = NIL;
        for k in 0..2 { if o_ops[R.b + 2 * k + 1] == P { r0 = res(o_ops[R.b + 2 * k]); } }
        let rop: u32 = o_ins[vz_redop(r, h)].op;
        // start: the identity in every lane but lane 0, which holds r0
        var idv = undef_of(vt);
        if rop == GIR_AND {
            var ones: u8[16] = [0xFF; 16];
            idv = vec_const(vt, ones[..]);
        }
        let st = vz_new(VPH, GIR_INSERTELT, vt, idv, r0, int_const(GIR_T_I32, 0), dbg);
        let vp = vz_phi2(VB, vt, st, VPH, NIL, VB);
        vz_map[r] = vp;
    }
    // the body, in order
    var i = b_first[h];
    while i != NIL {
        let I = o_ins[i];
        let k = vz_kind[i];
        if i == b_last[h] { break; }
        if k == VZ_ADDR {
            let s = new_run(4);
            o_ops[s] = o_ops[I.b];
            o_ops[s + 1] = o_ops[I.b + 1];
            let tv = res(o_ops[I.b + 2]);
            var ix = idx;
            if tv != iv {
                // (sext / zext of the IV: of the scalar index)
                ix = vz_new(VB, o_ins[tv].op, o_ins[tv].ty, idx, 0, 0, I.dbg);
                o_ins[ix].aux = ivt as! u16;
            }
            o_ops[s + 2] = ix;
            o_ops[s + 3] = o_ops[I.b + 3];
            vz_map[i] = vz_new(VB, GIR_GEP, GIR_T_PTR, res(I.a), s, 1, I.dbg);
        } else if k == VZ_SCAL {
            // an invariant computation (scalar, in VPH)
            let x = new_inst(I);
            if I.op == GIR_GEP {
                let s = new_run(2 + 2 * I.c);
                for w in 0..2 + 2 * I.c { o_ops[s + w] = o_ops[I.b + w]; }
                o_ins[x].b = s;
            }
            each_slot(x) { sl => vset(x, sl, vz_val(res(vget(x, sl)))); };
            link_end(VPH, x);
            vz_map[i] = x;
        } else if k == VZ_VEC && I.op == GIR_LOAD {
            let vt = vec_type(vf, I.ty);
            let x = vz_new(VB, GIR_LOAD, vt, vz_map[res(I.a)], I.b, 0, I.dbg);
            vz_map[i] = x;
        } else if k == VZ_NONE && I.op == GIR_STORE {
            let vt = vec_type(vf, I.aux);
            let x = new_inst(Inst { op: GIR_STORE as! u8, sub: 0, flags: 0, ty: GIR_T_VOID, aux: vt as! u16,
                                    a: vz_vec(VPH, res(I.a), I.aux, vt), b: vz_map[res(I.b)], c: I.c, dbg: I.dbg });
            link_end(VB, x);
        } else if k == VZ_VEC || k == VZ_REDOP {
            let vt = vec_type(vf, I.ty);
            let x = new_inst(I);
            o_ins[x].ty = vt as! u16;
            if I.op == GIR_BITCAST { o_ins[x].aux = vec_type(vf, I.aux) as! u16; }
            each_slot(x) { sl =>
                let v = res(vget(x, sl));
                vset(x, sl, vz_vec(VPH, v, otype(v), vec_type(vf, otype(v))));
            };
            link_end(VB, x);
            vz_map[i] = x;
        }
        i = o_nxt[i];
    }
    vz_br(VPH, VB);
    // the reductions' PHIs: the latch values
    for r in vz_red {
        let vp = vz_map[r];
        o_ops[o_ins[vp].b + 2] = vz_map[vz_redop(r, h)];
    }
    link_end(VB, vi_n);
    let done = vz_icmp(VB, GIR_EQ, ivt, vi_n, vtc);
    vz_condbr(VB, done, VMID, VB);
    // VMID: the reductions across the lanes, the end of the IV
    let iend = vz_new(VMID, GIR_ADD, ivt, init, vtc, 0, dbg);
    for r in vz_red {
        let rt: u32 = o_ins[r].ty;
        let vt = vec_type(vf, rt);
        let rop: u32 = o_ins[vz_redop(r, h)].op;
        var v = vz_map[vz_redop(r, h)];
        if vf == 4 {
            let s1 = vz_shuffle(VMID, vt, v, 2, 3, GIR_NONE, GIR_NONE);
            v = vz_new(VMID, rop, vt, v, s1, 0, dbg);
            let s2 = vz_shuffle(VMID, vt, v, 1, GIR_NONE, GIR_NONE, GIR_NONE);
            v = vz_new(VMID, rop, vt, v, s2, 0, dbg);
        } else {
            let s1 = vz_shuffle(VMID, vt, v, 1, GIR_NONE, 0, 0);
            v = vz_new(VMID, rop, vt, v, s1, 0, dbg);
        }
        let e = vz_new(VMID, GIR_EXTRACTELT, rt, v, int_const(GIR_T_I32, 0), 0, dbg);
        o_ins[e].aux = vt as! u16;
        vz_map[vz_redop(r, h)] = e;   // (now: the reduction's value after the vector loop)
    }
    let all = vz_icmp(VMID, GIR_EQ, ivt, vtc, tc);
    vz_condbr(VMID, all, X, SPH);
    // SPH: the scalar loop's start values
    let ivs = vz_phi2(SPH, ivt, init, VCHK, iend, VMID);
    vz_br(SPH, h);
    // the original loop starts from SPH
    var ph = b_first[h];
    while ph != NIL && o_ins[ph].op == GIR_PHI {
        let PI = o_ins[ph];
        for kk in 0..2 {
            if o_ops[PI.b + 2 * kk + 1] != P { continue; }
            o_ops[PI.b + 2 * kk + 1] = SPH;
            if ph == iv { o_ops[PI.b + 2 * kk] = ivs; }
            else {
                let r0 = res(o_ops[PI.b + 2 * kk]);
                let rf = vz_map[vz_redop(ph, h)];
                o_ops[PI.b + 2 * kk] = vz_phi2(SPH, PI.ty, r0, VCHK, rf, VMID);
            }
        }
        ph = o_nxt[ph];
    }
    // X: the exit, with the values used after the loop
    let HT = b_last[h];
    if o_ins[HT].b == E { o_ins[HT].b = X; } else { o_ins[HT].c = X; }
    vz_br(X, E);
    phi_rename_pred(E, h, X);
    i = b_first[h];
    while i != NIL {
        let k = vz_kind[i];
        if k == VZ_IVNEXT || k == VZ_REDOP {
            var outside = false;
            for q2 in u_start[i]..u_start[i + 1] {
                let u = u_list[q2];
                if o_blk[u] != NIL && o_blk[u] != h { outside = true; }
            }
            if outside {
                let fin = if k == VZ_IVNEXT { iend } else { vz_map[i] };
                let xp = vz_phi2(X, o_ins[i].ty, i, h, fin, VMID);
                for q2 in u_start[i]..u_start[i + 1] {
                    let u = u_list[q2];
                    if o_blk[u] == NIL || o_blk[u] == h || u == xp { continue; }
                    each_slot(u) { s => if res(vget(u, s)) == i { vset(u, s, xp); } };
                }
            }
        }
        i = o_nxt[i];
    }
    o_cfg_ok = false;
}
fn vz_link_after(a: u32, b: u32) {
    b_lnext[b] = b_lnext[a];
    b_lnext[a] = b;
}
// The reduction operation of reduction PHI r.
fn vz_redop(r: u32, h: u32) -> u32 {
    let R = o_ins[r];
    for k in 0..2 {
        let v = res(o_ops[R.b + 2 * k]);
        if vz_in(v, h) { return v; }
    }
    return NIL;
}
// The scalar value of v inside VPH (an invariant computed in the loop: its copy).
fn vz_val(v: u32) -> u32 {
    if vz_in(v, vz_h) && vz_map[v] != NIL && vz_kind[v] == VZ_SCAL { return vz_map[v]; }
    return v;
}
// The vector value of operand v (type t, vector type vt): the loop's vector
// value, or the splat of an invariant (built in VPH).
fn vz_vec(vph: u32, v: u32, t: u32, vt: u32) -> u32 {
    if vz_in(v, vz_h) && vz_map[v] != NIL {
        if vz_kind[v] != VZ_SCAL { return vz_map[v]; }
        return vz_splat_of(vph, vz_map[v], t, vt);
    }
    if gir_kind(v) == GIR_V_CONST {
        let k, x = ci(v);
        if k && x == 0 { return undef_of(vt); }
        if k {
            // a constant splat
            let es = store_of(t);
            var bytes: u8[16] = [0; 16];
            for q in 0..16 { bytes[q] = ((x >> (8 * (q % es))) & 0xFF) as! u8; }
            return vec_const(vt, bytes[..]);
        }
        let C = x_consts[xb_c + gir_idx(v)];
        if C.data == GIR_NONE && C.lo == 0 { return undef_of(vt); }
        if (t == GIR_T_F32 || t == GIR_T_F64) && C.data == GIR_NONE {
            let es = store_of(t);
            var bytes: u8[16] = [0; 16];
            for q in 0..16 { bytes[q] = ((C.lo >> (8 * (q % es))) & 0xFF) as! u8; }
            return vec_const(vt, bytes[..]);
        }
    }
    return vz_splat_of(vph, v, t, vt);
}
// The range [start, end) of access a over the iterations init .. n: its GEP
// with the index init and n.
fn vz_range(b: u32, a: u32, init: u32, n: u32, ivt: u32) -> u32, u32 {
    let A = o_ins[a];
    var p = res(if A.op == GIR_LOAD { A.a } else { A.b });
    let sz: u32 = store_of(if A.op == GIR_LOAD { A.ty } else { A.aux });
    if !is_inst(p) || o_ins[p].op != GIR_GEP || o_ins[p].c != 1 {
        // (an invariant address: one element; a GEP of the loop, of constant
        // offsets only, is rebuilt before it)
        if is_inst(p) && o_blk[p] != b && o_ins[p].op == GIR_GEP && o_ins[p].c == 0 {
            let G = o_ins[p];
            let s0 = new_run(2);
            o_ops[s0] = o_ops[G.b];
            o_ops[s0 + 1] = o_ops[G.b + 1];
            p = vz_new(b, GIR_GEP, GIR_T_PTR, res(G.a), s0, 0, 0);
        }
        let s = new_run(2);
        o_ops[s] = sz;
        o_ops[s + 1] = 0;
        let e = vz_new(b, GIR_GEP, GIR_T_PTR, p, s, 0, 0);
        return p, e;
    }
    let G = o_ins[p];
    let tv = res(o_ops[G.b + 2]);
    var lo = init;
    var hi = n;
    if is_inst(tv) && (o_ins[tv].op == GIR_SEXT || o_ins[tv].op == GIR_ZEXT) {
        lo = vz_new(b, o_ins[tv].op, o_ins[tv].ty, init, 0, 0, 0);
        o_ins[lo].aux = ivt as! u16;
        hi = vz_new(b, o_ins[tv].op, o_ins[tv].ty, n, 0, 0, 0);
        o_ins[hi].aux = ivt as! u16;
    }
    let s1 = new_run(4);
    o_ops[s1] = o_ops[G.b];
    o_ops[s1 + 1] = o_ops[G.b + 1];
    o_ops[s1 + 2] = lo;
    o_ops[s1 + 3] = o_ops[G.b + 3];
    let st = vz_new(b, GIR_GEP, GIR_T_PTR, res(G.a), s1, 1, 0);
    let s2 = new_run(4);
    o_ops[s2] = o_ops[G.b];
    o_ops[s2 + 1] = o_ops[G.b + 1];
    o_ops[s2 + 2] = hi;
    o_ops[s2 + 3] = o_ops[G.b + 3];
    let en = vz_new(b, GIR_GEP, GIR_T_PTR, res(G.a), s2, 1, 0);
    return st, en;
}
