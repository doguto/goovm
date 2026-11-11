// Allocator-aware lowerings of 16-byte vector operations (milestone E2):
// what the vectorizers (opt_vec.goose) produce, on SSE2 (the x86-64
// baseline). Every function here is reached from the dispatch of cg.goose
// / lowera.goose when vx_kind (ra.goose) returned K_A for the instruction
// through vx_kind_e2 below; other vector operations stay with the legacy
// lowerings (lane by lane in memory). To support more operations (other
// shuffles, compares and selects with masks, SSE4.1/AVX forms), extend
// vx_kind_e2 and add the lowering here.

// Whether vector instruction I (type t, lanes of lb bits, FP if lfp) has a
// lowering here.
fn vx_kind_e2(I: Inst, op: u32, t: u32, lb: u32, lfp: bool) -> bool {
    if op == GIR_MUL { return !lfp && lb == 32; }
    if op == GIR_SHL || op == GIR_LSHR || op == GIR_ASHR {
        if lfp || lb == 8 || op == GIR_ASHR && lb == 64 { return false; }
        let k, c = vsplat_const(I.b);
        return k && c < lb as u64;
    }
    if op == GIR_SHUFFLE { return vshuf_plan(I) != 0; }
    return false;
}

// A constant vector whose lanes are all equal: (ok, the lane value).
fn vsplat_const(v: u32) -> bool, u64 {
    if gir_kind(v) != GIR_V_CONST { return false, 0; }
    let C = M.consts[gir_idx(v)];
    let T = M.types[C.ty];
    if T.kind != TK_VECTOR { return false, 0; }
    let es = M.types[T.elems].size;
    if C.data == GIR_NONE { return true, 0; }
    var x0: u64 = 0;
    for k in 0..T.n {
        var x: u64 = 0;
        for q in 0..es { x |= (M.data[C.data + k * es + q] as u64) << (8 * q); }
        if k == 0 { x0 = x; } else if x != x0 { return false, 0; }
    }
    return true, x0;
}

// <4 x i32> multiplication with SSE2's pmuludq (lanes 0 and 2, then 1 and 3).
fn lower_vmul32(I: Inst, j: u32) {
    let xa = ra_xmm(I.a);
    let xb = ra_xmm(I.b);
    let t1 = ra_xtemp();
    let t2 = ra_xtemp();
    movaps_rr(t1, xa);
    sse_pint(0xF4, t1, xb);         // pmuludq: products of lanes 0, 2
    pshufd(t2, xa, 0xF5);           // lanes 1, 1, 3, 3
    let t3 = ra_xtemp();
    pshufd(t3, xb, 0xF5);
    sse_pint(0xF4, t2, t3);         // products of lanes 1, 3
    pshufd(t1, t1, 0x08);           // the low halves: 0, 2
    pshufd(t2, t2, 0x08);           // 1, 3
    sse_pint(0x62, t1, t2);         // punpckldq: 0, 1, 2, 3
    let xd = ra_xdef(j);
    movaps_rr(xd, t1);
    ra_xset(j, xd);
}

// Shifts of every lane by one constant: psllw/d/q, psrlw/d/q, psraw/d.
fn lower_vshift(I: Inst, j: u32, lb: u32) {
    let k, c = vsplat_const(I.b);
    let xa = ra_xmm(I.a);
    let xd = xdef_from(j, I.a, xa);
    let opc: u32 = if lb == 16 { 0x0F71 } else if lb == 32 { 0x0F72 } else { 0x0F73 };
    let ext: u32 = if I.op == GIR_SHL { 6 } else if I.op == GIR_LSHR { 2 } else { 4 };
    sse_rr(P_66, 0, opc, ext, xd);
    b1(c as! u32);
    ra_xset(j, xd);
}

// Shuffles of 32-bit or 64-bit lanes that one SSE2 instruction does:
// 1 pshufd of a, 2 pshufd of b, 3 shufps a, b (lanes 0-1 from a, 2-3 from b),
// 4 shufps b, a; (64-bit lanes) 5 shufpd a, b, 6 shufpd b, a, 7 pshufd of a,
// 8 pshufd of b; 0 none. The mask is in M.opnds at I.c (GIR_NONE: undefined).
fn vshuf_plan(I: Inst) -> u32 {
    if I.aux != I.ty { return 0; }
    let T = M.types[I.ty];
    let n = T.n;
    let lb = M.types[T.elems].size * 8;
    if n == 4 && lb == 32 {
        var froma = true;
        var fromb = true;
        var lo_a = true;     // lanes 0, 1 from a and 2, 3 from b
        var lo_b = true;     // the other way round
        for k in 0..4 {
            let m = M.opnds[I.c + k];
            if m == GIR_NONE { continue; }
            if m >= 4 { froma = false; } else { fromb = false; }
            if k < 2 { if m >= 4 { lo_a = false; } else { lo_b = false; } }
            else { if m < 4 { lo_a = false; } else { lo_b = false; } }
        }
        if froma { return 1; }
        if fromb { return 2; }
        if lo_a { return 3; }
        if lo_b { return 4; }
        return 0;
    }
    if n == 2 && lb == 64 {
        let m0 = M.opnds[I.c];
        let m1 = M.opnds[I.c + 1];
        let a0 = m0 == GIR_NONE || m0 < 2;
        let a1 = m1 == GIR_NONE || m1 < 2;
        let b0 = m0 == GIR_NONE || m0 >= 2;
        let b1v = m1 == GIR_NONE || m1 >= 2;
        if a0 && a1 { return 7; }
        if b0 && b1v { return 8; }
        if a0 && b1v { return 5; }
        if b0 && a1 { return 6; }
    }
    return 0;
}
fn vshuf_lane(m: u32, k: u32) -> u32 { if m == GIR_NONE { k } else { m & 3 } }
fn lower_vshuf_a(I: Inst, j: u32) {
    let p = vshuf_plan(I);
    let c = I.c;
    if p == 1 || p == 2 {
        let xs = ra_xmm(if p == 1 { I.a } else { I.b });
        var imm: u32 = 0;
        for k0 in 0..4 { let k: u32 = k0 as! u32; imm |= vshuf_lane(M.opnds[c + k], k) << (2 * k); }
        let xd = ra_xdef(j);
        pshufd(xd, xs, imm);
        ra_xset(j, xd);
        return;
    }
    if p == 3 || p == 4 {
        let first = if p == 3 { I.a } else { I.b };
        let second = if p == 3 { I.b } else { I.a };
        let xs2 = ra_xmm(second);
        let xs1 = ra_xmm(first);
        var imm: u32 = 0;
        for k0 in 0..4 { let k: u32 = k0 as! u32; imm |= vshuf_lane(M.opnds[c + k], k) << (2 * k); }
        let xd = xdef_from(j, first, xs1);
        shufps(xd, xs2, imm);
        ra_xset(j, xd);
        return;
    }
    // 64-bit lanes
    let m0 = M.opnds[c];
    let m1 = M.opnds[c + 1];
    let l0: u32 = if m0 == GIR_NONE { 0 } else { m0 & 1 };
    let l1: u32 = if m1 == GIR_NONE { 1 } else { m1 & 1 };
    if p == 7 || p == 8 {
        let xs = ra_xmm(if p == 7 { I.a } else { I.b });
        let xd = ra_xdef(j);
        // pshufd with the 64-bit lanes as pairs of 32-bit ones
        let imm = (2 * l0) | (2 * l0 + 1) << 2 | (2 * l1) << 4 | (2 * l1 + 1) << 6;
        pshufd(xd, xs, imm);
        ra_xset(j, xd);
        return;
    }
    let first = if p == 5 { I.a } else { I.b };
    let second = if p == 5 { I.b } else { I.a };
    let xs2 = ra_xmm(second);
    let xs1 = ra_xmm(first);
    let xd = xdef_from(j, first, xs1);
    sse_rr(P_66, 0, 0x0FC6, xd, xs2);   // shufpd
    b1(l0 | l1 << 1);
    ra_xset(j, xd);
}
