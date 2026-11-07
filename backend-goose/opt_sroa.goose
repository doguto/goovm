// Scalar replacement of aggregates on the OIR (opt.goose): an entry-block
// alloca that is only accessed at constant offsets (loads, stores, GEPs
// with a constant offset, memcpy/memmove/memset of a constant size, inline
// or libc calls) is split into one alloca per slice of bytes, which
// mem2reg then promotes. A slice is the byte range of a typed access; loads
// and stores that overlap must agree on offset and type. Copies are split
// into a load and a store per slice (bytes a copy moves that no typed
// access names get integer slices of their own), memsets into stores of the
// replicated byte.

let SR_MAX_SIZE: u32 = 1024;
let SR_MAX_SLICES: i64 = 64;

var sr_isfn: u8[>..] = [];      // per global: 1 memcpy, 2 memmove, 3 memset
var sr_acc_i: u32[>..] = [];    // accesses of the alloca: instruction, offset, size, type (NIL: copy/memset range)
var sr_acc_o: u32[>..] = [];
var sr_acc_n: u32[>..] = [];
var sr_acc_t: u32[>..] = [];
var sr_off: u32[>..] = [];      // per instruction: offset of an alloca-derived pointer, NIL
var sr_wl: u32[>..] = [];
var sr_sl_o: u32[>..] = [];     // slices: offset, size, type, new alloca
var sr_sl_n: u32[>..] = [];
var sr_sl_t: u32[>..] = [];
var sr_sl_a: u32[>..] = [];

// Which globals are memcpy, memmove, memset (by name).
fn sroa_init() {
    sr_isfn.clear();
    for G in M.globals {
        var k: u8 = 0;
        if G.kind == G_FUNC && G.flags & GF_DEFINED == 0 {
            let nm = M.strtab[G.name..G.name + G.name_len];
            if nm == "memcpy" { k = 1; }
            else if nm == "memmove" { k = 2; }
            else if nm == "memset" { k = 3; }
        }
        sr_isfn.push(k);
    }
}
// The library function kind of call I (1 memcpy, 2 memmove, 3 memset), its
// constant length; 0 if not such a call with a constant length.
fn sr_libcall(I: Inst) -> u32, u64 {
    if I.op != GIR_CALL || I.c != 3 || gir_kind(I.a) != GIR_V_GLOBAL { return 0, 0; }
    let k: u32 = sr_isfn[gir_idx(I.a)];
    if k == 0 { return 0, 0; }
    let kn, n = ci(res(o_ops[I.b + 4]));
    if !kn { return 0, 0; }
    return k, n;
}

// Splits the allocas that can be split (build_uses first). Returns whether
// any was.
fn sroa() -> bool {
    var any = false;
    var i = b_first[0];
    while i != NIL {
        let nx = o_nxt[i];
        if o_ins[i].op == GIR_ALLOCA && o_ins[i].a <= SR_MAX_SIZE && o_ins[i].a != 0 {
            if sr_off.len < o_ins.len { sr_off.resize(o_ins.len, NIL); }
            if sroa_one(i) {
                any = true;
                // (the use lists of the other allocas changed)
                o_fwd_dirty = true;
                resolve_all();
                build_uses();
            }
        }
        i = nx;
    }
    return any;
}

// The access of one use u (an instruction using pointer p = alloca + off).
// False if the use is not understood.
fn sr_use(u: u32, p: u32, off: u32) -> bool {
    let U = o_ins[u];
    let op: u32 = U.op;
    if op == GIR_LOAD {
        if U.flags & (IF_VOLATILE | IF_ORD_MASK) != 0 || !promotable_type(U.ty) { return false; }
        sr_acc(u, off, store_of(U.ty), U.ty);
        return true;
    }
    if op == GIR_STORE {
        if res(U.b) != p || res(U.a) == p { return false; }
        if U.flags & (IF_VOLATILE | IF_ORD_MASK) != 0 || !promotable_type(U.aux) { return false; }
        sr_acc(u, off, store_of(U.aux), U.aux);
        return true;
    }
    if op == GIR_GEP {
        if res(U.a) != p || U.c != 0 || o_ops[U.b + 1] != 0 { return false; }
        let d = o_ops[U.b];
        if d > 0x7FFFFFFF { return false; }   // (negative)
        if sr_off.len <= u { sr_off.resize(o_ins.len, NIL); }
        sr_off[u] = off + d;
        sr_wl.push(u);
        return true;
    }
    if op == GIR_MEMCPY || op == GIR_MEMSET {
        if op == GIR_MEMSET && res(U.a) != p { return false; }
        if op == GIR_MEMCPY && res(U.a) == p && res(U.b) == p { return false; }
        if op == GIR_MEMSET && !ci_ok(res(U.b)) { return false; }
        sr_acc(u, off, U.c, NIL);
        return true;
    }
    let k, len = sr_libcall(U);
    if k != 0 && nuses(u) == 0 && len <= SR_MAX_SIZE as u64 {
        let d = res(o_ops[U.b]);
        let s = res(o_ops[U.b + 2]);
        if k == 3 {
            if d != p || s == p || !ci_ok(s) { return false; }
        } else {
            if d == p && s == p { return false; }
            if d != p && s != p { return false; }
        }
        sr_acc(u, off, len as! u32, NIL);
        return true;
    }
    return false;
}
fn ci_ok(v: u32) -> bool {
    let k, x = ci(v);
    return k;
}
fn sr_acc(u: u32, off: u32, n: u32, t: u32) {
    sr_acc_i.push(u);
    sr_acc_o.push(off);
    sr_acc_n.push(n);
    sr_acc_t.push(t);
}

fn sroa_one(a: u32) -> bool {
    let size = o_ins[a].a;
    sr_acc_i.clear();
    sr_acc_o.clear();
    sr_acc_n.clear();
    sr_acc_t.clear();
    sr_wl.clear();
    sr_off[a] = 0;
    sr_wl.push(a);
    var k: i64 = 0;
    var gep = false;
    while k < sr_wl.len {
        let p = sr_wl[k];
        k++;
        if p != a { gep = true; }
        for q in u_start[p]..u_start[p + 1] {
            let u = u_list[q];
            if o_blk[u] == NIL { continue; }
            if !sr_use(u, p, sr_off[p]) { return false; }
        }
    }
    // every access once; a stored value or the other side of a copy is not
    // the alloca's own address
    for q in 0..sr_acc_i.len {
        let u = sr_acc_i[q];
        for q2 in 0..q { if sr_acc_i[q2] == u { return false; } }
        let U = o_ins[u];
        if U.op == GIR_STORE && sr_derived(res(U.a)) { return false; }
        if U.op == GIR_MEMCPY && sr_derived(res(U.a)) == sr_derived(res(U.b)) { return false; }
        if U.op == GIR_CALL {
            let k, len = sr_libcall(U);
            let dd = sr_derived(res(o_ops[U.b]));
            let sd = sr_derived(res(o_ops[U.b + 2]));
            if k == 3 && (!dd || sd) { return false; }
            if k != 3 && dd == sd { return false; }
        }
        if U.op == GIR_MEMSET && sr_derived(res(U.b)) { return false; }
    }
    // only worth it when the alloca is not already a plain scalar
    var typed = 0;
    var ranges = 0;
    for t in sr_acc_t { if t == NIL { ranges++; } else { typed++; } }
    if !gep && ranges == 0 { return false; }   // (mem2reg's case, or not promotable anyway)
    for q in 0..sr_acc_i.len {
        if sr_acc_o[q] + sr_acc_n[q] > size { return false; }
    }
    // slices: the typed accesses (overlaps must be identical)
    sr_sl_o.clear();
    sr_sl_n.clear();
    sr_sl_t.clear();
    sr_sl_a.clear();
    for q in 0..sr_acc_i.len {
        let t = sr_acc_t[q];
        if t == NIL { continue; }
        let o = sr_acc_o[q];
        let n = sr_acc_n[q];
        var found = false;
        for s in 0..sr_sl_o.len {
            let so = sr_sl_o[s];
            let sn = sr_sl_n[s];
            if o + n <= so || so + sn <= o { continue; }
            if so != o || sr_sl_t[s] != t { return false; }
            found = true;
        }
        if !found {
            if sr_sl_o.len >= SR_MAX_SLICES { return false; }
            sr_sl_o.push(o);
            sr_sl_n.push(n);
            sr_sl_t.push(t);
            sr_sl_a.push(NIL);
        }
    }
    // the bytes copies and memsets cover that no typed access names
    for q in 0..sr_acc_i.len {
        if sr_acc_t[q] != NIL { continue; }
        let o = sr_acc_o[q];
        let e = o + sr_acc_n[q];
        // a range must not cut a slice
        for s in 0..sr_sl_o.len {
            let so = sr_sl_o[s];
            let se = so + sr_sl_n[s];
            if se <= o || e <= so { continue; }
            if so < o || se > e { return false; }
        }
        var p = o;
        while p < e {
            var covered = false;
            for s in 0..sr_sl_o.len {
                if sr_sl_o[s] <= p && p < sr_sl_o[s] + sr_sl_n[s] {
                    p = sr_sl_o[s] + sr_sl_n[s];
                    covered = true;
                    break;
                }
            }
            if covered { continue; }
            // the gap up to the next slice, as integers of 8/4/2/1 bytes
            var g = e;
            for s in 0..sr_sl_o.len {
                if sr_sl_o[s] > p && sr_sl_o[s] < g { g = sr_sl_o[s]; }
            }
            while p < g {
                var w: u32 = 8;
                while w > g - p || p % w != 0 { w = w / 2; }
                if sr_sl_o.len >= SR_MAX_SLICES { return false; }
                sr_sl_o.push(p);
                sr_sl_n.push(w);
                sr_sl_t.push(if w == 8 { GIR_T_I64 } else if w == 4 { GIR_T_I32 } else if w == 2 { GIR_T_I16 } else { GIR_T_I8 });
                sr_sl_a.push(NIL);
                p += w;
            }
        }
    }
    if sr_sl_o.len == 0 { return false; }
    // a memset of a non-zero byte only into integer and FP slices
    for q in 0..sr_acc_i.len {
        if sr_acc_t[q] != NIL { continue; }
        let U = o_ins[sr_acc_i[q]];
        var bv: u32 = NIL;
        if U.op == GIR_MEMSET { bv = res(U.b); }
        else if U.op == GIR_CALL {
            let k, len = sr_libcall(U);
            if k == 3 { bv = res(o_ops[U.b + 2]); }
        }
        if bv == NIL { continue; }
        let kb, b8 = ci(bv);
        if b8 & 0xFF == 0 { continue; }
        for s in 0..sr_sl_o.len {
            if sr_sl_o[s] < sr_acc_o[q] || sr_sl_o[s] + sr_sl_n[s] > sr_acc_o[q] + sr_acc_n[q] { continue; }
            let c = cls_of(sr_sl_t[s]);
            if c != C_INT && c != C_FP { return false; }
        }
    }
    // the new allocas
    let dbg = o_ins[a].dbg;
    for s in 0..sr_sl_o.len {
        let t = sr_sl_t[s];
        let na = new_inst(Inst { op: GIR_ALLOCA as! u8, sub: 0, flags: 0, ty: GIR_T_PTR, aux: 0, a: sr_sl_n[s],
                                 b: M.types[t].align, c: 0, dbg: dbg });
        link_after(a, na);
        sr_sl_a[s] = na;
    }
    // rewrite the accesses
    for q in 0..sr_acc_i.len {
        let u = sr_acc_i[q];
        let o = sr_acc_o[q];
        let t = sr_acc_t[q];
        if t != NIL {
            let s = sr_slice_at(o);
            if o_ins[u].op == GIR_LOAD { o_ins[u].a = sr_sl_a[s]; } else { o_ins[u].b = sr_sl_a[s]; }
            continue;
        }
        sr_split_copy(u, o, sr_acc_n[q]);
    }
    return true;
}
fn sr_slice_at(o: u32) -> u32 {
    for s in 0..sr_sl_o.len { if sr_sl_o[s] == o { return s as! u32; } }
    assert(false);
    return 0;
}
// A pointer to p + d (a GEP before `at`, or p itself).
fn sr_ptr(at: u32, p: u32, d: u32) -> u32 {
    if d == 0 { return p; }
    let s = new_run(2);
    o_ops[s] = d;
    o_ops[s + 1] = 0;
    let g = new_inst(Inst { op: GIR_GEP as! u8, sub: 0, flags: 0, ty: GIR_T_PTR, aux: 0, a: p, b: s, c: 0,
                            dbg: o_ins[at].dbg });
    link_before(at, g);
    return g;
}
// Copy or memset u over [o, o + n) of the alloca: one load/store per slice.
fn sr_split_copy(u: u32, o: u32, n: u32) {
    let U = o_ins[u];
    var dst: u32 = 0;
    var src: u32 = 0;
    var bytev: u32 = NIL;
    if U.op == GIR_MEMCPY {
        dst = res(U.a);
        src = res(U.b);
    } else if U.op == GIR_MEMSET {
        dst = res(U.a);
        bytev = res(U.b);
    } else {
        dst = res(o_ops[U.b]);
        let k, len = sr_libcall(U);
        if k == 3 { bytev = res(o_ops[U.b + 2]); } else { src = res(o_ops[U.b + 2]); }
    }
    let into = bytev != NIL || sr_derived(dst);
    for s in 0..sr_sl_o.len {
        let so = sr_sl_o[s];
        if so < o || so + sr_sl_n[s] > o + n { continue; }
        let t = sr_sl_t[s];
        let d = so - o;
        if bytev != NIL {
            let kb, b8 = ci(bytev);
            let c = sr_splat(t, b8 & 0xFF);
            let st = new_inst(Inst { op: GIR_STORE as! u8, sub: 0, flags: 0, ty: GIR_T_VOID, aux: t as! u16, a: c,
                                     b: sr_sl_a[s], c: 0, dbg: U.dbg });
            link_before(u, st);
        } else if into {
            // into the alloca from src
            let ld = new_inst(Inst { op: GIR_LOAD as! u8, sub: 0, flags: 0, ty: t as! u16, aux: 0, a: sr_ptr(u, src, d),
                                     b: 0, c: 0, dbg: U.dbg });
            link_before(u, ld);
            let st = new_inst(Inst { op: GIR_STORE as! u8, sub: 0, flags: 0, ty: GIR_T_VOID, aux: t as! u16, a: ld,
                                     b: sr_sl_a[s], c: 0, dbg: U.dbg });
            link_before(u, st);
        } else {
            // out of the alloca into dst
            let ld = new_inst(Inst { op: GIR_LOAD as! u8, sub: 0, flags: 0, ty: t as! u16, aux: 0, a: sr_sl_a[s],
                                     b: 0, c: 0, dbg: U.dbg });
            link_before(u, ld);
            let st = new_inst(Inst { op: GIR_STORE as! u8, sub: 0, flags: 0, ty: GIR_T_VOID, aux: t as! u16, a: ld,
                                     b: sr_ptr(u, dst, d), c: 0, dbg: U.dbg });
            link_before(u, st);
        }
    }
    unlink(u);
}
// Whether pointer p was reached from the alloca being split (in the worklist).
fn sr_derived(p: u32) -> bool {
    for x in sr_wl { if x == p { return true; } }
    return false;
}
// The constant of type t whose bytes are all b.
fn sr_splat(t: u32, b: u64) -> u32 {
    var x: u64 = 0;
    for k in 0..store_of(t) { x = (x << 8) | b; }
    if cls_of(t) == C_INT { return int_const(t, x); }
    // FP or vector: the same bits
    if x == 0 { return undef_of(t); }
    if cls_of(t) == C_FP { return mk_const(t, x, 0); }
    return undef_of(t);   // (non-zero vector splats: not split, see sr_use)
}
