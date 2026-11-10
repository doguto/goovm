// Alias analysis for the middle-end (milestone E2): LLVM's BasicAA and TBAA
// on the OIR (opt.goose), as far as the passes ask.
//
// A pointer is decomposed into a base and a constant byte offset, following
// GEPs (a GEP with variable terms makes the offset unknown). The bases are
// classified: an alloca, a global variable or function, a noalias (restrict)
// parameter, another parameter, or something else (a loaded pointer, a call
// result, a PHI, ...). Two accesses do not alias when
//   - their TBAA nodes are unrelated (GirHeader.tbaa: neither is an ancestor
//     of the other in one type tree),
//   - they have the same base and constant offsets whose byte ranges do not
//     overlap,
//   - their bases are two different identified objects (allocas, globals,
//     noalias parameters), or a parameter and a function-local one (an
//     alloca or a noalias parameter),
//   - one base is an alloca whose address does not escape (only loads,
//     stores, GEPs, memcpy and memset use it, transitively) or a noalias
//     parameter that is not captured, and the other is a different base,
//   - one base is an internal global whose address is never taken in the
//     module (gp_ok) and the other is a different base,
//   - one is a store and the other reads a constant global (read-only data
//     is never written).
// A call writes memory unless it is GIR_IF_CALL_NOWRITE, and never writes a
// non-escaping alloca; it reads memory unless it is GIR_IF_CALL_NOREAD.
//
// aa_prepare() computes the per-function facts (escapes, captures) after the
// function changed; the queries are then O(length of the GEP chains).

var aa_esc: u8[>..] = [];       // per instruction (alloca): its address escapes
var aa_n: i64 = 0;              // o_ins.len when prepared
var aa_args_cap: u8[>..] = [];  // per parameter: a noalias parameter that is captured
var aa_wl: u32[>..] = [];
var aa_tb_depth: u8[>..] = [];  // per TBAA node: depth in its tree (0: not computed)
var aa_tb_n: u32 = 0;
var aa_tb_base: u32 = 0;        // opnds index of the TBAA parents (node k at aa_tb_base + k)

let AB_OTHER: u32 = 0;
let AB_ALLOCA: u32 = 1;
let AB_GLOBAL: u32 = 2;
let AB_NOALIAS: u32 = 3;
let AB_ARG: u32 = 4;

// The TBAA table of the module (opt_module).
fn aa_module_init() {
    aa_tb_n = 0;
    aa_tb_base = 0;
    aa_tb_depth.clear();
    let t = M.header[0].r2;
    if t == 0 || t >= M.opnds.len as! u32 { return; }
    aa_tb_n = M.opnds[t];
    aa_tb_base = t;
    aa_tb_depth.resize(aa_tb_n as i64 + 1, 0);
}
fn aa_tb_parent(k: u32) -> u32 {
    if k == 0 || k > aa_tb_n { return 0; }
    return M.opnds[aa_tb_base + k];
}
fn aa_tb_dep(k: u32) -> u32 {
    if k == 0 || k > aa_tb_n { return 0; }
    if aa_tb_depth[k] != 0 { return aa_tb_depth[k]; }
    var d: u32 = 1;
    var x = aa_tb_parent(k);
    while x != 0 && d < 250 {
        d++;
        x = aa_tb_parent(x);
    }
    aa_tb_depth[k] = d as! u8;
    return d;
}
// Whether accesses with TBAA nodes a and b may alias (0: no information).
fn aa_tbaa(a: u32, b: u32) -> bool {
    if a == 0 || b == 0 || a == b || a > aa_tb_n || b > aa_tb_n { return true; }
    var x = a;
    var y = b;
    var dx = aa_tb_dep(x);
    var dy = aa_tb_dep(y);
    while dx > dy { x = aa_tb_parent(x); dx--; }
    while dy > dx { y = aa_tb_parent(y); dy--; }
    // x and y are at the same depth: an ancestor relation iff they meet here
    if x == y { return true; }
    // different roots: unrelated type systems, conservatively aliasing
    var rx = x;
    while aa_tb_parent(rx) != 0 { rx = aa_tb_parent(rx); }
    var ry = y;
    while aa_tb_parent(ry) != 0 { ry = aa_tb_parent(ry); }
    return rx != ry;
}

// Base and constant offset of pointer p: (base, offset, offset known).
fn aa_decompose(p0: u32) -> u32, i64, bool {
    var p = res(p0);
    var off: i64 = 0;
    var known = true;
    var n = 0;
    while is_inst(p) && n < 32 {
        let I = o_ins[p];
        if I.op != GIR_GEP { break; }
        off += (o_ops[I.b] as u64 | (o_ops[I.b + 1] as u64 << 32)) as! i64;
        if I.c != 0 { known = false; }
        p = res(I.a);
        n++;
    }
    return p, off, known;
}
fn aa_kind(b: u32) -> u32 {
    let k = gir_kind(b);
    if k == GIR_V_INST {
        if o_ins[b].op == GIR_ALLOCA { return AB_ALLOCA; }
        return AB_OTHER;
    }
    if k == GIR_V_GLOBAL {
        if M.globals[gir_idx(b)].kind == G_ALIAS { return AB_OTHER; }
        return AB_GLOBAL;
    }
    if k == GIR_V_ARG {
        let a = gir_idx(b);
        if a < o_f.n_args && M.opnds[o_f.args + 2 * a + 1] & ABI_NOALIAS != 0 { return AB_NOALIAS; }
        return AB_ARG;
    }
    return AB_OTHER;   // (a constant: null, an integer cast to a pointer)
}
// A base no pointer with another base can reach.
fn aa_private(b: u32, k: u32) -> bool {
    if k == AB_ALLOCA { return b < aa_esc.len as! u32 && aa_esc[b] == 0; }
    if k == AB_NOALIAS { let a = gir_idx(b); return a < aa_args_cap.len as! u32 && aa_args_cap[a] == 0; }
    if k == AB_GLOBAL { let g = gir_idx(b); return g < gp_ok.len as! u32 && gp_ok[g] != 0; }
    return false;
}
inline fn aa_identified(k: u32) -> bool { k == AB_ALLOCA || k == AB_GLOBAL || k == AB_NOALIAS }

// Whether [p, p + ps) and [q, q + qs) may overlap (sizes in bytes, 0:
// unknown), with TBAA nodes pt and qt.
fn aa_alias(p: u32, ps: u32, pt: u32, q: u32, qs: u32, qt: u32) -> bool {
    if !aa_tbaa(pt, qt) { return false; }
    let pb, po, pk = aa_decompose(p);
    let qb, qo, qk = aa_decompose(q);
    if pb == qb {
        if !pk || !qk || ps == 0 || qs == 0 { return true; }
        return po < qo + qs as i64 && qo < po + ps as i64;
    }
    let kp = aa_kind(pb);
    let kq = aa_kind(qb);
    if aa_identified(kp) && aa_identified(kq) { return false; }
    if kp == AB_ARG && (kq == AB_ALLOCA || kq == AB_NOALIAS) { return false; }
    if kq == AB_ARG && (kp == AB_ALLOCA || kp == AB_NOALIAS) { return false; }
    if aa_private(pb, kp) || aa_private(qb, kq) { return false; }
    return true;
}
// Whether memory at p is read-only data.
fn aa_const_mem(p: u32) -> bool {
    let b, o, k = aa_decompose(p);
    if gir_kind(b) != GIR_V_GLOBAL { return false; }
    let G = M.globals[gir_idx(b)];
    return G.kind == G_VAR && G.flags & GF_CONST != 0 && G.flags & GF_DEFINED != 0;
}
// Whether call i may write the memory at p.
fn aa_call_mod(i: u32, p: u32) -> bool {
    let I = o_ins[i];
    if I.op == GIR_CALL && I.flags & IF_CALL_NOWRITE != 0 { return false; }
    if aa_const_mem(p) { return false; }
    let b, o, k = aa_decompose(p);
    let kb = aa_kind(b);
    if kb == AB_ALLOCA && aa_private(b, kb) { return false; }
    return true;
}
// Whether call i may read the memory at p.
fn aa_call_ref(i: u32, p: u32) -> bool {
    let I = o_ins[i];
    if I.op == GIR_CALL && I.flags & IF_CALL_NOREAD != 0 { return false; }
    let b, o, k = aa_decompose(p);
    let kb = aa_kind(b);
    if kb == AB_ALLOCA && aa_private(b, kb) { return false; }
    return true;
}

// The access of load or store i: (pointer, size, TBAA node).
fn aa_access(i: u32) -> u32, u32, u32 {
    let I = o_ins[i];
    if I.op == GIR_LOAD { return res(I.a), store_of(I.ty), I.b; }
    if I.op == GIR_STORE { return res(I.b), store_of(I.aux), I.c; }
    if I.op == GIR_MEMCPY || I.op == GIR_MEMSET { return res(I.a), I.c, 0; }
    return NIL, 0, 0;
}

// Whether instruction w (which writes memory) may change [p, p + ps) with
// TBAA node pt.
fn aa_clobbers(w: u32, p: u32, ps: u32, pt: u32) -> bool {
    let W = o_ins[w];
    let op: u32 = W.op;
    if op == GIR_STORE {
        if aa_const_mem(p) { return false; }
        return aa_alias(res(W.b), store_of(W.aux), W.c, p, ps, pt);
    }
    if op == GIR_MEMCPY || op == GIR_MEMSET {
        if aa_const_mem(p) { return false; }
        return aa_alias(res(W.a), W.c, 0, p, ps, pt);
    }
    if op == GIR_CALL { return aa_call_mod(w, p); }
    return true;
}

// Escapes and captures of the function's allocas and noalias parameters.
fn aa_prepare() {
    let n = o_ins.len;
    aa_n = n;
    aa_esc.clear();
    aa_esc.resize(n, 0);
    aa_args_cap.clear();
    aa_args_cap.resize(o_f.n_args, 0);
    let setjmp = o_f.flags & (FN_RETURNS_TWICE | FN_SJLJ) != 0;
    for i0 in 0..n {
        if o_blk[i0] == NIL { continue; }
        let i: u32 = i0 as! u32;
        let I = o_ins[i];
        let op: u32 = I.op;
        if op == GIR_ALLOCA && setjmp { aa_esc[i] = 1; }
        each_slot(i) { s =>
            let v = res(vget(i, s));
            var ok = false;
            if op == GIR_LOAD && s == SLOT_A { ok = true; }
            else if op == GIR_STORE && s == SLOT_B { ok = true; }
            else if op == GIR_GEP { ok = true; }   // (the GEP's own uses are checked)
            else if (op == GIR_MEMCPY || op == GIR_MEMSET) && s < SLOT_C { ok = true; }
            else if op == GIR_ICMP { ok = true; }   // (comparing a pointer does not capture it in a way that matters here)
            if !ok {
                // the base this value points into escapes
                let b, o, k = aa_decompose(v);
                if is_inst(b) && o_ins[b].op == GIR_ALLOCA { aa_esc[b] = 1; }
                if gir_kind(b) == GIR_V_ARG && gir_idx(b) < o_f.n_args { aa_args_cap[gir_idx(b)] = 1; }
            }
        };
        // a GEP with variable terms off an alloca: still private (the access
        // stays inside it or is undefined)
    }
}
