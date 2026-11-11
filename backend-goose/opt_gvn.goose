// Dominator-based common-subexpression elimination with load and store
// forwarding on the OIR (opt.goose), in the manner of LLVM's EarlyCSE: the
// dominator tree is walked in pre-order with a scoped hash table of the
// pure instructions seen on the path from the entry; an instruction equal
// to one in the table is replaced by it. Loads are keyed by (address, type)
// and valid while no write since may have changed the memory (E2): the
// memory writes of the path are logged, and the writes logged after an
// entry are checked against it with the alias analysis (opt_aa.goose:
// TBAA, bases and offsets, escapes, calls that write no memory). A block
// entered from several predecessors starts a new epoch, in which the
// entries of before are not valid, except for a private alloca all of whose
// writes are in one block that dominates the load. Calls that read no
// memory and write none are CSE'd like pure instructions.
//
// (E2) Conditions: a block entered by one edge of a conditional branch
// knows the branch's condition there (and in the blocks it dominates); a
// compare of the same operands that the known compares imply is replaced by
// its constant (LLVM's isImpliedCondition: x == y implies !(x != y), x < 5
// implies x < 7, ...), and so is a branch on a known condition.

var gv_tab: u32[>..] = [];      // open addressing: instruction id + 1, 0 = empty
var gv_undo: u32[>..] = [];     // slots filled, in order (scope exit clears them in reverse)
var gv_lt: u32[>..] = [];       // loads: slot -> id + 1 of the load or store that holds the value
var gv_lval: u32[>..] = [];     // per load-table entry (by instruction id): the value
var gv_lpos: u32[>..] = [];     // per entry: the length of the write log when it was made
var gv_lep: u32[>..] = [];      // per entry: the epoch (gv_ep) it was made in
var gv_wlog: u32[>..] = [];     // the memory writes on the path from the entry (dominator tree)
let GV_SCAN: i64 = 128;         // writes checked per lookup at most
var gv_lundo: u32[>..] = [];    // (slot, previous content) pairs
var gv_ep: u32 = 0;             // epoch of the alloca generations: new at a merge point
var gv_bep: u32[>..] = [];      // per block: the epoch at its end
var gv_cnt: u32 = 0;            // epoch counter (monotonic: a number is never reused)
var gv_base: u32[>..] = [];     // per instruction: the alloca its address is based on, NIL
var gv_sblk: u32[>..] = [];     // per alloca: the one block that writes it, NIL none, GV_MANY several
var gv_cur: u32 = 0;            // the block being walked
let GV_MANY: u32 = 0xFFFFFFFE;
var gv_changed = false;

// ------------------------------------------------------------ alias info

// gv_base for pointer-valued instructions (GEP chains off allocas) and
// gv_sblk, the one block that writes each alloca (aa_prepare first).
fn gv_alias() {
    let n = o_ins.len;
    gv_base.clear();
    gv_base.resize(n, NIL);
    gv_sblk.clear();
    gv_sblk.resize(n, NIL);
    // allocas and GEPs of them (operands are defined before use in RPO, except
    // through PHIs, which are not followed)
    for b in rpo {
        var i = b_first[b];
        while i != NIL {
            let I = o_ins[i];
            if I.op == GIR_ALLOCA {
                gv_base[i] = i;
            } else if I.op == GIR_GEP && is_inst(res(I.a)) {
                gv_base[i] = gv_base[res(I.a)];
            }
            i = o_nxt[i];
        }
    }
    for b in rpo {
        var i = b_first[b];
        while i != NIL {
            let I = o_ins[i];
            let op: u32 = I.op;
            var p: u32 = NIL;
            if op == GIR_STORE { p = res(I.b); }
            else if op == GIR_MEMCPY || op == GIR_MEMSET { p = res(I.a); }
            if p != NIL && is_inst(p) && gv_base[p] != NIL {
                let a = gv_base[p];
                gv_sblk[a] = if gv_sblk[a] == NIL || gv_sblk[a] == b { b } else { GV_MANY };
            }
            i = o_nxt[i];
        }
    }
}
// The private (non-escaping) alloca p is based on, or NIL.
fn gv_ne_base(p: u32) -> u32 {
    if !is_inst(p) { return NIL; }
    let a = gv_base[p];
    if a != NIL && aa_esc[a] == 0 { return a; }
    return NIL;
}
// Records load/store i (address p) as the holder of value v.
fn gv_lput(h: u64, i: u32, p: u32, v: u32) {
    gv_lundo.push(h as! u32);
    gv_lundo.push(gv_lt[h]);
    gv_lt[h] = i + 1;
    gv_lval[i] = v;
    gv_lpos[i] = gv_wlog.len as! u32;
    gv_lep[i] = gv_ep;
}
// The value load/store entry e (id + 1) holds now for an access of ps
// bytes at p with TBAA node pt, or NIL. Across a merge point (another
// epoch) only a private alloca all of whose writes are in one block that
// dominates this one keeps its entries: a path from the writing block to
// here passes the entry's block (a dominator, after that block's writes)
// again, and the writes of the dominator path since are in the log.
fn gv_lget(e: u32, p: u32, ps: u32, pt: u32) -> u32 {
    if e == 0 { return NIL; }
    let x = e - 1;
    if gv_lep[x] != gv_ep {
        let a = gv_ne_base(p);
        if a == NIL { return NIL; }
        let w = gv_sblk[a];
        if w == NIL || w == GV_MANY || !dominates(w, gv_cur) { return NIL; }
    }
    let s: i64 = gv_lpos[x];
    if gv_wlog.len - s > GV_SCAN { return NIL; }
    for k in s..gv_wlog.len {
        // (bit 31: a write of the loop whose header this walk passed, maybe
        // of an earlier iteration)
        let w = gv_wlog[k];
        aa_cross = w & 0x80000000 != 0;
        let c = aa_clobbers(w & 0x7FFFFFFF, p, ps, pt);
        aa_cross = false;
        if c { return NIL; }
    }
    return gv_lval[x];
}
fn gv_bump() -> u32 {
    gv_cnt++;
    return gv_cnt;
}
// The instruction writes memory: it goes to the write log.
fn gv_clobber(i: u32) {
    gv_wlog.push(i);
}
fn writes_mem(I: Inst) -> bool {
    let op: u32 = I.op;
    if op == GIR_CALL { return I.flags & IF_CALL_NOWRITE == 0; }
    if op == GIR_STORE || op == GIR_MEMCPY || op == GIR_MEMSET || op == GIR_VASTART { return true; }
    if op == GIR_CMPXCHG || op == GIR_ATOMICRMW || op == GIR_FENCE || op == GIR_ASM { return true; }
    if op == GIR_SJLJ_SETJMP || op == GIR_SJLJ_LONGJMP || op == GIR_STACKRESTORE || op == GIR_LANDINGPAD { return true; }
    if op == GIR_LOAD { return I.flags & (IF_VOLATILE | IF_ORD_MASK) != 0; }
    if op == GIR_A64 { return a64_effect(I.sub); }
    return false;
}

// ------------------------------------------------------------ the table

// Whether instruction I may be replaced by an equal one that dominates it.
fn cse_op(I: Inst) -> bool {
    let op: u32 = I.op;
    if op >= GIR_ADD && op <= GIR_BITCAST { return true; }
    if op == GIR_GEP { return true; }
    if op >= GIR_FADD && op <= GIR_INSERTELT { return true; }
    if op >= GIR_CTLZ && op <= GIR_ISFPCLASS { return true; }
    // a call of a function that neither reads nor writes memory and returns
    if op == GIR_CALL { return I.flags & (IF_CALL_NOWRITE | IF_CALL_NOREAD | IF_CALL_PURE | IF_INVOKE)
                                == (IF_CALL_NOWRITE | IF_CALL_NOREAD | IF_CALL_PURE); }
    return op == GIR_X86 || op == GIR_TLSADDR || op == GIR_BLOCKADDR;
}
inline fn commutes(op: u32) -> bool {
    op == GIR_ADD || op == GIR_MUL || op == GIR_AND || op == GIR_OR || op == GIR_XOR || op == GIR_FADD || op == GIR_FMUL
}
inline fn hmix(h: u64, x: u64) -> u64 {
    let y = (h ^ x) * 0x9E3779B97F4A7C15;
    return y ^ (y >> 31);
}
// Operands a, b of i in canonical order (commutative operations).
fn gv_ab(i: u32) -> u32, u32 {
    let I = o_ins[i];
    let m: u32 = OP_VAL[I.op];
    let a = if m & OV_A != 0 { res(I.a) } else { I.a };
    var b = if m & OV_B != 0 { res(I.b) } else { I.b };
    if I.op == GIR_GEP || I.op == GIR_CALL { b = 0; }   // (the run: compared word by word)
    if commutes(I.op) && b < a { return b, a; }
    return a, b;
}
fn gv_hash(i: u32) -> u64 {
    let I = o_ins[i];
    let m: u32 = OP_VAL[I.op];
    let a, b = gv_ab(i);
    let c = if m & OV_C != 0 { res(I.c) } else { I.c };
    var h = hmix(I.op as u64 | (I.sub as u64 << 8) | (I.ty as u64 << 16) | (I.aux as u64 << 32), a as u64);
    h = hmix(h, b as u64 | (c as u64 << 32));
    if I.op == GIR_GEP {
        for k in 0..2 + 2 * I.c {
            let w = o_ops[I.b + k];
            h = hmix(h, (if k >= 2 && k % 2 == 0 { res(w) } else { w }) as u64);
        }
    } else if I.op == GIR_CALL {
        for k in 0..2 * I.c {
            let w = o_ops[I.b + k];
            h = hmix(h, (if k % 2 == 0 { res(w) } else { w }) as u64);
        }
    }
    return h;
}
fn gv_equal(i: u32, j: u32) -> bool {
    let I = o_ins[i];
    let J = o_ins[j];
    if I.op != J.op || I.sub != J.sub || I.ty != J.ty || I.aux != J.aux { return false; }
    if (I.flags ^ J.flags) & (IF_VOLATILE | IF_ORD_MASK) != 0 { return false; }
    let a1, b1 = gv_ab(i);
    let a2, b2 = gv_ab(j);
    if a1 != a2 || b1 != b2 { return false; }
    let m: u32 = OP_VAL[I.op];
    let c1 = if m & OV_C != 0 { res(I.c) } else { I.c };
    let c2 = if m & OV_C != 0 { res(J.c) } else { J.c };
    if I.op == GIR_GEP {
        if I.c != J.c { return false; }
        for k in 0..2 + 2 * I.c {
            var x = o_ops[I.b + k];
            var y = o_ops[J.b + k];
            if k >= 2 && k % 2 == 0 {
                x = res(x);
                y = res(y);
            }
            if x != y { return false; }
        }
        return true;
    }
    if I.op == GIR_CALL {
        if I.c != J.c || I.flags != J.flags { return false; }
        for k in 0..2 * I.c {
            var x = o_ops[I.b + k];
            var y = o_ops[J.b + k];
            if k % 2 == 0 {
                x = res(x);
                y = res(y);
            }
            if x != y { return false; }
        }
        return true;
    }
    return c1 == c2;
}
fn gv_grow() {
    var n: i64 = 64;
    while n < 2 * o_ins.len { n *= 2; }
    gv_tab.clear();
    gv_tab.resize(n, 0);
    gv_lt.clear();
    gv_lt.resize(n, 0);
}
// The equal instruction in the table, or NIL (then i is added).
fn gv_find_add(i: u32) -> u32 {
    let mask: u64 = (gv_tab.len - 1) as! u64;
    var h = gv_hash(i) & mask;
    loop {
        let e = gv_tab[h];
        if e == 0 { break; }
        if gv_equal(i, e - 1) { return e - 1; }
        h = (h + 1) & mask;
    }
    gv_tab[h] = i + 1;
    gv_undo.push(h as! u32);
    return NIL;
}
// Loads: key (address, type) of load/store i.
fn gv_lkey(i: u32) -> u32, u32 {
    let I = o_ins[i];
    if I.op == GIR_LOAD { return res(I.a), I.ty; }
    return res(I.b), I.aux;
}
fn gv_lslot(p: u32, t: u32) -> u64 {
    let mask: u64 = (gv_lt.len - 1) as! u64;
    var h = hmix(p as u64, t as u64 * 0x51) & mask;
    loop {
        let e = gv_lt[h];
        if e == 0 { return h; }
        let ep, et = gv_lkey(e - 1);
        if ep == p && et == t { return h; }
        h = (h + 1) & mask;
    }
    return h;
}

// ------------------------------------------------------------ the walk

fn gvn() -> bool {
    gv_changed = false;
    resolve_all();
    gv_grow();
    aa_prepare();
    aa_cross = false;
    gv_alias();
    let n = o_ins.len;
    gv_lval.clear();
    gv_lval.resize(n, NIL);
    gv_lpos.clear();
    gv_lpos.resize(n, 0);
    gv_lep.clear();
    gv_lep.resize(n, 0);
    gv_bep.clear();
    gv_bep.resize(cfg_nb, 0);
    gv_undo.clear();
    gv_lundo.clear();
    gv_wlog.clear();
    gv_fc.clear();
    gv_fv.clear();
    gv_fpos.clear();
    gv_fpos.resize(cfg_nb, 0);
    gv_cnt = 1;
    gv_ep = 1;
    tmp_stack.clear();
    tmp_stack.push(0);
    tmp_pos.clear();
    tmp_pos.resize(3 * cfg_nb, 0);
    while tmp_stack.len != 0 {
        let e = tmp_stack.pop();
        if e & 0x80000000 != 0 {
            let b = e & 0x7FFFFFFF;
            let m1 = tmp_pos[3 * b];
            while gv_undo.len > m1 { gv_tab[gv_undo.pop()] = 0; }
            let m2 = tmp_pos[3 * b + 1];
            while gv_lundo.len > m2 {
                let old = gv_lundo.pop();
                let h = gv_lundo.pop();
                gv_lt[h] = old;
            }
            let m3: i64 = tmp_pos[3 * b + 2];
            while gv_wlog.len > m3 { gv_wlog.pop(); }
            let m4: i64 = gv_fpos[b];
            while gv_fc.len > m4 {
                gv_fc.pop();
                gv_fv.pop();
            }
            continue;
        }
        let b = e;
        tmp_pos[3 * b] = gv_undo.len as! u32;
        tmp_pos[3 * b + 1] = gv_lundo.len as! u32;
        tmp_pos[3 * b + 2] = gv_wlog.len as! u32;
        gv_fpos[b] = gv_fc.len as! u32;
        // the memory state at entry: the dominator's at its end if it is the
        // only predecessor; at a merge point, the dominator's state with the
        // writes of the blocks between it and here (a loop's body, the arms
        // of an if) added to the log; a new epoch if they are too many
        let np = p_start[b + 1] - p_start[b];
        if b != 0 && np == 1 && p_list[p_start[b]] == idom[b] {
            gv_ep = gv_bep[idom[b]];
            gv_note_edge(p_list[p_start[b]], b);
        } else if b != 0 {
            if gv_region_writes(b) { gv_ep = gv_bep[idom[b]]; } else { gv_ep = gv_bump(); }
        }
        gv_block(b);
        gv_bep[b] = gv_ep;
        tmp_stack.push(b | 0x80000000);
        var c = dt_first[b];
        while c != NIL {
            tmp_stack.push(c);
            c = dt_next[c];
        }
    }
    aa_cross = true;
    return gv_changed;
}

// The blocks from which merge block b is reached without passing its
// immediate dominator: their memory writes go to the write log (false: too
// many, the log is left as it was).
var gv_rmark: u32[>..] = [];
var gv_rep: u32 = 0;
var gv_rwl: u32[>..] = [];
let GV_RBLOCKS: i64 = 256;
let GV_RWRITES: i64 = 256;
fn gv_region_writes(b: u32) -> bool {
    let d = idom[b];
    if d == NIL { return false; }
    if gv_rmark.len < cfg_nb { gv_rmark.resize(cfg_nb, 0); }
    gv_rep++;
    let ep = gv_rep;
    gv_rwl.clear();
    let w0 = gv_wlog.len;
    var nblk: i64 = 0;
    // (a loop header: the region holds the loop's body, earlier iterations)
    var cross: u32 = 0;
    for k in p_start[b]..p_start[b + 1] {
        if rpo_num[p_list[k]] != NIL && dominates(b, p_list[k]) { cross = 0x80000000; }
    }
    for k in p_start[b]..p_start[b + 1] {
        let p = p_list[k];
        if p == d || rpo_num[p] == NIL || gv_rmark[p] == ep { continue; }
        gv_rmark[p] = ep;
        gv_rwl.push(p);
    }
    while gv_rwl.len != 0 {
        let x = gv_rwl.pop();
        nblk++;
        if nblk > GV_RBLOCKS { break; }
        var i = b_first[x];
        while i != NIL {
            if writes_mem(o_ins[i]) { gv_wlog.push(i | cross); }
            i = o_nxt[i];
        }
        if gv_wlog.len - w0 > GV_RWRITES { break; }
        for k in p_start[x]..p_start[x + 1] {
            let p = p_list[k];
            if p == d || rpo_num[p] == NIL || gv_rmark[p] == ep { continue; }
            gv_rmark[p] = ep;
            gv_rwl.push(p);
        }
    }
    if nblk > GV_RBLOCKS || gv_wlog.len - w0 > GV_RWRITES {
        while gv_wlog.len > w0 { gv_wlog.pop(); }
        return false;
    }
    return true;
}

// ---------------------------------------------------------- conditions
var gv_fc: u32[>..] = [];       // known conditions on the dominator path: the condition
var gv_fv: u8[>..] = [];        //   and its value
var gv_fpos: u32[>..] = [];     // per block: gv_fc.len at its entry
let GV_MAXF: i64 = 64;
// Block b is entered only from p: p's branch condition is known in b.
fn gv_note_edge(p: u32, b: u32) {
    let t = b_last[p];
    if t == NIL || gv_fc.len >= GV_MAXF { return; }
    let T = o_ins[t];
    if T.op != GIR_CONDBR || T.b == T.c { return; }
    let c = res(T.a);
    if !is_inst(c) { return; }
    gv_fc.push(c);
    gv_fv.push(if T.b == b { 1 } else { 0 });
    // (not x) known: x known the other way
    let C = o_ins[c];
    if C.op == GIR_XOR && C.ty == GIR_T_I1 && gv_fc.len < GV_MAXF {
        let k, v = ci(res(C.b));
        if k && v == 1 && is_inst(res(C.a)) {
            gv_fc.push(res(C.a));
            gv_fv.push(if T.b == b { 0 } else { 1 });
        }
    }
}
// Integer compares as sets of outcomes: domain (0 eq/ne, 1 signed, 2
// unsigned) and a mask of lt (4), eq (2), gt (1).
fn gv_pred_set(p: u32) -> u32, u32 {
    if p == GIR_EQ { return 0, 2; }
    if p == GIR_NE { return 0, 5; }
    if p == GIR_SLT { return 1, 4; }
    if p == GIR_SLE { return 1, 6; }
    if p == GIR_SGT { return 1, 1; }
    if p == GIR_SGE { return 1, 3; }
    if p == GIR_ULT { return 2, 4; }
    if p == GIR_ULE { return 2, 6; }
    if p == GIR_UGT { return 2, 1; }
    return 2, 3;   // uge
}
// The range [lo, hi] (in the order of domain d: signed or unsigned, as
// biased u64) where x pred c holds, for a constant c; ok false for ne.
fn gv_range(p: u32, d: u32, c: u64, bits: u32) -> bool, u64, u64 {
    let m = wmask(bits);
    let bias: u64 = if d == 1 { (1 as u64) << (bits - 1) } else { 0 };
    let x = (c + bias) & m;   // c in unsigned order
    if p == GIR_EQ { return true, x, x; }
    if p == GIR_NE { return false, 0, 0; }
    let ds, mk = gv_pred_set(p);
    if mk == 4 { if x == 0 { return true, 1, 0; } return true, 0, x - 1; }
    if mk == 6 { return true, 0, x; }
    if mk == 1 { if x == m { return true, 1, 0; } return true, x + 1, m; }
    return true, x, m;
}
// An FP predicate swapped (x pred y == y swapped x): the LLVM numbering is a
// mask of eq (1), gt (2), lt (4), unordered (8).
inline fn fswap(p: u32) -> u32 { (p & 9) | ((p & 2) << 1) | ((p & 4) >> 1) }
// Whether FP compare i is decided by the known conditions.
fn gv_implied_f(i: u32) -> bool, bool {
    let I = o_ins[i];
    let a = res(I.a);
    let b = res(I.b);
    // the outcomes the known compares of a and b leave
    var m: u32 = 15;
    var k: i64 = gv_fc.len - 1;
    while k >= 0 {
        let c = gv_fc[k];
        let fv = gv_fv[k] != 0;
        k--;
        if c == i { return true, fv; }
        let C = o_ins[c];
        if C.op != GIR_FCMP || C.aux != I.aux { continue; }
        var fp: u32 = C.sub;
        if res(C.a) == b && res(C.b) == a { fp = fswap(fp); }
        else if res(C.a) != a || res(C.b) != b { continue; }
        m &= if fv { fp } else { 15 & ~fp };
    }
    let qm: u32 = I.sub;
    if m == 15 { return false, false; }
    if m & ~qm == 0 { return true, true; }
    if m & qm == 0 { return true, false; }
    return false, false;
}
// Whether compare i (x pred y) is decided by the known conditions: (known, value).
fn gv_implied(i: u32) -> bool, bool {
    let I = o_ins[i];
    if I.op == GIR_FCMP { return gv_implied_f(i); }
    if !int_ty(I.aux) && I.aux != GIR_T_PTR { return false, false; }
    let bits: u32 = if I.aux == GIR_T_PTR { 64 } else { bits_of(I.aux) };
    if bits > 64 { return false, false; }
    let a = res(I.a);
    let b = res(I.b);
    let qd0, qm0 = gv_pred_set(I.sub);
    var acc: u32 = 7;       // outcomes left for (a, b) in domain dom
    var dom: u32 = qd0;     // (0 until a signed or unsigned fact or query fixes it)
    var k: i64 = gv_fc.len - 1;
    while k >= 0 {
        let c = gv_fc[k];
        let fv = gv_fv[k] != 0;
        k--;
        if c == i { return true, fv; }
        let C = o_ins[c];
        if C.op != GIR_ICMP || C.aux != I.aux { continue; }
        if res(C.a) == a && res(C.b) == b || res(C.a) == b && res(C.b) == a {
            var sp: u32 = C.sub;
            if res(C.a) != a { sp = swap_pred(sp); }
            let sd, sm = gv_pred_set(sp);
            if sd == 0 || dom == 0 || sd == dom {
                if sd != 0 { dom = sd; }
                acc &= if fv { sm } else { 7 & ~sm };
            }
        }
        var fa = res(C.a);
        var fb = res(C.b);
        var fp: u32 = C.sub;
        if fa == b && fb == a {
            let t = fa;
            fa = fb;
            fb = t;
            fp = swap_pred(fp);
        }
        if fa != a { continue; }
        if fb == b {
            if acc != 7 {
                if acc & ~qm0 == 0 { return true, true; }
                if acc & qm0 == 0 { return true, false; }
            }
            continue;
        }
        // the fact as a set of outcomes (negated if it is false)
        let fd, fm0 = gv_pred_set(fp);
        let fm = if fv { fm0 } else { 7 & ~fm0 };
        let qd, qm = gv_pred_set(I.sub);
        if fb == b {
            if fd != 0 && qd != 0 && fd != qd { continue; }
            if fm & ~qm == 0 { return true, true; }
            if fm & qm == 0 { return true, false; }
            continue;
        }
        // x pred1 c1 known, x pred2 c2 asked: by ranges
        let k1, c1 = ci(fb);
        let k2, c2 = ci(b);
        if !k1 || !k2 { continue; }
        let d = if fd != 0 { fd } else { qd };
        if d == 0 {
            // two equalities or inequalities
            if fp == GIR_EQ && fv && I.sub == GIR_EQ { return true, c1 == c2; }
            if fp == GIR_EQ && fv && I.sub == GIR_NE { return true, c1 != c2; }
            continue;
        }
        if fd != 0 && qd != 0 && fd != qd { continue; }
        // the fact's range (only a true relational or equality fact, or a
        // false one turned around)
        var p1 = fp;
        if !fv {
            if fp == GIR_EQ { continue; }
            p1 = inv_pred(fp);
        }
        let r1, lo1, hi1 = gv_range(p1, d, c1, bits);
        if !r1 || lo1 > hi1 { continue; }
        if I.sub == GIR_NE || I.sub == GIR_EQ {
            let bias: u64 = if d == 1 { (1 as u64) << (bits - 1) } else { 0 };
            let x2 = (c2 + bias) & wmask(bits);
            let outside = x2 < lo1 || x2 > hi1;
            if outside { return true, I.sub == GIR_NE; }
            if lo1 == hi1 && lo1 == x2 { return true, I.sub == GIR_EQ; }
            continue;
        }
        let r2, lo2, hi2 = gv_range(I.sub, d, c2, bits);
        if !r2 { continue; }
        if lo2 <= lo1 && hi1 <= hi2 { return true, true; }
        if hi1 < lo2 || hi2 < lo1 || lo2 > hi2 { return true, false; }
    }
    return false, false;
}
// Dead stores: the stores of the block since the last read that may see them.
var ds_st: u32[16] = [0; 16];
var ds_n: u32 = 0;
// A read of ps bytes at p with TBAA node pt (p NIL: any memory but private
// allocas) ends the stores it may see.
fn ds_read(p: u32, ps: u32, pt: u32) {
    var n: u32 = 0;
    for k in 0..ds_n {
        let s = ds_st[k];
        let q = res(o_ins[s].b);
        let keep = if p == NIL { gv_ne_base(q) != NIL } else { !aa_alias(p, ps, pt, q, store_of(o_ins[s].aux), o_ins[s].c) };
        if keep {
            ds_st[n] = s;
            n++;
        }
    }
    ds_n = n;
}

fn gv_block(b: u32) {
    ds_n = 0;
    gv_cur = b;
    var i = b_first[b];
    while i != NIL {
        let nx = o_nxt[i];
        let I = o_ins[i];
        let op: u32 = I.op;
        if op == GIR_LOAD && I.flags & (IF_VOLATILE | IF_ORD_MASK) == 0 {
            let p = res(I.a);
            let h = gv_lslot(p, I.ty);
            let v = gv_lget(gv_lt[h], p, store_of(I.ty), I.b);
            if v != NIL {
                replace(i, v);
                gv_changed = true;
            } else {
                gv_lput(h, i, p, i);
                ds_read(p, store_of(I.ty), I.b);
            }
        } else if op == GIR_STORE && I.flags & (IF_VOLATILE | IF_ORD_MASK) == 0 {
            gv_clobber(i);
            let p = res(I.b);
            gv_lput(gv_lslot(p, I.aux), i, p, res(I.a));
            // an earlier store of the same type to the same address is dead
            var n: u32 = 0;
            for k in 0..ds_n {
                let s = ds_st[k];
                if res(o_ins[s].b) == p && o_ins[s].aux == I.aux {
                    unlink(s);
                    gv_changed = true;
                } else {
                    ds_st[n] = s;
                    n++;
                }
            }
            ds_n = n;
            if ds_n == 16 {
                for k in 0..15 { ds_st[k] = ds_st[k + 1]; }
                ds_n = 15;
            }
            ds_st[ds_n] = i;
            ds_n++;
        } else if op == GIR_CALL && I.flags & IF_CALL_NOWRITE != 0 {
            // (reads memory, or none: a pure call is CSE'd)
            if I.flags & IF_CALL_NOREAD == 0 { ds_read(NIL, 0, 0); }
            else if cse_op(I) {
                let j = gv_find_add(i);
                if j != NIL {
                    replace(i, j);
                    gv_changed = true;
                }
            }
        } else if writes_mem(I) {
            gv_clobber(i);
            if op == GIR_MEMCPY { ds_read(res(I.b), I.c, 0); }
            else { ds_read(NIL, 0, 0); }
            if op != GIR_CALL && op != GIR_MEMCPY && op != GIR_MEMSET { ds_n = 0; }
        } else if op == GIR_LOAD {
            ds_n = 0;
        } else if cse_op(I) {
            if (op == GIR_ICMP || op == GIR_FCMP) && gv_fc.len != 0 {
                let kn, val = gv_implied(i);
                if kn {
                    replace(i, mk_const(GIR_T_I1, if val { 1 } else { 0 }, 0));
                    gv_changed = true;
                    i = nx;
                    continue;
                }
            }
            let j = gv_find_add(i);
            if j != NIL {
                replace(i, j);
                gv_changed = true;
            }
        } else if op == GIR_CONDBR && gv_fc.len != 0 {
            let c = res(I.a);
            var k: i64 = gv_fc.len - 1;
            while k >= 0 {
                if gv_fc[k] == c {
                    o_ins[i].a = mk_const(GIR_T_I1, gv_fv[k] as u64, 0);
                    gv_changed = true;
                    break;
                }
                k--;
            }
        }
        i = nx;
    }
}
