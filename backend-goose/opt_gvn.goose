// Dominator-based common-subexpression elimination with load and store
// forwarding on the OIR (opt.goose), in the manner of LLVM's EarlyCSE: the
// dominator tree is walked in pre-order with a scoped hash table of the
// pure instructions seen on the path from the entry; an instruction equal
// to one in the table is replaced by it. Loads are keyed by (address, type)
// and valid while no store may have changed the memory: a store or call
// moves a memory generation, and a block entered from several predecessors
// starts a new one. Memory is split by a simple alias analysis: the
// allocas whose address does not escape (only loads, stores and GEPs use
// it) have generations of their own, which only stores into them move, and
// calls and stores through other pointers leave them alone.

var gv_tab: u32[>..] = [];      // open addressing: instruction id + 1, 0 = empty
var gv_undo: u32[>..] = [];     // slots filled, in order (scope exit clears them in reverse)
var gv_lt: u32[>..] = [];       // loads: slot -> id + 1 of the load or store that holds the value
var gv_lval: u32[>..] = [];     // per load-table entry (by instruction id): the value
var gv_lgen: u32[>..] = [];     // per entry: the generation it is valid in
var gv_lep: u32[>..] = [];      // per entry of a non-escaping alloca: the epoch (gv_ep) too
var gv_lundo: u32[>..] = [];    // (slot, previous content) pairs
var gv_ep: u32 = 0;             // epoch of the alloca generations: new at a merge point
var gv_bep: u32[>..] = [];      // per block: the epoch at its end
var gv_bgen: u32[>..] = [];     // per block: the memory generation at its end
var gv_gen: u32 = 0;            // current generation of escaping memory
var gv_cnt: u32 = 0;            // generation counter (monotonic: a number is never reused)
var gv_agen: u32[>..] = [];     // per alloca (instruction id): its own generation, NIL = escapes
var gv_base: u32[>..] = [];     // per instruction: the alloca its address is based on, NIL
var gv_sblk: u32[>..] = [];     // per alloca: the one block that writes it, NIL none, GV_MANY several
var gv_cur: u32 = 0;            // the block being walked
let GV_MANY: u32 = 0xFFFFFFFE;
var gv_changed = false;

// ------------------------------------------------------------ alias info

// gv_base for pointer-valued instructions (GEP chains off allocas) and
// gv_agen for the allocas whose address does not escape.
fn gv_alias() {
    let n = o_ins.len;
    gv_base.clear();
    gv_base.resize(n, NIL);
    gv_agen.clear();
    gv_agen.resize(n, NIL);
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
                // (with setjmp, memory changes behind the CFG's back)
                gv_agen[i] = if o_f.flags & (FN_RETURNS_TWICE | FN_SJLJ) != 0 { NIL } else { 0 };
            } else if I.op == GIR_GEP && is_inst(res(I.a)) {
                gv_base[i] = gv_base[res(I.a)];
            }
            i = o_nxt[i];
        }
    }
    // escapes: an alloca-based value used other than as a load/store address
    // or a GEP base
    for b in rpo {
        var i = b_first[b];
        while i != NIL {
            let I = o_ins[i];
            let op: u32 = I.op;
            each_slot(i) { s =>
                let v = res(vget(i, s));
                if is_inst(v) && gv_base[v] != NIL {
                    var ok = false;
                    if op == GIR_LOAD && s == 0 { ok = true; }
                    else if op == GIR_STORE && s == 1 { ok = true; }
                    else if op == GIR_GEP && s == 0 { ok = true; }
                    else if (op == GIR_MEMCPY || op == GIR_MEMSET) && s < 2 { ok = true; }
                    if !ok { gv_agen[gv_base[v]] = NIL; }
                    // (the block that writes it)
                    if op == GIR_STORE && s == 1 || (op == GIR_MEMCPY || op == GIR_MEMSET) && s == 0 {
                        let a = gv_base[v];
                        gv_sblk[a] = if gv_sblk[a] == NIL || gv_sblk[a] == b { b } else { GV_MANY };
                    }
                }
            };
            i = o_nxt[i];
        }
    }
}
// The memory generation that guards a load or store at address p, and
// whether it is a non-escaping alloca's (then the epoch counts too).
fn gv_mgen(p: u32) -> u32, bool {
    if is_inst(p) {
        let a = gv_base[p];
        if a != NIL && gv_agen[a] != NIL { return gv_agen[a], true; }
    }
    return gv_gen, false;
}
// Records load/store i (address p) as the holder of value v.
fn gv_lput(h: u64, i: u32, p: u32, v: u32) {
    gv_lundo.push(h as! u32);
    gv_lundo.push(gv_lt[h]);
    gv_lt[h] = i + 1;
    gv_lval[i] = v;
    let g, al = gv_mgen(p);
    gv_lgen[i] = g;
    gv_lep[i] = if al { gv_ep } else { 0 };
}
// The value load/store entry e (id + 1) holds for address p now, or NIL.
// A non-escaping alloca's entry also needs the epoch (no merge point since),
// unless all writes of the alloca are in one block that dominates this one:
// then no write happens between the entry (which is in a dominator, after
// that block's writes, or its generation would differ) and here, because a
// path from the writing block to here passes the entry's block again.
fn gv_lget(e: u32, p: u32) -> u32 {
    if e == 0 { return NIL; }
    let g, al = gv_mgen(p);
    if gv_lgen[e - 1] != g { return NIL; }
    if al && gv_lep[e - 1] != gv_ep {
        let w = gv_sblk[gv_base[p]];
        if w == NIL || w == GV_MANY || !dominates(w, gv_cur) { return NIL; }
    }
    return gv_lval[e - 1];
}
fn gv_bump() -> u32 {
    gv_cnt++;
    return gv_cnt;
}
// The instruction writes memory: move the generations it may affect.
fn gv_clobber(i: u32) {
    let I = o_ins[i];
    let op: u32 = I.op;
    var p: u32 = NIL;
    if op == GIR_STORE { p = res(I.b); }
    else if op == GIR_MEMCPY || op == GIR_MEMSET { p = res(I.a); }
    if p != NIL && is_inst(p) {
        let a = gv_base[p];
        if a != NIL && gv_agen[a] != NIL {
            gv_agen[a] = gv_bump();
            return;
        }
    }
    gv_gen = gv_bump();
}
fn writes_mem(I: Inst) -> bool {
    let op: u32 = I.op;
    if op == GIR_STORE || op == GIR_CALL || op == GIR_MEMCPY || op == GIR_MEMSET || op == GIR_VASTART { return true; }
    if op == GIR_CMPXCHG || op == GIR_ATOMICRMW || op == GIR_FENCE || op == GIR_ASM { return true; }
    if op == GIR_SJLJ_SETJMP || op == GIR_SJLJ_LONGJMP || op == GIR_STACKRESTORE || op == GIR_LANDINGPAD { return true; }
    if op == GIR_LOAD { return I.flags & (IF_VOLATILE | IF_ORD_MASK) != 0; }
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
    if I.op == GIR_GEP { b = 0; }   // (the run: compared word by word)
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
    gv_alias();
    let n = o_ins.len;
    gv_lval.clear();
    gv_lval.resize(n, NIL);
    gv_lgen.clear();
    gv_lgen.resize(n, 0);
    gv_lep.clear();
    gv_lep.resize(n, 0);
    gv_bgen.clear();
    gv_bgen.resize(cfg_nb, 0);
    gv_bep.clear();
    gv_bep.resize(cfg_nb, 0);
    gv_undo.clear();
    gv_lundo.clear();
    gv_cnt = 1;
    gv_gen = 1;
    gv_ep = 1;
    tmp_stack.clear();
    tmp_stack.push(0);
    tmp_pos.clear();
    tmp_pos.resize(2 * cfg_nb, 0);
    while tmp_stack.len != 0 {
        let e = tmp_stack.pop();
        if e & 0x80000000 != 0 {
            let b = e & 0x7FFFFFFF;
            let m1 = tmp_pos[2 * b];
            while gv_undo.len > m1 { gv_tab[gv_undo.pop()] = 0; }
            let m2 = tmp_pos[2 * b + 1];
            while gv_lundo.len > m2 {
                let old = gv_lundo.pop();
                let h = gv_lundo.pop();
                gv_lt[h] = old;
            }
            continue;
        }
        let b = e;
        tmp_pos[2 * b] = gv_undo.len as! u32;
        tmp_pos[2 * b + 1] = gv_lundo.len as! u32;
        // the memory state at entry: the dominator's at its end if it is the
        // only predecessor, else unknown
        let np = p_start[b + 1] - p_start[b];
        if b != 0 && np == 1 && p_list[p_start[b]] == idom[b] {
            gv_gen = gv_bgen[idom[b]];
            gv_ep = gv_bep[idom[b]];
        } else if b != 0 {
            gv_gen = gv_bump();
            gv_ep = gv_bump();
        }
        gv_block(b);
        gv_bgen[b] = gv_gen;
        gv_bep[b] = gv_ep;
        tmp_stack.push(b | 0x80000000);
        var c = dt_first[b];
        while c != NIL {
            tmp_stack.push(c);
            c = dt_next[c];
        }
    }
    return gv_changed;
}

// Dead stores: the stores of the block since the last read that may see them.
var ds_st: u32[16] = [0; 16];
var ds_n: u32 = 0;
// The alloca a non-escaping pointer is based on, or NIL.
fn gv_ne_base(p: u32) -> u32 {
    if !is_inst(p) { return NIL; }
    let a = gv_base[p];
    if a != NIL && gv_agen[a] != NIL { return a; }
    return NIL;
}
// Pointers p and q may point to the same memory.
fn gv_may_alias(p: u32, q: u32) -> bool {
    if p == q { return true; }
    let a = gv_ne_base(p);
    let b = gv_ne_base(q);
    if a == NIL && b == NIL { return true; }
    return a == b;
}
// A read of memory at p (NIL: any escaping memory) ends the stores it may see.
fn ds_read(p: u32) {
    var n: u32 = 0;
    for k in 0..ds_n {
        let s = ds_st[k];
        let q = res(o_ins[s].b);
        let keep = if p == NIL { gv_ne_base(q) != NIL } else { !gv_may_alias(p, q) };
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
            let v = gv_lget(gv_lt[h], p);
            if v != NIL {
                replace(i, v);
                gv_changed = true;
            } else {
                gv_lput(h, i, p, i);
                ds_read(p);
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
        } else if writes_mem(I) {
            gv_clobber(i);
            ds_read(NIL);
            if op != GIR_CALL { ds_n = 0; }
        } else if op == GIR_LOAD {
            ds_n = 0;
        } else if cse_op(I) {
            let j = gv_find_add(i);
            if j != NIL {
                replace(i, j);
                gv_changed = true;
            }
        }
        i = nx;
    }
}
