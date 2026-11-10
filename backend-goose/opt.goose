// The Goose middle-end (milestone E1): an optimizer on GIR that runs before
// code generation when the header's opt_level is >= 1 (DESIGN.md §15).
//
// The GIR tables come in (M), new tables go out (x_*), and M is switched to
// them before the back-end proper runs. Each function is loaded into a
// mutable working form (the OIR below), optimized, and stored back; the
// functions are visited callees first, so the inliner (opt_inline.goose)
// copies callees that are already optimized out of the output tables.
//
// OIR: the instruction records of one function (and of the code inlined
// into it) in o_ins, with the GIR operand encoding except that an
// instruction reference is the local id (GIR_V_INST | id); operand runs
// (call arguments, PHI pairs, GEP terms, switch cases, ...) are copied into
// o_ops. Blocks hold a doubly linked list of their instructions
// (b_first/b_last, o_nxt/o_prv) and are linked in layout order (b_lnext).
// Deleting an instruction unlinks it (o_blk = NIL); replacing a value sets
// o_fwd[id], which every reader resolves (res) until resolve_all rewrites
// the operands. There are no hash maps of instructions and no use lists
// that have to be kept up to date: the passes that need uses build them
// (build_uses, CSR arrays), and the CFG analyses (opt_cfg.goose) are
// recomputed after a pass that changes the CFG.

let NIL: u32 = 0xFFFFFFFF;

// ------------------------------------------------------- output tables
var x_insts: Inst[>..] = [];
var x_blocks: Block[>..] = [];
var x_funcs: Func[>..] = [];
var x_opnds: u32[>..] = [];      // M.opnds, then the runs of the stored functions
var x_consts: Const[>..] = [];   // M.consts, then the constants the optimizer made
var x_asms: Asm[>..] = [];       // M.asms, then one record per stored ASM
var x_dies: Die[>..] = [];
var x_dattrs: DAttr[>..] = [];
var in2out: u32[>..] = [];       // input instruction index -> output index (debug info), NIL
// Where this call's region of each output array starts (M views x_*[xb_*..]).
var xb_i: i64 = 0;
var xb_b: i64 = 0;
var xb_f: i64 = 0;
var xb_o: i64 = 0;
var xb_c: i64 = 0;
var xb_a: i64 = 0;
var xb_d: i64 = 0;
var xb_t: i64 = 0;

// ---------------------------------------------------------------- OIR
var o_ins: Inst[>..] = [];
var o_nxt: u32[>..] = [];
var o_prv: u32[>..] = [];
var o_blk: u32[>..] = [];        // block of the instruction; NIL: deleted
var o_fwd: u32[>..] = [];        // the value that replaces it (NIL: none)
var o_old: u32[>..] = [];        // input instruction index (debug info), NIL
var o_ops: u32[>..] = [];
var b_first: u32[>..] = [];
var b_last: u32[>..] = [];
var b_lnext: u32[>..] = [];      // next block in layout order
var b_fl: u8[>..] = [];          // BF_*
let BF_DEAD: u8 = 1;
let BF_LP: u8 = 2;               // landing pad (starts with LANDINGPAD; no PHIs allowed)

var o_cfg_ok = false;            // the CFG analyses (opt_cfg.goose) describe the current CFG
var o_fwd_dirty = false;         // some o_fwd was set since the last resolve_all
var o_fi: u32 = 0;               // funcs index of the function being optimized
var o_f: Func;                   // its record (input)
var o_pinned = false;            // its blocks are named elsewhere (block addresses): no CFG changes
var o_dbg = false;               // the module has debug information entries
var opt_lv: u32 = 1;             // the optimization level (GIR opt_level bits 0..7: 1, 2, 3)
var opt_sz: u32 = 0;             // the size level (bits 8..9: 1 = -Os, 2 = -Oz)

// Value-operand masks per opcode: fields a, b, c, and the runs.
let OV_A: u8 = 1;
let OV_B: u8 = 2;
let OV_C: u8 = 4;
let OV_GEP: u8 = 8;
let OV_CALL: u8 = 16;
let OV_PHI: u8 = 32;
let OV_ASM: u8 = 64;
let OP_VAL: u8[84] = [
    1, 0, 1, 1, 0, 3, 3, 3,  // ret br condbr switch unreachable add sub mul
    3, 3, 3, 3, 3, 3, 3, 3,  // sdiv udiv srem urem and or xor shl
    3, 3, 3, 7, 1, 1, 1, 1,  // lshr ashr icmp select zext sext trunc ptrtoint
    1, 1, 0, 1, 3, 9, 17, 32,  // inttoptr bitcast alloca load store gep call phi
    3, 3, 3, 3, 1, 3, 1, 1,  // fadd fsub fmul fdiv fneg fcmp fpext fptrunc
    1, 1, 1, 1, 1, 3, 3, 7,  // fptosi fptoui sitofp uitofp extractvalue insertvalue extractelt insertelt
    3, 1, 0, 1, 1, 3, 3, 1,  // shuffle dynalloca stacksave stackrestore vastart memcpy memset ctlz
    1, 1, 1, 1, 7, 7, 3, 3,  // cttz ctpop bswap bitreverse fshl fshr ovf scmp
    3, 1, 3, 1, 1, 7, 3, 0,  // ucmp fabs copysign fsqrt isfpclass cmpxchg atomicrmw fence
    0, 0, 0, 1, 1, 0, 0, 1,  // tlsaddr frameaddr retaddr sjlj_setjmp sjlj_longjmp trap debugtrap indirectbr
    0, 3, 64, 0,  // blockaddr x86 asm landingpad
];

inline fn is_inst(v: u32) -> bool { gir_kind(v) == GIR_V_INST }
inline fn iref(id: u32) -> u32 { id }   // GIR_V_INST is kind 0
inline fn ck(v: u32) -> bool { gir_kind(v) == GIR_V_CONST }
inline fn alive(i: u32) -> bool { o_blk[i] != NIL }
inline fn is_term_op(op: u32) -> bool { op <= GIR_UNREACHABLE || op == GIR_INDIRECTBR }

// The value v resolves to (following replacements).
fn res(v: u32) -> u32 {
    var x = v;
    while gir_kind(x) == GIR_V_INST {
        let f = o_fwd[x];
        if f == NIL { break; }
        x = f;
    }
    return x;
}

// Type of an OIR value.
fn otype(v: u32) -> u32 {
    let k = gir_kind(v);
    if k == GIR_V_INST { return o_ins[v].ty; }
    if k == GIR_V_ARG { return M.opnds[o_f.args + 2 * gir_idx(v)]; }
    if k == GIR_V_CONST { return x_consts[xb_c + gir_idx(v)].ty; }
    return GIR_T_PTR;
}

// ------------------------------------------------------ operand slots
// A slot names one value operand of an instruction: 0, 1, 2 = field a, b,
// c; SLOT_RUN | k = o_ops[k].
let SLOT_RUN: u32 = 0x80000000;
let SLOT_A: u32 = 0;
let SLOT_B: u32 = 1;
let SLOT_C: u32 = 2;
var vs: u32[>..] = [];

// The value-operand slots of instruction i, into vs.
fn vslots(i: u32) {
    vs.clear();
    let I = o_ins[i];
    let m: u32 = if I.op < GIR_NOPS { OP_VAL[I.op] } else { 7 };
    if m & OV_A != 0 { vs.push(0); }
    if m & OV_B != 0 { vs.push(1); }
    if m & OV_C != 0 { vs.push(2); }
    if m >= OV_GEP {
        if m & OV_GEP != 0 { for k in 0..I.c { vs.push(SLOT_RUN | (I.b + 2 + 2 * k)); } }
        else { for k in 0..I.c { vs.push(SLOT_RUN | (I.b + 2 * k)); } }   // call args, PHI values, asm inputs
    }
}
fn vget(i: u32, s: u32) -> u32 {
    if s >= SLOT_RUN { return o_ops[s & ~SLOT_RUN]; }
    if s == 0 { return o_ins[i].a; }
    if s == 1 { return o_ins[i].b; }
    return o_ins[i].c;
}
fn vset(i: u32, s: u32, v: u32) {
    if s >= SLOT_RUN { o_ops[s & ~SLOT_RUN] = v; }
    else if s == 0 { o_ins[i].a = v; }
    else if s == 1 { o_ins[i].b = v; }
    else { o_ins[i].c = v; }
}
// The value-operand slots of instruction i: F(slot) for each (no array).
fn each_slot<F>(i: u32) {
    let I = o_ins[i];
    let m: u32 = if I.op < GIR_NOPS { OP_VAL[I.op] } else { 7 };
    if m & OV_A != 0 { F(SLOT_A); }
    if m & OV_B != 0 { F(SLOT_B); }
    if m & OV_C != 0 { F(SLOT_C); }
    if m >= OV_GEP {
        if m & OV_GEP != 0 { for k in 0..I.c { F(SLOT_RUN | (I.b + 2 + 2 * k)); } }
        else { for k in 0..I.c { F(SLOT_RUN | (I.b + 2 * k)); } }
    }
}
// Rewrites every operand of every live instruction to its resolved value
// (nothing to do unless a value was replaced since the last time).
fn resolve_all() {
    if !o_fwd_dirty { return; }
    o_fwd_dirty = false;
    for i0 in 0..o_ins.len {
        if o_blk[i0] == NIL { continue; }
        let i: u32 = i0 as! u32;
        each_slot(i) { s =>
            let v = vget(i, s);
            if gir_kind(v) == GIR_V_INST && o_fwd[v] != NIL { vset(i, s, res(v)); }
        };
    }
}

// ------------------------------------------------- instructions, blocks
fn new_inst(I: Inst) -> u32 {
    let id: u32 = o_ins.len as! u32;
    o_ins.push(I);
    o_nxt.push(NIL);
    o_prv.push(NIL);
    o_blk.push(NIL);
    o_fwd.push(NIL);
    o_old.push(NIL);
    return id;
}
fn new_block() -> u32 {
    o_cfg_ok = false;
    let b: u32 = b_first.len as! u32;
    b_first.push(NIL);
    b_last.push(NIL);
    b_lnext.push(NIL);
    b_fl.push(0);
    return b;
}
// Links instruction i at the end of block b.
fn link_end(b: u32, i: u32) {
    let l = b_last[b];
    o_prv[i] = l;
    o_nxt[i] = NIL;
    if l == NIL { b_first[b] = i; } else { o_nxt[l] = i; }
    b_last[b] = i;
    o_blk[i] = b;
}
// Links instruction i before instruction at (in its block).
fn link_before(at: u32, i: u32) {
    let b = o_blk[at];
    let p = o_prv[at];
    o_prv[i] = p;
    o_nxt[i] = at;
    o_prv[at] = i;
    if p == NIL { b_first[b] = i; } else { o_nxt[p] = i; }
    o_blk[i] = b;
}
fn link_after(at: u32, i: u32) {
    let n = o_nxt[at];
    if n == NIL { link_end(o_blk[at], i); return; }
    link_before(n, i);
}
fn link_start(b: u32, i: u32) {
    let f = b_first[b];
    if f == NIL { link_end(b, i); } else { link_before(f, i); }
}
// Removes instruction i from its block (it stays in o_ins, dead).
fn unlink(i: u32) {
    let b = o_blk[i];
    if b == NIL { return; }
    let p = o_prv[i];
    let n = o_nxt[i];
    if p == NIL { b_first[b] = n; } else { o_nxt[p] = n; }
    if n == NIL { b_last[b] = p; } else { o_prv[n] = p; }
    o_blk[i] = NIL;
    o_prv[i] = NIL;
    o_nxt[i] = NIL;
}
// Replaces instruction i by value v everywhere and deletes it.
fn replace(i: u32, v: u32) {
    if v != i {
        o_fwd[i] = v;
        o_fwd_dirty = true;
    }
    unlink(i);
}
// The first instruction of b that is not a PHI (NIL: none).
fn first_non_phi(b: u32) -> u32 {
    var i = b_first[b];
    while i != NIL && o_ins[i].op == GIR_PHI { i = o_nxt[i]; }
    return i;
}
// A run of n words appended to o_ops (zeros); returns its start.
fn new_run(n: u32) -> u32 {
    let s: u32 = o_ops.len as! u32;
    for k in 0..n { o_ops.push(0); }
    return s;
}

// ----------------------------------------------------------- constants
// Integer constants are canonical in the optimizer: one x_consts entry per
// (type, value), so equal constants are equal references (the exporter
// repeats integer constants; FP and aggregate ones it deduplicates).
var ch_key: u32[>..] = [];      // open addressing: x_consts index + 1, 0 = empty
var ch_n: i64 = 0;
var undef_c: u32[>..] = [];     // per type: its zero/undef constant ref, NIL

fn ch_hash(lo: u64, hi: u64, t: u32) -> u64 {
    var h: u64 = lo * 0x9E3779B97F4A7C15 + hi * 0xC2B2AE3D27D4EB4F + (t as u64) * 0x165667B19E3779F9;
    h ^= h >> 29;
    return h;
}
fn ch_grow() {
    var n: i64 = if ch_key.len == 0 { 1024 } else { ch_key.len * 2 };
    while n < 4 * (x_consts.len - xb_c) { n *= 2; }
    ch_key.clear();
    ch_key.resize(n, 0);
    ch_n = 0;
    for k in xb_c..x_consts.len {
        let C = x_consts[k];
        if cls_of(C.ty) == C_INT || cls_of(C.ty) == C_INT2 { ch_put((k - xb_c) as! u32); }
    }
}
fn ch_put(k: u32) {
    let C = x_consts[xb_c + k];
    let mask: u64 = (ch_key.len - 1) as! u64;
    var h = ch_hash(C.lo, C.hi, C.ty) & mask;
    loop {
        let e = ch_key[h];
        if e == 0 {
            ch_key[h] = k + 1;
            ch_n++;
            return;
        }
        let D = x_consts[xb_c + e - 1];
        if D.lo == C.lo && D.hi == C.hi && D.ty == C.ty { return; }
        h = (h + 1) & mask;
    }
}
// The constant (type t, bits lo/hi) as a value reference. t: INT or INT2
// (any width; lo/hi must be zero-extended from the width).
fn mk_const(t: u32, lo: u64, hi: u64) -> u32 {
    if (ch_n + 1) * 2 > ch_key.len { ch_grow(); }
    let mask: u64 = (ch_key.len - 1) as! u64;
    var h = ch_hash(lo, hi, t) & mask;
    loop {
        let e = ch_key[h];
        if e == 0 { break; }
        let D = x_consts[xb_c + e - 1];
        if D.lo == lo && D.hi == hi && D.ty == t { return GIR_V_CONST << 30 | (e - 1); }
        h = (h + 1) & mask;
    }
    let k: u32 = (x_consts.len - xb_c) as! u32;
    x_consts.push(Const { lo: lo, hi: hi, ty: t, data: GIR_NONE });
    ch_key[h] = k + 1;
    ch_n++;
    return GIR_V_CONST << 30 | k;
}
// The canonical reference of integer constant c (others are returned as is).
fn canon_const(v: u32) -> u32 {
    let C = x_consts[xb_c + gir_idx(v)];
    if C.data != GIR_NONE { return v; }
    let c = cls_of(C.ty);
    if c != C_INT && c != C_INT2 { return v; }
    return mk_const(C.ty, C.lo, C.hi);
}
// Mask of the low `bits` bits.
checkfree fn wmask(bits: u32) -> u64 {
    if bits >= 64 { return 0xFFFFFFFFFFFFFFFF; }
    return ((1 as u64) << bits) - 1;
}
// An integer constant of type t (INT, <= 64 bits) with value x (truncated).
fn int_const(t: u32, x: u64) -> u32 { mk_const(t, x & wmask(bits_of(t)), 0) }
// The undefined (zero) value of type t.
fn undef_of(t: u32) -> u32 {
    if undef_c.len <= t { undef_c.resize(M.types.len, NIL); }
    let u = undef_c[t];
    if u != NIL { return u; }
    var r: u32 = 0;
    let c = cls_of(t);
    if c == C_INT || c == C_INT2 { r = mk_const(t, 0, 0); }
    else {
        let k: u32 = (x_consts.len - xb_c) as! u32;
        x_consts.push(Const { lo: 0, hi: 0, ty: t, data: GIR_NONE });
        r = GIR_V_CONST << 30 | k;
    }
    undef_c[t] = r;
    return r;
}
// Constant value of an INT-class constant reference (zero-extended).
inline fn cval(v: u32) -> u64 { x_consts[xb_c + gir_idx(v)].lo }
fn is_int_const(v: u32) -> bool {
    if gir_kind(v) != GIR_V_CONST { return false; }
    let C = x_consts[xb_c + gir_idx(v)];
    return cls_of(C.ty) == C_INT && C.data == GIR_NONE;
}

// --------------------------------------------------------------- loading
var amap: u32[>..] = [];         // inlining: argument k -> its value in the caller
var amap_on = false;
var ld_fbase: u32 = 0;           // first instruction of the source function
var ld_ibase: u32 = 0;           // its local id 0 in the OIR
var ld_bbase: u32 = 0;           // its block 0 in the OIR

inline fn cvt(v: u32) -> u32 {
    let k = gir_kind(v);
    if k == GIR_V_INST { return gir_idx(v) - ld_fbase + ld_ibase; }
    if k == GIR_V_CONST { return canon_const(v); }
    if k == GIR_V_ARG && amap_on { return amap[gir_idx(v)]; }
    return v;
}

// Appends function f (instructions in ins, blocks in blk, runs in x_opnds)
// to the OIR: its instruction k gets id ld_ibase + k (o_ins must have that
// length), its block k number ld_bbase + k (likewise). Blocks are linked in
// their order; the caller links the first one into the layout.
fn oir_load(ins: const Inst[:], blk: const Block[:], f: Func, track: bool) {
    ld_fbase = f.first_inst;
    ld_ibase = o_ins.len as! u32;
    ld_bbase = b_first.len as! u32;
    for b in 0..f.n_blocks {
        let nb = new_block();
        if b > 0 { b_lnext[nb - 1] = nb; }
    }
    for b in 0..f.n_blocks {
        let B = blk[f.first_block + b];
        let ob = ld_bbase + b;
        for gi in B.first_inst..B.first_inst + B.n_inst {
            let I = ins[gi];
            let id = new_inst(load_inst(I));
            if track { o_old[id] = gi; }
            link_end(ob, id);
            if I.op == GIR_LANDINGPAD { b_fl[ob] |= BF_LP; }
        }
    }
}
// The OIR form of record I (operands converted, runs copied).
fn load_inst(I0: Inst) -> Inst {
    var I = I0;
    let op: u32 = I.op;
    let m: u32 = if op < GIR_NOPS { OP_VAL[op] } else { 7 };
    if m & OV_A != 0 { I.a = cvt(I.a); }
    if m & OV_B != 0 { I.b = cvt(I.b); }
    if m & OV_C != 0 { I.c = cvt(I.c); }
    let s: u32 = o_ops.len as! u32;
    if op == GIR_BR { I.a += ld_bbase; }
    else if op == GIR_CONDBR {
        I.b += ld_bbase;
        I.c += ld_bbase;
    } else if op == GIR_GEP {
        o_ops.push(x_opnds[xb_o + I0.b]);
        o_ops.push(x_opnds[xb_o + I0.b + 1]);
        for k in 0..I.c {
            o_ops.push(cvt(x_opnds[xb_o + I0.b + 2 + 2 * k]));
            o_ops.push(x_opnds[xb_o + I0.b + 3 + 2 * k]);
        }
        I.b = s;
    } else if op == GIR_CALL {
        for k in 0..I.c {
            o_ops.push(cvt(x_opnds[xb_o + I0.b + 2 * k]));
            o_ops.push(x_opnds[xb_o + I0.b + 2 * k + 1]);
        }
        if I.flags & IF_INVOKE != 0 { o_ops.push(x_opnds[xb_o + I0.b + 2 * I.c] + ld_bbase); }
        I.b = s;
    } else if op == GIR_PHI {
        for k in 0..I.c {
            o_ops.push(cvt(x_opnds[xb_o + I0.b + 2 * k]));
            o_ops.push(x_opnds[xb_o + I0.b + 2 * k + 1] + ld_bbase);
        }
        I.b = s;
    } else if op == GIR_SWITCH {
        o_ops.push(x_opnds[xb_o + I0.b] + ld_bbase);
        for k in 0..I.c {
            o_ops.push(canon_const(x_opnds[xb_o + I0.b + 1 + 2 * k]));
            o_ops.push(x_opnds[xb_o + I0.b + 2 + 2 * k] + ld_bbase);
        }
        I.b = s;
    } else if op == GIR_INDIRECTBR {
        for k in 0..I.c { o_ops.push(x_opnds[xb_o + I0.b + k] + ld_bbase); }
        I.b = s;
    } else if op == GIR_SHUFFLE {
        let n = M.types[I.ty].n;
        for k in 0..n { o_ops.push(x_opnds[xb_o + I0.c + k]); }
        I.c = s;
    } else if op == GIR_LANDINGPAD {
        for k in 0..I.b { o_ops.push(x_opnds[xb_o + I0.a + k]); }
        I.a = s;
    } else if op == GIR_ASM {
        // the asm's (input value, register) pairs, then its (register,
        // offset) outputs; b = the run, c = the number of inputs
        let A = x_asms[xb_a + I0.a];
        for k in 0..A.n_in {
            o_ops.push(cvt(x_opnds[xb_o + A.ops + 2 * k]));
            o_ops.push(x_opnds[xb_o + A.ops + 2 * k + 1]);
        }
        for k in 0..2 * A.n_out { o_ops.push(x_opnds[xb_o + A.ops + 2 * A.n_in + k]); }
        I.b = s;
        I.c = A.n_in;
    }
    return I;
}

// --------------------------------------------------------------- storing
var st_bnum: u32[>..] = [];      // OIR block -> output block number (NIL: dead)
var st_map: u32[>..] = [];       // OIR instruction -> output instruction index

inline fn sv(v0: u32) -> u32 {
    let v = res(v0);
    if gir_kind(v) == GIR_V_INST { return st_map[v]; }
    return v;
}

// Appends the OIR function to the output tables as function fi.
fn oir_store(fi: u32) {
    let nbo = b_first.len;
    if st_bnum.len < nbo { st_bnum.resize(nbo, NIL); }
    if st_map.len < o_ins.len { st_map.resize(o_ins.len, NIL); }
    var nb: u32 = 0;
    var b: u32 = 0;
    while b != NIL {
        if b_fl[b] & BF_DEAD == 0 {
            st_bnum[b] = nb;
            nb++;
        } else {
            st_bnum[b] = NIL;
        }
        b = b_lnext[b];
    }
    let base: u32 = (x_insts.len - xb_i) as! u32;
    var n: u32 = 0;
    b = 0;
    while b != NIL {
        if b_fl[b] & BF_DEAD == 0 {
            var i = b_first[b];
            while i != NIL {
                st_map[i] = base + n;
                n++;
                i = o_nxt[i];
            }
        }
        b = b_lnext[b];
    }
    let fb: u32 = (x_blocks.len - xb_b) as! u32;
    b = 0;
    while b != NIL {
        if b_fl[b] & BF_DEAD == 0 {
            let first: u32 = (x_insts.len - xb_i) as! u32;
            var i = b_first[b];
            while i != NIL {
                x_insts.push(store_inst(i));
                if o_old[i] != NIL { in2out[o_old[i]] = st_map[i]; }
                i = o_nxt[i];
            }
            x_blocks.push(Block { first_inst: first, n_inst: (x_insts.len - xb_i) as! u32 - first });
        }
        b = b_lnext[b];
    }
    x_funcs[xb_f + fi].first_block = fb;
    x_funcs[xb_f + fi].n_blocks = nb;
    x_funcs[xb_f + fi].first_inst = base;
    x_funcs[xb_f + fi].n_inst = n;
}
inline fn sb(b: u32) -> u32 { st_bnum[b] }
// The output record of OIR instruction i.
fn store_inst(i: u32) -> Inst {
    var I = o_ins[i];
    let op: u32 = I.op;
    let m: u32 = if op < GIR_NOPS { OP_VAL[op] } else { 7 };
    if m & OV_A != 0 { I.a = sv(I.a); }
    if m & OV_B != 0 { I.b = sv(I.b); }
    if m & OV_C != 0 { I.c = sv(I.c); }
    let s0 = I.b;
    let s: u32 = (x_opnds.len - xb_o) as! u32;
    if op == GIR_BR { I.a = sb(I.a); }
    else if op == GIR_CONDBR {
        I.b = sb(I.b);
        I.c = sb(I.c);
    } else if op == GIR_GEP {
        x_opnds.push(o_ops[s0]);
        x_opnds.push(o_ops[s0 + 1]);
        for k in 0..I.c {
            x_opnds.push(sv(o_ops[s0 + 2 + 2 * k]));
            x_opnds.push(o_ops[s0 + 3 + 2 * k]);
        }
        I.b = s;
    } else if op == GIR_CALL {
        for k in 0..I.c {
            x_opnds.push(sv(o_ops[s0 + 2 * k]));
            x_opnds.push(o_ops[s0 + 2 * k + 1]);
        }
        if I.flags & IF_INVOKE != 0 { x_opnds.push(sb(o_ops[s0 + 2 * I.c])); }
        I.b = s;
    } else if op == GIR_PHI {
        for k in 0..I.c {
            x_opnds.push(sv(o_ops[s0 + 2 * k]));
            x_opnds.push(sb(o_ops[s0 + 2 * k + 1]));
        }
        I.b = s;
    } else if op == GIR_SWITCH {
        x_opnds.push(sb(o_ops[s0]));
        for k in 0..I.c {
            x_opnds.push(o_ops[s0 + 1 + 2 * k]);
            x_opnds.push(sb(o_ops[s0 + 2 + 2 * k]));
        }
        I.b = s;
    } else if op == GIR_INDIRECTBR {
        for k in 0..I.c { x_opnds.push(sb(o_ops[s0 + k])); }
        I.b = s;
    } else if op == GIR_SHUFFLE {
        let n = M.types[I.ty].n;
        for k in 0..n { x_opnds.push(o_ops[I.c + k]); }
        I.c = s;
    } else if op == GIR_LANDINGPAD {
        for k in 0..I.b { x_opnds.push(o_ops[I.a + k]); }
        I.a = s;
    } else if op == GIR_ASM {
        var A = x_asms[xb_a + I.a];
        let nin = I.c;
        for k in 0..nin {
            x_opnds.push(sv(o_ops[s0 + 2 * k]));
            x_opnds.push(o_ops[s0 + 2 * k + 1]);
        }
        for k in 0..2 * A.n_out { x_opnds.push(o_ops[s0 + 2 * nin + k]); }
        A.ops = s;
        I.a = (x_asms.len - xb_a) as! u32;
        x_asms.push(A);
        I.b = 0;
        I.c = 0;
    }
    return I;
}

fn oir_reset() {
    o_ins.clear();
    o_nxt.clear();
    o_prv.clear();
    o_blk.clear();
    o_fwd.clear();
    o_old.clear();
    o_ops.clear();
    b_first.clear();
    b_last.clear();
    b_lnext.clear();
    b_fl.clear();
    o_cfg_ok = false;
    o_fwd_dirty = false;
}

// ------------------------------------------------------------ debug info
// The DIE attributes that name instructions: a variable's address
// (GIR_DF_LOCAL) and a label (GIR_DF_LABEL) follow the instruction to its
// output index; an attribute whose instruction is gone (a promoted alloca,
// deleted code) is dropped, so the variable has no location (gdb: optimized
// out).
fn remap_dies() {
    if M.dies.len == 0 { return; }
    for D in M.dies {
        var E = D;
        E.attrs = (x_dattrs.len - xb_t) as! u32;
        for k in D.attrs..D.attrs + D.n_attrs {
            var A = M.dattrs[k];
            if A.form == DF_LOCAL {
                let v: u32 = (A.val & 0xFFFFFFFF) as! u32;
                if gir_kind(v) == GIR_V_INST {
                    let nv = in2out[gir_idx(v)];
                    if nv == NIL { continue; }
                    A.val = (A.val & 0xFFFFFFFF00000000) | (nv as u64);
                }
            } else if A.form == DF_LABEL {
                let nv = in2out[A.val];
                if nv == NIL { continue; }
                A.val = nv as u64;
            }
            x_dattrs.push(A);
        }
        E.n_attrs = (x_dattrs.len - xb_t) as! u32 - E.attrs;
        x_dies.push(E);
    }
}

// ---------------------------------------------------------------- driver

// Blocks of function fi named by block addresses (BLOCKADDR anywhere, data
// relocations): its block numbers must not change.
var fn_pinned: u8[>..] = [];

fn opt_module() {
    // (the output arrays never shrink, because M holds views of them: a
    // second call appends a new region)
    xb_c = x_consts.len;
    x_consts.append(M.consts);
    xb_o = x_opnds.len;
    x_opnds.append(M.opnds);
    xb_a = x_asms.len;
    x_asms.append(M.asms);
    xb_f = x_funcs.len;
    x_funcs.append(M.funcs);
    xb_i = x_insts.len;
    xb_b = x_blocks.len;
    xb_d = x_dies.len;
    xb_t = x_dattrs.len;
    in2out.clear();
    in2out.resize(M.insts.len, NIL);
    ch_key.clear();
    ch_n = 0;
    ch_grow();
    undef_c.clear();
    build_type_rc();
    o_dbg = M.dies.len != 0;
    opt_lv = M.header[0].r0 & 0xFF;
    if opt_lv > 3 { opt_lv = 3; }
    opt_sz = (M.header[0].r0 >> 8) & 3;
    fn_pinned.clear();
    fn_pinned.resize(M.funcs.len, 0);
    for d in M.drelocs {
        if d.kind == DR_BLOCK || d.kind == DR_BLOCKDIFF32 {
            let g = M.globals[d.target];
            if g.kind == G_FUNC && g.func != GIR_NONE { fn_pinned[g.func] = 1; }
        }
    }
    for I in M.insts {
        if I.op == GIR_BLOCKADDR {
            let g = M.globals[I.a];
            if g.func != GIR_NONE { fn_pinned[g.func] = 1; }
        }
    }
    opt_off("");    // (reads GOOVM_OPT)
    opt_verify_on = find(opt_env, "verify") >= 0;
    inl_scan();
    gp_scan();
    aa_module_init();
    sroa_init();
    opt_order();
    for fi in fn_order { opt_function(fi); }
    // internal functions whose calls were all inlined are not emitted
    // (kept with debug information, whose subprograms name them)
    if !o_dbg && !opt_off("inline") {
        for fi in 0..M.funcs.len {
            let F = M.funcs[fi];
            if F.flags & FN_INTERNAL == 0 || fn_calls[fi] != 0 || fn_addr[fi] != 0 { continue; }
            if M.gcomdat.len != 0 && M.gcomdat[F.global] != GIR_NONE { continue; }
            x_funcs[xb_f + fi].flags |= FN_DEAD;
        }
    }
    remap_dies();
    if opt_dump_on() { dump_module(); }
    // (field by field: the other tables stay the host's)
    M.funcs = x_funcs[xb_f..];
    M.blocks = x_blocks[xb_b..];
    M.insts = x_insts[xb_i..];
    M.opnds = x_opnds[xb_o..];
    M.consts = x_consts[xb_c..];
    M.asms = x_asms[xb_a..];
    M.dies = x_dies[xb_d..];
    M.dattrs = x_dattrs[xb_t..];
}

// The order functions are optimized in: callees before callers (a
// post-order of the call graph from every function, opt_order in
// opt_inline.goose; calls inside a cycle in any order).
var fn_order: u32[>..] = [];

// Passes switched off by the environment variable GOOVM_OPT (a list such as
// "-gvn,-inline": for bisecting; "-all" runs no pass at all).
var opt_verify_on = false;
var opt_env: u8[>..] = [];
var opt_env_read = false;
fn opt_off(name: const u8[:]) -> bool {
    if !opt_env_read {
        opt_env_read = true;
        opt_env.clear();
        if !env("GOOVM_OPT", opt_env) { opt_env.clear(); }
    }
    if opt_env.len == 0 { return false; }
    var w: u8[>..] = [];
    w.push('-');
    w.append(name);
    return find(opt_env, w) >= 0 || find(opt_env, "-all") >= 0;
}

// One round of the scalar passes.
fn opt_round() {
    ensure_cfg();
    if !opt_off("fold") {
        simplify();
        simplify_phis();
    }
    if !opt_off("gvn") { gvn(); }
    resolve_all();
    dce();
    if !opt_off("cfg") && simplify_cfg() { simplify_phis(); }
}

fn opt_dump_on() -> bool {
    opt_off("");    // (reads the variable)
    return find(opt_env, "dump") >= 0;
}

fn opt_function(fi: u32) {
    o_fi = fi;
    o_f = M.funcs[fi];
    o_pinned = fn_pinned[fi] != 0;
    oir_reset();
    amap_on = false;
    oir_load(M.insts, M.blocks, o_f, true);
    if o_f.flags & FN_OPTNONE != 0 {
        // optnone: not optimized (and -O0 code generation, cg.goose fn_opt)
        inl_record();
        oir_store(fi);
        return;
    }
    if !opt_off("m2r") {
        ensure_cfg();
        if remove_unreachable() { ensure_cfg(); }
        build_uses();
        if !opt_off("sroa") && sroa() {
            resolve_all();
            build_uses();
        }
        if mem2reg() { simplify_phis(); }
    }
    opt_round();
    if !opt_off("tre") && tail_recursion() { opt_round(); }
    if !opt_off("inline") && inl_any_call() {
        ensure_cfg();
        build_loops();
        if inline_calls() {
            resolve_all();
            ensure_cfg();
            if remove_unreachable() { ensure_cfg(); }
            opt_round();
            resolve_all();
            build_uses();
            if !opt_off("sroa") && sroa() {
                resolve_all();
                build_uses();
            }
            if mem2reg() { simplify_phis(); }
            opt_round();
        }
    }
    if !opt_off("lrot") && rotate_loops() {
        resolve_all();
        ensure_cfg();
        build_uses();
        if mem2reg() { simplify_phis(); }
    }
    opt_round();
    if !opt_off("licm") && licm() {
        if !opt_off("iv") && indvars() { licm(); }
        opt_round();
    }
    if !opt_off("gprom") && promote_globals() {
        resolve_all();
        ensure_cfg();
        build_uses();
        if mem2reg() { simplify_phis(); }
        opt_round();
    }
    if !opt_off("rotate") {
        ensure_cfg();
        rotate_layout();
    }
    if opt_verify_on { opt_verify(); }
    inl_record();
    oir_store(fi);
}
