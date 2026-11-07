// Register allocation (milestone A2): the state behind the value-location
// interface, the liveness pre-pass, and the allocator's primitives.
//
// One forward pass per function (`ra_prepass`) counts the uses of every
// value, finds whether it is used outside its block ("global") and, if not,
// its last use, and whether a call lies between its definition and its last
// use. Code generation then keeps values in registers:
//
//   - a local value lives in a register from its definition to its last use
//     (where the register is freed); it gets a frame slot only if it has to
//     be spilled (register pressure, or a call / legacy lowering clobbers
//     its register and no callee-saved register is free);
//   - a global value is stored to its home slot when it is defined
//     ("write-through", like LLVM's RegAllocFast for live-out values); a
//     register copy is a cache that is dropped at the end of the block;
//   - PHIs live in their home: the predecessors' edges write it;
//   - every block starts with all registers free (arguments are in their
//     registers at the start of the entry block).
//
// Register numbers: 0..15 general registers, 16..31 xmm0..15.

let NOREG: u8 = 0xFF;
let PEND: u8 = 0xFE;       // a deferred load (ra_pend): the value is in memory at pend[k].m
let PADDR: u8 = 0xFD;      // a deferred address (a GEP folded into the next load or store)
let RV_NONE: u32 = 0xFFFFFFFF;
let RV_TEMP: u32 = 0xFFFFFFFE;

let GP_ALLOC: u32 = 0xFFCF;    // rax..r15 minus rsp, rbp
let GP_CALLER: u32 = 0x0FC7;   // rax rcx rdx rsi rdi r8 r9 r10 r11
let GP_CALLEE: u32 = 0xF008;   // rbx r12 r13 r14 r15
let XMM_ALL: u32 = 0xFFFF0000;
let CS_REGS: u32[5] = [RBX, R12, R13, R14, R15];

// Value states (v_st).
let ST_MEM: u8 = 1;     // the home holds the value
let ST_GLOB: u8 = 2;    // used outside its block (v_last is not meaningful)
let ST_EXT: u8 = 4;     // the register copy has garbage above the value's width (8/16/32-bit INT)
let ST_CS: u8 = 8;      // a call lies between the definition and the last use
let ST_PHI: u8 = 16;    // a PHI: its home is written by the edges
let ST_NODEF: u8 = 32;  // a memory write lies between the definition and the use (no deferred load)

// Register classes of types.
let RC_MEM: u8 = 0;
let RC_GPR: u8 = 1;
let RC_XMM: u8 = 2;
let RC_VX: u8 = 3;    // vectors of 8 or 16 bytes: an xmm register

// Homes.
let H_NONE: u8 = 0;
let H_SLOT: u8 = 1;     // v_off is the rbp offset of the value's slot
let H_ALLOCA: u8 = 2;   // the value is the address rbp + v_off (static alloca)
let H_PTR: u8 = 3;      // the value is the pointer stored at rbp + v_off (over-aligned alloca)
let H_BYVAL: u8 = 4;    // argument: the value is the address rbp + v_off of the caller's copy
let H_STACK: u8 = 5;    // argument passed on the stack: its home is the incoming slot at rbp + v_off

var r_val: u32[32] = [0xFFFFFFFF; 32];   // value held by each register (RV_NONE, RV_TEMP)
var r_free: u32 = 0;     // allocatable registers that hold nothing
var r_lock: u32 = 0;     // registers the current instruction uses (not evictable)
var r_temp: u32 = 0;     // scratch registers of the current instruction
var r_alloc: u32 = 0;    // the registers this function may allocate
var r_cs_used: u32 = 0;  // callee-saved registers that were allocated (the prologue saves them)
var ra_carry = false;    // the current instruction's registers stay locked into the next one

// Per value (id: local instruction index, or f_nins + argument number):
//   reg   the register holding it (0..31), NOREG, PEND or PADDR
//   st    ST_* state bits
//   home  H_* kind of home; off: its rbp offset (0 = none yet)
//   nuse  uses (saturating at 255)
//   ncl   calls and legacy lowerings before it in its block (saturating)
//   kind  for instructions: how it is lowered (K_*)
//   hint  the register its (only) use wants it in: a return value, a call argument
//   nev   uses by an extractvalue in its block (saturating): an aggregate call
//         result whose uses are all extractvalues gets their values in its
//         return registers (call_result)
//   last  last use (local position), for values used only in their block
struct VInfo { reg: u8, st: u8, home: u8, nuse: u8, ncl: u8, kind: u8, hint: u8, nev: u8, last: u32, off: i32 }
var vi: VInfo[>..] = [];
var t_off: i32[>..] = [];       // PHI temp slots (blocks that need them)
var b_tag: u32[>..] = [];       // per local block: == pp_epoch if its PHIs need temp slots
var f_nins: u32 = 0;
var pp_epoch: u32 = 0;          // advances per function (b_tag)
var cur_pos: u32 = 0;           // local index of the instruction being lowered
var dying: u32[>..] = [];       // values whose last use is the current instruction

// Deferred loads (single-use loads from frame or rip-relative addresses,
// materialized or folded at their use) and the deferred address of a GEP.
struct Pend { id: u32, m: Mem }
var pend: Pend[>..] = [];
var n_pend: i64 = 0;          // entries of pend in use
var paddr_m: Mem = Mem { M_REG, 0, 0, 0, 0 };
// A compare whose flags feed the next instruction (CONDBR, SELECT).
var flags_id: u32 = 0xFFFFFFFF;
var flags_cc: u32 = 0;
var flags_cc2: u32 = 0;
var flags_comb: u32 = 0;        // FCMP: 0 = cc only, 1 = cc && cc2, 2 = cc || cc2

// Per-function facts from the pre-pass.
var pp_ncs: u32 = 0;            // local values that span a call
var f_call = false;             // calls something (not a leaf)
var f_rsp = false;              // moves rsp in the body (dynamic alloca, stack restore, inline asm)
var f_asm = false;              // contains inline assembly (may clobber any register)
var f_share = true;             // frame slots of dead values may be reused

// Frame slots.
var lay_off: i64 = 0;           // bytes below rbp so far
var free8: i32[>..] = [];
var free16: i32[>..] = [];
var n_free8: i64 = 0;
var n_free16: i64 = 0;

// Register classes by type id (per module).
var t_rc: u8[>..] = [];

checkfree fn bit(r: u32) -> u32 { (1 as u32) << (r & 31) }
inline fn ctz32(m: u32) -> u32 { ctz(m) as! u32 }

fn build_type_rc() {
    t_rc.clear();
    for T in M.types {
        var rc: u8 = RC_MEM;
        if T.cls == C_INT { rc = RC_GPR; }
        else if T.cls == C_FP && T.bits != 16 { rc = RC_XMM; }
        else if T.cls == C_VEC && T.n >= 2 && (T.store == 16 || T.store == 8) {
            let L = M.types[T.elems];
            if L.cls == C_INT && (L.bits == 8 || L.bits == 16 || L.bits == 32 || L.bits == 64) && L.size * T.n == T.store
               || L.cls == C_FP && (L.bits == 32 || L.bits == 64) {
                rc = RC_VX;
            }
        }
        t_rc.push(rc);
    }
}
inline fn rc_of(t: u32) -> u8 { t_rc[t] }
inline fn in_xmm(c: u8) -> bool { c >= RC_XMM }

// Moves between an xmm register and memory for a value of type t (f32, f64
// or a register-resident vector).
fn xmm_load_t(x: u32, m: Mem, t: u32) {
    if t == GIR_T_F32 { movss_load(x, m); }
    else if t == GIR_T_F64 { movsd_load(x, m); }
    else if M.types[t].store == 16 { movups_load(x, m); }
    else { movq_load(x, m); }
}
fn xmm_store_t(m: Mem, x: u32, t: u32) {
    if t == GIR_T_F32 { movss_store(m, x); }
    else if t == GIR_T_F64 { movsd_store(m, x); }
    else if M.types[t].store == 16 { movups_store(m, x); }
    else { movq_store(m, x); }
}

inline fn is_val(v: u32) -> bool { gir_kind(v) <= GIR_V_ARG }
inline fn vid(v: u32) -> u32 {
    if gir_kind(v) == GIR_V_INST { return gir_idx(v) - f_first_inst; }
    return f_nins + gir_idx(v);
}
inline fn vtype(id: u32) -> u32 {
    if id < f_nins { return M.insts[f_first_inst + id].ty; }
    return M.opnds[f_args + 2 * (id - f_nins)];
}

// --------------------------------------------------------------- pre-pass

// Per opcode: value operands (U_*), whether the instruction writes memory
// that a load may read (W), and how it is lowered (K_*).
let U_A = 1;
let U_B = 2;
let U_C = 4;
let U_GEP = 8;
let U_CALL = 16;
let U_ASM = 64;
let OP_USES: u8[84] = [
    1, 0, 1, 1, 0, 3, 3, 3,  // ret br condbr switch unreachable add sub mul
    3, 3, 3, 3, 3, 3, 3, 3,  // sdiv udiv srem urem and or xor shl
    3, 3, 3, 7, 1, 1, 1, 1,  // lshr ashr icmp select zext sext trunc ptrtoint
    1, 1, 0, 1, 3, 9, 17, 0,  // inttoptr bitcast alloca load store gep call phi
    3, 3, 3, 3, 1, 3, 1, 1,  // fadd fsub fmul fdiv fneg fcmp fpext fptrunc
    1, 1, 1, 1, 1, 3, 3, 7,  // fptosi fptoui sitofp uitofp extractvalue insertvalue extractelt insertelt
    3, 1, 0, 1, 1, 3, 3, 1,  // shuffle dynalloca stacksave stackrestore vastart memcpy memset ctlz
    1, 1, 1, 1, 7, 7, 3, 3,  // cttz ctpop bswap bitreverse fshl fshr ovf scmp
    3, 1, 3, 1, 1, 7, 3, 0,  // ucmp fabs copysign fsqrt isfpclass cmpxchg atomicrmw fence
    0, 0, 0, 1, 1, 0, 0, 1,  // tlsaddr frameaddr retaddr sjlj_setjmp sjlj_longjmp trap debugtrap indirectbr
    0, 3, 64, 0,  // blockaddr x86 asm landingpad
];
// Lowering kinds: K_A allocator-aware; K_T allocator-aware if the result
// (or compared/stored/source) type is in a register class, else legacy;
// K_B legacy (clobbers the caller-saved registers); K_CALL a call; K_ALL
// clobbers every register (sjlj setjmp, inline asm). +16: writes memory.
let K_A = 0;
let K_T = 1;
let K_B = 2;
let K_CALL = 3;
let K_ALL = 4;
let K_DONE = 5;    // an extractvalue whose value the call before it defined (call_result)
let K_W = 16;
let OP_KIND: u8[84] = [
    0, 0, 0, 0, 0, 1, 1, 1,  // ret br condbr switch unreachable add sub mul
    1, 1, 1, 1, 1, 1, 1, 1,  // sdiv udiv srem urem and or xor shl
    1, 1, 1, 1, 1, 1, 1, 1,  // lshr ashr icmp select zext sext trunc ptrtoint
    1, 1, 0, 1, 17, 0, 19, 0,  // inttoptr bitcast alloca load store gep call phi
    1, 1, 1, 1, 1, 1, 1, 1,  // fadd fsub fmul fdiv fneg fcmp fpext fptrunc
    1, 1, 1, 1, 1, 2, 1, 1,  // fptosi fptoui sitofp uitofp extractvalue insertvalue extractelt insertelt
    2, 2, 2, 2, 18, 16, 16, 2,  // shuffle dynalloca stacksave stackrestore vastart memcpy memset ctlz
    2, 2, 2, 2, 2, 2, 2, 2,  // cttz ctpop bswap bitreverse fshl fshr ovf scmp
    2, 1, 1, 1, 1, 18, 18, 18,  // ucmp fabs copysign fsqrt isfpclass cmpxchg atomicrmw fence
    2, 2, 2, 20, 18, 0, 0, 0,  // tlsaddr frameaddr retaddr sjlj_setjmp sjlj_longjmp trap debugtrap indirectbr
    2, 2, 20, 2,  // blockaddr x86 asm landingpad
];

// How instruction I is lowered: K_A, K_B, K_CALL or K_ALL.
fn inst_kind(I: Inst) -> u32 {
    let op: u32 = I.op;
    if op >= GIR_NOPS { return K_B; }
    let k: u32 = OP_KIND[op] & 15;
    if k != K_T { return k; }
    if op == GIR_EXTRACTVALUE { return ev_kind(I.ty); }
    if op == GIR_ISFPCLASS {
        return if (I.aux == GIR_T_F32 || I.aux == GIR_T_F64) && fpclass_fast(I.b) { K_A } else { K_B };
    }
    // the type that decides: the compared / stored / cast source type, or the result
    var t: u32 = I.ty;
    if op == GIR_ICMP || op == GIR_FCMP || op == GIR_STORE { t = I.aux; }
    if op == GIR_EXTRACTELT { t = I.aux; }
    let rc = t_rc[t];
    if rc == RC_MEM { return K_B; }
    if rc == RC_VX { return vx_kind(I, op, t); }
    if op < GIR_ZEXT { return K_A; }   // binops, icmp
    return inst_kind2(I, op, t, rc);
}
// extractvalue of a field of a register class is a load from the aggregate's
// memory (INT fields whose store size is their register width: no odd sizes).
fn ev_kind(t: u32) -> u32 {
    let rc = t_rc[t];
    if in_xmm(rc) { return K_A; }
    if rc == RC_GPR && store_of(t) == int_bytes(bits_of(t)) { return K_A; }
    return K_B;
}
// Operations on vectors that live in xmm registers; the others are legacy
// (lane by lane in memory).
fn vx_kind(I: Inst, op: u32, t: u32) -> u32 {
    let L = M.types[M.types[t].elems];
    let lfp = L.cls == C_FP;
    let lb: u32 = L.bits;
    if op == GIR_LOAD || op == GIR_STORE { return K_A; }
    if op >= GIR_FADD && op <= GIR_FDIV || op == GIR_FNEG || op == GIR_FABS { return if lfp { K_A } else { K_B }; }
    if op == GIR_ADD || op == GIR_SUB || op == GIR_AND || op == GIR_OR || op == GIR_XOR { return if lfp { K_B } else { K_A }; }
    if op == GIR_MUL { return if !lfp && lb == 16 { K_A } else { K_B }; }
    if op == GIR_INSERTELT { return if gir_kind(I.c) == GIR_V_CONST && lb != 8 { K_A } else { K_B }; }
    if op == GIR_EXTRACTELT { return if gir_kind(I.b) == GIR_V_CONST && lb != 8 { K_A } else { K_B }; }
    if op == GIR_BITCAST {
        let o = rc_of(I.aux);
        if o == RC_MEM || size_of(I.ty) != size_of(I.aux) { return K_B; }
        return K_A;
    }
    if op == GIR_SELECT { return if rc_of(type_of(I.a)) == RC_GPR { K_A } else { K_B }; }
    return K_B;
}
fn inst_kind2(I: Inst, op: u32, t: u32, rc: u8) -> u32 {
    if op >= GIR_ZEXT && op <= GIR_BITCAST || op >= GIR_FPEXT && op <= GIR_UITOFP {
        let o = rc_of(I.aux);
        if o == RC_MEM { return K_B; }
        if o == RC_VX && (op != GIR_BITCAST || size_of(I.ty) != size_of(I.aux)) { return K_B; }
        return K_A;
    }
    if op == GIR_SELECT && rc_of(type_of(I.a)) == RC_MEM { return K_B; }  // vector condition
    if (op == GIR_LOAD || op == GIR_STORE) && t > GIR_T_F64 && rc == RC_GPR { return K_B; }  // odd-size integers
    return K_A;
}

// A use at local position j of block [lo, j]; ncl = calls in the block
// before j, mw = 1 + position of the last memory write before j in the
// block (0: none); nodef: the user is a legacy lowering (it gets no
// deferred load).
inline fn pp_use(v: u32, j: u32, lo: u32, ncl: u32, mw: u32, nodef: bool) {
    let k = gir_kind(v);
    if k > GIR_V_ARG { return; }
    var u: u32 = 0;
    var local = false;
    if k == GIR_V_INST {
        u = gir_idx(v) - f_first_inst;
        if u >= f_nins { return; }   // (not an instruction of this function: an unused 0 operand)
        local = u >= lo && u < j;
    } else {
        u = f_nins + gir_idx(v);
        local = lo == 0;
    }
    pp_use2(u, j, local, ncl, nodef || mw > u);
}
fn pp_use2(u: u32, j: u32, local: bool, ncl: u32, nodef: bool) {
    if vi[u].home == H_ALLOCA { return; }   // (marked before the walk; addresses are rematerialized)
    let n = vi[u].nuse;
    if n != 255 { vi[u].nuse = n + 1; }
    if local {
        vi[u].last = j;
        var st = vi[u].st;
        if ncl > vi[u].ncl && st & ST_CS == 0 {
            st |= ST_CS;
            pp_ncs++;
        }
        if nodef { st |= ST_NODEF; }
        vi[u].st = st;
    } else {
        vi[u].st |= ST_GLOB;
    }
}
// PHI incoming values of successor s for the edge from block b (used at b's
// terminator, position j). A PHI of s that reads another PHI of s, and the
// PHIs of indirectbr targets (written before the jump, for every target),
// need the temp-slot scheme (parallel copy).
fn pp_phi_uses(s: u32, b: u32, j: u32, lo: u32, ncl: u32, mw: u32, all: bool) {
    let B = M.blocks[f_first_block + s];
    let slo = B.first_inst;
    let shi = B.first_inst + B.n_inst;
    if shi == slo || M.insts[slo].op != GIR_PHI { return; }
    if all { b_tag[s] = pp_epoch; }
    for k in slo..shi {
        let I = M.insts[k];
        if I.op != GIR_PHI { break; }
        for p in 0..I.c {
            if M.opnds[I.b + 2 * p + 1] == b {
                let v = M.opnds[I.b + 2 * p];
                pp_use(v, j, lo, ncl, mw, false);
                if gir_kind(v) == GIR_V_INST {
                    let g = gir_idx(v);
                    if g >= slo && g < shi && g != k && M.insts[g].op == GIR_PHI { b_tag[s] = pp_epoch; }
                }
                break;
            }
        }
    }
}

fn pp_runs(I: Inst, m: u32, j: u32, lo: u32, ncl: u32, mw: u32, nodef: bool) {
    if m & U_GEP != 0 {
        for k in 0..I.c { pp_use(M.opnds[I.b + 2 + 2 * k], j, lo, ncl, mw, nodef); }
    } else if m & U_CALL != 0 {
        for k in 0..I.c { pp_use(M.opnds[I.b + 2 * k], j, lo, ncl, mw, nodef); }
    } else {
        let A = M.asms[I.a];
        for q in 0..A.n_in { pp_use(M.opnds[A.ops + 2 * q], j, lo, ncl, mw, true); }
    }
}
// Register hints: a value used by a return or as a plain call argument is
// computed in that register if it is free.
fn pp_hint(v: u32, r: u32) {
    if gir_kind(v) != GIR_V_INST { return; }
    let u = gir_idx(v) - f_first_inst;
    if u >= f_nins { return; }
    let c = rc_of(M.insts[f_first_inst + u].ty);
    if c == RC_GPR { pp_gpr_hint(u, r); }
    else if in_xmm(c) && r == RAX { vi[u].hint = 16; }
}
// General register r for u, and for the operand of u if u is an integer /
// pointer conversion of it (`(void *)(long)x` as an argument).
fn pp_gpr_hint(u: u32, r: u32) {
    vi[u].hint = r as! u8;
    let I = M.insts[f_first_inst + u];
    let op: u32 = I.op;
    if op == GIR_INTTOPTR || op == GIR_PTRTOINT || op == GIR_BITCAST || op == GIR_TRUNC || op == GIR_ZEXT {
        if gir_kind(I.a) != GIR_V_INST { return; }
        let w = gir_idx(I.a) - f_first_inst;
        if w < u && rc_of(M.insts[f_first_inst + w].ty) == RC_GPR { vi[w].hint = r as! u8; }
    }
}
fn pp_call_hints(I: Inst) {
    var gp: u32 = 0;
    var fp: u32 = 0;
    for k in 0..I.c {
        let v = M.opnds[I.b + 2 * k];
        if M.opnds[I.b + 2 * k + 1] != 0 { return; }
        let c = rc_of(type_of(v));
        if c == RC_GPR {
            if gp == 6 { return; }
            if gir_kind(v) == GIR_V_INST {
                let u = gir_idx(v) - f_first_inst;
                if u < f_nins { pp_gpr_hint(u, ARG_GPR[gp]); }
            }
            gp++;
        } else if in_xmm(c) {
            if fp == 8 { return; }
            if gir_kind(v) == GIR_V_INST {
                let u = gir_idx(v) - f_first_inst;
                if u < f_nins { vi[u].hint = (16 + fp) as! u8; }
            }
            fp++;
        } else {
            return;
        }
    }
}
fn pp_term(I: Inst, op: u32, b: u32, j: u32, lo: u32, ncl: u32, mw: u32) {
    if op == GIR_BR { pp_phi_uses(I.a, b, j, lo, ncl, mw, false); }
    else if op == GIR_CONDBR {
        pp_phi_uses(I.b, b, j, lo, ncl, mw, false);
        pp_phi_uses(I.c, b, j, lo, ncl, mw, false);
    } else if op == GIR_SWITCH {
        pp_phi_uses(M.opnds[I.b], b, j, lo, ncl, mw, false);
        for k in 0..I.c { pp_phi_uses(M.opnds[I.b + 2 + 2 * k], b, j, lo, ncl, mw, false); }
    } else if op == GIR_INDIRECTBR {
        for k in 0..I.c { pp_phi_uses(M.opnds[I.b + k], b, j, lo, ncl, mw, true); }
    }
}

fn ra_prepass(insts: const Inst[:], blocks: const Block[:]) {
    pp_epoch++;
    pp_ncs = 0;
    f_call = false;
    f_rsp = false;
    f_asm = false;
    let nv: i64 = f_nins as i64 + f_nargs;
    assert(vi.len >= nv);
    let z = VInfo { reg: NOREG, st: 0, home: H_NONE, nuse: 0, ncl: 0, kind: 0, hint: NOREG, nev: 0, last: 0, off: 0 };
    for q in 0..nv { vi[q] = z; }
    // static allocas (entry block): their uses need no bookkeeping
    let E = blocks[0];
    for gi in E.first_inst..E.first_inst + E.n_inst {
        if M.insts[gi].op == GIR_ALLOCA { vi[gi - f_first_inst].home = H_ALLOCA; }
    }
    for B, b in blocks {
        let lo = B.first_inst - f_first_inst;
        let hi = lo + B.n_inst;
        var ncl: u32 = 0;
        var mw: u32 = 0;
        var j = lo;
        while j < hi {
            let I = insts[j];
            let op: u32 = I.op;
            let kd: u32 = if op < GIR_NOPS { OP_KIND[op] } else { K_B };
            var k2 = kd & 15;
            if k2 == K_T { k2 = inst_kind(I); }
            let nodef = k2 == K_B || k2 == K_ALL;
            let m: u32 = if op < GIR_NOPS { OP_USES[op] } else { U_A | U_B | U_C };
            if m & U_A != 0 { pp_use(I.a, j, lo, ncl, mw, nodef); }
            if m & U_B != 0 { pp_use(I.b, j, lo, ncl, mw, nodef); }
            if m & U_C != 0 { pp_use(I.c, j, lo, ncl, mw, nodef); }
            if m >= U_GEP { pp_runs(I, m, j, lo, ncl, mw, nodef); }
            if op == GIR_RET { pp_hint(I.a, RAX); }
            else if op == GIR_CALL { pp_call_hints(I); }
            else if op == GIR_EXTRACTVALUE && gir_kind(I.a) == GIR_V_INST {
                let u = gir_idx(I.a) - f_first_inst;
                if u >= lo && u < j && vi[u].nev != 255 { vi[u].nev++; }
            }
            if op <= GIR_SWITCH || op == GIR_INDIRECTBR { pp_term(I, op, b as! u32, j, lo, ncl, mw); }
            // the instruction itself
            if kd & K_W != 0 { mw = j + 1; }
            if k2 != K_A {
                ncl++;
                if k2 == K_CALL || op == GIR_TLSADDR { f_call = true; }
                if k2 == K_ALL { f_asm = true; }
                if op == GIR_DYNALLOCA || op == GIR_STACKRESTORE { f_rsp = true; }
            }
            vi[j].kind = k2 as! u8;
            if I.ty != GIR_T_VOID {
                vi[j].last = j;
                vi[j].ncl = if ncl > 255 { 255 } else { ncl as! u8 };
                if op == GIR_PHI {
                    vi[j].st |= ST_PHI;
                    t_off[j] = 0;
                }
            }
            j++;
        }
    }
}

// --------------------------------------------------------------- frame slots

// A fresh slot of sz bytes (16-aligned from 16 bytes on).
fn new_slot(sz: i64) -> i32 {
    if sz >= 16 { lay_off = (lay_off + sz + 15) & ~15; }
    else { lay_off = ((lay_off + 7) & ~7) + sz; }
    return (-lay_off) as! i32;
}
// Slot size of a value of type t: INT and FP 8, INT2 and X87 16, else the
// allocation size rounded up to 8.
fn slot_size(t: u32) -> i64 {
    let c = cls_of(t);
    if c == C_INT || c == C_FP { return 8; }
    if c == C_INT2 || c == C_X87 { return 16; }
    let s: i64 = size_of(t);
    if s == 0 { return 8; }
    return (s + 7) & ~7;
}
fn slot_align(t: u32) -> i64 { if slot_size(t) >= 16 { 16 } else { 8 } }
inline fn val_slot_size(t: u32) -> i64 { if t > GIR_T_F64 { slot_size(t) } else { 8 } }

// The home slot of value id (allocated on first use). Local values reuse
// slots of dead local values.
fn ra_home_off(id: u32) -> i32 {
    let o = vi[id].off;
    if o != 0 { return o; }
    let sz = val_slot_size(vtype(id));
    var n: i32 = 0;
    if f_share && vi[id].st & (ST_GLOB | ST_PHI) == 0 {
        if sz == 8 && n_free8 != 0 {
            n_free8--;
            n = free8[n_free8];
        } else if sz == 16 && n_free16 != 0 {
            n_free16--;
            n = free16[n_free16];
        }
    }
    if n == 0 { n = new_slot(sz); }
    vi[id].off = n;
    vi[id].home = H_SLOT;
    return n;
}
inline fn ra_home(id: u32) -> Mem { m_rbp(ra_home_off(id)) }
fn ra_free_slot(id: u32) {
    let o = vi[id].off;
    let sz = val_slot_size(vtype(id));
    if sz == 8 {
        if n_free8 < free8.len { free8[n_free8] = o; } else { free8.push(o); }
        n_free8++;
    } else if sz == 16 {
        if n_free16 < free16.len { free16[n_free16] = o; } else { free16.push(o); }
        n_free16++;
    }
    vi[id].off = 0;
}

// ------------------------------------------------- typed home loads/stores

// Bytes a register value of `bits` bits occupies in memory (1, 2, 4, 8).
checkfree fn int_bytes(bits: u32) -> u32 {
    if bits <= 8 { return 1; }
    if bits <= 16 { return 2; }
    if bits <= 32 { return 4; }
    return 8;
}
// Zero-extending load / store of an INT value of `bits` bits.
checkfree fn load_int(r: u32, m: Mem, bits: u32) {
    let n = int_bytes(bits);
    if n == 1 { load8z(r, m); }
    else if n == 2 { load16z(r, m); }
    else if n == 4 { load32(r, m); }
    else { load64(r, m); }
}
checkfree fn store_int(m: Mem, r: u32, bits: u32) {
    let n = int_bytes(bits);
    if n == 1 { store8(m, r); }
    else if n == 2 { store16(m, r); }
    else if n == 4 { store32(m, r); }
    else { store64(m, r); }
}
// Width flag of an operation on `bits`-bit values: 1 = 64-bit operand size.
checkfree fn wq(bits: u32) -> u32 { if bits > 32 { 1 } else { 0 } }
// Exact register widths (8, 16, 32, 64) may carry garbage above the width;
// odd widths are always kept zero-extended.
checkfree fn exact_width(bits: u32) -> bool { bits == 8 || bits == 16 || bits == 32 || bits == 64 }

// Stores register r (value id) to its home.
fn ra_store_home(id: u32, r: u32) {
    let t = vtype(id);
    let m = ra_home(id);
    if r >= 16 { xmm_store_t(m, r - 16, t); }
    else { store_int(m, r, bits_of(t)); }
    vi[id].st |= ST_MEM;
}
// Loads value id from memory m into register r (marks nothing).
fn ra_load_from(r: u32, m: Mem, t: u32) {
    if r >= 16 { xmm_load_t(r - 16, m, t); }
    else { load_int(r, m, bits_of(t)); }
}

// --------------------------------------------------------------- allocation

fn ra_live_after(id: u32) -> bool {
    if vi[id].st & ST_PIN != 0 { return rg_live_after(id); }
    return vi[id].st & ST_GLOB != 0 || vi[id].last > cur_pos;
}
inline fn ra_note(id: u32) {
    if vi[id].st & ST_GLOB == 0 && vi[id].last == cur_pos { dying.push(id); }
}
// Preferred registers for value id: callee-saved ones if it lives across a call.
fn ra_pref(id: u32) -> u32 {
    if vi[id].st & (ST_CS | ST_GLOB) == ST_CS { return GP_CALLEE; }
    return GP_CALLER;
}

// Frees a register that holds nothing the program needs.
inline fn ra_release(r: u32) {
    r_val[r] = RV_NONE;
    r_free |= bit(r);
}
// Picks a register of class mask xm, preferring pref; evicts one if none is
// free. The register is locked for the current instruction; the caller
// records what it holds.
fn ra_alloc(xm: u32, pref: u32) -> u32 {
    let avail = r_free & ~r_lock & xm;
    var c = avail & pref;
    if c == 0 { c = avail; }
    var r: u32 = 0;
    if c != 0 { r = ctz32(c); } else { r = ra_evict(xm); }
    r_free &= ~bit(r);
    r_lock |= bit(r);
    if bit(r) & GP_CALLEE != 0 { r_cs_used |= bit(r); }
    return r;
}
// Frees a register of class xm by spilling the value whose next use is the
// farthest (a value that is also in its home costs nothing).
fn ra_evict(xm: u32) -> u32 {
    var m = ~r_free & ~r_lock & xm & r_alloc & ~rg_pin;   // (pinned global values stay)
    if m == 0 && rg_on { return rg_borrow(xm); }
    if m == 0 { assert(false); }   // every register is locked: a lowering asks for too many
    var best: u32 = 32;
    var best_last: u32 = 0;
    while m != 0 {
        let r = ctz32(m);
        m &= m - 1;
        let id = r_val[r];
        if id >= RV_TEMP { continue; }
        if vi[id].st & ST_MEM != 0 {
            best = r;
            break;
        }
        let l = vi[id].last;
        if best == 32 || l > best_last {
            best = r;
            best_last = l;
        }
    }
    if best == 32 { assert(false); }
    let id = r_val[best];
    if vi[id].st & ST_MEM == 0 { ra_store_home(id, best); }
    vi[id].reg = NOREG;
    r_val[best] = RV_NONE;
    return best;
}
// A scratch register (freed at the end of the instruction).
fn ra_temp() -> u32 {
    let r = ra_alloc(GP_ALLOC, GP_CALLER);
    r_val[r] = RV_TEMP;
    r_temp |= bit(r);
    return r;
}
fn ra_xtemp() -> u32 {
    let r = ra_alloc(XMM_ALL, XMM_ALL);
    r_val[r] = RV_TEMP;
    r_temp |= bit(r);
    return r - 16;
}
// Value id leaves register `from` (which the instruction will overwrite): it
// moves to a free register of the same class, or to its home.
fn ra_evacuate(id: u32, from: u32) {
    let xm: u32 = if from >= 16 { XMM_ALL } else { GP_ALLOC };
    let avail = r_free & ~r_lock & xm & r_alloc & ~bit(from);
    if avail != 0 {
        var c = avail & ra_pref(id);
        if c == 0 { c = avail; }
        let to = ctz32(c);
        if from >= 16 { movaps_rr(to - 16, from - 16); } else { mov_rr64(to, from); }
        r_free &= ~bit(to);
        if bit(to) & GP_CALLEE != 0 { r_cs_used |= bit(to); }
        r_val[to] = id;
        vi[id].reg = to as! u8;
        if r_lock & bit(from) != 0 { r_lock |= bit(to); }
    } else {
        if vi[id].st & ST_MEM == 0 { ra_store_home(id, from); }
        vi[id].reg = NOREG;
    }
    r_val[from] = RV_NONE;
    r_free |= bit(from);
}
// The current instruction overwrites register r: r's value is moved away,
// and r becomes a scratch register of the instruction.
fn ra_clobber(r: u32) {
    let occ = r_val[r];
    if occ < RV_TEMP { ra_evacuate(occ, r); }
    r_free &= ~bit(r);
    r_val[r] = RV_TEMP;
    r_temp |= bit(r);
    r_lock |= bit(r);
}

// Spills every register in mask whose value is not in its home (and forgets
// the register copies). Used before calls and legacy lowerings.
fn ra_flush(mask: u32) {
    var m = ~r_free & r_alloc & mask;
    while m != 0 {
        let r = ctz32(m);
        m &= m - 1;
        let id = r_val[r];
        if id >= RV_TEMP { continue; }
        if vi[id].st & ST_MEM == 0 { ra_store_home(id, r); }
        vi[id].reg = NOREG;
        ra_release(r);
    }
}

// Normalizes the register copy of value id (zero-extends it).
fn ra_norm(id: u32, r: u32) {
    zext_reg(r, bits_of(vtype(id)));
    vi[id].st &= ~ST_EXT;
}

// ------------------------------------------------------ deferred loads

fn ra_pend_add(id: u32, m: Mem) {
    if n_pend < pend.len { pend[n_pend] = Pend { id: id, m: m }; } else { pend.push(Pend { id: id, m: m }); }
    n_pend++;
    vi[id].reg = PEND;
}
// The memory of deferred load id (removes it).
fn ra_take_pend(id: u32) -> Mem {
    var k: i64 = 0;
    let n = n_pend;
    while k < n {
        if pend[k].id == id { break; }
        k++;
    }
    if k == n { assert(false); }
    let m = pend[k].m;
    pend[k] = pend[n - 1];
    n_pend = n - 1;
    vi[id].reg = NOREG;
    return m;
}

// ================================================ the allocator-aware interface

// Materializes a non-register INT value (constant, global, alloca or argument
// address, deferred load, home) into register r.
fn ra_mat_gpr(v: u32, r: u32) {
    let k = gir_kind(v);
    let i = gir_idx(v);
    if k == GIR_V_CONST {
        let c = M.consts[i];
        if c.ty <= GIR_T_PTR || cls_of(c.ty) == C_INT { mov_ri(r, c.lo); }
        else { load_n(r, const_mem(i), size_of(c.ty)); }  // the bits of a small FP/vector constant
        return;
    }
    if k == GIR_V_GLOBAL {
        global_addr(r, i);
        return;
    }
    let id = vid(v);
    let h = vi[id].home;
    if h == H_ALLOCA || h == H_BYVAL {
        lea64(r, m_rbp(vi[id].off));
        return;
    }
    let t = vtype(id);
    if vi[id].reg == PEND {
        if dbg_on { dbg_ld(id); }
        load_int(r, ra_take_pend(id), bits_of(t));
        if dbg_on { dbg_ld_end(); }
        return;
    }
    if h == H_STACK {
        load_int(r, m_rbp(vi[id].off), bits_of(t));
        if !exact_width(bits_of(t)) { zext_reg(r, bits_of(t)); }
        return;
    }
    load_int(r, ra_home(id), bits_of(t));
}
// INT value v in a general register (locked); returns the register. With
// `clean`, the register is zero-extended above the value's width.
fn ra_gpr(v: u32, clean: bool) -> u32 {
    if is_val(v) {
        let id = vid(v);
        let r: u32 = vi[id].reg;
        if r < 32 {
            if r >= 16 { assert(false); }   // an xmm value: a register class mix-up
            r_lock |= bit(r);
            ra_note(id);
            if clean && vi[id].st & ST_EXT != 0 { ra_norm(id, r); }
            return r;
        }
        let h = vi[id].home;
        if h == H_ALLOCA || h == H_BYVAL {
            let t = ra_temp();
            lea64(t, m_rbp(vi[id].off));
            return t;
        }
        let n = ra_alloc(GP_ALLOC, ra_pref(id));
        if r == PEND { vi[id].st &= ~ST_MEM; }
        ra_mat_gpr(v, n);
        r_val[n] = id;
        vi[id].reg = n as! u8;
        ra_note(id);
        return n;
    }
    let t = ra_temp();
    ra_mat_gpr(v, t);
    return t;
}
// v into exactly register r, which the instruction then owns (r is
// overwritten by the instruction; v keeps its own register if it lives on).
fn ra_gpr_into(v: u32, r: u32, clean: bool) {
    var src: u32 = 32;
    var id: u32 = RV_NONE;
    if is_val(v) {
        id = vid(v);
        let vr: u32 = vi[id].reg;
        if vr < 32 { src = vr; }
    }
    let occ = r_val[r];
    if src == r {
        // v is already in r: keep a copy elsewhere if v lives on
        if ra_live_after(id) {
            ra_evacuate(id, r);
            r_free &= ~bit(r);
            r_val[r] = RV_TEMP;
            r_temp |= bit(r);
        }
        r_lock |= bit(r);
        ra_note(id);
        if clean && vi[id].st & ST_EXT != 0 {
            zext_reg(r, bits_of(vtype(id)));
            if vi[id].reg == r as! u8 { vi[id].st &= ~ST_EXT; }
        }
        return;
    }
    if occ < RV_TEMP { ra_evacuate(occ, r); }
    r_free &= ~bit(r);
    r_val[r] = RV_TEMP;
    r_temp |= bit(r);
    r_lock |= bit(r);
    if src < 32 {
        mov_rr64(r, src);
        r_lock |= bit(src);
        ra_note(id);
        if clean && vi[id].st & ST_EXT != 0 { zext_reg(r, bits_of(vtype(id))); }
        return;
    }
    if id != RV_NONE { ra_note(id); }
    ra_mat_gpr(v, r);
}
// A register for the INT result of j (locked; recorded by ra_set).
fn ra_def(j: u32) -> u32 {
    if rg_on && rg_reg[j] != NOREG {
        // a pinned value is computed in its register (reserved by rg_def_start)
        let r: u32 = rg_reg[j];
        r_lock |= bit(r);
        return r;
    }
    let h: u32 = vi[j].hint;
    if h < 16 && vi[j].st & (ST_CS | ST_GLOB) == 0 && r_free & ~r_lock & bit(h) != 0 {
        return ra_alloc(GP_ALLOC, bit(h));
    }
    return ra_alloc(GP_ALLOC, ra_pref(j));
}
// Whether ra_def(j) would give j its hint register: a three-operand form
// (lea, imul, movsx, a load) then writes the result there instead of into a
// dying operand's register, which saves the copy at the call or return.
fn hint_free(j: u32) -> bool {
    if rg_on && rg_reg[j] != NOREG { return true; }   // (ra_def gives its register)
    let h: u32 = vi[j].hint;
    return h < 16 && vi[j].st & (ST_CS | ST_GLOB) == 0 && r_free & ~r_lock & bit(h) != 0;
}
// The register of operand v if the result may take it over: v is a local
// value whose last use is this instruction and it is in a register.
fn ra_reuse(v: u32) -> u32 {
    if !is_val(v) { return 32; }
    let id = vid(v);
    let r: u32 = vi[id].reg;
    if r >= 32 { return 32; }
    if vi[id].st & ST_GLOB != 0 || vi[id].last != cur_pos { return 32; }
    return r;
}
// ra_reuse, or the scratch register r that ra_gpr built a non-value
// operand in (a constant, a global or alloca address): r is the operand's
// register and the result may take it over.
fn ra_reuse2(v: u32, r: u32) -> u32 {
    if r < 32 && r_temp & bit(r) != 0 { return r; }
    return ra_reuse(v);
}
// The result of j is in register r (a general or an xmm register, 0..31);
// ext: it has garbage above its width. Global values are written to their
// home at once; a result nobody uses is dropped.
fn ra_set(j: u32, r0: u32, ext0: bool) {
    var r = r0;
    var ext = ext0;
    if rg_on && vi[j].st & ST_PIN != 0 {
        // a pinned value goes to its register, normalized
        let pr: u32 = rg_reg[j];
        if r != pr {
            if pr >= 16 { movaps_rr(pr - 16, r - 16); } else { mov_rr64(pr, r); }
            if r_temp & bit(r) == 0 && r_val[r] >= RV_TEMP {
                r_val[r] = RV_NONE;
                r_free |= bit(r);
            }
            r = pr;
        }
        if ext && r < 16 { zext_reg(r, bits_of(vtype(j))); }
        ext = false;
    }
    let old = r_val[r];
    if old < RV_TEMP && old != j { vi[old].reg = NOREG; }
    r_temp &= ~bit(r);
    r_free &= ~bit(r);
    r_lock |= bit(r);
    r_val[r] = j;
    vi[j].reg = r as! u8;
    var st = vi[j].st & ~(ST_MEM | ST_EXT);
    if ext { st |= ST_EXT; }
    vi[j].st = st;
    if st & (ST_GLOB | ST_PIN) == ST_GLOB {
        ra_store_home(j, r);
    } else if vi[j].nuse == 0 {
        r_val[r] = RV_NONE;
        vi[j].reg = NOREG;
        r_free |= bit(r);
    }
}

// --- xmm values (f32, f64); xmm numbers 0..15 in and out
fn ra_mat_xmm(v: u32, x: u32) {
    let k = gir_kind(v);
    let i = gir_idx(v);
    if k == GIR_V_CONST {
        let c = M.consts[i];
        if c.lo == 0 && c.hi == 0 && c.data == GIR_NONE { xorps_rr(x, x); return; }
        xmm_load_t(x, const_mem(i), c.ty);
        return;
    }
    let id = vid(v);
    let t = vtype(id);
    var m = Mem { M_REG, 0, 0, 0, 0 };
    let pend = vi[id].reg == PEND;
    if pend { m = ra_take_pend(id); }
    else if vi[id].home == H_STACK { m = m_rbp(vi[id].off); }
    else { m = ra_home(id); }
    if pend && dbg_on { dbg_ld(id); }
    xmm_load_t(x, m, t);
    if pend && dbg_on { dbg_ld_end(); }
}
fn ra_xmm(v: u32) -> u32 {
    if is_val(v) {
        let id = vid(v);
        let r: u32 = vi[id].reg;
        if r < 32 {
            if r < 16 { assert(false); }    // a general-register value: a class mix-up
            r_lock |= bit(r);
            ra_note(id);
            return r - 16;
        }
        let n = ra_alloc(XMM_ALL, XMM_ALL);
        if r == PEND { vi[id].st &= ~ST_MEM; }
        ra_mat_xmm(v, n - 16);
        r_val[n] = id;
        vi[id].reg = n as! u8;
        ra_note(id);
        return n - 16;
    }
    let t = ra_xtemp();
    ra_mat_xmm(v, t);
    return t;
}
fn ra_xmm_into(v: u32, x: u32) {
    let r = x + 16;
    var src: u32 = 32;
    var id: u32 = RV_NONE;
    if is_val(v) {
        id = vid(v);
        let vr: u32 = vi[id].reg;
        if vr < 32 { src = vr; }
    }
    if src == r {
        if ra_live_after(id) {
            ra_evacuate(id, r);
            r_free &= ~bit(r);
            r_val[r] = RV_TEMP;
            r_temp |= bit(r);
        }
        r_lock |= bit(r);
        ra_note(id);
        return;
    }
    let occ = r_val[r];
    if occ < RV_TEMP { ra_evacuate(occ, r); }
    r_free &= ~bit(r);
    r_val[r] = RV_TEMP;
    r_temp |= bit(r);
    r_lock |= bit(r);
    if src < 32 {
        movaps_rr(x, src - 16);
        r_lock |= bit(src);
        ra_note(id);
        return;
    }
    if id != RV_NONE { ra_note(id); }
    ra_mat_xmm(v, x);
}
fn ra_xdef(j: u32) -> u32 {
    if rg_on && rg_reg[j] != NOREG {
        let r: u32 = rg_reg[j];
        r_lock |= bit(r);
        return r - 16;
    }
    let h: u32 = vi[j].hint;
    if h >= 16 && h < 32 && vi[j].st & ST_GLOB == 0 && r_free & ~r_lock & bit(h) != 0 {
        return ra_alloc(XMM_ALL, bit(h)) - 16;
    }
    return ra_alloc(XMM_ALL, XMM_ALL) - 16;
}
fn ra_xreuse(v: u32) -> u32 {
    let r = ra_reuse(v);
    if r < 32 && r >= 16 { return r - 16; }
    return 32;
}
fn ra_xset(j: u32, x: u32) { ra_set(j, x + 16, false); }

// Operand descriptors for instructions that take an immediate or a memory
// operand.
let OK_REG: u32 = 0;
let OK_IMM: u32 = 1;
let OK_MEM: u32 = 2;
struct Opnd { kind: u32, reg: u32, imm: i64, m: Mem }

// The memory operand of v if it can be read in place (a deferred load, or a
// value that is only in its home), for an access of n bytes; ok = false
// otherwise.
fn ra_mem_opnd(v: u32, n: u32) -> bool, Mem {
    let z = Mem { M_REG, 0, 0, 0, 0 };
    if !is_val(v) { return false, z; }
    let id = vid(v);
    let r = vi[id].reg;
    if r < 32 { return false, z; }
    let t = vtype(id);
    let c = rc_of(t);
    if c == RC_GPR && int_bytes(bits_of(t)) != n || c == RC_VX { return false, z; }
    if r == PEND {
        ra_note(id);
        return true, ra_take_pend(id);
    }
    let h = vi[id].home;
    if h == H_SLOT && vi[id].st & ST_MEM != 0 {
        ra_note(id);
        return true, m_rbp(vi[id].off);
    }
    return false, z;
}

// ---------------------------------------------------------------- blocks

// The register file at the start of a function (r_alloc set): empty.
fn ra_func_start() {
    for r in 32 { r_val[r] = RV_NONE; }
    r_free = r_alloc;
    r_lock = 0;
    r_temp = 0;
    n_pend = 0;
    dying.clear();
    flags_id = RV_NONE;
    ra_carry = false;
}
// All registers become free at the start of a block (local values are dead,
// global values and PHIs are in their homes).
fn ra_block_start() {
    var m = ~r_free & r_alloc;
    while m != 0 {
        let r = ctz32(m);
        m &= m - 1;
        let id = r_val[r];
        if id < RV_TEMP { vi[id].reg = NOREG; }
        r_val[r] = RV_NONE;
    }
    r_free = r_alloc;
    r_lock = 0;
    r_temp = 0;
    n_pend = 0;
    flags_id = RV_NONE;
    ra_carry = false;
}

// End of an instruction: frees the registers (and slots) of values whose last
// use it was, and its scratch registers.
fn ra_end_inst() {
    if ra_carry {
        ra_carry = false;
        return;
    }
    for id in dying {
        let r: u32 = vi[id].reg;
        if r < 32 && r_val[r] == id {
            vi[id].reg = NOREG;
            ra_release(r);
        }
        if f_share && vi[id].off != 0 && vi[id].home == H_SLOT && vi[id].st & (ST_GLOB | ST_PHI) == 0 {
            ra_free_slot(id);
        }
    }
    dying.clear();
    var m = r_temp;
    while m != 0 {
        let r = ctz32(m);
        m &= m - 1;
        r_val[r] = RV_NONE;
    }
    r_free |= r_temp;
    r_temp = 0;
    r_lock = 0;
    if rg_on {
        if rg_nborrow != 0 { rg_restore(); }
        rg_kills();
    }
}
