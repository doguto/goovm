// Global register allocation for optimized code (milestone E1, DESIGN.md
// §16). At opt_level >= 1, before a function's body is generated, the
// values that live across blocks (ST_GLOB: PHIs, values used in other
// blocks, arguments used outside the entry block) are given a register for
// their whole live range ("pinned"), or none (they keep -O0's write-through
// home). The block-local allocator of ra.goose then works around them: a
// pinned value is in its register from its definition (or the start of a
// block it is live into) to its last use in each block, never spilled; the
// local values and scratch registers take what is free.
//
//   liveness   live-in/live-out bitsets of the global values per block
//              (backward dataflow), then the live segments of each value in
//              the linear order of the instructions: instruction j is at
//              position 2j + 2, a block spans [2 first + 1, 2 last + 3); a
//              definition starts at its position, a use ends one after it,
//              so an instruction's operands and its result interfere
//   clobbers   calls and legacy lowerings clobber the caller-saved
//              registers at 2j + 3 (after the operands are read, before the
//              result), inline asm and setjmp every register, rep movs/stos
//              rdi and rsi; a value live across such a point cannot have
//              those registers (its own definition is exempt)
//   assignment values in order of spill weight (uses weighted 8^loop depth),
//              each to the first register of its class that is free over
//              all its segments (per-register occupancy bitmaps over the
//              positions), its PHI partner's or its argument register first;
//              a value that finds no register stays in memory
//   splitting  (E2) a value live across calls may take a caller-saved
//              register (any xmm register: the SysV ABI has none that is
//              callee-saved) when its uses weigh more than the calls it
//              crosses: it is stored to its home where it is defined, gives
//              up the register before each call it lives across and is
//              reloaded after it (rq_list), as LLVM's greedy allocator
//              splits such a range around the calls
//   registers  rbx r12-r15 (callee-saved) and rsi rdi r8 r9 r10; xmm4-15.
//              rax rcx rdx r11 and xmm0-3 are never pinned: they are the
//              fixed registers of division, shifts, returns and indirect
//              calls, and what the lowerings' scratch needs is always there

let ST_PIN: u8 = 64;     // vi[].st: a pinned global value (rg_reg holds its register)
let ST_KEEP: u8 = 128;   // vi[].st: the value must stay in its home (a debug variable's address)
let RG_GPR_CALLER: u32 = 0x07C0;   // rsi rdi r8 r9 r10
let RG_XMM: u32 = 0xFFF00000;      // xmm4..xmm15
let RG_MAX_BITS: i64 = 1 << 26;    // liveness bitsets larger than this: sparse liveness (E2)

var rg_on = false;                 // pinned values in this function
var rg_reg: u8[>..] = [];          // per value id: its register, NOREG
var rg_gid: u32[>..] = [];         // per value id: global value number, NIL
var rg_val: u32[>..] = [];         // global number -> value id
var rg_cs: u32 = 0;                // callee-saved registers of pinned values
var rg_pin: u32 = 0;               // registers holding pinned values now
var rg_kill_next: u32 = 0;         // first instruction whose kills are not processed
var rg_nb: u32 = 0;
var rg_words: i64 = 0;             // words per bitset
var rg_lin: u64[>..] = [];         // live-in bitsets, rg_words per block
var rg_lout: u64[>..] = [];
var rg_gen: u64[>..] = [];         // upward-exposed uses per block
var rg_def: u64[>..] = [];         // definitions per block
var rg_ss: u32[>..] = [];          // successors (CSR)
var rg_sl: u32[>..] = [];
var rg_bfirst: u32[>..] = [];      // per block: first and last local instruction
var rg_blast: u32[>..] = [];
var rg_bdepth: u8[>..] = [];       // per block: loop depth estimate
// segments of the global values: built per block, then grouped by value
var sg_v: u32[>..] = [];
var sg_s: u32[>..] = [];
var sg_e: u32[>..] = [];
var vs_start: u32[>..] = [];       // per global value: its segments (CSR, in order)
var vs_s: u32[>..] = [];
var vs_e: u32[>..] = [];
// kills: per instruction, the pinned values whose live segment ends there
var kl_start: u32[>..] = [];
var kl_list: u32[>..] = [];
var kl_tmp_j: u32[>..] = [];
var kl_tmp_v: u32[>..] = [];
// live-in pinned values per block (CSR)
var li_start: u32[>..] = [];
var li_list: u32[>..] = [];
// clobber points (positions) and their kinds
var cl_pos: u32[>..] = [];
var cl_kind: u8[>..] = [];
let CL_CALL: u8 = 1;   // caller-saved GPRs and all xmm
let CL_ALL: u8 = 2;    // every register
let CL_REP: u8 = 3;    // rdi, rsi
// occupancy bitmaps: 32 registers x rg_pw words
var rg_occ: u64[>..] = [];
var rg_pw: i64 = 0;
var rg_weight: u32[>..] = [];      // per global value
var rg_order: u32[>..] = [];
var rg_hint: u8[>..] = [];         // per global value: preferred register, NOREG
var rg_seen: u32[>..] = [];        // per global value: last block stamp seen in the backward scan
// (E2) values split around calls: per value id 1 if it is reloaded after the
// calls it lives across; per instruction (CSR) the values reloaded after it
var rg_rl: u8[>..] = [];
var rq_start: u32[>..] = [];
var rq_list: u32[>..] = [];
var rq_tmp_j: u32[>..] = [];
var rq_tmp_v: u32[>..] = [];
var rg_iblk: u32[>..] = [];        // per instruction: its block
var rg_lpl: u64[>..] = [];         // global values live into a landing pad (bitset)
var rg_any_rl = false;
// (E2) two-address sharing: an arithmetic instruction whose result and one
// operand that dies there are both candidates may give them one register
// (the operand's segment ends where the result's starts): `s = s + x` in a
// loop then needs no copy for the PHI. rg_share[j] = the operand's value id,
// rg_shby[id] = the instruction, NIL.
var rg_share: u32[>..] = [];
var rg_shby: u32[>..] = [];

inline fn rg_bit(w: u64[>..]&, base: i64, g: u32) -> bool { (w[base + (g >> 6)] >> (g & 63)) & 1 != 0 }

// Successors of block b (local), into rg_sl.
fn rg_succs(b: u32) {
    let B = M.blocks[f_first_block + b];
    if B.n_inst == 0 { return; }
    let t = B.first_inst + B.n_inst - 1;
    let I = M.insts[t];
    let op: u32 = I.op;
    if op == GIR_BR { rg_sl.push(I.a); }
    else if op == GIR_CONDBR {
        rg_sl.push(I.b);
        rg_sl.push(I.c);
    } else if op == GIR_SWITCH {
        rg_sl.push(M.opnds[I.b]);
        for k in 0..I.c { rg_sl.push(M.opnds[I.b + 2 + 2 * k]); }
    } else if op == GIR_INDIRECTBR {
        for k in 0..I.c { rg_sl.push(M.opnds[I.b + k]); }
    }
    if B.n_inst >= 2 {
        let C = M.insts[t - 1];
        if C.op == GIR_CALL && C.flags & IF_INVOKE != 0 { rg_sl.push(M.opnds[C.b + 2 * C.c]); }
    }
}

// The global value number of operand v (NIL if it is not a candidate).
inline fn rg_g(v: u32) -> u32 {
    let k = gir_kind(v);
    if k == GIR_V_INST {
        let u = gir_idx(v) - f_first_inst;
        if u >= f_nins { return NIL; }
        return rg_gid[u];
    }
    if k == GIR_V_ARG { return rg_gid[f_nins + gir_idx(v)]; }
    return NIL;
}

// Decides the registers of the function's global values (after ra_prepass,
// dbg_keep_homes). Sets rg_on and rg_cs.
fn rg_alloc(insts: const Inst[:], blocks: const Block[:]) {
    rg_on = false;
    rg_cs = 0;
    rg_pin = 0;
    rg_kill_next = 0;
    let nv: i64 = f_nins as i64 + f_nargs;
    if rg_reg.len < nv {
        rg_reg.resize(nv, NOREG);
        rg_gid.resize(nv, NIL);
        rg_rl.resize(nv, 0);
        rg_share.resize(nv, NIL);
        rg_shby.resize(nv, NIL);
    }
    for q in 0..nv {
        rg_reg[q] = NOREG;
        rg_gid[q] = NIL;
        rg_rl[q] = 0;
        rg_share[q] = NIL;
        rg_shby[q] = NIL;
    }
    rg_any_rl = false;
    let F = M.funcs[f_index];
    // (E2) functions that call setjmp are allocated too, as LLVM's are:
    // longjmp restores the callee-saved registers to their values at the
    // setjmp, which is what C allows for the non-volatile variables changed in
    // between; __builtin_setjmp clobbers every register (CL_ALL)
    let nb: u32 = blocks.len as! u32;
    rg_nb = nb;
    // candidates
    rg_val.clear();
    classify_reset();
    for a in 0..f_nargs {
        let t = M.opnds[f_args + 2 * a];
        let l = classify(t, M.opnds[f_args + 2 * a + 1]);
        let id = f_nins + a;
        let c = rc_of(t);
        if l.kind == AL_GPR && c == RC_GPR || l.kind == AL_XMM && in_xmm(c) {
            if vi[id].st & (ST_GLOB | ST_KEEP) == ST_GLOB && vi[id].nuse != 0 {
                rg_gid[id] = rg_val.len as! u32;
                rg_val.push(id);
            }
        }
    }
    // (E2) the PHIs of indirectbr targets keep their home: the edges'
    // moves all happen before the one jump
    rg_ibt.clear();
    rg_ibt.resize(nb, 0);
    for I in insts {
        if I.op == GIR_INDIRECTBR { for q in 0..I.c { rg_ibt[M.opnds[I.b + q]] = 1; } }
    }
    for I, j in insts {
        // (a PHI is always a candidate: the edges define it, even if all its
        // uses are in its block)
        if I.ty == GIR_T_VOID || vi[j].nuse == 0 || vi[j].st & ST_KEEP != 0 { continue; }
        if vi[j].st & ST_GLOB == 0 && I.op != GIR_PHI { continue; }
        let c = rc_of(I.ty);
        if c == RC_MEM || vi[j].home == H_ALLOCA || vi[j].home == H_PTR { continue; }
        if I.op == GIR_PHI && rg_ibt[rg_blk_of(blocks, j as! u32)] != 0 { continue; }
        rg_gid[j] = rg_val.len as! u32;
        rg_val.push(j as! u32);
    }
    let ng: u32 = rg_val.len as! u32;
    if ng == 0 { return; }
    rg_words = (ng as i64 + 63) >> 6;
    rg_build_cfg(blocks);
    // (E2) dense bitsets, or (larger functions) a walk from each use
    if rg_words * nb as i64 * 64 > RG_MAX_BITS || opt_off("dense") {
        rg_liveness_sparse(insts);
    } else {
        rg_liveness(insts, blocks);
        rg_lists_from_bits();
    }
    rg_segments(insts, blocks);
    rg_clobbers(insts);
    rg_assign();
    if rg_on { rg_finish(insts, blocks); }
}

fn rg_build_cfg(blocks: const Block[:]) {
    let nb = rg_nb;
    rg_ss.clear();
    rg_sl.clear();
    rg_bfirst.clear();
    rg_blast.clear();
    rg_iblk.clear();
    for B, b in blocks {
        rg_ss.push(rg_sl.len as! u32);
        rg_succs(b as! u32);
        rg_bfirst.push(B.first_inst - f_first_inst);
        rg_blast.push(B.first_inst - f_first_inst + B.n_inst - 1);
        for k in 0..B.n_inst { rg_iblk.push(b as! u32); }
    }
    rg_ss.push(rg_sl.len as! u32);
    // loop depth estimate: a retreating edge (to a block at or before the
    // source in layout order) closes a loop over the blocks between them
    rg_bdepth.clear();
    rg_bdepth.resize(nb, 0);
    for b in 0..nb {
        for k in rg_ss[b]..rg_ss[b + 1] {
            let h = rg_sl[k];
            if h > b { continue; }
            for x in h..b + 1 { if rg_bdepth[x] < 4 { rg_bdepth[x]++; } }
        }
    }
}

// Uses of instruction I (local index j) that are candidates: calls F(g).
fn rg_each_use<F>(I: Inst) {
    let op: u32 = I.op;
    let m: u32 = if op < GIR_NOPS { OP_USES[op] } else { U_A | U_B | U_C };
    if m & U_A != 0 { let g = rg_g(I.a); if g != NIL { F(g); } }
    if m & U_B != 0 { let g = rg_g(I.b); if g != NIL { F(g); } }
    if m & U_C != 0 { let g = rg_g(I.c); if g != NIL { F(g); } }
    if m >= U_GEP {
        if m & U_GEP != 0 {
            for k in 0..I.c { let g = rg_g(M.opnds[I.b + 2 + 2 * k]); if g != NIL { F(g); } }
        } else if m & U_CALL != 0 {
            for k in 0..I.c { let g = rg_g(M.opnds[I.b + 2 * k]); if g != NIL { F(g); } }
        } else {
            let A = M.asms[I.a];
            for q in 0..A.n_in { let g = rg_g(M.opnds[A.ops + 2 * q]); if g != NIL { F(g); } }
        }
    }
}
// PHI incoming values from block b (at its terminator): calls F(g).
fn rg_each_phi_use<F>(b: u32) {
    for k in rg_ss[b]..rg_ss[b + 1] {
        let s = rg_sl[k];
        let S = M.blocks[f_first_block + s];
        for pi in S.first_inst..S.first_inst + S.n_inst {
            let P = M.insts[pi];
            if P.op != GIR_PHI { break; }
            for q in 0..P.c {
                if M.opnds[P.b + 2 * q + 1] != b { continue; }
                let g = rg_g(M.opnds[P.b + 2 * q]);
                if g != NIL { F(g); }
                break;
            }
        }
    }
}

fn rg_liveness(insts: const Inst[:], blocks: const Block[:]) {
    let nb = rg_nb;
    let w = rg_words;
    let n: i64 = w * nb as i64;
    rg_lin.clear();
    rg_lin.resize(n, 0);
    rg_lout.clear();
    rg_lout.resize(n, 0);
    rg_gen.clear();
    rg_gen.resize(n, 0);
    rg_def.clear();
    rg_def.resize(n, 0);
    // arguments are defined at the entry
    for a in 0..f_nargs {
        let g = rg_gid[f_nins + a];
        if g != NIL { rg_def[g >> 6] |= (1 as u64) << (g & 63); }
    }
    for b in 0..nb {
        let base: i64 = w * b as i64;
        for j in rg_bfirst[b]..rg_blast[b] + 1 {
            let I = insts[j];
            if I.op != GIR_PHI {
                rg_each_use(I) { g =>
                    if (rg_def[base + (g >> 6)] >> (g & 63)) & 1 == 0 { rg_gen[base + (g >> 6)] |= (1 as u64) << (g & 63); }
                };
            }
            let gd = rg_gid[j];
            if gd != NIL { rg_def[base + (gd >> 6)] |= (1 as u64) << (gd & 63); }
        }
        rg_each_phi_use(b) { g =>
            if (rg_def[base + (g >> 6)] >> (g & 63)) & 1 == 0 { rg_gen[base + (g >> 6)] |= (1 as u64) << (g & 63); }
        };
    }
    // backward dataflow, blocks in reverse layout order until stable
    var changed = true;
    while changed {
        changed = false;
        var b: i64 = nb as i64 - 1;
        while b >= 0 {
            let base: i64 = w * b;
            for k in rg_ss[b]..rg_ss[b + 1] {
                let sb: i64 = w * rg_sl[k] as i64;
                for x in 0..w { rg_lout[base + x] |= rg_lin[sb + x]; }
            }
            for x in 0..w {
                let nw = rg_gen[base + x] | (rg_lout[base + x] & ~rg_def[base + x]);
                if nw != rg_lin[base + x] {
                    rg_lin[base + x] = nw;
                    changed = true;
                }
            }
            b--;
        }
    }
}

// (E2) The live-in and live-out sets as lists per block (CSR, values in
// increasing order), from the bitsets (which are then released).
var rg_li_s: u32[>..] = [];
var rg_li: u32[>..] = [];
var rg_lo_s: u32[>..] = [];
var rg_lo: u32[>..] = [];
fn rg_lists_from_bits() {
    let w = rg_words;
    rg_li_s.clear();
    rg_li.clear();
    rg_lo_s.clear();
    rg_lo.clear();
    for b in 0..rg_nb {
        rg_li_s.push(rg_li.len as! u32);
        rg_lo_s.push(rg_lo.len as! u32);
        let base: i64 = w * b as i64;
        for x in 0..w {
            var m = rg_lin[base + x];
            while m != 0 {
                rg_li.push((x as u32) * 64 + ctz(m) as! u32);
                m &= m - 1;
            }
            m = rg_lout[base + x];
            while m != 0 {
                rg_lo.push((x as u32) * 64 + ctz(m) as! u32);
                m &= m - 1;
            }
        }
    }
    rg_li_s.push(rg_li.len as! u32);
    rg_lo_s.push(rg_lo.len as! u32);
    rg_lin.clear();
    rg_lout.clear();
    rg_gen.clear();
    rg_def.clear();
}

// (E2) Liveness without bitsets, for functions whose bitsets would be too
// large: from each use, backwards through the predecessors until the
// definition's block (the same sets as rg_liveness: a value is live into a
// block when a path from it reaches a use without passing the definition;
// live out of a block when live into a successor; a PHI's incoming value
// is used at the end of its predecessor).
var rg_ps: u32[>..] = [];
var rg_pl: u32[>..] = [];
var rg_us_s: u32[>..] = [];    // per value: its uses (block; bit 31: a PHI edge)
var rg_us: u32[>..] = [];
var rg_us_tg: u32[>..] = [];
var rg_us_tb: u32[>..] = [];
var rg_mk_in: u32[>..] = [];   // per block: value + 1 marked live in / out
var rg_mk_out: u32[>..] = [];
var rg_stk: u32[>..] = [];
var rg_pin_b: u32[>..] = [];   // pairs (block, value), in increasing value order
var rg_pin_g: u32[>..] = [];
var rg_pout_b: u32[>..] = [];
var rg_pout_g: u32[>..] = [];
fn rg_liveness_sparse(insts: const Inst[:]) {
    let nb = rg_nb;
    let ng: u32 = rg_val.len as! u32;
    // predecessors
    rg_ps.clear();
    rg_ps.resize(nb + 1, 0);
    for b in 0..nb { for k in rg_ss[b]..rg_ss[b + 1] { rg_ps[rg_sl[k] + 1]++; } }
    for b in 0..nb { rg_ps[b + 1] += rg_ps[b]; }
    rg_pl.clear();
    rg_pl.resize(rg_ps[nb], 0);
    if rg_fill.len < nb { rg_fill.resize(nb, 0); }
    for b in 0..nb { rg_fill[b] = rg_ps[b]; }
    for b in 0..nb {
        for k in rg_ss[b]..rg_ss[b + 1] {
            let s = rg_sl[k];
            rg_pl[rg_fill[s]] = b;
            rg_fill[s]++;
        }
    }
    // uses, grouped by value
    rg_us_tg.clear();
    rg_us_tb.clear();
    for b in 0..nb {
        for j in rg_bfirst[b]..rg_blast[b] + 1 {
            let I = insts[j];
            if I.op != GIR_PHI {
                rg_each_use(I) { g =>
                    rg_us_tg.push(g);
                    rg_us_tb.push(b);
                };
            }
        }
        rg_each_phi_use(b) { g =>
            rg_us_tg.push(g);
            rg_us_tb.push(b | 0x80000000);
        };
    }
    rg_us_s.clear();
    rg_us_s.resize(ng + 1, 0);
    for g in rg_us_tg { rg_us_s[g + 1]++; }
    for g in 0..ng { rg_us_s[g + 1] += rg_us_s[g]; }
    rg_us.clear();
    rg_us.resize(rg_us_s[ng], 0);
    if rg_fill.len < ng { rg_fill.resize(ng, 0); }
    for g in 0..ng { rg_fill[g] = rg_us_s[g]; }
    for k in 0..rg_us_tg.len {
        let g = rg_us_tg[k];
        rg_us[rg_fill[g]] = rg_us_tb[k];
        rg_fill[g]++;
    }
    rg_mk_in.clear();
    rg_mk_in.resize(nb, 0);
    rg_mk_out.clear();
    rg_mk_out.resize(nb, 0);
    rg_pin_b.clear();
    rg_pin_g.clear();
    rg_pout_b.clear();
    rg_pout_g.clear();
    for g in 0..ng {
        let id = rg_val[g];
        let d: u32 = if id >= f_nins { 0 } else { rg_iblk[id] };
        let stamp: u32 = g + 1;
        rg_stk.clear();
        for q in rg_us_s[g]..rg_us_s[g + 1] {
            let u = rg_us[q] & 0x7FFFFFFF;
            // (a use in the definition's block comes after the definition;
            // a PHI edge from it is used at its end)
            if u == d || rg_mk_in[u] == stamp { continue; }
            rg_mk_in[u] = stamp;
            rg_pin_b.push(u);
            rg_pin_g.push(g);
            rg_stk.push(u);
        }
        while rg_stk.len != 0 {
            let x = rg_stk.pop();
            for k in rg_ps[x]..rg_ps[x + 1] {
                let p = rg_pl[k];
                if rg_mk_out[p] != stamp {
                    rg_mk_out[p] = stamp;
                    rg_pout_b.push(p);
                    rg_pout_g.push(g);
                }
                if p == d || rg_mk_in[p] == stamp { continue; }
                rg_mk_in[p] = stamp;
                rg_pin_b.push(p);
                rg_pin_g.push(g);
                rg_stk.push(p);
            }
        }
    }
    // per block, in increasing value order (a stable counting sort)
    rg_csr(rg_pin_b, rg_pin_g, nb);
    rg_li_s.clear();
    rg_li_s.append(rg_cs_st);
    rg_li.clear();
    rg_li.append(rg_cs_out);
    rg_csr(rg_pout_b, rg_pout_g, nb);
    rg_lo_s.clear();
    rg_lo_s.append(rg_cs_st);
    rg_lo.clear();
    rg_lo.append(rg_cs_out);
}
var rg_cs_st: u32[>..] = [];
var rg_cs_out: u32[>..] = [];
fn rg_csr(bs: const u32[:], gs: const u32[:], nb: u32) {
    rg_cs_st.clear();
    rg_cs_st.resize(nb + 1, 0);
    for b in bs { rg_cs_st[b + 1]++; }
    for b in 0..nb { rg_cs_st[b + 1] += rg_cs_st[b]; }
    rg_cs_out.clear();
    rg_cs_out.resize(rg_cs_st[nb], 0);
    if rg_fill.len < nb { rg_fill.resize(nb, 0); }
    for b in 0..nb { rg_fill[b] = rg_cs_st[b]; }
    for k in 0..bs.len {
        let b = bs[k];
        rg_cs_out[rg_fill[b]] = gs[k];
        rg_fill[b]++;
    }
}

// Live segments of every global value, and the kill points (where a
// segment ends inside a block).
fn rg_segments(insts: const Inst[:], blocks: const Block[:]) {
    let nb = rg_nb;
    let w = rg_words;
    let ng: u32 = rg_val.len as! u32;
    sg_v.clear();
    sg_s.clear();
    sg_e.clear();
    kl_tmp_j.clear();
    kl_tmp_v.clear();
    rg_seen.clear();
    rg_seen.resize(ng, NIL);
    rg_weight.clear();
    rg_weight.resize(ng, 0);
    // segment ends found by a backward scan of each block: rg_seen[g] == b
    // once g's last use in b (or live-out) has been recorded; sg_e of the
    // value's open segment is kept in rg_tmpe
    if rg_tmpe.len < ng { rg_tmpe.resize(ng, 0); }
    for b in 0..nb {
        let base: i64 = w * b as i64;
        let bs: u32 = 2 * rg_bfirst[b] + 1;
        let be: u32 = 2 * rg_blast[b] + 3;
        let fq: u32 = (1 as u32) << (3 * rg_bdepth[b]);
        // live-out values end at the block end
        for q in rg_lo_s[b]..rg_lo_s[b + 1] {
            let g = rg_lo[q];
            rg_seen[g] = b;
            rg_tmpe[g] = be;
        }
        // PHI incoming values used at the terminator
        let tj = rg_blast[b];
        rg_each_phi_use(b) { g =>
            rg_weight[g] += fq;
            if rg_seen[g] != b {
                rg_seen[g] = b;
                rg_tmpe[g] = 2 * tj + 3;
                kl_tmp_j.push(tj);
                kl_tmp_v.push(g);
            }
        };
        var j: i64 = rg_blast[b];
        while j >= rg_bfirst[b] {
            let I = insts[j];
            let gd = rg_gid[j];
            // (E2) the operand that may share the result's register: ends at
            // the result's start
            if gd != NIL && rg_share_op(I) {
                let comm = I.op != GIR_SUB && I.op != GIR_FSUB && I.op != GIR_FDIV;
                var sv: u32 = NIL;
                let ga = rg_g(I.a);
                let gb = rg_g(I.b);
                if ga != NIL && rg_seen[ga] != b && I.b != I.a { sv = I.a; }
                else if comm && gb != NIL && rg_seen[gb] != b && I.b != I.a { sv = I.b; }
                if sv != NIL {
                    let g = rg_g(sv);
                    rg_seen[g] = b;
                    rg_tmpe[g] = 2 * j as! u32 + 2;
                    kl_tmp_j.push(j as! u32);
                    kl_tmp_v.push(g);
                    let id = rg_val[g];
                    rg_share[j] = id;
                    rg_shby[id] = j as! u32;
                }
            }
            if gd != NIL {
                rg_weight[gd] += fq;
                if rg_seen[gd] != b {
                    // defined, never used after: dies at once
                    rg_seen[gd] = b;
                    rg_tmpe[gd] = 2 * j as! u32 + 3;
                    kl_tmp_j.push(j as! u32);
                    kl_tmp_v.push(gd);
                }
                let st: u32 = if I.op == GIR_PHI { bs } else { 2 * j as! u32 + 2 };
                sg_v.push(gd);
                sg_s.push(st);
                sg_e.push(rg_tmpe[gd]);
            }
            if I.op != GIR_PHI {
                let jj: u32 = j as! u32;
                rg_each_use(I) { g =>
                    rg_weight[g] += fq;
                    if rg_seen[g] != b {
                        rg_seen[g] = b;
                        rg_tmpe[g] = 2 * jj + 3;
                        kl_tmp_j.push(jj);
                        kl_tmp_v.push(g);
                    }
                };
            }
            j--;
        }
        // values live into the block: a segment from its start
        for q in rg_li_s[b]..rg_li_s[b + 1] {
            let g = rg_li[q];
            sg_v.push(g);
            sg_s.push(bs);
            sg_e.push(rg_tmpe[g]);
        }
        // arguments: live from the entry
        if b == 0 {
            for a in 0..f_nargs {
                let g = rg_gid[f_nins + a];
                if g == NIL || rg_seen[g] != 0 { continue; }
                sg_v.push(g);
                sg_s.push(bs);
                sg_e.push(rg_tmpe[g]);
            }
        }
    }
    // group by value (counting sort), sorted by start, merging touching ones
    vs_start.clear();
    vs_start.resize(ng + 1, 0);
    for g in sg_v { vs_start[g + 1]++; }
    for g in 0..ng { vs_start[g + 1] += vs_start[g]; }
    let ns = sg_v.len;
    vs_s.clear();
    vs_s.resize(ns, 0);
    vs_e.clear();
    vs_e.resize(ns, 0);
    if rg_fill.len < ng { rg_fill.resize(ng, 0); }
    for g in 0..ng { rg_fill[g] = vs_start[g]; }
    for k in 0..ns {
        let g = sg_v[k];
        let p = rg_fill[g];
        vs_s[p] = sg_s[k];
        vs_e[p] = sg_e[k];
        rg_fill[g] = p + 1;
    }
    // (segments of one value were pushed block by block, ends before starts
    // within a block: sort each value's run by start)
    for g in 0..ng {
        let a = vs_start[g];
        let e = vs_start[g + 1];
        var k = a + 1;
        while k < e {
            let s0 = vs_s[k];
            let e0 = vs_e[k];
            var q = k;
            while q > a && vs_s[q - 1] > s0 {
                vs_s[q] = vs_s[q - 1];
                vs_e[q] = vs_e[q - 1];
                q--;
            }
            vs_s[q] = s0;
            vs_e[q] = e0;
            k++;
        }
    }
}
var rg_tmpe: u32[>..] = [];
var rg_fill: u32[>..] = [];

// The clobber points of the function.
fn rg_clobbers(insts: const Inst[:]) {
    cl_pos.clear();
    cl_kind.clear();
    for I, j in insts {
        let k: u32 = vi[j].kind;
        var c: u8 = 0;
        if k == K_ALL { c = CL_ALL; }
        else if k == K_B || k == K_CALL || I.op == GIR_TLSADDR { c = CL_CALL; }
        else if (I.op == GIR_MEMCPY || I.op == GIR_MEMSET) && I.c > 64 { c = CL_REP; }
        if c != 0 {
            cl_pos.push(2 * j as! u32 + 3);
            cl_kind.push(c);
        }
    }
}

// The clobbers inside global value g's segments (its definition exempt):
// a mask of CL_* bits.
fn rg_crossed(g: u32) -> u32 {
    let id = rg_val[g];
    var dpos: u32 = NIL;
    if id < f_nins && M.insts[f_first_inst + id].op != GIR_PHI { dpos = 2 * id + 3; }
    var m: u32 = 0;
    for k in vs_start[g]..vs_start[g + 1] {
        let s = vs_s[k];
        let e = vs_e[k];
        // first clobber at or after s (binary search)
        var lo: i64 = 0;
        var hi: i64 = cl_pos.len;
        while lo < hi {
            let mid = (lo + hi) >> 1;
            if cl_pos[mid] < s { lo = mid + 1; } else { hi = mid; }
        }
        while lo < cl_pos.len && cl_pos[lo] < e {
            if cl_pos[lo] != dpos { m |= (1 as u32) << cl_kind[lo]; }
            lo++;
        }
    }
    return m;
}
// The weight of the calls inside g's segments (its definition exempt): each
// 8^(loop depth of its block), what reloading g after each of them costs.
fn rg_cross_weight(g: u32) -> u32 {
    let id = rg_val[g];
    var dpos: u32 = NIL;
    if id < f_nins && M.insts[f_first_inst + id].op != GIR_PHI { dpos = 2 * id + 3; }
    var w: u32 = 0;
    for k in vs_start[g]..vs_start[g + 1] {
        let s = vs_s[k];
        let e = vs_e[k];
        var lo: i64 = 0;
        var hi: i64 = cl_pos.len;
        while lo < hi {
            let mid = (lo + hi) >> 1;
            if cl_pos[mid] < s { lo = mid + 1; } else { hi = mid; }
        }
        while lo < cl_pos.len && cl_pos[lo] < e {
            if cl_pos[lo] != dpos {
                let j = (cl_pos[lo] - 3) >> 1;
                let x = w + ((1 as u32) << (3 * rg_bdepth[rg_iblk[j]]));
                w = if x < w { 0xFFFFFFFF } else { x };
            }
            lo++;
        }
    }
    return w;
}
// The clobber points inside g's segments, for the reload lists.
fn rg_note_reloads(g: u32) {
    let id = rg_val[g];
    var dpos: u32 = NIL;
    if id < f_nins && M.insts[f_first_inst + id].op != GIR_PHI { dpos = 2 * id + 3; }
    for k in vs_start[g]..vs_start[g + 1] {
        let s = vs_s[k];
        let e = vs_e[k];
        var lo: i64 = 0;
        var hi: i64 = cl_pos.len;
        while lo < hi {
            let mid = (lo + hi) >> 1;
            if cl_pos[mid] < s { lo = mid + 1; } else { hi = mid; }
        }
        while lo < cl_pos.len && cl_pos[lo] < e {
            if cl_pos[lo] != dpos {
                rq_tmp_j.push((cl_pos[lo] - 3) >> 1);
                rq_tmp_v.push(id);
            }
            lo++;
        }
    }
}
// The instructions whose result may share a dying operand's register.
fn rg_share_op(I: Inst) -> bool {
    if tgt_a64 { return false; }    // (F1: three-address: the AArch64 allocator does not share)
    let op: u32 = I.op;
    let c = rc_of(I.ty);
    if c == RC_GPR {
        return (op == GIR_ADD || op == GIR_SUB || op == GIR_AND || op == GIR_OR || op == GIR_XOR || op == GIR_MUL)
               && bits_of(I.ty) <= 64;
    }
    if c == RC_XMM { return op >= GIR_FADD && op <= GIR_FDIV; }
    if c == RC_VX {
        return op >= GIR_FADD && op <= GIR_FDIV || op == GIR_ADD || op == GIR_SUB || op == GIR_AND || op == GIR_OR
               || op == GIR_XOR;
    }
    return false;
}
// The operand of instruction j that shares its register (a value reference),
// or NIL: both pinned to one register.
fn rg_shared(j: u32) -> u32 {
    if !rg_on || j >= rg_share.len as! u32 { return NIL; }
    let id = rg_share[j];
    if id == NIL || rg_reg[j] == NOREG || rg_reg[id] != rg_reg[j] { return NIL; }
    if id >= f_nins { return GIR_V_ARG << 30 | (id - f_nins); }
    return f_first_inst + id;
}
var rg_ibt: u8[>..] = [];          // per block: an indirectbr target
// The block of local instruction j (PHIs: at the start of their block).
fn rg_blk_of(blocks: const Block[:], j: u32) -> u32 {
    var lo: i64 = 0;
    var hi: i64 = blocks.len - 1;
    while lo < hi {
        let mid = (lo + hi + 1) >> 1;
        if blocks[mid].first_inst - f_first_inst <= j { lo = mid; } else { hi = mid - 1; }
    }
    return lo as! u32;
}
// Whether register r is free over g's segments.
fn rg_free(r: u32, g: u32) -> bool {
    let base: i64 = rg_pw * r as i64;
    for k in vs_start[g]..vs_start[g + 1] {
        let s = vs_s[k];
        let e = vs_e[k];
        var p = s;
        while p < e {
            let wi: i64 = base + (p >> 6) as i64;
            let lo = p & 63;
            var hib: u32 = 64;
            if e - (p - lo) < 64 { hib = e - (p - lo); }
            var m: u64 = if hib == 64 { 0xFFFFFFFFFFFFFFFF } else { ((1 as u64) << hib) - 1 };
            m &= ~(((1 as u64) << lo) - 1);
            if rg_occ[wi] & m != 0 { return false; }
            p = (p - lo) + 64;
        }
    }
    return true;
}
fn rg_take(r: u32, g: u32) {
    let base: i64 = rg_pw * r as i64;
    for k in vs_start[g]..vs_start[g + 1] {
        let s = vs_s[k];
        let e = vs_e[k];
        var p = s;
        while p < e {
            let wi: i64 = base + (p >> 6) as i64;
            let lo = p & 63;
            var hib: u32 = 64;
            if e - (p - lo) < 64 { hib = e - (p - lo); }
            var m: u64 = if hib == 64 { 0xFFFFFFFFFFFFFFFF } else { ((1 as u64) << hib) - 1 };
            m &= ~(((1 as u64) << lo) - 1);
            rg_occ[wi] |= m;
            p = (p - lo) + 64;
        }
    }
}
// Marks register r busy over [s, e).
fn rg_block_range(r: u32, s: u32, e: u32) {
    let base: i64 = rg_pw * r as i64;
    var p = s;
    while p < e {
        rg_occ[base + (p >> 6) as i64] |= (1 as u64) << (p & 63);
        p++;
    }
}

fn rg_assign() {
    let ng: u32 = rg_val.len as! u32;
    let npos: i64 = 2 * f_nins as i64 + 4;
    rg_pw = (npos + 63) >> 6;
    rg_occ.clear();
    rg_occ.resize(32 * rg_pw, 0);
    // registers of the arguments that stay local to the entry block are busy
    // until their last use there
    classify_reset();
    rg_hint.clear();
    rg_hint.resize(ng, NOREG);
    for a in 0..f_nargs {
        let t = M.opnds[f_args + 2 * a];
        let l = classify(t, M.opnds[f_args + 2 * a + 1]);
        let id = f_nins + a;
        let c = rc_of(t);
        if !(l.kind == AL_GPR && c == RC_GPR || l.kind == AL_XMM && in_xmm(c)) || vi[id].nuse == 0 { continue; }
        let r: u32 = if l.kind == AL_GPR { l.r0 } else { 16 + l.r0 };
        let g = rg_gid[id];
        if g != NIL {
            rg_hint[g] = r as! u8;
        } else if vi[id].st & ST_GLOB == 0 {
            rg_block_range(r, 1, 2 * vi[id].last + 3);
        } else {
            // a global argument in memory: its register is a cache until its
            // first use (blocked over the entry block's first instruction)
            rg_block_range(r, 1, 3);
        }
    }
    // values live into a landing pad are not split (the unwinder restores
    // only the callee-saved registers)
    let w = rg_words;
    rg_lpl.clear();
    rg_lpl.resize(w, 0);
    for b in 0..rg_nb {
        let B = M.blocks[f_first_block + b];
        if B.n_inst == 0 || M.insts[B.first_inst].op != GIR_LANDINGPAD { continue; }
        for q in rg_li_s[b]..rg_li_s[b + 1] { rg_lpl[rg_li[q] >> 6] |= (1 as u64) << (rg_li[q] & 63); }
    }
    rq_tmp_j.clear();
    rq_tmp_v.clear();
    let split = !opt_off("split");
    // registers that arguments arrive in: other values take them last
    var argm: u32 = 0;
    for g in 0..ng { if rg_hint[g] != NOREG { argm |= bit(rg_hint[g]); } }
    // PHI partners: a PHI and its incoming values prefer each other's register
    rg_order.clear();
    for g in 0..ng { rg_order.push(g); }
    sort(rg_order) { a, b => rg_weight[a] > rg_weight[b] || rg_weight[a] == rg_weight[b] && a < b };
    var any = false;
    for g in rg_order {
        let id = rg_val[g];
        let t = vtype(id);
        let c = rc_of(t);
        let cr = rg_crossed(g);
        var cand: u32 = 0;
        var pref: u32 = 0;
        // splitting around the calls: allowed when the calls it crosses
        // weigh less than its uses and definition
        var rld = false;
        let calls = cr & ((1 as u32) << CL_CALL) != 0;
        let can_split = split && calls && cr & ((1 as u32) << CL_ALL) == 0 && !rg_bit(rg_lpl, 0, g)
                        && rg_cross_weight(g) < rg_weight[g];
        if c == RC_GPR {
            if cr & ((1 as u32) << CL_ALL) != 0 { continue; }
            if calls { cand = GP_CALLEE; pref = GP_CALLEE; }
            else { cand = GP_CALLEE | RG_GPR_CALLER; pref = RG_GPR_CALLER; }
            if cr & ((1 as u32) << CL_REP) != 0 { cand &= ~(bit(RSI) | bit(RDI)); }
        } else {
            if cr & ((1 as u32) << CL_ALL) != 0 || calls && !can_split { continue; }
            cand = RG_XMM;
            pref = RG_XMM;
            rld = calls;
        }
        var r: u32 = 32;
        let h: u32 = rg_phi_hint(g);
        if h < 32 && cand & bit(h) != 0 && rg_free(h, g) { r = h; }
        if r == 32 {
            var m = cand & pref & ~argm;
            while m != 0 && r == 32 {
                let x = ctz32(m);
                m &= m - 1;
                if rg_free(x, g) { r = x; }
            }
            m = cand & pref & argm;
            while m != 0 && r == 32 {
                let x = ctz32(m);
                m &= m - 1;
                if rg_free(x, g) { r = x; }
            }
            m = cand & ~pref;
            while m != 0 && r == 32 {
                let x = ctz32(m);
                m &= m - 1;
                if rg_free(x, g) { r = x; }
            }
        }
        if r == 32 && c == RC_GPR && can_split {
            // no callee-saved register left: a caller-saved one, split
            var m = RG_GPR_CALLER;
            if cr & ((1 as u32) << CL_REP) != 0 { m &= ~(bit(RSI) | bit(RDI)); }
            if h < 32 && m & bit(h) != 0 && rg_free(h, g) { r = h; }
            while m != 0 && r == 32 {
                let x = ctz32(m);
                m &= m - 1;
                if rg_free(x, g) { r = x; }
            }
            rld = r != 32;
        }
        if r == 32 { continue; }
        rg_take(r, g);
        rg_reg[id] = r as! u8;
        if rld {
            rg_rl[id] = 1;
            rg_any_rl = true;
            rg_note_reloads(g);
        }
        if bit(r) & GP_CALLEE != 0 { rg_cs |= bit(r); }
        any = true;
    }
    rg_on = any;
}
// A register value g would like: its argument register, the register of an
// assigned PHI it feeds or of an assigned incoming value of it (if a PHI).
fn rg_phi_hint(g: u32) -> u32 {
    if rg_hint[g] != NOREG { return rg_hint[g]; }
    let id = rg_val[g];
    if id < f_nins && rg_share[id] != NIL && rg_reg[rg_share[id]] != NOREG { return rg_reg[rg_share[id]]; }
    if rg_shby[id] != NIL && rg_reg[rg_shby[id]] != NOREG { return rg_reg[rg_shby[id]]; }
    if id >= f_nins { return 32; }
    let I = M.insts[f_first_inst + id];
    if I.op == GIR_PHI {
        for q in 0..I.c {
            let v = M.opnds[I.b + 2 * q];
            if gir_kind(v) == GIR_V_INST {
                let u = gir_idx(v) - f_first_inst;
                if u < f_nins && rg_reg[u] != NOREG { return rg_reg[u]; }
            } else if gir_kind(v) == GIR_V_ARG {
                let u = f_nins + gir_idx(v);
                if rg_reg[u] != NOREG { return rg_reg[u]; }
            }
        }
    }
    return 32;
}

// After the assignment: kill lists of the pinned values, live-in lists, and
// the value states.
fn rg_finish(insts: const Inst[:], blocks: const Block[:]) {
    let nb = rg_nb;
    let w = rg_words;
    // kills (only pinned values), grouped by instruction
    kl_start.clear();
    kl_start.resize(f_nins + 1, 0);
    for k in 0..kl_tmp_j.len {
        if rg_reg[rg_val[kl_tmp_v[k]]] == NOREG { continue; }
        kl_start[kl_tmp_j[k] + 1]++;
    }
    for j in 0..f_nins { kl_start[j + 1] += kl_start[j]; }
    kl_list.clear();
    kl_list.resize(kl_start[f_nins], 0);
    if rg_fill.len < f_nins { rg_fill.resize(f_nins, 0); }
    for j in 0..f_nins { rg_fill[j] = kl_start[j]; }
    for k in 0..kl_tmp_j.len {
        let id = rg_val[kl_tmp_v[k]];
        if rg_reg[id] == NOREG { continue; }
        let j = kl_tmp_j[k];
        kl_list[rg_fill[j]] = id;
        rg_fill[j]++;
    }
    // reloads after the calls, grouped by instruction
    rq_start.clear();
    rq_start.resize(f_nins + 1, 0);
    for j in rq_tmp_j { rq_start[j + 1]++; }
    for j in 0..f_nins { rq_start[j + 1] += rq_start[j]; }
    rq_list.clear();
    rq_list.resize(rq_start[f_nins], 0);
    for j in 0..f_nins { rg_fill[j] = rq_start[j]; }
    for k in 0..rq_tmp_j.len {
        let j = rq_tmp_j[k];
        rq_list[rg_fill[j]] = rq_tmp_v[k];
        rg_fill[j]++;
    }
    // pinned live-ins per block
    li_start.clear();
    li_list.clear();
    for b in 0..nb {
        li_start.push(li_list.len as! u32);
        for q in rg_li_s[b]..rg_li_s[b + 1] {
            let id = rg_val[rg_li[q]];
            if rg_reg[id] != NOREG { li_list.push(id); }
        }
    }
    li_start.push(li_list.len as! u32);
    for g in 0..rg_val.len {
        let id = rg_val[g];
        if rg_reg[id] != NOREG { vi[id].st |= ST_PIN; }
    }
    // a local value that feeds a pinned PHI is computed in the PHI's register
    // when that is free (the edge's copy is then a no-op)
    for g in 0..rg_val.len {
        let id = rg_val[g];
        if rg_reg[id] == NOREG || id >= f_nins { continue; }
        let I = M.insts[f_first_inst + id];
        if I.op != GIR_PHI { continue; }
        for q in 0..I.c {
            let v = M.opnds[I.b + 2 * q];
            if gir_kind(v) != GIR_V_INST { continue; }
            let u = gir_idx(v) - f_first_inst;
            if u >= f_nins || rg_gid[u] != NIL || vi[u].hint != NOREG || vi[u].st & ST_GLOB != 0 { continue; }
            if (rc_of(vtype(u)) == RC_GPR) == (rg_reg[id] < 16) { vi[u].hint = rg_reg[id]; }
        }
    }
}

// ================================================ code generation support

// Block b starts: its pinned live-ins and PHIs are in their registers.
fn rg_block_enter(b: u32) {
    rg_pin = 0;
    for k in li_start[b]..li_start[b + 1] { rg_put(li_list[k]); }
    let B = M.blocks[f_first_block + b];
    for gi in B.first_inst..B.first_inst + B.n_inst {
        if M.insts[gi].op != GIR_PHI { break; }
        let j = gi - f_first_inst;
        if rg_reg[j] != NOREG { rg_put(j); }
    }
    rg_kill_next = B.first_inst - f_first_inst;
}
fn rg_put(id: u32) {
    let r: u32 = rg_reg[id];
    let occ = r_val[r];
    if occ < RV_TEMP && occ != id { vi[occ].reg = NOREG; }
    r_val[r] = id;
    vi[id].reg = r as! u8;
    vi[id].st &= ~ST_EXT;
    r_free &= ~bit(r);
    rg_pin |= bit(r);
    if bit(r) & GP_CALLEE != 0 { r_cs_used |= bit(r); }
}
// Entry block: arguments that are pinned move from their argument register to
// their own (a parallel copy), normalized.
fn rg_entry_moves() {
    for a in 0..f_nargs {
        let id = f_nins + a;
        if rg_reg[id] == NOREG { continue; }
        let src: u32 = vi[id].reg;
        let dst: u32 = rg_reg[id];
        if src < 32 && src != dst {
            mv_src.push(src);
            mv_dst.push(dst);
        }
    }
    // arguments whose argument register is overwritten lose that cache
    for a in 0..f_nargs {
        let id = f_nins + a;
        let r: u32 = vi[id].reg;
        if r >= 32 || rg_reg[id] != NOREG { continue; }
        for d in mv_dst {
            if d == r {
                vi[id].reg = NOREG;
                r_val[r] = RV_NONE;
                r_free |= bit(r);
            }
        }
    }
    if mv_src.len != 0 { emit_moves(); }
    for a in 0..f_nargs {
        let id = f_nins + a;
        if rg_reg[id] == NOREG { continue; }
        let r: u32 = vi[id].reg;
        if r < 32 && r != rg_reg[id] && r_val[r] == id {
            r_val[r] = RV_NONE;
            r_free |= bit(r);
        }
        let ext = vi[id].st & ST_EXT != 0;
        rg_put(id);
        if ext { zext_reg(rg_reg[id], bits_of(vtype(id))); }
        if rg_rl[id] != 0 { ra_store_home(id, rg_reg[id]); }
    }
}
// (E2) Before clobbering instruction j: the split values it lives across
// give up their registers (their home holds them since their definition).
fn rg_drop_rl(j: u32) {
    for k in rq_start[j]..rq_start[j + 1] {
        let id = rq_list[k];
        let r: u32 = rg_reg[id];
        if r_val[r] == id {
            r_val[r] = RV_NONE;
            r_free |= bit(r);
        }
        vi[id].reg = NOREG;
        rg_pin &= ~bit(r);
    }
}
// After it: they are reloaded.
fn rg_reload_rl(j: u32) {
    for k in rq_start[j]..rq_start[j + 1] {
        let id = rq_list[k];
        let r: u32 = rg_reg[id];
        let occ = r_val[r];
        if occ < RV_TEMP && occ != id { ra_evacuate(occ, r); }
        ra_load_from(r, ra_home(id), vtype(id));
        r_val[r] = id;
        r_free &= ~bit(r);
        r_temp &= ~bit(r);
        vi[id].reg = r as! u8;
        vi[id].st &= ~ST_EXT;
        rg_pin |= bit(r);
    }
}
// After the instruction that defines split value j: its home is written.
fn rg_def_store(j: u32) {
    if rg_rl[j] != 0 { ra_store_home(j, rg_reg[j]); }
}
// Instruction j defines pinned value j: its register is reserved for it (a
// local value there moves away).
fn rg_def_start(j: u32) {
    let r: u32 = rg_reg[j];
    let occ = r_val[r];
    if occ < RV_TEMP && occ != j && rg_shared(j) != NIL && occ == rg_share[j] {
        // (the operand that shares the register stays there for the lowering)
        rg_pin |= bit(r);
        return;
    }
    if occ < RV_TEMP && occ != j { ra_evacuate(occ, r); }
    r_free &= ~bit(r);
    r_val[r] = RV_TEMP;
    rg_pin |= bit(r);
    if bit(r) & GP_CALLEE != 0 { r_cs_used |= bit(r); }
}
// After the lowering of instruction j that defines pinned value j: a
// lowering that wrote the value to its home (legacy lowerings of vectors,
// odd-sized results) leaves it to be loaded into its register.
fn rg_def_end(j: u32) {
    let r: u32 = rg_reg[j];
    if vi[j].reg == r as! u8 || M.insts[f_first_inst + j].op == GIR_PHI { return; }
    ra_load_from(r, ra_home(j), vtype(j));
    let occ = r_val[r];
    if occ < RV_TEMP && occ != j { vi[occ].reg = NOREG; }
    r_val[r] = j;
    vi[j].reg = r as! u8;
    r_free &= ~bit(r);
    r_temp &= ~bit(r);
    rg_pin |= bit(r);
}
// End of instruction: the pinned values whose live range ends at an
// instruction up to the current one free their register.
fn rg_kills() {
    while rg_kill_next <= cur_pos {
        let j = rg_kill_next;
        for k in kl_start[j]..kl_start[j + 1] {
            let id = kl_list[k];
            let r: u32 = rg_reg[id];
            if r_val[r] == id {
                r_val[r] = RV_NONE;
                r_free |= bit(r);
                rg_pin &= ~bit(r);
            } else {
                // (E2: a result that shared the register holds it now)
                let o = r_val[r];
                if !(o < RV_TEMP && o < rg_reg.len as! u32 && rg_reg[o] == r && vi[o].st & ST_PIN != 0) { rg_pin &= ~bit(r); }
            }
            vi[id].reg = NOREG;
        }
        rg_kill_next++;
    }
}
// Whether pinned value id is still live after the current instruction.
fn rg_live_after(id: u32) -> bool {
    // (its kill, if in this block, is at or after the current instruction)
    for k in kl_start[cur_pos]..kl_start[cur_pos + 1] {
        if kl_list[k] == id { return false; }
    }
    return true;
}

// Under pressure (a lowering needs more scratch registers than the pinned
// values leave): a pinned value not used by the current instruction lends
// its register for the instruction; it goes to its home and comes back at
// the end of the instruction (rg_restore).
var rg_brr: u32[8] = [0; 8];
var rg_brid: u32[8] = [0; 8];
var rg_nborrow: u32 = 0;
fn rg_borrow(xm: u32) -> u32 {
    let m = ~r_lock & xm & rg_pin & r_alloc;
    if m == 0 || rg_nborrow == 8 {
        write_stderr(str("goovm: no register to borrow: function ", f_index, " instruction ", cur_pos, " op ",
                         M.insts[f_first_inst + cur_pos].op, " free ", r_free, " lock ", r_lock, " pin ", rg_pin,
                         " alloc ", r_alloc, " xm ", xm, " n ", rg_nborrow, "\n"));
        assert(false);
    }
    let r = ctz32(m);
    let id = r_val[r];
    if id >= RV_TEMP { assert(false); }
    let I = M.insts[f_first_inst + cur_pos];
    if I.op <= GIR_UNREACHABLE || I.op == GIR_INDIRECTBR { assert(false); }   // (no code after a terminator)
    if vi[id].st & ST_MEM == 0 { ra_store_home(id, r); }
    vi[id].reg = NOREG;
    r_val[r] = RV_NONE;
    rg_pin &= ~bit(r);
    rg_brr[rg_nborrow] = r;
    rg_brid[rg_nborrow] = id;
    rg_nborrow++;
    return r;
}
fn rg_restore() {
    for k in 0..rg_nborrow {
        let r = rg_brr[k];
        let id = rg_brid[k];
        if !rg_live_after(id) { continue; }
        let occ = r_val[r];
        if occ < RV_TEMP && occ != id { ra_evacuate(occ, r); }
        ra_load_from(r, ra_home(id), vtype(id));
        r_val[r] = id;
        r_free &= ~bit(r);
        vi[id].reg = r as! u8;
        rg_pin |= bit(r);
    }
    rg_nborrow = 0;
}
