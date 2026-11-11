// AArch64 global register allocation for optimized code (milestone F1;
// the x86-64 allocator is rag.goose, DESIGN.md §16). The analysis is
// rag.goose's (live-in/live-out bitsets, live segments, clobber crossing,
// per-register occupancy bitmaps: rg_build_cfg, rg_liveness, rg_segments,
// rg_crossed, rg_free, rg_take); what is AArch64's is the candidate
// selection (AAPCS64 arguments), the clobber points, the register sets and
// the hooks into a64ra.goose / a64cg.goose.
//
//   GPRs   x19-x28 (callee-saved: values live across calls) and x2-x15;
//          x0/x1 (returns, the lowerings' fixed operands), x16/x17, x18 are
//          never pinned
//   V      v8-v15 (callee-saved, values of at most 8 bytes across calls),
//          v16-v30 and v2-v7; v0/v1 and v31 never
// A value live across a call or a memory-tier lowering (K_CALL, K_B) takes a
// callee-saved register or none; across inline assembly none.

let AR_GP_CALLEE: u64 = 0x1FF80000;          // x19..x28
let AR_GP_CALLER: u64 = 0x0000FFFC;          // x2..x15
let AR_V_CALLEE: u64 = 0x0000FF0000000000;   // v8..v15
let AR_V_CALLER: u64 = 0x7FFF00FC00000000;   // v2..v7, v16..v30

var a_rg_cs: u64 = 0;        // callee-saved registers of pinned values
var a_rg_pin: u64 = 0;       // registers holding pinned values now
var a_rg_hint: u32[>..] = [];   // per global value: preferred register (64: none)

// The argument register of parameter a if it arrives in one register of its
// class (a_parts after a_classify of the parameters), else 64.
fn a_rg_argreg(a: u32) -> u32 {
    let q0 = a_pfirst[a];
    if a_pfirst[a + 1] != q0 + 1 { return 64; }
    let P = a_parts[q0];
    let t = M.opnds[f_args + 2 * a];
    let c = arc(t);
    if P.kind == AP_X && c == ARC_GPR { return P.reg; }
    if P.kind == AP_V && a_inv(c) && P.size == M.types[t].store && a_plain(P) { return AV0 + P.reg; }
    return 64;
}

fn a_rg_alloc(insts: const Inst[:], blocks: const Block[:]) {
    rg_on = false;
    a_rg_cs = 0;
    a_rg_pin = 0;
    rg_kill_next = 0;
    let nv: i64 = f_nins as i64 + f_nargs;
    if rg_reg.len < nv {
        rg_reg.resize(nv, NOREG);
        rg_gid.resize(nv, NIL);
    }
    for q in 0..nv {
        rg_reg[q] = NOREG;
        rg_gid[q] = NIL;
    }
    let F = M.funcs[f_index];
    if F.flags & (FN_SJLJ | FN_RETURNS_TWICE) != 0 { return; }
    let nb: u32 = blocks.len as! u32;
    rg_nb = nb;
    rg_val.clear();
    a_classify_reset();
    for a in 0..f_nargs { a_classify(M.opnds[f_args + 2 * a], M.opnds[f_args + 2 * a + 1]); }
    a_classify_end();
    for a in 0..f_nargs {
        let id = f_nins + a;
        if a_rg_argreg(a) == 64 { continue; }
        if vi[id].st & (ST_GLOB | ST_KEEP) == ST_GLOB && vi[id].nuse != 0 {
            rg_gid[id] = rg_val.len as! u32;
            rg_val.push(id);
        }
    }
    for I, j in insts {
        if I.op == GIR_INDIRECTBR { return; }
        if I.ty == GIR_T_VOID || vi[j].nuse == 0 || vi[j].st & ST_KEEP != 0 { continue; }
        if vi[j].st & ST_GLOB == 0 && I.op != GIR_PHI { continue; }
        let c = arc(I.ty);
        if c == ARC_MEM || vi[j].home == H_ALLOCA || vi[j].home == H_PTR { continue; }
        rg_gid[j] = rg_val.len as! u32;
        rg_val.push(j as! u32);
    }
    let ng: u32 = rg_val.len as! u32;
    if ng == 0 { return; }
    rg_words = (ng as i64 + 63) >> 6;
    rg_build_cfg(blocks);
    // dense bitsets, or (larger functions) a walk from each use (rag.goose)
    if rg_words * nb as i64 * 64 > RG_MAX_BITS || opt_off("dense") {
        rg_liveness_sparse(insts);
    } else {
        rg_liveness(insts, blocks);
        rg_lists_from_bits();
    }
    rg_segments(insts, blocks);
    a_rg_clobbers(insts);
    a_rg_assign();
    if rg_on { a_rg_finish(insts, blocks); }
}

fn a_rg_clobbers(insts: const Inst[:]) {
    cl_pos.clear();
    cl_kind.clear();
    for I, j in insts {
        let k: u32 = vi[j].kind;
        var c: u8 = 0;
        if k == K_ALL { c = CL_ALL; }
        else if k == K_B || k == K_CALL { c = CL_CALL; }
        if c != 0 {
            cl_pos.push(2 * j as! u32 + 3);
            cl_kind.push(c);
        }
    }
}

fn a_rg_phi_hint(g: u32) -> u32 {
    if a_rg_hint[g] != 64 { return a_rg_hint[g]; }
    let id = rg_val[g];
    if id >= f_nins { return 64; }
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
    return 64;
}

fn a_rg_assign() {
    let ng: u32 = rg_val.len as! u32;
    let npos: i64 = 2 * f_nins as i64 + 4;
    rg_pw = (npos + 63) >> 6;
    rg_occ.clear();
    rg_occ.resize(64 * rg_pw, 0);
    a_rg_hint.clear();
    a_rg_hint.resize(ng, 64);
    // argument registers: busy until the last use of an argument that is not
    // a candidate (or its first use, for a global one in memory)
    var argm: u64 = 0;
    for a in 0..f_nargs {
        let r = a_rg_argreg(a);
        let id = f_nins + a;
        if r == 64 || vi[id].nuse == 0 { continue; }
        let g = rg_gid[id];
        if g != NIL {
            a_rg_hint[g] = r;
            argm |= abit(r);
        } else if vi[id].st & ST_GLOB == 0 {
            rg_block_range(r, 1, 2 * vi[id].last + 3);
        } else {
            rg_block_range(r, 1, 3);
        }
    }
    rg_order.clear();
    for g in 0..ng { rg_order.push(g); }
    sort(rg_order) { a, b => rg_weight[a] > rg_weight[b] || rg_weight[a] == rg_weight[b] && a < b };
    var any = false;
    for g in rg_order {
        let id = rg_val[g];
        let t = vtype(id);
        let c = arc(t);
        let cr = rg_crossed(g);
        var cand: u64 = 0;
        var pref: u64 = 0;
        if cr & ((1 as u32) << CL_ALL) != 0 { continue; }
        let calls = cr & ((1 as u32) << CL_CALL) != 0;
        if c == ARC_GPR {
            if calls { cand = AR_GP_CALLEE; pref = AR_GP_CALLEE; }
            else { cand = AR_GP_CALLEE | AR_GP_CALLER; pref = AR_GP_CALLER; }
        } else {
            let small = M.types[t].store <= 8;
            if calls {
                if !small { continue; }
                cand = AR_V_CALLEE;
                pref = AR_V_CALLEE;
            } else {
                cand = AR_V_CALLER | (if small { AR_V_CALLEE } else { 0 as u64 });
                pref = AR_V_CALLER;
            }
        }
        var r: u32 = 64;
        let h = a_rg_phi_hint(g);
        if h < 64 && cand & abit(h) != 0 && rg_free(h, g) { r = h; }
        if r == 64 {
            var m = cand & pref & ~argm;
            while m != 0 && r == 64 {
                let x = actz(m);
                m &= m - 1;
                if rg_free(x, g) { r = x; }
            }
            m = cand & pref & argm;
            while m != 0 && r == 64 {
                let x = actz(m);
                m &= m - 1;
                if rg_free(x, g) { r = x; }
            }
            m = cand & ~pref;
            while m != 0 && r == 64 {
                let x = actz(m);
                m &= m - 1;
                if rg_free(x, g) { r = x; }
            }
        }
        if r == 64 { continue; }
        rg_take(r, g);
        rg_reg[id] = r as! u8;
        if abit(r) & (A_GP_CALLEE | A_V_CALLEE) != 0 { a_rg_cs |= abit(r); }
        any = true;
    }
    rg_on = any;
}

// Kill lists, live-in lists, value states (rag.goose's rg_finish with the
// AArch64 register classes).
fn a_rg_finish(insts: const Inst[:], blocks: const Block[:]) {
    let nb = rg_nb;
    let w = rg_words;
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
    // a local value that feeds a pinned PHI is computed in the PHI's register when free
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
            if (arc(vtype(u)) == ARC_GPR) == (rg_reg[id] < 32) { vi[u].hint = rg_reg[id]; }
        }
    }
}

// ------------------------------------------------------------ code generation hooks

fn a_rg_put(id: u32) {
    let r: u32 = rg_reg[id];
    let occ = a_rval[r];
    if occ < RV_TEMP && occ != id { vi[occ].reg = NOREG; }
    a_rval[r] = id;
    vi[id].reg = r as! u8;
    vi[id].st &= ~ST_EXT;
    a_free &= ~abit(r);
    a_rg_pin |= abit(r);
    if abit(r) & (A_GP_CALLEE | A_V_CALLEE) != 0 { a_csused |= abit(r); }
}
fn a_rg_block_enter(b: u32) {
    a_rg_pin = 0;
    for k in li_start[b]..li_start[b + 1] { a_rg_put(li_list[k]); }
    let B = M.blocks[f_first_block + b];
    for gi in B.first_inst..B.first_inst + B.n_inst {
        if M.insts[gi].op != GIR_PHI { break; }
        let j = gi - f_first_inst;
        if rg_reg[j] != NOREG { a_rg_put(j); }
    }
    rg_kill_next = B.first_inst - f_first_inst;
}
// Pinned arguments move from their argument register to their own.
fn a_rg_entry_moves() {
    for a in 0..f_nargs {
        let id = f_nins + a;
        if rg_reg[id] == NOREG { continue; }
        let src: u32 = vi[id].reg;
        let dst: u32 = rg_reg[id];
        if src < 64 && src != dst {
            a_mvs.push(src);
            a_mvd.push(dst);
        }
    }
    for a in 0..f_nargs {
        let id = f_nins + a;
        let r: u32 = vi[id].reg;
        if r >= 64 || rg_reg[id] != NOREG { continue; }
        for d in a_mvd {
            if d == r {
                vi[id].reg = NOREG;
                a_rval[r] = RV_NONE;
                a_free |= abit(r);
            }
        }
    }
    if a_mvs.len != 0 { a_emit_moves(); }
    for a in 0..f_nargs {
        let id = f_nins + a;
        if rg_reg[id] == NOREG { continue; }
        let r: u32 = vi[id].reg;
        if r < 64 && r != rg_reg[id] && a_rval[r] == id {
            a_rval[r] = RV_NONE;
            a_free |= abit(r);
        }
        let ext = vi[id].st & ST_EXT != 0;
        a_rg_put(id);
        if ext && rg_reg[id] < 32 { a_zext(rg_reg[id], bits_of(vtype(id))); }
    }
}
fn a_rg_def_start(j: u32) {
    let r: u32 = rg_reg[j];
    let occ = a_rval[r];
    if occ < RV_TEMP && occ != j { a_evacuate(occ, r); }
    a_free &= ~abit(r);
    a_rval[r] = RV_TEMP;
    a_rg_pin |= abit(r);
    if abit(r) & (A_GP_CALLEE | A_V_CALLEE) != 0 { a_csused |= abit(r); }
}
// After the lowering of j (pinned): a lowering that wrote the value to its
// home leaves it to be loaded.
fn a_rg_def_end(j: u32) {
    let r: u32 = rg_reg[j];
    if vi[j].reg == r as! u8 || M.insts[f_first_inst + j].op == GIR_PHI { return; }
    a_load_t(r, AFP, a_home_off(j) as i64, vtype(j));
    let occ = a_rval[r];
    if occ < RV_TEMP && occ != j { vi[occ].reg = NOREG; }
    a_rval[r] = j;
    vi[j].reg = r as! u8;
    vi[j].st &= ~ST_EXT;
    a_free &= ~abit(r);
    a_tmp &= ~abit(r);
    a_rg_pin |= abit(r);
}
fn a_rg_kills() {
    while rg_kill_next <= cur_pos {
        let j = rg_kill_next;
        for k in kl_start[j]..kl_start[j + 1] {
            let id = kl_list[k];
            let r: u32 = rg_reg[id];
            if a_rval[r] == id {
                a_rval[r] = RV_NONE;
                a_free |= abit(r);
            }
            a_rg_pin &= ~abit(r);
            vi[id].reg = NOREG;
        }
        rg_kill_next++;
    }
}
// Register pressure: a pinned value the current instruction does not use
// lends its register (stored to its home, reloaded at the end).
var a_brr: u32[8] = [0; 8];
var a_brid: u32[8] = [0; 8];
var a_nborrow: u32 = 0;
fn a_rg_borrow(xm: u64) -> u32 {
    let m = ~a_lock & xm & a_rg_pin & a_alloc;
    if m == 0 || a_nborrow == 8 {
        write_stderr(str("goovm: aarch64: no register to borrow: function ", f_index, " instruction ", cur_pos, "\n"));
        assert(false);
    }
    let r = actz(m);
    let id = a_rval[r];
    if id >= RV_TEMP { assert(false); }
    a_store_home(id, r);
    vi[id].reg = NOREG;
    a_rval[r] = RV_NONE;
    a_rg_pin &= ~abit(r);
    a_brr[a_nborrow] = r;
    a_brid[a_nborrow] = id;
    a_nborrow++;
    return r;
}
fn a_rg_restore() {
    for k in 0..a_nborrow {
        let r = a_brr[k];
        let id = a_brid[k];
        if !rg_live_after(id) { continue; }
        let occ = a_rval[r];
        if occ < RV_TEMP && occ != id { a_evacuate(occ, r); }
        a_load_t(r, AFP, a_home_off(id) as i64, vtype(id));
        a_rval[r] = id;
        a_free &= ~abit(r);
        vi[id].reg = r as! u8;
        a_rg_pin |= abit(r);
    }
    a_nborrow = 0;
}
// Whether the edge from -> to has PHI moves that emit code.
fn a_edge_phi(from: u32, to: u32) -> bool {
    if !a_has_phi(to) { return false; }
    if !rg_on { return true; }
    let B = M.blocks[f_first_block + to];
    for k in B.first_inst..B.first_inst + B.n_inst {
        let I = M.insts[k];
        if I.op != GIR_PHI { break; }
        let j = k - f_first_inst;
        if vi[j].nuse == 0 { continue; }
        if vi[j].st & ST_PIN == 0 { return true; }
        let d: u32 = rg_reg[j];
        for p in 0..I.c {
            if M.opnds[I.b + 2 * p + 1] != from { continue; }
            let v = M.opnds[I.b + 2 * p];
            if !is_val(v) { return true; }
            let r: u32 = vi[vid(v)].reg;
            if r != d || (r < 32 && vi[vid(v)].st & ST_EXT != 0) { return true; }
            break;
        }
    }
    return false;
}
// PHI moves with pinned PHIs: memory PHIs first, then a parallel copy of the
// registers, then the incoming values that are not in registers.
fn a_phi_moves_rg(from: u32, to: u32) {
    let B = M.blocks[f_first_block + to];
    var npin = 0;
    for k in B.first_inst..B.first_inst + B.n_inst {
        let I = M.insts[k];
        if I.op != GIR_PHI { break; }
        let j = k - f_first_inst;
        if vi[j].nuse == 0 { continue; }
        if vi[j].st & ST_PIN != 0 {
            npin++;
            continue;
        }
        for p in 0..I.c {
            if M.opnds[I.b + 2 * p + 1] != from { continue; }
            a_phi_copy(a_phi_dst(to, j), M.opnds[I.b + 2 * p], I.ty);
            break;
        }
    }
    if npin == 0 { return; }
    for pass in 2 {
        for k in B.first_inst..B.first_inst + B.n_inst {
            let I = M.insts[k];
            if I.op != GIR_PHI { break; }
            let j = k - f_first_inst;
            if vi[j].nuse == 0 || vi[j].st & ST_PIN == 0 { continue; }
            let dst: u32 = rg_reg[j];
            for p in 0..I.c {
                if M.opnds[I.b + 2 * p + 1] != from { continue; }
                let v = M.opnds[I.b + 2 * p];
                var src: u32 = 64;
                if is_val(v) {
                    let id = vid(v);
                    let r: u32 = vi[id].reg;
                    if r < 64 {
                        src = r;
                        if pass == 0 && r < 32 && vi[id].st & ST_EXT != 0 { a_norm(id, r); }
                    }
                }
                if pass == 0 && src < 64 {
                    a_mvs.push(src);
                    a_mvd.push(dst);
                } else if pass == 1 && src == 64 {
                    if dst >= 32 { a_mat_v(v, dst); } else { a_mat_gpr(v, dst); }
                }
                break;
            }
        }
        if pass == 0 && a_mvs.len != 0 { a_emit_moves(); }
    }
}
