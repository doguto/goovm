// SSA construction and cleanup on the OIR (opt.goose): use lists,
// promotion of allocas to SSA values (mem2reg, Cytron et al. with
// liveness-pruned PHI placement as LLVM's PromoteMemToReg does), trivial
// PHI removal and dead-code elimination.

// ------------------------------------------------------------ use lists

var u_start: u32[>..] = [];     // per instruction: users u_list[u_start[i] .. u_start[i + 1])
var u_list: u32[>..] = [];      // (an instruction that uses a value twice is listed twice)
var u_cnt: u32[>..] = [];

// Use lists of the live instructions (resolve_all first: operands are
// assumed resolved).
fn build_uses() {
    let n = o_ins.len;
    u_cnt.clear();
    u_cnt.resize(n + 1, 0);
    for i0 in 0..n {
        if o_blk[i0] == NIL { continue; }
        let i: u32 = i0 as! u32;
        each_slot(i) { s =>
            let v = vget(i, s);
            if gir_kind(v) == GIR_V_INST { u_cnt[v]++; }
        };
    }
    u_start.clear();
    var acc: u32 = 0;
    for i in 0..n {
        u_start.push(acc);
        acc += u_cnt[i];
        u_cnt[i] = 0;
    }
    u_start.push(acc);
    u_list.clear();
    u_list.resize(acc, 0);
    for i0 in 0..n {
        if o_blk[i0] == NIL { continue; }
        let i: u32 = i0 as! u32;
        each_slot(i) { s =>
            let v = vget(i, s);
            if gir_kind(v) == GIR_V_INST {
                u_list[u_start[v] + u_cnt[v]] = i;
                u_cnt[v]++;
            }
        };
    }
}
inline fn nuses(i: u32) -> u32 { u_start[i + 1] - u_start[i] }

// ------------------------------------------------------------- mem2reg

var m_var: u32[>..] = [];       // per instruction (alloca): its variable, NIL
var m_ty: u32[>..] = [];        // per variable: the type of its loads and stores
var m_bad: u8[>..] = [];        // per variable: not promoted after all (a PHI at a landing pad)
var m_cur: u32[>..] = [];       // renaming: current value per variable (NIL: undefined)
var m_undo: u32[>..] = [];      // renaming: (variable, old value) pairs
var m_phivar: u32[>..] = [];    // per instruction: the variable of a PHI placed here, NIL
// per variable: blocks that store it, blocks with a load before any store
var m_dhead: u32[>..] = [];
var m_uhead: u32[>..] = [];
var m_eblk: u32[>..] = [];
var m_enxt: u32[>..] = [];
var m_seen: u32[>..] = [];      // per variable: block stamp of the last store seen
var m_lastd: u32[>..] = [];     // per variable: last block added to its def list
var m_mark_def: u32[>..] = [];  // per block, epoch-stamped marks
var m_mark_live: u32[>..] = [];
var m_mark_phi: u32[>..] = [];
var m_epoch: u32 = 0;
var m_wl: u32[>..] = [];
var m_plv: u32[>..] = [];       // PHI placements: variable, block
var m_plb: u32[>..] = [];

// Whether a value of type t may be promoted (it lives in registers).
fn promotable_type(t: u32) -> bool {
    let c = cls_of(t);
    if c == C_INT || c == C_INT2 { return true; }
    if c == C_FP { return t != GIR_T_F16; }
    if c == C_VEC { return rc_of(t) == RC_VX; }
    return false;
}

// Promotes the entry block's allocas whose only uses are whole loads and
// stores of one type (build_cfg and build_uses first). Returns whether any
// was promoted.
fn mem2reg() -> bool {
    let n = o_ins.len;
    m_var.clear();
    m_var.resize(n, NIL);
    m_ty.clear();
    var nv: u32 = 0;
    var i = b_first[0];
    while i != NIL {
        let I = o_ins[i];
        if I.op == GIR_ALLOCA {
            let t = alloca_type(i);
            if t != NIL {
                m_var[i] = nv;
                m_ty.push(t);
                nv++;
            }
        }
        i = o_nxt[i];
    }
    if nv == 0 { return false; }
    let nb = cfg_nb;
    m_bad.clear();
    m_bad.resize(nv, 0);
    m_dhead.clear();
    m_dhead.resize(nv, NIL);
    m_uhead.clear();
    m_uhead.resize(nv, NIL);
    m_seen.clear();
    m_seen.resize(nv, NIL);
    m_lastd.clear();
    m_lastd.resize(nv, NIL);
    m_eblk.clear();
    m_enxt.clear();
    // def blocks and upward-exposed uses, one pass over the reachable blocks
    for b in rpo {
        var j = b_first[b];
        while j != NIL {
            let J = o_ins[j];
            if J.op == GIR_LOAD && gir_kind(J.a) == GIR_V_INST && m_var[J.a] != NIL {
                let v = m_var[J.a];
                if m_seen[v] != b {
                    m_seen[v] = b;    // (one entry per block is enough)
                    m_eblk.push(b);
                    m_enxt.push(m_uhead[v]);
                    m_uhead[v] = (m_eblk.len - 1) as! u32;
                }
            } else if J.op == GIR_STORE && gir_kind(J.b) == GIR_V_INST && m_var[J.b] != NIL {
                let v = m_var[J.b];
                m_seen[v] = b;
                if m_lastd[v] != b {
                    m_lastd[v] = b;
                    m_eblk.push(b);
                    m_enxt.push(m_dhead[v]);
                    m_dhead[v] = (m_eblk.len - 1) as! u32;
                }
            }
            j = o_nxt[j];
        }
    }
    build_df();
    if m_mark_def.len < nb {
        m_mark_def.resize(nb, 0);
        m_mark_live.resize(nb, 0);
        m_mark_phi.resize(nb, 0);
    }
    m_plv.clear();
    m_plb.clear();
    for v in 0..nv {
        m_epoch++;
        let ep = m_epoch;
        if ep == 0 { assert(false); }
        // live-in blocks: from the upward-exposed uses backwards, stopping at defs
        var e = m_dhead[v];
        while e != NIL {
            m_mark_def[m_eblk[e]] = ep;
            e = m_enxt[e];
        }
        m_wl.clear();
        e = m_uhead[v];
        while e != NIL {
            let b = m_eblk[e];
            if m_mark_live[b] != ep {
                m_mark_live[b] = ep;
                m_wl.push(b);
            }
            e = m_enxt[e];
        }
        while m_wl.len != 0 {
            let b = m_wl.pop();
            for k in p_start[b]..p_start[b + 1] {
                let p = p_list[k];
                if rpo_num[p] == NIL || m_mark_live[p] == ep || m_mark_def[p] == ep { continue; }
                m_mark_live[p] = ep;
                m_wl.push(p);
            }
        }
        // iterated dominance frontier of the defs, where live
        m_wl.clear();
        e = m_dhead[v];
        while e != NIL {
            m_wl.push(m_eblk[e]);
            e = m_enxt[e];
        }
        while m_wl.len != 0 {
            let b = m_wl.pop();
            var d = df_head[b];
            while d != NIL {
                let x = df_blk[d];
                d = df_nxt[d];
                if m_mark_phi[x] == ep || m_mark_live[x] != ep { continue; }
                m_mark_phi[x] = ep;
                m_plv.push(v);
                m_plb.push(x);
                if b_fl[x] & BF_LP != 0 { m_bad[v] = 1; }
                if m_mark_def[x] != ep {
                    m_mark_def[x] = ep;
                    m_wl.push(x);
                }
            }
        }
    }
    // the PHIs
    m_phivar.clear();
    m_phivar.resize(o_ins.len, NIL);
    for v, k in m_plv {
        if m_bad[v] != 0 { continue; }
        let b = m_plb[k];
        let np = p_start[b + 1] - p_start[b];
        let s = new_run(2 * np);
        let u = undef_of(m_ty[v]);
        for q in 0..np {
            o_ops[s + 2 * q] = u;
            o_ops[s + 2 * q + 1] = p_list[p_start[b] + q];
        }
        let ph = new_inst(Inst { op: GIR_PHI, sub: 0, flags: 0, ty: m_ty[v] as! u16, aux: 0, a: 0, b: s, c: np, dbg: 0 });
        m_phivar.push(v);
        link_start(b, ph);
    }
    for a in 0..n {
        let v = m_var[a];
        if v != NIL && m_bad[v] != 0 { m_var[a] = NIL; }
    }
    m2r_rename();
    // the allocas go
    i = b_first[0];
    while i != NIL {
        let nx = o_nxt[i];
        if i < n && m_var[i] != NIL { unlink(i); }
        i = nx;
    }
    return true;
}

// The type of alloca a's loads and stores if it can be promoted, NIL if not.
fn alloca_type(a: u32) -> u32 {
    var t: u32 = NIL;
    for k in u_start[a]..u_start[a + 1] {
        let u = u_list[k];
        let U = o_ins[u];
        var ut: u32 = NIL;
        if U.op == GIR_LOAD && U.a == a {
            ut = U.ty;
        } else if U.op == GIR_STORE && U.b == a && U.a != a {
            ut = U.aux;
        } else {
            return NIL;
        }
        if U.flags & (IF_VOLATILE | IF_ORD_MASK) != 0 { return NIL; }
        if t == NIL { t = ut; } else if t != ut { return NIL; }
    }
    if t == NIL { return NIL; }   // unused: DCE removes it
    if !promotable_type(t) || store_of(t) > o_ins[a].a { return NIL; }
    return t;
}

// The value of variable v now (its undefined value if none).
fn m2r_val(v: u32) -> u32 {
    let c = m_cur[v];
    if c == NIL { return undef_of(m_ty[v]); }
    return c;
}
fn m2r_set(v: u32, x: u32) {
    m_undo.push(v);
    m_undo.push(m_cur[v]);
    m_cur[v] = x;
}

// Renaming along the dominator tree (pre-order with an explicit stack).
fn m2r_rename() {
    m_cur.clear();
    m_cur.resize(m_ty.len, NIL);
    m_undo.clear();
    tmp_stack.clear();
    tmp_stack.push(0);
    tmp_pos.clear();
    tmp_pos.resize(cfg_nb, 0);
    while tmp_stack.len != 0 {
        let e = tmp_stack.pop();
        if e & 0x80000000 != 0 {
            // leaving the block: undo its definitions
            let mark = tmp_pos[e & 0x7FFFFFFF];
            while m_undo.len > mark {
                let old = m_undo.pop();
                let v = m_undo.pop();
                m_cur[v] = old;
            }
            continue;
        }
        let b = e;
        tmp_pos[b] = m_undo.len as! u32;
        var i = b_first[b];
        while i != NIL {
            let nx = o_nxt[i];
            let I = o_ins[i];
            if I.op == GIR_PHI {
                if i < m_phivar.len && m_phivar[i] != NIL { m2r_set(m_phivar[i], i); }
            } else if I.op == GIR_LOAD {
                let a = res(I.a);
                if gir_kind(a) == GIR_V_INST && a < m_var.len && m_var[a] != NIL { replace(i, m2r_val(m_var[a])); }
            } else if I.op == GIR_STORE {
                let a = res(I.b);
                if gir_kind(a) == GIR_V_INST && a < m_var.len && m_var[a] != NIL {
                    m2r_set(m_var[a], res(I.a));
                    unlink(i);
                }
            }
            i = nx;
        }
        // the PHI entries of this block's edges
        for k in s_start[b]..s_start[b + 1] {
            let s = s_list[k];
            var j = b_first[s];
            while j != NIL && o_ins[j].op == GIR_PHI {
                if j < m_phivar.len && m_phivar[j] != NIL {
                    let J = o_ins[j];
                    let x = m2r_val(m_phivar[j]);
                    for q in 0..J.c {
                        if o_ops[J.b + 2 * q + 1] == b { o_ops[J.b + 2 * q] = x; }
                    }
                }
                j = o_nxt[j];
            }
        }
        tmp_stack.push(b | 0x80000000);
        var c = dt_first[b];
        while c != NIL {
            tmp_stack.push(c);
            c = dt_next[c];
        }
    }
}

// --------------------------------------------------------- PHI cleanup

// Replaces the PHIs whose incoming values are all one value (or the PHI
// itself) by that value, until none is left. Returns whether any changed.
fn simplify_phis() -> bool {
    var any = false;
    var changed = true;
    while changed {
        changed = false;
        for b in rpo {
            var i = b_first[b];
            while i != NIL && o_ins[i].op == GIR_PHI {
                let nx = o_nxt[i];
                let I = o_ins[i];
                var same: u32 = NIL;
                var ok = true;
                for k in 0..I.c {
                    let v = res(o_ops[I.b + 2 * k]);
                    if v == i { continue; }
                    if same == NIL { same = v; } else if same != v { ok = false; break; }
                }
                if ok && same != NIL {
                    replace(i, same);
                    changed = true;
                    any = true;
                }
                i = nx;
            }
        }
    }
    return any;
}

// -------------------------------------------------------------- DCE

// Whether instruction I has an effect besides its value (it stays even if
// unused).
fn has_effect(I: Inst) -> bool {
    let op: u32 = I.op;
    if op == GIR_LOAD { return I.flags & (IF_VOLATILE | IF_ORD_MASK) != 0; }
    if op >= GIR_ADD && op <= GIR_BITCAST { return false; }   // binops, icmp, select, casts
    if op == GIR_ALLOCA || op == GIR_GEP || op == GIR_PHI { return false; }
    if op >= GIR_FADD && op <= GIR_SHUFFLE { return false; }  // FP, casts, aggregates, vectors
    if op >= GIR_CTLZ && op <= GIR_ISFPCLASS { return false; } // bit ops, ovf, scmp, fabs, ...
    if op == GIR_BLOCKADDR || op == GIR_X86 || op == GIR_TLSADDR { return false; }
    if op == GIR_FRAMEADDR || op == GIR_RETADDR || op == GIR_STACKSAVE || op == GIR_ISCONST { return false; }
    // (E2) a call that writes no memory, does not throw and returns
    if op == GIR_CALL { return I.flags & (IF_CALL_NOWRITE | IF_CALL_PURE | IF_INVOKE) != (IF_CALL_NOWRITE | IF_CALL_PURE); }
    return true;
}

var dce_live: u8[>..] = [];
// Deletes the instructions whose values nobody needs (mark from the
// instructions with effects). resolve_all first.
fn dce() -> bool {
    let n = o_ins.len;
    dce_live.clear();
    dce_live.resize(n, 0);
    tmp_stack.clear();
    for i in 0..n {
        if o_blk[i] == NIL { continue; }
        if has_effect(o_ins[i]) {
            dce_live[i] = 1;
            tmp_stack.push(i as! u32);
        }
    }
    while tmp_stack.len != 0 {
        let i = tmp_stack.pop();
        each_slot(i) { s =>
            let v = vget(i, s);
            if gir_kind(v) == GIR_V_INST && dce_live[v] == 0 && o_blk[v] != NIL {
                dce_live[v] = 1;
                tmp_stack.push(v);
            }
        };
    }
    var any = false;
    for i in 0..n {
        if o_blk[i] != NIL && dce_live[i] == 0 {
            unlink(i as! u32);
            any = true;
        }
    }
    return any;
}
