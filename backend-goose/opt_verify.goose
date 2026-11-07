// A verifier of the OIR after optimization (GOOVM_OPT=verify), for
// testing: every instruction operand is defined by a live instruction that
// dominates the use (a PHI operand: the end of its predecessor), PHIs are
// at the start of their block with one entry per CFG edge, every block ends
// in one terminator, allocas are in the entry block. A violation is printed
// with the function and the instruction, and aborts.

var vf_pos: u32[>..] = [];      // per instruction: its position in its block

fn vf_fail(msg: const u8[:], i: u32) {
    let G = M.globals[o_f.global];
    write_stderr(str("goovm: verify: ", msg, " at instruction ", i, " (op ", o_ins[i].op, ") of ",
                     M.strtab[G.name..G.name + G.name_len], "\n"));
    assert(false);
}
// Whether the definition v reaches the use at instruction u (or, for a PHI
// operand, the end of block p).
fn vf_dominates(v: u32, u: u32, p: u32) -> bool {
    let db = o_blk[v];
    if db == NIL { return false; }
    if p != NIL {
        if rpo_num[p] == NIL { return true; }   // (an unreachable predecessor)
        return dominates(db, p);
    }
    let ub = o_blk[u];
    if db == ub { return vf_pos[v] < vf_pos[u]; }
    return dominates(db, ub);
}
fn opt_verify() {
    build_cfg();
    if vf_pos.len < o_ins.len { vf_pos.resize(o_ins.len, 0); }
    for b in rpo {
        var k: u32 = 0;
        var i = b_first[b];
        var phis = true;
        while i != NIL {
            vf_pos[i] = k;
            k++;
            let op: u32 = o_ins[i].op;
            if op == GIR_PHI && !phis { vf_fail("PHI after a non-PHI", i); }
            if op != GIR_PHI { phis = false; }
            if is_term_op(op) && i != b_last[b] { vf_fail("terminator inside a block", i); }
            if op == GIR_ALLOCA && b != 0 { vf_fail("alloca outside the entry block", i); }
            i = o_nxt[i];
        }
        if b_last[b] == NIL || !is_term_op(o_ins[b_last[b]].op) { vf_fail("block without a terminator", b_first[b]); }
    }
    for b in rpo {
        var i = b_first[b];
        while i != NIL {
            let I = o_ins[i];
            if I.op == GIR_PHI {
                let np = p_start[b + 1] - p_start[b];
                if I.c != np { vf_fail("PHI entries do not match the predecessors", i); }
                for k in 0..I.c {
                    let v = res(o_ops[I.b + 2 * k]);
                    let p = o_ops[I.b + 2 * k + 1];
                    var found = false;
                    for q in p_start[b]..p_start[b + 1] { if p_list[q] == p { found = true; } }
                    if !found { vf_fail("PHI entry from a block that is not a predecessor", i); }
                    if is_inst(v) && !vf_dominates(v, i, p) { vf_fail("PHI operand does not dominate its edge", i); }
                }
            } else {
                each_slot(i) { s =>
                    let v = res(vget(i, s));
                    if is_inst(v) && !vf_dominates(v, i, NIL) { vf_fail("operand does not dominate its use", i); }
                };
            }
            i = o_nxt[i];
        }
    }
}
