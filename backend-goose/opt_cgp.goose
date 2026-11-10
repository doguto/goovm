// Preparation for code generation (milestone E2, LLVM's CodeGenPrepare):
// the last pass of the middle-end (opt.goose).
//
// Address sinking: a GEP that x86 can fold into a memory operand (a
// constant offset, or one index scaled by 1, 2, 4 or 8) is cloned right
// before every load and store that uses it as its address, unless it is
// already the instruction right before its only user. The code generator
// folds a single-use GEP into the next instruction's address (DESIGN.md
// §5), so `p->a`, `p->b`, `p->c` in three blocks are three memory operands
// off the one register that holds p, instead of three pointers computed
// once and kept live (in registers or frame slots) across the blocks.

var cg_users: u32[>..] = [];

// Whether GEP I fits an x86 address mode.
fn cgp_foldable(I: Inst) -> bool {
    if I.c > 1 { return false; }
    let off = (o_ops[I.b] as u64 | (o_ops[I.b + 1] as u64 << 32)) as! i64;
    if off < -0x80000000 || off > 0x7FFFFFFF { return false; }
    if I.c == 1 {
        let sc = o_ops[I.b + 3];
        if sc != 1 && sc != 2 && sc != 4 && sc != 8 { return false; }
    }
    return true;
}

fn sink_addrs() -> bool {
    resolve_all();
    build_uses();
    var any = false;
    let n: u32 = o_ins.len as! u32;
    for g in 0..n {
        if o_blk[g] == NIL { continue; }
        let G = o_ins[g];
        if G.op != GIR_GEP || !cgp_foldable(G) { continue; }
        let nu = u_start[g + 1] - u_start[g];
        if nu == 0 { continue; }
        cg_users.clear();
        for q in u_start[g]..u_start[g + 1] {
            let u = u_list[q];
            if o_blk[u] == NIL { continue; }
            let U = o_ins[u];
            let addr = U.op == GIR_LOAD && res(U.a) == g || U.op == GIR_STORE && res(U.b) == g && res(U.a) != g;
            if !addr { continue; }
            // (already folded: the only user, right after the GEP)
            if nu == 1 && o_nxt[g] == u { continue; }
            cg_users.push(u);
        }
        for u in cg_users {
            let c = new_inst(G);
            let s = new_run(2 + 2 * G.c);
            for k in 0..2 + 2 * G.c { o_ops[s + k] = o_ops[G.b + k]; }
            o_ins[c].b = s;
            o_ins[c].dbg = o_ins[u].dbg;
            link_before(u, c);
            if o_ins[u].op == GIR_LOAD { o_ins[u].a = c; } else { o_ins[u].b = c; }
            any = true;
        }
    }
    if any { dce(); }
    return any;
}
