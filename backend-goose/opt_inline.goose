// Inlining (opt.goose): functions are optimized callees first (a post-order
// of the call graph), so a call is replaced by a copy of the callee's
// optimized body out of the output tables. The cost model (E2) is LLVM's
// InlineCost on GIR instructions (LLVM's InstrCost of 5 is one
// instruction): the callee is evaluated at the call site, with the
// constant arguments folded through it and the branches they decide
// pruned; loads, stores and constant GEPs of memory SROA will split (the
// callee's allocas, the caller's allocas passed as arguments, unless the
// callee lets the pointer escape) and no-op casts are free, a call costs
// the call penalty; the call site's own cost is subtracted. Thresholds as
// LLVM's (225, 250 at -O3, 75 for an optsize caller, 25 minsize, 325 for
// an inlinehint callee, 45 for a cold one, half again for a callee of one
// block, a large bonus for the last call of an internal function, which is
// then not emitted); always_inline always; noinline and bodies that cannot
// be copied (va_start, dynamic allocas, setjmp, frame/return addresses,
// landing pads and invokes, block addresses) never. A call that is an
// invoke is not inlined. The caller grows by at most a few thousand
// instructions.

let INL_ONCE: u32 = 3000;       // LLVM's LastCallToStaticBonus (15000 / 5)
let INL_GROWTH: u32 = 4000;     // instructions a caller may grow by
let INL_PENALTY: u32 = 5;       // LLVM's CallPenalty (25 / 5)
var ic_st: u8[>..] = [];        // cost model, per callee instruction: IC_*
var ic_val: u64[>..] = [];      //   its constant value (IC_CONST)
var ic_root: u32[>..] = [];     //   IC_SROA: its root (argument k, or IC_AL | callee alloca)
var ic_live: u8[>..] = [];      //   per callee block: reachable
var ic_wl: u32[>..] = [];
var ic_arg_st: u8[>..] = [];    //   per argument of the call
var ic_arg_val: u64[>..] = [];
var ic_sroa_ok: u8[>..] = [];   //   per root: still SROA-able (arguments first, then allocas)
let IC_UNK: u8 = 0;
let IC_CONST: u8 = 1;
let IC_SROA: u8 = 2;
let IC_AL: u32 = 0x80000000;
let FN_DEAD: u32 = 0x800000;    // output GirFunc flag (bit 23, reserved for back-ends): all calls were inlined; not emitted

var fn_done: u8[>..] = [];      // per function: stored (optimized) in the output tables
var fn_size: u32[>..] = [];     // its size then
var fn_inl: u8[>..] = [];       // its body may be inlined
var fn_calls: u32[>..] = [];    // direct call sites left in the module
var fn_addr: u8[>..] = [];      // its address is taken (or it is an alias target)
var cg_start: u32[>..] = [];    // call graph: direct callees (funcs indices)
var cg_list: u32[>..] = [];
var inl_cand: u32[>..] = [];
var inl_rets: u32[>..] = [];    // (value, block) pairs of the copied returns

// The funcs index of the function that call I calls directly, or NIL.
fn callee_of(I: Inst) -> u32 {
    if gir_kind(I.a) != GIR_V_GLOBAL { return NIL; }
    let G = M.globals[gir_idx(I.a)];
    if G.kind != G_FUNC || G.func == GIR_NONE { return NIL; }
    return G.func;
}

// Call counts, address-taken functions and the call graph of the input.
fn inl_scan() {
    let nf = M.funcs.len;
    fn_done.clear();
    fn_done.resize(nf, 0);
    fn_size.clear();
    fn_size.resize(nf, 0);
    fn_inl.clear();
    fn_inl.resize(nf, 0);
    fn_calls.clear();
    fn_calls.resize(nf, 0);
    fn_addr.clear();
    fn_addr.resize(nf, 0);
    cg_start.clear();
    cg_list.clear();
    for F in M.funcs {
        cg_start.push(cg_list.len as! u32);
        for gi in F.first_inst..F.first_inst + F.n_inst {
            let I = M.insts[gi];
            let op: u32 = I.op;
            if op == GIR_CALL {
                let c = callee_of(I);
                if c != NIL {
                    fn_calls[c]++;
                    cg_list.push(c);
                }
                for k in 0..I.c { inl_note_addr(M.opnds[I.b + 2 * k]); }
                continue;
            }
            let m: u32 = if op < GIR_NOPS { OP_VAL[op] } else { 7 };
            if m & OV_A != 0 { inl_note_addr(I.a); }
            if m & OV_B != 0 { inl_note_addr(I.b); }
            if m & OV_C != 0 { inl_note_addr(I.c); }
            if op == GIR_GEP { for k in 0..I.c { inl_note_addr(M.opnds[I.b + 2 + 2 * k]); } }
            else if op == GIR_PHI { for k in 0..I.c { inl_note_addr(M.opnds[I.b + 2 * k]); } }
            else if op == GIR_ASM {
                let A = M.asms[I.a];
                for k in 0..A.n_in { inl_note_addr(M.opnds[A.ops + 2 * k]); }
            }
        }
    }
    cg_start.push(cg_list.len as! u32);
    for d in M.drelocs { inl_note_addr(GIR_V_GLOBAL << 30 | d.target); }
    for G in M.globals {
        if G.kind == G_ALIAS { inl_note_addr(GIR_V_GLOBAL << 30 | G.func); }
    }
}
fn inl_note_addr(v: u32) {
    if gir_kind(v) != GIR_V_GLOBAL || v == GIR_NONE { return; }
    let G = M.globals[gir_idx(v)];
    if G.kind == G_FUNC && G.func != GIR_NONE { fn_addr[G.func] = 1; }
}

// Callees before callers: an iterative post-order DFS of the call graph.
fn opt_order() {
    fn_order.clear();
    let nf: u32 = M.funcs.len as! u32;
    tmp_pos.clear();
    tmp_pos.resize(nf, NIL);    // NIL = unvisited, else next callee position
    tmp_stack.clear();
    for r in 0..nf {
        if tmp_pos[r] != NIL { continue; }
        tmp_pos[r] = cg_start[r];
        tmp_stack.push(r);
        while tmp_stack.len != 0 {
            let f = tmp_stack[tmp_stack.len - 1];
            let k = tmp_pos[f];
            if k < cg_start[f + 1] {
                tmp_pos[f] = k + 1;
                let c = cg_list[k];
                if tmp_pos[c] == NIL {
                    tmp_pos[c] = cg_start[c];
                    tmp_stack.push(c);
                }
            } else {
                tmp_stack.pop();
                fn_order.push(f);
            }
        }
    }
}

// Before the OIR function is stored: its size and whether it may be inlined.
fn inl_record() {
    var n: u32 = 0;
    var ok = !o_addr;
    let fl = o_f.flags;
    if fl & (FN_VASTART | FN_SJLJ | FN_RETURNS_TWICE | FN_NOINLINE | FN_OPTNONE) != 0 { ok = false; }
    for a in 0..o_f.n_args {
        let w = M.opnds[o_f.args + 2 * a + 1];
        if w & ABI_BYVAL != 0 && abi_size(w) > 4096 { ok = false; }
    }
    for i in 0..o_ins.len {
        if o_blk[i] == NIL { continue; }
        let I = o_ins[i];
        let op: u32 = I.op;
        if op != GIR_PHI && op != GIR_ALLOCA && op != GIR_BR { n++; }
        if op == GIR_DYNALLOCA || op == GIR_STACKSAVE || op == GIR_STACKRESTORE || op == GIR_VASTART
           || op == GIR_FRAMEADDR || op == GIR_RETADDR || op == GIR_SJLJ_SETJMP || op == GIR_SJLJ_LONGJMP
           || op == GIR_LANDINGPAD || op == GIR_INDIRECTBR || op == GIR_BLOCKADDR {
            ok = false;
        }
        if op == GIR_CALL && I.flags & IF_INVOKE != 0 { ok = false; }
    }
    fn_size[o_fi] = n;
    fn_inl[o_fi] = if ok { 1 } else { 0 };
    fn_done[o_fi] = 1;
}


// Inlines the calls the cost model accepts (build_cfg and build_loops
// first: loop depths). Returns whether any call was inlined.
fn inline_calls() -> bool {
    if o_pinned { return false; }
    inl_cand.clear();
    var size: u32 = 0;
    for b in rpo {
        var i = b_first[b];
        while i != NIL { size++; i = o_nxt[i]; }
    }
    for b in rpo {
        var i = b_first[b];
        while i != NIL {
            let I = o_ins[i];
            if I.op == GIR_CALL && I.flags & (IF_INVOKE | IF_NOINLINE_CALL) == 0 {
                let c = callee_of(I);
                if c != NIL && c != o_fi && fn_done[c] != 0 && fn_inl[c] != 0 && inl_args_ok(i, c) {
                    let F = M.funcs[c];
                    var want = F.flags & FN_ALWAYSINLINE != 0 || I.flags & IF_ALWAYSINLINE_CALL != 0;
                    if !want { want = inl_profitable(i, c); }
                    if want { inl_cand.push(i); }
                }
            }
            i = o_nxt[i];
        }
    }
    if inl_cand.len == 0 { return false; }
    let limit = size + INL_GROWTH;
    var any = false;
    for c in inl_cand {
        if o_blk[c] == NIL { continue; }
        let cfi = callee_of(o_ins[c]);
        if size + fn_size[cfi] > limit && M.funcs[cfi].flags & FN_ALWAYSINLINE == 0
           && o_ins[c].flags & IF_ALWAYSINLINE_CALL == 0 { continue; }
        if o_ins[c].flags & IF_VARARG != 0 && M.funcs[cfi].flags & FN_VARARG == 0 { continue; }
        inline_call(c, cfi);
        size += fn_size[cfi];
        fn_calls[cfi]--;
        any = true;
    }
    return any;
}

// The arguments of call i match callee c's parameters (a variadic callee:
// at least as many; the extra ones are dropped).
fn inl_args_ok(i: u32, c: u32) -> bool {
    let I = o_ins[i];
    let F = M.funcs[c];
    if F.flags & FN_VARARG != 0 { return I.c >= F.n_args; }
    return I.c == F.n_args;
}

// LLVM's threshold for inlining callee c into the function being
// optimized (in GIR instructions).
fn inl_threshold(c: u32) -> u32 {
    let F = M.funcs[c];
    var t: u32 = if opt_lv >= 3 { 50 } else { 45 };
    if F.flags & FN_INLINEHINT != 0 { t = 65; }
    if F.flags & FN_COLD != 0 && t > 9 { t = 9; }
    let cf = o_f.flags;
    if cf & FN_MINSIZE != 0 && t > 5 { t = 5; }
    else if cf & FN_OPTSIZE != 0 && t > 15 { t = 15; }
    return t;
}

// The state of a value in the callee during the cost evaluation.
fn ic_get(v: u32, F2: Func) -> u8, u64, u32 {
    let k = gir_kind(v);
    if k == GIR_V_INST {
        let x = gir_idx(v) - F2.first_inst;
        if x >= F2.n_inst { return IC_UNK, 0, 0; }
        return ic_st[x], ic_val[x], ic_root[x];
    }
    if k == GIR_V_ARG {
        let a = gir_idx(v);
        if a >= ic_arg_st.len { return IC_UNK, 0, 0; }
        return ic_arg_st[a], ic_arg_val[a], a;
    }
    if k == GIR_V_CONST {
        let ok, x = ci(v);
        if ok { return IC_CONST, x, 0; }
    }
    return IC_UNK, 0, 0;
}
// A use of v that is not a load/store address or a constant GEP base: the
// SROA root it is based on is no longer SROA-able.
fn ic_escape(v: u32, F2: Func) {
    let s, x, r = ic_get(v, F2);
    if s != IC_SROA { return; }
    let k = if r & IC_AL != 0 { ic_arg_st.len as! u32 + (r & ~IC_AL) } else { r };
    if k < ic_sroa_ok.len { ic_sroa_ok[k] = 0; }
}
fn ic_ok(r: u32) -> bool {
    let k = if r & IC_AL != 0 { ic_arg_st.len as! u32 + (r & ~IC_AL) } else { r };
    return k < ic_sroa_ok.len && ic_sroa_ok[k] != 0;
}

// The caller value v, if it is (a constant GEP of) an alloca of the caller.
fn inl_is_alloca_ptr(v0: u32) -> bool {
    var v = res(v0);
    var n = 0;
    while is_inst(v) && n < 8 {
        let I = o_ins[v];
        if I.op == GIR_ALLOCA { return true; }
        if I.op != GIR_GEP || I.c != 0 { return false; }
        v = res(I.a);
        n++;
    }
    return false;
}

// Whether inlining call i of callee c pays by LLVM's cost model.
fn inl_profitable(i: u32, c: u32) -> bool {
    let F = M.funcs[c];
    let F2 = x_funcs[xb_f + c];
    let C = o_ins[i];
    var thr: u32 = inl_threshold(c);
    let once = F.flags & FN_INTERNAL != 0 && fn_calls[c] == 1 && fn_addr[c] == 0
               && (M.gcomdat.len == 0 || M.gcomdat[F.global] == GIR_NONE);
    // the call site: its arguments
    ic_arg_st.clear();
    ic_arg_val.clear();
    ic_sroa_ok.clear();
    for k in 0..F2.n_args {
        let v = res(o_ops[C.b + 2 * k]);
        let ok, x = ci(v);
        if ok {
            ic_arg_st.push(IC_CONST);
            ic_arg_val.push(x);
        } else if inl_is_alloca_ptr(v) {
            ic_arg_st.push(IC_SROA);
            ic_arg_val.push(0);
        } else {
            ic_arg_st.push(IC_UNK);
            ic_arg_val.push(0);
        }
        ic_sroa_ok.push(1);
    }
    let n = F2.n_inst;
    if ic_st.len < n {
        ic_st.resize(n, 0);
        ic_val.resize(n, 0);
        ic_root.resize(n, 0);
    }
    // the callee's allocas are SROA roots too (by instruction position)
    for x in 0..n {
        ic_sroa_ok.push(1);
        ic_st[x] = IC_UNK;
    }
    // pass 1, layout order: constants and SROA pointers
    for x in 0..n {
        let I = x_insts[xb_i + F2.first_inst + x];
        let op: u32 = I.op;
        var st: u8 = IC_UNK;
        var val: u64 = 0;
        var root: u32 = 0;
        if op == GIR_ALLOCA {
            st = IC_SROA;
            root = IC_AL | x;
        } else if op == GIR_GEP {
            let sa, va, ra = ic_get(I.a, F2);
            if sa == IC_SROA && I.c == 0 { st = IC_SROA; root = ra; }
            else {
                ic_escape(I.a, F2);
                for k in 0..I.c { ic_escape(x_opnds[xb_o + I.b + 2 + 2 * k], F2); }
            }
        } else if op == GIR_LOAD {
            // (the address is fine)
        } else if op == GIR_STORE {
            ic_escape(I.a, F2);
        } else if op >= GIR_ADD && op <= GIR_ASHR && int_ty(I.ty) && bits_of(I.ty) <= 64 {
            let sa, va, ra = ic_get(I.a, F2);
            let sb, vb, rb = ic_get(I.b, F2);
            if sa == IC_CONST && sb == IC_CONST {
                let ok, r = fold_bin(op, bits_of(I.ty), va, vb);
                if ok { st = IC_CONST; val = r; }
            }
        } else if op == GIR_ICMP && int_ty(I.aux) && bits_of(I.aux) <= 64 {
            let sa, va, ra = ic_get(I.a, F2);
            let sb, vb, rb = ic_get(I.b, F2);
            if sa == IC_CONST && sb == IC_CONST {
                st = IC_CONST;
                val = if fold_icmp(I.sub, bits_of(I.aux), va, vb) { 1 } else { 0 };
            } else {
                ic_escape(I.a, F2);
                ic_escape(I.b, F2);
            }
        } else if op == GIR_SELECT {
            let sa, va, ra = ic_get(I.a, F2);
            if sa == IC_CONST {
                let s2, v2, r2 = ic_get(if va & 1 != 0 { I.b } else { I.c }, F2);
                if s2 == IC_CONST { st = IC_CONST; val = v2; }
            }
            ic_escape(I.b, F2);
            ic_escape(I.c, F2);
        } else if (op == GIR_ZEXT || op == GIR_TRUNC) && int_ty(I.ty) && bits_of(I.ty) <= 64 {
            let sa, va, ra = ic_get(I.a, F2);
            if sa == IC_CONST { st = IC_CONST; val = va & wmask(bits_of(I.ty)); }
        } else if op == GIR_SEXT && int_ty(I.ty) && bits_of(I.ty) <= 64 && int_ty(I.aux) {
            let sa, va, ra = ic_get(I.a, F2);
            if sa == IC_CONST { st = IC_CONST; val = (sx(va, bits_of(I.aux)) as! u64) & wmask(bits_of(I.ty)); }
        } else if op == GIR_MEMCPY || op == GIR_MEMSET {
            // (constant-size copies of SROA memory are split by SROA)
        } else if op == GIR_PHI {
            for k in 0..I.c { ic_escape(x_opnds[xb_o + I.b + 2 * k], F2); }
        } else if op == GIR_CALL {
            for k in 0..I.c { ic_escape(x_opnds[xb_o + I.b + 2 * k], F2); }
        } else if op == GIR_RET {
            ic_escape(I.a, F2);
        } else {
            let m: u32 = if op < GIR_NOPS { OP_VAL[op] } else { 7 };
            if m & OV_A != 0 { ic_escape(I.a, F2); }
            if m & OV_B != 0 { ic_escape(I.b, F2); }
            if m & OV_C != 0 { ic_escape(I.c, F2); }
        }
        ic_st[x] = st;
        ic_val[x] = val;
        ic_root[x] = root;
    }
    // pass 2: the blocks the constants leave reachable
    let nb = F2.n_blocks;
    ic_live.clear();
    ic_live.resize(nb, 0);
    ic_wl.clear();
    ic_live[0] = 1;
    ic_wl.push(0);
    var nlive: u32 = 0;
    while ic_wl.len != 0 {
        let b = ic_wl.pop();
        nlive++;
        let B = x_blocks[xb_b + F2.first_block + b];
        if B.n_inst == 0 { continue; }
        let T = x_insts[xb_i + B.first_inst + B.n_inst - 1];
        let op: u32 = T.op;
        if op == GIR_BR { ic_mark(T.a); }
        else if op == GIR_CONDBR {
            let s, v, r = ic_get(T.a, F2);
            if s == IC_CONST { ic_mark(if v & 1 != 0 { T.b } else { T.c }); }
            else {
                ic_mark(T.b);
                ic_mark(T.c);
            }
        } else if op == GIR_SWITCH {
            let s, v, r = ic_get(T.a, F2);
            var hit: u32 = NIL;
            if s == IC_CONST {
                hit = x_opnds[xb_o + T.b];
                for k in 0..T.c {
                    let ok, cv = ci(x_opnds[xb_o + T.b + 1 + 2 * k]);
                    if ok && cv == v { hit = x_opnds[xb_o + T.b + 2 + 2 * k]; }
                }
                ic_mark(hit);
            } else {
                ic_mark(x_opnds[xb_o + T.b]);
                for k in 0..T.c { ic_mark(x_opnds[xb_o + T.b + 2 + 2 * k]); }
            }
        } else if op == GIR_INDIRECTBR {
            for k in 0..T.c { ic_mark(x_opnds[xb_o + T.b + k]); }
        }
        if B.n_inst >= 2 {
            let P = x_insts[xb_i + B.first_inst + B.n_inst - 2];
            if P.op == GIR_CALL && P.flags & IF_INVOKE != 0 { ic_mark(x_opnds[xb_o + P.b + 2 * P.c]); }
        }
    }
    // pass 3: the cost of the reachable code
    if nlive == 1 { thr += thr / 2; }          // LLVM's single-block bonus
    if once { thr += INL_ONCE; }
    let budget: u32 = thr + 1 + F2.n_args + INL_PENALTY;   // (the call site's own cost goes)
    var cost: u32 = 0;
    for b in 0..nb {
        if ic_live[b] == 0 { continue; }
        let B = x_blocks[xb_b + F2.first_block + b];
        for gi in B.first_inst..B.first_inst + B.n_inst {
            let x = gi - F2.first_inst;
            let I = x_insts[xb_i + gi];
            let op: u32 = I.op;
            if ic_st[x] == IC_CONST { continue; }
            if op == GIR_PHI || op == GIR_ALLOCA || op == GIR_BR || op == GIR_RET { continue; }
            if op == GIR_BITCAST || op == GIR_PTRTOINT || op == GIR_INTTOPTR || op == GIR_TRUNC { continue; }
            if op == GIR_GEP && ic_st[x] == IC_SROA && ic_ok(ic_root[x]) { continue; }
            if op == GIR_LOAD {
                let s, v, r = ic_get(I.a, F2);
                if s == IC_SROA && ic_ok(r) { continue; }
            }
            if op == GIR_STORE {
                let s, v, r = ic_get(I.b, F2);
                if s == IC_SROA && ic_ok(r) { continue; }
            }
            if op == GIR_CONDBR || op == GIR_SWITCH {
                let s, v, r = ic_get(I.a, F2);
                if s == IC_CONST { continue; }
            }
            cost += if op == GIR_CALL { 1 + INL_PENALTY } else { 1 };
            if cost > budget && !inl_trace { return false; }
        }
    }
    if inl_trace {
        let G = M.globals[o_f.global];
        let H = M.globals[F.global];
        write_stderr(str("inline? ", M.strtab[G.name..G.name + G.name_len], " <- ", M.strtab[H.name..H.name + H.name_len],
                         " cost ", cost, " budget ", budget, " size ", fn_size[c], if cost <= budget { " yes" } else { " no" }, "\n"));
    }
    return cost <= budget;
}
var inl_trace = false;
fn ic_mark(b: u32) {
    if b == NIL || b >= ic_live.len || ic_live[b] != 0 { return; }
    ic_live[b] = 1;
    ic_wl.push(b);
}

// Whether the function has a direct call of a function that may be inlined.
fn inl_any_call() -> bool {
    if o_pinned { return false; }
    for i in 0..o_ins.len {
        if o_blk[i] == NIL || o_ins[i].op != GIR_CALL || o_ins[i].flags & IF_NOINLINE_CALL != 0 { continue; }
        let c = callee_of(o_ins[i]);
        if c != NIL && c != o_fi && fn_done[c] != 0 && fn_inl[c] != 0 { return true; }
    }
    return false;
}

// A copy of sz bytes from src to dst before instruction at (byval
// arguments): the inline memcpy up to 4096 bytes, else a call of memcpy
// is not available here, so such callees are not inlined (inl_record).
fn inl_copy(at: u32, dst: u32, src: u32, sz: u32, al: u32, dbg: u32) {
    let x = new_inst(Inst { op: GIR_MEMCPY as! u8, sub: 0, flags: 0, ty: GIR_T_VOID as! u16, aux: 0, a: dst, b: src,
                            c: sz, dbg: dbg });
    link_before(at, x);
}

fn inline_call(c: u32, cfi: u32) {
    o_cfg_ok = false;
    let C = o_ins[c];
    let F2 = x_funcs[xb_f + cfi];
    let B = o_blk[c];
    let id0: u32 = o_ins.len as! u32;
    // arguments (a signext argument arrives as an i32: back to the parameter's type)
    amap.clear();
    for k in 0..F2.n_args {
        var v = res(o_ops[C.b + 2 * k]);
        let pt: u32 = x_opnds[xb_o + F2.args + 2 * k];
        let aw: u32 = x_opnds[xb_o + F2.args + 2 * k + 1];
        if aw & ABI_BYVAL != 0 {
            // byval: the callee works on a copy of its own (an alloca of the
            // caller, filled where the call was)
            let sz = abi_size(aw);
            let al = new_inst(Inst { op: GIR_ALLOCA as! u8, sub: 0, flags: 0, ty: GIR_T_PTR as! u16, aux: 0, a: sz,
                                     b: abi_align(aw), c: 0, dbg: 0 });
            link_start(0, al);
            inl_copy(c, al, v, sz, abi_align(aw), C.dbg);
            v = al;
        }
        let vt = otype(v);
        if vt != pt && cls_of(vt) == C_INT && cls_of(pt) == C_INT && bits_of(vt) > bits_of(pt) {
            let x = new_inst(Inst { op: GIR_TRUNC as! u8, sub: 0, flags: 0, ty: pt as! u16, aux: vt as! u16, a: v,
                                    b: 0, c: 0, dbg: C.dbg });
            link_before(c, x);
            v = x;
        }
        amap.push(v);
    }
    let nb0: u32 = b_first.len as! u32;
    let ib: u32 = o_ins.len as! u32;
    amap_on = true;
    oir_load(x_insts[xb_i..], x_blocks[xb_b..], F2, false);
    amap_on = false;
    let nbc = F2.n_blocks;
    // the code after the call moves to a new block
    let B2 = new_block();
    var i = o_nxt[c];
    while i != NIL {
        let nx = o_nxt[i];
        unlink(i);
        link_end(B2, i);
        i = nx;
    }
    sc_tmp.clear();
    succs_into(B2, sc_tmp);
    for s in sc_tmp { phi_rename_pred(s, B, B2); }
    // layout: B, the callee's blocks, B2
    b_lnext[B2] = b_lnext[B];
    b_lnext[B] = nb0;
    b_lnext[nb0 + nbc - 1] = B2;
    // the returns branch to B2
    inl_rets.clear();
    for b in nb0..nb0 + nbc {
        let t = b_last[b];
        if t == NIL || o_ins[t].op != GIR_RET { continue; }
        var v = o_ins[t].a;
        if C.ty != GIR_T_VOID && v != GIR_NONE {
            v = res(v);
            let vt = otype(v);
            if vt != C.ty && cls_of(vt) == C_INT && cls_of(C.ty) == C_INT {
                let x = new_inst(Inst { op: GIR_TRUNC as! u8, sub: 0, flags: 0, ty: C.ty, aux: vt as! u16, a: v,
                                        b: 0, c: 0, dbg: C.dbg });
                link_before(t, x);
                v = x;
            }
            inl_rets.push(v);
            inl_rets.push(b);
        }
        o_ins[t].op = GIR_BR as! u8;
        o_ins[t].a = B2;
        o_ins[t].b = 0;
        o_ins[t].c = 0;
    }
    // the callee's allocas go to the caller's entry block
    var a = b_first[nb0];
    while a != NIL {
        let nx = o_nxt[a];
        if o_ins[a].op == GIR_ALLOCA {
            unlink(a);
            link_start(0, a);
        }
        a = nx;
    }
    // the copied code has the call's source location
    for x in ib..o_ins.len { o_ins[x].dbg = C.dbg; }
    // the call becomes a branch to the callee's entry
    let br = new_inst(Inst { op: GIR_BR as! u8, sub: 0, flags: 0, ty: GIR_T_VOID, aux: 0, a: nb0, b: 0, c: 0, dbg: C.dbg });
    link_after(c, br);
    if C.ty == GIR_T_VOID {
        unlink(c);
    } else if inl_rets.len == 0 {
        replace(c, undef_of(C.ty));
    } else if inl_rets.len == 2 {
        replace(c, inl_rets[0]);
    } else {
        let n: u32 = (inl_rets.len / 2) as! u32;
        let s = new_run(2 * n);
        for k in 0..2 * n { o_ops[s + k] = inl_rets[k]; }
        let ph = new_inst(Inst { op: GIR_PHI as! u8, sub: 0, flags: 0, ty: C.ty, aux: 0, a: 0, b: s, c: n, dbg: 0 });
        link_start(B2, ph);
        replace(c, ph);
    }
    if id0 > 0 {}   // (the ids from id0 on are the copy)
}

// Tail recursion elimination (LLVM's TailCallElim): a call of the function
// itself right before a return (`return f(...)`, or `return x + f(...)` with
// the sum only returned: an accumulator) becomes a jump back to the start,
// where the arguments are PHIs; with an accumulator, a PHI sums the x's and
// every other return adds it. Functions with allocas (the frame would be
// reused while a pointer into it may be live), byval or variadic arguments
// are left alone.
var tre_call: u32[>..] = [];    // per site: the call
var tre_add: u32[>..] = [];     // per site: the accumulating add, or NIL
var tre_phi: u32[>..] = [];     // per argument: its PHI
let TRE_ARG: u32 = 0x40000000;  // GIR_V_ARG << 30
fn tre_self_call(c: u32) -> bool {
    if c == NIL || o_ins[c].op != GIR_CALL { return false; }
    let C = o_ins[c];
    return C.flags & (IF_INVOKE | IF_VARARG) == 0 && callee_of(C) == o_fi && C.c == o_f.n_args;
}
fn tail_recursion() -> bool {
    if o_pinned || o_f.flags & (FN_VARARG | FN_VASTART | FN_SJLJ | FN_RETURNS_TWICE) != 0 { return false; }
    for a in 0..o_f.n_args {
        if M.opnds[o_f.args + 2 * a + 1] & ABI_BYVAL != 0 { return false; }
    }
    resolve_all();
    tre_call.clear();
    tre_add.clear();
    var acc = false;
    var any_call = false;
    for b0 in 0..b_first.len {
        let b: u32 = b0 as! u32;
        if !live_block(b) { continue; }
        var i = b_first[b];
        while i != NIL {
            let op: u32 = o_ins[i].op;
            if op == GIR_ALLOCA || op == GIR_DYNALLOCA || op == GIR_STACKSAVE || op == GIR_LANDINGPAD { return false; }
            if op == GIR_CALL && callee_of(o_ins[i]) == o_fi { any_call = true; }
            i = o_nxt[i];
        }
    }
    if !any_call { return false; }
    tre_dup_rets();
    build_uses();
    let rt = o_f.ret_ty;
    for b0 in 0..b_first.len {
        let b: u32 = b0 as! u32;
        if !live_block(b) { continue; }
        let t = b_last[b];
        if t == NIL || o_ins[t].op != GIR_RET { continue; }
        let p = o_prv[t];
        if p == NIL { continue; }
        let v = if rt == GIR_T_VOID { GIR_NONE } else { res(o_ins[t].a) };
        if tre_self_call(p) && (rt == GIR_T_VOID || v == p && u_start[p + 1] - u_start[p] == 1) {
            tre_call.push(p);
            tre_add.push(NIL);
            continue;
        }
        // ret (add x, c) with c = f(...) right before and only used there
        if rt == GIR_T_VOID || v != p || o_ins[p].op != GIR_ADD || !int_ty(rt) || bits_of(rt) > 64 { continue; }
        if o_ins[p].ty != rt || u_start[p + 1] - u_start[p] != 1 { continue; }
        let c = o_prv[p];
        if !tre_self_call(c) || u_start[c + 1] - u_start[c] != 1 { continue; }
        let x = if res(o_ins[p].b) == c { res(o_ins[p].a) } else { res(o_ins[p].b) };
        if x == c || res(o_ins[p].a) != c && res(o_ins[p].b) != c { continue; }
        tre_call.push(c);
        tre_add.push(p);
        acc = true;
    }
    let ns: u32 = tre_call.len as! u32;
    if ns == 0 { return false; }
    // (with an accumulator, the other returns must return the type itself)
    if acc {
        for b0 in 0..b_first.len {
            let b: u32 = b0 as! u32;
            if !live_block(b) { continue; }
            let t = b_last[b];
            if t == NIL || o_ins[t].op != GIR_RET || tre_site(b) { continue; }
            if otype(res(o_ins[t].a)) != rt { return false; }
        }
    }
    // the entry block's instructions move to a new header H; block 0 jumps there
    let H = new_block();
    var i = b_first[0];
    while i != NIL {
        let nx = o_nxt[i];
        unlink(i);
        link_end(H, i);
        i = nx;
    }
    let dbg = o_ins[b_last[H]].dbg;
    let br0 = new_inst(Inst { op: GIR_BR as! u8, sub: 0, flags: 0, ty: GIR_T_VOID, aux: 0, a: H, b: 0, c: 0, dbg: dbg });
    link_end(0, br0);
    sc_tmp.clear();
    succs_into(H, sc_tmp);
    for s in sc_tmp { phi_rename_pred(s, 0, H); }
    b_lnext[H] = b_lnext[0];
    b_lnext[0] = H;
    // argument PHIs (entries: the argument from block 0, then one per site)
    tre_phi.clear();
    for a in 0..o_f.n_args {
        let r = new_run(2 * (1 + ns));
        o_ops[r] = TRE_ARG | a;
        o_ops[r + 1] = 0;
        let ph = new_inst(Inst { op: GIR_PHI as! u8, sub: 0, flags: 0, ty: M.opnds[o_f.args + 2 * a] as! u16, aux: 0,
                                 a: 0, b: r, c: 1 + ns, dbg: dbg });
        tre_phi.push(ph);
    }
    // uses of the arguments read the PHIs (the PHIs are not linked yet)
    for i0 in 0..o_ins.len {
        let u: u32 = i0 as! u32;
        if o_blk[u] == NIL { continue; }
        each_slot(u) { s =>
            let v = vget(u, s);
            if gir_kind(v) == GIR_V_ARG { vset(u, s, tre_phi[gir_idx(v)]); }
        };
    }
    for ph in tre_phi { link_start(H, ph); }
    var A: u32 = NIL;
    if acc {
        let r = new_run(2 * (1 + ns));
        o_ops[r] = int_const(rt, 0);
        o_ops[r + 1] = 0;
        A = new_inst(Inst { op: GIR_PHI as! u8, sub: 0, flags: 0, ty: rt as! u16, aux: 0, a: 0, b: r, c: 1 + ns, dbg: dbg });
        link_start(H, A);
    }
    // the sites jump to H
    for k in 0..ns {
        let c = tre_call[k];
        let b = o_blk[c];
        let t = b_last[b];
        for a in 0..o_f.n_args {
            let I = o_ins[tre_phi[a]];
            o_ops[I.b + 2 * (1 + k)] = res(o_ops[o_ins[c].b + 2 * a]);
            o_ops[I.b + 2 * (1 + k) + 1] = b;
        }
        if acc {
            var nv = A;
            if tre_add[k] != NIL {
                let p = tre_add[k];
                let x = if res(o_ins[p].b) == c { res(o_ins[p].a) } else { res(o_ins[p].b) };
                nv = ins_new(t, GIR_ADD, rt, A, x);
            }
            let I = o_ins[A];
            o_ops[I.b + 2 * (1 + k)] = nv;
            o_ops[I.b + 2 * (1 + k) + 1] = b;
        }
        // (the return, the add of the accumulator to it and the call go)
        let tdbg = o_ins[t].dbg;
        unlink(t);
        if tre_add[k] != NIL { unlink(tre_add[k]); }
        unlink(c);
        let br = new_inst(Inst { op: GIR_BR as! u8, sub: 0, flags: 0, ty: GIR_T_VOID, aux: 0, a: H, b: 0, c: 0, dbg: tdbg });
        link_end(b, br);
    }
    // the other returns add the accumulator
    if acc {
        for b0 in 0..b_first.len {
            let b: u32 = b0 as! u32;
            if !live_block(b) { continue; }
            let t = b_last[b];
            if t == NIL || o_ins[t].op != GIR_RET { continue; }
            let s = ins_new(t, GIR_ADD, rt, A, res(o_ins[t].a));
            o_ins[t].a = s;
        }
    }
    o_cfg_ok = false;
    return true;
}
// Returns of a PHI (`R: v = phi ...; ret v`, what `c ? x : f(y) + z` leaves):
// a predecessor that ends in `br R` right after the call (or the add) that
// computes its incoming value gets a return of its own, which the site scan
// then finds.
var tre_tmp: u32[>..] = [];
fn tre_dup_rets() {
    let rt = o_f.ret_ty;
    if rt == GIR_T_VOID { return; }
    for b0 in 0..b_first.len {
        let R: u32 = b0 as! u32;
        if !live_block(R) { continue; }
        let t = b_last[R];
        let f = b_first[R];
        if t == NIL || o_ins[t].op != GIR_RET || f == t || o_ins[f].op != GIR_PHI || o_nxt[f] != t { continue; }
        if res(o_ins[t].a) != f { continue; }
        tre_tmp.clear();
        for k in 0..o_ins[f].c {
            tre_tmp.push(o_ops[o_ins[f].b + 2 * k + 1]);
            tre_tmp.push(res(o_ops[o_ins[f].b + 2 * k]));
        }
        var k: i64 = 0;
        while k < tre_tmp.len {
            let p = tre_tmp[k];
            let w = tre_tmp[k + 1];
            k += 2;
            let pt = b_last[p];
            if pt == NIL || o_ins[pt].op != GIR_BR || p == R { continue; }
            let q = o_prv[pt];
            if q == NIL || q != w { continue; }
            var site = tre_self_call(q);
            if !site && o_ins[q].op == GIR_ADD {
                let c = o_prv[q];
                site = tre_self_call(c) && (res(o_ins[q].a) == c || res(o_ins[q].b) == c);
            }
            if !site { continue; }
            o_ins[pt].op = GIR_RET as! u8;
            o_ins[pt].a = w;
            o_ins[pt].b = 0;
            o_ins[pt].c = 0;
            phi_remove_pred(R, p);
            o_cfg_ok = false;
        }
    }
}
// Whether block b ends in one of the sites' returns.
fn tre_site(b: u32) -> bool {
    for c in tre_call { if o_blk[c] == b { return true; } }
    return false;
}
