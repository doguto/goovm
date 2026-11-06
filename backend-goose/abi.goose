// The SysV x86-64 calling convention, as LLVM's x86-64 C convention applies
// it to IR types (clang has already classified C types into these):
//   - INT (i1..i64, ptr): rdi rsi rdx rcx r8 r9, then an 8-byte stack slot;
//   - INT2 (i65..i128): two consecutive registers, or a 16-byte-aligned
//     16-byte stack slot if fewer than two are left;
//   - FP (f16, f32, f64): xmm0..xmm7, then an 8-byte stack slot;
//   - VEC: one xmm per 16 bytes (lane-1 vectors as their lane), else 16-byte
//     aligned stack slots;
//   - X87 (f80): a 16-byte-aligned 16-byte stack slot;
//   - byval: a copy of the pointee in the stack area, aligned to max(8, align).
// Returns: integer leaves in rax rdx rcx, FP leaves in xmm0 xmm1, vector
// leaves in xmm0..xmm3, f80 leaves in st0 st1 (the exporter rejects types
// that would not fit). Variadic calls set al to the number of xmm registers
// used.

let AL_GPR = 1;
let AL_GPR2 = 2;
let AL_XMM = 3;
let AL_STACK = 4;
let AL_BYVAL = 5;

// An argument's location: register(s) r0 (r1), xmm count n, or stack
// offset off and byte count n.
struct ArgLoc { kind: u32, r0: u32, r1: u32, n: u32, off: u32 }

let ARG_GPR: u32[6] = [RDI, RSI, RDX, RCX, R8, R9];

var cl_gp: u32 = 0;
var cl_fp: u32 = 0;
var cl_stack: u32 = 0;
var arg_locs: ArgLoc[>..] = [];

checkfree fn align_up32(x: u32, a: u32) -> u32 { (x + a - 1) & ~(a - 1) }

fn classify_reset() {
    cl_gp = 0;
    cl_fp = 0;
    cl_stack = 0;
}
fn stack_slot(size: u32, al: u32) -> ArgLoc {
    cl_stack = align_up32(cl_stack, al);
    let off = cl_stack;
    cl_stack += align_up32(size, 8);
    return ArgLoc { kind: AL_STACK, r0: 0, r1: 0, n: size, off: off };
}
// Location of the next argument, of type t with ABI word w.
fn classify(t: u32, w: u32) -> ArgLoc {
    if w & ABI_BYVAL != 0 {
        let size = abi_size(w);
        var al = abi_align(w);
        if al < 8 { al = 8; }
        var l = stack_slot(size, al);
        l.kind = AL_BYVAL;
        return l;
    }
    var tt = t;
    var c = cls_of(t);
    if c == C_VEC && M.types[t].n == 1 {
        tt = M.types[t].elems;
        c = cls_of(tt);
    }
    if c == C_INT {
        if cl_gp < 6 {
            let r = ARG_GPR[cl_gp];
            cl_gp++;
            return ArgLoc { kind: AL_GPR, r0: r, r1: 0, n: 1, off: 0 };
        }
        return stack_slot(8, 8);
    }
    if c == C_INT2 {
        if cl_gp + 2 <= 6 {
            let r0 = ARG_GPR[cl_gp];
            let r1 = ARG_GPR[(cl_gp + 1) % 6];
            cl_gp += 2;
            return ArgLoc { kind: AL_GPR2, r0: r0, r1: r1, n: 2, off: 0 };
        }
        return stack_slot(16, 16);
    }
    if c == C_FP {
        if cl_fp < 8 {
            let x = cl_fp;
            cl_fp++;
            return ArgLoc { kind: AL_XMM, r0: x, r1: 0, n: 1, off: 0 };
        }
        return stack_slot(8, 8);
    }
    if c == C_X87 { return stack_slot(16, 16); }
    // VEC
    let st = M.types[t].store;
    let k: u32 = if st <= 16 { 1 } else { (st + 15) / 16 };
    if cl_fp + k <= 8 {
        let x = cl_fp;
        cl_fp += k;
        return ArgLoc { kind: AL_XMM, r0: x, r1: 0, n: k, off: 0 };
    }
    return stack_slot(16 * k, 16);
}

// Moves between xmm registers and memory for `n` bytes of FP/vector data.
checkfree fn xmm_load_n(x: u32, m: Mem, n: u32) {
    if n <= 4 { movd_load(x, m); }
    else if n <= 8 { movq_load(x, m); }
    else { movups_load(x, m); }
}
checkfree fn xmm_store_n(m: Mem, x: u32, n: u32) {
    if n == 2 {
        movd_rx(RAX, x);
        store16(m, RAX);
    } else if n <= 4 { movd_store(m, x); }
    else if n <= 8 { movq_store(m, x); }
    else { movups_store(m, x); }
}
// Bytes of a value of type t that are meaningful in its slot.
fn val_bytes(t: u32) -> u32 {
    let c = cls_of(t);
    if c == C_INT { return 8; }
    if c == C_X87 { return 10; }
    if c == C_INT2 { return 16; }
    return M.types[t].store;
}

// --------------------------------------------------------------- returns

let RP_GPR = 1;
let RP_XMM = 2;
let RP_X87 = 3;
struct RetPart { kind: u32, reg: u32, off: u32, size: u32, t: u32 }
var ret_parts: RetPart[>..] = [];
var rp_gp: u32 = 0;
var rp_fp: u32 = 0;
var rp_x87: u32 = 0;
let RET_GPR: u32[3] = [RAX, RDX, RCX];

recursive fn ret_leaves(t: u32, off: u32) {
    let d = M.types[t];
    let c: u32 = d.cls;
    if c == C_INT {
        ret_parts.push(RetPart { kind: RP_GPR, reg: RET_GPR[rp_gp % 3], off: off, size: d.store, t: t });
        rp_gp++;
    } else if c == C_INT2 {
        ret_parts.push(RetPart { kind: RP_GPR, reg: RET_GPR[rp_gp % 3], off: off, size: 8, t: GIR_T_I64 });
        ret_parts.push(RetPart { kind: RP_GPR, reg: RET_GPR[(rp_gp + 1) % 3], off: off + 8, size: d.store - 8,
                                 t: GIR_T_I64 });
        rp_gp += 2;
    } else if c == C_FP {
        ret_parts.push(RetPart { kind: RP_XMM, reg: rp_fp, off: off, size: d.store, t: t });
        rp_fp++;
    } else if c == C_X87 {
        ret_parts.push(RetPart { kind: RP_X87, reg: rp_x87, off: off, size: 10, t: t });
        rp_x87++;
    } else if c == C_VEC {
        if d.n == 1 {
            ret_leaves(d.elems, off);
        } else {
            var p: u32 = 0;
            while p < d.store {
                let n: u32 = if d.store - p >= 16 { 16 } else { d.store - p };
                ret_parts.push(RetPart { kind: RP_XMM, reg: rp_fp, off: off + p, size: n, t: t });
                rp_fp++;
                p += 16;
            }
        }
    } else if d.kind == TK_STRUCT {
        for i in 0..d.n {
            let ft = M.opnds[d.elems + 2 * i];
            let fo = M.opnds[d.elems + 2 * i + 1];
            ret_leaves(ft, off + fo);
        }
    } else if d.kind == TK_ARRAY {
        let es = M.types[d.elems].size;
        for i in 0..d.n { ret_leaves(d.elems, off + i * es); }
    }
}
// Fills ret_parts for a VEC or MEM return type.
fn classify_ret(t: u32) {
    ret_parts.clear();
    rp_gp = 0;
    rp_fp = 0;
    rp_x87 = 0;
    ret_leaves(t, 0);
}

// Loads the return value v of type t into the return registers.
fn ret_value(v: u32, t: u32) {
    let c = cls_of(t);
    if c == C_INT { use_fixed(v, RAX); return; }
    if c == C_INT2 { use_gpr2(v, RAX, RDX); return; }
    if c == C_FP { use_xmm(v, XMM0); return; }
    if c == C_X87 { fld_m(10, val_mem(v)); return; }
    classify_ret(t);
    let m = val_mem(v);
    // x87 parts: the first leaf ends up in st0, so push the last one first.
    var k: i64 = ret_parts.len - 1;
    while k >= 0 {
        let p = ret_parts[k];
        if p.kind == RP_X87 { fld_m(10, m_add(m, p.off)); }
        k--;
    }
    for p in ret_parts {
        if p.kind == RP_GPR { load_n(p.reg, m_add(m, p.off), p.size); }
        else if p.kind == RP_XMM { xmm_load_n(p.reg, m_add(m, p.off), p.size); }
    }
}
// Stores the return registers of a call returning type t into the result
// of local instruction j.
fn ret_result(j: u32, t: u32) {
    let c = cls_of(t);
    if c == C_INT {
        zext_reg(RAX, bits_of(t));
        put_gpr(j, RAX);
        return;
    }
    if c == C_INT2 {
        if bits_of(t) < 128 { zext_reg(RDX, bits_of(t) - 64); }
        put_gpr2(j, RAX, RDX);
        return;
    }
    if c == C_FP {
        put_xmm(j, XMM0, t);
        return;
    }
    let m = res_mem(j);
    if c == C_X87 {
        fstp_m(10, m);
        return;
    }
    classify_ret(t);
    for p in ret_parts {
        if p.kind == RP_GPR { store_n(m_add(m, p.off), p.reg, p.size); }
        else if p.kind == RP_XMM { xmm_store_n(m_add(m, p.off), p.reg, p.size); }
    }
    for p in ret_parts {
        if p.kind == RP_X87 { fstp_m(10, m_add(m, p.off)); }
    }
}

// ----------------------------------------------------------------- calls

// Emits the call instruction itself (the callee is in R11 if indirect).
fn emit_call_insn(callee: u32, direct: bool) {
    if direct {
        b1(0xE8);  // call rel32
        rela(here(), g_sym[gir_idx(callee)], R_X86_64_PLT32, -4);
        b4(0);
    } else {
        call_r(R11);
    }
}

// Register moves into argument registers (a parallel copy).
var mv_src: u32[>..] = [];
var mv_dst: u32[>..] = [];

// Register of value v if it is in one (locked), else materializes v into t.
fn gpr_or(v: u32, t: u32) -> u32 {
    if is_val(v) {
        let id = vid(v);
        let r: u32 = vi[id].reg;
        if r < 16 {
            r_lock |= bit(r);
            ra_note(id);
            if vi[id].st & ST_EXT != 0 {
                mov_rr64(t, r);
                zext_reg(t, bits_of(vtype(id)));
                return t;
            }
            return r;
        }
        ra_note(id);
    }
    ra_mat_gpr(v, t);
    return t;
}

// Before a call: values in caller-saved registers that live on move to a
// free callee-saved register, or are written to their home (their register
// stays a source for the argument moves).
fn ra_save_caller() {
    var m = ~r_free & r_alloc & (GP_CALLER | XMM_ALL);
    while m != 0 {
        let r = ctz32(m);
        m &= m - 1;
        let id = r_val[r];
        if id >= RV_TEMP || !ra_live_after(id) { continue; }
        let cs = r_free & r_alloc & GP_CALLEE & ~r_lock;
        if r < 16 && cs != 0 && vi[id].st & ST_GLOB == 0 {
            let to = ctz32(cs);
            mov_rr64(to, r);
            r_free &= ~bit(to);
            r_cs_used |= bit(to);
            r_val[to] = id;
            vi[id].reg = to as! u8;
            ra_release(r);
            continue;
        }
        if vi[id].st & ST_MEM == 0 { ra_store_home(id, r); }
    }
}
// After a call: the caller-saved registers hold nothing.
fn ra_after_call() {
    let mask = GP_CALLER | XMM_ALL;
    var m = ~r_free & r_alloc & mask;
    while m != 0 {
        let r = ctz32(m);
        m &= m - 1;
        let id = r_val[r];
        if id < RV_TEMP { vi[id].reg = NOREG; }
        r_val[r] = RV_NONE;
    }
    r_free |= r_alloc & mask;
    r_temp &= ~mask;
    r_lock &= ~mask;
}
// Emits the moves mv_src[k] -> mv_dst[k] (registers 0..31, a parallel copy).
fn emit_moves() {
    var n = mv_src.len;
    var k: i64 = 0;
    while k < n {
        if mv_src[k] == mv_dst[k] {
            mv_src[k] = mv_src[n - 1];
            mv_dst[k] = mv_dst[n - 1];
            n--;
        } else {
            k++;
        }
    }
    while n > 0 {
        var done = false;
        var i: i64 = 0;
        while i < n {
            let d = mv_dst[i];
            var busy = false;
            for q in 0..n { if q != i && mv_src[q] == d { busy = true; } }
            if !busy {
                let s = mv_src[i];
                if d >= 16 { movaps_rr(d - 16, s - 16); } else { mov_rr64(d, s); }
                mv_src[i] = mv_src[n - 1];
                mv_dst[i] = mv_dst[n - 1];
                n--;
                done = true;
                break;
            }
            i++;
        }
        if done { continue; }
        // a cycle: swap the first move's registers
        let d = mv_dst[0];
        let s = mv_src[0];
        if d >= 16 {
            xorps_rr(d - 16, s - 16);
            xorps_rr(s - 16, d - 16);
            xorps_rr(d - 16, s - 16);
        } else {
            xchg_rr(d, s);
        }
        mv_src[0] = mv_src[n - 1];
        mv_dst[0] = mv_dst[n - 1];
        n--;
        for q in 0..n {
            if mv_src[q] == d { mv_src[q] = s; }
            else if mv_src[q] == s { mv_src[q] = d; }
        }
    }
    mv_src.clear();
    mv_dst.clear();
}

fn lower_call(I: Inst, j: u32) {
    let n = I.c;
    let s = I.b;
    let callee = I.a;
    let direct = gir_kind(callee) == GIR_V_GLOBAL && M.globals[gir_idx(callee)].kind == G_FUNC;
    if lower_call_fast(I, j, direct) { return; }
    classify_reset();
    arg_locs.clear();
    for k in 0..n {
        let v = M.opnds[s + 2 * k];
        let w = M.opnds[s + 2 * k + 1];
        arg_locs.push(classify(type_of(v), w));
    }
    let sbytes = align_up32(cl_stack, 16);
    if sbytes != 0 { grp1_ri64(G1_SUB, RSP, sbytes as! i32); }
    // Stack arguments and byval copies first: they need scratch registers.
    if cl_stack != 0 {
        let t = ra_temp();
        for l, k in arg_locs {
            let v = M.opnds[s + 2 * k as! u32];
            if l.kind == AL_STACK {
                let tt = type_of(v);
                let dst = m_rsp(l.off as! i32);
                let c = rc_of(tt);
                if c == RC_GPR {
                    if is_const(v) && cls_of(M.consts[gir_idx(v)].ty) == C_INT && store_const(dst, M.consts[gir_idx(v)].lo, 8) {
                        continue;
                    }
                    store64(dst, gpr_or(v, t));
                } else if in_xmm(c) {
                    if c == RC_XMM && is_const(v) && store_const(dst, M.consts[gir_idx(v)].lo, store_of(tt)) { continue; }
                    xmm_store_t(dst, ra_xmm(v), tt);
                } else {
                    let vb = val_bytes(tt);
                    let cb: u32 = if is_const(v) && store_of(tt) < vb { store_of(tt) } else { vb };
                    copy_mem_t(dst, val_mem(v), cb, gran_of(tt), t);
                }
            } else if l.kind == AL_BYVAL {
                if l.n > 64 {
                    ra_gpr_into(v, RSI, false);
                    ra_clobber(RDI);
                    ra_clobber(RCX);
                    lea64(RDI, m_rsp(l.off as! i32));
                    mov_ri(RCX, l.n);
                    rep_movsb();
                } else {
                    let src = ra_addr(v);
                    copy_mem_t(m_rsp(l.off as! i32), src, l.n, 8, t);
                }
            }
        }
    }
    ra_save_caller();
    // Register arguments: values in registers by parallel moves, the rest
    // loaded straight into their argument register.
    if !direct {
        if is_val(callee) && vi[vid(callee)].reg < 16 {
            mv_src.push(vi[vid(callee)].reg);
            mv_dst.push(R11);
            ra_note(vid(callee));
        }
    }
    for l, k in arg_locs {
        let v = M.opnds[s + 2 * k as! u32];
        if !is_val(v) { continue; }
        let id = vid(v);
        let r: u32 = vi[id].reg;
        if r >= 32 { continue; }
        if l.kind == AL_GPR && r < 16 {
            mv_src.push(r);
            mv_dst.push(l.r0);
            ra_note(id);
        } else if l.kind == AL_XMM && r >= 16 && in_xmm(rc_of(type_of(v))) {
            mv_src.push(r);
            mv_dst.push(16 + l.r0);
            ra_note(id);
        }
    }
    emit_moves();
    var nfp: u32 = 0;
    for l, k in arg_locs {
        let v = M.opnds[s + 2 * k as! u32];
        let t = type_of(v);
        if l.kind == AL_GPR {
            if is_val(v) && vi[vid(v)].reg < 16 {
                // moved; zero-extend narrow values that carry garbage (zeroext arguments)
                let id = vid(v);
                if vi[id].st & ST_EXT != 0 && bits_of(t) < 32 { zext_reg(l.r0, bits_of(t)); }
                continue;
            }
            if rc_of(t) == RC_GPR { ra_mat_gpr(v, l.r0); }
            else {
                // a one-lane vector or another small value passed in a GPR
                load_n(l.r0, val_mem(v), store_of(t));
            }
        } else if l.kind == AL_GPR2 {
            use_gpr2(v, l.r0, l.r1);
        } else if l.kind == AL_XMM {
            nfp = l.r0 + l.n;
            if in_xmm(rc_of(t)) {
                if is_val(v) && vi[vid(v)].reg >= 16 && vi[vid(v)].reg < 32 { continue; }
                ra_mat_xmm(v, l.r0);
            } else if cls_of(t) == C_FP {
                // f16: its 16-bit pattern
                xmm_load_n(l.r0, val_mem(v), 2);
            } else if M.types[t].n == 1 && cls_of(M.types[t].elems) == C_FP {
                xmm_load_n(l.r0, val_mem(v), M.types[t].store);
            } else {
                let m = val_mem(v);
                let st = M.types[t].store;
                var p: u32 = 0;
                var x = l.r0;
                while p < st {
                    xmm_load_n(x, m_add(m, p), if st - p >= 16 { 16 } else { st - p });
                    p += 16;
                    x++;
                }
            }
        }
    }
    if !direct && !(is_val(callee) && vi[vid(callee)].reg < 16) { ra_mat_gpr(callee, R11); }
    if I.flags & IF_VARARG != 0 { mov_ri(RAX, cl_fp); }  // al = number of vector registers used
    emit_call_insn(callee, direct);
    ra_after_call();
    if sbytes != 0 { grp1_ri64(G1_ADD, RSP, sbytes as! i32); }
    call_result(j, I.ty);
}
// The result of the call j (in the return registers).
fn call_result(j: u32, t: u32) {
    if t == GIR_T_VOID { return; }
    let c = rc_of(t);
    if c == RC_GPR {
        let bits = bits_of(t);
        if exact_width(bits) { ra_set(j, RAX, bits < 64); }
        else {
            zext_reg(RAX, bits);
            ra_set(j, RAX, false);
        }
        return;
    }
    if in_xmm(c) {
        ra_set(j, 16 + XMM0, false);
        return;
    }
    ret_result(j, t);
}

// Calls whose arguments are all plain INT, f32 or f64 values in registers
// (most calls): no classification, no stack area. False if not applicable.
var fa_tgt: u32[16] = [0; 16];
fn lower_call_fast(I: Inst, j: u32, direct: bool) -> bool {
    let n = I.c;
    if n > 14 { return false; }
    let s = I.b;
    let callee = I.a;
    var gp: u32 = 0;
    var fp: u32 = 0;
    for k in 0..n {
        if M.opnds[s + 2 * k + 1] != 0 { return false; }
        let c = rc_of(type_of(M.opnds[s + 2 * k]));
        if c == RC_GPR {
            if gp == 6 { return false; }
            fa_tgt[k] = ARG_GPR[gp];
            gp++;
        } else if in_xmm(c) {
            if fp == 8 { return false; }
            fa_tgt[k] = 16 + fp;
            fp++;
        } else {
            return false;
        }
    }
    ra_save_caller();
    var creg = false;
    if !direct && is_val(callee) {
        let id = vid(callee);
        let r: u32 = vi[id].reg;
        if r < 16 {
            mv_src.push(r);
            mv_dst.push(R11);
            ra_note(id);
            creg = true;
        }
    }
    for k in 0..n {
        let v = M.opnds[s + 2 * k];
        if !is_val(v) { continue; }
        let id = vid(v);
        let r: u32 = vi[id].reg;
        if r < 32 {
            mv_src.push(r);
            mv_dst.push(fa_tgt[k]);
            ra_note(id);
        }
    }
    if mv_src.len != 0 { emit_moves(); }
    for k in 0..n {
        let v = M.opnds[s + 2 * k];
        let tg = fa_tgt[k];
        if is_val(v) {
            let id = vid(v);
            if vi[id].reg < 32 {
                if tg < 16 && vi[id].st & ST_EXT != 0 {
                    let b = bits_of(vtype(id));
                    if b < 32 { zext_reg(tg, b); }
                }
                continue;
            }
        }
        if tg < 16 { ra_mat_gpr(v, tg); } else { ra_mat_xmm(v, tg - 16); }
    }
    if !direct && !creg { ra_mat_gpr(callee, R11); }
    if I.flags & IF_VARARG != 0 { mov_ri(RAX, fp); }  // al = number of vector registers used
    emit_call_insn(callee, direct);
    ra_after_call();
    call_result(j, I.ty);
    return true;
}

// ------------------------------------------------------------ prologue

// Per argument with prologue work: (argument number, location).
struct ProArg { a: u32, off: i32 }
var pro_args: ProArg[>..] = [];

// Argument homes and registers at function entry (before the body is
// generated); pro_args lists the arguments the prologue must store.
fn setup_args() {
    classify_reset();
    pro_args.clear();
    for a in 0..f_nargs {
        let t = M.opnds[f_args + 2 * a];
        let w = M.opnds[f_args + 2 * a + 1];
        let l = classify(t, w);
        let id = f_nins + a;
        if vi[id].nuse == 0 { continue; }   // never used
        let c = rc_of(t);
        if l.kind == AL_BYVAL {
            vi[id].home = H_BYVAL;
            vi[id].off = (16 + l.off) as! i32;
            vi[id].st |= ST_MEM;
        } else if l.kind == AL_STACK {
            vi[id].home = H_STACK;
            vi[id].off = (16 + l.off) as! i32;
            vi[id].st |= ST_MEM;
            if cls_of(t) == C_INT2 && bits_of(t) < 128 {
                // normalized into a slot of its own
                vi[id].home = H_SLOT;
                vi[id].off = new_slot(16);
                pro_args.push(ProArg { a: a, off: vi[id].off });
            }
        } else if l.kind == AL_GPR && c == RC_GPR || l.kind == AL_XMM && in_xmm(c) {
            // register-resident
            let r: u32 = if l.kind == AL_GPR { l.r0 } else { 16 + l.r0 };
            vi[id].reg = r as! u8;
            var st = vi[id].st;
            if c == RC_GPR && exact_width(bits_of(t)) && bits_of(t) < 64 { st |= ST_EXT; }
            vi[id].st = st;
            let pa = st & ST_GLOB != 0 || c == RC_GPR && !exact_width(bits_of(t));
            if st & ST_GLOB != 0 {
                ra_home_off(id);
                vi[id].st |= ST_MEM;
            }
            if pa { pro_args.push(ProArg { a: a, off: vi[id].off }); }
        } else {
            // INT2, vectors, f16 in registers: stored to a home
            ra_home_off(id);
            vi[id].st |= ST_MEM;
            vi[id].reg = NOREG;
            pro_args.push(ProArg { a: a, off: vi[id].off });
        }
    }
    va_gp = cl_gp;
    va_fp = cl_fp;
    va_stack = cl_stack;
}
// The entry block starts with the register-resident arguments in their registers.
fn ra_entry_state() {
    ra_block_start();
    for a in 0..f_nargs {
        let id = f_nins + a;
        if vi[id].nuse == 0 { continue; }
        let r: u32 = vi[id].reg;
        if r < 32 {
            r_val[r] = id;
            r_free &= ~bit(r);
        }
    }
}
// Prologue code for the arguments in pro_args (normalization, homes).
fn prologue_args() {
    classify_reset();
    var q: i64 = 0;
    for a in 0..f_nargs {
        let t = M.opnds[f_args + 2 * a];
        let w = M.opnds[f_args + 2 * a + 1];
        let l = classify(t, w);
        if q >= pro_args.len || pro_args[q].a != a { continue; }
        let ho = pro_args[q].off;
        q++;
        let id = f_nins + a;
        let c = cls_of(t);
        if l.kind == AL_STACK {
            // INT2 narrower than 128 bits
            let src = m_rbp((16 + l.off) as! i32);
            let home = m_rbp(ho);
            copy_mem_t(home, src, 16, 8, RAX);
            load64(RAX, m_add(home, 8));
            zext_reg(RAX, bits_of(t) - 64);
            store64(m_add(home, 8), RAX);
        } else if l.kind == AL_GPR && rc_of(t) == RC_GPR {
            if !exact_width(bits_of(t)) { zext_reg(l.r0, bits_of(t)); }
            if vi[id].st & ST_GLOB != 0 { store_int(m_rbp(ho), l.r0, bits_of(t)); }
        } else if l.kind == AL_XMM && in_xmm(rc_of(t)) {
            xmm_store_t(m_rbp(ho), l.r0, t);
        } else if l.kind == AL_GPR {
            store64(m_rbp(ho), l.r0);
        } else if l.kind == AL_GPR2 {
            let home = m_rbp(ho);
            if bits_of(t) < 128 { zext_reg(l.r1, bits_of(t) - 64); }
            store64(home, l.r0);
            store64(m_add(home, 8), l.r1);
        } else if l.kind == AL_XMM {
            let home = m_rbp(ho);
            let st = M.types[t].store;
            if c == C_FP { xmm_store_n(home, l.r0, st); }
            else {
                var p: u32 = 0;
                var x = l.r0;
                while p < st {
                    xmm_store_n(m_add(home, p), x, if st - p >= 16 { 16 } else { st - p });
                    p += 16;
                    x++;
                }
            }
        }
    }
}

// Register save area of a variadic function: rdi..r9 at +0..+40, xmm0..7 at
// +48..+160 (only if al != 0).
fn save_va_regs() {
    for i in 6 { store64(m_rbp(rsa_off + 8 * i as! i32), ARG_GPR[i]); }
    test_rr32(RAX, RAX);  // al only matters; test eax, eax is equivalent for al = 0..8 callers
    let p = jcc_fwd(CC_E);
    for i: u32 in 0..8 { movups_store(m_rbp(rsa_off + 48 + 16 * i as! i32), i); }
    patch_here(p);
}

fn lower_vastart(I: Inst) {
    let p = addr_of(I.a, RDX);
    store_imm32(p, 8 * va_gp);
    store_imm32(m_add(p, 4), 48 + 16 * va_fp);
    lea64(RAX, m_rbp((16 + va_stack) as! i32));
    store64(m_add(p, 8), RAX);
    lea64(RAX, m_rbp(rsa_off));
    store64(m_add(p, 16), RAX);
}
