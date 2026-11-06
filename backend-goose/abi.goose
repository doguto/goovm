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

fn lower_call(I: Inst, j: u32) {
    let n = I.c;
    let s = I.b;
    let args = M.opnds[s..s + 2 * n];
    let callee = I.a;
    let direct = gir_kind(callee) == GIR_V_GLOBAL && M.globals[gir_idx(callee)].kind == G_FUNC;
    // Fast path (most calls): every argument is a plain INT or FP value
    // that gets a register, so there is no stack area to build.
    var ngp: u32 = 0;
    var nfp: u32 = 0;
    var isfp: bool[14] = [false; 14];
    var k: i64 = 0;
    while k < args.len && k < 28 {
        let t = type_of(args[k]);
        let c = cls_of(t);
        if args[k + 1] != 0 || (c != C_INT && c != C_FP) { break; }
        if c == C_INT { ngp++; } else { nfp++; }
        isfp[(k >> 1) % 14] = c == C_FP;
        k += 2;
    }
    if k == args.len && ngp <= 6 && nfp <= 8 {
        if !direct { use_fixed(callee, R11); }
        var gp: u32 = 0;
        var fp: u32 = 0;
        k = 0;
        while k < args.len {
            let v = args[k];
            if !isfp[(k >> 1) % 14] {
                use_fixed(v, ARG_GPR[gp % 6]);
                gp++;
            } else {
                use_xmm(v, fp);
                fp++;
            }
            k += 2;
        }
        if I.flags & IF_VARARG != 0 { mov_ri(RAX, fp); }  // al = number of vector registers used
        emit_call_insn(callee, direct);
        if I.ty != GIR_T_VOID { ret_result(j, I.ty); }
        return;
    }
    classify_reset();
    arg_locs.clear();
    for k in 0..n {
        let v = M.opnds[s + 2 * k];
        let w = M.opnds[s + 2 * k + 1];
        arg_locs.push(classify(type_of(v), w));
    }
    let sbytes = align_up32(cl_stack, 16);
    if sbytes != 0 { grp1_ri64(G1_SUB, RSP, sbytes as! i32); }
    // Stack arguments and byval copies first: they use RAX, RSI, RDI, RCX.
    for l, k in arg_locs {
        let v = M.opnds[s + 2 * k as! u32];
        if l.kind == AL_STACK {
            let t = type_of(v);
            let dst = m_rsp(l.off as! i32);
            if cls_of(t) == C_INT {
                use_gpr(v, RAX);
                store64(dst, RAX);
            } else {
                copy_val(dst, v, val_bytes(t));
            }
        } else if l.kind == AL_BYVAL {
            use_gpr(v, RSI);
            copy_mem(m_rsp(l.off as! i32), m_reg(RSI, 0), l.n);
        }
    }
    if !direct { use_fixed(callee, R11); }
    for l, k in arg_locs {
        let v = M.opnds[s + 2 * k as! u32];
        if l.kind == AL_GPR { use_fixed(v, l.r0); }
        else if l.kind == AL_GPR2 { use_gpr2(v, l.r0, l.r1); }
        else if l.kind == AL_XMM {
            let t = type_of(v);
            if cls_of(t) == C_FP { use_xmm(v, l.r0); }
            else if M.types[t].n == 1 && cls_of(M.types[t].elems) == C_FP {
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
    if I.flags & IF_VARARG != 0 { mov_ri(RAX, cl_fp); }  // al = number of vector registers used
    emit_call_insn(callee, direct);
    if sbytes != 0 { grp1_ri64(G1_ADD, RSP, sbytes as! i32); }
    if I.ty != GIR_T_VOID { ret_result(j, I.ty); }
}

// ------------------------------------------------------------ prologue

// Stores the incoming arguments into their homes (after the frame is set up).
fn spill_args() {
    classify_reset();
    for a in 0..f_nargs {
        let t = M.opnds[f_args + 2 * a];
        let w = M.opnds[f_args + 2 * a + 1];
        let l = classify(t, w);
        let home = m_rbp(a_off[a]);
        let c = cls_of(t);
        if l.kind == AL_BYVAL {
            a_home[a] = A_BYVAL;
            a_off[a] = (16 + l.off) as! i32;
        } else if l.kind == AL_GPR {
            if c == C_VEC {
                store64(home, l.r0);
            } else {
                zext_reg(l.r0, bits_of(t));
                store64(home, l.r0);
            }
        } else if l.kind == AL_GPR2 {
            if bits_of(t) < 128 { zext_reg(l.r1, bits_of(t) - 64); }
            store64(home, l.r0);
            store64(m_add(home, 8), l.r1);
        } else if l.kind == AL_XMM {
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
        } else {
            let src = m_rbp((16 + l.off) as! i32);
            if c == C_INT {
                load_n(RAX, src, M.types[t].store);
                zext_reg(RAX, bits_of(t));
                store64(home, RAX);
            } else {
                copy_mem(home, src, val_bytes(t));
                if c == C_INT2 && bits_of(t) < 128 {
                    load64(RAX, m_add(home, 8));
                    zext_reg(RAX, bits_of(t) - 64);
                    store64(m_add(home, 8), RAX);
                }
            }
        }
    }
    va_gp = cl_gp;
    va_fp = cl_fp;
    va_stack = cl_stack;
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
