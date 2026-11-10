// AAPCS64 (milestone F1), as LLVM's CC_AArch64_AAPCS applies it to IR types
// (clang has already classified C types into these; gir.h):
//   - INT (i1..i64, ptr): x0..x7, then an 8-byte stack slot;
//   - FP (f16, f32, f64) and vectors of 8 bytes: v0..v7, then an 8-byte slot;
//     f128 and 16-byte vectors: v0..v7, then a 16-byte-aligned 16-byte slot;
//   - INT2 (i65..i128): an even-numbered register pair (x1 is skipped for an
//     i128 after an int), else a 16-byte-aligned 16-byte slot, and no
//     further GPR argument goes in a register;
//   - an array whose members are all of one type (HFA [n x float], HVA,
//     [n x i64]) is a block: consecutive registers of its class if they are
//     all free, else the whole class is used up and the members go to the
//     stack, the first at an alignment of max(8, min(align, 16)), the others
//     packed after it;
//   - other aggregates (struct arguments; clang never passes them, other IR
//     producers may) member by member;
//   - the GIR_ABI_SRET argument in x8; byval copies in the stack area
//     (aligned to max(8, align)).
// Variadic arguments are passed like the others (Linux). Returns: the
// members in x0..x7 and v0..v7, in order.

let AP_X = 1;
let AP_V = 2;
let AP_STK = 3;
let AP_BYVAL = 4;   // the pointee is copied to the stack at soff (size bytes)
// Part of an argument: `size` bytes at `off` of the value, in x/v register
// `reg` (0..7, 8 for sret) or at stack offset `soff`; t: the part's type.
// A vector part whose register form differs from its memory form (LLVM's
// type legalization of vectors that are not 8 or 16 bytes of i8..i64 /
// f32 / f64 lanes: lanes promoted to a wider integer, or added): nl lanes of
// lm bytes in memory, lanes of lr bytes in the register; a plain part has
// nl = 1, lm = lr = size.
struct APart { kind: u32, reg: u32, off: u32, size: u32, soff: u32, t: u32, nl: u32, lm: u32, lr: u32 }
var a_parts: APart[>..] = [];
var a_pfirst: u32[>..] = [];     // per argument: its first part (one more entry at the end)
var a_ngrn: u32 = 0;
var a_nsrn: u32 = 0;
var a_nstk: u32 = 0;
// leaves of the argument being classified
struct ALeaf { fp: bool, off: u32, size: u32, t: u32, nl: u32, lm: u32, lr: u32 }
var a_leaf: ALeaf[>..] = [];

recursive fn a_leaves(t: u32, off: u32) {
    let d = M.types[t];
    let c: u32 = d.cls;
    if c == C_INT {
        let n: u32 = if d.store <= 8 { d.store } else { 8 };
        a_leaf.push(ALeaf { fp: false, off: off, size: n, t: t, nl: 1, lm: n, lr: n });
    } else if c == C_INT2 {
        a_leaf.push(ALeaf { fp: false, off: off, size: 8, t: GIR_T_I64, nl: 1, lm: 8, lr: 8 });
        a_leaf.push(ALeaf { fp: false, off: off + 8, size: 8, t: GIR_T_I64, nl: 1, lm: 8, lr: 8 });
    } else if c == C_FP {
        a_leaf.push(ALeaf { fp: true, off: off, size: d.store, t: t, nl: 1, lm: d.store, lr: d.store });
    } else if c == C_VEC {
        a_vec_leaves(t, off);
    } else if d.kind == TK_STRUCT {
        for i in 0..d.n {
            a_leaves(M.opnds[d.elems + 2 * i], off + M.opnds[d.elems + 2 * i + 1]);
        }
    } else if d.kind == TK_ARRAY {
        let es = M.types[d.elems].size;
        for i in 0..d.n { a_leaves(d.elems, off + i * es); }
    }
}
// The registers of a vector value, as LLVM's type legalization makes them
// (AArch64: v1i8..v1f32 are widened, other power-of-two vectors narrower
// than 64 bits get wider integer lanes, other lane counts are widened to a
// power of two, vectors wider than 128 bits are split in 128-bit pieces).
fn a_vec_leaves(t: u32, off: u32) {
    let d = M.types[t];
    let L = M.types[d.elems];
    let n = d.n;
    let lb: u32 = L.size;
    let fp = L.cls == C_FP;
    if (d.store == 8 || d.store == 16) && lb * n == d.store {
        a_leaf.push(ALeaf { fp: true, off: off, size: d.store, t: t, nl: 1, lm: d.store, lr: d.store });
        return;
    }
    if n == 1 {
        let sz: u32 = if lb > 8 { 16 } else { 8 };
        a_leaf.push(ALeaf { fp: true, off: off, size: sz, t: t, nl: 1, lm: lb, lr: lb });
        return;
    }
    var n2: u32 = 1;
    while n2 < n { n2 = n2 * 2; }
    var lr = lb;
    if !fp { while n2 * lr < 8 { lr = lr * 2; } }
    var total = n2 * lr;
    if total < 8 { total = 8; }
    if total <= 16 {
        a_leaf.push(ALeaf { fp: true, off: off, size: total, t: t, nl: n, lm: lb, lr: lr });
        return;
    }
    // 128-bit pieces of 16 / lr lanes each
    let per = 16 / lr;
    var k: u32 = 0;
    while k < n {
        let cnt: u32 = if n - k < per { n - k } else { per };
        a_leaf.push(ALeaf { fp: true, off: off + k * lb, size: 16, t: t, nl: cnt, lm: lb, lr: lr });
        k += per;
    }
}
// Whether part P is a plain load/store of `size` bytes.
checkfree fn a_plain(P: APart) -> bool { P.nl * P.lm == P.size && P.lm == P.lr }
// V register r = part P of the memory at base + off.
fn a_part_load_v(P: APart, r: u32, base: u32, off: i64) {
    if a_plain(P) {
        a_ls(LS_FLDR, a_log2(P.size), r, base, off + P.off as i64);
        return;
    }
    let sm = a_log2(P.lm);
    let sr = a_log2(P.lr);
    if P.lm == P.lr && P.lm >= 4 && P.nl * P.lm > 8 {
        // (widened: the lanes are contiguous; read them as one access when it stays inside)
        a_vzero(true, r);
    } else {
        a_vzero(true, r);
    }
    for k in 0..P.nl {
        let o: i64 = off + P.off as i64 + (k * P.lm) as i64;
        if P.lm == 8 && P.lr == 8 {
            a_ls(LS_LDR, 3, AX17, base, o);
            a_ins_gp(3, r, AX17, k);
        } else {
            a_ls(LS_LDR, sm, AX17, base, o);
            a_ins_gp(sr, r, AX17, k);
        }
    }
}
// Part P from V register r to the memory at base + off.
fn a_part_store_v(P: APart, r: u32, base: u32, off: i64) {
    if a_plain(P) {
        a_ls(LS_FSTR, a_log2(P.size), r, base, off + P.off as i64);
        return;
    }
    let sm = a_log2(P.lm);
    let sr = a_log2(P.lr);
    for k in 0..P.nl {
        let o: i64 = off + P.off as i64 + (k * P.lm) as i64;
        a_umov(sr, AX17, r, k);
        a_ls(LS_STR, sm, AX17, base, o);
    }
}
fn a_classify_reset() {
    a_parts.clear();
    a_pfirst.clear();
    a_ngrn = 0;
    a_nsrn = 0;
    a_nstk = 0;
}
fn a_stack(size: u32, al: u32) -> u32 {
    a_nstk = align_up32(a_nstk, al);
    let o = a_nstk;
    a_nstk += size;
    return o;
}
fn a_part(kind: u32, reg: u32, L: ALeaf, soff: u32) {
    a_parts.push(APart { kind: kind, reg: reg, off: L.off, size: L.size, soff: soff, t: L.t, nl: L.nl, lm: L.lm, lr: L.lr });
}
// Appends the parts of the next argument (type t, ABI word w).
fn a_classify(t: u32, w: u32) {
    a_pfirst.push(a_parts.len as! u32);
    if w & ABI_BYVAL != 0 {
        var al = abi_align(w);
        if al < 8 { al = 8; }
        let size = abi_size(w);
        let o = a_stack(align_up32(size, 8), al);
        a_parts.push(APart { kind: AP_BYVAL, reg: 0, off: 0, size: size, soff: o, t: t, nl: 1, lm: size, lr: size });
        return;
    }
    if w & ABI_SRET != 0 {
        a_parts.push(APart { kind: AP_X, reg: 8, off: 0, size: 8, soff: 0, t: GIR_T_PTR, nl: 1, lm: 8, lr: 8 });
        return;
    }
    a_leaf.clear();
    a_leaves(t, 0);
    let D = M.types[t];
    // a block: an array of one member type, or an INT2
    var blk = D.cls == C_INT2;
    if D.kind == TK_ARRAY && a_leaf.len != 0 {
        blk = true;
        for L in a_leaf { if L.fp != a_leaf[0].fp || L.size != a_leaf[0].size { blk = false; } }
        if a_leaf.len < 2 && D.cls != C_INT2 { blk = a_leaf.len == 1; }
    }
    if blk {
        let n: u32 = a_leaf.len as! u32;
        let fp = a_leaf[0].fp;
        if !fp && D.align >= 16 && a_ngrn % 2 == 1 && a_ngrn < 8 { a_ngrn++; }
        if fp && a_nsrn + n <= 8 {
            for L in a_leaf {
                a_part(AP_V, a_nsrn, L, 0);
                a_nsrn++;
            }
            return;
        }
        if !fp && a_ngrn + n <= 8 {
            for L in a_leaf {
                a_part(AP_X, a_ngrn, L, 0);
                a_ngrn++;
            }
            return;
        }
        if fp { a_nsrn = 8; } else { a_ngrn = 8; }
        var al: u32 = if D.align < 16 { D.align } else { 16 };
        if al < 8 { al = 8; }
        var first = true;
        for L in a_leaf {
            let o = a_stack(L.size, if first { al } else { 1 });
            first = false;
            a_part(AP_STK, 0, L, o);
        }
        a_nstk = align_up32(a_nstk, 8);
        return;
    }
    for L in a_leaf {
        if L.fp {
            if a_nsrn < 8 {
                a_part(AP_V, a_nsrn, L, 0);
                a_nsrn++;
            } else {
                let sz: u32 = if L.size > 8 { 16 } else { 8 };
                a_part(AP_STK, 0, L, a_stack(sz, sz));
            }
        } else {
            if a_ngrn < 8 {
                a_part(AP_X, a_ngrn, L, 0);
                a_ngrn++;
            } else {
                a_part(AP_STK, 0, L, a_stack(8, 8));
            }
        }
    }
}
fn a_classify_end() { a_pfirst.push(a_parts.len as! u32); }

// Return parts of type t (the members in x0..x7 / v0..v7, in order).
var a_rparts: APart[>..] = [];
fn a_classify_ret(t: u32) {
    a_rparts.clear();
    a_leaf.clear();
    a_leaves(t, 0);
    var g: u32 = 0;
    var f: u32 = 0;
    for L in a_leaf {
        if L.fp {
            a_rparts.push(APart { kind: AP_V, reg: f, off: L.off, size: L.size, soff: 0, t: L.t, nl: L.nl, lm: L.lm, lr: L.lr });
            f++;
        } else {
            a_rparts.push(APart { kind: AP_X, reg: g, off: L.off, size: L.size, soff: 0, t: L.t, nl: 1, lm: L.size, lr: L.size });
            g++;
        }
    }
}

// ------------------------------------------------------------ moves

// Emits the moves a_mvs[k] -> a_mvd[k] (registers 0..63; GPR to GPR or V to V, a
// parallel copy; cycles go through x16 / v31).
var a_mvs: u32[>..] = [];
var a_mvd: u32[>..] = [];
fn a_emit_moves() {
    var n = a_mvs.len;
    var k: i64 = 0;
    while k < n {
        if a_mvs[k] == a_mvd[k] {
            a_mvs[k] = a_mvs[n - 1];
            a_mvd[k] = a_mvd[n - 1];
            n--;
        } else {
            k++;
        }
    }
    while n > 0 {
        var done = false;
        var i: i64 = 0;
        while i < n {
            let d = a_mvd[i];
            var busy = false;
            for q in 0..n { if q != i && a_mvs[q] == d { busy = true; } }
            if !busy {
                let s = a_mvs[i];
                if d >= 32 { a_vmov(true, d, s); } else { a_mov_rr(true, d, s); }
                a_mvs[i] = a_mvs[n - 1];
                a_mvd[i] = a_mvd[n - 1];
                n--;
                done = true;
                break;
            }
            i++;
        }
        if done { continue; }
        // a cycle: break it through the scratch register of the class
        let s = a_mvs[0];
        let tmp: u32 = if s >= 32 { AV31 } else { AX16 };
        if s >= 32 { a_vmov(true, tmp, s); } else { a_mov_rr(true, tmp, s); }
        for q in 0..n { if a_mvs[q] == s { a_mvs[q] = tmp; } }
    }
    a_mvs.clear();
    a_mvd.clear();
}

// ------------------------------------------------------------ calls

// Before a call: values in caller-saved registers that live on move to a free
// callee-saved register of their class, or are written to their home.
fn a_save_caller() {
    var m = ~a_free & a_alloc & (A_GP_CALLER | A_V_CALLER);
    while m != 0 {
        let r = actz(m);
        m &= m - 1;
        let id = a_rval[r];
        if id >= RV_TEMP || !a_live_after(id) { continue; }
        if vi[id].st & ST_GLOB == 0 {
            var cs: u64 = 0;
            if r < 32 { cs = a_free & a_alloc & A_GP_CALLEE & ~a_lock; }
            else if M.types[vtype(id)].store <= 8 { cs = a_free & a_alloc & A_V_CALLEE & ~a_lock; }
            if cs != 0 {
                let to = actz(cs);
                if r < 32 { a_mov_rr(true, to, r); } else { a_vmov(false, to, r); }
                a_free &= ~abit(to);
                a_csused |= abit(to);
                a_rval[to] = id;
                vi[id].reg = to as! u8;
                a_release(r);
                continue;
            }
        }
        if vi[id].st & ST_MEM == 0 { a_store_home(id, r); }
    }
}
// After a call: the caller-saved registers hold nothing.
fn a_after_call() {
    let mask = A_GP_CALLER | A_V_CALLER;
    var m = ~a_free & a_alloc & mask;
    while m != 0 {
        let r = actz(m);
        m &= m - 1;
        let id = a_rval[r];
        if id < RV_TEMP { vi[id].reg = NOREG; }
        a_rval[r] = RV_NONE;
    }
    a_free |= a_alloc & mask;
    a_tmp &= ~mask;
    a_lock &= ~mask;
}

// The address of the memory that holds value v (any class) into register r:
// its home (written there first if it lives only in a register), its alloca
// area, a constant's pool entry.
fn a_val_addr(v: u32, r: u32) {
    let k = gir_kind(v);
    if k == GIR_V_CONST {
        a_const_addr(r, gir_idx(v));
        return;
    }
    let id = vid(v);
    let rr: u32 = vi[id].reg;
    if rr < 64 && vi[id].st & ST_MEM == 0 { a_store_home(id, rr); }
    a_add_off(r, AFP, a_home_off(id) as i64);
}
// The memory of value v as (base register, offset): x29 + its home, or the
// pool entry's address in r.
fn a_val_mem(v: u32, r: u32) -> u32, i64 {
    let k = gir_kind(v);
    if k == GIR_V_CONST {
        a_const_addr(r, gir_idx(v));
        return r, 0;
    }
    let id = vid(v);
    let rr: u32 = vi[id].reg;
    if rr < 64 && vi[id].st & ST_MEM == 0 { a_store_home(id, rr); }
    return AFP, a_home_off(id) as i64;
}
// Loads `size` bytes (1..8, zero-extended) at base + off into x register r.
fn a_load_n(r: u32, base: u32, off: i64, size: u32) {
    if size == 1 || size == 2 || size == 4 || size == 8 {
        a_ls(LS_LDR, a_log2(size), r, base, off);
        return;
    }
    // 3, 5, 6, 7 bytes: the largest power of two first, then the smaller
    // pieces above it, each through x17 (r must not be the base)
    var p: u32 = 0;
    while p < size {
        let rest = size - p;
        let c: u32 = if rest >= 4 { 4 } else if rest >= 2 { 2 } else { 1 };
        if p == 0 {
            a_ls(LS_LDR, a_log2(c), r, base, off);
        } else {
            a_ls(LS_LDR, a_log2(c), AX17, base, off + p as i64);
            a_logic_rr(AL_ORR, true, r, r, AX17, 0, 8 * p);
        }
        p += c;
    }
}
fn a_store_n(r: u32, base: u32, off: i64, size: u32) {
    if size == 1 || size == 2 || size == 4 || size == 8 {
        a_ls(LS_STR, a_log2(size), r, base, off);
        return;
    }
    var p: u32 = 0;
    while p < size {
        let rest = size - p;
        let c: u32 = if rest >= 4 { 4 } else if rest >= 2 { 2 } else { 1 };
        if p == 0 {
            a_ls(LS_STR, a_log2(c), r, base, off);
        } else {
            a_lsr_imm(true, AX17, r, 8 * p);
            a_ls(LS_STR, a_log2(c), AX17, base, off + p as i64);
        }
        p += c;
    }
}
// Whether an access of 2^s bytes at offset off is one instruction.
checkfree fn a_ls_ok(s: u32, off: i64) -> bool {
    let sz: i64 = (1 as i64) << s;
    return off >= 0 && off % sz == 0 && off < 4096 * sz || off >= -256 && off < 256;
}
// The chunks of an n-byte copy: 16, 8, 4, 2, 1 bytes; whether all are one
// instruction at base offset o.
fn a_copy_ok(o: i64, n: u32) -> bool {
    var p: u32 = 0;
    while p < n {
        let rest = n - p;
        let c: u32 = if rest >= 16 { 16 } else if rest >= 8 { 8 } else if rest >= 4 { 4 } else if rest >= 2 { 2 } else { 1 };
        if !a_ls_ok(a_log2(c), o + p as i64) { return false; }
        p += c;
    }
    return true;
}
// Copies n bytes from [sb + soff] to [db + doff] through v31 (b/h/s/d/q
// moves); a source too far for the offsets goes through x16, a destination
// through x17. Nothing else is written.
fn a_copy(db: u32, doff: i64, sb: u32, soff: i64, n: u32) {
    var sbr = sb;
    var so = soff;
    var dbr = db;
    var dof = doff;
    if !a_copy_ok(so, n) {
        a_add_off(AX16, sb, so);
        sbr = AX16;
        so = 0;
    }
    if !a_copy_ok(dof, n) {
        a_add_off(AX17, db, dof);
        dbr = AX17;
        dof = 0;
    }
    var p: u32 = 0;
    while p < n {
        let rest = n - p;
        let c: u32 = if rest >= 16 { 16 } else if rest >= 8 { 8 } else if rest >= 4 { 4 } else if rest >= 2 { 2 } else { 1 };
        a_ls(LS_FLDR, a_log2(c), AV31, sbr, so + p as i64);
        a_ls(LS_FSTR, a_log2(c), AV31, dbr, dof + p as i64);
        p += c;
    }
}

// The call instruction (bl to a global, or blr x16), with an invoke's call
// site and its outgoing argument area for the unwinder.
fn a_call_insn(callee: u32, direct: bool, args: u32, creg: u32) {
    let st = here();
    if call_lp != GIR_NONE && args != 0 { a_cfi_ev(st, CE_ARGS, args, 0); }
    if direct {
        a_rela(g_sym[gir_idx(callee)], R_AARCH64_CALL26, 0);
        a_bl_raw();
    } else {
        a_blr(creg);
    }
    if call_lp != GIR_NONE {
        f_sites.push(CallSite { start: st, end: here(), lp: call_lp });
        if args != 0 { a_cfi_ev(here(), CE_ARGS, 0, 0); }
    }
}
// A call of a library function the back-end names (fp128, outline atomics).
fn a_call_lib(name: const u8[:]) {
    a_rela(a_libsym(name), R_AARCH64_CALL26, 0);
    a_bl_raw();
}

fn a_lower_call(I: Inst, j: u32) {
    let n = I.c;
    let s = I.b;
    let callee = I.a;
    let direct = gir_kind(callee) == GIR_V_GLOBAL && M.globals[gir_idx(callee)].kind == G_FUNC;
    a_classify_reset();
    for k in 0..n {
        let v = M.opnds[s + 2 * k];
        a_classify(type_of(v), M.opnds[s + 2 * k + 1]);
    }
    a_classify_end();
    let sbytes = align_up32(a_nstk, 16);
    if sbytes != 0 { a_add_off(ASP, ASP, -(sbytes as i64)); }
    // stack parts and byval copies first (they use x17 / v31 and temps)
    if a_nstk != 0 {
        // (no register is allocated or locked here: a call may have many stack arguments)
        for k in 0..n {
            let v = M.opnds[s + 2 * k];
            let t = type_of(v);
            var r: u32 = 64;
            if is_val(v) {
                r = vi[vid(v)].reg;
                a_note(vid(v));
            }
            for q in a_pfirst[k]..a_pfirst[k + 1] {
                let P = a_parts[q];
                if P.kind == AP_STK {
                    let c = arc(t);
                    if c == ARC_GPR {
                        var x = r;
                        if x >= 32 {
                            x = AX17;
                            if gir_kind(v) == GIR_V_CONST && a_const_bits(gir_idx(v)) == 0 { x = AZR; }
                            else { a_mat_gpr(v, AX17); }
                        }
                        a_ls(LS_STR, 3, x, ASP, P.soff as i64);
                    } else if a_inv(c) && P.off == 0 && P.size == M.types[t].store && a_plain(P) {
                        var x = r;
                        if x < 32 || x >= 64 {
                            x = AV31;
                            a_mat_v(v, AV31);
                        }
                        a_ls(LS_FSTR, a_log2(P.size), x, ASP, P.soff as i64);
                    } else if a_plain(P) || P.size <= 8 && P.lm == P.lr && P.nl * P.lm <= P.size {
                        let b, o = a_val_mem(v, AX16);
                        a_copy(ASP, P.soff as i64, b, o + P.off as i64, if a_plain(P) { P.size } else { P.nl * P.lm });
                    } else {
                        let b, o = a_val_mem(v, AX16);
                        a_part_load_v(P, AV31, b, o);
                        a_ls(LS_FSTR, a_log2(P.size), AV31, ASP, P.soff as i64);
                    }
                } else if P.kind == AP_BYVAL {
                    var x = r;
                    if x >= 32 {
                        x = AX16;
                        a_mat_gpr(v, AX16);
                    }
                    a_copy(ASP, P.soff as i64, x, 0, P.size);
                }
            }
        }
    }
    a_save_caller();
    // an indirect callee in a register: blr that register, unless an argument
    // goes there (then a copy in x9..x15); otherwise loaded into x16 last
    var creg: u32 = AX16;
    if !direct && is_val(callee) && vi[vid(callee)].reg < 32 {
        let cid = vid(callee);
        creg = vi[cid].reg;
        if creg <= AX8 {
            let r = a_alloc_r(0xFE00, 0xFE00);
            a_rval[r] = RV_TEMP;
            a_tmp |= abit(r);
            a_mov_rr(true, r, creg);
            creg = r;
        }
        a_lock |= abit(creg);
        a_note(cid);
    }
    // register parts: values in registers by a parallel copy, the rest loaded after
    for k in 0..n {
        let v = M.opnds[s + 2 * k];
        if !is_val(v) { continue; }
        let id = vid(v);
        let r: u32 = vi[id].reg;
        if r >= 64 { continue; }
        let q = a_pfirst[k];
        if a_pfirst[k + 1] != q + 1 { continue; }
        let P = a_parts[q];
        if P.kind == AP_X && r < 32 {
            a_mvs.push(r);
            a_mvd.push(P.reg);
            a_note(id);
        } else if P.kind == AP_V && r >= 32 {
            a_mvs.push(r);
            a_mvd.push(AV0 + P.reg);
            a_note(id);
        }
    }
    a_emit_moves();
    for k in 0..n {
        let v = M.opnds[s + 2 * k];
        let t = type_of(v);
        let q0 = a_pfirst[k];
        let q1 = a_pfirst[k + 1];
        let single = q1 == q0 + 1;
        if single && is_val(v) && vi[vid(v)].reg < 64 {
            let P = a_parts[q0];
            if P.kind == AP_X || P.kind == AP_V { continue; }   // (moved)
        }
        let c = arc(t);
        if single && c == ARC_GPR && a_parts[q0].kind == AP_X {
            a_mat_gpr(v, a_parts[q0].reg);
            continue;
        }
        if single && a_inv(c) && a_parts[q0].kind == AP_V {
            a_mat_v(v, AV0 + a_parts[q0].reg);
            continue;
        }
        // parts of a value in memory
        var have = false;
        for q in q0..q1 { if a_parts[q].kind == AP_X || a_parts[q].kind == AP_V { have = true; } }
        if !have { continue; }
        let b, o = a_val_mem(v, AX16);
        for q in q0..q1 {
            let P = a_parts[q];
            if P.kind == AP_X { a_load_n(P.reg, b, o + P.off as i64, P.size); }
            else if P.kind == AP_V { a_part_load_v(P, AV0 + P.reg, b, o); }
        }
    }
    if !direct && creg == AX16 { a_mat_gpr(callee, AX16); }
    a_call_insn(callee, direct, sbytes, creg);
    a_after_call();
    if sbytes != 0 { a_add_off(ASP, ASP, sbytes as i64); }
    a_call_result(j, I.ty);
}
// The result of call j (in the return registers).
fn a_call_result(j: u32, t: u32) {
    if t == GIR_T_VOID { return; }
    let c = arc(t);
    if c == ARC_GPR {
        let bits = bits_of(t);
        if exact_width(bits) { a_set(j, AX0, bits < 64); }
        else {
            a_zext(AX0, bits);
            a_set(j, AX0, false);
        }
        return;
    }
    if a_inv(c) {
        a_set(j, AV0, false);
        return;
    }
    // memory classes: the parts to the result's home
    a_classify_ret(t);
    vi[j].st |= ST_MEM;
    vi[j].reg = NOREG;
    let off: i64 = a_home_off(j) as i64;
    for P in a_rparts {
        if P.kind == AP_X { a_store_n(P.reg, AFP, off + P.off as i64, P.size); }
        else { a_part_store_v(P, AV0 + P.reg, AFP, off); }
    }
}

// The return value v (type t) into the return registers.
fn a_ret_value(v: u32, t: u32) {
    let c = arc(t);
    if c == ARC_GPR {
        a_gpr_into(v, AX0, false);
        return;
    }
    if a_inv(c) {
        a_vr_into(v, AV0);
        return;
    }
    a_classify_ret(t);
    let b, o = a_val_mem(v, AX16);
    for P in a_rparts {
        if P.kind == AP_X { a_load_n(P.reg, b, o + P.off as i64, P.size); }
        else { a_part_load_v(P, AV0 + P.reg, b, o); }
    }
}

// ------------------------------------------------------------ arguments

// Incoming stack arguments are at x29 + frame size + offset, which is known
// only when the prologue is made: the prologue copies them to their homes.
struct AProArg { a: u32, off: i32 }
var a_pro: AProArg[>..] = [];
var a_fparts: APart[>..] = [];   // the function's own parameters (a_parts is reused by calls)
var a_fpfirst: u32[>..] = [];
var a_va_gr: u32 = 0;     // GPRs taken by named arguments
var a_va_vr: u32 = 0;
var a_va_stk: u32 = 0;    // stack bytes of named arguments

fn a_setup_args() {
    a_classify_reset();
    for a in 0..f_nargs { a_classify(M.opnds[f_args + 2 * a], M.opnds[f_args + 2 * a + 1]); }
    a_classify_end();
    a_va_gr = a_ngrn;
    a_va_vr = a_nsrn;
    a_va_stk = a_nstk;
    a_fparts.clear();
    a_fparts.append(a_parts);
    a_fpfirst.clear();
    a_fpfirst.append(a_pfirst);
    a_pro.clear();
    for a in 0..f_nargs {
        let id = f_nins + a;
        if vi[id].nuse == 0 { continue; }
        let t = M.opnds[f_args + 2 * a];
        let q0 = a_pfirst[a];
        let q1 = a_pfirst[a + 1];
        let P = a_parts[q0];
        let c = arc(t);
        if P.kind == AP_BYVAL {
            // the address of the copy, formed in the prologue into a slot
            vi[id].home = H_PTR;
            vi[id].off = a_new_slot(8);
            vi[id].st |= ST_MEM;
            a_pro.push(AProArg { a: a, off: vi[id].off });
            continue;
        }
        if q1 == q0 + 1 && (P.kind == AP_X && c == ARC_GPR || P.kind == AP_V && a_inv(c) && P.size == M.types[t].store) {
            let r: u32 = if P.kind == AP_X { P.reg } else { AV0 + P.reg };
            vi[id].reg = r as! u8;
            var st = vi[id].st;
            if c == ARC_GPR && bits_of(t) < 64 { st |= ST_EXT; }
            vi[id].st = st;
            if st & ST_GLOB != 0 {
                a_home_off(id);
                vi[id].st |= ST_MEM;
                a_pro.push(AProArg { a: a, off: vi[id].off });
            }
            continue;
        }
        // stack parts, aggregates, INT2: copied to a home by the prologue
        a_home_off(id);
        vi[id].st |= ST_MEM;
        vi[id].reg = NOREG;
        a_pro.push(AProArg { a: a, off: vi[id].off });
    }
}
// The entry block starts with the register-resident arguments in their registers.
fn a_entry_state() {
    a_block_start();
    for a in 0..f_nargs {
        let id = f_nins + a;
        if vi[id].nuse == 0 { continue; }
        let r: u32 = vi[id].reg;
        if r < 64 {
            a_rval[r] = id;
            a_free &= ~abit(r);
        }
    }
}
// Prologue code for the arguments in a_pro (the frame size is known: incoming
// stack arguments are at x29 + a_frame + offset).
fn a_prologue_args() {
    var qq: i64 = 0;
    for a in 0..f_nargs {
        if qq >= a_pro.len || a_pro[qq].a != a { continue; }
        let ho: i64 = a_pro[qq].off as i64;
        qq++;
        let id = f_nins + a;
        let t = M.opnds[f_args + 2 * a];
        let q0 = a_fpfirst[a];
        let q1 = a_fpfirst[a + 1];
        for q in q0..q1 {
            let P = a_fparts[q];
            if P.kind == AP_BYVAL {
                a_add_off(AX16, AFP, a_frame + P.soff as i64);
                a_ls(LS_STR, 3, AX16, AFP, ho);
            } else if P.kind == AP_X {
                if q1 == q0 + 1 && arc(t) == ARC_GPR {
                    a_store_t(P.reg, AFP, ho, t);
                } else {
                    a_store_n(P.reg, AFP, ho + P.off as i64, P.size);
                }
            } else if P.kind == AP_V {
                a_part_store_v(P, AV0 + P.reg, AFP, ho);
            } else if a_plain(P) {
                a_copy(AFP, ho + P.off as i64, AFP, a_frame + P.soff as i64, P.size);
            } else {
                a_ls(LS_FLDR, a_log2(P.size), AV31, AFP, a_frame + P.soff as i64);
                a_part_store_v(P, AV31, AFP, ho);
            }
        }
        if vi[id].reg < 64 { vi[id].st |= ST_MEM; }
    }
}

// Variadic functions: the prologue saves x(n)..x7 below __gr_top and
// q(n)..q7 below __vr_top, and the pointer to the first variadic stack
// argument in a slot (va_start reads it).
var a_va_gr_off: i64 = 0;    // the GPR save area (64 bytes) at x29 + off
var a_va_vr_off: i64 = 0;    // the FP/SIMD save area (128 bytes)
var a_va_stk_off: i64 = 0;   // slot holding __stack
fn a_save_va_regs() {
    var r = a_va_gr;
    while r < 8 {
        if r + 1 < 8 {
            a_ldstp(false, 0, r, r + 1, AFP, a_va_gr_off + 8 * r as i64);
            r += 2;
        } else {
            a_ls(LS_STR, 3, r, AFP, a_va_gr_off + 8 * r as i64);
            r++;
        }
    }
    var v = a_va_vr;
    while v < 8 {
        a_ls(LS_FSTR, 4, AV0 + v, AFP, a_va_vr_off + 16 * v as i64);
        v++;
    }
    a_add_off(AX16, AFP, a_frame + a_va_stk as i64);
    a_ls(LS_STR, 3, AX16, AFP, a_va_stk_off);
}
// va_start(ap): { __stack, __gr_top, __vr_top, __gr_offs, __vr_offs }.
fn a_lower_vastart(I: Inst) {
    let p = a_gpr(I.a, false);
    let t = a_temp();
    a_ls(LS_LDR, 3, t, AFP, a_va_stk_off);
    a_ls(LS_STR, 3, t, p, 0);
    a_add_off(t, AFP, a_va_gr_off + 64);
    a_ls(LS_STR, 3, t, p, 8);
    a_add_off(t, AFP, a_va_vr_off + 128);
    a_ls(LS_STR, 3, t, p, 16);
    a_mov_imm(t, (0 - 8 * (8 - a_va_gr) as i64) as! u64, false);
    a_ls(LS_STR, 2, t, p, 24);
    a_mov_imm(t, (0 - 16 * (8 - a_va_vr) as i64) as! u64, false);
    a_ls(LS_STR, 2, t, p, 28);
}
