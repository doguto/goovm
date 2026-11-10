import binary;

// Instruction simplification on the OIR (opt.goose): constant folding,
// algebraic identities, strength reduction, compare and cast folding, GEP
// merging (an "instcombine-lite"). One forward pass over the blocks in RPO;
// operands are simplified before their users except around loops, and the
// pipeline runs the pass more than once.

var fold_changed = false;

// v as an INT constant of at most 64 bits: (true, its zero-extended value).
fn ci(v: u32) -> bool, u64 {
    if gir_kind(v) != GIR_V_CONST { return false, 0; }
    let C = x_consts[xb_c + gir_idx(v)];
    if C.data != GIR_NONE || cls_of(C.ty) != C_INT { return false, 0; }
    return true, C.lo;
}
// x (zero-extended from bits) sign-extended to 64 bits.
checkfree fn sx(x: u64, bits: u32) -> i64 {
    if bits >= 64 { return x as! i64; }
    let s: u32 = 64 - bits;
    return ((x << s) as! i64) >> s;
}
// log2 of x if it is a power of two (> 1), else 0.
fn log2p(x: u64) -> u32 {
    if x < 2 || x & (x - 1) != 0 { return 0; }
    return ctz(x) as! u32;
}
inline fn int_ty(t: u32) -> bool { cls_of(t) == C_INT }

// A new instruction before `at` with the given fields (dbg of `at`).
fn ins_new(at: u32, op: u32, ty: u32, a: u32, b: u32) -> u32 {
    let x = new_inst(Inst { op: op as! u8, sub: 0, flags: 0, ty: ty as! u16, aux: 0, a: a, b: b, c: 0,
                            dbg: o_ins[at].dbg });
    link_before(at, x);
    return x;
}

// Folds an integer binary operation on constants (zero-extended, bits <=
// 64): (ok, result). Not folded: division by zero, signed overflow of
// division, shifts by the width or more (undefined).
fn fold_bin(op: u32, bits: u32, a: u64, b: u64) -> bool, u64 {
    let m = wmask(bits);
    if op == GIR_ADD { return true, (a + b) & m; }
    if op == GIR_SUB { return true, (a - b) & m; }
    if op == GIR_MUL { return true, (a * b) & m; }
    if op == GIR_AND { return true, a & b; }
    if op == GIR_OR { return true, a | b; }
    if op == GIR_XOR { return true, a ^ b; }
    if op == GIR_SHL || op == GIR_LSHR || op == GIR_ASHR {
        if b >= bits as u64 { return false, 0; }
        let n: u32 = b as! u32;
        if op == GIR_SHL { return true, (a << n) & m; }
        if op == GIR_LSHR { return true, a >> n; }
        return true, ((sx(a, bits) >> n) as! u64) & m;
    }
    if b == 0 { return false, 0; }
    if op == GIR_UDIV { return true, a / b; }
    if op == GIR_UREM { return true, a % b; }
    let sa = sx(a, bits);
    let sb = sx(b, bits);
    if sb == -1 { return op == GIR_SREM, 0; }   // (x / -1 may overflow: left alone)
    if op == GIR_SDIV { return true, ((sa / sb) as! u64) & m; }
    // (Goose's % on signed integers is Euclidean; srem truncates: rem)
    if op == GIR_SREM { return true, (rem(sa, sb) as! u64) & m; }
    return false, 0;
}
// Folds icmp `p` on constants of `bits` bits.
fn fold_icmp(p: u32, bits: u32, a: u64, b: u64) -> bool {
    let sa = sx(a, bits);
    let sb = sx(b, bits);
    return match p {
        GIR_EQ => a == b, GIR_NE => a != b, GIR_UGT => a > b, GIR_UGE => a >= b, GIR_ULT => a < b,
        GIR_ULE => a <= b, GIR_SGT => sa > sb, GIR_SGE => sa >= sb, GIR_SLT => sa < sb, _ => sa <= sb,
    };
}
checkfree fn inv_pred(p: u32) -> u32 {
    return match p {
        GIR_EQ => GIR_NE, GIR_NE => GIR_EQ, GIR_UGT => GIR_ULE, GIR_UGE => GIR_ULT, GIR_ULT => GIR_UGE,
        GIR_ULE => GIR_UGT, GIR_SGT => GIR_SLE, GIR_SGE => GIR_SLT, GIR_SLT => GIR_SGE, _ => GIR_SGT,
    };
}
checkfree fn swp_pred(p: u32) -> u32 {
    return match p {
        GIR_UGT => GIR_ULT, GIR_UGE => GIR_ULE, GIR_ULT => GIR_UGT, GIR_ULE => GIR_UGE,
        GIR_SGT => GIR_SLT, GIR_SGE => GIR_SLE, GIR_SLT => GIR_SGT, GIR_SLE => GIR_SGE, _ => p,
    };
}
inline fn bool_c(x: bool) -> u32 { mk_const(GIR_T_I1, if x { 1 } else { 0 }, 0) }

// (E2) FP arithmetic on two f32 or f64 constants (IEEE, round to nearest).
fn simp_fbin(i: u32) -> u32 {
    let I = o_ins[i];
    let t: u32 = I.ty;
    if t != GIR_T_F32 && t != GIR_T_F64 { return NIL; }
    let ka, x = fpc(res(I.a));
    let kb, y = fpc(res(I.b));
    if !ka || !kb { return NIL; }
    let op: u32 = I.op;
    if t == GIR_T_F64 {
        var r: f64 = 0.0;
        if op == GIR_FADD { r = x + y; } else if op == GIR_FSUB { r = x - y; } else if op == GIR_FMUL { r = x * y; } else { r = x / y; }
        return mk_const(t, binary::bits_of_f64(r), 0);
    }
    let xf = x as f32;
    let yf = y as f32;
    var r: f32 = 0.0;
    if op == GIR_FADD { r = xf + yf; } else if op == GIR_FSUB { r = xf - yf; } else if op == GIR_FMUL { r = xf * yf; } else { r = xf / yf; }
    return mk_const(t, binary::bits_of_f32(r) as u64, 0);
}

// One pass over the function. Returns whether anything changed.
fn simplify() -> bool {
    fold_changed = false;
    for b in rpo {
        var i = b_first[b];
        while i != NIL {
            let nx = o_nxt[i];
            let r = simp(i);
            if r != NIL {
                replace(i, r);
                fold_changed = true;
            }
            i = nx;
        }
    }
    return fold_changed;
}

// Simplifies instruction i: a value that replaces it, or NIL (i may have been
// rewritten in place).
fn simp(i: u32) -> u32 {
    let op: u32 = o_ins[i].op;
    if op >= GIR_ADD && op <= GIR_ASHR {
        o_ins[i].a = res(o_ins[i].a);
        o_ins[i].b = res(o_ins[i].b);
        if int_ty(o_ins[i].ty) && bits_of(o_ins[i].ty) <= 64 { return simp_bin(i); }
        return NIL;
    }
    if op == GIR_ICMP {
        o_ins[i].a = res(o_ins[i].a);
        o_ins[i].b = res(o_ins[i].b);
        return simp_icmp(i);
    }
    if op == GIR_SELECT { return simp_select(i); }
    if op >= GIR_ZEXT && op <= GIR_BITCAST {
        o_ins[i].a = res(o_ins[i].a);
        return simp_cast(i);
    }
    if op == GIR_GEP { return simp_gep(i); }
    if op == GIR_EXTRACTVALUE {
        let x = simp_extract_ins(i);
        if x != NIL { return x; }
        return simp_extract(i);
    }
    if op == GIR_EXTRACTELT { return simp_extract_elt(i); }
    if op == GIR_FCMP {
        o_ins[i].a = res(o_ins[i].a);
        o_ins[i].b = res(o_ins[i].b);
        return simp_fcmp(i);
    }
    if op >= GIR_FADD && op <= GIR_FDIV { return simp_fbin(i); }
    if op == GIR_CALL { return simp_call(i); }
    return NIL;
}

// pow(x, 2.0) -> x * x (LLVM's LibCallSimplifier does it at any level; what
// libstdc++'s std::pow(double, int) leaves for a square).
fn simp_call(i: u32) -> u32 {
    let I = o_ins[i];
    if I.flags & (IF_INVOKE | IF_VARARG) != 0 || I.c != 2 || I.ty != GIR_T_F64 || gir_kind(I.a) != GIR_V_GLOBAL {
        return NIL;
    }
    if sr_isfn[gir_idx(I.a)] != 4 { return NIL; }
    let y = res(o_ops[I.b + 2]);
    if gir_kind(y) != GIR_V_CONST { return NIL; }
    let C = x_consts[xb_c + gir_idx(y)];
    if C.ty != GIR_T_F64 || C.lo != 0x4000000000000000 { return NIL; }
    let x = res(o_ops[I.b]);
    return ins_new(i, GIR_FMUL, GIR_T_F64, x, x);
}

// An f32 or f64 constant as an f64: (ok, value).
fn fpc(v: u32) -> bool, f64 {
    if gir_kind(v) != GIR_V_CONST { return false, 0.0; }
    let C = x_consts[xb_c + gir_idx(v)];
    if C.data != GIR_NONE && C.data != 0 { return false, 0.0; }
    if C.ty == GIR_T_F64 { return true, binary::f64_of_bits(C.lo); }
    if C.ty == GIR_T_F32 { return true, binary::f32_of_bits((C.lo & 0xFFFFFFFF) as! u32) as f64; }
    return false, 0.0;
}
// (E2) FP compares: of constants, of fabs(x) with +0.0.
fn simp_fcmp(i: u32) -> u32 {
    let I = o_ins[i];
    let p: u32 = I.sub;
    if p == F_FALSE { return bool_c(false); }
    if p == F_TRUE { return bool_c(true); }
    let a = I.a;
    let b = I.b;
    let ka, x = fpc(a);
    let kb, y = fpc(b);
    if ka && kb && (I.aux == GIR_T_F32 || I.aux == GIR_T_F64) {
        // the outcome: unordered (8), less (4), greater (2), equal (1)
        var o: u32 = 1;
        if x != x || y != y { o = 8; } else if x < y { o = 4; } else if x > y { o = 2; }
        return bool_c(p & o != 0);
    }
    if gir_kind(b) == GIR_V_CONST && is_inst(a) && o_ins[a].op == GIR_FABS {
        let C = x_consts[xb_c + gir_idx(b)];
        if C.data == GIR_NONE && C.lo == 0 && C.hi == 0 && (C.ty == GIR_T_F32 || C.ty == GIR_T_F64) {
            // |x| < 0 never; |x| >= 0 unless NaN (then unordered)
            if p == F_OLT { return bool_c(false); }
            if p == F_UGE { return bool_c(true); }
        }
    }
    return NIL;
}

// (E2) extractvalue through a chain of insertvalues: the inserted value at
// the same offset and type, or what is below an insertion elsewhere; of a
// zero constant: zero.
fn simp_extract_ins(i: u32) -> u32 {
    let t: u32 = o_ins[i].ty;
    let off = o_ins[i].b;
    let sz = store_of(t);
    var v = res(o_ins[i].a);
    var n = 0;
    while n < 64 {
        n++;
        if gir_kind(v) == GIR_V_CONST {
            let C = x_consts[xb_c + gir_idx(v)];
            if C.data == GIR_NONE && cls_of(C.ty) == C_MEM { return undef_of(t); }
            return NIL;
        }
        if !is_inst(v) { return NIL; }
        let I = o_ins[v];
        if I.op == GIR_EXTRACTVALUE && cls_of(I.ty) == C_MEM && n > 1 {
            // (a field of a field)
            break;
        }
        if I.op != GIR_INSERTVALUE { break; }
        let io = I.c;
        let it = otype(res(I.b));
        let isz = store_of(it);
        if io == off && it == t { return res(I.b); }
        if io + isz <= off || off + sz <= io {
            v = res(I.a);
            continue;
        }
        // the inserted aggregate holds the field
        if cls_of(it) == C_MEM && io <= off && off + sz <= io + isz {
            let e = new_inst(Inst { op: GIR_EXTRACTVALUE as! u8, sub: 0, flags: 0, ty: t as! u16, aux: 0, a: res(I.b),
                                    b: off - io, c: 0, dbg: o_ins[i].dbg });
            link_before(i, e);
            return e;
        }
        return NIL;
    }
    if v != res(o_ins[i].a) {
        o_ins[i].a = v;
        fold_changed = true;
    }
    return NIL;
}
// (E2) extractelement with a constant lane through a chain of
// insertelements; of a zero constant: zero.
fn simp_extract_elt(i: u32) -> u32 {
    let k0, lane = ci(res(o_ins[i].b));
    if !k0 { return NIL; }
    var v = res(o_ins[i].a);
    var n = 0;
    while n < 64 {
        n++;
        if gir_kind(v) == GIR_V_CONST {
            let C = x_consts[xb_c + gir_idx(v)];
            if C.data == GIR_NONE { return undef_of(o_ins[i].ty); }
            return NIL;
        }
        if !is_inst(v) { return NIL; }
        let I = o_ins[v];
        if I.op != GIR_INSERTELT { break; }
        let k1, l1 = ci(res(I.c));
        if !k1 { break; }
        if l1 == lane { return res(I.b); }
        v = res(I.a);
    }
    if v != res(o_ins[i].a) {
        o_ins[i].a = v;
        fold_changed = true;
    }
    return NIL;
}

// extractvalue (load p), off -> load (p + off), right after the aggregate
// load (the memory is the same there).
fn simp_extract(i: u32) -> u32 {
    let a = res(o_ins[i].a);
    if !is_inst(a) { return NIL; }
    let L = o_ins[a];
    if L.op != GIR_LOAD || L.flags & (IF_VOLATILE | IF_ORD_MASK) != 0 || o_blk[a] == NIL { return NIL; }
    let t: u32 = o_ins[i].ty;
    if cls_of(t) == C_MEM || store_of(t) == 0 { return NIL; }
    var p = res(L.a);
    let off = o_ins[i].b;
    if off != 0 {
        let s = new_run(2);
        o_ops[s] = off;
        o_ops[s + 1] = 0;
        let g = new_inst(Inst { op: GIR_GEP as! u8, sub: 0, flags: 0, ty: GIR_T_PTR, aux: 0, a: p, b: s, c: 0, dbg: L.dbg });
        link_after(a, g);
        p = g;
        let ld = new_inst(Inst { op: GIR_LOAD as! u8, sub: 0, flags: 0, ty: t as! u16, aux: 0, a: p, b: 0, c: 0, dbg: L.dbg });
        link_after(g, ld);
        return ld;
    }
    let ld = new_inst(Inst { op: GIR_LOAD as! u8, sub: 0, flags: 0, ty: t as! u16, aux: 0, a: p, b: 0, c: 0, dbg: L.dbg });
    link_after(a, ld);
    return ld;
}

fn simp_bin(i: u32) -> u32 {
    let I = o_ins[i];
    let op: u32 = I.op;
    let t: u32 = I.ty;
    let bits = bits_of(t);
    let m = wmask(bits);
    var a = I.a;
    var b = I.b;
    var ka, va = ci(a);
    var kb, vb = ci(b);
    if ka && kb {
        let ok, r = fold_bin(op, bits, va, vb);
        if ok { return int_const(t, r); }
        return NIL;
    }
    let comm = op == GIR_ADD || op == GIR_MUL || op == GIR_AND || op == GIR_OR || op == GIR_XOR;
    if comm && ka {
        // constant to the right
        o_ins[i].a = b;
        o_ins[i].b = a;
        a = I.b;
        b = I.a;
        ka = false;
        kb = true;
        vb = va;
        fold_changed = true;
    }
    if kb {
        if vb == 0 {
            if op == GIR_ADD || op == GIR_SUB || op == GIR_OR || op == GIR_XOR || op == GIR_SHL || op == GIR_LSHR
               || op == GIR_ASHR { return a; }
            if op == GIR_MUL || op == GIR_AND { return b; }
        }
        if vb == 1 {
            if op == GIR_MUL || op == GIR_UDIV || op == GIR_SDIV { return a; }
            if op == GIR_UREM || op == GIR_SREM { return int_const(t, 0); }
        }
        if vb == m {
            if op == GIR_AND { return a; }
            if op == GIR_OR { return b; }
        }
        // (x op c1) op c2 for add, and, or, xor, mul
        if is_inst(a) {
            let A = o_ins[a];
            if A.op == op && (op == GIR_ADD || op == GIR_AND || op == GIR_OR || op == GIR_XOR || op == GIR_MUL) {
                let k1, v1 = ci(res(A.b));
                if k1 {
                    let ok, r = fold_bin(op, bits, v1, vb);
                    if ok {
                        o_ins[i].a = res(A.a);
                        o_ins[i].b = int_const(t, r);
                        fold_changed = true;
                        return NIL;
                    }
                }
            }
            // (x - c1) + c2, (x + c1) - c2
            if (A.op == GIR_SUB && op == GIR_ADD || A.op == GIR_ADD && op == GIR_SUB) {
                let k1, v1 = ci(res(A.b));
                if k1 {
                    o_ins[i].a = res(A.a);
                    o_ins[i].b = int_const(t, (vb - v1) & m);
                    fold_changed = true;
                    return NIL;
                }
            }
        }
        // x - c -> x + (-c)
        if op == GIR_SUB {
            o_ins[i].op = GIR_ADD as! u8;
            o_ins[i].b = int_const(t, (0 - vb) & m);
            fold_changed = true;
            return NIL;
        }
        let k = log2p(vb);
        if k != 0 {
            if op == GIR_MUL {
                o_ins[i].op = GIR_SHL as! u8;
                o_ins[i].b = int_const(t, k as u64);
                fold_changed = true;
                return NIL;
            }
            if op == GIR_UDIV {
                o_ins[i].op = GIR_LSHR as! u8;
                o_ins[i].b = int_const(t, k as u64);
                fold_changed = true;
                return NIL;
            }
            if op == GIR_UREM {
                o_ins[i].op = GIR_AND as! u8;
                o_ins[i].b = int_const(t, vb - 1);
                fold_changed = true;
                return NIL;
            }
            if (op == GIR_SDIV || op == GIR_SREM) && k < bits - 1 && (bits == 32 || bits == 64) {
                fold_changed = true;
                return sdiv_pow2(i, op, t, bits, a, k, vb, m);
            }
        }
        // division of an i32 by another constant: a multiplication by its
        // reciprocal (Granlund-Montgomery, Hacker's Delight 10-1)
        if bits == 32 && vb > 1 && log2p(vb) == 0 && (op == GIR_UDIV || op == GIR_UREM) {
            fold_changed = true;
            return udiv_magic(i, op, a, vb);
        }
        if bits == 32 && vb > 1 && vb < 0x80000000 && log2p(vb) == 0 && (op == GIR_SDIV || op == GIR_SREM) {
            fold_changed = true;
            return sdiv_magic(i, op, a, vb);
        }
    }
    if ka && va == 0 {
        if op == GIR_SHL || op == GIR_LSHR || op == GIR_ASHR || op == GIR_UDIV || op == GIR_SDIV
           || op == GIR_UREM || op == GIR_SREM { return a; }
    }
    if ka && va == m && op == GIR_ASHR { return a; }   // (-1 >> x)
    if a == b {
        if op == GIR_SUB || op == GIR_XOR { return int_const(t, 0); }
        if op == GIR_AND || op == GIR_OR { return a; }
    }
    return NIL;
}

// x / 2^k, x % 2^k for signed x: t = x + ((x >>s (bits-1)) >>u (bits-k));
// q = t >>s k; r = x - (t & -2^k).
fn sdiv_pow2(i: u32, op: u32, t: u32, bits: u32, a: u32, k: u32, vb: u64, m: u64) -> u32 {
    let s1 = ins_new(i, GIR_ASHR, t, a, int_const(t, (bits - 1) as u64));
    let s2 = ins_new(i, GIR_LSHR, t, s1, int_const(t, (bits - k) as u64));
    let s3 = ins_new(i, GIR_ADD, t, a, s2);
    if op == GIR_SDIV { return ins_new(i, GIR_ASHR, t, s3, int_const(t, k as u64)); }
    let s4 = ins_new(i, GIR_AND, t, s3, int_const(t, (0 - vb) & m));
    return ins_new(i, GIR_SUB, t, a, s4);
}
fn ins_cast(at: u32, op: u32, ty: u32, x: u32, from: u32) -> u32 {
    let n = new_inst(Inst { op: op as! u8, sub: 0, flags: 0, ty: ty as! u16, aux: from as! u16, a: x, b: 0, c: 0,
                            dbg: o_ins[at].dbg });
    link_before(at, n);
    return n;
}
// x / d, x % d for an unsigned i32 x: with l = ceil(log2 d), m = 2^(32+l)/d + 1,
// q = x * m >> (32 + l) (in 64 bits; when m needs 33 bits, with m - 2^32:
// q = ((x * (m - 2^32) >> 32) + x) >> l).
fn udiv_magic(i: u32, op: u32, a: u32, d: u64) -> u32 {
    let I32: u32 = GIR_T_I32;
    if d >= 0x80000000 {
        // the quotient is 0 or 1
        let c = new_inst(Inst { op: GIR_ICMP as! u8, sub: GIR_UGE as! u8, flags: 0, ty: GIR_T_I1, aux: I32 as! u16,
                                a: a, b: int_const(I32, d), c: 0, dbg: o_ins[i].dbg });
        link_before(i, c);
        let q = ins_cast(i, GIR_ZEXT, I32, c, GIR_T_I1);
        if op == GIR_UDIV { return q; }
        let qd = ins_new(i, GIR_MUL, I32, q, int_const(I32, d));
        return ins_new(i, GIR_SUB, I32, a, qd);
    }
    var l: u32 = 0;
    while ((1 as u64) << l) < d { l++; }
    let m: u64 = ((1 as u64) << (32 + l)) / d + 1;
    let I64: u32 = GIR_T_I64;
    let x = ins_cast(i, GIR_ZEXT, I64, a, I32);
    var q: u32 = 0;
    if m < 0x100000000 {
        let p = ins_new(i, GIR_MUL, I64, x, int_const(I64, m));
        q = ins_new(i, GIR_LSHR, I64, p, int_const(I64, (32 + l) as u64));
    } else {
        let p = ins_new(i, GIR_MUL, I64, x, int_const(I64, m - 0x100000000));
        let h = ins_new(i, GIR_LSHR, I64, p, int_const(I64, 32));
        let t = ins_new(i, GIR_ADD, I64, h, x);
        q = ins_new(i, GIR_LSHR, I64, t, int_const(I64, l as u64));
    }
    let q32 = ins_cast(i, GIR_TRUNC, I32, q, I64);
    if op == GIR_UDIV { return q32; }
    let qd = ins_new(i, GIR_MUL, I32, q32, int_const(I32, d));
    return ins_new(i, GIR_SUB, I32, a, qd);
}
// x / d, x % d for a signed i32 x and 2 <= d < 2^31 (Hacker's Delight, figure
// 10-1): q = (mulhs(M, x) [+ x if M < 0]) >>s s, plus 1 if negative.
fn sdiv_magic(i: u32, op: u32, a: u32, d: u64) -> u32 {
    let two31: u64 = 0x80000000;
    let ad = d;
    let anc: u64 = two31 - 1 - two31 % ad;
    var p: u32 = 31;
    var q1: u64 = two31 / anc;
    var r1: u64 = two31 - q1 * anc;
    var q2: u64 = two31 / ad;
    var r2: u64 = two31 - q2 * ad;
    loop {
        p++;
        q1 = (2 * q1) & 0xFFFFFFFF;
        r1 = (2 * r1) & 0xFFFFFFFF;
        if r1 >= anc {
            q1 = (q1 + 1) & 0xFFFFFFFF;
            r1 = (r1 - anc) & 0xFFFFFFFF;
        }
        q2 = (2 * q2) & 0xFFFFFFFF;
        r2 = (2 * r2) & 0xFFFFFFFF;
        if r2 >= ad {
            q2 = (q2 + 1) & 0xFFFFFFFF;
            r2 = (r2 - ad) & 0xFFFFFFFF;
        }
        let delta = (ad - r2) & 0xFFFFFFFF;
        if !(q1 < delta || q1 == delta && r1 == 0) { break; }
    }
    let mm: u64 = (q2 + 1) & 0xFFFFFFFF;   // M as an i32 bit pattern
    let sh: u32 = p - 32;
    let I64: u32 = GIR_T_I64;
    let I32: u32 = GIR_T_I32;
    let x = ins_cast(i, GIR_SEXT, I64, a, I32);
    let mm64: u64 = sx(mm, 32) as! u64;
    let pr = ins_new(i, GIR_MUL, I64, x, int_const(I64, mm64));
    let h = ins_new(i, GIR_ASHR, I64, pr, int_const(I64, 32));
    var t = ins_cast(i, GIR_TRUNC, I32, h, I64);
    if mm >= two31 { t = ins_new(i, GIR_ADD, I32, t, a); }
    if sh != 0 { t = ins_new(i, GIR_ASHR, I32, t, int_const(I32, sh as u64)); }
    let u = ins_new(i, GIR_LSHR, I32, t, int_const(I32, 31));
    let q = ins_new(i, GIR_ADD, I32, t, u);
    if op == GIR_SDIV { return q; }
    let qd = ins_new(i, GIR_MUL, I32, q, int_const(I32, d));
    return ins_new(i, GIR_SUB, I32, a, qd);
}

fn simp_icmp(i: u32) -> u32 {
    let I = o_ins[i];
    let t: u32 = I.aux;
    if !int_ty(t) || bits_of(t) > 64 { return NIL; }
    let bits = bits_of(t);
    var p: u32 = I.sub;
    var a = I.a;
    var b = I.b;
    var ka, va = ci(a);
    var kb, vb = ci(b);
    if ka && kb { return bool_c(fold_icmp(p, bits, va, vb)); }
    if a == b {
        return bool_c(p == GIR_EQ || p == GIR_UGE || p == GIR_ULE || p == GIR_SGE || p == GIR_SLE);
    }
    if ka {
        // constant to the right
        p = swp_pred(p);
        o_ins[i].sub = p as! u8;
        o_ins[i].a = b;
        o_ins[i].b = a;
        a = I.b;
        b = I.a;
        kb = true;
        vb = va;
        fold_changed = true;
    }
    if kb {
        let m = wmask(bits);
        // unsigned extremes
        if vb == 0 {
            if p == GIR_ULT { return bool_c(false); }
            if p == GIR_UGE { return bool_c(true); }
        }
        if vb == m {
            if p == GIR_UGT { return bool_c(false); }
            if p == GIR_ULE { return bool_c(true); }
        }
        // (E2) the compares that one value decides become equalities:
        // x <u MAX -> x != MAX, x >u 0 -> x != 0, x >=u MAX -> x == MAX,
        // x <=u 0 -> x == 0, and the signed extremes likewise
        let smax: u64 = m >> 1;
        let smin: u64 = smax + 1;
        var np: u32 = NIL;
        if p == GIR_ULT && vb == m || p == GIR_UGT && vb == 0 || p == GIR_SLT && vb == smax || p == GIR_SGT && vb == smin {
            np = GIR_NE;
        } else if p == GIR_UGE && vb == m || p == GIR_ULE && vb == 0 || p == GIR_SGE && vb == smax || p == GIR_SLE && vb == smin {
            np = GIR_EQ;
        } else if p == GIR_SLT && vb == smin || p == GIR_SGT && vb == smax {
            return bool_c(false);
        } else if p == GIR_SGE && vb == smin || p == GIR_SLE && vb == smax {
            return bool_c(true);
        }
        if np != NIL {
            o_ins[i].sub = np as! u8;
            p = np;
            fold_changed = true;
        }
        if is_inst(a) {
            let A = o_ins[a];
            // (zext i1 x) ==/!= c
            if A.op == GIR_ZEXT && A.aux == GIR_T_I1 && (p == GIR_EQ || p == GIR_NE) {
                let x = res(A.a);
                if vb > 1 { return bool_c(p == GIR_NE); }
                let keep = (vb == 1) == (p == GIR_EQ);   // the result is x itself
                if keep { return x; }
                return bool_not(i, x);
            }
            // (zext x) cmp c / (sext x) cmp c with c in x's range
            if (A.op == GIR_ZEXT || A.op == GIR_SEXT) && int_ty(A.aux) && A.aux != GIR_T_I1 {
                let sb: u32 = bits_of(A.aux);
                let sm = wmask(sb);
                var fits = false;
                if A.op == GIR_ZEXT { fits = vb <= sm && (p == GIR_EQ || p == GIR_NE || p <= GIR_ULE); }
                else { fits = sx(vb, bits) == sx(vb & sm, sb) && (p == GIR_EQ || p == GIR_NE || p >= GIR_SGT); }
                if fits {
                    o_ins[i].aux = A.aux;
                    o_ins[i].a = res(A.a);
                    o_ins[i].b = int_const(A.aux, vb & sm);
                    fold_changed = true;
                    return NIL;
                }
            }
            // (x ^ c1) ==/!= c2 -> x ==/!= c1 ^ c2; (x + c1) ==/!= c2 -> x ==/!= c2 - c1
            if (A.op == GIR_XOR || A.op == GIR_ADD) && (p == GIR_EQ || p == GIR_NE) {
                let k1, v1 = ci(res(A.b));
                if k1 {
                    o_ins[i].a = res(A.a);
                    o_ins[i].b = int_const(t, if A.op == GIR_XOR { v1 ^ vb } else { (vb - v1) & m });
                    fold_changed = true;
                    return NIL;
                }
            }
        }
    }
    // (zext x) cmp (zext y), (sext x) cmp (sext y) of one source type
    if is_inst(a) && is_inst(b) {
        let A = o_ins[a];
        let B = o_ins[b];
        if A.op == B.op && A.aux == B.aux && (A.op == GIR_ZEXT && (p <= GIR_ULE) || A.op == GIR_SEXT) {
            o_ins[i].aux = A.aux;
            o_ins[i].a = res(A.a);
            o_ins[i].b = res(B.a);
            fold_changed = true;
            return NIL;
        }
    }
    return NIL;
}
// The negation of i1 value x, as a new instruction before `at` (an inverted
// compare if x is a compare).
fn bool_not(at: u32, x: u32) -> u32 {
    if is_inst(x) && o_ins[x].op == GIR_ICMP {
        var X = o_ins[x];
        X.sub = inv_pred(X.sub) as! u8;
        X.dbg = o_ins[at].dbg;
        let n = new_inst(X);
        link_before(at, n);
        return n;
    }
    return ins_new(at, GIR_XOR, GIR_T_I1, x, bool_c(true));
}

fn simp_select(i: u32) -> u32 {
    let c = res(o_ins[i].a);
    let x = res(o_ins[i].b);
    let y = res(o_ins[i].c);
    o_ins[i].a = c;
    o_ins[i].b = x;
    o_ins[i].c = y;
    if x == y { return x; }
    let kc, vc = ci(c);
    if kc && otype(c) == GIR_T_I1 { return if vc != 0 { x } else { y }; }
    if o_ins[i].ty == GIR_T_I1 && otype(c) == GIR_T_I1 {
        let kx, vx = ci(x);
        let ky, vy = ci(y);
        if kx && ky {
            if vx == 1 && vy == 0 { return c; }
            if vx == 0 && vy == 1 { return bool_not(i, c); }
        }
    }
    return NIL;
}

fn simp_cast(i: u32) -> u32 {
    let I = o_ins[i];
    let op: u32 = I.op;
    let t: u32 = I.ty;
    let st: u32 = I.aux;
    let a = I.a;
    if op == GIR_BITCAST && t == st { return a; }
    if !int_ty(t) || !int_ty(st) || bits_of(t) > 64 || bits_of(st) > 64 { return NIL; }
    let db = bits_of(t);
    let sb = bits_of(st);
    let k, v = ci(a);
    if k {
        if op == GIR_ZEXT || op == GIR_TRUNC || op == GIR_PTRTOINT || op == GIR_INTTOPTR || op == GIR_BITCAST {
            return int_const(t, v);
        }
        if op == GIR_SEXT { return int_const(t, sx(v, sb) as! u64); }
        return NIL;
    }
    if (op == GIR_PTRTOINT || op == GIR_INTTOPTR || op == GIR_BITCAST) && db == sb && is_inst(a) {
        let A = o_ins[a];
        // inttoptr (ptrtoint p) -> p (64-bit both ways)
        if (A.op == GIR_PTRTOINT || A.op == GIR_INTTOPTR || A.op == GIR_BITCAST) && A.aux == t
           && bits_of(A.ty) == db { return res(A.a); }
        return NIL;
    }
    if !is_inst(a) { return NIL; }
    let A = o_ins[a];
    let x = res(A.a);
    if (A.op == GIR_ZEXT || A.op == GIR_SEXT) && int_ty(A.aux) {
        let xb: u32 = bits_of(A.aux);
        if op == GIR_ZEXT && A.op == GIR_ZEXT || op == GIR_SEXT && A.op == GIR_SEXT || op == GIR_SEXT && A.op == GIR_ZEXT {
            // ext (ext x) -> ext x (zext of a zext is a zext)
            o_ins[i].op = A.op;
            o_ins[i].aux = A.aux;
            o_ins[i].a = x;
            fold_changed = true;
            return NIL;
        }
        if op == GIR_TRUNC {
            if A.aux == t { return x; }
            if db < xb {
                o_ins[i].aux = A.aux;
                o_ins[i].a = x;
                fold_changed = true;
                return NIL;
            }
            // trunc (ext x) wider than x: ext x
            o_ins[i].op = A.op;
            o_ins[i].aux = A.aux;
            o_ins[i].a = x;
            fold_changed = true;
            return NIL;
        }
    }
    if op == GIR_TRUNC && A.op == GIR_TRUNC {
        o_ins[i].aux = A.aux;
        o_ins[i].a = x;
        fold_changed = true;
        return NIL;
    }
    return NIL;
}

// GEP: constant indices into the offset, no terms and offset 0 -> the base,
// a GEP of a GEP merged.
fn simp_gep(i: u32) -> u32 {
    let I = o_ins[i];
    let s = I.b;
    var base = res(I.a);
    o_ins[i].a = base;
    var off: u64 = o_ops[s] as u64 | (o_ops[s + 1] as u64 << 32);
    // fold constant terms
    var n: u32 = 0;
    var folded = false;
    for k in 0..I.c {
        let x = res(o_ops[s + 2 + 2 * k]);
        let sc = o_ops[s + 3 + 2 * k];
        let kx, vx = ci(x);
        if kx {
            off += (sx(vx, bits_of(otype(x))) as! u64) * (sc as u64);
            folded = true;
            continue;
        }
        o_ops[s + 2 + 2 * n] = x;
        o_ops[s + 3 + 2 * n] = sc;
        n++;
    }
    if folded {
        o_ops[s] = (off & 0xFFFFFFFF) as! u32;
        o_ops[s + 1] = (off >> 32) as! u32;
        o_ins[i].c = n;
        fold_changed = true;
    }
    if n == 0 && off == 0 { return base; }
    // a scale an address mode cannot take (not 1, 2, 4, 8): the index times the
    // scale as an instruction of its own (then common to the GEPs that share it)
    for k in 0..n {
        let sc = o_ops[s + 3 + 2 * k];
        if sc == 1 || sc == 2 || sc == 4 || sc == 8 || sc == 0 { continue; }
        var x = o_ops[s + 2 + 2 * k];
        let xt = otype(x);
        if !int_ty(xt) || bits_of(xt) > 64 { continue; }
        if bits_of(xt) < 64 {
            let e = new_inst(Inst { op: GIR_SEXT as! u8, sub: 0, flags: 0, ty: GIR_T_I64, aux: xt as! u16, a: x, b: 0, c: 0,
                                    dbg: o_ins[i].dbg });
            link_before(i, e);
            x = e;
        }
        let lg = log2p(sc as u64);
        var m: u32 = 0;
        if lg != 0 { m = ins_new(i, GIR_SHL, GIR_T_I64, x, int_const(GIR_T_I64, lg as u64)); }
        else { m = ins_new(i, GIR_MUL, GIR_T_I64, x, int_const(GIR_T_I64, sc as u64)); }
        o_ops[s + 2 + 2 * k] = m;
        o_ops[s + 3 + 2 * k] = 1;
        fold_changed = true;
    }
    // a GEP of a GEP: one GEP (the inner one's terms first)
    if is_inst(base) && o_ins[base].op == GIR_GEP {
        let B = o_ins[base];
        let bs = B.b;
        let bn = B.c;
        // (only when one of them has no index terms: the back-end folds a GEP
        // into each load and store, so terms would be computed again per use,
        // and an address of many terms needs as many registers at once)
        if (bn == 0 || n == 0) && bn + n <= 2 {
            let boff: u64 = o_ops[bs] as u64 | (o_ops[bs + 1] as u64 << 32);
            let tot = off + boff;
            let ns = new_run(2 + 2 * (bn + n));
            o_ops[ns] = (tot & 0xFFFFFFFF) as! u32;
            o_ops[ns + 1] = (tot >> 32) as! u32;
            for k in 0..bn {
                o_ops[ns + 2 + 2 * k] = res(o_ops[bs + 2 + 2 * k]);
                o_ops[ns + 3 + 2 * k] = o_ops[bs + 3 + 2 * k];
            }
            for k in 0..n {
                o_ops[ns + 2 + 2 * (bn + k)] = o_ops[s + 2 + 2 * k];
                o_ops[ns + 3 + 2 * (bn + k)] = o_ops[s + 3 + 2 * k];
            }
            o_ins[i].a = res(B.a);
            o_ins[i].b = ns;
            o_ins[i].c = bn + n;
            fold_changed = true;
        }
    }
    return NIL;
}
