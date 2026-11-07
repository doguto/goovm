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
    return NIL;
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
                // t = x + ((x >>s (bits-1)) >>u (bits-k)); q = t >>s k; r = x - (t & -2^k)
                let s1 = ins_new(i, GIR_ASHR, t, a, int_const(t, (bits - 1) as u64));
                let s2 = ins_new(i, GIR_LSHR, t, s1, int_const(t, (bits - k) as u64));
                let s3 = ins_new(i, GIR_ADD, t, a, s2);
                if op == GIR_SDIV {
                    o_ins[i].op = GIR_ASHR as! u8;
                    o_ins[i].a = s3;
                    o_ins[i].b = int_const(t, k as u64);
                } else {
                    let s4 = ins_new(i, GIR_AND, t, s3, int_const(t, (0 - vb) & m));
                    o_ins[i].op = GIR_SUB as! u8;
                    o_ins[i].a = a;
                    o_ins[i].b = s4;
                }
                fold_changed = true;
                return NIL;
            }
        }
    }
    if ka && va == 0 {
        if op == GIR_SHL || op == GIR_LSHR || op == GIR_ASHR || op == GIR_UDIV || op == GIR_SDIV
           || op == GIR_UREM || op == GIR_SREM { return a; }
    }
    if a == b {
        if op == GIR_SUB || op == GIR_XOR { return int_const(t, 0); }
        if op == GIR_AND || op == GIR_OR { return a; }
    }
    return NIL;
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
    // a GEP of a GEP: one GEP (the inner one's terms first)
    if is_inst(base) && o_ins[base].op == GIR_GEP {
        let B = o_ins[base];
        let bs = B.b;
        let bn = B.c;
        if bn + n <= 4 {
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
