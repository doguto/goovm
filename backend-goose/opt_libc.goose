// Library call simplification (milestone E2; LLVM's SimplifyLibCalls) on
// the OIR (opt.goose, called from the simplifier): calls of the C library's
// string and memory functions whose arguments are constant strings (bytes
// of read-only globals) or constant sizes are folded or turned into cheaper
// operations, as LLVM does at -O1 and above:
//   strlen, strnlen          constant length (of a select of two constants:
//                            a select of the lengths)
//   strcmp, strncmp, memcmp, bcmp   constant result; against "" a byte load
//   strchr, strrchr, memchr, strstr, strpbrk   a constant pointer or null
//   strspn, strcspn          constant
//   strcpy, stpcpy, strncpy  inline copies of the constant (GIR_MEMCPY,
//                            GIR_MEMSET)
//   strcat, strncat          strlen of the destination and an inline copy
//   sprintf, snprintf        format without conversions, or "%s" of a
//                            constant: an inline copy, constant result
//   memcpy, memmove, memset  of constant size: GIR_MEMCPY / GIR_MEMSET
//                            (memmove when the operands cannot overlap)
//   __memcpy_chk ... __snprintf_chk   the unchecked call when the object
//                            size is unknown (-1) or large enough
//   printf("%s\n", s), printf("c") / printf("%c", c)   puts / putchar
// Calls marked nobuiltin (-fno-builtin) are left alone. A call that needs a
// function the module does not declare is left alone too (the exporter
// declares the usual companions at opt_level >= 1: strlen, memcpy, puts,
// putchar, ...).

let LB_STRLEN: u32 = 1;
let LB_STRNLEN: u32 = 2;
let LB_STRCMP: u32 = 3;
let LB_STRNCMP: u32 = 4;
let LB_MEMCMP: u32 = 5;
let LB_BCMP: u32 = 6;
let LB_STRCHR: u32 = 7;
let LB_STRRCHR: u32 = 8;
let LB_MEMCHR: u32 = 9;
let LB_STRSTR: u32 = 10;
let LB_STRPBRK: u32 = 11;
let LB_STRSPN: u32 = 12;
let LB_STRCSPN: u32 = 13;
let LB_STRCPY: u32 = 14;
let LB_STPCPY: u32 = 15;
let LB_STRNCPY: u32 = 16;
let LB_STRCAT: u32 = 17;
let LB_STRNCAT: u32 = 18;
let LB_SPRINTF: u32 = 19;
let LB_SNPRINTF: u32 = 20;
let LB_MEMCPY: u32 = 21;
let LB_MEMMOVE: u32 = 22;
let LB_MEMSET: u32 = 23;
let LB_MEMCPY_CHK: u32 = 24;
let LB_MEMMOVE_CHK: u32 = 25;
let LB_MEMSET_CHK: u32 = 26;
let LB_STRCPY_CHK: u32 = 27;
let LB_STPCPY_CHK: u32 = 28;
let LB_STRCAT_CHK: u32 = 29;
let LB_SNPRINTF_CHK: u32 = 30;
let LB_SPRINTF_CHK: u32 = 31;
let LB_VSNPRINTF_CHK: u32 = 32;
let LB_VSPRINTF_CHK: u32 = 33;
let LB_VSNPRINTF: u32 = 34;
let LB_VSPRINTF: u32 = 35;
let LB_PRINTF: u32 = 36;
let LB_PUTS: u32 = 37;
let LB_PUTCHAR: u32 = 38;
let LB_STRNCPY_CHK: u32 = 39;
let LB_STRNCAT_CHK: u32 = 40;
let LB_MEMPCPY: u32 = 41;
let LB_FLOOR: u32 = 42;          // floor .. nearbyint, then their float versions (+6)
let LB_CEIL: u32 = 43;
let LB_TRUNC: u32 = 44;
let LB_ROUND: u32 = 45;
let LB_RINT: u32 = 46;
let LB_NEARBYINT: u32 = 47;
// (allocation functions, for GIR_OBJSIZE: LLVM's MemoryBuiltins table)
let LB_MALLOC: u32 = 54;         // malloc, valloc, operator new (n)
let LB_CALLOC: u32 = 55;         // calloc (n, m)
let LB_REALLOC: u32 = 56;        // realloc, reallocf (p, n)
let LB_ALIGNED: u32 = 57;        // aligned_alloc, memalign (a, n)
let LB_BCOPY: u32 = 58;
let LB_N: u32 = 59;

var lb_kind: u8[>..] = [];      // per global: LB_*, 0
var lb_sym: u32[>..] = [];      // per LB_*: a global of that name, NIL
var lb_on = false;

fn lb_name(nm: const u8[:]) -> u32 {
    if nm == "strlen" { return LB_STRLEN; }
    if nm == "strnlen" { return LB_STRNLEN; }
    if nm == "strcmp" { return LB_STRCMP; }
    if nm == "strncmp" { return LB_STRNCMP; }
    if nm == "memcmp" { return LB_MEMCMP; }
    if nm == "bcmp" { return LB_BCMP; }
    if nm == "strchr" { return LB_STRCHR; }
    if nm == "strrchr" { return LB_STRRCHR; }
    if nm == "memchr" { return LB_MEMCHR; }
    if nm == "strstr" { return LB_STRSTR; }
    if nm == "strpbrk" { return LB_STRPBRK; }
    if nm == "strspn" { return LB_STRSPN; }
    if nm == "strcspn" { return LB_STRCSPN; }
    if nm == "strcpy" { return LB_STRCPY; }
    if nm == "stpcpy" { return LB_STPCPY; }
    if nm == "strncpy" { return LB_STRNCPY; }
    if nm == "strcat" { return LB_STRCAT; }
    if nm == "strncat" { return LB_STRNCAT; }
    if nm == "sprintf" { return LB_SPRINTF; }
    if nm == "snprintf" { return LB_SNPRINTF; }
    if nm == "memcpy" { return LB_MEMCPY; }
    if nm == "memmove" { return LB_MEMMOVE; }
    if nm == "memset" { return LB_MEMSET; }
    if nm == "__memcpy_chk" { return LB_MEMCPY_CHK; }
    if nm == "__memmove_chk" { return LB_MEMMOVE_CHK; }
    if nm == "__memset_chk" { return LB_MEMSET_CHK; }
    if nm == "__strcpy_chk" { return LB_STRCPY_CHK; }
    if nm == "__stpcpy_chk" { return LB_STPCPY_CHK; }
    if nm == "__strcat_chk" { return LB_STRCAT_CHK; }
    if nm == "__snprintf_chk" { return LB_SNPRINTF_CHK; }
    if nm == "__sprintf_chk" { return LB_SPRINTF_CHK; }
    if nm == "__vsnprintf_chk" { return LB_VSNPRINTF_CHK; }
    if nm == "__vsprintf_chk" { return LB_VSPRINTF_CHK; }
    if nm == "vsnprintf" { return LB_VSNPRINTF; }
    if nm == "vsprintf" { return LB_VSPRINTF; }
    if nm == "printf" { return LB_PRINTF; }
    if nm == "puts" { return LB_PUTS; }
    if nm == "putchar" { return LB_PUTCHAR; }
    if nm == "__strncpy_chk" { return LB_STRNCPY_CHK; }
    if nm == "__strncat_chk" { return LB_STRNCAT_CHK; }
    if nm == "mempcpy" { return LB_MEMPCPY; }
    if nm == "floor" { return LB_FLOOR; }
    if nm == "ceil" { return LB_CEIL; }
    if nm == "trunc" { return LB_TRUNC; }
    if nm == "round" { return LB_ROUND; }
    if nm == "rint" { return LB_RINT; }
    if nm == "nearbyint" { return LB_NEARBYINT; }
    if nm == "floorf" { return LB_FLOOR + 6; }
    if nm == "ceilf" { return LB_CEIL + 6; }
    if nm == "truncf" { return LB_TRUNC + 6; }
    if nm == "roundf" { return LB_ROUND + 6; }
    if nm == "rintf" { return LB_RINT + 6; }
    if nm == "nearbyintf" { return LB_NEARBYINT + 6; }
    if nm == "malloc" || nm == "valloc" || nm == "_Znwm" || nm == "_Znam" || nm == "_ZnwmRKSt9nothrow_t" ||
       nm == "_ZnamRKSt9nothrow_t" || nm == "_ZnwmSt11align_val_t" || nm == "_ZnamSt11align_val_t" ||
       nm == "_ZnwmSt11align_val_tRKSt9nothrow_t" || nm == "_ZnamSt11align_val_tRKSt9nothrow_t" {
        return LB_MALLOC;
    }
    if nm == "calloc" { return LB_CALLOC; }
    if nm == "bcopy" { return LB_BCOPY; }
    if nm == "realloc" || nm == "reallocf" { return LB_REALLOC; }
    if nm == "aligned_alloc" || nm == "memalign" { return LB_ALIGNED; }
    return 0;
}

fn lb_init() {
    lb_dr_on = false;
    lb_kind.clear();
    lb_sym.clear();
    lb_sym.resize(LB_N, NIL);
    lb_on = M.header[0].r1 == GIR_TARGET_X86_64 || true;
    for G, g in M.globals {
        var k: u32 = 0;
        if G.kind == G_FUNC && G.flags & GF_INTERNAL == 0 {
            k = lb_name(M.strtab[G.name..G.name + G.name_len]);
        }
        lb_kind.push(k as! u8);
        if k != 0 && lb_sym[k] == NIL { lb_sym[k] = g as! u32; }
    }
}

// ------------------------------------------------------- constant bytes
// A pointer into read-only data: (ok, data index of the byte, bytes left in
// the object).
fn lb_ptr(p: u32) -> bool, i64, i64 {
    let b, off, known = aa_decompose(p);
    if !known || off < 0 || gir_kind(b) != GIR_V_GLOBAL { return false, 0, 0; }
    let G = M.globals[gir_idx(b)];
    if G.kind != G_VAR || G.flags & (GF_CONST | GF_DEFINED) != (GF_CONST | GF_DEFINED) { return false, 0, 0; }
    if G.flags & (GF_WEAK | GF_RELOCS | GF_TLS | GF_COMMON) != 0 { return false, 0, 0; }
    if off >= G.size as i64 { return false, 0, 0; }
    if G.flags & GF_ZERO != 0 { return true, -1, G.size as i64 - off; }
    return true, G.data as i64 + off, G.size as i64 - off;
}
// The length of the string at p when it is known: a constant string, or
// selects and PHIs of strings of one length (LLVM's GetStringLength).
var lb_budget: u32 = 0;
recursive fn lb_slen(p0: u32, depth: u32) -> bool, i64 {
    if depth == 0 { lb_budget = 512; }
    if lb_budget == 0 { return false, 0; }
    lb_budget--;
    let p = res(p0);
    let ok, d, n = lb_str(p);
    if ok { return true, n; }
    if depth >= 64 || !is_inst(p) { return false, 0; }
    let I = o_ins[p];
    if I.op == GIR_SELECT {
        let ka, la = lb_slen(I.b, depth + 1);
        if !ka { return false, 0; }
        let kb, lb = lb_slen(I.c, depth + 1);
        if !kb || la != lb { return false, 0; }
        return true, la;
    }
    if I.op == GIR_PHI {
        var first = true;
        var l: i64 = 0;
        for q in 0..I.c {
            let v = res(o_ops[I.b + 2 * q]);
            if v == p { continue; }
            let kv, lv = lb_slen(v, depth + 1);
            if !kv || !first && lv != l { return false, 0; }
            l = lv;
            first = false;
        }
        return !first, l;
    }
    return false, 0;
}
// (E2) Loads from constant variables (LLVM's ConstantFoldLoadFromConstPtr):
// the bytes of the initializer as an integer, FP or vector constant; a
// pointer that a data relocation puts there: the target (plus the addend).
var lb_dr_start: u32[>..] = [];   // per global: its first data relocation in lb_dr (counting sort)
var lb_dr: u32[>..] = [];
var lb_dr_on = false;
var lb_dr_fill: u32[>..] = [];
fn lb_dr_index() {
    lb_dr_on = true;
    lb_dr_start.clear();
    lb_dr_start.resize(M.globals.len + 1, 0);
    for d in M.drelocs { if d.owner < M.globals.len as! u32 { lb_dr_start[d.owner + 1]++; } }
    for g in 0..M.globals.len { lb_dr_start[g + 1] += lb_dr_start[g]; }
    lb_dr.clear();
    lb_dr.resize(M.drelocs.len, 0);
    lb_dr_fill.clear();
    lb_dr_fill.append(lb_dr_start[..M.globals.len]);
    for d, k in M.drelocs {
        if d.owner >= M.globals.len as! u32 { continue; }
        lb_dr[lb_dr_fill[d.owner]] = k as! u32;
        lb_dr_fill[d.owner]++;
    }
}
fn simp_load_const(i: u32) -> u32 {
    let I = o_ins[i];
    if I.flags & (IF_VOLATILE | IF_ORD_MASK) != 0 { return NIL; }
    let t: u32 = I.ty;
    let sz: i64 = store_of(t) as i64;
    let cl = cls_of(t);
    if sz == 0 || sz > 16 || cl != C_INT && cl != C_FP && cl != C_VEC || sz > 8 && cl != C_VEC { return NIL; }
    let b, off, known = aa_decompose(I.a);
    if !known || off < 0 || gir_kind(b) != GIR_V_GLOBAL { return NIL; }
    let g = gir_idx(b);
    let G = M.globals[g];
    if G.kind != G_VAR || G.flags & (GF_CONST | GF_DEFINED) != (GF_CONST | GF_DEFINED) { return NIL; }
    if G.flags & (GF_WEAK | GF_TLS | GF_COMMON) != 0 || off + sz > G.size as i64 { return NIL; }
    if G.flags & GF_RELOCS != 0 {
        if !lb_dr_on { lb_dr_index(); }
        for q in lb_dr_start[g]..lb_dr_start[g + 1] {
            let d = M.drelocs[lb_dr[q]];
            let lo = d.offset as i64;
            let w: i64 = if d.kind == DR_ABS64 { 8 } else { 4 };
            if lo + w <= off || lo >= off + sz { continue; }
            // a pointer exactly there: the target
            if d.kind != DR_ABS64 || lo != off || t != GIR_T_PTR || d.target >= M.globals.len as! u32 { return NIL; }
            if M.globals[d.target].kind == G_FUNC && d.blk != 0 { return NIL; }
            return lb_gep(i, GIR_V_GLOBAL << 30 | d.target, d.addend);
        }
    }
    var bytes: u8[16] = [0; 16];
    if G.flags & GF_ZERO == 0 {
        for q in 0..sz { bytes[q] = M.data[G.data as i64 + off + q]; }
    }
    if cl == C_VEC { return vec_const(t, bytes[..sz]); }
    var v: u64 = 0;
    var q = sz;
    while q > 0 {
        q--;
        v = (v << 8) | bytes[q] as u64;
    }
    if t == GIR_T_PTR {
        if v != 0 { return NIL; }
        return lb_null();
    }
    if cl == C_FP { return mk_const(t, v, 0); }
    return int_const(t, v);
}

// The byte at data index d + k (d = -1: a zero object).
inline fn lb_byte(d: i64, k: i64) -> u8 {
    if d < 0 { return 0; }
    return M.data[d + k];
}
// A constant C string: (ok, data index, length without the NUL).
fn lb_str(p: u32) -> bool, i64, i64 {
    let ok, d, n = lb_ptr(p);
    if !ok { return false, 0, 0; }
    var k: i64 = 0;
    while k < n {
        if lb_byte(d, k) == 0 { return true, d, k; }
        k++;
    }
    return false, 0, 0;
}

// ------------------------------------------------------- building
fn lb_call(at: u32, k: u32, ty: u32, a0: u32, a1: u32, a2: u32, n: u32) -> u32 {
    let g = lb_sym[k];
    if g == NIL { return NIL; }
    let s = new_run(2 * n);
    o_ops[s] = a0;
    o_ops[s + 1] = 0;
    if n > 1 { o_ops[s + 2] = a1; o_ops[s + 3] = 0; }
    if n > 2 { o_ops[s + 4] = a2; o_ops[s + 5] = 0; }
    let c = new_inst(Inst { op: GIR_CALL as! u8, sub: 0, flags: 0, ty: ty as! u16, aux: 0, a: GIR_V_GLOBAL << 30 | g,
                            b: s, c: n, dbg: o_ins[at].dbg });
    link_before(at, c);
    return c;
}
fn lb_gep(at: u32, p: u32, off: i64) -> u32 {
    if off == 0 { return p; }
    let s = new_run(2);
    let uo = off as! u64;
    o_ops[s] = (uo & 0xFFFFFFFF) as! u32;
    o_ops[s + 1] = (uo >> 32) as! u32;
    let g = new_inst(Inst { op: GIR_GEP as! u8, sub: 0, flags: 0, ty: GIR_T_PTR, aux: 0, a: p, b: s, c: 0,
                            dbg: o_ins[at].dbg });
    link_before(at, g);
    return g;
}
fn lb_memcpy(at: u32, d: u32, s: u32, n: i64) {
    if n <= 0 { return; }
    let x = new_inst(Inst { op: GIR_MEMCPY as! u8, sub: 0, flags: 0, ty: GIR_T_VOID, aux: 0, a: d, b: s,
                            c: n as! u32, dbg: o_ins[at].dbg });
    link_before(at, x);
}
fn lb_memset(at: u32, d: u32, v: u32, n: i64) {
    if n <= 0 { return; }
    let x = new_inst(Inst { op: GIR_MEMSET as! u8, sub: 0, flags: 0, ty: GIR_T_VOID, aux: 0, a: d, b: v,
                            c: n as! u32, dbg: o_ins[at].dbg });
    link_before(at, x);
}
fn lb_zext8(at: u32, p: u32, t: u32) -> u32 {
    let l = new_inst(Inst { op: GIR_LOAD as! u8, sub: 0, flags: 0, ty: GIR_T_I8, aux: 0, a: p, b: 0, c: 0,
                            dbg: o_ins[at].dbg });
    link_before(at, l);
    let z = new_inst(Inst { op: GIR_ZEXT as! u8, sub: 0, flags: 0, ty: t as! u16, aux: GIR_T_I8, a: l, b: 0, c: 0,
                            dbg: o_ins[at].dbg });
    link_before(at, z);
    return z;
}
inline fn lb_arg(I: Inst, k: u32) -> u32 { res(o_ops[I.b + 2 * k]) }
fn lb_null() -> u32 { mk_const(GIR_T_PTR, 0, 0) }

// strlen of p: a constant, a select of constants, or NIL.
recursive fn lb_strlen_of(at: u32, p: u32, t: u32, depth: u32) -> u32 {
    let ok, n = lb_slen(p, 0);
    if ok { return int_const(t, n as! u64); }
    if depth < 3 && is_inst(p) && o_ins[p].op == GIR_SELECT {
        let S = o_ins[p];
        let x = lb_strlen_of(at, res(S.b), t, depth + 1);
        if x == NIL { return NIL; }
        let y = lb_strlen_of(at, res(S.c), t, depth + 1);
        if y == NIL { return NIL; }
        let sel = new_inst(Inst { op: GIR_SELECT as! u8, sub: 0, flags: 0, ty: t as! u16, aux: 0, a: res(S.a), b: x, c: y,
                                  dbg: o_ins[at].dbg });
        link_before(at, sel);
        return sel;
    }
    return NIL;
}
// Compares n bytes (n < 0: up to the NUL) of two constants: -1, 0, 1 as
// strcmp/memcmp return (C: the difference of unsigned chars; LLVM folds to
// the sign).
fn lb_cmp(da: i64, la: i64, db: i64, lb: i64, n: i64, nul: bool) -> i64 {
    var k: i64 = 0;
    loop {
        if n >= 0 && k >= n { return 0; }
        let ca: i64 = if k < la { lb_byte(da, k) as i64 } else { 0 };
        let cb: i64 = if k < lb { lb_byte(db, k) as i64 } else { 0 };
        if ca != cb { return if ca < cb { -1 } else { 1 }; }
        if nul && ca == 0 { return 0; }
        k++;
    }
    return 0;
}

// An upper bound of integer value v (unsigned; all ones: unknown), from its
// constants, masks, or-ed constants and zero extensions.
recursive fn umax_of(v0: u32, depth: u32) -> u64 {
    let v = res(v0);
    let k, x = ci(v);
    if k { return x; }
    if !is_inst(v) || depth > 6 { return 0xFFFFFFFFFFFFFFFF; }
    let I = o_ins[v];
    let m = wmask(bits_of(I.ty));
    if I.op == GIR_AND {
        let a = umax_of(I.a, depth + 1);
        let b = umax_of(I.b, depth + 1);
        return if a < b { a } else { b };
    }
    if I.op == GIR_OR || I.op == GIR_XOR {
        let a = umax_of(I.a, depth + 1);
        let b = umax_of(I.b, depth + 1);
        if a == 0xFFFFFFFFFFFFFFFF || b == 0xFFFFFFFFFFFFFFFF { return m; }
        // (the bits up to the highest set bit of either)
        var x2 = a | b;
        var r: u64 = 0;
        while x2 != 0 { r = (r << 1) | 1; x2 >>= 1; }
        return r & m;
    }
    if I.op == GIR_ZEXT { let a = umax_of(I.a, depth + 1); let sm = wmask(bits_of(I.aux)); return if a < sm { a } else { sm }; }
    if I.op == GIR_LSHR {
        let kb, s = ci(res(I.b));
        if kb && s < 64 { return umax_of(I.a, depth + 1) >> s; }
    }
    return m;
}

// Simplifies library call i: the value that replaces it, or NIL (i may
// have been deleted after its replacement was emitted: then a value).
fn simp_libcall(i: u32) -> u32 {
    let I = o_ins[i];
    if I.flags & (IF_INVOKE | IF_CALL_NOBUILTIN) != 0 || gir_kind(I.a) != GIR_V_GLOBAL { return NIL; }
    let g = gir_idx(I.a);
    if g >= lb_kind.len as! u32 { return NIL; }
    let k: u32 = lb_kind[g];
    if k == 0 { return NIL; }
    let t: u32 = I.ty;
    let n = I.c;
    // f(fpext x) for an exact libm f: fpext(ff(x)) (LLVM's shrinking)
    if k >= LB_FLOOR && k <= LB_NEARBYINT && n == 1 && t == GIR_T_F64 {
        let x = lb_arg(I, 0);
        if is_inst(x) && o_ins[x].op == GIR_FPEXT && o_ins[x].aux == GIR_T_F32 {
            let c = lb_call(i, k + 6, GIR_T_F32, res(o_ins[x].a), 0, 0, 1);
            if c == NIL { return NIL; }
            o_ins[c].flags = I.flags & (IF_CALL_NOWRITE | IF_CALL_NOREAD | IF_CALL_PURE);
            let e = new_inst(Inst { op: GIR_FPEXT as! u8, sub: 0, flags: 0, ty: GIR_T_F64, aux: GIR_T_F32, a: c, b: 0, c: 0,
                                    dbg: I.dbg });
            link_before(i, e);
            return e;
        }
        return NIL;
    }
    if k == LB_STRLEN && n == 1 && int_ty(t) {
        return lb_strlen_of(i, lb_arg(I, 0), t, 0);
    }
    let fo = lb_fortified(i, k);
    if fo != NIL { return fo; }
    if k == LB_STRNLEN && n == 2 && int_ty(t) {
        let ok, d, l = lb_str(lb_arg(I, 0));
        let kn, m = ci(lb_arg(I, 1));
        if kn && m == 0 { return int_const(t, 0); }
        if ok && kn { return int_const(t, if (l as u64) < m { l as u64 } else { m }); }
        // a bound no larger than the string: the bound itself
        if ok && umax_of(lb_arg(I, 1), 0) <= l as u64 { return lb_arg(I, 1); }
        if ok {
            // min(bound, length)
            let bt = otype(lb_arg(I, 1));
            let lc = int_const(bt, l as! u64);
            let c = new_inst(Inst { op: GIR_ICMP as! u8, sub: GIR_ULT as! u8, flags: 0, ty: GIR_T_I1, aux: bt as! u16,
                                    a: lb_arg(I, 1), b: lc, c: 0, dbg: I.dbg });
            link_before(i, c);
            let s = new_inst(Inst { op: GIR_SELECT as! u8, sub: 0, flags: 0, ty: bt as! u16, aux: 0, a: c, b: lb_arg(I, 1),
                                    c: lc, dbg: I.dbg });
            link_before(i, s);
            return s;
        }
        return NIL;
    }
    if (k == LB_STRCMP || k == LB_STRNCMP || k == LB_MEMCMP || k == LB_BCMP) && int_ty(t) {
        let a = lb_arg(I, 0);
        let b = lb_arg(I, 1);
        var len: i64 = -1;
        if k != LB_STRCMP {
            if n != 3 { return NIL; }
            let kn, m = ci(lb_arg(I, 2));
            if !kn { return NIL; }
            if m == 0 { return int_const(t, 0); }
            if m > 0x7FFFFFFF { return NIL; }
            len = m as! i64;
        } else if n != 2 { return NIL; }
        if a == b { return int_const(t, 0); }
        let nul = k == LB_STRCMP || k == LB_STRNCMP;
        var oka = false;
        var da: i64 = 0;
        var la: i64 = 0;
        var okb = false;
        var db: i64 = 0;
        var lbn: i64 = 0;
        if nul {
            oka, da, la = lb_str(a);
            okb, db, lbn = lb_str(b);
        } else {
            oka, da, la = lb_ptr(a);
            okb, db, lbn = lb_ptr(b);
            if oka && la < len || okb && lbn < len { return NIL; }
        }
        if oka && okb { return int_const(t, lb_cmp(da, la, db, lbn, len, nul) as! u64); }
        // against "" (or one byte of memcmp): the bytes themselves
        if nul && (oka && la == 0 || okb && lbn == 0) {
            let x = if oka { b } else { a };
            let z = lb_zext8(i, x, t);
            if okb { return z; }
            return ins_new(i, GIR_SUB, t, int_const(t, 0), z);
        }
        if !nul && len == 1 {
            let za = lb_zext8(i, a, t);
            let zb = lb_zext8(i, b, t);
            return ins_new(i, GIR_SUB, t, za, zb);
        }
        return NIL;
    }
    if (k == LB_STRCHR || k == LB_STRRCHR) && n == 2 && t == GIR_T_PTR {
        let s = lb_arg(I, 0);
        let ok, d, l = lb_str(s);
        let kc, c = ci(lb_arg(I, 1));
        if !ok || !kc { return NIL; }
        let ch = c & 0xFF;
        var at: i64 = -1;
        var q: i64 = 0;
        while q <= l {
            if lb_byte(d, q) as u64 == ch {
                at = q;
                if k == LB_STRCHR { break; }
            }
            q++;
        }
        if at < 0 { return lb_null(); }
        return lb_gep(i, s, at);
    }
    if k == LB_MEMCHR && n == 3 && t == GIR_T_PTR {
        let s = lb_arg(I, 0);
        let kc, c = ci(lb_arg(I, 1));
        let kn, m = ci(lb_arg(I, 2));
        if !kc || !kn { return NIL; }
        if m == 0 { return lb_null(); }
        let ok, d, l = lb_ptr(s);
        if !ok || (l as u64) < m { return NIL; }
        var q: i64 = 0;
        while q < m as! i64 {
            if lb_byte(d, q) as u64 == c & 0xFF { return lb_gep(i, s, q); }
            q++;
        }
        return lb_null();
    }
    if (k == LB_STRSTR || k == LB_STRPBRK) && n == 2 && t == GIR_T_PTR {
        let s = lb_arg(I, 0);
        let ok1, d1, l1 = lb_str(s);
        let ok2, d2, l2 = lb_str(lb_arg(I, 1));
        if k == LB_STRSTR && ok2 && l2 == 0 { return s; }
        if k == LB_STRPBRK && ok2 && l2 == 0 { return lb_null(); }
        if k == LB_STRPBRK && ok2 && l2 == 1 && !ok1 {
            // strchr(s, c)
            return lb_call(i, LB_STRCHR, GIR_T_PTR, s, int_const(GIR_T_I32, lb_byte(d2, 0) as u64), 0, 2);
        }
        if !ok1 || !ok2 { return NIL; }
        var q: i64 = 0;
        while q <= l1 {
            if k == LB_STRSTR {
                if q + l2 > l1 { break; }
                var m: i64 = 0;
                while m < l2 && lb_byte(d1, q + m) == lb_byte(d2, m) { m++; }
                if m == l2 { return lb_gep(i, s, q); }
            } else {
                if q == l1 { break; }
                var m: i64 = 0;
                while m < l2 {
                    if lb_byte(d1, q) == lb_byte(d2, m) { return lb_gep(i, s, q); }
                    m++;
                }
            }
            q++;
        }
        return lb_null();
    }
    if (k == LB_STRSPN || k == LB_STRCSPN) && n == 2 && int_ty(t) {
        let ok1, d1, l1 = lb_str(lb_arg(I, 0));
        let ok2, d2, l2 = lb_str(lb_arg(I, 1));
        // "" on either side: 0, except strcspn(s, ""): strlen(s)
        if ok1 && l1 == 0 || k == LB_STRSPN && ok2 && l2 == 0 { return int_const(t, 0); }
        if k == LB_STRCSPN && ok2 && l2 == 0 && !ok1 { return lb_call(i, LB_STRLEN, t, lb_arg(I, 0), 0, 0, 1); }
        if !ok1 || !ok2 { return NIL; }
        var q: i64 = 0;
        while q < l1 {
            var inset = false;
            var m: i64 = 0;
            while m < l2 {
                if lb_byte(d1, q) == lb_byte(d2, m) { inset = true; }
                m++;
            }
            if inset != (k == LB_STRSPN) { break; }
            q++;
        }
        return int_const(t, q as! u64);
    }
    if (k == LB_STRCPY || k == LB_STPCPY || k == LB_STRCPY_CHK || k == LB_STPCPY_CHK) && t == GIR_T_PTR {
        let dst = lb_arg(I, 0);
        let src = lb_arg(I, 1);
        let ok, l = lb_slen(src, 0);
        if !ok || l + 1 > 4096 {
            // stpcpy whose result is not used: strcpy
            if k == LB_STPCPY && lb_sym[LB_STRCPY] != NIL && !nuses_any(i) {
                lb_call(i, LB_STRCPY, GIR_T_PTR, dst, src, 0, 2);
                unlink(i);
            }
            return NIL;
        }
        if k == LB_STRCPY_CHK || k == LB_STPCPY_CHK {
            let kz, z = ci(lb_arg(I, 2));
            if !kz || z != wmask(bits_of(otype(lb_arg(I, 2)))) && z < (l + 1) as! u64 { return NIL; }
        }
        lb_memcpy(i, dst, src, l + 1);
        if k == LB_STRCPY || k == LB_STRCPY_CHK { return dst; }
        return lb_gep(i, dst, l);
    }
    if (k == LB_STRNCPY || k == LB_STRNCPY_CHK) && t == GIR_T_PTR {
        let dst = lb_arg(I, 0);
        let src = lb_arg(I, 1);
        let ok, l = lb_slen(src, 0);
        let kn, m = ci(lb_arg(I, 2));
        if !ok || !kn || m > 4096 { return NIL; }
        if k == LB_STRNCPY_CHK {
            let kz, z = ci(lb_arg(I, 3));
            if !kz || z != wmask(bits_of(otype(lb_arg(I, 3)))) && z < m { return NIL; }
        }
        let cp: i64 = if l + 1 < m as! i64 { l + 1 } else { m as! i64 };
        lb_memcpy(i, dst, src, cp);
        lb_memset(i, lb_gep(i, dst, cp), int_const(GIR_T_I8, 0), m as! i64 - cp);
        return dst;
    }
    if (k == LB_STRCAT || k == LB_STRCAT_CHK) && t == GIR_T_PTR {
        let dst = lb_arg(I, 0);
        let src = lb_arg(I, 1);
        let ok, l = lb_slen(src, 0);
        if !ok || l + 1 > 4096 { return NIL; }
        if k == LB_STRCAT_CHK {
            let kz, z = ci(lb_arg(I, 2));
            if !kz || z != wmask(bits_of(otype(lb_arg(I, 2)))) { return NIL; }
        }
        if l == 0 { return dst; }
        let sl = lb_call(i, LB_STRLEN, GIR_T_I64, dst, 0, 0, 1);
        if sl == NIL { return NIL; }
        let p = new_run(4);
        o_ops[p] = 0;
        o_ops[p + 1] = 0;
        o_ops[p + 2] = sl;
        o_ops[p + 3] = 1;
        let e = new_inst(Inst { op: GIR_GEP as! u8, sub: 0, flags: 0, ty: GIR_T_PTR, aux: 0, a: dst, b: p, c: 1,
                                dbg: I.dbg });
        link_before(i, e);
        lb_memcpy(i, e, src, l + 1);
        return dst;
    }
    if (k == LB_SPRINTF || k == LB_SNPRINTF || k == LB_SPRINTF_CHK || k == LB_SNPRINTF_CHK) && int_ty(t) {
        // the format's position, and the size limit (snprintf)
        let fi: u32 = if k == LB_SPRINTF { 1 } else if k == LB_SNPRINTF { 2 } else if k == LB_SPRINTF_CHK { 3 } else { 4 };
        if n <= fi { return NIL; }
        var lim: i64 = -1;
        if k == LB_SNPRINTF || k == LB_SNPRINTF_CHK {
            let kn, m = ci(lb_arg(I, 1));
            if !kn || m > 4096 { return NIL; }
            lim = m as! i64;
        }
        if k == LB_SPRINTF_CHK || k == LB_SNPRINTF_CHK {
            // flag, object size: unknown size only
            let ko, os = ci(lb_arg(I, fi - 1));
            if !ko || os != wmask(bits_of(otype(lb_arg(I, fi - 1)))) { return NIL; }
        }
        let dst = lb_arg(I, 0);
        let fmt = lb_arg(I, fi);
        let ok, d, l = lb_str(fmt);
        if !ok || l + 1 > 4096 { return NIL; }
        var pct: i64 = -1;
        var q: i64 = 0;
        while q < l {
            if lb_byte(d, q) == '%' { pct = q; break; }
            q++;
        }
        var src = fmt;
        var len = l;
        if pct >= 0 {
            // only "%s" with a constant string
            if l != 2 || lb_byte(d, 1) != 's' || n != fi + 2 { return NIL; }
            src = lb_arg(I, fi + 1);
            let ok2, d2, l2 = lb_str(src);
            if !ok2 || l2 + 1 > 4096 { return NIL; }
            len = l2;
        } else if n != fi + 1 { return NIL; }
        if lim < 0 || len + 1 <= lim { lb_memcpy(i, dst, src, len + 1); }
        else if lim > 0 {
            lb_memcpy(i, dst, src, lim - 1);
            lb_memset(i, lb_gep(i, dst, lim - 1), int_const(GIR_T_I8, 0), 1);
        }
        return int_const(t, len as! u64);
    }
    if k == LB_BCOPY && n == 3 && t == GIR_T_VOID && lb_sym[LB_MEMMOVE] != NIL {
        // bcopy(s, d, n): memmove(d, s, n)
        lb_call(i, LB_MEMMOVE, GIR_T_PTR, lb_arg(I, 1), lb_arg(I, 0), lb_arg(I, 2), 3);
        unlink(i);
        return NIL;
    }
    if k == LB_MEMMOVE && n == 3 {
        let kn, m = ci(lb_arg(I, 2));
        let dst = lb_arg(I, 0);
        if kn && m <= 64 && m != 0 && aa_alias(dst, m as! u32, 0, lb_arg(I, 1), m as! u32, 0) {
            lb_move_small(i, dst, lb_arg(I, 1), m as! i64);
            if t == GIR_T_VOID { unlink(i); return NIL; }
            return dst;
        }
    }
    if (k == LB_MEMCMP || k == LB_BCMP) && n == 3 && int_ty(t) {
        let kn, m = ci(lb_arg(I, 2));
        if kn && m > 1 && m <= 32 && lb_only_eq0(i) { return lb_cmp_eq(i, lb_arg(I, 0), lb_arg(I, 1), m as! i64, t); }
    }
    if (k == LB_MEMCPY || k == LB_MEMMOVE || k == LB_MEMPCPY || k == LB_MEMCPY_CHK || k == LB_MEMMOVE_CHK) && n >= 3 {
        let dst = lb_arg(I, 0);
        let src = lb_arg(I, 1);
        let kn, m = ci(lb_arg(I, 2));
        if !kn || m > 4096 { return NIL; }
        if k == LB_MEMCPY_CHK || k == LB_MEMMOVE_CHK {
            let kz, z = ci(lb_arg(I, 3));
            if !kz || z != wmask(bits_of(otype(lb_arg(I, 3)))) && z < m { return NIL; }
        }
        if (k == LB_MEMMOVE || k == LB_MEMMOVE_CHK) && m != 0 && aa_alias(dst, m as! u32, 0, src, m as! u32, 0) { return NIL; }
        lb_memcpy(i, dst, src, m as! i64);
        if k == LB_MEMPCPY { return lb_gep(i, dst, m as! i64); }
        if t == GIR_T_VOID { unlink(i); return NIL; }
        return dst;
    }
    if (k == LB_MEMSET || k == LB_MEMSET_CHK) && n >= 3 {
        let dst = lb_arg(I, 0);
        let kn, m = ci(lb_arg(I, 2));
        if !kn || m > 4096 { return NIL; }
        if k == LB_MEMSET_CHK {
            let kz, z = ci(lb_arg(I, 3));
            if !kz || z != wmask(bits_of(otype(lb_arg(I, 3)))) && z < m { return NIL; }
        }
        let v = lb_arg(I, 1);
        let vt = otype(v);
        var b8 = v;
        if vt != GIR_T_I8 {
            let kv, x = ci(v);
            if kv { b8 = int_const(GIR_T_I8, x & 0xFF); }
            else {
                b8 = new_inst(Inst { op: GIR_TRUNC as! u8, sub: 0, flags: 0, ty: GIR_T_I8, aux: vt as! u16, a: v, b: 0, c: 0,
                                     dbg: I.dbg });
                link_before(i, b8);
            }
        }
        lb_memset(i, dst, b8, m as! i64);
        if t == GIR_T_VOID { unlink(i); return NIL; }
        return dst;
    }
    if (k == LB_VSNPRINTF_CHK || k == LB_VSPRINTF_CHK) && n >= 4 {
        // (dst, [n,] flag, objsize, fmt, ap) -> v(s)(n)printf when the size is unknown
        let si: u32 = if k == LB_VSNPRINTF_CHK { 3 } else { 2 };
        let ko, os = ci(lb_arg(I, si));
        if !ko || os != wmask(bits_of(otype(lb_arg(I, si)))) { return NIL; }
        if k == LB_VSNPRINTF_CHK {
            if n != 6 { return NIL; }
            return lb_call4(i, LB_VSNPRINTF, t, lb_arg(I, 0), lb_arg(I, 1), lb_arg(I, 4), lb_arg(I, 5));
        }
        if n != 5 { return NIL; }
        return lb_call(i, LB_VSPRINTF, t, lb_arg(I, 0), lb_arg(I, 3), lb_arg(I, 4), 3);
    }
    if k == LB_PRINTF && n >= 1 && I.flags & IF_VARARG != 0 {
        let ok, d, l = lb_str(lb_arg(I, 0));
        if !ok { return NIL; }
        // printf("%s\n", s) -> puts(s); printf("c") and printf("%c", c) -> putchar
        if l == 3 && lb_byte(d, 0) == '%' && lb_byte(d, 1) == 's' && lb_byte(d, 2) == 10 && n == 2 {
            if nuses_any(i) { return NIL; }
            let c = lb_call(i, LB_PUTS, GIR_T_I32, lb_arg(I, 1), 0, 0, 1);
            if c == NIL { return NIL; }
            unlink(i);
            return NIL;
        }
        if l == 1 && lb_byte(d, 0) != '%' && n == 1 {
            if nuses_any(i) { return NIL; }
            let c = lb_call(i, LB_PUTCHAR, GIR_T_I32, int_const(GIR_T_I32, lb_byte(d, 0) as u64), 0, 0, 1);
            if c == NIL { return NIL; }
            unlink(i);
            return NIL;
        }
        if l == 0 && n == 1 {
            if nuses_any(i) { return int_const(t, 0); }
            unlink(i);
            return NIL;
        }
        if l == 2 && lb_byte(d, 0) == '%' && lb_byte(d, 1) == 'c' && n == 2 && otype(lb_arg(I, 1)) == GIR_T_I32 {
            if nuses_any(i) { return NIL; }
            let c = lb_call(i, LB_PUTCHAR, GIR_T_I32, lb_arg(I, 1), 0, 0, 1);
            if c == NIL { return NIL; }
            unlink(i);
            return NIL;
        }
    }
    return NIL;
}
fn lb_call4(at: u32, k: u32, ty: u32, a0: u32, a1: u32, a2: u32, a3: u32) -> u32 {
    let g = lb_sym[k];
    if g == NIL { return NIL; }
    let s = new_run(8);
    o_ops[s] = a0;
    o_ops[s + 1] = 0;
    o_ops[s + 2] = a1;
    o_ops[s + 3] = 0;
    o_ops[s + 4] = a2;
    o_ops[s + 5] = 0;
    o_ops[s + 6] = a3;
    o_ops[s + 7] = 0;
    let c = new_inst(Inst { op: GIR_CALL as! u8, sub: 0, flags: 0, ty: ty as! u16, aux: 0, a: GIR_V_GLOBAL << 30 | g,
                            b: s, c: 4, dbg: o_ins[at].dbg });
    link_before(at, c);
    return c;
}
// The chunks of a small copy or compare: 8, 4, 2 and 1 bytes.
inline fn lb_chunk(left: i64) -> i64 { if left >= 8 { 8 } else if left >= 4 { 4 } else if left >= 2 { 2 } else { 1 } }
inline fn lb_ity(w: i64) -> u32 { if w == 8 { GIR_T_I64 } else if w == 4 { GIR_T_I32 } else if w == 2 { GIR_T_I16 } else { GIR_T_I8 } }
var lb_vals: u32[>..] = [];
// memmove of m <= 64 bytes that may overlap: every chunk is loaded before
// the first store (as LLVM's inline memmove expansion).
fn lb_move_small(at: u32, d: u32, s: u32, m: i64) {
    lb_vals.clear();
    var off: i64 = 0;
    while off < m {
        let w = lb_chunk(m - off);
        let l = new_inst(Inst { op: GIR_LOAD as! u8, sub: 0, flags: 0, ty: lb_ity(w) as! u16, aux: 0, a: lb_gep(at, s, off),
                                b: 0, c: 0, dbg: o_ins[at].dbg });
        link_before(at, l);
        lb_vals.push(l);
        off += w;
    }
    off = 0;
    var q: i64 = 0;
    while off < m {
        let w = lb_chunk(m - off);
        let x = new_inst(Inst { op: GIR_STORE as! u8, sub: 0, flags: 0, ty: GIR_T_VOID, aux: lb_ity(w) as! u16, a: lb_vals[q],
                                b: lb_gep(at, d, off), c: 0, dbg: o_ins[at].dbg });
        link_before(at, x);
        off += w;
        q++;
    }
}
// Whether every use of call i is a test of it against 0 (== or !=); a scan
// of the function (functions of a moderate size only).
fn lb_only_eq0(i: u32) -> bool {
    if o_ins.len > 50000 { return false; }
    var any = false;
    for x0 in 0..o_ins.len {
        let x: u32 = x0 as! u32;
        if o_blk[x] == NIL { continue; }
        var uses = false;
        each_slot(x) { s =>
            if res(vget(x, s)) == i { uses = true; }
        };
        if !uses { continue; }
        let X = o_ins[x];
        if X.op != GIR_ICMP || X.sub != GIR_EQ && X.sub != GIR_NE { return false; }
        let o = if res(X.a) == i { res(X.b) } else { res(X.a) };
        let k, v = ci(o);
        if !k || v != 0 { return false; }
        any = true;
    }
    return any;
}
// memcmp / bcmp of m bytes, only tested against 0: 0 when the bytes are
// equal, else 1 (as LLVM's ExpandMemCmp for equality).
fn lb_cmp_eq(at: u32, a: u32, b: u32, m: i64, t: u32) -> u32 {
    var acc: u32 = NIL;
    var off: i64 = 0;
    let dbg = o_ins[at].dbg;
    while off < m {
        let w = lb_chunk(m - off);
        let it = lb_ity(w);
        let la = new_inst(Inst { op: GIR_LOAD as! u8, sub: 0, flags: 0, ty: it as! u16, aux: 0, a: lb_gep(at, a, off),
                                 b: 0, c: 0, dbg: dbg });
        link_before(at, la);
        let lb = new_inst(Inst { op: GIR_LOAD as! u8, sub: 0, flags: 0, ty: it as! u16, aux: 0, a: lb_gep(at, b, off),
                                 b: 0, c: 0, dbg: dbg });
        link_before(at, lb);
        var x = ins_new(at, GIR_XOR, it, la, lb);
        if it != GIR_T_I64 {
            x = new_inst(Inst { op: GIR_ZEXT as! u8, sub: 0, flags: 0, ty: GIR_T_I64, aux: it as! u16, a: x, b: 0, c: 0, dbg: dbg });
            link_before(at, x);
        }
        acc = if acc == NIL { x } else { ins_new(at, GIR_OR, GIR_T_I64, acc, x) };
        off += w;
    }
    let c = new_inst(Inst { op: GIR_ICMP as! u8, sub: GIR_NE as! u8, flags: 0, ty: GIR_T_I1, aux: GIR_T_I64, a: acc,
                            b: int_const(GIR_T_I64, 0), c: 0, dbg: dbg });
    link_before(at, c);
    let z = new_inst(Inst { op: GIR_ZEXT as! u8, sub: 0, flags: 0, ty: t as! u16, aux: GIR_T_I1, a: c, b: 0, c: 0, dbg: dbg });
    link_before(at, z);
    return z;
}

// A __*_chk call whose check cannot fail (LLVM's FortifiedLibCallSimplifier,
// isFortifiedCallFoldable): the object size is unknown (-1) or at least the
// size argument (or the constant source string's length + 1), and the flag
// (the printf family) is 0. It becomes the unchecked function without the
// flag and object size arguments; NIL: not foldable.
fn lb_fortified(i: u32, k: u32) -> u32 {
    var plain: u32 = 0;
    var os: u32 = NIL;       // operand positions: object size, size, source string, flag
    var sz: u32 = NIL;
    var st: u32 = NIL;
    var fg: u32 = NIL;
    if k == LB_MEMCPY_CHK { plain = LB_MEMCPY; os = 3; sz = 2; }
    else if k == LB_MEMMOVE_CHK { plain = LB_MEMMOVE; os = 3; sz = 2; }
    else if k == LB_MEMSET_CHK { plain = LB_MEMSET; os = 3; sz = 2; }
    else if k == LB_STRCPY_CHK { plain = LB_STRCPY; os = 2; st = 1; }
    else if k == LB_STPCPY_CHK { plain = LB_STPCPY; os = 2; st = 1; }
    else if k == LB_STRCAT_CHK { plain = LB_STRCAT; os = 2; }
    else if k == LB_STRNCPY_CHK { plain = LB_STRNCPY; os = 3; sz = 2; }
    else if k == LB_STRNCAT_CHK { plain = LB_STRNCAT; os = 3; }
    else if k == LB_SNPRINTF_CHK { plain = LB_SNPRINTF; os = 3; sz = 1; fg = 2; }
    else if k == LB_SPRINTF_CHK { plain = LB_SPRINTF; os = 2; fg = 1; }
    else if k == LB_VSNPRINTF_CHK { plain = LB_VSNPRINTF; os = 3; sz = 1; fg = 2; }
    else if k == LB_VSPRINTF_CHK { plain = LB_VSPRINTF; os = 2; fg = 1; }
    else { return NIL; }
    let I = o_ins[i];
    if I.c <= os || lb_sym[plain] == NIL { return NIL; }
    if fg != NIL {
        let kf, f = ci(lb_arg(I, fg));
        if !kf || f != 0 { return NIL; }
    }
    let ko, o = ci(lb_arg(I, os));
    if !ko { return NIL; }
    if o != wmask(bits_of(otype(lb_arg(I, os)))) {
        if sz != NIL {
            let kn, m = ci(lb_arg(I, sz));
            if !kn || m > o { return NIL; }
        } else if st != NIL {
            let ok, d, l = lb_str(lb_arg(I, st));
            if !ok || (l + 1) as! u64 > o { return NIL; }
        } else {
            return NIL;
        }
    }
    // the call without the flag and the object size
    let drop2: u32 = if fg != NIL { fg } else { os };
    let s = new_run(2 * (I.c - (if fg != NIL { 2 } else { 1 })));
    var w: u32 = 0;
    for q in 0..I.c {
        if q == os || q == drop2 { continue; }
        o_ops[s + 2 * w] = o_ops[I.b + 2 * q];
        o_ops[s + 2 * w + 1] = o_ops[I.b + 2 * q + 1];
        w++;
    }
    let c = new_inst(Inst { op: GIR_CALL as! u8, sub: 0, flags: I.flags & IF_VARARG, ty: I.ty, aux: I.aux,
                            a: GIR_V_GLOBAL << 30 | lb_sym[plain], b: s, c: w, dbg: I.dbg });
    link_before(i, c);
    if I.ty == GIR_T_VOID { unlink(i); return NIL; }
    return c;
}

// Whether the value of instruction i is used (a slow scan: only for the
// rare printf rewrites).
fn nuses_any(i: u32) -> bool {
    for x0 in 0..o_ins.len {
        let x: u32 = x0 as! u32;
        if o_blk[x] == NIL { continue; }
        var used = false;
        each_slot(x) { s => if res(vget(x, s)) == i { used = true; } };
        if used { return true; }
    }
    return false;
}

// ------------------------------------------------------------ objectsize
// (E2) GIR_OBJSIZE (llvm.objectsize, __builtin_object_size and
// __builtin_dynamic_object_size at -O1 and above): the bytes from the
// pointer to the end of its object, folded once the object is known (after
// inlining, as LLVM's InstCombine does); what is left after all functions
// are optimized is unknown (opt.goose, isconst_refine: -1, or 0 for the
// minimum), as LLVM's LowerConstantIntrinsics. Objects: allocas, defined
// variables that cannot be replaced (not weak or common), byval arguments,
// the results of the allocation functions with constant (or, dynamic,
// any) sizes, null (0 bytes unless null is unknown); selects and PHIs of
// them (the larger, or the smaller for the minimum). An offset outside the
// object leaves 0 bytes. Dynamic: run-time sizes and GEP offsets.
let OS_MIN: u32 = 1;
let OS_NULLUNK: u32 = 2;
let OS_DYN: u32 = 4;

fn os_new(at: u32, op: u32, ty: u32, aux: u32, a: u32, b: u32, c: u32) -> u32 {
    let x = new_inst(Inst { op: op as! u8, sub: 0, flags: 0, ty: ty as! u16, aux: aux as! u16, a: a, b: b, c: c,
                            dbg: o_ins[at].dbg });
    link_before(at, x);
    return x;
}
fn os_type(v: u32) -> u32 {
    let k = gir_kind(v);
    if k == GIR_V_INST { return o_ins[v].ty; }
    if k == GIR_V_ARG { return M.opnds[o_f.args + 2 * gir_idx(v)]; }
    if k == GIR_V_CONST { return x_consts[xb_c + gir_idx(v)].ty; }
    return GIR_T_PTR;
}
// v as an i64 (size_t arguments are i64 already; narrower: zero-extended)
fn os_i64(at: u32, v: u32) -> u32 {
    let t = os_type(v);
    if t == GIR_T_I64 { return v; }
    let kc, x = ci(v);
    if kc { return int_const(GIR_T_I64, x); }
    return os_new(at, GIR_ZEXT, GIR_T_I64, t, v, 0, 0);
}

// The size of the object based at b: (known, constant size, run-time size
// value or NIL); a run-time size only with OS_DYN.
fn os_size(at: u32, b: u32, fl: u32) -> bool, i64, u32 {
    let k = gir_kind(b);
    if k == GIR_V_GLOBAL {
        let G = M.globals[gir_idx(b)];
        if G.kind == G_VAR && G.flags & GF_DEFINED != 0 && G.flags & (GF_WEAK | GF_COMMON) == 0 {
            return true, G.size as i64, NIL;
        }
        return false, 0, NIL;
    }
    if k == GIR_V_ARG {
        let a = gir_idx(b);
        if a < o_f.n_args {
            let w = M.opnds[o_f.args + 2 * a + 1];
            if w & ABI_BYVAL != 0 { return true, abi_size(w) as i64, NIL; }
        }
        return false, 0, NIL;
    }
    if k == GIR_V_CONST {
        let C = x_consts[xb_c + gir_idx(b)];
        if C.ty == GIR_T_PTR && C.data == GIR_NONE && C.lo == 0 && C.hi == 0 && fl & OS_NULLUNK == 0 {
            return true, 0, NIL;
        }
        return false, 0, NIL;
    }
    if k != GIR_V_INST { return false, 0, NIL; }
    let I = o_ins[b];
    if I.op == GIR_ALLOCA { return true, I.a as i64, NIL; }
    if I.op == GIR_DYNALLOCA {
        let ka, xa = ci(res(I.a));
        if ka { return true, xa as! i64, NIL; }
        if fl & OS_DYN != 0 { return true, 0, os_i64(at, res(I.a)); }
        return false, 0, NIL;
    }
    if I.op == GIR_CALL && I.flags & IF_CALL_NOBUILTIN == 0 && gir_kind(I.a) == GIR_V_GLOBAL {
        let lk: u32 = lb_kind[gir_idx(I.a)];
        var s0: u32 = NIL;
        var s1: u32 = NIL;
        if lk == LB_MALLOC && I.c >= 1 { s0 = o_ops[I.b]; }
        else if lk == LB_CALLOC && I.c == 2 { s0 = o_ops[I.b]; s1 = o_ops[I.b + 2]; }
        else if (lk == LB_REALLOC || lk == LB_ALIGNED) && I.c == 2 { s0 = o_ops[I.b + 2]; }
        if s0 == NIL { return false, 0, NIL; }
        s0 = res(s0);
        let k0, x0 = ci(s0);
        if s1 == NIL {
            if k0 { return true, x0 as! i64, NIL; }
            if fl & OS_DYN != 0 { return true, 0, os_i64(at, s0); }
            return false, 0, NIL;
        }
        s1 = res(s1);
        let k1, x1 = ci(s1);
        if k0 && k1 {
            // (an overflowing product: no object)
            if x1 != 0 && x0 > 0xFFFFFFFFFFFFFFFF / x1 { return false, 0, NIL; }
            return true, (x0 * x1) as! i64, NIL;
        }
        if fl & OS_DYN != 0 {
            return true, 0, os_new(at, GIR_MUL, GIR_T_I64, 0, os_i64(at, s0), os_i64(at, s1), 0);
        }
        return false, 0, NIL;
    }
    return false, 0, NIL;
}

// The remaining bytes of (size, offset): 0 outside the object (LLVM's
// getSizeWithOverflow).
inline fn os_rem(sz: i64, off: i64) -> i64 {
    if off < 0 || off > sz { return 0; }
    return sz - off;
}

// (memo of the selects and PHIs evaluated for one GIR_OBJSIZE: 1 in
// progress, 2 known, 3 unknown)
var os_ep: u32 = 0;
var os_mep: u32[>..] = [];
var os_mst: u8[>..] = [];
var os_msz: i64[>..] = [];
var os_moff: i64[>..] = [];

// Static: the object of pointer p0 and the offset into it (known, size, offset).
recursive fn os_st(at: u32, p0: u32, fl: u32) -> bool, i64, i64 {
    var p = res(p0);
    var off: i64 = 0;
    var n = 0;
    while is_inst(p) && o_ins[p].op == GIR_GEP && n < 64 {
        let G = o_ins[p];
        off += (o_ops[G.b] as u64 | (o_ops[G.b + 1] as u64 << 32)) as! i64;
        for q in 0..G.c {
            let ix = res(o_ops[G.b + 2 + 2 * q]);
            let ki, xi = ci(ix);
            if !ki { return false, 0, 0; }
            off += (sx(xi, bits_of(os_type(ix))) as! u64 * (o_ops[G.b + 3 + 2 * q] as u64)) as! i64;
        }
        p = res(G.a);
        n++;
    }
    if is_inst(p) && (o_ins[p].op == GIR_SELECT || o_ins[p].op == GIR_PHI) {
        if os_mep.len < o_ins.len {
            os_mep.resize(o_ins.len, 0);
            os_mst.resize(o_ins.len, 0);
            os_msz.resize(o_ins.len, 0);
            os_moff.resize(o_ins.len, 0);
        }
        if os_mep[p] == os_ep {
            // (a cycle of PHIs: unknown, as LLVM)
            if os_mst[p] != 2 { return false, 0, 0; }
            return true, os_msz[p], os_moff[p] + off;
        }
        os_mep[p] = os_ep;
        os_mst[p] = 1;
        let I = o_ins[p];
        var ok = true;
        var first = true;
        var bs: i64 = 0;
        var bo: i64 = 0;
        let nv: u32 = if I.op == GIR_SELECT { 2 } else { I.c };
        for q in 0..nv {
            let v = if I.op == GIR_SELECT { if q == 0 { I.b } else { I.c } } else { o_ops[I.b + 2 * q] };
            if res(v) == p { continue; }
            let kv, sv, ov = os_st(at, v, fl);
            if !kv { ok = false; break; }
            // the larger remainder (the smaller for the minimum)
            if first || (if fl & OS_MIN != 0 { os_rem(sv, ov) < os_rem(bs, bo) } else { os_rem(sv, ov) > os_rem(bs, bo) }) {
                bs = sv;
                bo = ov;
            }
            first = false;
        }
        if !ok || first {
            os_mst[p] = 3;
            return false, 0, 0;
        }
        os_mst[p] = 2;
        os_msz[p] = bs;
        os_moff[p] = bo;
        return true, bs, bo + off;
    }
    let known, sz, dsz = os_size(at, p, fl & ~OS_DYN);
    if !known || dsz != NIL { return false, 0, 0; }
    return true, sz, off;
}

// Dynamic: (known, size value, offset value), both i64, made before at.
recursive fn os_dy(at: u32, p0: u32, fl: u32, depth: u32) -> bool, u32, u32 {
    let ks, ss, so = os_st(at, p0, fl);
    if ks { return true, int_const(GIR_T_I64, ss as! u64), int_const(GIR_T_I64, so as! u64); }
    var p = res(p0);
    var off: i64 = 0;
    var doff: u32 = NIL;
    var n = 0;
    while is_inst(p) && o_ins[p].op == GIR_GEP && n < 64 {
        let G = o_ins[p];
        off += (o_ops[G.b] as u64 | (o_ops[G.b + 1] as u64 << 32)) as! i64;
        for q in 0..G.c {
            let ix = res(o_ops[G.b + 2 + 2 * q]);
            let sc: u64 = o_ops[G.b + 3 + 2 * q] as u64;
            let ki, xi = ci(ix);
            if ki {
                off += (sx(xi, bits_of(os_type(ix))) as! u64 * sc) as! i64;
                continue;
            }
            var t = ix;
            let it = os_type(ix);
            if it != GIR_T_I64 { t = os_new(at, GIR_SEXT, GIR_T_I64, it, ix, 0, 0); }
            if sc != 1 { t = os_new(at, GIR_MUL, GIR_T_I64, 0, t, int_const(GIR_T_I64, sc), 0); }
            doff = if doff == NIL { t } else { os_new(at, GIR_ADD, GIR_T_I64, 0, doff, t, 0) };
        }
        p = res(G.a);
        n++;
    }
    var sv: u32 = NIL;
    var ov: u32 = NIL;
    if is_inst(p) && o_ins[p].op == GIR_SELECT && depth < 16 {
        // the chosen object's size and offset
        let I = o_ins[p];
        let ka, sa, oa = os_dy(at, I.b, fl, depth + 1);
        if !ka { return false, 0, 0; }
        let kb, sb, ob = os_dy(at, I.c, fl, depth + 1);
        if !kb { return false, 0, 0; }
        let c = res(I.a);
        sv = if sa == sb { sa } else { os_new(at, GIR_SELECT, GIR_T_I64, 0, c, sa, sb) };
        ov = if oa == ob { oa } else { os_new(at, GIR_SELECT, GIR_T_I64, 0, c, oa, ob) };
    } else {
        let known, sz, dsz = os_size(at, p, fl);
        if !known { return false, 0, 0; }
        sv = if dsz == NIL { int_const(GIR_T_I64, sz as! u64) } else { dsz };
        ov = int_const(GIR_T_I64, 0);
    }
    if off != 0 { ov = os_add(at, ov, int_const(GIR_T_I64, off as! u64)); }
    if doff != NIL { ov = os_add(at, ov, doff); }
    return true, sv, ov;
}
fn os_add(at: u32, a: u32, b: u32) -> u32 {
    let ka, xa = ci(a);
    let kb, xb = ci(b);
    if ka && kb { return int_const(GIR_T_I64, xa + xb); }
    if ka && xa == 0 { return b; }
    if kb && xb == 0 { return a; }
    return os_new(at, GIR_ADD, GIR_T_I64, 0, a, b, 0);
}

// GIR_OBJSIZE i: its value when the object is known, else NIL.
fn simp_objsize(i: u32) -> u32 {
    let I = o_ins[i];
    let fl: u32 = I.sub;
    let ty: u32 = I.ty;
    os_ep++;
    // (static first: no instructions are made when that suffices)
    let ks, ss, so = os_st(i, I.a, fl);
    if ks { return int_const(ty, os_rem(ss, so) as! u64); }
    if fl & OS_DYN == 0 { return NIL; }
    let kd, sv, ov = os_dy(i, I.a, fl, 0);
    if !kd { return NIL; }
    // size < offset (or a negative offset): 0
    let lt = os_new(i, GIR_ICMP, GIR_T_I1, GIR_T_I64, sv, ov, 0);
    o_ins[lt].sub = GIR_ULT as! u8;
    let d = os_new(i, GIR_SUB, GIR_T_I64, 0, sv, ov, 0);
    let r = os_new(i, GIR_SELECT, GIR_T_I64, 0, lt, int_const(GIR_T_I64, 0), d);
    if ty == GIR_T_I64 { return r; }
    return os_new(i, GIR_TRUNC, ty, GIR_T_I64, r, 0, 0);
}
// Its value when nothing is known: -1, or 0 for the minimum.
fn objsize_unknown(i: u32) -> u32 {
    let ty: u32 = o_ins[i].ty;
    return int_const(ty, if o_ins[i].sub & OS_MIN != 0 { 0 as u64 } else { 0xFFFFFFFFFFFFFFFF as u64 });
}
