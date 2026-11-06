// goosecc B2: builtin functions, as clang's CGBuiltin.cpp emits them at -O0
// (and as tools/goovm-llc/gir_export.cpp then lowers the intrinsics):
// library builtins with a direct lowering (memcpy, abs, fabs, floor, ...),
// __builtin_* operations, bit operations, overflow checks, FP
// classification, setjmp/longjmp, va_*, and the __sync / __atomic family.

namespace gen;

import std;
import .common;
import .types;
import .ast;
import .sema;
import .builtins;

let KEEP_CALL: u32 = 0xFFFFFFFE;

fn barg(n: u32, i: i64) -> u32 { nlist[nodes[n].v + i] }

fn strip_builtin(name: const u8[:]) -> const u8[:] {
    if starts_with(name, "__builtin_") { return name[10..]; }
    return name;
}

// A call of a library function that clang lowers itself; KEEP_CALL to
// emit an ordinary call.
recursive fn builtin_lib_call(s: i64, n: u32, dst: u32) -> u32 {
    if is_internal_sym(s) { return KEEP_CALL; }
    let a = syms[s].attr;
    if a != 0 && sym_attrs[a].asm_len != 0 { return KEEP_CALL; }
    let id = syms[s].name;
    if builtin_index(id) < 0 { return KEEP_CALL; }
    let name = ident_text(id as i64);
    if !is_library_name(name) { return KEEP_CALL; }
    return lib_builtin(name, n, dst, false);
}

fn is_math_const_fn(b: const u8[:]) -> bool {
    return b == "fabs" || b == "fabsf" || b == "fabsl" || b == "copysign" || b == "copysignf" || b == "copysignl" ||
        b == "floor" || b == "floorf" || b == "floorl" || b == "ceil" || b == "ceilf" || b == "ceill" ||
        b == "trunc" || b == "truncf" || b == "truncl" || b == "round" || b == "roundf" || b == "roundl" ||
        b == "rint" || b == "rintf" || b == "rintl" || b == "nearbyint" || b == "nearbyintf" || b == "nearbyintl" ||
        b == "fmin" || b == "fminf" || b == "fminl" || b == "fmax" || b == "fmaxf" || b == "fmaxl" ||
        b == "roundeven" || b == "roundevenf" || b == "roundevenl";
}

// The library builtins (name without __builtin_); `forced` for the
// __builtin_ spellings (always lowered).
recursive fn lib_builtin(name: const u8[:], n: u32, dst: u32, forced: bool) -> u32 {
    let nd = nodes[n];
    let nargs = nd.c as i64;
    if name == "memcpy" || name == "memmove" || name == "memset" {
        if nargs != 3 { return KEEP_CALL; }
        let d = ex_val(barg(n, 0));
        let s2 = ex_val(barg(n, 1));
        let ln = ex_val(barg(n, 2));
        let len = conv(ln, nty(barg(n, 2)), t_ulong);
        if name == "memset" {
            let b = int_cast(s2, vtype(s2), GIR_T_I8, false);
            if is_const(len) && c_lo(len) <= 256 { mem_set(d, b, c_lo(len) as! i64, false); }
            else { libcall3("memset", GIR_T_PTR, d, ins_zext(b, GIR_T_I32), len); }
            return d;
        }
        if name == "memcpy" && is_const(len) && c_lo(len) <= 256 { mem_copy(d, s2, c_lo(len) as! i64, false); return d; }
        libcall3(name, GIR_T_PTR, d, s2, len);
        return d;
    }
    if name == "abs" || name == "labs" || name == "llabs" {
        if nargs != 1 { return KEEP_CALL; }
        let x = ex_val(barg(n, 0));
        let t = vtype(x);
        let neg = ins_bin(GIR_SUB, t, c_zero(t), x);
        let c = ins_icmp(GIR_SLT, t, x, c_zero(t));
        return ins_select(c, neg, x);
    }
    if is_math_const_fn(name) {
        if nargs < 1 { return KEEP_CALL; }
        let rq = unqual(nd.ty);
        let x = ex_val(barg(n, 0));
        let t = vtype(x);
        var y: u32 = NONE;
        if nargs > 1 { y = ex_val(barg(n, 1)); }
        if starts_with(name, "fabs") { return fp_unary_fold(GIR_FABS, t, x); }
        if starts_with(name, "copysign") {
            if is_const(x) && is_const(y) && t != GIR_T_F80 {
                let ok, a = c_as_double(x);
                let ok2, b = c_as_double(y);
                if ok && ok2 { return c_double(libm_copysign(a, b), t); }
            }
            return emit(GIR_COPYSIGN, t, 0, 0, t, x, y, 0);
        }
        // floor & co.: a libm call, folded for constants (LLVM folds them)
        if is_const(x) && t != GIR_T_F80 && (y == NONE || is_const(y)) {
            let ok, a = c_as_double(x);
            var b = 0.0;
            if y != NONE { let ok2, b2 = c_as_double(y); b = b2; }
            if ok {
                let base = if ends_with(name, "f") && name != "nearbyintf" && !starts_with(name, "nearbyint") { name } else { name };
                let r = libm_fold(math_base(name), a, b);
                return c_double(if t == GIR_T_F32 { round_f32(r) } else { r }, t);
            }
        }
        if y != NONE { return libcall2(name, t, x, y); }
        return libcall1(name, t, x);
    }
    if name == "alloca" {
        let sz = ex_val(barg(n, 0));
        return emit(GIR_DYNALLOCA, GIR_T_PTR, 0, 0, 0, conv(sz, nty(barg(n, 0)), t_ulong), 16, 0);
    }
    if name == "bzero" && nargs == 2 {
        let d = ex_val(barg(n, 0));
        let ln = conv(ex_val(barg(n, 1)), nty(barg(n, 1)), t_ulong);
        if is_const(ln) && c_lo(ln) <= 256 { mem_set(d, c_i8(0), c_lo(ln) as! i64, false); }
        else { libcall3("memset", GIR_T_PTR, d, c_i32(0), ln); }
        return NONE;
    }
    if name == "bcopy" && nargs == 3 {
        let s2 = ex_val(barg(n, 0));
        let d = ex_val(barg(n, 1));
        let ln = conv(ex_val(barg(n, 2)), nty(barg(n, 2)), t_ulong);
        libcall3("memmove", GIR_T_PTR, d, s2, ln);
        return NONE;
    }
    if name == "strlen" && nargs == 1 {
        let ok, len = const_strlen(barg(n, 0));
        if ok { return c_i64(len); }
    }
    return KEEP_CALL;
}

fn math_base(name: const u8[:]) -> const u8[:] {
    let b = name;
    if b == "floorf" || b == "floorl" { return "floor"; }
    if b == "ceilf" || b == "ceill" { return "ceil"; }
    if b == "truncf" || b == "truncl" { return "trunc"; }
    if b == "roundf" || b == "roundl" { return "round"; }
    if b == "rintf" || b == "rintl" { return "rint"; }
    if b == "nearbyintf" || b == "nearbyintl" { return "nearbyint"; }
    if b == "fminf" || b == "fminl" { return "fmin"; }
    if b == "fmaxf" || b == "fmaxl" { return "fmax"; }
    if b == "roundevenf" || b == "roundevenl" { return "roundeven"; }
    return b;
}

fn libm_fold(b: const u8[:], x: f64, y: f64) -> f64 {
    let k = if b == "floor" { 0 } else if b == "ceil" { 1 } else if b == "trunc" { 2 } else if b == "round" { 3 }
        else if b == "rint" || b == "nearbyint" || b == "roundeven" { 4 } else if b == "fmin" { 5 } else { 6 };
    return libm_op(k, x, y);
}

extern fn libm_op(k: i64, x: f64, y: f64) -> f64 = "goosecc_libm_op";
extern fn libm_copysign(x: f64, y: f64) -> f64 = "goosecc_copysign";

fn fp_unary_fold(op: i64, t: u32, x: u32) -> u32 {
    if is_const(x) && op == GIR_FABS {
        let c = m_consts[cidx(x)];
        if t == GIR_T_F64 { return c_fp(c.lo & 0x7FFFFFFFFFFFFFFF, 0, t); }
        if t == GIR_T_F32 { return c_fp(c.lo & 0x7FFFFFFF, 0, t); }
        if t == GIR_T_F80 { return c_fp(c.lo, c.hi & 0x7FFF, t); }
    }
    if t == GIR_T_F16 {
        let i = ins_bitcast(x, GIR_T_I16);
        let m = ins_bin(GIR_AND, GIR_T_I16, i, c_int(0x7FFF, GIR_T_I16));
        return ins_bitcast(m, GIR_T_F16);
    }
    return emit(op, t, 0, 0, t, x, 0, 0);
}

// strlen of a string literal (clang's constant evaluator folds it).
fn const_strlen(n: u32) -> bool, i64 {
    var m = n;
    loop {
        let nd = nodes[m];
        if (nd.kind == N_ICAST || nd.kind == N_CAST) && (nd.op == CK_ARRAY2PTR || nd.op == CK_NOOP || nd.op == CK_BITCAST) { m = nd.a; continue; }
        if nd.kind == N_STRING {
            let sl = strs[nd.a];
            if type_size(sl.elem) != 1 { return false, 0; }
            let b = strbytes[sl.start..sl.start + sl.len];
            for c, i in b { if c == 0 { return true, i; } }
            return false, 0;
        }
        return false, 0;
    }
}

// ------------------------------------------------------------ N_BUILTIN

recursive fn ex_builtin(n: u32, dst: u32) -> u32 {
    let nd = nodes[n];
    if nd.op == BI_IMAG_CONST {
        let re, im = ex_cplx(n);
        if dst != NONE { store_cplx(nd.ty, re, im, dst, false); }
        return NONE;
    }
    if nd.op == BI_BITCAST {
        let q = nd.ty;
        let tmp = alloca(type_size(q), type_align(q));
        store_any(nty(nd.a), nd.a, tmp);
        if vkind(q) == VK_AGG {
            if dst != NONE { mem_copy(dst, tmp, type_size(q), false); }
            return NONE;
        }
        if vkind(q) == VK_COMPLEX {
            if dst != NONE { mem_copy(dst, tmp, type_size(q), false); }
            return NONE;
        }
        return load_c(q, tmp, false);
    }
    if nd.op == BI_CONVERTVECTOR {
        let v = ex_val(nd.a);
        let st = nty(nd.a);
        let rq = nd.ty;
        let rt = vty(rq);
        let lanes = m_types[rt].n;
        var r = c_zero(rt);
        let se = tbase(st);
        let de = tbase(rq);
        for i in 0..lanes {
            let x = emit(GIR_EXTRACTELT, mty(se), 0, 0, vtype(v), v, c_i32(i as i64), 0);
            let y = conv(x, se, de);
            r = emit(GIR_INSERTELT, rt, 0, 0, 0, r, y, c_i32(i as i64));
        }
        return r;
    }
    let s = nd.a as i64;
    let full = sym_name(s);
    let name = strip_builtin(full);
    let r = lib_builtin(name, n, dst, true);
    if r != KEEP_CALL { return r; }
    return ex_builtin2(full, name, n, dst);
}

fn isfpclass(x: u32, mask: u32) -> u32 {
    var v = x;
    var t = vtype(v);
    if t == GIR_T_F16 { v = half_to_float(v); t = GIR_T_F32; }
    return emit(GIR_ISFPCLASS, GIR_T_I1, 0, 0, t, v, mask, 0);
}

fn fp_inf_const(t: u32) -> u32 {
    if t == GIR_T_F64 { return c_fp(0x7FF0000000000000, 0, t); }
    if t == GIR_T_F32 { return c_fp(0x7F800000, 0, t); }
    if t == GIR_T_F16 { return c_fp(0x7C00, 0, t); }
    return c_fp(0x8000000000000000, 0x7FFF, t);
}

fn fp_nan_const(t: u32, quiet: bool, payload: u64) -> u32 {
    if t == GIR_T_F64 {
        var m = payload & 0x7FFFFFFFFFFFF;
        if quiet { m = m | 0x8000000000000; } else if m == 0 { m = 1; }
        return c_fp(0x7FF0000000000000 | m, 0, t);
    }
    if t == GIR_T_F32 {
        var m = payload & 0x3FFFFF;
        if quiet { m = m | 0x400000; } else if m == 0 { m = 1; }
        return c_fp(0x7F800000 | m, 0, t);
    }
    if t == GIR_T_F16 { return c_fp(if quiet { 0x7E00 } else { 0x7D00 }, 0, t); }
    var m = payload & 0x3FFFFFFFFFFFFFFF;
    if quiet { m = m | 0x4000000000000000; } else if m == 0 { m = 1; }
    return c_fp(0x8000000000000000 | m, 0x7FFF, t);
}

// The NaN payload of __builtin_nan("...") (strtoull of the string).
fn nan_payload(a: u32) -> u64 {
    var m = a;
    loop {
        let nd = nodes[m];
        if (nd.kind == N_ICAST || nd.kind == N_CAST) && (nd.op == CK_ARRAY2PTR || nd.op == CK_NOOP || nd.op == CK_BITCAST) { m = nd.a; continue; }
        break;
    }
    if nodes[m].kind != N_STRING { return 0; }
    let sl = strs[nodes[m].a];
    let b = strbytes[sl.start..sl.start + sl.len];
    var v: u64 = 0;
    var i = 0;
    var base: u64 = 10;
    if b.len > 2 && b[0] == '0' && (b[1] == 'x' || b[1] == 'X') { base = 16; i = 2; }
    else if b.len > 1 && b[0] == '0' { base = 8; }
    while i < b.len && b[i] != 0 {
        let c = b[i];
        var d: u64 = 99;
        if c >= '0' && c <= '9' { d = (c - '0') as u64; }
        else if c >= 'a' && c <= 'f' { d = (c - 'a') as u64 + 10; }
        else if c >= 'A' && c <= 'F' { d = (c - 'A') as u64 + 10; }
        if d >= base { break; }
        v = v * base + d;
        i++;
    }
    return v;
}

fn fp_suffix_type(name: const u8[:], dflt: u32) -> u32 {
    if ends_with(name, "f") { return GIR_T_F32; }
    if ends_with(name, "l") { return GIR_T_F80; }
    if ends_with(name, "f16") { return GIR_T_F16; }
    return dflt;
}

recursive fn ex_builtin2(full: const u8[:], name: const u8[:], n: u32, dst: u32) -> u32 {
    let nd = nodes[n];
    let nargs = nd.c as i64;
    let rq = unqual(nd.ty);
    if name == "expect" || name == "expect_with_probability" || name == "assume_aligned" || name == "launder" ||
       name == "unpredictable" {
        let v = ex_val(barg(n, 0));
        for i in 1..nargs { ex_ignore(barg(n, i)); }
        return v;
    }
    if name == "prefetch" || name == "assume" || name == "va_end" || name == "__clear_cache" || name == "speculation_safe_value_dummy" {
        if name == "assume" { return NONE; }
        for i in nargs { let x = barg(n, i); if has_side_effects(x) { ex_ignore(x); } }
        return NONE;
    }
    if name == "unreachable" { emit_term(GIR_UNREACHABLE, 0, 0, 0); return NONE; }
    if name == "trap" || name == "debugtrap" {
        emit(if name == "trap" { GIR_TRAP } else { GIR_DEBUGTRAP }, GIR_T_VOID, 0, 0, 0, 0, 0, 0);
        if name == "trap" { emit_term(GIR_UNREACHABLE, 0, 0, 0); }
        return NONE;
    }
    if name == "return_address" || name == "frame_address" {
        let ok, lvl = fold_int(barg(n, 0));
        return emit(if name == "return_address" { GIR_RETADDR } else { GIR_FRAMEADDR }, GIR_T_PTR, 0, 0, 0, lvl as! u32, 0, 0);
    }
    if name == "extract_return_addr" || name == "frob_return_addr" { return ex_val(barg(n, 0)); }
    if name == "va_start" || name == "c23_va_start" {
        f_flags = f_flags | FN_VASTART;
        let ap = ex_val(barg(n, 0));
        emit(GIR_VASTART, GIR_T_VOID, 0, 0, 0, ap, 0, 0);
        return NONE;
    }
    if name == "va_copy" {
        let d = ex_val(barg(n, 0));
        let s = ex_val(barg(n, 1));
        mem_copy(d, s, 24, false);
        return NONE;
    }
    if name == "setjmp" {
        // clang: buf[0] = frame address, buf[2] = stack pointer, then the intrinsic
        f_flags = f_flags | FN_SJLJ;
        let buf = ex_val(barg(n, 0));
        let fa = emit(GIR_FRAMEADDR, GIR_T_PTR, 0, 0, 0, 0, 0, 0);
        ins_store(GIR_T_PTR, fa, buf, false);
        let sp = emit(GIR_STACKSAVE, GIR_T_PTR, 0, 0, 0, 0, 0, 0);
        ins_store(GIR_T_PTR, sp, gep(buf, 16), false);
        return emit(GIR_SJLJ_SETJMP, GIR_T_I32, 0, 0, 0, buf, 0, 0);
    }
    if name == "longjmp" {
        let buf = ex_val(barg(n, 0));
        ex_ignore(barg(n, 1));
        emit(GIR_SJLJ_LONGJMP, GIR_T_VOID, 0, 0, 0, buf, 0, 0);
        emit_term(GIR_UNREACHABLE, 0, 0, 0);
        return NONE;
    }
    if name == "alloca_with_align" || name == "alloca_uninitialized" || name == "alloca_with_align_uninitialized" {
        let sz = ex_val(barg(n, 0));
        var al: i64 = 16;
        if nargs > 1 { let ok, a = fold_int(barg(n, 1)); if ok { al = a / 8; } }
        if al < 16 { al = 16; }
        return emit(GIR_DYNALLOCA, GIR_T_PTR, 0, 0, 0, conv(sz, nty(barg(n, 0)), t_ulong), al as! u32, 0);
    }
    // bit operations
    if starts_with(name, "clz") || starts_with(name, "ctz") || starts_with(name, "popcount") || starts_with(name, "parity") ||
       starts_with(name, "ffs") || starts_with(name, "clrsb") || starts_with(name, "bswap") || starts_with(name, "bitreverse") ||
       name == "stdc_count_ones" {
        return bit_builtin(name, n);
    }
    if starts_with(name, "rotateleft") || starts_with(name, "rotateright") {
        let x = ex_val(barg(n, 0));
        let s = ex_val(barg(n, 1));
        let t = vtype(x);
        let sv = int_cast(s, vtype(s), t, false);
        return emit(if starts_with(name, "rotateleft") { GIR_FSHL } else { GIR_FSHR }, t, 0, 0, t, x, x, sv);
    }
    if ends_with(name, "_overflow") || ends_with(name, "_overflow_p") { return overflow_builtin(name, n); }
    // floating point
    if name == "inf" || name == "inff" || name == "infl" || name == "huge_val" || name == "huge_valf" || name == "huge_vall" ||
       name == "inff16" || name == "huge_valf16" {
        return fp_inf_const(vty(rq));
    }
    if name == "nan" || name == "nanf" || name == "nanl" || name == "nans" || name == "nansf" || name == "nansl" ||
       name == "nanf16" || name == "nansf16" {
        let quiet = !starts_with(name, "nans");
        return fp_nan_const(vty(rq), quiet, nan_payload(barg(n, 0)));
    }
    if name == "isnan" || name == "isinf" || name == "isfinite" || name == "isnormal" || name == "issubnormal" ||
       name == "iszero" || name == "issignaling" || name == "isfpclass" {
        let x = ex_val(barg(n, 0));
        var mask: u32 = 0;
        if name == "isnan" { mask = 3; } else if name == "isinf" { mask = 0x204; } else if name == "isfinite" { mask = 0x1F8; }
        else if name == "isnormal" { mask = 0x108; } else if name == "issubnormal" { mask = 0x90; } else if name == "iszero" { mask = 0x60; }
        else if name == "issignaling" { mask = 1; }
        else { let ok, m = fold_int(barg(n, 1)); mask = m as! u32; }
        let b = isfpclass(x, mask);
        return int_cast(b, GIR_T_I1, vty(rq), false);
    }
    if name == "isinf_sign" {
        let x = ex_val(barg(n, 0));
        let t = vtype(x);
        let isinf = isfpclass(x, 0x204);
        let neg = signbit_of(x);
        let s = ins_select(neg, c_i32(-1), c_i32(1));
        return ins_select(isinf, s, c_i32(0));
    }
    if name == "signbit" || name == "signbitf" || name == "signbitl" {
        let x = ex_val(barg(n, 0));
        let b = signbit_of(x);
        return int_cast(b, GIR_T_I1, vty(rq), false);
    }
    if name == "fpclassify" {
        // (nan, inf, normal, subnormal, zero, x)
        let x = ex_val(barg(n, 5));
        let vn = ex_val(barg(n, 0));
        let vi = ex_val(barg(n, 1));
        let vnorm = ex_val(barg(n, 2));
        let vsub = ex_val(barg(n, 3));
        let vz = ex_val(barg(n, 4));
        let isz = isfpclass(x, 0x60);
        let isn = isfpclass(x, 3);
        let isi = isfpclass(x, 0x204);
        let isnorm = isfpclass(x, 0x108);
        var r = ins_select(isnorm, vnorm, vsub);
        r = ins_select(isi, vi, r);
        r = ins_select(isn, vn, r);
        r = ins_select(isz, vz, r);
        return r;
    }
    if name == "isgreater" || name == "isgreaterequal" || name == "isless" || name == "islessequal" ||
       name == "islessgreater" || name == "isunordered" {
        let x = ex_val(barg(n, 0));
        let y = ex_val(barg(n, 1));
        let t = vtype(x);
        let p = if name == "isgreater" { F_OGT } else if name == "isgreaterequal" { F_OGE } else if name == "isless" { F_OLT }
            else if name == "islessequal" { F_OLE } else if name == "islessgreater" { F_ONE } else { F_UNO };
        let c = ins_fcmp(p, t, x, y);
        return int_cast(c, GIR_T_I1, vty(rq), false);
    }
    if name == "sqrt" || name == "sqrtf" || name == "sqrtl" {
        // __builtin_sqrt with math-errno: the libm call
        let x = ex_val(barg(n, 0));
        return libcall1(name, vtype(x), x);
    }
    if name == "complex" {
        let re = ex_val(barg(n, 0));
        let im = ex_val(barg(n, 1));
        if dst != NONE { store_cplx(rq, re, im, dst, false); }
        return NONE;
    }
    if name == "conj" || name == "conjf" || name == "conjl" {
        let re, im = ex_cplx(barg(n, 0));
        if dst != NONE { store_cplx(rq, re, neg_any(im), dst, false); }
        return NONE;
    }
    if name == "creal" || name == "crealf" || name == "creall" || name == "cimag" || name == "cimagf" || name == "cimagl" {
        let re, im = ex_cplx(barg(n, 0));
        return if starts_with(name, "creal") { re } else { im };
    }
    if name == "object_size" || name == "dynamic_object_size" {
        let ok, ty = fold_int(barg(n, 1));
        let p = barg(n, 0);
        let ok2, sz = object_size(p);
        if ok2 { return c_i64(sz); }
        if has_side_effects(p) { ex_ignore(p); }
        return c_i64(if ty >= 2 { 0 } else { -1 });
    }
    if starts_with(full, "__builtin___") && ends_with(name, "_chk") {
        return chk_builtin(name, n);
    }
    if name == "shufflevector" { return shuffle_builtin(n); }
    if starts_with(full, "__sync_") || starts_with(full, "__atomic_") || starts_with(full, "__c11_atomic_") {
        return atomic_builtin(full, n, dst);
    }
    if starts_with(name, "ia32_") { return x86_builtin(name, n); }
    if name == "classify_type" || name == "constant_p" { return c_int(0, vty(rq)); }
    // a library function under its __builtin_ name: call the library function
    if starts_with(full, "__builtin_") && builtin_index(intern(name)) >= 0 {
        return call_named(name, n, dst);
    }
    err_at(nd.loc, str("goosecc: unsupported builtin '", full, "'"));
    return if vkind(rq) == VK_SCALAR { c_zero(vty(rq)) } else { NONE };
}

fn signbit_of(x: u32) -> u32 {
    let t = vtype(x);
    if t == GIR_T_F64 {
        let i = ins_bitcast(x, GIR_T_I64);
        return ins_icmp(GIR_SLT, GIR_T_I64, i, c_i64(0));
    }
    if t == GIR_T_F32 {
        let i = ins_bitcast(x, GIR_T_I32);
        return ins_icmp(GIR_SLT, GIR_T_I32, i, c_i32(0));
    }
    if t == GIR_T_F16 {
        let i = ins_bitcast(x, GIR_T_I16);
        return ins_icmp(GIR_SLT, GIR_T_I16, i, c_int(0, GIR_T_I16));
    }
    // f80: the sign is bit 79
    let tmp = alloca(16, 16);
    ins_store(GIR_T_F80, x, tmp, false);
    let hi = ins_load(GIR_T_I16, gep(tmp, 8), false);
    return ins_icmp(GIR_SLT, GIR_T_I16, hi, c_int(0, GIR_T_I16));
}

// __builtin_object_size of a pointer into a known object (as LLVM's -O0
// lowerObjectSizeCall finds it).
recursive fn object_size(p: u32) -> bool, i64 {
    let ok, t, a, l1, l2 = eval_addr_noemit(p);
    if !ok || t < 0 { return false, 0; }
    let s = glob_sym[t];
    var size: i64 = -1;
    if s >= 0 { size = type_size(syms[s].ty); }
    else { size = m_globals[t].size as i64; }
    if size < 0 || a > size || a < 0 { return false, 0; }
    return true, size - a;
}

fn eval_addr_noemit(p: u32) -> bool, i64, i64, i64, i64 {
    // only for decayed arrays of objects with static storage
    var m = p;
    loop {
        let nd = nodes[m];
        if (nd.kind == N_ICAST || nd.kind == N_CAST) && (nd.op == CK_NOOP || nd.op == CK_BITCAST) { m = nd.a; continue; }
        break;
    }
    let nd = nodes[m];
    if (nd.kind == N_ICAST || nd.kind == N_CAST) && nd.op == CK_ARRAY2PTR && nodes[nd.a].kind == N_DECLREF {
        let s = nodes[nd.a].a as i64;
        if sym_addr.len > s && sym_addr[s] != NONE {
            return false, -1, 0, -1, -1;
        }
    }
    return false, -1, 0, -1, -1;
}

recursive fn chk_builtin(name: const u8[:], n: u32) -> u32 {
    // __builtin___memcpy_chk(d, s, n, os): the plain function if the size is
    // known to fit (or os is -1), else the checking function
    let nd = nodes[n];
    let nargs = nd.c as i64;
    let base = name[2..name.len - 4];   // "memcpy"
    let ok, os = fold_int(barg(n, nargs - 1));
    var fits = ok && os == -1;
    if ok && !fits && nargs >= 4 {
        let ok2, len = fold_int(barg(n, 2));
        if ok2 && len <= os && len >= 0 { fits = true; }
    }
    if fits && (base == "memcpy" || base == "memmove" || base == "memset" || base == "mempcpy") {
        let d = ex_val(barg(n, 0));
        let s = ex_val(barg(n, 1));
        let ln = conv(ex_val(barg(n, 2)), nty(barg(n, 2)), t_ulong);
        ex_ignore(barg(n, 3));
        if base == "memset" {
            let b = int_cast(s, vtype(s), GIR_T_I8, false);
            if is_const(ln) && c_lo(ln) <= 256 { mem_set(d, b, c_lo(ln) as! i64, false); }
            else { libcall3("memset", GIR_T_PTR, d, ins_zext(b, GIR_T_I32), ln); }
            return d;
        }
        if base == "memcpy" && is_const(ln) && c_lo(ln) <= 256 { mem_copy(d, s, c_lo(ln) as! i64, false); return d; }
        return libcall3(base, GIR_T_PTR, d, s, ln);
    }
    if fits {
        // the other _chk functions: call the plain one without the size
        return call_named_n(base, n, nargs - 1);
    }
    return call_named(name, n, NONE);
}

// Calls the library function `name` with the builtin call's arguments.
recursive fn call_named(name: const u8[:], n: u32, dst: u32) -> u32 { call_named_n(name, n, nodes[n].c as i64) }

recursive fn call_named_n(name: const u8[:], n: u32, nargs: i64) -> u32 {
    let nd = nodes[n];
    let id = intern(name);
    let g = global_by_name(id, true);
    let rq = unqual(nd.ty);
    let ra = ret_abi(rq);
    abi_start(ra);
    let mark = call_vals.len;
    let amark = cabis.len;
    for i in nargs { cabis.push(arg_abi(nty(barg(n, i)))); }
    var sret: u32 = NONE;
    if ra.kind == AK_SRET {
        sret = alloca(type_size(rq), type_align(rq));
        call_vals.push(sret);
        call_vals.push(ABI_SRET);
    }
    for i in nargs { push_arg(barg(n, i), cabis[amark + i]); }
    cabis.resize(amark);
    let rt = if ra.kind == AK_SRET { GIR_T_VOID } else { ret_gir_type(ra) };
    let s = m_opnds.len as! u32;
    let cnt = (call_vals.len - mark) / 2;
    for i in cnt {
        op_ref(call_vals[mark + 2 * i]);
        op_imm(call_vals[mark + 2 * i + 1]);
    }
    call_vals.resize(mark);
    // variadic library functions (printf & co.) need al
    let bt = types[syms[nd.a].ty >> 4];
    let fl: u32 = if bt.flags & (TF_VARIADIC | TF_NOPROTO) != 0 { IF_VARARG } else { 0 };
    let r = emit(GIR_CALL, rt, 0, fl, 0, gref(g), s, cnt as! u32);
    if syms[nd.a].flags & SF_NORETURN != 0 { emit_term(GIR_UNREACHABLE, 0, 0, 0); }
    if ra.kind == AK_DIRECT { return r; }
    return NONE;
}

// ------------------------------------------------------------ bit operations

recursive fn bit_builtin(name: const u8[:], n: u32) -> u32 {
    let nd = nodes[n];
    let rq = unqual(nd.ty);
    let x = ex_val(barg(n, 0));
    let t = vtype(x);
    let rt = vty(rq);
    if starts_with(name, "bswap") { return emit(GIR_BSWAP, t, 0, 0, t, x, 0, 0); }
    if starts_with(name, "bitreverse") { return emit(GIR_BITREVERSE, t, 0, 0, t, x, 0, 0); }
    if starts_with(name, "clzg") || starts_with(name, "ctzg") {
        let clz = starts_with(name, "clz");
        let r = emit(if clz { GIR_CTLZ } else { GIR_CTTZ }, t, 0, 0, t, x, if nodes[n].c > 1 { 0 } else { 1 }, 0);
        let rr = int_cast(r, t, rt, false);
        if nodes[n].c > 1 {
            let fb = ex_val(barg(n, 1));
            let z = ins_icmp(GIR_EQ, t, x, c_zero(t));
            return ins_select(z, conv(fb, nty(barg(n, 1)), rq), rr);
        }
        return rr;
    }
    if starts_with(name, "clz") {
        let r = emit(GIR_CTLZ, t, 0, 0, t, x, 1, 0);
        return int_cast(r, t, rt, false);
    }
    if starts_with(name, "ctz") {
        let r = emit(GIR_CTTZ, t, 0, 0, t, x, 1, 0);
        return int_cast(r, t, rt, false);
    }
    if starts_with(name, "popcount") || name == "stdc_count_ones" {
        let r = emit(GIR_CTPOP, t, 0, 0, t, x, 0, 0);
        return int_cast(r, t, rt, false);
    }
    if starts_with(name, "parity") {
        let r = emit(GIR_CTPOP, t, 0, 0, t, x, 0, 0);
        let b = ins_bin(GIR_AND, t, r, c_int(1, t));
        return int_cast(b, t, rt, false);
    }
    if starts_with(name, "ffs") {
        let tz = emit(GIR_CTTZ, t, 0, 0, t, x, 1, 0);
        let p1 = ins_bin(GIR_ADD, t, tz, c_int(1, t));
        let z = ins_icmp(GIR_EQ, t, x, c_zero(t));
        let r = ins_select(z, c_zero(t), p1);
        return int_cast(r, t, rt, false);
    }
    if starts_with(name, "clrsb") {
        let bits = tbits(t) as i64;
        let sh = ins_bin(GIR_ASHR, t, x, c_int((bits - 1) as! u64, t));
        let y = ins_bin(GIR_XOR, t, x, sh);
        let lz = emit(GIR_CTLZ, t, 0, 0, t, y, 0, 0);
        let r = ins_bin(GIR_SUB, t, lz, c_int(1, t));
        return int_cast(r, t, rt, false);
    }
    return c_zero(rt);
}

// __builtin_{add,sub,mul}_overflow (and the typed s/u variants).
recursive fn overflow_builtin(name: const u8[:], n: u32) -> u32 {
    let nd = nodes[n];
    let is_p = ends_with(name, "_overflow_p");
    let a0 = barg(n, 0);
    let a1 = barg(n, 1);
    let a2 = barg(n, 2);
    var opk: i64 = 0;   // 0 add, 1 sub, 2 mul
    var base = name;
    if starts_with(base, "s") || starts_with(base, "u") {
        // sadd_overflow, uaddl_overflow, ...
        base = base[1..];
    }
    if starts_with(base, "add") { opk = 0; } else if starts_with(base, "sub") { opk = 1; } else { opk = 2; }
    let qa = nty(a0);
    let qb = nty(a1);
    // the result type: the pointee of the third argument (or its type for _p)
    let qr = if is_p { unqual(nty(a2)) } else { unqual(tbase(nty(a2))) };
    let xa = ex_val(a0);
    let xb = ex_val(a1);
    var pres: u32 = NONE;
    if is_p { ex_ignore(a2); } else { pres = ex_val(a2); }
    let sa = is_signed(qa);
    let sb = is_signed(qb);
    let sr = is_signed(qr);
    let wa = tbits(vtype(xa)) as i64;
    let wb = tbits(vtype(xb)) as i64;
    let wr = tbits(vty(qr)) as i64;
    let rt = vty(qr);
    if vtype(xa) == rt && vtype(xb) == rt && sa == sb && sb == sr {
        let k = if opk == 0 { if sr { OVF_SADD } else { OVF_UADD } } else if opk == 1 { if sr { OVF_SSUB } else { OVF_USUB } }
            else { if sr { OVF_SMUL } else { OVF_UMUL } };
        let st = ty_pair(rt, GIR_T_I1, tsize(rt));
        let r = emit(GIR_OVF, st, k, 0, rt, xa, xb, 0);
        let v = emit(GIR_EXTRACTVALUE, rt, 0, 0, 0, r, 0, 0);
        let o = emit(GIR_EXTRACTVALUE, GIR_T_I1, 0, 0, 0, r, tsize(rt), 0);
        if !is_p { store_c(qr, v, pres, false); }
        return int_cast(o, GIR_T_I1, vty(nd.ty), false);
    }
    // mixed types: compute exactly in a wide signed type, then check the range
    var w: i64 = wa;
    if wb > w { w = wb; }
    if wr > w { w = wr; }
    let any_signed = sa || sb || sr;
    var ew = w;
    if any_signed && (!sa || !sb || !sr) { ew = w + 1; }
    if opk == 2 { ew = wa + wb + 1; }
    var et: u32 = GIR_T_I128;
    if ew <= 64 { et = GIR_T_I64; }
    let ea = int_cast(xa, vtype(xa), et, sa);
    let eb = int_cast(xb, vtype(xb), et, sb);
    var ovf: u32 = c_false();
    var r: u32 = 0;
    if ew > 128 {
        // 128-bit operands: use the overflow op of i128 directly (signed)
        let k = if opk == 0 { OVF_SADD } else if opk == 1 { OVF_SSUB } else { OVF_SMUL };
        let k2 = if sa || sb { k } else { if opk == 0 { OVF_UADD } else if opk == 1 { OVF_USUB } else { OVF_UMUL } };
        let st = ty_pair(et, GIR_T_I1, 16);
        let rr = emit(GIR_OVF, st, k2, 0, et, ea, eb, 0);
        r = emit(GIR_EXTRACTVALUE, et, 0, 0, 0, rr, 0, 0);
        ovf = emit(GIR_EXTRACTVALUE, GIR_T_I1, 0, 0, 0, rr, 16, 0);
    } else {
        let gop = if opk == 0 { GIR_ADD } else if opk == 1 { GIR_SUB } else { GIR_MUL };
        if et == GIR_T_I128 && opk == 2 {
            let st = ty_pair(et, GIR_T_I1, 16);
            let rr = emit(GIR_OVF, st, OVF_SMUL, 0, et, ea, eb, 0);
            r = emit(GIR_EXTRACTVALUE, et, 0, 0, 0, rr, 0, 0);
            ovf = emit(GIR_EXTRACTVALUE, GIR_T_I1, 0, 0, 0, rr, 16, 0);
        } else {
            r = ins_bin(gop, et, ea, eb);
        }
    }
    // does r fit the result type?
    let tr = int_cast(r, et, rt, false);
    let back = int_cast(tr, rt, et, sr);
    let ne = ins_icmp(GIR_NE, et, back, r);
    var o2 = ins_bin(GIR_OR, GIR_T_I1, ovf, ne);
    if !sr {
        // an unsigned result: negative values do not fit
        let neg = ins_icmp(GIR_SLT, et, r, c_zero(et));
        if any_signed { o2 = ins_bin(GIR_OR, GIR_T_I1, o2, neg); }
    }
    if !is_p { store_c(qr, tr, pres, false); }
    return int_cast(o2, GIR_T_I1, vty(nd.ty), false);
}

recursive fn shuffle_builtin(n: u32) -> u32 {
    let nd = nodes[n];
    let a = ex_val(barg(n, 0));
    let b = ex_val(barg(n, 1));
    let rt = vty(unqual(nd.ty));
    let s = m_opnds.len as! u32;
    let cnt = nd.c as i64 - 2;
    for i in cnt {
        let ok, v = fold_int(barg(n, 2 + i));
        if !ok || v < 0 { op_imm(NONE); } else { op_imm(v as! u32); }
    }
    return emit(GIR_SHUFFLE, rt, 0, 0, vtype(a), a, b, s);
}

recursive fn x86_builtin(name: const u8[:], n: u32) -> u32 {
    let nd = nodes[n];
    let rq = unqual(nd.ty);
    let rt = vty(rq);
    var k: i64 = -1;
    if name == "ia32_maxps" { k = X86_MAXPS; } else if name == "ia32_minps" { k = X86_MINPS; }
    else if name == "ia32_movmskps" { k = X86_MOVMSKPS; } else if name == "ia32_packssdw128" { k = X86_PACKSSDW; }
    else if name == "ia32_psllwi128" { k = X86_PSLLIW; } else if name == "ia32_psrlwi128" { k = X86_PSRLIW; }
    else if name == "ia32_psrawi128" { k = X86_PSRAIW; } else if name == "ia32_pslldi128" { k = X86_PSLLID; }
    else if name == "ia32_psrldi128" { k = X86_PSRLID; } else if name == "ia32_psradi128" { k = X86_PSRAID; }
    if k >= 0 {
        let a = ex_val(barg(n, 0));
        var b: u32 = 0;
        if nd.c > 1 {
            b = ex_val(barg(n, 1));
            if k >= X86_PSLLIW { b = int_cast(b, vtype(b), GIR_T_I32, false); }
        }
        return emit(GIR_X86, rt, k as! u32, 0, vtype(a), a, b, 0);
    }
    if name == "ia32_vec_ext_v4si" || name == "ia32_vec_ext_v2di" || name == "ia32_vec_ext_v4sf" || name == "ia32_vec_ext_v8hi" ||
       name == "ia32_vec_ext_v16qi" {
        let v = ex_val(barg(n, 0));
        let ok, i = fold_int(barg(n, 1));
        let lanes = m_types[vtype(v)].n as i64;
        let e = emit(GIR_EXTRACTELT, m_types[vtype(v)].elems, 0, 0, vtype(v), v, c_i32(i % lanes), 0);
        return int_cast(e, vtype(e), rt, false);
    }
    err_at(nd.loc, str("goosecc: unsupported builtin '__builtin_", name, "'"));
    return c_zero(rt);
}

// ------------------------------------------------------------ atomics

fn ord_flags(o: i64) -> u32 {
    // C ABI memory orders -> LLVM orderings
    let lo = match o { 0 => 2, 1 => 4, 2 => 4, 3 => 5, 4 => 6, _ => 7 };
    return (lo as! u32) << IF_ORD_SHIFT;
}

fn atomic_order(n: u32) -> u32 {
    let ok, o = fold_int(n);
    if !ok { return ord_flags(5); }
    return ord_flags(o);
}

fn atomic_load_lv(l: LV, q: u32) -> u32 {
    let t = mty(q);
    if tcls(t) == C_INT || tcls(t) == C_FP {
        let v = emit(GIR_LOAD, t, 0, ord_flags(5) | (if l.vol { IF_VOLATILE } else { 0 }), 0, l.addr, 0, 0);
        if kind_of(q) == TY_BOOL { return int_cast(v, GIR_T_I8, GIR_T_I1, false); }
        return v;
    }
    return lv_load(l);
}

fn atomic_store_lv(l: LV, q: u32, v: u32) {
    let t = mty(q);
    var x = v;
    if kind_of(q) == TY_BOOL { x = int_cast(v, vtype(v), GIR_T_I8, false); }
    if tcls(t) == C_INT || tcls(t) == C_FP {
        emit(GIR_STORE, GIR_T_VOID, 0, ord_flags(5) | (if l.vol { IF_VOLATILE } else { 0 }), t, x, l.addr, 0);
        return;
    }
    lv_store(l, v);
}

// ++ / -- on an _Atomic lvalue.
fn atomic_incdec(l: LV, q: u32, inc: bool, post: bool) -> u32 {
    let t = mty(q);
    if kind_of(q) == TY_POINTER {
        let ok, es, ev = elem_size(tbase(q));
        let d = c_i64(if inc { es } else { -es });
        let old = emit(GIR_ATOMICRMW, GIR_T_I64, RMW_ADD, ord_flags(5), GIR_T_I64, l.addr, d, 0);
        let nv = ins_bin(GIR_ADD, GIR_T_I64, old, d);
        return ins_inttoptr(if post { old } else { nv });
    }
    if tcls(t) == C_INT && kind_of(q) != TY_BOOL {
        let one = c_int(1, t);
        let old = emit(GIR_ATOMICRMW, t, if inc { RMW_ADD } else { RMW_SUB }, ord_flags(5), t, l.addr, one, 0);
        if post { return old; }
        return ins_bin(if inc { GIR_ADD } else { GIR_SUB }, t, old, one);
    }
    // a compare-exchange loop (floats, bool)
    let old0 = atomic_load_lv(l, q);
    let loop_b = new_block();
    let done = new_block();
    let pre = cur_blk;
    br(loop_b);
    start_block(loop_b);
    let s = m_opnds.len as! u32;
    op_ref(old0);
    op_blk(pre as! u32);
    let phi_at = m_opnds.len;
    op_imm(0);
    op_imm(0);
    let cur = emit(GIR_PHI, vtype(old0), 0, 0, 0, 0, s, 2);
    var nv: u32 = 0;
    let vt = vtype(cur);
    if tcls(vt) == C_FP || tcls(vt) == C_X87 { nv = ins_fbin(if inc { GIR_FADD } else { GIR_FSUB }, vt, cur, c_double(1.0, vt)); }
    else if kind_of(q) == TY_BOOL { nv = if inc { c_true() } else { ins_bin(GIR_XOR, GIR_T_I1, cur, c_true()) }; }
    else { nv = ins_bin(if inc { GIR_ADD } else { GIR_SUB }, vt, cur, c_int(1, vt)); }
    let ok_v, got = cmpxchg_value(l.addr, q, cur, nv);
    // patch the back-edge value of the PHI to the value read
    m_opnds[phi_at] = got;
    if is_local(got) { f_ofix.push(phi_at as! u32); }
    m_opnds[phi_at + 1] = cur_blk as! u32;
    f_bfix.push((phi_at + 1) as! u32);
    condbr(ok_v, done, loop_b);
    start_block(done);
    return if post { cur } else { nv };
}

// cmpxchg of a C scalar (through its integer bits); returns (success, old value).
fn cmpxchg_value(p: u32, q: u32, expected: u32, nv: u32) -> u32, u32 {
    let t = mty(q);
    var it = t;
    if tcls(t) != C_INT { it = ty_int(tsize(t) * 8); }
    var e = expected;
    var x = nv;
    if kind_of(q) == TY_BOOL { e = int_cast(e, GIR_T_I1, GIR_T_I8, false); x = int_cast(x, GIR_T_I1, GIR_T_I8, false); }
    if it != t { e = ins_bitcast(e, it); x = ins_bitcast(x, it); }
    let st = ty_pair(it, GIR_T_I1, tsize(it));
    let fl = ord_flags(5) | ((7 as u32) << 4);
    let r = emit(GIR_CMPXCHG, st, 0, fl, it, p, e, x);
    var old = emit(GIR_EXTRACTVALUE, it, 0, 0, 0, r, 0, 0);
    let ok = emit(GIR_EXTRACTVALUE, GIR_T_I1, 0, 0, 0, r, tsize(it), 0);
    if it != t { old = ins_bitcast(old, t); }
    if kind_of(q) == TY_BOOL { old = int_cast(old, GIR_T_I8, GIR_T_I1, false); }
    return ok, old;
}

// x op= y on an _Atomic lvalue.
recursive fn atomic_compound(n: u32) -> u32 {
    let nd = nodes[n];
    let lq = unqual(nty(nd.a));
    let ct = nd.c;
    let op = nd.op as i64;
    let rhs = ex_val(nd.b);
    let l = ex_lv(nd.a);
    let t = mty(lq);
    if tcls(t) == C_INT && kind_of(lq) != TY_BOOL && ct == lq && (op == B_ADD || op == B_SUB || op == B_AND || op == B_OR || op == B_XOR) {
        let k = match op { B_ADD => RMW_ADD, B_SUB => RMW_SUB, B_AND => RMW_AND, B_OR => RMW_OR, _ => RMW_XOR };
        let old = emit(GIR_ATOMICRMW, t, k, ord_flags(5), t, l.addr, rhs, 0);
        return arith(op, ct, old, rhs);
    }
    if kind_of(lq) == TY_POINTER && (op == B_PTRADD || op == B_PTRSUB) {
        let ok, es, ev = elem_size(tbase(lq));
        let i = int_cast(rhs, vtype(rhs), GIR_T_I64, is_signed(nty(nd.b)));
        var d = ins_bin(GIR_MUL, GIR_T_I64, i, c_i64(es));
        if op == B_PTRSUB { d = ins_bin(GIR_SUB, GIR_T_I64, c_i64(0), d); }
        let old = emit(GIR_ATOMICRMW, GIR_T_I64, RMW_ADD, ord_flags(5), GIR_T_I64, l.addr, d, 0);
        return ins_inttoptr(ins_bin(GIR_ADD, GIR_T_I64, old, d));
    }
    // a compare-exchange loop
    let old0 = atomic_load_lv(l, lq);
    let loop_b = new_block();
    let done = new_block();
    let pre = cur_blk;
    br(loop_b);
    start_block(loop_b);
    let s = m_opnds.len as! u32;
    op_ref(old0);
    op_blk(pre as! u32);
    let phi_at = m_opnds.len;
    op_imm(0);
    op_imm(0);
    let cur = emit(GIR_PHI, vtype(old0), 0, 0, 0, 0, s, 2);
    var r: u32 = 0;
    if op == B_PTRADD || op == B_PTRSUB { r = ptr_add(cur, tbase(lq), rhs, nty(nd.b), op == B_PTRSUB); }
    else {
        let ov = conv(cur, lq, ct);
        r = conv(arith(op, ct, ov, rhs), ct, lq);
    }
    let okv, got = cmpxchg_value(l.addr, lq, cur, r);
    m_opnds[phi_at] = got;
    if is_local(got) { f_ofix.push(phi_at as! u32); }
    m_opnds[phi_at + 1] = cur_blk as! u32;
    f_bfix.push((phi_at + 1) as! u32);
    condbr(okv, done, loop_b);
    start_block(done);
    return r;
}

recursive fn atomic_builtin(full: const u8[:], n: u32, dst: u32) -> u32 {
    let nd = nodes[n];
    let nargs = nd.c as i64;
    let rq = unqual(nd.ty);
    if full == "__sync_synchronize" || full == "__atomic_thread_fence" || full == "__c11_atomic_thread_fence" {
        var fl = ord_flags(5);
        if nargs > 0 { fl = atomic_order(barg(n, 0)); }
        emit(GIR_FENCE, GIR_T_VOID, 0, fl, 0, 0, 0, 0);
        return NONE;
    }
    if full == "__atomic_signal_fence" || full == "__c11_atomic_signal_fence" {
        emit(GIR_FENCE, GIR_T_VOID, 0, atomic_order(barg(n, 0)) | IF_SINGLETHREAD, 0, 0, 0, 0);
        return NONE;
    }
    if ends_with(full, "is_lock_free") || ends_with(full, "always_lock_free") {
        let ok, sz = fold_int(barg(n, 0));
        let lf = ok && (sz == 1 || sz == 2 || sz == 4 || sz == 8);
        return c_int(if lf { 1 } else { 0 }, vty(rq));
    }
    let sync = starts_with(full, "__sync_");
    let code, rmw_k, fetch_first = atomic_code(full);
    if code < 0 {
        err_at(nd.loc, str("goosecc: unsupported builtin '", full, "'"));
        return c_zero(GIR_T_I32);
    }
    let p = ex_val(barg(n, 0));
    let pq = unqual(tbase(nty(barg(n, 0))));
    let vt0 = mty(pq);
    var t = vt0;
    if kind_of(pq) == TY_POINTER { t = GIR_T_I64; }
    // the value operand (pointer-sized for pointers)
    if code == AT_LOAD_N || code == AT_LOAD {
        let ord = if nargs > 1 { atomic_order(barg(n, nargs - 1)) } else { ord_flags(5) };
        let v = emit(GIR_LOAD, vt0, 0, ord, 0, p, 0, 0);
        if code == AT_LOAD {
            let r = ex_val(barg(n, 1));
            ins_store(vt0, v, r, false);
            return NONE;
        }
        if kind_of(pq) == TY_BOOL { return int_cast(v, GIR_T_I8, GIR_T_I1, false); }
        return v;
    }
    if code == AT_STORE_N || code == AT_STORE || code == AT_INIT || code == AT_CLEAR || code == AT_LOCK_RELEASE {
        var v: u32 = 0;
        var ord = ord_flags(5);
        if code == AT_CLEAR || code == AT_LOCK_RELEASE {
            v = c_int(0, if code == AT_CLEAR { GIR_T_I8 } else { vt0 });
            if code == AT_CLEAR && nargs > 1 { ord = atomic_order(barg(n, 1)); }
            if code == AT_LOCK_RELEASE { ord = ord_flags(3); }
            emit(GIR_STORE, GIR_T_VOID, 0, ord, vtype(v), v, p, 0);
            return NONE;
        }
        if code == AT_STORE {
            let src = ex_val(barg(n, 1));
            v = ins_load(vt0, src, false);
        } else {
            v = ex_val(barg(n, 1));
            v = conv(v, nty(barg(n, 1)), pq);
            if kind_of(pq) == TY_BOOL { v = int_cast(v, GIR_T_I1, GIR_T_I8, false); }
        }
        if nargs > 2 { ord = atomic_order(barg(n, 2)); }
        if code == AT_INIT { ord = 0; }
        emit(GIR_STORE, GIR_T_VOID, 0, ord, vt0, v, p, 0);
        return NONE;
    }
    if code == AT_TAS {
        let old = emit(GIR_ATOMICRMW, GIR_T_I8, RMW_XCHG, if nargs > 1 { atomic_order(barg(n, 1)) } else { ord_flags(5) }, GIR_T_I8, p, c_i8(1), 0);
        let b = ins_icmp(GIR_NE, GIR_T_I8, old, c_i8(0));
        return int_cast(b, GIR_T_I1, vty(rq), false);
    }
    if code == AT_XCHG_N || code == AT_XCHG || code == AT_LOCK_TAS {
        var v: u32 = 0;
        if code == AT_XCHG { v = ins_load(vt0, ex_val(barg(n, 1)), false); }
        else { v = conv(ex_val(barg(n, 1)), nty(barg(n, 1)), pq); }
        var x = v;
        if kind_of(pq) == TY_POINTER { x = ins_ptrtoint(v, GIR_T_I64); }
        if kind_of(pq) == TY_BOOL { x = int_cast(v, GIR_T_I1, GIR_T_I8, false); t = GIR_T_I8; }
        let ord = if code == AT_LOCK_TAS { ord_flags(2) } else if nargs > 2 { atomic_order(barg(n, nargs - 1)) } else { ord_flags(5) };
        var old = emit(GIR_ATOMICRMW, t, RMW_XCHG, ord, t, p, x, 0);
        if kind_of(pq) == TY_POINTER { old = ins_inttoptr(old); }
        if code == AT_XCHG {
            ins_store(vt0, old, ex_val(barg(n, 2)), false);
            return NONE;
        }
        if kind_of(pq) == TY_BOOL { return int_cast(old, GIR_T_I8, GIR_T_I1, false); }
        return old;
    }
    if code == AT_CAS {
        var expected: u32 = 0;
        var desired: u32 = 0;
        var exp_p: u32 = NONE;
        var it = t;
        if tcls(vt0) != C_INT { it = ty_int(tsize(vt0) * 8); }
        if sync {
            expected = conv(ex_val(barg(n, 1)), nty(barg(n, 1)), pq);
            desired = conv(ex_val(barg(n, 2)), nty(barg(n, 2)), pq);
        } else {
            exp_p = ex_val(barg(n, 1));
            expected = ins_load(it, exp_p, false);
            if rmw_k == 1 { desired = ins_load(it, ex_val(barg(n, 2)), false); }
            else { desired = conv(ex_val(barg(n, 2)), nty(barg(n, 2)), pq); }
        }
        if kind_of(pq) == TY_POINTER { if vtype(expected) == GIR_T_PTR { expected = ins_ptrtoint(expected, GIR_T_I64); } desired = ins_ptrtoint(desired, GIR_T_I64); }
        if vtype(expected) != it { expected = ins_bitcast(expected, it); }
        if vtype(desired) != it { desired = int_cast(desired, vtype(desired), it, false); }
        var fl = ord_flags(5) | ((7 as u32) << 4);
        if !sync && nargs >= 6 {
            let so = atomic_order(barg(n, 4));
            var fo = atomic_order(barg(n, 5)) >> IF_ORD_SHIFT;
            if fo == 5 || fo == 6 { fo = 2; }
            fl = so | (fo << 4);
            let ok, w = fold_int(barg(n, 3));
            if ok && w != 0 { fl = fl | 0x80; }
        }
        let st = ty_pair(it, GIR_T_I1, tsize(it));
        let r = emit(GIR_CMPXCHG, st, 0, fl, it, p, expected, desired);
        let old = emit(GIR_EXTRACTVALUE, it, 0, 0, 0, r, 0, 0);
        let ok = emit(GIR_EXTRACTVALUE, GIR_T_I1, 0, 0, 0, r, tsize(it), 0);
        if rmw_k == 2 {
            if kind_of(pq) == TY_POINTER { return ins_inttoptr(old); }
            return old;
        }
        if !sync {
            // on failure, the old value is written back to *expected
            let wb = new_block();
            let cont = new_block();
            condbr(ok, cont, wb);
            start_block(wb);
            ins_store(it, old, exp_p, false);
            br(cont);
            start_block(cont);
        }
        return int_cast(ok, GIR_T_I1, vty(rq), false);
    }
    let k = rmw_k;
    var v = ex_val(barg(n, 1));
    var kk = k;
    if kind_of(pq) == TY_POINTER {
        // pointer arithmetic: GNU atomics on pointers add bytes for __atomic, elements for __sync
        v = int_cast(v, vtype(v), GIR_T_I64, is_signed(nty(barg(n, 1))));
        if !sync {
            // __atomic_fetch_add on a pointer adds bytes
        } else {
            let ok, es, ev = elem_size(tbase(pq));
            if es != 1 { v = ins_bin(GIR_MUL, GIR_T_I64, v, c_i64(es)); }
        }
    } else {
        v = conv(v, nty(barg(n, 1)), pq);
        if kk == RMW_MAX && !is_signed(pq) { kk = RMW_UMAX; }
        if kk == RMW_MIN && !is_signed(pq) { kk = RMW_UMIN; }
    }
    let ord = if !sync && nargs > 2 { atomic_order(barg(n, 2)) } else { ord_flags(5) };
    if tcls(t) == C_FP && (kk == RMW_ADD || kk == RMW_SUB) { kk = if kk == RMW_ADD { RMW_FADD } else { RMW_FSUB }; }
    let old = emit(GIR_ATOMICRMW, t, kk as! u32, ord, t, p, v, 0);
    var res = old;
    if !fetch_first {
        if kk == RMW_NAND {
            let a = ins_bin(GIR_AND, t, old, v);
            res = ins_bin(GIR_XOR, t, a, c_int(0xFFFFFFFFFFFFFFFF, t));
        } else if kk == RMW_MAX || kk == RMW_UMAX || kk == RMW_MIN || kk == RMW_UMIN {
            let pr = if kk == RMW_MAX { GIR_SGT } else if kk == RMW_UMAX { GIR_UGT } else if kk == RMW_MIN { GIR_SLT } else { GIR_ULT };
            let c = ins_icmp(pr, t, old, v);
            res = ins_select(c, old, v);
        } else if kk == RMW_FADD || kk == RMW_FSUB {
            res = ins_fbin(if kk == RMW_FADD { GIR_FADD } else { GIR_FSUB }, t, old, v);
        } else {
            let gop = match kk { RMW_ADD => GIR_ADD, RMW_SUB => GIR_SUB, RMW_AND => GIR_AND, RMW_OR => GIR_OR, _ => GIR_XOR };
            res = ins_bin(gop, t, old, v);
        }
    }
    if kind_of(pq) == TY_POINTER { return ins_inttoptr(res); }
    return res;
}

let AT_LOAD_N = 1;
let AT_LOAD = 2;
let AT_STORE_N = 3;
let AT_STORE = 4;
let AT_INIT = 5;
let AT_CLEAR = 6;
let AT_LOCK_RELEASE = 7;
let AT_TAS = 8;
let AT_XCHG_N = 9;
let AT_XCHG = 10;
let AT_LOCK_TAS = 11;
let AT_CAS = 12;
let AT_RMW = 13;

// Decodes an atomic builtin's name: (kind, RMW op or CAS variant, fetch first).
// CAS variants: 1 = the generic __atomic_compare_exchange (pointer to the
// desired value), 2 = __sync_val_compare_and_swap.
fn atomic_code(full: const u8[:]) -> i64, i64, bool {
    var name = full;
    if starts_with(full, "__sync_") { name = full[7..]; }
    else if starts_with(full, "__atomic_") { name = full[9..]; }
    else if starts_with(full, "__c11_atomic_") { name = full[13..]; }
    if name == "load_n" { return AT_LOAD_N, 0, false; }
    if name == "load" { return AT_LOAD, 0, false; }
    if name == "store_n" { return AT_STORE_N, 0, false; }
    if name == "store" { return AT_STORE, 0, false; }
    if name == "init" { return AT_INIT, 0, false; }
    if name == "clear" { return AT_CLEAR, 0, false; }
    if name == "lock_release" { return AT_LOCK_RELEASE, 0, false; }
    if name == "test_and_set" { return AT_TAS, 0, false; }
    if name == "exchange_n" { return AT_XCHG_N, 0, false; }
    if name == "exchange" { return AT_XCHG, 0, false; }
    if name == "lock_test_and_set" { return AT_LOCK_TAS, 0, false; }
    if name == "compare_exchange" { return AT_CAS, 1, false; }
    if name == "val_compare_and_swap" { return AT_CAS, 2, false; }
    if name == "compare_exchange_n" || name == "compare_exchange_strong" || name == "compare_exchange_weak" ||
       name == "bool_compare_and_swap" { return AT_CAS, 0, false; }
    var fetch_first = false;
    var opname = name;
    if starts_with(name, "fetch_and_") { fetch_first = true; opname = name[10..]; }
    else if ends_with(name, "_and_fetch") { opname = name[..name.len - 10]; }
    else if starts_with(name, "fetch_") { fetch_first = true; opname = name[6..]; }
    else if ends_with(name, "_fetch") { opname = name[..name.len - 6]; }
    let k: i64 = if opname == "add" { RMW_ADD } else if opname == "sub" { RMW_SUB } else if opname == "and" { RMW_AND }
        else if opname == "or" { RMW_OR } else if opname == "xor" { RMW_XOR } else if opname == "nand" { RMW_NAND }
        else if opname == "max" { RMW_MAX } else if opname == "min" { RMW_MIN } else { -1 };
    if k < 0 { return -1, 0, false; }
    return AT_RMW, k, fetch_first;
}
