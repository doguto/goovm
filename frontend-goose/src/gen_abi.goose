// goosecc B2: C types as GIR types, and the x86-64 SysV calling convention
// as clang-20 lowers it (X86_64ABIInfo in clang/lib/CodeGen/Targets/X86.cpp):
// the eightbyte classification of every argument and return type, register
// budgets, and the coerced GIR types the back-end then passes in registers.

namespace gen;

import std;
import dictionary;
import .common;
import .types;
import .ast;

// ------------------------------------------------------- scalar GIR types

var vec_cache = dictionary<u32, u32> {};    // C type index -> GIR vector type

// The GIR type of a value of scalar C type q (VOID for aggregates and void).
recursive fn vty(q: u32) -> u32 {
    let t = types[q >> 4];
    let k = t.kind as i64;
    if k == TY_INT || k == TY_UINT { return GIR_T_I32; }
    if k == TY_POINTER { return GIR_T_PTR; }
    if k == TY_LONG || k == TY_ULONG || k == TY_LLONG || k == TY_ULLONG { return GIR_T_I64; }
    if k == TY_CHAR || k == TY_SCHAR || k == TY_UCHAR { return GIR_T_I8; }
    if k == TY_BOOL { return GIR_T_I1; }
    if k == TY_SHORT || k == TY_USHORT { return GIR_T_I16; }
    if k == TY_DOUBLE { return GIR_T_F64; }
    if k == TY_FLOAT { return GIR_T_F32; }
    if k == TY_LDOUBLE { return GIR_T_F80; }
    if k == TY_INT128 || k == TY_UINT128 { return GIR_T_I128; }
    if k == TY_FLOAT16 { return GIR_T_F16; }
    if k == TY_BF16 { return GIR_T_I16; }
    if k == TY_ENUM { return vty(enum_underlying(q)); }
    if k == TY_VECTOR || k == TY_EXTVECTOR {
        let ti = (q >> 4) as! u32;
        let r = vec_cache.get(ti);
        if r { return r; }
        let e = mty(t.base);
        var n = t.n as! u32;
        let v = ty_vec(n, e);
        vec_cache.insert(ti, v);
        return v;
    }
    return GIR_T_VOID;
}

// The GIR type of the C type in memory (bool is a byte).
fn mty(q: u32) -> u32 {
    if kind_of(q) == TY_BOOL { return GIR_T_I8; }
    return vty(q);
}

fn is_bool(q: u32) -> bool { kind_of(q) == TY_BOOL }

// How the lowering holds a value of C type q.
let VK_SCALAR = 0;    // one GIR value
let VK_COMPLEX = 1;   // two GIR values (real, imaginary)
let VK_AGG = 2;       // in memory (struct, union, array)
let VK_VOID = 3;

fn vkind(q: u32) -> i64 {
    let k = kind_of(q);
    if k == TY_STRUCT || k == TY_UNION || k == TY_ARRAY || k == TY_VLA { return VK_AGG; }
    if k == TY_COMPLEX { return VK_COMPLEX; }
    if k == TY_VOID { return VK_VOID; }
    return VK_SCALAR;
}

fn csize(q: u32) -> i64 { type_size(q) }
fn calign(q: u32) -> i64 { type_align(q) }

// ---------------------------------------------------------- classification

let CL_NO = 0;
let CL_INT = 1;
let CL_SSE = 2;
let CL_SSEUP = 3;
let CL_X87 = 4;
let CL_X87UP = 5;
let CL_CX87 = 6;
let CL_MEM = 7;

fn cl_merge(acc: i64, f: i64) -> i64 {
    if acc == f || f == CL_NO { return acc; }
    if f == CL_MEM { return CL_MEM; }
    if acc == CL_NO { return f; }
    if acc == CL_INT || f == CL_INT { return CL_INT; }
    if f == CL_X87 || f == CL_X87UP || f == CL_CX87 || acc == CL_X87 || acc == CL_X87UP { return CL_MEM; }
    return CL_SSE;
}

fn post_merge(size_bits: i64, lo: i64, hi: i64) -> i64, i64 {
    var l = lo;
    var h = hi;
    if h == CL_MEM { l = CL_MEM; }
    if h == CL_X87UP && l != CL_X87 { l = CL_MEM; }
    if size_bits > 128 && (l != CL_SSE || h != CL_SSEUP) { l = CL_MEM; }
    if h == CL_SSEUP && l != CL_SSE { h = CL_SSE; }
    return l, h;
}

fn set_cur(off: i64, lo: i64, hi: i64, v: i64) -> i64, i64 {
    if off < 64 { return v, hi; }
    return lo, v;
}

fn is_flex_record(q: u32) -> bool {
    let r = rec_of(q);
    return records[r].flags & RF_FLEX != 0;
}

// X86_64ABIInfo::classify: the classes of the two eightbytes of q placed at
// bit offset `off`.
recursive fn classify(q: u32, off: i64) -> i64, i64 {
    var lo = CL_NO;
    var hi = CL_NO;
    let k = kind_of(q);
    if k == TY_VOID { return lo, hi; }
    if k == TY_INT128 || k == TY_UINT128 { return CL_INT, CL_INT; }
    if (k >= TY_BOOL && k <= TY_ULLONG) || k == TY_POINTER { return set_cur(off, lo, hi, CL_INT); }
    if k == TY_ENUM { return classify(enum_underlying(q), off); }
    if k == TY_FLOAT || k == TY_DOUBLE || k == TY_FLOAT16 || k == TY_BF16 { return set_cur(off, lo, hi, CL_SSE); }
    if k == TY_FLOAT128 { return CL_SSE, CL_SSEUP; }
    if k == TY_LDOUBLE { return CL_X87, CL_X87UP; }
    if k == TY_VECTOR || k == TY_EXTVECTOR {
        let size = csize(q) * 8;
        if size == 8 || size == 16 || size == 32 {
            let a, b = set_cur(off, lo, hi, CL_INT);
            lo = a;
            hi = b;
            if off / 64 != (off + size - 1) / 64 { hi = lo; }
            return lo, hi;
        }
        if size == 64 {
            let e = kind_of(tbase(q));
            if e == TY_DOUBLE && types[q >> 4].n == 1 { return set_cur(off, lo, hi, CL_MEM); }
            var c = CL_SSE;
            if types[q >> 4].n == 1 && (e == TY_LLONG || e == TY_ULLONG || e == TY_LONG || e == TY_ULONG) { c = CL_INT; }
            let a, b = set_cur(off, lo, hi, c);
            lo = a;
            hi = b;
            if off != 0 && off != 64 { hi = lo; }
            return lo, hi;
        }
        if size == 128 { return CL_SSE, CL_SSEUP; }
        return set_cur(off, lo, hi, CL_MEM);
    }
    if k == TY_COMPLEX {
        let et = tbase(q);
        let ek = kind_of(et);
        let size = csize(q) * 8;
        var cur = CL_MEM;
        if is_integer_kind(ek) {
            if size <= 64 { cur = CL_INT; } else if size <= 128 { lo = CL_INT; hi = CL_INT; cur = -1; }
        } else if ek == TY_FLOAT16 || ek == TY_FLOAT || ek == TY_BF16 {
            cur = CL_SSE;
        } else if ek == TY_DOUBLE {
            lo = CL_SSE;
            hi = CL_SSE;
            cur = -1;
        } else if ek == TY_LDOUBLE {
            cur = CL_CX87;
        }
        if cur >= 0 {
            let a, b = set_cur(off, lo, hi, cur);
            lo = a;
            hi = b;
        }
        let esz = csize(et) * 8;
        if hi == CL_NO && off / 64 != (off + esz) / 64 { hi = lo; }
        return lo, hi;
    }
    if k == TY_ARRAY {
        let size = csize(q) * 8;
        let et = tbase(q);
        if size > 512 { return set_cur(off, lo, hi, CL_MEM); }
        if off % (calign(et) * 8) != 0 { return set_cur(off, lo, hi, CL_MEM); }
        let esz = csize(et) * 8;
        let n = types[q >> 4].n;
        if size > 128 && (size != esz || size > 128) { return set_cur(off, lo, hi, CL_MEM); }
        var o = off;
        for i in n {
            let fl, fh = classify(et, o);
            lo = cl_merge(lo, fl);
            hi = cl_merge(hi, fh);
            if lo == CL_MEM || hi == CL_MEM { break; }
            o += esz;
        }
        return post_merge(size, lo, hi);
    }
    if k == TY_STRUCT || k == TY_UNION {
        let size = csize(q) * 8;
        if size > 512 { return set_cur(off, lo, hi, CL_MEM); }
        if is_flex_record(q) { return set_cur(off, lo, hi, CL_MEM); }
        let r = rec_of(q);
        let is_union = k == TY_UNION;
        let first = records[r].first as i64;
        let cnt = records[r].count as i64;
        for i in first..first + cnt {
            let f = fields[i];
            let bf = f.width >= 0;
            if bf && f.name == 0 { continue; }
            let fo = off + (if bf { f.bitpos } else { f.offset * 8 });
            if size > 128 && ((!is_union && size != csize(f.ty) * 8) || size > 128) {
                return post_merge(size, CL_MEM, hi);
            }
            if !bf && fo % (calign(f.ty) * 8) != 0 {
                return post_merge(size, CL_MEM, hi);
            }
            var fl = CL_NO;
            var fh = CL_NO;
            if bf {
                let w = f.width as i64;
                let eblo = fo / 64;
                let ebhi = (fo + w - 1) / 64;
                if eblo != 0 {
                    fl = CL_NO;
                    fh = CL_INT;
                } else {
                    fl = CL_INT;
                    fh = if ebhi != 0 { CL_INT } else { CL_NO };
                }
                if w == 0 { fl = CL_NO; fh = CL_NO; }
            } else {
                let a, b = classify(f.ty, fo);
                fl = a;
                fh = b;
            }
            lo = cl_merge(lo, fl);
            hi = cl_merge(hi, fh);
            if lo == CL_MEM || hi == CL_MEM { break; }
        }
        return post_merge(size, lo, hi);
    }
    return set_cur(off, lo, hi, CL_MEM);
}

// ------------------------------------------------------------ ABI records

let AK_DIRECT = 0;    // the value itself (t0), sign-extended to i32 if ext
let AK_COERCE = 1;    // n parts: GIR type t0 at byte off0, t1 at off1 of the object in memory
let AK_BYVAL = 2;     // a pointer to a copy (size, align)
let AK_IGNORE = 3;
let AK_SRET = 4;      // return: through a hidden pointer

struct Abi {
    kind: u8,
    ext: u8,         // 1: signext to i32
    n: u8,           // AK_COERCE: number of parts (1 or 2)
    tmp: u8,         // AK_COERCE: the parts extend past the object (go through a temporary)
    t0: u32,
    t1: u32,
    off0: u32,
    off1: u32,
    size: u32,       // object size (AK_BYVAL, AK_SRET, AK_COERCE)
    align: u32,
}

fn abi_ignore() -> Abi { Abi { kind: AK_IGNORE, ext: 0, n: 0, tmp: 0, t0: 0, t1: 0, off0: 0, off1: 0, size: 0, align: 1 } }

recursive fn is_promotable(q: u32) -> bool {
    let k = kind_of(q);
    if k == TY_ENUM { return is_promotable(enum_underlying(q)); }
    return k == TY_BOOL || k == TY_CHAR || k == TY_SCHAR || k == TY_UCHAR || k == TY_SHORT || k == TY_USHORT;
}

fn direct(q: u32) -> Abi {
    var e: u8 = 0;
    if is_promotable(q) && is_signed(q) { e = 1; }
    return Abi { kind: AK_DIRECT, ext: e, n: 0, tmp: 0, t0: vty(q), t1: 0, off0: 0, off1: 0, size: csize(q) as! u32,
        align: calign(q) as! u32 };
}

// The coerced type of an INTEGER / SSE eightbyte at byte offset `at` of an
// object of `size` bytes; the second result is set if the type reads past
// the end of the object.
fn eight_type(c: i64, at: i64, size: i64, pair: bool) -> u32, bool {
    let rem = size - at;
    if c == CL_INT {
        if rem >= 8 || pair { return GIR_T_I64, rem < 8; }
        return ty_int((rem * 8) as! u32), false;
    }
    if rem >= 8 || pair { return GIR_T_F64, rem < 8; }
    if rem == 4 { return GIR_T_F32, false; }
    if rem == 2 { return GIR_T_F16, false; }
    return GIR_T_F64, true;
}

// The SSEUp part: the whole vector (16 bytes) as one value.
fn byte_vector(q: u32) -> u32 {
    if is_vector(q) { return vty(q); }
    return ty_vec(2, GIR_T_I64);
}

fn coerce1(t: u32, off: i64, size: i64, tmp: bool) -> Abi {
    return Abi { kind: AK_COERCE, ext: 0, n: 1, tmp: if tmp { 1 } else { 0 }, t0: t, t1: 0, off0: off as! u32, off1: 0,
        size: size as! u32, align: 1 };
}
fn coerce2(a: u32, b: u32, size: i64, tmp: bool) -> Abi {
    return Abi { kind: AK_COERCE, ext: 0, n: 2, tmp: if tmp { 1 } else { 0 }, t0: a, t1: b, off0: 0, off1: 8,
        size: size as! u32, align: 1 };
}

fn byval(q: u32) -> Abi {
    var al = calign(q);
    if al < 8 { al = 8; }
    return Abi { kind: AK_BYVAL, ext: 0, n: 0, tmp: 0, t0: GIR_T_PTR, t1: 0, off0: 0, off1: 0, size: csize(q) as! u32,
        align: al as! u32 };
}

fn is_agg_abi(q: u32) -> bool {
    let k = kind_of(q);
    return k == TY_STRUCT || k == TY_UNION || k == TY_COMPLEX || k == TY_ARRAY;
}

// getIndirectResult: an argument that is passed in memory.
fn indirect_arg(q: u32, free_int: i64) -> Abi {
    if !is_agg_abi(q) && !(is_vector(q) && csize(q) > 16) { return direct(q); }
    let al = if calign(q) > 8 { calign(q) } else { 8 };
    let size = csize(q);
    if free_int == 0 && al == 8 && size <= 8 && size > 0 {
        return coerce1(ty_int((size * 8) as! u32), 0, size, false);
    }
    return byval(q);
}

// The ABI of a value of type q given its classes (no register budget).
// Returns the ABI and the integer and SSE registers it needs.
fn abi_of_classes(q: u32, lo: i64, hi: i64, is_ret: bool) -> Abi, i64, i64 {
    let size = csize(q);
    if lo == CL_NO && hi == CL_NO { return abi_ignore(), 0, 0; }
    if lo == CL_MEM { return byval(q), 0, 0; }
    if lo == CL_X87 || lo == CL_CX87 {
        if is_ret {
            if lo == CL_X87 {
                if !is_agg_abi(q) { return direct(q), 0, 0; }
                return coerce1(GIR_T_F80, 0, size, false), 0, 0;
            }
            var a = coerce2(GIR_T_F80, GIR_T_F80, size, false);
            a.off1 = 16;
            return a, 0, 0;
        }
        return byval(q), 0, 0;
    }
    // scalars that need no coercion
    if !is_agg_abi(q) && !is_vector(q) {
        if lo == CL_INT && (hi == CL_NO) { return direct(q), 1, 0; }
        if lo == CL_SSE && hi == CL_NO { return direct(q), 0, 1; }
        if lo == CL_INT && hi == CL_INT {
            // __int128: {i64, i64}
            return coerce2(GIR_T_I64, GIR_T_I64, size, false), 2, 0;
        }
    }
    if lo == CL_SSE && hi == CL_SSEUP {
        if is_vector(q) { return direct(q), 0, 1; }
        return coerce1(byte_vector(q), 0, size, false), 0, 1;
    }
    var nint = 0;
    var nsse = 0;
    if lo == CL_NO {
        // the low eightbyte is padding: the value is the high part at offset 8
        let t, tmp = eight_type(if hi == CL_INT { CL_INT } else { CL_SSE }, 8, size, false);
        if hi == CL_INT { nint = 1; } else { nsse = 1; }
        return coerce1(t, 8, size, tmp), nint, nsse;
    }
    let pair = hi != CL_NO && hi != CL_X87UP;
    let lt, lt_tmp = eight_type(lo, 0, size, pair);
    if lo == CL_INT { nint++; } else { nsse++; }
    if !pair {
        if is_vector(q) && !lt_tmp && lo == CL_INT && tsize(lt) == size as! u32 {
            return coerce1(lt, 0, size, false), nint, nsse;
        }
        return coerce1(lt, 0, size, lt_tmp), nint, nsse;
    }
    let hc = if hi == CL_INT { CL_INT } else { CL_SSE };
    let ht, ht_tmp = eight_type(hc, 8, size, false);
    if hc == CL_INT { nint++; } else { nsse++; }
    return coerce2(lt, ht, size, lt_tmp || ht_tmp), nint, nsse;
}

fn ret_abi(q: u32) -> Abi {
    if is_void(q) { return abi_ignore(); }
    let lo, hi = classify(q, 0);
    if lo == CL_MEM && is_vector(q) {
        // getIndirectReturnResult: a vector is not an aggregate, LLVM returns it in registers
        return direct(q);
    }
    if lo == CL_MEM {
        return Abi { kind: AK_SRET, ext: 0, n: 0, tmp: 0, t0: GIR_T_PTR, t1: 0, off0: 0, off1: 0, size: csize(q) as! u32,
            align: calign(q) as! u32 };
    }
    let a, ni, ns = abi_of_classes(q, lo, hi, true);
    return a;
}

// Per function: abis[first] is the return, abis[first + 1 + i] parameter i.
var abis: Abi[>..] = [];
var fabi_cache = dictionary<u32, u32> {};

var abi_free_int: i64 = 0;
var abi_free_sse: i64 = 0;

fn abi_start(ret: Abi) {
    abi_free_int = 6;
    abi_free_sse = 8;
    if ret.kind == AK_SRET { abi_free_int = 5; }
}

// The ABI of the next argument of type q (computeInfo's register budget).
fn arg_abi(q0: u32) -> Abi {
    var q = unqual(q0);
    if kind_of(q) == TY_ARRAY || kind_of(q) == TY_VLA { q = t_voidptr; }
    let lo, hi = classify(q, 0);
    var a = abi_ignore();
    var ni: i64 = 0;
    var ns: i64 = 0;
    if lo == CL_MEM || lo == CL_X87 || lo == CL_CX87 {
        a = indirect_arg(q, abi_free_int);
    } else {
        let a2, x, y = abi_of_classes(q, lo, hi, false);
        a = a2;
        ni = x;
        ns = y;
        if a.kind == AK_DIRECT && !is_agg_abi(q) && !is_vector(q) && lo == CL_INT && is_promotable(q) {
            a.ext = if is_signed(q) { 1 } else { 0 };
        }
    }
    if abi_free_int >= ni && abi_free_sse >= ns {
        abi_free_int -= ni;
        abi_free_sse -= ns;
        return a;
    }
    if lo == CL_INT && hi == CL_INT && !is_agg_abi(q) {
        // __int128 without two free registers: on the stack as i128
        return Abi { kind: AK_DIRECT, ext: 0, n: 0, tmp: 0, t0: GIR_T_I128, t1: 0, off0: 0, off1: 0, size: 16, align: 16 };
    }
    return indirect_arg(q, abi_free_int);
}

// The ABI of function type ft (prototyped parameters only).
fn fn_abi(ft: u32) -> u32 {
    let ti = (ft >> 4) as! u32;
    let r = fabi_cache.get(ti);
    if r { return r; }
    let t = types[ti];
    let first = abis.len as! u32;
    let ra = ret_abi(unqual(t.base));
    abis.push(ra);
    abi_start(ra);
    for i in t.n { abis.push(arg_abi(tparams[t.extra + i])); }
    fabi_cache.insert(ti, first);
    return first;
}
