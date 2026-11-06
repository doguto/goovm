// goosecc: semantic helpers shared by the parser: keywords, the token
// cursor, conversions (C11 6.3), the usual arithmetic conversions and
// assignment compatibility.

import std;
import .common;
import .types;
import .ast;

// ---------------------------------------------------------------------------
// Keywords. A keyword token has kind TK_KW + code (set when the token
// stream is built; val keeps the identifier).

let TK_KW = 100;
let KW_AUTO = 1;
let KW_BREAK = 2;
let KW_CASE = 3;
let KW_CHAR = 4;
let KW_CONST = 5;
let KW_CONTINUE = 6;
let KW_DEFAULT = 7;
let KW_DO = 8;
let KW_DOUBLE = 9;
let KW_ELSE = 10;
let KW_ENUM = 11;
let KW_EXTERN = 12;
let KW_FLOAT = 13;
let KW_FOR = 14;
let KW_GOTO = 15;
let KW_IF = 16;
let KW_INLINE = 17;
let KW_INT = 18;
let KW_LONG = 19;
let KW_REGISTER = 20;
let KW_RESTRICT = 21;
let KW_RETURN = 22;
let KW_SHORT = 23;
let KW_SIGNED = 24;
let KW_SIZEOF = 25;
let KW_STATIC = 26;
let KW_STRUCT = 27;
let KW_SWITCH = 28;
let KW_TYPEDEF = 29;
let KW_UNION = 30;
let KW_UNSIGNED = 31;
let KW_VOID = 32;
let KW_VOLATILE = 33;
let KW_WHILE = 34;
let KW_ALIGNAS = 35;
let KW_ALIGNOF = 36;
let KW_ATOMIC = 37;
let KW_BOOL = 38;
let KW_COMPLEX = 39;
let KW_GENERIC = 40;
let KW_IMAGINARY = 41;
let KW_NORETURN = 42;
let KW_STATIC_ASSERT = 43;
let KW_THREAD_LOCAL = 44;
let KW_ATTRIBUTE = 45;
let KW_EXTENSION = 46;
let KW_ASM = 47;
let KW_TYPEOF = 48;
let KW_TYPEOF_UNQUAL = 49;
let KW_LABEL = 50;
let KW_REAL = 51;
let KW_IMAG = 52;
let KW_VA_ARG = 53;
let KW_OFFSETOF = 54;
let KW_TYPES_COMPAT = 55;
let KW_CHOOSE_EXPR = 56;
let KW_INT128 = 57;
let KW_FLOAT128 = 58;
let KW_FLOAT16 = 59;
let KW_BF16 = 60;
let KW_AUTO_TYPE = 61;
let KW_FUNC = 62;           // __func__ __FUNCTION__ __PRETTY_FUNCTION__
let KW_NULLABILITY = 63;    // _Nonnull _Nullable _Null_unspecified _Nullable_result
let KW_CONVERTVECTOR = 64;
let KW_BITCAST = 65;
let KW_UNALIGNED = 66;      // __unaligned (ignored)
let KW_DECLSPEC = 67;
let KW_IBM128 = 68;
let KW_FLOAT32X = 69;       // unused placeholder
let KW_LAST = 70;

var opt_kw_inline: bool = true;
var opt_kw_restrict: bool = true;
var opt_kw_gnu: bool = true;      // typeof, asm

fn set_kw(name: const u8[:], k: i64) {
    let id = intern(name);
    idents[id].kw = k as! u16;
}

fn keywords_init() {
    set_kw("auto", KW_AUTO); set_kw("break", KW_BREAK); set_kw("case", KW_CASE); set_kw("char", KW_CHAR);
    set_kw("const", KW_CONST); set_kw("__const", KW_CONST); set_kw("__const__", KW_CONST);
    set_kw("continue", KW_CONTINUE); set_kw("default", KW_DEFAULT); set_kw("do", KW_DO);
    set_kw("double", KW_DOUBLE); set_kw("else", KW_ELSE); set_kw("enum", KW_ENUM); set_kw("extern", KW_EXTERN);
    set_kw("float", KW_FLOAT); set_kw("for", KW_FOR); set_kw("goto", KW_GOTO); set_kw("if", KW_IF);
    if opt_kw_inline { set_kw("inline", KW_INLINE); }
    set_kw("__inline", KW_INLINE); set_kw("__inline__", KW_INLINE);
    set_kw("int", KW_INT); set_kw("long", KW_LONG); set_kw("register", KW_REGISTER);
    if opt_kw_restrict { set_kw("restrict", KW_RESTRICT); }
    set_kw("__restrict", KW_RESTRICT); set_kw("__restrict__", KW_RESTRICT);
    set_kw("return", KW_RETURN); set_kw("short", KW_SHORT); set_kw("signed", KW_SIGNED);
    set_kw("__signed", KW_SIGNED); set_kw("__signed__", KW_SIGNED); set_kw("sizeof", KW_SIZEOF);
    set_kw("static", KW_STATIC); set_kw("struct", KW_STRUCT); set_kw("switch", KW_SWITCH);
    set_kw("typedef", KW_TYPEDEF); set_kw("union", KW_UNION); set_kw("unsigned", KW_UNSIGNED);
    set_kw("void", KW_VOID); set_kw("volatile", KW_VOLATILE); set_kw("__volatile", KW_VOLATILE);
    set_kw("__volatile__", KW_VOLATILE); set_kw("while", KW_WHILE); set_kw("_Alignas", KW_ALIGNAS);
    set_kw("_Alignof", KW_ALIGNOF); set_kw("__alignof", KW_ALIGNOF); set_kw("__alignof__", KW_ALIGNOF);
    set_kw("_Atomic", KW_ATOMIC); set_kw("_Bool", KW_BOOL); set_kw("_Complex", KW_COMPLEX);
    set_kw("__complex", KW_COMPLEX); set_kw("__complex__", KW_COMPLEX); set_kw("_Generic", KW_GENERIC);
    set_kw("_Imaginary", KW_IMAGINARY); set_kw("_Noreturn", KW_NORETURN); set_kw("_Static_assert", KW_STATIC_ASSERT);
    set_kw("_Thread_local", KW_THREAD_LOCAL); set_kw("__thread", KW_THREAD_LOCAL);
    set_kw("__attribute__", KW_ATTRIBUTE); set_kw("__attribute", KW_ATTRIBUTE); set_kw("__extension__", KW_EXTENSION);
    if opt_kw_gnu { set_kw("asm", KW_ASM); set_kw("typeof", KW_TYPEOF); }
    set_kw("__asm", KW_ASM); set_kw("__asm__", KW_ASM); set_kw("__typeof", KW_TYPEOF); set_kw("__typeof__", KW_TYPEOF);
    set_kw("typeof_unqual", KW_TYPEOF_UNQUAL); set_kw("__typeof_unqual__", KW_TYPEOF_UNQUAL);
    set_kw("__label__", KW_LABEL); set_kw("__real", KW_REAL); set_kw("__real__", KW_REAL);
    set_kw("__imag", KW_IMAG); set_kw("__imag__", KW_IMAG); set_kw("__builtin_va_arg", KW_VA_ARG);
    set_kw("__builtin_offsetof", KW_OFFSETOF); set_kw("__builtin_types_compatible_p", KW_TYPES_COMPAT);
    set_kw("__builtin_choose_expr", KW_CHOOSE_EXPR); set_kw("__int128", KW_INT128);
    set_kw("__float128", KW_FLOAT128); set_kw("_Float16", KW_FLOAT16); set_kw("__bf16", KW_BF16);
    set_kw("__auto_type", KW_AUTO_TYPE); set_kw("__func__", KW_FUNC); set_kw("__FUNCTION__", KW_FUNC);
    set_kw("__PRETTY_FUNCTION__", KW_FUNC); set_kw("_Nonnull", KW_NULLABILITY); set_kw("_Nullable", KW_NULLABILITY);
    set_kw("_Null_unspecified", KW_NULLABILITY); set_kw("_Nullable_result", KW_NULLABILITY);
    set_kw("__builtin_convertvector", KW_CONVERTVECTOR); set_kw("__builtin_bit_cast", KW_BITCAST);
    set_kw("__unaligned", KW_UNALIGNED); set_kw("__ibm128", KW_IBM128);
}

// ---------------------------------------------------------------------------
// The token cursor.

var pc: i64 = 0;

fn tk() -> i64 { tu_toks[pc].kind as i64 }
fn tk_n(k: i64) -> i64 {
    let i = pc + k;
    if i < tu_toks.len { return tu_toks[i].kind as i64; }
    return TK_EOF;
}
fn tloc() -> u32 { tu_toks[pc].xloc }
fn tval() -> u32 { tu_toks[pc].val }
fn kw(k: i64) -> i64 { TK_KW + k }
fn at(k: i64) -> bool { tu_toks[pc].kind as i64 == k }
fn at_kw(k: i64) -> bool { tu_toks[pc].kind as i64 == TK_KW + k }
fn adv() { if pc < tu_toks.len - 1 { pc++; } }
fn accept(k: i64) -> bool {
    if at(k) { adv(); return true; }
    return false;
}

var tok_buf: u8[>..] = [];
fn tok_desc(out: u8[>..]&, i: i64) {
    let t = tu_toks[i];
    if t.kind as i64 == TK_EOF { out.append("end of file"); return; }
    out.push('\'');
    var tt = t;
    if tt.kind as i64 >= TK_KW { tt.kind = TK_IDENT; }
    if tt.kind as i64 == TK_ANNOT_PACK { out.append("#pragma pack"); } else { tok_spelling_any(out, tt); }
    out.push('\'');
}

fn tok_spelling_any(out: u8[>..]&, t: Tok) {
    let k = t.kind as i64;
    if k == TK_IDENT {
        out.append(ident_text(t.val as i64));
    } else if is_punct(k) {
        out.append(PUNCT_SPELL[k - TK_L_SQUARE]);
    } else {
        out.append(src[t.spell..t.spell + t.val]);
    }
}

fn expect(k: i64, what: const u8[:]) -> bool {
    if at(k) { adv(); return true; }
    tok_buf.clear();
    tok_buf.append("expected ");
    tok_buf.append(what);
    tok_buf.append(", got ");
    tok_desc(tok_buf, pc);
    error_at(tloc() as i64, tok_buf);
    return false;
}

fn err(msg: const u8[:]) { error_at(tloc() as i64, msg); }

// Warnings that clang-20 makes errors by default (-Wno-X downgrades them).
var opt_wno_return: bool = false;
var opt_wno_int_conv: bool = false;
var opt_wno_implicit_fn: bool = false;
var opt_wno_implicit_int: bool = false;
var opt_c89: bool = false;
fn return_mismatch(loc: u32, msg: const u8[:]) {
    if opt_wno_return { warn_at(loc as i64, msg); } else { error_at(loc as i64, msg); }
}
fn int_conversion(loc: u32, msg: const u8[:]) {
    if opt_wno_int_conv { warn_at(loc as i64, msg); } else { error_at(loc as i64, msg); }
}
fn implicit_fn(loc: u32, msg: const u8[:]) {
    if opt_wno_implicit_fn || opt_c89 { warn_at(loc as i64, msg); } else { error_at(loc as i64, msg); }
}
fn implicit_int(loc: u32, msg: const u8[:]) {
    if opt_wno_implicit_int || opt_c89 { warn_at(loc as i64, msg); } else { error_at(loc as i64, msg); }
}
fn err_at(loc: u32, msg: const u8[:]) { error_at(loc as i64, msg); }
fn warn(loc: u32, msg: const u8[:]) { warn_at(loc as i64, msg); }

var tn_buf: u8[>..] = [];
fn tname(q: u32) -> const u8[:] {
    tn_buf.clear();
    tn_buf.push('\'');
    type_name(tn_buf, q);
    tn_buf.push('\'');
    return tn_buf;
}

// ---------------------------------------------------------------------------
// Conversions.

fn nty(n: u32) -> u32 { nodes[n].ty }
fn nflags(n: u32) -> i64 { nodes[n].flags as i64 }

fn icast(n: u32, ck: i64, to: u32) -> u32 {
    let r = node(N_ICAST, ck, to, n as i64, 0, 0, nodes[n].loc);
    return r;
}

// Lvalue-to-rvalue, array-to-pointer and function-to-pointer conversion
// (C11 6.3.2.1).
fn rv(n: u32) -> u32 {
    let t = nty(n);
    let k = kind_of(t);
    if k == TY_ARRAY || k == TY_VLA {
        return icast(n, CK_ARRAY2PTR, mk_ptr(tbase(t)));
    }
    if k == TY_FUNC {
        return icast(n, CK_FUNC2PTR, mk_ptr(unqual(t)));
    }
    if is_lvalue(n) {
        let r = icast(n, CK_LVAL2RVAL, unqual(t));
        return r;
    }
    return n;
}

// The integer promotions (C11 6.3.1.1), applied to an rvalue.
fn promote(n: u32) -> u32 {
    let t = nty(n);
    let to = promoted_type(n);
    if to == unqual(t) { return n; }
    return icast(n, CK_INTEGRAL, to);
}

fn bitfield_width(n: u32) -> i64 {
    // n is an rvalue load of a bit-field member (or the member itself)
    var m = n;
    if nodes[m].kind == N_ICAST && nodes[m].op == CK_LVAL2RVAL { m = nodes[m].a; }
    if nodes[m].kind == N_MEMBER && nodes[m].flags & NF_BITFIELD != 0 { return fields[nodes[m].b].width as i64; }
    return -1;
}

fn promoted_type(n: u32) -> u32 {
    let t = unqual(nty(n));
    let k = kind_of(t);
    if !is_integer_kind(k) { return t; }
    let w = bitfield_width(n);
    if w >= 0 {
        // a bit-field narrower than int promotes to int (or unsigned int)
        if k != TY_INT128 && k != TY_UINT128 && k != TY_LONG && k != TY_ULONG && k != TY_LLONG && k != TY_ULLONG {
            if w < 32 { return t_int; }
            if w == 32 { return if is_signed(t) { t_int } else { t_uint }; }
        }
    }
    if k == TY_ENUM {
        let u = enum_underlying(t);
        if int_rank(u) < 4 { return t_int; }
        return u;
    }
    if int_rank(t) < 4 { return t_int; }
    return t;
}

fn cast_kind(from: u32, to: u32) -> i64 {
    let kf = kind_of(from);
    let kt = kind_of(to);
    if kt == TY_VOID { return CK_TOVOID; }
    if unqual(tcanon(from)) == unqual(tcanon(to)) { return CK_NOOP; }
    let fi = is_integer_kind(kf);
    let ff = is_float_kind(kf);
    if kt == TY_BOOL {
        if fi { return CK_INT2BOOL; }
        if ff { return CK_FLOAT2BOOL; }
        if kf == TY_POINTER { return CK_PTR2BOOL; }
    }
    if is_integer_kind(kt) {
        if fi {
            if type_size(from) == type_size(to) && is_signed(from) == is_signed(to) { return CK_NOOP; }
            return CK_INTEGRAL;
        }
        if ff { return CK_FLOAT2INT; }
        if kf == TY_POINTER { return CK_PTR2INT; }
        if kf == TY_COMPLEX { return CK_COMPLEX2REAL; }
    }
    if is_float_kind(kt) {
        if fi { return CK_INT2FLOAT; }
        if ff { return CK_FLOATCAST; }
        if kf == TY_COMPLEX { return CK_COMPLEX2REAL; }
    }
    if kt == TY_POINTER {
        if fi { return CK_INT2PTR; }
        if kf == TY_POINTER { return CK_BITCAST; }
    }
    if kt == TY_COMPLEX {
        if kf == TY_COMPLEX { return CK_COMPLEXCAST; }
        return CK_REAL2COMPLEX;
    }
    if kt == TY_VECTOR || kt == TY_EXTVECTOR {
        if kf == TY_VECTOR || kf == TY_EXTVECTOR { return CK_VECBITCAST; }
        if type_size(from) == type_size(to) { return CK_VECBITCAST; }
        return CK_VECSPLAT;
    }
    if (kf == TY_VECTOR || kf == TY_EXTVECTOR) { return CK_VECBITCAST; }
    return CK_NOOP;
}

// Converts rvalue n to type `to` (no checks).
fn convert(n: u32, to0: u32) -> u32 {
    let to = unqual(to0);
    let from = nty(n);
    if unqual(from) == to { return n; }
    let ck = cast_kind(from, to);
    if is_null_const(n) && kind_of(to) == TY_POINTER { return icast(n, CK_NULL2PTR, to); }
    if ck == CK_REAL2COMPLEX && unqual(tbase(to)) != unqual(from) {
        // convert to the element type first
        let e = icast(n, cast_kind(from, tbase(to)), unqual(tbase(to)));
        return icast(e, CK_REAL2COMPLEX, to);
    }
    if ck == CK_COMPLEX2REAL && unqual(tbase(from)) != to {
        let e = icast(n, CK_COMPLEX2REAL, unqual(tbase(from)));
        return icast(e, cast_kind(nty(e), to), to);
    }
    return icast(n, ck, to);
}

// Is n a null pointer constant (an integer constant 0, or such cast to void *)?
fn is_null_const(n: u32) -> bool {
    var m = n;
    loop {
        let nd = nodes[m];
        if nd.flags & NF_NULLCONST != 0 { return true; }
        if nd.kind == N_INT { return nd.v == 0 && is_integer(nd.ty); }
        if (nd.kind == N_CAST || nd.kind == N_ICAST) && (nd.op == CK_NOOP || nd.op == CK_INTEGRAL || nd.op == CK_BITCAST || nd.op == CK_NULL2PTR || nd.op == CK_INT2PTR) {
            if kind_of(nd.ty) == TY_POINTER {
                let pt = tbase(nd.ty);
                if !(kind_of(pt) == TY_VOID && quals(pt) == 0) { return false; }
            } else if !is_integer(nd.ty) {
                return false;
            }
            m = nd.a;
            continue;
        }
        if nd.kind == N_UNARY && nd.op == U_EXTENSION { m = nd.a; continue; }
        if is_integer(nd.ty) && (nd.kind == N_BINARY || nd.kind == N_UNARY || nd.kind == N_COND || nd.kind == N_SIZEOF) {
            let ok, v = fold_int(m);
            return ok && v == 0;
        }
        return false;
    }
}

// The usual arithmetic conversions on two rvalues. Returns the converted
// operands and the common type.
fn arith_common(a: u32, b: u32) -> u32 {
    let ta = unqual(nty(a));
    let tb = unqual(nty(b));
    let ca = is_complex(ta);
    let cb = is_complex(tb);
    let ra = if ca { unqual(tbase(ta)) } else { ta };
    let rb = if cb { unqual(tbase(tb)) } else { tb };
    var r: u32 = 0;
    if is_real_float(ra) || is_real_float(rb) {
        if is_real_float(ra) && is_real_float(rb) {
            r = if float_rank(ra) >= float_rank(rb) { ra } else { rb };
        } else {
            r = if is_real_float(ra) { ra } else { rb };
        }
    } else {
        let pa = promoted_type(a);
        let pb = promoted_type(b);
        r = int_common(if ca { ra } else { pa }, if cb { rb } else { pb });
    }
    if ca || cb { return mk_complex(r); }
    return r;
}

fn int_common(a: u32, b: u32) -> u32 {
    let pa = if kind_of(a) == TY_ENUM { enum_underlying(a) } else { a };
    let pb = if kind_of(b) == TY_ENUM { enum_underlying(b) } else { b };
    if pa == pb { return pa; }
    let sa = is_signed(pa);
    let sb = is_signed(pb);
    let ra = int_rank(pa);
    let rb = int_rank(pb);
    if sa == sb { return if ra >= rb { pa } else { pb }; }
    let u = if sa { pb } else { pa };
    let s = if sa { pa } else { pb };
    if int_rank(u) >= int_rank(s) { return u; }
    if type_size(s) > type_size(u) { return s; }
    return unsigned_of(s);
}

// ---------------------------------------------------------------------------
// Integer constant folding (used for null pointer constants, ICEs, etc.).
// Returns (ok, value) with the value truncated/extended to the node type.

fn trunc_to(v: i64, t: u32) -> i64 {
    let k = kind_of(t);
    if k == TY_BOOL { return if v != 0 { 1 } else { 0 }; }
    let sz = type_size(t);
    if sz >= 8 || sz <= 0 { return v; }
    let bits = sz * 8;
    let m = (1 << bits) - 1;
    let u = v & m;
    if is_signed(t) && u >= (1 << (bits - 1)) { return u - (1 << bits); }
    return u;
}

recursive fn fold_int(n: u32) -> bool, i64 {
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_INT { return true, nd.v; }
    if k == N_SIZEOF || k == N_OFFSETOF {
        if nd.v < 0 { return false, 0; }
        return true, nd.v;
    }
    if k == N_ICAST || k == N_CAST {
        let op = nd.op as i64;
        if op == CK_LVAL2RVAL || op == CK_ARRAY2PTR || op == CK_FUNC2PTR { return false, 0; }
        if op == CK_FLOAT2INT {
            let ok, f = fold_float(nd.a);
            if !ok { return false, 0; }
            return true, trunc_to(float_to_int(f, nd.ty), nd.ty);
        }
        if op == CK_FLOAT2BOOL {
            let ok, f = fold_float(nd.a);
            if !ok { return false, 0; }
            return true, if f != 0.0 { 1 } else { 0 };
        }
        if !is_integer(nodes[nd.a].ty) && !(op == CK_NULL2PTR) { return false, 0; }
        let ok, v = fold_int(nd.a);
        if !ok { return false, 0; }
        if kind_of(nd.ty) == TY_POINTER { return true, v; }
        if !is_integer(nd.ty) { return false, 0; }
        return true, trunc_to(v, nd.ty);
    }
    if k == N_UNARY {
        let op = nd.op as i64;
        if op == U_EXTENSION || op == U_PLUS { return fold_int(nd.a); }
        if op == U_NOT {
            if is_real_float(nodes[nd.a].ty) {
                let ok, f = fold_float(nd.a);
                return ok, if f == 0.0 { 1 } else { 0 };
            }
            let ok, v = fold_int(nd.a);
            return ok, if v == 0 { 1 } else { 0 };
        }
        if !is_integer(nd.ty) { return false, 0; }
        let ok, v = fold_int(nd.a);
        if !ok { return false, 0; }
        if op == U_NEG { return true, trunc_to((0 - (v as! u64)) as! i64, nd.ty); }
        if op == U_BITNOT { return true, trunc_to(~v, nd.ty); }
        return false, 0;
    }
    if k == N_BINARY {
        let op = nd.op as i64;
        if op == B_LAND || op == B_LOR {
            let ok, a = fold_bool(nd.a);
            if !ok { return false, 0; }
            if op == B_LAND && !a { return true, 0; }
            if op == B_LOR && a { return true, 1; }
            let ok2, b = fold_bool(nd.b);
            if !ok2 { return false, 0; }
            return true, if b { 1 } else { 0 };
        }
        if op == B_COMMA { return false, 0; }
        let at = nodes[nd.a].ty;
        if (op == B_LT || op == B_GT || op == B_LE || op == B_GE || op == B_EQ || op == B_NE) && is_real_float(at) {
            let ok, x = fold_float(nd.a);
            let ok2, y = fold_float(nd.b);
            if !ok || !ok2 { return false, 0; }
            let c = match op { B_LT => x < y, B_GT => x > y, B_LE => x <= y, B_GE => x >= y, B_EQ => x == y, _ => x != y };
            return true, if c { 1 } else { 0 };
        }
        if !is_integer(at) && !(kind_of(at) == TY_POINTER && (op == B_EQ || op == B_NE)) { return false, 0; }
        let ok, a = fold_int(nd.a);
        if !ok { return false, 0; }
        let ok2, b = fold_int(nd.b);
        if !ok2 { return false, 0; }
        let uns = !is_signed(at) || kind_of(at) == TY_POINTER;
        let ua = a as! u64;
        let ub = b as! u64;
        var r: i64 = 0;
        if op == B_MUL { r = (ua * ub) as! i64; }
        else if op == B_DIV || op == B_REM {
            if b == 0 { return false, 0; }
            if uns {
                let sz = type_size(at);
                var xa = ua;
                var xb = ub;
                if sz < 8 && sz > 0 { let m: u64 = (1 << (sz * 8)) - 1; xa = ua & m; xb = ub & m; }
                r = (if op == B_DIV { xa / xb } else { xa % xb }) as! i64;
            } else if a == -9223372036854775807 - 1 && b == -1 {
                r = if op == B_DIV { a } else { 0 };
            } else {
                r = if op == B_DIV { a / b } else { rem(a, b) };
            }
        }
        else if op == B_ADD { r = (ua + ub) as! i64; }
        else if op == B_SUB { r = (ua - ub) as! i64; }
        else if op == B_SHL { if b < 0 || b >= 64 { r = 0; } else { r = (ua << (b as! u64)) as! i64; } }
        else if op == B_SHR {
            if b < 0 || b >= 64 { r = if !uns && a < 0 { -1 } else { 0 }; }
            else if uns {
                let sz = type_size(at);
                var xa = ua;
                if sz < 8 && sz > 0 { let m: u64 = (1 << (sz * 8)) - 1; xa = ua & m; }
                r = (xa >> (b as! u64)) as! i64;
            } else { r = a >> (b as! u64); }
        }
        else if op == B_AND { r = a & b; }
        else if op == B_XOR { r = a ^ b; }
        else if op == B_OR { r = a | b; }
        else {
            var c = false;
            if uns {
                let sz = type_size(at);
                var xa = ua;
                var xb = ub;
                if sz < 8 && sz > 0 { let m: u64 = (1 << (sz * 8)) - 1; xa = ua & m; xb = ub & m; }
                c = match op { B_LT => xa < xb, B_GT => xa > xb, B_LE => xa <= xb, B_GE => xa >= xb, B_EQ => xa == xb, _ => xa != xb };
            } else {
                c = match op { B_LT => a < b, B_GT => a > b, B_LE => a <= b, B_GE => a >= b, B_EQ => a == b, _ => a != b };
            }
            return true, if c { 1 } else { 0 };
        }
        return true, trunc_to(r, nd.ty);
    }
    if k == N_COND {
        let ok, c = fold_bool(nd.a);
        if !ok { return false, 0; }
        if nd.b == 0 {
            if c { return fold_int(nd.a); }
            return fold_int(nd.c);
        }
        if c { return fold_int(nd.b); }
        return fold_int(nd.c);
    }
    return false, 0;
}

recursive fn fold_bool(n: u32) -> bool, bool {
    if is_real_float(nodes[n].ty) {
        let ok, f = fold_float(n);
        return ok, f != 0.0;
    }
    let ok, v = fold_int(n);
    if ok { return true, v != 0; }
    // the address of an object or function is never null
    let ok2, sym = address_base(n);
    if ok2 { return true, true; }
    return false, false;
}

// The object/function whose address a pointer expression is (for &x,
// arrays decaying, functions decaying, string literals).
fn address_base(n: u32) -> bool, i64 {
    var m = n;
    loop {
        let nd = nodes[m];
        if nd.kind == N_ICAST || nd.kind == N_CAST {
            if nd.op == CK_ARRAY2PTR || nd.op == CK_FUNC2PTR || nd.op == CK_BITCAST || nd.op == CK_NOOP {
                let inner = nodes[nd.a];
                if (nd.op == CK_ARRAY2PTR || nd.op == CK_FUNC2PTR) && inner.kind == N_DECLREF { return true, inner.a as i64; }
                if nd.op == CK_ARRAY2PTR && inner.kind == N_STRING { return true, -1; }
                m = nd.a;
                continue;
            }
            return false, 0;
        }
        if nd.kind == N_UNARY && nd.op == U_ADDR {
            let inner = nodes[nd.a];
            if inner.kind == N_DECLREF { return true, inner.a as i64; }
            return false, 0;
        }
        return false, 0;
    }
}

fn float_to_int(f: f64, t: u32) -> i64 {
    if f != f { return 0; }
    if !is_signed(t) && f >= 9223372036854775808.0 {
        if f >= 18446744073709551616.0 { return -1; }
        return ((f - 9223372036854775808.0) as! i64) + (-9223372036854775807 - 1);
    }
    if f >= 9223372036854775807.0 { return 9223372036854775807; }
    if f <= -9223372036854775808.0 { return -9223372036854775807 - 1; }
    return f as! i64;
}

fn bits_to_f64(v: i64) -> f64 {
    var x = v;
    return reinterpret_f64(x);
}

extern fn reinterpret_f64(v: i64) -> f64 = "goosecc_bits_to_f64";
extern fn reinterpret_i64(v: f64) -> i64 = "goosecc_f64_to_bits";
extern fn round_f32(v: f64) -> f64 = "goosecc_round_f32";

recursive fn fold_float(n: u32) -> bool, f64 {
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_FLOAT { return true, reinterpret_f64(nd.v); }
    if k == N_INT {
        if is_signed(nd.ty) { return true, nd.v as f64; }
        return true, (nd.v as! u64) as f64;
    }
    if k == N_ICAST || k == N_CAST {
        let op = nd.op as i64;
        if op == CK_INT2FLOAT {
            let ok, v = fold_int(nd.a);
            if !ok { return false, 0.0; }
            var f: f64 = if is_signed(nodes[nd.a].ty) { v as f64 } else { (v as! u64) as f64 };
            if kind_of(nd.ty) == TY_FLOAT { f = round_f32(f); }
            return true, f;
        }
        if op == CK_FLOATCAST || op == CK_NOOP {
            let ok, f = fold_float(nd.a);
            if !ok { return false, 0.0; }
            if kind_of(nd.ty) == TY_FLOAT { return true, round_f32(f); }
            return true, f;
        }
        return false, 0.0;
    }
    if k == N_UNARY {
        let ok, f = fold_float(nd.a);
        if !ok { return false, 0.0; }
        if nd.op == U_NEG { return true, 0.0 - f; }
        if nd.op == U_PLUS || nd.op == U_EXTENSION { return true, f; }
        return false, 0.0;
    }
    if k == N_BINARY && is_real_float(nd.ty) {
        let ok, a = fold_float(nd.a);
        let ok2, b = fold_float(nd.b);
        if !ok || !ok2 { return false, 0.0; }
        var r = 0.0;
        if nd.op == B_ADD { r = a + b; }
        else if nd.op == B_SUB { r = a - b; }
        else if nd.op == B_MUL { r = a * b; }
        else if nd.op == B_DIV { r = a / b; }
        else { return false, 0.0; }
        if kind_of(nd.ty) == TY_FLOAT { r = round_f32(r); }
        return true, r;
    }
    if k == N_COND {
        let ok, c = fold_bool(nd.a);
        if !ok { return false, 0.0; }
        if c { return fold_float(if nd.b == 0 { nd.a } else { nd.b }); }
        return fold_float(nd.c);
    }
    return false, 0.0;
}
