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
    if pt_rec && i > pt_peek && i <= pt_eof { pt_peek = i; }
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
    // Like clang's ImpCastExprToType: a conversion of an implicit
    // conversion of the same kind updates it (a promotion followed by a
    // conversion is then one IntegralCast from the original type).
    let nd = nodes[n];
    if nd.kind == N_ICAST && nd.op as i64 == ck && ck != CK_LVAL2RVAL && ck != CK_ARRAY2PTR && ck != CK_FUNC2PTR {
        nodes[n].ty = to;
        return n;
    }
    let r = node(N_ICAST, ck, to, n as i64, 0, 0, nd.loc);
    return r;
}

// Lvalue-to-rvalue, array-to-pointer and function-to-pointer conversion
// (C11 6.3.2.1).
fn rv(n: u32) -> u32 {
    let t = nty(n);
    let k = kind_of(t);
    if k == TY_ARRAY || k == TY_VLA {
        // qualifiers of an array type are those of its elements
        return icast(n, CK_ARRAY2PTR, mk_ptr(with_quals(tbase(t), quals(t))));
    }
    if k == TY_FUNC {
        return icast(n, CK_FUNC2PTR, mk_ptr(unqual(t)));
    }
    if is_lvalue(n) {
        if quals(t) & Q_ATOMIC != 0 {
            // an atomic load, then the value (clang: LValueToRValue to
            // _Atomic(T), AtomicToNonAtomic)
            let l = icast(n, CK_LVAL2RVAL, unqual(t) | (Q_ATOMIC as! u32));
            return icast(l, CK_ATOMIC, unqual(t));
        }
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

// The width of the bit-field n refers to, or -1: a load of a bit-field
// member, or (clang's getSourceBitField) an assignment to one, a prefix
// increment of one, or a comma whose right operand is one.
fn bitfield_width(n: u32) -> i64 {
    var m = n;
    loop {
        let nd = nodes[m];
        if nd.kind == N_ICAST && (nd.op == CK_LVAL2RVAL || nd.op == CK_NOOP) { m = nd.a; continue; }
        if nd.kind == N_ASSIGN { m = nd.a; continue; }
        if nd.kind == N_BINARY && nd.op == B_COMMA { m = nd.b; continue; }
        if nd.kind == N_UNARY && (nd.op == U_PREINC || nd.op == U_PREDEC) { m = nd.a; continue; }
        break;
    }
    if nodes[m].kind == N_MEMBER && nodes[m].flags & NF_BITFIELD != 0 { return fields[nodes[m].b].width as i64; }
    return -1;
}

fn promoted_type(n: u32) -> u32 {
    let t = unqual(nty(n));
    let k = kind_of(t);
    if !is_integer_kind(k) { return t; }
    let w = bitfield_width(n);
    if w >= 0 {
        // a bit-field narrower than int promotes to int whatever its type
        // (GCC compatibility, clang's isPromotableBitField)
        if w < 32 { return t_int; }
        if w == 32 { return if is_signed(t) { t_int } else { t_uint }; }
    }
    if k == TY_ENUM {
        let u = enum_underlying(t);
        if int_rank(u) < 4 { return t_int; }
        return u;
    }
    if int_rank(t) < 4 { return t_int; }
    return t;
}

// The type after the default argument promotions (C11 6.5.2.2p6).
fn arg_promoted_type(t0: u32) -> u32 {
    let t = unqual(t0);
    let k = kind_of(t);
    if k == TY_FLOAT { return t_double; }
    if !is_integer_kind(k) { return t; }
    if k == TY_ENUM {
        let u = enum_underlying(t);
        if int_rank(u) < 4 { return t_int; }
        return u;
    }
    if int_rank(t) < 4 { return t_int; }
    return t;
}

// Pointer types that differ only in qualifiers at any level.
fn cvr_similar(a0: u32, b0: u32) -> bool {
    var a = a0;
    var b = b0;
    loop {
        a = unqual(tcanon(a));
        b = unqual(tcanon(b));
        if a == b { return true; }
        if kind_of(a) != TY_POINTER || kind_of(b) != TY_POINTER { return false; }
        a = tbase(a);
        b = tbase(b);
    }
    return false;
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
        if fi { return CK_INTEGRAL; }
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
        if kf == TY_POINTER {
            // a qualification conversion is a no-op (clang NoOp, hasCvrSimilarType)
            if cvr_similar(from, to) { return CK_NOOP; }
            return CK_BITCAST;
        }
    }
    if kt == TY_COMPLEX {
        if kf == TY_COMPLEX { return CK_COMPLEXCAST; }
        return CK_REAL2COMPLEX;
    }
    if kt == TY_VECTOR || kt == TY_EXTVECTOR {
        if kf == TY_VECTOR || kf == TY_EXTVECTOR { return CK_BITCAST; }
        if type_size(from) == type_size(to) { return CK_BITCAST; }
        return CK_VECSPLAT;
    }
    if (kf == TY_VECTOR || kf == TY_EXTVECTOR) { return CK_BITCAST; }
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

// Is n a null pointer constant: an integer constant expression with value
// 0, or such an expression cast to void * (C11 6.3.2.3p3)? As in clang,
// implicit conversions are looked through, and only an explicit cast to
// unqualified void * of an integer operand counts (`(void *)(void *)0` is
// not one).
fn is_null_const(n: u32) -> bool {
    var m = n;
    loop {
        let nd = nodes[m];
        if nd.kind == N_ICAST { m = nd.a; continue; }
        if nd.kind == N_CAST && kind_of(nd.ty) == TY_POINTER {
            let pt = tbase(nd.ty);
            if kind_of(pt) == TY_VOID && quals(pt) == 0 && is_integer(nodes[nd.a].ty) { m = nd.a; continue; }
            return false;
        }
        if !is_integer(nd.ty) { return false; }
        if nd.kind == N_INT { return nd.v == 0; }
        if nd.kind == N_UNARY && nd.op == U_EXTENSION { m = nd.a; continue; }
        let ok, v = fold_int(m);
        return ok && v == 0;
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

// G1: the lowering's constant folding reads const variables as clang's
// constant evaluator does (EvaluateAsRValue / EvaluateAsInt: CodeGen's
// reads of such variables, the conditions it folds, static initializers).
// The front end's own constant expressions never do: an integer constant
// expression of C reads no variable (fold_cvars is off while parsing).
var fold_cvars: bool = false;
var cvar_init: u32[>..] = [];   // per symbol: the initializer the evaluator reads (0: none)
var cvar_decl: u32[>..] = [];   // per file-scope symbol: the N_DECL that defines it
var cv_ctx: u32 = 0;            // the definition being lowered (its N_FUNCDEF / N_DECL node)
var cv_ctx_late: bool = false;  // emitted after the whole unit (clang's deferred definitions)
var cv_depth: i64 = 0;
// The library functions the evaluator folds, by identifier (lower_tu:
// unless -fno-builtin or -fno-builtin-NAME): strlen and memchr.
var fold_lib_strlen: u32 = 0xFFFFFFFF;
var fold_lib_memchr: u32 = 0xFFFFFFFF;

// A const, non-volatile, non-weak variable (an array of such elements),
// not a parameter: clang's evaluator reads its initializer
// (isConstantEmittableObjectType, evaluateVarDeclInit).
fn cv_eligible(s: i64) -> bool {
    let sy = syms[s];
    if sy.kind != SK_VAR || sy.flags & SF_PARAM != 0 || sy.flags & SF_WEAK != 0 { return false; }
    var t = sy.ty;
    while is_array(t) && kind_of(t) != TY_VLA { t = tbase(t); }
    let q = quals(t);
    return q & Q_CONST != 0 && q & (Q_VOLATILE | Q_ATOMIC) == 0;
}

fn cv_grow() {
    while cvar_init.len < syms.len { cvar_init.push(0); cvar_decl.push(0); }
}

// The parser: variable s is defined at decl with initializer init.
fn cv_define(s: i64, decl: u32, init: u32) {
    if init == 0 || !cv_eligible(s) { return; }
    cv_grow();
    cvar_init[s] = init;
    cvar_decl[s] = decl;
}

// GNU modes accept an array bound that clang's evaluator folds (reads of
// const variables, differences of addresses) as a constant size, as an
// extension (Sema's checkArraySize with AllowFold). n: an integer rvalue.
recursive fn fold_gnu(n: u32) -> bool, i64 {
    let f0 = fold_cvars;
    let l0 = cv_ctx_late;
    fold_cvars = true;
    cv_ctx_late = true;
    let ok, v = fold_int(n);
    fold_cvars = f0;
    cv_ctx_late = l0;
    return ok, v;
}

// The address pointer expression n computes, as (base, offset in bytes):
// base -1 for an integer (a null pointer plus an offset), else a variable
// or function symbol. clang folds differences and comparisons of addresses
// of one base, and offsetof written as (size_t)&((T *)0)->m (G1).
recursive fn fold_addr(n: u32) -> bool, i64, i64 {
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_ICAST || k == N_CAST {
        let op = nd.op as i64;
        if op == CK_BITCAST || op == CK_NOOP { return fold_addr(nd.a); }
        if op == CK_NULL2PTR { return true, -1, 0; }
        if op == CK_INT2PTR {
            let ok, v = fold_int(nd.a);
            return ok, -1, v;
        }
        if op == CK_ARRAY2PTR || op == CK_FUNC2PTR { return fold_lvaddr(nd.a); }
        if op == CK_LVAL2RVAL && kind_of(nd.ty) == TY_POINTER && cv_depth <= 32 {
            // a const pointer variable (G1)
            let init, w = cvar_member_init(nd.a);
            if init == 0 || w >= 0 { return false, 0, 0; }
            cv_depth++;
            let ok, b, o = fold_addr(init);
            cv_depth--;
            return ok, b, o;
        }
        return false, 0, 0;
    }
    if k == N_UNARY && nd.op == U_ADDR { return fold_lvaddr(nd.a); }
    if (k == N_CALL || k == N_BUILTIN) && fold_call_kind(n) == 2 {
        // memchr: where it finds the byte, or a null pointer
        let ok, j = fold_memchr(n);
        if !ok { return false, 0, 0; }
        if j < 0 { return true, -1, 0; }
        let ok2, b, o = fold_addr(nlist[nd.v]);
        if !ok2 { return false, 0, 0; }
        return true, b, o + j;
    }
    if k == N_BINARY && (nd.op == B_PTRADD || nd.op == B_PTRSUB) {
        let ok, b, o = fold_addr(nd.a);
        if !ok { return false, 0, 0; }
        let ok2, i = fold_int(nd.b);
        if !ok2 { return false, 0, 0; }
        var es: i64 = 1;
        let pt = tbase(nd.ty);
        if !is_void(pt) { es = type_size(pt); }
        if es <= 0 { return false, 0, 0; }
        if nd.op == B_PTRADD { return true, b, o + i * es; }
        return true, b, o - i * es;
    }
    return false, 0, 0;
}

recursive fn fold_lvaddr(n: u32) -> bool, i64, i64 {
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_STRING { return true, -2 - (n as i64), 0; }
    if k == N_DECLREF {
        let s = nd.a as i64;
        if syms[s].kind != SK_VAR && syms[s].kind != SK_FUNC { return false, 0, 0; }
        return true, s, 0;
    }
    if k == N_INDEX {
        let ok, b, o = fold_addr(nd.a);
        if !ok { return false, 0, 0; }
        let ok2, i = fold_int(nd.b);
        let es = type_size(nd.ty);
        if !ok2 || es <= 0 { return false, 0, 0; }
        return true, b, o + i * es;
    }
    if k == N_MEMBER {
        if nd.flags & NF_BITFIELD != 0 { return false, 0, 0; }
        var ok = false;
        var b: i64 = 0;
        var o: i64 = 0;
        if nd.op == 1 { ok, b, o = fold_addr(nd.a); } else { ok, b, o = fold_lvaddr(nd.a); }
        if !ok { return false, 0, 0; }
        return true, b, o + fields[nd.b].offset;
    }
    if k == N_UNARY && nd.op == U_DEREF { return fold_addr(nd.a); }
    return false, 0, 0;
}

// A constant complex value (re, im) for the comparisons clang folds.
recursive fn fold_cplx(n: u32) -> bool, f64, f64 {
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_ICAST || k == N_CAST {
        let op = nd.op as i64;
        if op == CK_REAL2COMPLEX {
            if is_real_float(nodes[nd.a].ty) {
                let ok, f = fold_float(nd.a);
                return ok, f, 0.0;
            }
            let ok, v = fold_int(nd.a);
            if !ok { return false, 0.0, 0.0; }
            if is_signed(nodes[nd.a].ty) { return true, v as f64, 0.0; }
            return true, (v as! u64) as f64, 0.0;
        }
        if op == CK_COMPLEXCAST || op == CK_NOOP {
            let ok, re, im = fold_cplx(nd.a);
            if !ok { return false, 0.0, 0.0; }
            if kind_of(cplx_base_of(nd.ty)) == TY_FLOAT { return true, round_f32(re), round_f32(im); }
            return true, re, im;
        }
        return false, 0.0, 0.0;
    }
    if k == N_UNARY && (nd.op == U_NEG || nd.op == U_PLUS) {
        let ok, re, im = fold_cplx(nd.a);
        if nd.op == U_NEG { return ok, -re, -im; }
        return ok, re, im;
    }
    return false, 0.0, 0.0;
}
fn cplx_base_of(t: u32) -> u32 { tbase(t) }

// A pointer clang's evaluator follows into a constant object (G1): the
// initializer of the array it points into (single: of the one object it
// points at, an array of one), the element count, the element index (up
// to one past the end) and the element type.
struct CPtr { init: u32, single: bool, alen: i64, k: i64, ety: u32 }

recursive fn cptr_eval(p: u32) -> bool, CPtr {
    let none = CPtr { init: 0, single: false, alen: 0, k: 0, ety: 0 };
    let nd = nodes[p];
    let k = nd.kind as i64;
    if k == N_ICAST || k == N_CAST {
        let op = nd.op as i64;
        if op == CK_NOOP || op == CK_BITCAST { return cptr_eval(nd.a); }
        if op == CK_ARRAY2PTR {
            let a = nd.a;
            let at = unqual(nodes[a].ty);
            if nodes[a].kind == N_STRING {
                let sl = strs[nodes[a].a];
                return true, CPtr { init: a, single: false, alen: sl.len as i64 + 1, k: 0, ety: sl.elem };
            }
            if !is_array(at) || kind_of(at) == TY_VLA || types[at >> 4].n < 0 { return false, none; }
            let init, w = cvar_member_init(a);
            if init == 0 { return false, none; }
            return true, CPtr { init: init, single: false, alen: types[at >> 4].n, k: 0, ety: tbase(at) };
        }
        if op == CK_LVAL2RVAL && kind_of(nd.ty) == TY_POINTER && fold_cvars {
            // a const pointer variable: what its initializer points at
            if cv_depth > 32 { return false, none; }
            let init, w = cvar_member_init(nd.a);
            if init == 0 || w >= 0 { return false, none; }
            cv_depth++;
            let ok, P = cptr_eval(init);
            cv_depth--;
            return ok, P;
        }
        return false, none;
    }
    if k == N_UNARY && nd.op == U_ADDR {
        let a = nodes[nd.a];
        if a.kind == N_INDEX {
            // &p[i]: p + i
            let ok, P = cptr_eval(a.a);
            if !ok { return false, none; }
            let ok2, i = fold_int(a.b);
            if !ok2 { return false, none; }
            return cptr_adjust(P, i, a.ty);
        }
        if a.kind == N_UNARY && a.op == U_DEREF { return cptr_eval(a.a); }
        // the whole object: &c, &s, &x.f
        var init: u32 = 0;
        if a.kind == N_STRING { init = nd.a; } else {
            let i2, w = cvar_member_init(nd.a);
            if w >= 0 { return false, none; }
            init = i2;
        }
        if init == 0 { return false, none; }
        return true, CPtr { init: init, single: true, alen: 1, k: 0, ety: unqual(a.ty) };
    }
    if k == N_BINARY && (nd.op == B_PTRADD || nd.op == B_PTRSUB) {
        let ok, P = cptr_eval(nd.a);
        if !ok { return false, none; }
        let ok2, i = fold_int(nd.b);
        if !ok2 { return false, none; }
        return cptr_adjust(P, if nd.op == B_PTRADD { i } else { -i }, tbase(nd.ty));
    }
    return false, none;
}

// P moved by i elements of type et (that of the pointer arithmetic).
fn cptr_adjust(P: CPtr, i: i64, et: u32) -> bool, CPtr {
    if type_size(et) != type_size(P.ety) { return false, P; }
    let k = P.k + i;
    if k < 0 || k > P.alen { return false, P; }
    var Q = P;
    Q.k = k;
    return true, Q;
}

// Element P.k + j, a character (one-byte integer type) the evaluator reads.
fn cptr_read(P: CPtr, j: i64) -> bool, i64 {
    let i = P.k + j;
    if i < 0 || i >= P.alen || type_size(P.ety) != 1 || !is_integer(P.ety) || kind_of(P.ety) == TY_BOOL { return false, 0; }
    var e: u32 = 0;
    if P.single { e = P.init; } else {
        let nd = nodes[P.init];
        if nd.kind == N_STRING {
            let sl = strs[nd.a];
            if type_size(sl.elem) != 1 { return false, 0; }
            if i < sl.len as i64 { return true, trunc_to(strbytes[sl.start as i64 + i] as i64, P.ety); }
            return true, 0;
        }
        if nd.kind != N_INITLIST { return false, 0; }
        if i < nd.c as i64 { e = nlist[nd.v + i]; } else { e = nd.b; }
        if e == 0 { return true, 0; }
    }
    cv_depth++;
    let ok, v = fold_int(e);
    cv_depth--;
    if !ok { return false, 0; }
    return true, trunc_to(v, P.ety);
}

// A call of a library function the evaluator folds (strlen 1, memchr 2), or
// of its __builtin_ form; 0 if none.
fn fold_call_kind(n: u32) -> i64 {
    let nd = nodes[n];
    if nd.kind == N_BUILTIN && nd.op == BI_CALL {
        let nm = ident_text(syms[nd.a].name as i64);
        if nm == "__builtin_strlen" && nd.c == 1 { return 1; }
        if nm == "__builtin_memchr" && nd.c == 3 { return 2; }
        return 0;
    }
    if nd.kind != N_CALL { return 0; }
    var c = nd.a;
    while nodes[c].kind == N_ICAST && nodes[c].op == CK_FUNC2PTR { c = nodes[c].a; }
    if nodes[c].kind != N_DECLREF { return 0; }
    let s = nodes[c].a as i64;
    let sy = syms[s];
    if sy.kind != SK_FUNC || sy.sc == SC_STATIC { return 0; }
    if sy.attr != 0 && sym_attrs[sy.attr].asm_len != 0 { return 0; }
    let ft = types[sy.ty >> 4];
    if sy.name == fold_lib_strlen && nd.c == 1 && ft.n == 1 && kind_of(ft.base) == TY_ULONG { return 1; }
    if sy.name == fold_lib_memchr && nd.c == 3 && ft.n == 3 && kind_of(ft.base) == TY_POINTER { return 2; }
    return 0;
}

// strlen(p) as the evaluator folds it (EvaluateBuiltinStrLen).
fn fold_strlen(p: u32) -> bool, i64 {
    let ok, P = cptr_eval(p);
    if !ok { return false, 0; }
    var j: i64 = 0;
    loop {
        let ok2, c = cptr_read(P, j);
        if !ok2 { return false, 0; }
        if c == 0 { return true, j; }
        j++;
    }
    return false, 0;
}

// memchr(p, c, n): the index of the byte found (-1 not found: a null pointer).
fn fold_memchr(n: u32) -> bool, i64 {
    let nd = nodes[n];
    let ok, P = cptr_eval(nlist[nd.v]);
    if !ok { return false, 0; }
    let okc, c = fold_int(nlist[nd.v + 1]);
    let okn, len = fold_int(nlist[nd.v + 2]);
    if !okc || !okn { return false, 0; }
    if len == 0 { return true, -1; }
    var j: i64 = 0;
    while (j as! u64) < (len as! u64) {
        let ok2, v = cptr_read(P, j);
        if !ok2 { return false, 0; }
        if v & 255 == c & 255 { return true, j; }
        j++;
    }
    return true, -1;
}

// The initializer of variable s that a read of it folds to, or 0: a const,
// non-volatile, non-weak variable defined with an initializer (cvar_init,
// filled by the lowering), whose definition clang had seen when it emitted
// the code being lowered (CodeGen emits an external definition as it is
// parsed, deferred ones after the unit).
fn cvar_value_init(s: i64) -> u32 {
    if !fold_cvars || s < 0 || s >= cvar_init.len || cv_depth > 32 { return 0; }
    let init = cvar_init[s];
    if init == 0 { return 0; }
    if syms[s].flags & SF_FILESCOPE != 0 && !cv_ctx_late && cvar_decl[s] >= cv_ctx { return 0; }
    return init;
}

// The initializer a read of member chain n (s.f.g, a[2].f: a const
// variable's, with constant indices) folds to, and the bit-field width of
// the last member (-1: none); 0 if none.
recursive fn cvar_member_init(n: u32) -> u32, i64 {
    let nd = nodes[n];
    if nd.kind == N_DECLREF { return cvar_value_init(nd.a as i64), -1; }
    if nd.kind == N_INDEX {
        let ok, i = fold_int(nd.b);
        if !ok || i < 0 { return 0, -1; }
        let b = nodes[nd.a];
        if b.kind != N_ICAST || b.op != CK_ARRAY2PTR {
            // p[i]: through a pointer clang's evaluator follows (G1)
            let pinit, k = cvar_ptr_init(nd.a);
            if pinit == 0 { return 0, -1; }
            return cvar_elem_init(pinit, k, i), -1;
        }
        let init, w = cvar_member_init(b.a);
        if init == 0 || nodes[init].kind != N_INITLIST { return 0, -1; }
        let il = nodes[init];
        if i < il.c as i64 { return nlist[il.v + i], -1; }
        if il.b != 0 { return il.b, -1; }
        return 0, -1;
    }
    if nd.kind == N_UNARY && nd.op == U_DEREF {
        // *p: through a pointer clang's evaluator follows (G1)
        let init, k = cvar_ptr_init(nd.a);
        if init == 0 { return 0, -1; }
        return cvar_elem_init(init, k, 0), -1;
    }
    if nd.kind == N_MEMBER && nd.op == 0 {
        let init, w = cvar_member_init(nd.a);
        return cvar_field_init(init, nodes[nd.a].ty, nd.b as i64);
    }
    if nd.kind == N_MEMBER && nd.op == 1 {
        // p->f: the object p points at (G1)
        let init, k = cvar_ptr_init(nd.a);
        if init == 0 { return 0, -1; }
        return cvar_field_init(cvar_elem_init(init, k, 0), tbase(nodes[nd.a].ty), nd.b as i64);
    }
    return 0, -1;
}

// Member f's initializer in a record initializer of record type rt, and its
// bit-field width (-1: none); 0 if none.
fn cvar_field_init(init: u32, rt: u32, f: i64) -> u32, i64 {
    if init == 0 || nodes[init].kind != N_INITLIST || !is_record(rt) { return 0, -1; }
    let il = nodes[init];
    let r = rec_of(rt);
    if records[r].flags & RF_UNION != 0 {
        if il.a as i64 != f - (records[r].first as i64) + 1 || il.c == 0 { return 0, -1; }
        return nlist[il.v], fields[f].width as i64;
    }
    // one child per member but unnamed bit-fields
    var ci: i64 = 0;
    for i in (records[r].first as i64)..f {
        if fields[i].width >= 0 && fields[i].name == 0 { continue; }
        ci++;
    }
    if ci >= il.c as i64 { return 0, -1; }
    return nlist[il.v + ci], fields[f].width as i64;
}

// Element k + i of the array whose initializer is init (k -1: init is a
// single object, element 0 only); 0 if none.
fn cvar_elem_init(init: u32, k: i64, i: i64) -> u32 {
    if k < 0 { return if i == 0 { init } else { 0 }; }
    if nodes[init].kind != N_INITLIST { return 0; }
    let il = nodes[init];
    let j = k + i;
    if j < il.c as i64 { return nlist[il.v + j]; }
    if il.b != 0 { return il.b; }
    return 0;
}

// The object pointer rvalue p points at when clang's evaluator follows
// it: a const pointer variable's initializer &X or X (an array), X a
// const variable (or a member or element of one) or a string literal. The
// object's initializer, and the element index (-1: not an array element).
recursive fn cvar_ptr_init(p: u32) -> u32, i64 {
    var n = p;
    while nodes[n].kind == N_ICAST && nodes[n].op == CK_NOOP { n = nodes[n].a; }
    let nd = nodes[n];
    if nd.kind == N_ICAST && nd.op == CK_LVAL2RVAL {
        if cv_depth > 32 { return 0, -1; }
        let init, w = cvar_member_init(nd.a);
        if init == 0 || w >= 0 { return 0, -1; }
        cv_depth++;
        let r, k = cvar_ptr_init(init);
        cv_depth--;
        return r, k;
    }
    if nd.kind == N_UNARY && nd.op == U_ADDR {
        let a = nodes[nd.a];
        if a.kind == N_INDEX {
            // &b[i]: b + i
            let ok, i = fold_int(a.b);
            if !ok { return 0, -1; }
            let init, k = cvar_ptr_init(a.a);
            if init == 0 || k < 0 { return 0, -1; }
            return init, k + i;
        }
        let init, w = cvar_member_init(nd.a);
        return init, -1;
    }
    if nd.kind == N_ICAST && nd.op == CK_ARRAY2PTR {
        if nodes[nd.a].kind == N_STRING { return nd.a, 0; }
        let init, w = cvar_member_init(nd.a);
        return init, 0;
    }
    if nd.kind == N_BINARY && (nd.op == B_PTRADD || nd.op == B_PTRSUB) {
        let ok, i = fold_int(nd.b);
        if !ok { return 0, -1; }
        let init, k = cvar_ptr_init(nd.a);
        if init == 0 { return 0, -1; }
        let d = if nd.op == B_PTRADD { i } else { -i };
        if k < 0 { return if d == 0 { init } else { 0 }, -1; }
        if k + d < 0 { return 0, -1; }
        return init, k + d;
    }
    return 0, -1;
}

// A read of a const variable (or a member of one) folded as an integer.
recursive fn fold_cvar_int(n: u32) -> bool, i64 {
    let nd = nodes[n];
    let a = nodes[nd.a];
    var init: u32 = 0;
    var w: i64 = -1;
    if a.kind == N_DECLREF {
        init = cvar_value_init(a.a as i64);
    } else if a.kind == N_MEMBER || a.kind == N_INDEX {
        init, w = cvar_member_init(nd.a);
        if init == 0 && a.kind == N_INDEX && is_integer(nd.ty) {
            // an element of a const character array initialized by a string
            let ok, i0 = fold_int(a.b);
            if !ok || i0 < 0 { return false, 0; }
            var i = i0;
            let b = nodes[a.a];
            var si: u32 = 0;
            if b.kind == N_ICAST && b.op == CK_ARRAY2PTR {
                if nodes[b.a].kind == N_STRING { si = b.a; } else { let si2, w2 = cvar_member_init(b.a); si = si2; }
            } else {
                // through a pointer to a character array (G1)
                let si2, k = cvar_ptr_init(a.a);
                if k < 0 { return false, 0; }
                si = si2;
                i = i + k;
            }
            if si == 0 || nodes[si].kind != N_STRING { return false, 0; }
            let sl = strs[nodes[si].a];
            let es = type_size(sl.elem);
            let at = types[unqual(nodes[si].ty) >> 4];
            if es <= 0 || es > 8 || at.n >= 0 && i >= at.n { return false, 0; }
            var v: i64 = 0;
            if i < sl.len as i64 {   // (len counts elements)
                for k in es { v = v | ((strbytes[sl.start as i64 + i * es + k] as i64) << ((8 * k) as! u64)); }
            }
            return true, trunc_to(v, nd.ty);
        }
    }
    if init == 0 { return false, 0; }
    cv_depth++;
    let ok, v0 = fold_int(init);
    cv_depth--;
    if !ok { return false, 0; }
    var v = v0;
    if w > 0 && w < 64 {
        // a bit-field holds its width's bits
        let m = (1 << (w as! u64)) - 1;
        v = v & m;
        if is_signed(nd.ty) && v >= (1 << ((w - 1) as! u64)) { v = v - (1 << (w as! u64)); }
    }
    if kind_of(nd.ty) == TY_POINTER { return true, v; }
    if !is_integer(nd.ty) { return false, 0; }
    return true, trunc_to(v, nd.ty);
}

recursive fn fold_int(n: u32) -> bool, i64 {
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_INT {
        if nd.flags & NF_BCP != 0 && fold_cvars {
            // G1: folds now if its operand does; else not at all
            if bcp_fold(nd.a) { return true, 1; }
            return false, 0;
        }
        return true, nd.v;
    }
    if k == N_SIZEOF || k == N_OFFSETOF {
        if nd.v < 0 { return false, 0; }
        return true, nd.v;
    }
    if (k == N_CALL || k == N_BUILTIN) && fold_cvars && fold_call_kind(n) == 1 {
        let ok, v = fold_strlen(nlist[nd.v]);
        if !ok { return false, 0; }
        return true, trunc_to(v, nd.ty);
    }
    if k == N_ICAST || k == N_CAST {
        let op = nd.op as i64;
        if op == CK_LVAL2RVAL && fold_cvars { return fold_cvar_int(n); }
        if op == CK_LVAL2RVAL || op == CK_ARRAY2PTR || op == CK_FUNC2PTR { return false, 0; }
        if op == CK_PTR2INT && fold_cvars {
            // (size_t)&((T *)0)->m and other offsets from a null pointer
            let ok, b, o = fold_addr(nd.a);
            if !ok || b != -1 { return false, 0; }
            return true, trunc_to(o, nd.ty);
        }
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
        if op == CK_PTR2BOOL && fold_cvars {
            let ok, b = fold_bool(nd.a);
            return ok, if b { 1 } else { 0 };
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
            if fold_cvars && kind_of(nodes[nd.a].ty) == TY_POINTER {
                let ok, b = fold_bool(nd.a);
                return ok, if b { 0 } else { 1 };
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
        if fold_cvars && (op == B_PTRDIFF || (kind_of(at) == TY_POINTER && is_cmp_op_s(op))) {
            // addresses of one base: their difference, their order (G1)
            let ok, b1, o1 = fold_addr(nd.a);
            if !ok { return false, 0; }
            let ok2, b2, o2 = fold_addr(nd.b);
            if !ok2 { return false, 0; }
            if b1 != b2 {
                // the address of an object is not a null pointer (unless weak)
                let nul1 = b1 == -1 && o1 == 0;
                let nul2 = b2 == -1 && o2 == 0;
                if (op == B_EQ || op == B_NE) && nul1 != nul2 && (nul1 || b1 != -1) && (nul2 || b2 != -1) &&
                   !addr_weak(if nul1 { b2 } else { b1 }) {
                    return true, if op == B_NE { 1 } else { 0 };
                }
                return false, 0;
            }
            if op == B_PTRDIFF {
                var es: i64 = 1;
                let pt = tbase(at);
                if !is_void(pt) { es = type_size(pt); }
                if es <= 0 { return false, 0; }
                return true, trunc_to((o1 - o2) / es, nd.ty);
            }
            let c = match op { B_LT => o1 < o2, B_GT => o1 > o2, B_LE => o1 <= o2, B_GE => o1 >= o2, B_EQ => o1 == o2, _ => o1 != o2 };
            return true, if c { 1 } else { 0 };
        }
        if fold_cvars && (op == B_EQ || op == B_NE) && is_complex(at) {
            let ok, r1, i1 = fold_cplx(nd.a);
            let ok2, r2, i2 = fold_cplx(nd.b);
            if !ok || !ok2 { return false, 0; }
            let eq = r1 == r2 && i1 == i2;
            return true, if (op == B_EQ) == eq { 1 } else { 0 };
        }
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

// Is base b (fold_addr) a weak symbol?
fn addr_weak(b: i64) -> bool {
    if b < 0 { return false; }
    let sy = syms[b];
    return sy.flags & SF_WEAK != 0 || (sy.attr != 0 && sym_attrs[sy.attr].flags & AM_WEAK != 0);
}

// An operand of __builtin_constant_p without side effects for sure (reads
// of non-volatile objects, constants, casts and arithmetic of such).
recursive fn bcp_simple(n: u32) -> bool {
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_INT || k == N_FLOAT || k == N_STRING || k == N_DECLREF || k == N_SIZEOF || k == N_OFFSETOF { return true; }
    if k == N_ICAST || k == N_CAST {
        if nd.op == CK_LVAL2RVAL && quals(nodes[nd.a].ty) & Q_VOLATILE != 0 { return false; }
        return bcp_simple(nd.a);
    }
    if k == N_UNARY {
        let op = nd.op as i64;
        if op == U_PREINC || op == U_PREDEC || op == U_POSTINC || op == U_POSTDEC { return false; }
        return bcp_simple(nd.a);
    }
    if k == N_BINARY { return nd.op != B_COMMA && bcp_simple(nd.a) && bcp_simple(nd.b); }
    if k == N_MEMBER { return bcp_simple(nd.a); }
    if k == N_INDEX { return bcp_simple(nd.a) && bcp_simple(nd.b); }
    return false;
}

// __builtin_constant_p of operand x as clang's evaluator decides it in
// CodeGen (EvaluateBuiltinConstantP): a constant, or a pointer that is null
// or to the first character of a string literal.
recursive fn bcp_fold(x: u32) -> bool {
    let t = nodes[x].ty;
    if kind_of(t) == TY_POINTER {
        let ok, b, o = fold_addr(x);
        return ok && (b == -1 || (b <= -2 && o == 0));
    }
    if is_real_float(t) {
        let ok, f = fold_float(x);
        return ok;
    }
    let ok, v = fold_int(x);
    return ok;
}

fn is_cmp_op_s(op: i64) -> bool { op == B_LT || op == B_GT || op == B_LE || op == B_GE || op == B_EQ || op == B_NE }

recursive fn fold_bool(n: u32) -> bool, bool {
    if is_real_float(nodes[n].ty) {
        let ok, f = fold_float(n);
        return ok, f != 0.0;
    }
    let ok, v = fold_int(n);
    if ok { return true, v != 0; }
    // the address of an object or function is never null, unless it is
    // weak (G1: clang's evaluator does not fold that one)
    let ok2, sym = address_base(n);
    if ok2 && (sym < 0 || syms[sym].flags & SF_WEAK == 0) { return true, true; }
    if fold_cvars && kind_of(nodes[n].ty) == TY_POINTER {
        // G1: what fold_addr follows (const pointer variables, memchr)
        let ok3, b, o = fold_addr(n);
        if ok3 && b == -1 { return true, o != 0; }
        if ok3 && !addr_weak(b) { return true, true; }
    }
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
    if k == N_BUILTIN && nd.op == BI_CALL && fold_cvars && nd.c == 0 {
        // __builtin_huge_val, __builtin_inf and their f/l forms (G1)
        let nm = ident_text(syms[nd.a].name as i64);
        if nm == "__builtin_huge_val" || nm == "__builtin_huge_valf" || nm == "__builtin_huge_vall" ||
           nm == "__builtin_inf" || nm == "__builtin_inff" || nm == "__builtin_infl" {
            return true, 1.0 / 0.0;
        }
        return false, 0.0;
    }
    if k == N_INT {
        if nd.flags & NF_BCP != 0 && fold_cvars {
            if bcp_fold(nd.a) { return true, 1.0; }
            return false, 0.0;
        }
        if is_signed(nd.ty) { return true, nd.v as f64; }
        return true, (nd.v as! u64) as f64;
    }
    if k == N_ICAST || k == N_CAST {
        let op = nd.op as i64;
        if op == CK_LVAL2RVAL && fold_cvars && is_real_float(nd.ty) {
            // a const variable's (G1)
            var init: u32 = 0;
            let ak = nodes[nd.a].kind as i64;
            if ak == N_DECLREF { init = cvar_value_init(nodes[nd.a].a as i64); }
            else if ak == N_MEMBER || ak == N_INDEX { let i2, w = cvar_member_init(nd.a); init = i2; }
            if init == 0 { return false, 0.0; }
            cv_depth++;
            let ok, f = fold_float(init);
            cv_depth--;
            return ok, f;
        }
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
        if nd.op == U_NEG { return true, -f; }
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
