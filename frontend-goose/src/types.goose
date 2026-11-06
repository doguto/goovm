// goosecc: the C type system. Types are uniqued in a global table, so two
// canonical types are equal exactly when their indices are. A "qtype" is a
// u32: (type index << 4) | qualifiers. Record (struct/union) layout follows
// the SysV x86-64 ABI as clang implements it.

import std;
import .common;

let Q_CONST = 1;
let Q_VOLATILE = 2;
let Q_RESTRICT = 4;
let Q_ATOMIC = 8;
let Q_MASK = 15;

let TY_VOID = 1;
let TY_BOOL = 2;
let TY_CHAR = 3;
let TY_SCHAR = 4;
let TY_UCHAR = 5;
let TY_SHORT = 6;
let TY_USHORT = 7;
let TY_INT = 8;
let TY_UINT = 9;
let TY_LONG = 10;
let TY_ULONG = 11;
let TY_LLONG = 12;
let TY_ULLONG = 13;
let TY_INT128 = 14;
let TY_UINT128 = 15;
let TY_FLOAT16 = 16;
let TY_BF16 = 17;
let TY_FLOAT = 18;
let TY_DOUBLE = 19;
let TY_LDOUBLE = 20;
let TY_FLOAT128 = 21;
let TY_COMPLEX = 22;    // base = element type
let TY_POINTER = 23;    // base = pointee
let TY_ARRAY = 24;      // base = element, n = length (-1 incomplete)
let TY_VLA = 25;        // base = element, n = size expression node
let TY_FUNC = 26;       // base = return type, n = param count, extra = first param in tparams
let TY_STRUCT = 27;     // extra = record id
let TY_UNION = 28;      // extra = record id
let TY_ENUM = 29;       // extra = enum id, base = underlying type once complete
let TY_VECTOR = 30;     // base = element, n = lanes
let TY_EXTVECTOR = 31;  // clang ext_vector_type

let TF_VARIADIC = 1;
let TF_NOPROTO = 2;     // K&R or ()
let TF_NORETURN = 4;    // function type carries noreturn
let TF_ALIGNED = 8;     // an alignment override (typedef with aligned attribute)

struct Type {
    kind: u8,
    flags: u8,
    rsv1: u16,
    align: u32,
    size: i64,
    base: u32,
    extra: u32,
    n: i64,
    canon: u32,     // the type without alignment overrides
    hnext: i32,
}

var types: Type[>..] = [];
var tparams: u32[>..] = [];
var tyhash: i32[>..<] = [];      // bucket heads
var tymask: i64 = 0;

struct Record {
    name: u32,
    ty: u32,
    first: u32,
    count: u32,
    size: i64,
    align: u32,
    flags: u16,
    rsv: u16,
    attr_align: u32,    // aligned(N) on the record
    pack: u32,          // #pragma pack in effect at the definition (0 = none)
    loc: u32,
    scope: u32,         // scope depth of the definition
}
let RF_UNION = 1;
let RF_COMPLETE = 2;
let RF_PACKED = 4;
let RF_FLEX = 8;
let RF_TRANSPARENT = 16;
let RF_BEING_DEFINED = 32;
let RF_HAS_BITFIELD = 64;
let RF_CONST_MEMBER = 128;   // some member (recursively) is const
let RF_VOLATILE_MEMBER = 256;
let RF_MSSTRUCT = 512;

struct Field {
    name: u32,
    ty: u32,        // qtype
    offset: i64,    // bytes, for non-bit-fields; storage start for bit-fields
    bitpos: i64,    // bit offset from the start of the record
    width: i32,     // bit-field width, -1 for an ordinary member
    attr_align: u32,
    flags: u8,      // FF_*
    rsv: u8,
    rsv2: u16,
    loc: u32,
}
let FF_PACKED = 1;
let FF_ANON = 2;     // an anonymous struct/union member

var records: Record[>..] = [];
var fields: Field[>..] = [];

struct EnumRec {
    name: u32,
    ty: u32,
    underlying: u32,
    complete: bool,
    packed: bool,
    rsv: u16,
    loc: u32,
    scope: u32,
}
var enums: EnumRec[>..] = [];

// Builtin type indices (filled by types_init).
var t_void: u32 = 0;
var t_bool: u32 = 0;
var t_char: u32 = 0;
var t_schar: u32 = 0;
var t_uchar: u32 = 0;
var t_short: u32 = 0;
var t_ushort: u32 = 0;
var t_int: u32 = 0;
var t_uint: u32 = 0;
var t_long: u32 = 0;
var t_ulong: u32 = 0;
var t_llong: u32 = 0;
var t_ullong: u32 = 0;
var t_int128: u32 = 0;
var t_uint128: u32 = 0;
var t_float16: u32 = 0;
var t_bf16: u32 = 0;
var t_float: u32 = 0;
var t_double: u32 = 0;
var t_ldouble: u32 = 0;
var t_float128: u32 = 0;
var t_valist: u32 = 0;       // __builtin_va_list = struct __va_list_tag [1]
var t_valist_rec: u32 = 0;
var t_voidptr: u32 = 0;
var t_charptr: u32 = 0;
var t_cvoidptr: u32 = 0;
var t_ccharptr: u32 = 0;
var t_size: u32 = 0;         // unsigned long
var t_ptrdiff: u32 = 0;      // long
var t_wchar: u32 = 0;        // int

// ---------------------------------------------------------------------------
// qtype helpers

fn qt(t: i64, q: i64) -> u32 { ((t << 4) | q) as! u32 }
fn tyi(q: u32) -> i64 { (q >> 4) as i64 }
fn quals(q: u32) -> i64 { (q & 15) as i64 }
fn unqual(q: u32) -> u32 { q & 4294967280 }
fn with_quals(q: u32, add: i64) -> u32 { q | (add as! u32) }
fn kind_of(q: u32) -> i64 { types[q >> 4].kind as i64 }
fn tbase(q: u32) -> u32 { types[q >> 4].base }
fn tcanon(q: u32) -> u32 { qt(types[q >> 4].canon as i64, quals(q)) }

// ---------------------------------------------------------------------------
// Uniquing

fn ty_hash(kind: i64, flags: i64, base: u32, n: i64, extra: u32, align: u32) -> u64 {
    var h: u64 = (kind as! u64) * 1000003;
    h = (h ^ (flags as! u64)) * 1099511628211;
    h = (h ^ (base as u64)) * 1099511628211;
    h = (h ^ (n as! u64)) * 1099511628211;
    h = (h ^ (extra as u64)) * 1099511628211;
    h = (h ^ (align as u64)) * 1099511628211;
    return h ^ (h >> 29);
}

fn ty_grow() {
    let n = if tyhash.len == 0 { 4096 } else { tyhash.len * 2 };
    tyhash.clear();
    tyhash.resize(n, -1);
    tymask = n - 1;
    for t, i in types {
        if i == 0 { continue; }
        if t.kind == TY_STRUCT || t.kind == TY_UNION || t.kind == TY_ENUM {
            if t.flags & TF_ALIGNED == 0 { types[i].hnext = -1; continue; }
        }
        let h = ty_hash(t.kind as i64, t.flags as i64, t.base, t.n, t.extra, if t.flags & TF_ALIGNED != 0 { t.align } else { 0 });
        let b = (h as! i64) & tymask;
        types[i].hnext = tyhash[b];
        tyhash[b] = i as! i32;
    }
}

// The function-type params being built are in fn_scratch.
var fn_scratch: u32[>..<] = [];

fn params_equal(first: u32, n: i64) -> bool {
    if n != fn_scratch.len { return false; }
    for i in n { if tparams[first + i] != fn_scratch[i] { return false; } }
    return true;
}

// Finds or makes the type (kind, flags, base, n, extra). For TY_FUNC the
// parameters are in fn_scratch and `extra` is ignored. align: an alignment
// override (0 = natural).
recursive fn mk_type(kind: i64, flags: i64, base: u32, n: i64, extra: u32, align: u32) -> u32 {
    if (types.len + 1) * 2 > tyhash.len { ty_grow(); }
    var ex = extra;
    var hn = n;
    if kind == TY_FUNC {
        var h2: u64 = 7;
        for p in fn_scratch { h2 = (h2 ^ (p as u64)) * 1099511628211; }
        ex = (h2 ^ (h2 >> 32)) as! u32;
        hn = fn_scratch.len;
    }
    let h = ty_hash(kind, flags, base, hn, ex, align);
    let b = (h as! i64) & tymask;
    var i = tyhash[b] as i64;
    while i >= 0 {
        let t = types[i];
        if t.kind as i64 == kind && t.flags as i64 == flags && t.base == base && (if align != 0 { t.align == align } else { t.flags & TF_ALIGNED == 0 }) {
            if kind == TY_FUNC {
                if t.n == hn && params_equal(t.extra, hn) { return i as! u32; }
            } else if t.n == n && t.extra == extra {
                return i as! u32;
            }
        }
        i = t.hnext as i64;
    }
    let id = types.len;
    var e = extra;
    if kind == TY_FUNC {
        e = tparams.len as! u32;
        for p in fn_scratch { tparams.push(p); }
    }
    var fl = flags;
    if align != 0 { fl = fl | TF_ALIGNED; }
    types.push(Type { kind: kind as! u8, flags: fl as! u8, rsv1: 0, align: 0, size: -1, base: base, extra: e, n: hn, canon: id as! u32, hnext: tyhash[b] });
    tyhash[b] = id as! i32;
    compute_size(id);
    if align != 0 {
        types[id].align = align;
        types[id].canon = mk_type(kind, flags, base, n, extra, 0);
    }
    return id as! u32;
}

fn compute_size(id: i64) {
    let t = types[id];
    let k = t.kind as i64;
    var size: i64 = -1;
    var al: u32 = 1;
    if k == TY_POINTER { size = 8; al = 8; }
    else if k == TY_ARRAY {
        let e = types[t.base >> 4];
        if t.n >= 0 && e.size >= 0 { size = e.size * t.n; }
        al = e.align;
    } else if k == TY_VLA {
        al = types[t.base >> 4].align;
    } else if k == TY_COMPLEX {
        let e = types[t.base >> 4];
        size = e.size * 2;
        al = e.align;
    } else if k == TY_VECTOR || k == TY_EXTVECTOR {
        let e = types[t.base >> 4];
        size = e.size * t.n;
        // clang: the alignment is the size, rounded up to a power of two
        var a: i64 = 1;
        while a < size { a *= 2; }
        if k == TY_EXTVECTOR {
            size = a;
        }
        al = a as! u32;
    } else if k == TY_FUNC {
        size = -1;
        al = 1;
    }
    types[id].size = size;
    types[id].align = al;
}

fn mk_ptr(to: u32) -> u32 { qt(mk_type(TY_POINTER, 0, to, 0, 0, 0) as i64, 0) }
fn mk_array(elem: u32, n: i64) -> u32 { qt(mk_type(TY_ARRAY, 0, elem, n, 0, 0) as i64, 0) }
fn mk_complex(elem: u32) -> u32 { qt(mk_type(TY_COMPLEX, 0, unqual(elem), 0, 0, 0) as i64, 0) }

fn mk_vla(elem: u32, size_node: i64) -> u32 {
    // VLAs are not uniqued: each has its own size expression.
    let id = types.len;
    types.push(Type { kind: TY_VLA, flags: 0, rsv1: 0, align: types[elem >> 4].align, size: -1, base: elem, extra: 0, n: size_node, canon: id as! u32, hnext: -1 });
    return qt(id, 0);
}

fn mk_basic(kind: i64, size: i64, al: u32) -> u32 {
    let id = types.len;
    types.push(Type { kind: kind as! u8, flags: 0, rsv1: 0, align: al, size: size, base: 0, extra: 0, n: 0, canon: id as! u32, hnext: -1 });
    return id as! u32;
}

// A record or enum type: not uniqued.
fn mk_tagged(kind: i64, extra: u32) -> u32 {
    let id = types.len;
    types.push(Type { kind: kind as! u8, flags: 0, rsv1: 0, align: 1, size: -1, base: 0, extra: extra, n: 0, canon: id as! u32, hnext: -1 });
    return id as! u32;
}

// The same type with alignment `al` (typedef ... __attribute__((aligned))).
fn with_align(q: u32, al: u32) -> u32 {
    let t = types[q >> 4];
    let k = t.kind as i64;
    let id = types.len;
    types.push(Type { kind: t.kind, flags: t.flags | TF_ALIGNED, rsv1: 0, align: al, size: t.size, base: t.base, extra: t.extra, n: t.n, canon: t.canon, hnext: -1 });
    return qt(id, quals(q));
}

fn types_init() {
    types.push(Type { kind: 0, flags: 0, rsv1: 0, align: 0, size: 0, base: 0, extra: 0, n: 0, canon: 0, hnext: -1 });
    t_void = mk_basic(TY_VOID, -1, 1) << 4;
    t_bool = mk_basic(TY_BOOL, 1, 1) << 4;
    t_char = mk_basic(TY_CHAR, 1, 1) << 4;
    t_schar = mk_basic(TY_SCHAR, 1, 1) << 4;
    t_uchar = mk_basic(TY_UCHAR, 1, 1) << 4;
    t_short = mk_basic(TY_SHORT, 2, 2) << 4;
    t_ushort = mk_basic(TY_USHORT, 2, 2) << 4;
    t_int = mk_basic(TY_INT, 4, 4) << 4;
    t_uint = mk_basic(TY_UINT, 4, 4) << 4;
    t_long = mk_basic(TY_LONG, 8, 8) << 4;
    t_ulong = mk_basic(TY_ULONG, 8, 8) << 4;
    t_llong = mk_basic(TY_LLONG, 8, 8) << 4;
    t_ullong = mk_basic(TY_ULLONG, 8, 8) << 4;
    t_int128 = mk_basic(TY_INT128, 16, 16) << 4;
    t_uint128 = mk_basic(TY_UINT128, 16, 16) << 4;
    t_float16 = mk_basic(TY_FLOAT16, 2, 2) << 4;
    t_bf16 = mk_basic(TY_BF16, 2, 2) << 4;
    t_float = mk_basic(TY_FLOAT, 4, 4) << 4;
    t_double = mk_basic(TY_DOUBLE, 8, 8) << 4;
    t_ldouble = mk_basic(TY_LDOUBLE, 16, 16) << 4;
    t_float128 = mk_basic(TY_FLOAT128, 16, 16) << 4;
    tyhash.resize(4096, -1);
    tymask = 4095;
    t_voidptr = mk_ptr(t_void);
    t_charptr = mk_ptr(t_char);
    t_cvoidptr = mk_ptr(t_void | Q_CONST);
    t_ccharptr = mk_ptr(t_char | Q_CONST);
    t_size = t_ulong;
    t_ptrdiff = t_long;
    t_wchar = t_int;
    // struct __va_list_tag { unsigned gp_offset, fp_offset; void *overflow_arg_area, *reg_save_area; }
    let r = records.len;
    let rt = mk_tagged(TY_STRUCT, r as! u32);
    records.push(Record { name: intern("__va_list_tag"), ty: rt, first: fields.len as! u32, count: 4, size: 24, align: 8,
        flags: RF_COMPLETE, rsv: 0, attr_align: 0, pack: 0, loc: 0, scope: 0 });
    fields.push(Field { name: intern("gp_offset"), ty: t_uint, offset: 0, bitpos: 0, width: -1, attr_align: 0, flags: 0, rsv: 0, rsv2: 0, loc: 0 });
    fields.push(Field { name: intern("fp_offset"), ty: t_uint, offset: 4, bitpos: 32, width: -1, attr_align: 0, flags: 0, rsv: 0, rsv2: 0, loc: 0 });
    fields.push(Field { name: intern("overflow_arg_area"), ty: t_voidptr, offset: 8, bitpos: 64, width: -1, attr_align: 0, flags: 0, rsv: 0, rsv2: 0, loc: 0 });
    fields.push(Field { name: intern("reg_save_area"), ty: t_voidptr, offset: 16, bitpos: 128, width: -1, attr_align: 0, flags: 0, rsv: 0, rsv2: 0, loc: 0 });
    types[rt].size = 24;
    types[rt].align = 8;
    t_valist_rec = rt << 4;
    t_valist = mk_array(t_valist_rec, 1);
}

// ---------------------------------------------------------------------------
// Predicates

fn is_integer_kind(k: i64) -> bool { (k >= TY_BOOL && k <= TY_UINT128) || k == TY_ENUM }
fn is_integer(q: u32) -> bool { is_integer_kind(kind_of(q)) }
fn is_float_kind(k: i64) -> bool { k >= TY_FLOAT16 && k <= TY_FLOAT128 }
fn is_real_float(q: u32) -> bool { is_float_kind(kind_of(q)) }
fn is_complex(q: u32) -> bool { kind_of(q) == TY_COMPLEX }
fn is_arith(q: u32) -> bool { let k = kind_of(q); is_integer_kind(k) || is_float_kind(k) || k == TY_COMPLEX }
fn is_pointer(q: u32) -> bool { kind_of(q) == TY_POINTER }
fn is_scalar(q: u32) -> bool { is_arith(q) || is_pointer(q) }
fn is_void(q: u32) -> bool { kind_of(q) == TY_VOID }
fn is_func(q: u32) -> bool { kind_of(q) == TY_FUNC }
fn is_array(q: u32) -> bool { let k = kind_of(q); k == TY_ARRAY || k == TY_VLA }
fn is_record(q: u32) -> bool { let k = kind_of(q); k == TY_STRUCT || k == TY_UNION }
fn is_vector(q: u32) -> bool { let k = kind_of(q); k == TY_VECTOR || k == TY_EXTVECTOR }
fn is_aggregate(q: u32) -> bool { is_array(q) || is_record(q) }

fn is_signed_kind(k: i64) -> bool {
    return k == TY_CHAR || k == TY_SCHAR || k == TY_SHORT || k == TY_INT || k == TY_LONG || k == TY_LLONG || k == TY_INT128;
}

// Signedness of an integer type (enums: of their underlying type).
recursive fn is_signed(q: u32) -> bool {
    let k = kind_of(q);
    if k == TY_ENUM {
        let u = enums[types[q >> 4].extra].underlying;
        if u == 0 { return false; }
        return is_signed(u);
    }
    return is_signed_kind(k);
}

fn rec_of(q: u32) -> i64 { types[q >> 4].extra as i64 }

recursive fn is_complete(q: u32) -> bool {
    let t = types[q >> 4];
    let k = t.kind as i64;
    if k == TY_VOID || k == TY_FUNC { return false; }
    if k == TY_STRUCT || k == TY_UNION { return records[t.extra].flags & RF_COMPLETE != 0; }
    if k == TY_ENUM { return enums[t.extra].complete; }
    if k == TY_ARRAY { return t.n >= 0 && is_complete(t.base); }
    if k == TY_VLA { return true; }
    return true;
}

recursive fn type_size(q: u32) -> i64 {
    let t = types[q >> 4];
    let k = t.kind as i64;
    if k == TY_STRUCT || k == TY_UNION {
        return records[t.extra].size;
    }
    if k == TY_ENUM {
        let u = enums[t.extra].underlying;
        if u == 0 { return -1; }
        return type_size(u);
    }
    if k == TY_ARRAY {
        if t.n < 0 { return -1; }
        let es = type_size(t.base);
        if es < 0 { return -1; }
        return es * t.n;
    }
    return t.size;
}

recursive fn type_align(q: u32) -> i64 {
    let t = types[q >> 4];
    if t.flags & TF_ALIGNED != 0 { return t.align as i64; }
    let k = t.kind as i64;
    if k == TY_STRUCT || k == TY_UNION { return records[t.extra].align as i64; }
    if k == TY_ENUM {
        let u = enums[t.extra].underlying;
        if u == 0 { return 4; }
        return type_align(u);
    }
    if k == TY_ARRAY || k == TY_VLA { return type_align(t.base); }
    if k == TY_VOID || k == TY_FUNC { return 1; }
    return t.align as i64;
}

// Integer conversion rank.
recursive fn int_rank(q: u32) -> i64 {
    let k = kind_of(q);
    return match k {
        TY_BOOL => 1,
        TY_CHAR, TY_SCHAR, TY_UCHAR => 2,
        TY_SHORT, TY_USHORT => 3,
        TY_INT, TY_UINT => 4,
        TY_LONG, TY_ULONG => 5,
        TY_LLONG, TY_ULLONG => 6,
        TY_INT128, TY_UINT128 => 7,
        TY_ENUM => int_rank(enum_underlying(q)),
        _ => 0,
    };
}

recursive fn enum_underlying(q: u32) -> u32 {
    let u = enums[types[q >> 4].extra].underlying;
    if u == 0 { return t_uint; }
    return u;
}

recursive fn unsigned_of(q: u32) -> u32 {
    let k = kind_of(q);
    return match k {
        TY_CHAR, TY_SCHAR, TY_UCHAR => t_uchar,
        TY_SHORT, TY_USHORT => t_ushort,
        TY_INT, TY_UINT => t_uint,
        TY_LONG, TY_ULONG => t_ulong,
        TY_LLONG, TY_ULLONG => t_ullong,
        TY_INT128, TY_UINT128 => t_uint128,
        TY_ENUM => unsigned_of(enum_underlying(q)),
        _ => q,
    };
}

recursive fn signed_of(q: u32) -> u32 {
    let k = kind_of(q);
    return match k {
        TY_CHAR, TY_SCHAR, TY_UCHAR => t_schar,
        TY_SHORT, TY_USHORT => t_short,
        TY_INT, TY_UINT => t_int,
        TY_LONG, TY_ULONG => t_long,
        TY_LLONG, TY_ULLONG => t_llong,
        TY_INT128, TY_UINT128 => t_int128,
        _ => q,
    };
}

fn float_rank(q: u32) -> i64 {
    return match kind_of(q) {
        TY_FLOAT16 => 1, TY_BF16 => 1, TY_FLOAT => 2, TY_DOUBLE => 3, TY_LDOUBLE => 4, TY_FLOAT128 => 5, _ => 0,
    };
}

// ---------------------------------------------------------------------------
// Compatibility (C11 6.2.7). Ignores alignment overrides.

recursive fn compatible(a: u32, b: u32) -> bool {
    if quals(a) != quals(b) { return false; }
    return compatible_unq(a, b);
}

recursive fn compatible_unq(a0: u32, b0: u32) -> bool {
    let a = tcanon(unqual(a0));
    let b = tcanon(unqual(b0));
    if a == b { return true; }
    let ka = kind_of(a);
    let kb = kind_of(b);
    // an enum is compatible with its underlying type
    if ka == TY_ENUM && kb != TY_ENUM { return compatible_unq(enum_underlying(a), b); }
    if kb == TY_ENUM && ka != TY_ENUM { return compatible_unq(a, enum_underlying(b)); }
    if ka != kb { return false; }
    let ta = types[a >> 4];
    let tb = types[b >> 4];
    if ka == TY_POINTER { return compatible(ta.base, tb.base); }
    if ka == TY_ARRAY || ka == TY_VLA {
        if !compatible(ta.base, tb.base) { return false; }
        if ka == TY_ARRAY && ta.n >= 0 && tb.n >= 0 && ta.n != tb.n { return false; }
        return true;
    }
    if ka == TY_COMPLEX || ka == TY_VECTOR || ka == TY_EXTVECTOR { return ta.base == tb.base && ta.n == tb.n; }
    if ka == TY_FUNC {
        if !compatible(ta.base, tb.base) { return false; }
        let pa = ta.flags & TF_NOPROTO == 0;
        let pb = tb.flags & TF_NOPROTO == 0;
        if pa && pb {
            if ta.n != tb.n { return false; }
            if (ta.flags & TF_VARIADIC) != (tb.flags & TF_VARIADIC) { return false; }
            for i in ta.n {
                if !compatible_unq(tparams[ta.extra + i], tparams[tb.extra + i]) { return false; }
            }
            return true;
        }
        if pa != pb {
            // a prototype vs. no prototype: no variadic, params compatible with their promotions
            let p = if pa { ta } else { tb };
            if p.flags & TF_VARIADIC != 0 { return false; }
            return true;
        }
        return true;
    }
    return false;
}

// The composite type of two compatible types (for redeclarations).
recursive fn composite(a: u32, b: u32) -> u32 {
    let ka = kind_of(a);
    let ta = types[a >> 4];
    let tb = types[b >> 4];
    if ka == TY_ARRAY && kind_of(b) == TY_ARRAY {
        if ta.n < 0 && tb.n >= 0 { return qt(tyi(b), quals(a)); }
        return a;
    }
    if ka == TY_FUNC && kind_of(b) == TY_FUNC {
        if ta.flags & TF_NOPROTO != 0 && tb.flags & TF_NOPROTO == 0 { return b; }
        return a;
    }
    return a;
}

// ---------------------------------------------------------------------------
// Record layout (SysV x86-64, clang's ItaniumRecordLayoutBuilder).

fn layout_record(r: i64) {
    let rec = records[r];
    let is_union = rec.flags & RF_UNION != 0;
    let packed = rec.flags & RF_PACKED != 0;
    let pack_bits = (rec.pack as i64) * 8;    // #pragma pack (MaxFieldAlignment), 0 = none
    var data_bits: i64 = 0;    // data size in bits (a multiple of 8)
    var unfilled: i64 = 0;     // unused bits at the end of the last bit-field byte(s)
    var al_bits: i64 = 8;
    var flags = rec.flags;
    let ms = rec.flags & RF_MSSTRUCT != 0;
    var last_unit: i64 = 0;    // ms_struct: storage unit size of the last bit-field
    for i in rec.first..rec.first + rec.count {
        let f = fields[i];
        let ft = f.ty;
        var tsize = type_size(ft);
        let talign = type_align(ft);
        let fpacked = packed || f.flags & FF_PACKED != 0;
        let explicit_bits = (f.attr_align as i64) * 8;
        if kind_of(ft) == TY_ARRAY && types[ft >> 4].n < 0 {
            tsize = 0;     // flexible array member
            flags = flags | RF_FLEX;
        }
        if quals(ft) & Q_CONST != 0 { flags = flags | RF_CONST_MEMBER; }
        if is_record(ft) && records[rec_of(ft)].flags & RF_CONST_MEMBER != 0 { flags = flags | RF_CONST_MEMBER; }
        if ms && f.width >= 0 && !is_union {
            // ms_struct bit-fields: a unit of the declared type is allocated
            // and shared by following bit-fields of the same size.
            flags = flags | RF_HAS_BITFIELD;
            let w = f.width as i64;
            let unit_bits = tsize * 8;
            var fal = unit_bits;
            if fpacked { fal = 8; }
            if explicit_bits > fal { fal = explicit_bits; }
            if pack_bits > 0 && w > 0 && fal > pack_bits { fal = pack_bits; }
            if last_unit != unit_bits || unfilled < w {
                if last_unit == 0 && w == 0 { fal = 1; }
                unfilled = 0;
                last_unit = 0;
            }
            var off = data_bits - unfilled;
            if w == 0 || w > unfilled {
                off = round_up(off, fal);
                unfilled = 0;
            }
            fields[i].bitpos = off;
            fields[i].offset = (off / unit_bits) * tsize;
            if w > 0 {
                if unfilled == 0 {
                    data_bits = off + unit_bits;
                    unfilled = unit_bits;
                }
                unfilled -= w;
                last_unit = unit_bits;
            } else {
                data_bits = round_up(off, 8);
                unfilled = 0;
                last_unit = 0;
            }
            if fal / 8 * 8 > al_bits { al_bits = fal / 8 * 8; }
            continue;
        }
        if f.width >= 0 {
            flags = flags | RF_HAS_BITFIELD;
            let w = f.width as i64;
            let unit_bits = tsize * 8;
            var fal = talign * 8;
            if fpacked { fal = 8; }
            if explicit_bits > fal { fal = explicit_bits; }
            if fpacked && explicit_bits == 0 { fal = 1; }
            if pack_bits > 0 && w > 0 {
                if fpacked { fal = pack_bits; } else if fal > pack_bits { fal = pack_bits; }
            }
            var off: i64 = 0;
            if !is_union {
                off = data_bits - unfilled;
                let allow_padding = pack_bits == 0;
                if w == 0 || (allow_padding && fal > 1 && (off % fal) + w > unit_bits) {
                    off = round_up(off, fal);
                } else if explicit_bits > 0 && (pack_bits == 0 || explicit_bits <= pack_bits) {
                    off = round_up(off, explicit_bits);
                }
            }
            fields[i].bitpos = off;
            let ual = if fal >= 8 { fal } else { 8 };
            fields[i].offset = (off / ual) * (ual / 8);
            if f.name == 0 { fal = 1; }
            if is_union {
                let rs = round_up(w, 8);
                if rs > data_bits { data_bits = rs; }
            } else {
                let nb = off + w;
                data_bits = round_up(nb, 8);
                unfilled = data_bits - nb;
            }
            if fal / 8 * 8 > al_bits { al_bits = fal / 8 * 8; }
            continue;
        }
        // An ordinary member.
        var fal = talign * 8;
        if fpacked { fal = 8; }
        if explicit_bits > fal { fal = explicit_bits; }
        if pack_bits > 0 && fal > pack_bits { fal = pack_bits; }
        if fal > al_bits { al_bits = fal; }
        let fs = if tsize < 0 { 0 } else { tsize * 8 };
        unfilled = 0;
        last_unit = 0;
        if is_union {
            fields[i].offset = 0;
            fields[i].bitpos = 0;
            if fs > data_bits { data_bits = fs; }
            continue;
        }
        let off = round_up(data_bits, fal);
        fields[i].offset = off / 8;
        fields[i].bitpos = off;
        data_bits = off + fs;
    }
    var al = al_bits / 8;
    if rec.attr_align as i64 > al { al = rec.attr_align as i64; }
    var size = round_up(data_bits, 8) / 8;
    size = round_up(size, al);
    records[r].size = size;
    records[r].align = al as! u32;
    records[r].flags = flags | RF_COMPLETE;
    types[rec.ty].size = size;
    types[rec.ty].align = al as! u32;
}

fn round_up(x: i64, a: i64) -> i64 {
    if a <= 1 { return x; }
    return ((x + a - 1) / a) * a;
}

// ---------------------------------------------------------------------------
// Type names (for diagnostics and the layout oracle).

fn type_name(out: u8[>..]&, q: u32) {
    type_name_decl(out, q, "");
}

// Writes the type q declaring `name` (C declarator syntax). Parameter
// types of function types are written in a simplified form.
var tn_tmp: u8[>..] = [];
var tn_tmp2: u8[>..] = [];
fn type_name_decl(out: u8[>..]&, q: u32, name: const u8[:]) {
    tn_tmp.clear();
    tn_tmp.append(name);
    var t = q;
    var prev_ptr = false;
    loop {
        let k = kind_of(t);
        if k == TY_POINTER {
            tn_tmp2.clear();
            tn_tmp2.push('*');
            quals_text(tn_tmp2, quals(t), true);
            tn_tmp2.append(tn_tmp);
            tn_tmp.clear();
            tn_tmp.append(tn_tmp2);
            prev_ptr = true;
            t = tbase(t);
            continue;
        }
        if k == TY_ARRAY || k == TY_VLA || k == TY_FUNC {
            if prev_ptr {
                tn_tmp2.clear();
                tn_tmp2.push('(');
                tn_tmp2.append(tn_tmp);
                tn_tmp2.push(')');
                tn_tmp.clear();
                tn_tmp.append(tn_tmp2);
            }
            prev_ptr = false;
            if k == TY_FUNC {
                let ft = types[t >> 4];
                tn_tmp.push('(');
                if ft.flags & TF_NOPROTO == 0 {
                    if ft.n == 0 && ft.flags & TF_VARIADIC == 0 { tn_tmp.append("void"); }
                    for i in ft.n {
                        if i > 0 { tn_tmp.append(", "); }
                        simple_type_name(tn_tmp, tparams[ft.extra + i]);
                    }
                    if ft.flags & TF_VARIADIC != 0 { tn_tmp.append(if ft.n > 0 { ", ..." } else { "..." }); }
                }
                tn_tmp.push(')');
                t = ft.base;
            } else {
                let n = types[t >> 4].n;
                if k == TY_ARRAY && n >= 0 { format(tn_tmp, "[", n, "]"); } else if k == TY_VLA { tn_tmp.append("[*]"); } else { tn_tmp.append("[]"); }
                t = tbase(t);
            }
            continue;
        }
        break;
    }
    quals_text(out, quals(t), false);
    base_name(out, t);
    if tn_tmp.len > 0 {
        if tn_tmp[0] != '(' && tn_tmp[0] != '[' { out.push(' '); }
        out.append(tn_tmp);
    }
}

// A parameter type: the base type and its pointers, without nesting.
fn simple_type_name(out: u8[>..]&, q: u32) {
    var t = q;
    var stars = 0;
    var fnptr = false;
    loop {
        let k = kind_of(t);
        if k == TY_POINTER { stars++; t = tbase(t); continue; }
        if k == TY_FUNC { fnptr = true; t = types[t >> 4].base; continue; }
        if k == TY_ARRAY || k == TY_VLA { stars++; t = tbase(t); continue; }
        break;
    }
    quals_text(out, quals(t), false);
    base_name(out, t);
    if fnptr { out.append(" (*)(...)"); return; }
    if stars > 0 { out.push(' '); }
    for i in stars { out.push('*'); }
}

fn quals_text(out: u8[>..]&, q: i64, after: bool) {
    if q & Q_CONST != 0 { out.append(if after { " const" } else { "const " }); }
    if q & Q_VOLATILE != 0 { out.append(if after { " volatile" } else { "volatile " }); }
    if q & Q_RESTRICT != 0 { out.append(if after { " restrict" } else { "restrict " }); }
    if q & Q_ATOMIC != 0 { out.append(if after { " _Atomic" } else { "_Atomic " }); }
    if after && q != 0 { out.push(' '); }
}

recursive fn base_name(out: u8[>..]&, q: u32) {
    let t = types[q >> 4];
    let k = t.kind as i64;
    if k == TY_STRUCT || k == TY_UNION {
        out.append(if k == TY_STRUCT { "struct " } else { "union " });
        let r = records[t.extra];
        if r.name != 0 { out.append(ident_text(r.name as i64)); } else { out.append("(anonymous)"); }
        return;
    }
    if k == TY_ENUM {
        out.append("enum ");
        let e = enums[t.extra];
        if e.name != 0 { out.append(ident_text(e.name as i64)); } else { out.append("(anonymous)"); }
        return;
    }
    if k == TY_COMPLEX {
        out.append("_Complex ");
        base_name(out, t.base);
        return;
    }
    if k == TY_VECTOR || k == TY_EXTVECTOR {
        base_name(out, t.base);
        format(out, " __attribute__((ext_vector_type(", t.n, ")))");
        return;
    }
    out.append(match k {
        TY_VOID => "void", TY_BOOL => "_Bool", TY_CHAR => "char", TY_SCHAR => "signed char",
        TY_UCHAR => "unsigned char", TY_SHORT => "short", TY_USHORT => "unsigned short", TY_INT => "int",
        TY_UINT => "unsigned int", TY_LONG => "long", TY_ULONG => "unsigned long", TY_LLONG => "long long",
        TY_ULLONG => "unsigned long long", TY_INT128 => "__int128", TY_UINT128 => "unsigned __int128",
        TY_FLOAT16 => "_Float16", TY_BF16 => "__bf16", TY_FLOAT => "float", TY_DOUBLE => "double",
        TY_LDOUBLE => "long double", TY_FLOAT128 => "__float128", _ => "<type>",
    });
}
