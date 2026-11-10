// goosecc: declarations, statements and the translation unit.

import std;
import .common;
import .types;
import .ast;
import .sema;
import .expr;
import .builtins;
import .init;
import .dtype;

// ---------------------------------------------------------------------------
// Attributes

let MODE_QI = 1;
let MODE_HI = 2;
let MODE_SI = 3;
let MODE_DI = 4;
let MODE_TI = 5;
let MODE_SF = 6;
let MODE_DF = 7;
let MODE_XF = 8;
let MODE_TF = 9;
let MODE_WORD = 10;
let MODE_POINTER = 11;
let MODE_HF = 12;

let AM_NORETURN = 1;
let AM_WEAK = 2;
let AM_TRANSPARENT = 4;
let AM_PACKED = 8;
let AM_USED = 16;
let AM_UNUSED = 32;
let AM_ALWAYS_INLINE = 64;
let AM_CONST = 128;
let AM_MAY_ALIAS = 256;
let AM_FALLTHROUGH = 512;
let AM_GNU_INLINE = 1024;
let AM_MS_STRUCT = 2048;
let AM_GCC_STRUCT = 4096;

let AM_CTOR = 8192;
let AM_DTOR = 16384;
let AM_NOCOMMON = 32768;
let AM_COMMON = 65536;
let AM_NODEBUG = 131072;       // G1: no debug information for the function

struct Attrs {
    aligned: u32 = 0,
    mode: u8 = 0,
    vector_size: i64 = 0,
    ext_vector: i64 = 0,
    neon_lanes: i64 = 0,    // neon_vector_type(N) / neon_polyvector_type(N) (AArch64)
    cleanup: i32 = -1,
    asm_off: u32 = 0,
    asm_len: u32 = 0,
    misc: u32 = 0,
    sec_off: u32 = 0,       // section("name"): in strbytes
    sec_len: u32 = 0,
    alias_off: u32 = 0,     // alias("name")
    alias_len: u32 = 0,
    vis: u8 = 0,            // visibility("hidden") = 1, ("protected") = 2
    ctor_prio: u16 = 65535,
    dtor_prio: u16 = 65535,
}

// The string argument of an attribute: ("text") -> (offset in strbytes, length).
recursive fn attr_string_arg() -> u32, u32 {
    adv();
    var off: u32 = 0;
    var len: u32 = 0;
    if at(TK_STRING) {
        let s = string_literal();
        let sl = strs[nodes[s].a];
        off = sl.start;
        len = sl.len - 1;
    }
    while !at(TK_R_PAREN) && !at(TK_EOF) { adv(); }
    expect(TK_R_PAREN, "')'");
    return off, len;
}

fn attr_name(id: u32) -> const u8[:] {
    let s = ident_text(id as i64);
    if s.len > 4 && s[0] == '_' && s[1] == '_' && s[s.len - 1] == '_' && s[s.len - 2] == '_' { return s[2..s.len - 2]; }
    return s;
}

fn skip_balanced() {
    // at '(' : skip to the matching ')'
    var depth = 0;
    loop {
        let k = tk();
        if k == TK_EOF { return; }
        if k == TK_L_PAREN { depth++; }
        if k == TK_R_PAREN {
            depth--;
            if depth == 0 { adv(); return; }
        }
        adv();
    }
}

recursive fn attr_int_arg() -> i64 {
    // ( constant-expression )
    adv();
    let e = parse_cond();
    var v: i64 = 0;
    let ok, x = fold_int(rv(e));
    if ok { v = x; } else { err_at(nodes[e].loc, "attribute argument is not an integer constant expression"); }
    while !at(TK_R_PAREN) && !at(TK_EOF) { adv(); }
    expect(TK_R_PAREN, "')'");
    return v;
}

recursive fn parse_attributes(a: Attrs&) {
    loop {
        if at_kw(KW_ATTRIBUTE) {
            adv();
            if !expect(TK_L_PAREN, "'('") { return; }
            if !expect(TK_L_PAREN, "'('") { return; }
            loop {
                if at(TK_R_PAREN) || at(TK_EOF) { break; }
                if accept(TK_COMMA) { continue; }
                if !at(TK_IDENT) && tk() < TK_KW {
                    err("expected attribute name");
                    break;
                }
                let name = attr_name(tval());
                adv();
                if name == "aligned" {
                    if at(TK_L_PAREN) {
                        let v = attr_int_arg();
                        if v > a.aligned as i64 { a.aligned = v as! u32; }
                    } else if a.aligned < 16 {
                        a.aligned = 16;
                    }
                } else if name == "packed" {
                    a.misc = a.misc | AM_PACKED;
                } else if name == "mode" {
                    if at(TK_L_PAREN) {
                        adv();
                        if at(TK_IDENT) {
                            let m = attr_name(tval());
                            a.mode = match_mode(m);
                            adv();
                        }
                        expect(TK_R_PAREN, "')'");
                    }
                } else if name == "vector_size" {
                    if at(TK_L_PAREN) { a.vector_size = attr_int_arg(); }
                } else if name == "ext_vector_type" {
                    if at(TK_L_PAREN) { a.ext_vector = attr_int_arg(); }
                } else if name == "neon_vector_type" || name == "neon_polyvector_type" {
                    if at(TK_L_PAREN) { a.neon_lanes = attr_int_arg(); }
                } else if name == "transparent_union" {
                    a.misc = a.misc | AM_TRANSPARENT;
                } else if name == "noreturn" {
                    a.misc = a.misc | AM_NORETURN;
                } else if name == "weak" {
                    a.misc = a.misc | AM_WEAK;
                } else if name == "used" {
                    a.misc = a.misc | AM_USED;
                } else if name == "unused" {
                    a.misc = a.misc | AM_UNUSED;
                } else if name == "always_inline" {
                    a.misc = a.misc | AM_ALWAYS_INLINE;
                } else if name == "gnu_inline" {
                    a.misc = a.misc | AM_GNU_INLINE;
                } else if name == "ms_struct" {
                    a.misc = a.misc | AM_MS_STRUCT;
                } else if name == "gcc_struct" {
                    a.misc = a.misc | AM_GCC_STRUCT;
                } else if name == "may_alias" {
                    a.misc = a.misc | AM_MAY_ALIAS;
                } else if name == "fallthrough" {
                    a.misc = a.misc | AM_FALLTHROUGH;
                } else if name == "nodebug" {
                    a.misc = a.misc | AM_NODEBUG;
                } else if name == "section" {
                    if at(TK_L_PAREN) {
                        let o, l = attr_string_arg();
                        a.sec_off = o;
                        a.sec_len = l;
                    }
                } else if name == "alias" {
                    if at(TK_L_PAREN) {
                        let o, l = attr_string_arg();
                        a.alias_off = o;
                        a.alias_len = l;
                    }
                } else if name == "visibility" {
                    if at(TK_L_PAREN) {
                        let o, l = attr_string_arg();
                        let v = strbytes[o..o + l];
                        if v == "hidden" || v == "internal" { a.vis = 1; } else if v == "protected" { a.vis = 2; } else { a.vis = 0; }
                    }
                } else if name == "constructor" || name == "destructor" {
                    var prio: i64 = 65535;
                    if at(TK_L_PAREN) { prio = attr_int_arg(); }
                    if name == "constructor" { a.misc = a.misc | AM_CTOR; a.ctor_prio = prio as! u16; }
                    else { a.misc = a.misc | AM_DTOR; a.dtor_prio = prio as! u16; }
                } else if name == "nocommon" {
                    a.misc = a.misc | AM_NOCOMMON;
                } else if name == "common" {
                    a.misc = a.misc | AM_COMMON;
                } else if name == "cleanup" {
                    if at(TK_L_PAREN) {
                        adv();
                        if at(TK_IDENT) {
                            let s = lookup_ord(tval());
                            if s < 0 { err(str("use of undeclared identifier '", ident_text(tval() as i64), "'")); }
                            a.cleanup = s as! i32;
                            adv();
                        }
                        expect(TK_R_PAREN, "')'");
                    }
                } else if at(TK_L_PAREN) {
                    skip_balanced();
                }
            }
            expect(TK_R_PAREN, "')'");
            expect(TK_R_PAREN, "')'");
        } else if at_kw(KW_DECLSPEC) {
            adv();
            if at(TK_L_PAREN) { skip_balanced(); }
        } else {
            return;
        }
    }
}

fn match_mode(m: const u8[:]) -> u8 {
    if m == "QI" || m == "byte" { return MODE_QI; }
    if m == "HI" { return MODE_HI; }
    if m == "SI" { return MODE_SI; }
    if m == "DI" { return MODE_DI; }
    if m == "TI" { return MODE_TI; }
    if m == "SF" { return MODE_SF; }
    if m == "DF" { return MODE_DF; }
    if m == "XF" { return MODE_XF; }
    if m == "TF" { return MODE_TF; }
    if m == "HF" { return MODE_HF; }
    if m == "word" { return MODE_WORD; }
    if m == "pointer" { return MODE_POINTER; }
    return 0;
}

// An asm label: asm("name") after a declarator.
recursive fn parse_asm_label(a: Attrs&) {
    if !at_kw(KW_ASM) { return; }
    adv();
    expect(TK_L_PAREN, "'('");
    if at(TK_STRING) {
        let s = string_literal();
        let sl = strs[nodes[s].a];
        a.asm_off = sl.start;
        a.asm_len = sl.len - 1;
    }
    expect(TK_R_PAREN, "')'");
}

// Applies the type attributes (mode, vector_size, ext_vector_type) to t.
fn apply_type_attrs(t: u32, a: Attrs&, loc: u32) -> u32 {
    var r = t;
    if a.mode != 0 {
        let m = a.mode as i64;
        let k = kind_of(r);
        let q = quals(r);
        if is_integer_kind(k) || k == TY_VOID {
            let sgn = is_signed(r);
            r = match m {
                MODE_QI => if sgn { t_schar } else { t_uchar },
                MODE_HI => if sgn { t_short } else { t_ushort },
                MODE_SI => if sgn { t_int } else { t_uint },
                MODE_DI, MODE_WORD, MODE_POINTER => if sgn { t_long } else { t_ulong },
                MODE_TI => if sgn { t_int128 } else { t_uint128 },
                _ => r,
            };
        } else if is_real_float(r) || k == TY_COMPLEX {
            let c = k == TY_COMPLEX;
            var f = match m { MODE_SF => t_float, MODE_DF => t_double, MODE_XF => t_ldouble, MODE_TF => t_float128, MODE_HF => t_float16, _ => r };
            if c && f != r { f = mk_complex(f); }
            if m == MODE_SF || m == MODE_DF || m == MODE_XF || m == MODE_TF || m == MODE_HF { r = f; }
        } else if is_vector(r) {
            // mode on a vector element: rare
        }
        r = with_quals(r, q);
    }
    if a.neon_lanes > 0 {
        a.vector_size = a.neon_lanes * type_size(unqual(r));
        a.neon_lanes = 0;
    }
    if a.vector_size > 0 {
        let q = quals(r);
        let el = unqual(r);
        let es = type_size(el);
        if es <= 0 || !is_scalar(el) || is_pointer(el) {
            err_at(loc, str("invalid vector element type ", tname(el)));
        } else {
            let n = a.vector_size / es;
            r = with_quals(qt(mk_type(TY_VECTOR, 0, el, n, 0, 0) as i64, 0), q);
        }
    }
    if a.ext_vector > 0 {
        let q = quals(r);
        r = with_quals(qt(mk_type(TY_EXTVECTOR, 0, unqual(r), a.ext_vector, 0, 0) as i64, 0), q);
    }
    // consumed: later applications see only attributes parsed after this
    a.mode = 0;
    a.vector_size = 0;
    a.ext_vector = 0;
    return r;
}

// ---------------------------------------------------------------------------
// Declaration specifiers

struct DeclSpec {
    sc: u8 = 0,
    thread: bool = false,
    is_inline: bool = false,
    noreturn: bool = false,
    q: u8 = 0,
    nvoid: u8 = 0,
    nchar: u8 = 0,
    nshort: u8 = 0,
    nint: u8 = 0,
    nlong: u8 = 0,
    nfloat: u8 = 0,
    ndouble: u8 = 0,
    nsigned: u8 = 0,
    nunsigned: u8 = 0,
    nbool: u8 = 0,
    ncomplex: u8 = 0,
    nint128: u8 = 0,
    nfloat128: u8 = 0,
    nfloat16: u8 = 0,
    nbf16: u8 = 0,
    nnamed: u8 = 0,
    named: u32 = 0,
    dnamed: u32 = 0,       // -g: the written type of `named` (dtype.goose)
    auto_type: bool = false,
    align: u32 = 0,
    tag_sym: i32 = -1,
    tag_defined: bool = false,
    any: bool = false,
    has_sc: bool = false,
    loc: u32 = 0,
}

fn has_type_spec(ds: DeclSpec&) -> bool {
    return ds.nvoid + ds.nchar + ds.nshort + ds.nint + ds.nlong + ds.nfloat + ds.ndouble + ds.nsigned + ds.nunsigned +
        ds.nbool + ds.ncomplex + ds.nint128 + ds.nfloat128 + ds.nfloat16 + ds.nbf16 + ds.nnamed > 0 || ds.auto_type;
}

fn is_typedef_name(id: u32) -> bool {
    let s = lookup_ord(id);
    return s >= 0 && syms[s].kind == SK_TYPEDEF;
}

// Does token i start a type name (for casts, sizeof, compound literals)?
recursive fn starts_type_name(i: i64) -> bool {
    let t = tu_toks[i];
    let k = t.kind as i64;
    if k == TK_IDENT { return is_typedef_name(t.val); }
    if k < TK_KW { return false; }
    let w = k - TK_KW;
    return w == KW_CHAR || w == KW_CONST || w == KW_DOUBLE || w == KW_ENUM || w == KW_FLOAT || w == KW_INT ||
        w == KW_LONG || w == KW_RESTRICT || w == KW_SHORT || w == KW_SIGNED || w == KW_STRUCT || w == KW_UNION ||
        w == KW_UNSIGNED || w == KW_VOID || w == KW_VOLATILE || w == KW_ATOMIC || w == KW_BOOL || w == KW_COMPLEX ||
        w == KW_TYPEOF || w == KW_TYPEOF_UNQUAL || w == KW_INT128 || w == KW_FLOAT128 || w == KW_FLOAT16 ||
        w == KW_BF16 || w == KW_NULLABILITY || w == KW_ATTRIBUTE || w == KW_ALIGNAS || w == KW_UNALIGNED ||
        w == KW_IBM128 || w == KW_IMAGINARY || (w == KW_EXTENSION && starts_type_name(i + 1));
}

// Does the current token start a declaration?
recursive fn starts_declaration() -> bool {
    let t = tu_toks[pc];
    let k = t.kind as i64;
    if k == TK_IDENT { return is_typedef_name(t.val) && tk_n(1) != TK_COLON; }
    if k < TK_KW { return false; }
    let w = k - TK_KW;
    if w == KW_TYPEDEF || w == KW_EXTERN || w == KW_STATIC || w == KW_AUTO || w == KW_REGISTER ||
       w == KW_THREAD_LOCAL || w == KW_INLINE || w == KW_NORETURN || w == KW_STATIC_ASSERT || w == KW_AUTO_TYPE {
        return true;
    }
    if w == KW_EXTENSION {
        var j = pc + 1;
        while tu_toks[j].kind as i64 == TK_KW + KW_EXTENSION { j++; }
        let save = pc;
        pc = j;
        let r = starts_declaration();
        pc = save;
        return r;
    }
    return starts_type_name(pc);
}

recursive fn parse_declspec(ds: DeclSpec&, a: Attrs&, allow_sc: bool) {
    ds.loc = tloc();
    loop {
        let t = tu_toks[pc];
        let k = t.kind as i64;
        if k == TK_IDENT {
            if !has_type_spec(ds) && is_typedef_name(t.val) {
                // a typedef name, unless it is the declarator (T T;)
                let s = lookup_ord(t.val);
                ds.named = syms[s].ty;
                ds.dnamed = d_typedef(s, syms[s].ty);
                ds.nnamed++;
                ds.any = true;
                syms[s].flags = syms[s].flags | SF_USED;
                adv();
                continue;
            }
            break;
        }
        if k < TK_KW { break; }
        let w = k - TK_KW;
        if w == KW_TYPEDEF || w == KW_EXTERN || w == KW_STATIC || w == KW_AUTO || w == KW_REGISTER {
            if !allow_sc { err("storage class specifier not allowed here"); }
            if ds.has_sc && !(ds.thread && (w == KW_EXTERN || w == KW_STATIC)) {
                err("cannot combine with previous storage class specifier");
            }
            ds.sc = match w { KW_TYPEDEF => SC_TYPEDEF, KW_EXTERN => SC_EXTERN, KW_STATIC => SC_STATIC, KW_AUTO => SC_AUTO, _ => SC_REGISTER };
            ds.has_sc = true;
            ds.any = true;
            adv();
            continue;
        }
        if w == KW_THREAD_LOCAL { ds.thread = true; ds.any = true; adv(); continue; }
        if w == KW_INLINE { ds.is_inline = true; ds.any = true; adv(); continue; }
        if w == KW_NORETURN { ds.noreturn = true; ds.any = true; adv(); continue; }
        if w == KW_CONST { ds.q = ds.q | Q_CONST; ds.any = true; adv(); continue; }
        if w == KW_VOLATILE { ds.q = ds.q | Q_VOLATILE; ds.any = true; adv(); continue; }
        if w == KW_RESTRICT { ds.q = ds.q | Q_RESTRICT; ds.any = true; adv(); continue; }
        if w == KW_NULLABILITY || w == KW_UNALIGNED { adv(); continue; }
        if w == KW_ATOMIC {
            ds.any = true;
            adv();
            if at(TK_L_PAREN) {
                adv();
                let ty = parse_type_name();
                let dty = tn_dty;
                expect(TK_R_PAREN, "')'");
                ds.named = with_quals(ty, Q_ATOMIC);
                ds.dnamed = d_quals(dty, Q_ATOMIC);
                ds.nnamed++;
            } else {
                ds.q = ds.q | Q_ATOMIC;
            }
            continue;
        }
        if w == KW_VOID { ds.nvoid++; ds.any = true; adv(); continue; }
        if w == KW_CHAR { ds.nchar++; ds.any = true; adv(); continue; }
        if w == KW_SHORT { ds.nshort++; ds.any = true; adv(); continue; }
        if w == KW_INT { ds.nint++; ds.any = true; adv(); continue; }
        if w == KW_LONG { ds.nlong++; ds.any = true; adv(); continue; }
        if w == KW_FLOAT { ds.nfloat++; ds.any = true; adv(); continue; }
        if w == KW_DOUBLE { ds.ndouble++; ds.any = true; adv(); continue; }
        if w == KW_SIGNED { ds.nsigned++; ds.any = true; adv(); continue; }
        if w == KW_UNSIGNED { ds.nunsigned++; ds.any = true; adv(); continue; }
        if w == KW_BOOL { ds.nbool++; ds.any = true; adv(); continue; }
        if w == KW_COMPLEX || w == KW_IMAGINARY { ds.ncomplex++; ds.any = true; adv(); continue; }
        if w == KW_INT128 { ds.nint128++; ds.any = true; adv(); continue; }
        if w == KW_FLOAT128 || w == KW_IBM128 { ds.nfloat128++; ds.any = true; adv(); continue; }
        if w == KW_FLOAT16 { ds.nfloat16++; ds.any = true; adv(); continue; }
        if w == KW_BF16 { ds.nbf16++; ds.any = true; adv(); continue; }
        if w == KW_AUTO_TYPE { ds.auto_type = true; ds.any = true; adv(); continue; }
        if w == KW_STRUCT || w == KW_UNION {
            ds.any = true;
            ds.named = parse_record_spec(ds, w == KW_UNION);
            ds.dnamed = ds.named;
            ds.nnamed++;
            continue;
        }
        if w == KW_ENUM {
            ds.any = true;
            ds.named = parse_enum_spec(ds);
            ds.dnamed = ds.named;
            ds.nnamed++;
            continue;
        }
        if w == KW_TYPEOF || w == KW_TYPEOF_UNQUAL {
            ds.any = true;
            adv();
            expect(TK_L_PAREN, "'('");
            var ty: u32 = t_int;
            var dty: u32 = 0;
            if starts_type_name(pc) {
                ty = parse_type_name();
                dty = tn_dty;
            } else {
                let e = parse_expr();
                ty = nty(e);
                dty = expr_written(e);
            }
            expect(TK_R_PAREN, "')'");
            if w == KW_TYPEOF_UNQUAL { ty = unqual(ty); dty = d_unqual(dty); }
            ds.named = ty;
            ds.dnamed = dty;
            ds.nnamed++;
            continue;
        }
        if w == KW_ALIGNAS {
            ds.any = true;
            adv();
            expect(TK_L_PAREN, "'('");
            var al: i64 = 0;
            if starts_type_name(pc) {
                al = type_align(parse_type_name());
            } else {
                let e = parse_cond();
                let ok, v = fold_int(rv(e));
                if !ok { err_at(nodes[e].loc, "'_Alignas' requires an integer constant expression"); }
                al = v;
            }
            expect(TK_R_PAREN, "')'");
            if al > ds.align as i64 { ds.align = al as! u32; }
            continue;
        }
        if w == KW_ATTRIBUTE || w == KW_DECLSPEC {
            parse_attributes(a);
            continue;
        }
        if w == KW_EXTENSION { adv(); continue; }
        break;
    }
}

// The type the specifiers denote. implicit: allow a missing type (int).
fn finish_declspec(ds: DeclSpec&, implicit: bool) -> u32 {
    var t: u32 = 0;
    let loc = ds.loc;
    if ds.nnamed > 0 {
        if ds.nnamed > 1 || ds.nvoid + ds.nchar + ds.nshort + ds.nint + ds.nlong + ds.nfloat + ds.ndouble + ds.nbool + ds.nint128 > 0 {
            err_at(loc, "cannot combine with previous type specifier");
        }
        t = ds.named;
        if ds.nsigned + ds.nunsigned > 0 {
            // GNU: 'unsigned T' is an error; keep T
            err_at(loc, "'signed'/'unsigned' cannot be combined with a type name");
        }
    } else if ds.nvoid > 0 {
        t = t_void;
    } else if ds.nbool > 0 {
        t = t_bool;
    } else if ds.nchar > 0 {
        t = if ds.nunsigned > 0 { t_uchar } else if ds.nsigned > 0 { t_schar } else { t_char };
    } else if ds.nint128 > 0 {
        t = if ds.nunsigned > 0 { t_uint128 } else { t_int128 };
    } else if ds.nfloat > 0 {
        t = t_float;
    } else if ds.ndouble > 0 {
        t = if ds.nlong > 0 { t_ldouble } else { t_double };
    } else if ds.nfloat128 > 0 {
        t = t_float128;
    } else if ds.nfloat16 > 0 {
        t = t_float16;
    } else if ds.nbf16 > 0 {
        t = t_bf16;
    } else if ds.nshort > 0 {
        t = if ds.nunsigned > 0 { t_ushort } else { t_short };
    } else if ds.nlong >= 2 {
        t = if ds.nunsigned > 0 { t_ullong } else { t_llong };
    } else if ds.nlong == 1 {
        t = if ds.nunsigned > 0 { t_ulong } else { t_long };
    } else if ds.nint > 0 || ds.nsigned > 0 || ds.nunsigned > 0 {
        t = if ds.nunsigned > 0 { t_uint } else { t_int };
    } else if ds.ncomplex > 0 {
        t = t_double;
    } else if ds.auto_type {
        t = 0;
    } else {
        if !implicit { err_at(loc, "type specifier missing"); }
        else { implicit_int(loc, "type specifier missing, defaults to 'int'"); }
        t = t_int;
    }
    if ds.ncomplex > 0 && t != 0 {
        if is_integer(t) || is_real_float(t) { t = mk_complex(t); }
    }
    if t == 0 { return 0; }
    return with_quals(t, ds.q as i64);
}

// The written type of the specifiers, given finish_declspec's result t
// (-g; dtype.goose).
fn declspec_dty(ds: DeclSpec&, t: u32) -> u32 {
    if !dbg_types || t == 0 || ds.nnamed == 0 || ds.ncomplex > 0 || ds.dnamed == 0 { return t; }
    if !dq_sugar(ds.dnamed) || dq_canon(ds.dnamed) != ds.named { return t; }
    return d_quals(ds.dnamed, ds.q as i64);
}

// ---------------------------------------------------------------------------
// struct / union / enum

var fscratch: Field[>..<] = [];
var fdscratch: u32[>..<] = [];       // -g: the members' written types, next to fscratch

fn pack_at(i: i64) -> u32 {
    // the last change at or before token i
    var lo = 0;
    var hi = pack_changes.len / 2;
    while lo < hi {
        let mid = (lo + hi) / 2;
        if pack_changes[2 * mid] as i64 <= i { lo = mid + 1; } else { hi = mid; }
    }
    if lo == 0 { return 0; }
    return pack_changes[2 * (lo - 1) + 1];
}

fn ms_at(i: i64) -> bool {
    var r = false;
    var j = 0;
    while j + 1 < ms_changes.len && ms_changes[j] as i64 <= i {
        r = ms_changes[j + 1] != 0;
        j += 2;
    }
    return r;
}

fn new_record(name: u32, is_union: bool, loc: u32) -> i64 {
    let r = records.len;
    let ty = mk_tagged(if is_union { TY_UNION } else { TY_STRUCT }, r as! u32);
    records.push(Record { name: name, ty: ty, first: 0, count: 0, size: -1, align: 1, flags: if is_union { RF_UNION } else { 0 },
        rsv: 0, attr_align: 0, pack: 0, loc: loc, scope: scope_depth as! u32 });
    return r;
}

fn tag_kind_ok(s: i64, kind: i64) -> bool {
    return kind_of(qt(syms[s].v, 0)) == kind;
}

recursive fn parse_record_spec(ds: DeclSpec&, is_union: bool) -> u32 {
    let loc = tloc();
    let start_tok = pc;
    adv();
    var ra = Attrs { .. };
    parse_attributes(ra);
    var name: u32 = 0;
    if at(TK_IDENT) {
        name = tval();
        adv();
    } else if tk() >= TK_KW && tk_n(1) == TK_L_BRACE {
        // a keyword used as a tag name is an error in C
    }
    parse_attributes(ra);
    let kind = if is_union { TY_UNION } else { TY_STRUCT };
    if at(TK_L_BRACE) {
        var r: i64 = -1;
        var s: i64 = -1;
        if name != 0 {
            s = lookup_tag(name);
            if s >= 0 && syms[s].scope as i64 == scope_depth && tag_kind_ok(s, kind) {
                let rr = rec_of(qt(syms[s].v, 0));
                if records[rr].flags & (RF_COMPLETE | RF_BEING_DEFINED) != 0 {
                    err_at(loc, str("redefinition of '", ident_text(name as i64), "'"));
                    s = -1;
                } else {
                    r = rr;
                }
            } else if s >= 0 && syms[s].scope as i64 == scope_depth {
                err_at(loc, str("use of '", ident_text(name as i64), "' with tag type that does not match previous declaration"));
                s = -1;
            } else {
                s = -1;
            }
        }
        if r < 0 {
            r = new_record(name, is_union, loc);
            if name == 0 { dt_note_record_in(r); }
            s = new_sym(SK_TAG, name, records[r].ty << 4, loc);
            syms[s].v = records[r].ty as i64;
            if name != 0 { bind_sym(s, true); }
        }
        records[r].flags = records[r].flags | RF_BEING_DEFINED;
        dt_note_record(r, cur_func);
        records[r].pack = pack_at(start_tok);
        records[r].scope = scope_depth as! u32;
        records[r].loc = loc;
        parse_record_body(r);
        parse_attributes(ra);
        if ra.misc & AM_PACKED != 0 { records[r].flags = records[r].flags | RF_PACKED; }
        if ra.misc & AM_TRANSPARENT != 0 { records[r].flags = records[r].flags | RF_TRANSPARENT; }
        if (ms_at(start_tok) || ra.misc & AM_MS_STRUCT != 0) && ra.misc & AM_GCC_STRUCT == 0 { records[r].flags = records[r].flags | RF_MSSTRUCT; }
        if ra.aligned != 0 { records[r].attr_align = ra.aligned; }
        records[r].flags = records[r].flags & ~RF_BEING_DEFINED;
        layout_record(r);
        ds.tag_sym = s as! i32;
        ds.tag_defined = true;
        return records[r].ty << 4;
    }
    if name == 0 {
        err_at(loc, "declaration of anonymous struct must be a definition");
        let r = new_record(0, is_union, loc);
        return records[r].ty << 4;
    }
    // A reference, or a forward declaration ("struct S;").
    let fwd = at(TK_SEMI) && !ds.any && !has_type_spec(ds);
    var s = lookup_tag(name);
    if s >= 0 && fwd && syms[s].scope as i64 != scope_depth { s = -1; }
    if s >= 0 {
        if !tag_kind_ok(s, kind) {
            err_at(loc, str("use of '", ident_text(name as i64), "' with tag type that does not match previous declaration"));
        } else {
            ds.tag_sym = s as! i32;
            return qt(syms[s].v, 0);
        }
    }
    let r = new_record(name, is_union, loc);
    dt_note_record(r, cur_func);
    let s2 = new_sym(SK_TAG, name, records[r].ty << 4, loc);
    syms[s2].v = records[r].ty as i64;
    bind_sym(s2, true);
    ds.tag_sym = s2 as! i32;
    return records[r].ty << 4;
}

recursive fn parse_record_body(r: i64) {
    expect(TK_L_BRACE, "'{'");
    let mark = fscratch.len;
    let outer_rec = cur_rec;
    cur_rec = r;
    while !at(TK_R_BRACE) && !at(TK_EOF) {
        if at(TK_SEMI) { adv(); continue; }
        if at_kw(KW_STATIC_ASSERT) { parse_static_assert(); continue; }
        var ds = DeclSpec { .. };
        var fa = Attrs { .. };
        parse_declspec(ds, fa, false);
        if !ds.any {
            tok_buf.clear();
            tok_buf.append("expected member declaration, got ");
            tok_desc(tok_buf, pc);
            err(tok_buf);
            // skip to ; or }
            while !at(TK_SEMI) && !at(TK_R_BRACE) && !at(TK_EOF) { adv(); }
            accept(TK_SEMI);
            continue;
        }
        let base = finish_declspec(ds, true);
        let bt = apply_type_attrs(base, fa, ds.loc);
        let dbt = d_after(declspec_dty(ds, base), base, bt);
        if at(TK_SEMI) {
            // an anonymous struct/union member (C11), or nothing
            if is_record(bt) && records[rec_of(bt)].name == 0 {
                fscratch.push(Field { name: 0, ty: bt, offset: 0, bitpos: 0, width: -1, attr_align: fa.aligned,
                    flags: (FF_ANON | (if fa.misc & AM_PACKED != 0 { FF_PACKED } else { 0 })) as! u8, rsv: 0, rsv2: 0, loc: ds.loc });
                if dbg_types { fdscratch.push(bt); }
            } else if is_record(bt) && ds.tag_defined == false {
                warn(ds.loc, "declaration does not declare anything");
            } else if is_record(bt) {
                // a tagged struct defined inside: also an anonymous member with -fms-extensions; here nothing
            } else {
                warn(ds.loc, "declaration does not declare anything");
            }
            adv();
            continue;
        }
        loop {
            var da = fa;
            var name: u32 = 0;
            var ty = bt;
            var dty = dbt;
            var floc = tloc();
            var width: i64 = -1;
            if !at(TK_COLON) {
                let d = parse_declarator(bt, dbt, 0, da);
                name = d.name;
                ty = d.ty;
                dty = d.dty;
                floc = d.loc;
            }
            parse_attributes(da);
            if accept(TK_COLON) {
                let e = parse_cond();
                let ok, v = fold_int(rv(e));
                if !ok { err_at(nodes[e].loc, "bit-field width is not an integer constant expression"); }
                width = v;
                if !is_integer(ty) {
                    err_at(floc, str("bit-field has non-integral type ", tname(ty)));
                    width = -1;
                } else if v < 0 {
                    err_at(floc, "bit-field has negative width");
                    width = -1;
                } else if v > type_size(ty) * 8 {
                    err_at(floc, str("width of bit-field (", v, " bits) exceeds the width of its type (", type_size(ty) * 8, " bits)"));
                    width = type_size(ty) * 8;
                } else if v == 0 && name != 0 {
                    err_at(floc, "named bit-field has zero width");
                }
            }
            parse_attributes(da);
            let ty0 = ty;
            ty = apply_type_attrs(ty, da, floc);
            dty = d_after(dty, ty0, ty);
            if is_func(ty) {
                err_at(floc, "field declared as a function");
            } else if kind_of(ty) == TY_VLA {
                err_at(floc, "fields must have a constant size: 'variable length array in structure' extension will never be supported");
                ty = t_int;
            } else if !is_complete(ty) && !(kind_of(ty) == TY_ARRAY && types[ty >> 4].n < 0) {
                err_at(floc, str("field has incomplete type ", tname(ty)));
                ty = t_int;
            }
            var fal = da.aligned;
            if ds.align > fal { fal = ds.align; }
            fscratch.push(Field { name: name, ty: ty, offset: 0, bitpos: 0, width: width as! i32, attr_align: fal,
                flags: (if da.misc & AM_PACKED != 0 { FF_PACKED } else { 0 }) as! u8, rsv: 0, rsv2: 0, loc: floc });
            if dbg_types { fdscratch.push(if dq_canon(dty) == ty { dty } else { ty }); }
            if !accept(TK_COMMA) { break; }
        }
        expect(TK_SEMI, "';' after member declaration");
    }
    expect(TK_R_BRACE, "'}'");
    // checks: flexible array members, duplicates
    let n = fscratch.len - mark;
    for i in mark..fscratch.len {
        let f = fscratch[i];
        if kind_of(f.ty) == TY_ARRAY && types[f.ty >> 4].n < 0 {
            if i != fscratch.len - 1 {
                err_at(f.loc, str("flexible array member '", ident_text(f.name as i64), "' with type ", tname(f.ty), " is not at the end of struct"));
            } else if records[r].flags & RF_UNION != 0 {
                // allowed as an extension
            }
        }
        if f.name != 0 {
            for j in mark..i {
                if fscratch[j].name == f.name {
                    err_at(f.loc, str("duplicate member '", ident_text(f.name as i64), "'"));
                    break;
                }
            }
        }
    }
    cur_rec = outer_rec;
    records[r].first = fields.len as! u32;
    records[r].count = n as! u32;
    if dbg_types {
        for i in mark..fscratch.len { dt_set_field(fields.len + i - mark, fdscratch[i]); }
        fdscratch.resize(mark);
    }
    for i in mark..fscratch.len { fields.push(fscratch[i]); }
    fscratch.resize(mark);
}

recursive fn parse_enum_spec(ds: DeclSpec&) -> u32 {
    let loc = tloc();
    adv();
    var ea = Attrs { .. };
    parse_attributes(ea);
    var name: u32 = 0;
    if at(TK_IDENT) { name = tval(); adv(); }
    parse_attributes(ea);
    var fixed: u32 = 0;
    if at(TK_COLON) && (at(TK_COLON) && starts_type_name(pc + 1)) {
        adv();
        fixed = unqual(parse_type_name());
    }
    if at(TK_L_BRACE) {
        var e: i64 = -1;
        var s: i64 = -1;
        if name != 0 {
            s = lookup_tag(name);
            if s >= 0 && syms[s].scope as i64 == scope_depth && tag_kind_ok(s, TY_ENUM) && !enums[types[syms[s].v].extra].complete {
                e = types[syms[s].v].extra as i64;
            } else if s >= 0 && syms[s].scope as i64 == scope_depth {
                err_at(loc, str("redefinition of '", ident_text(name as i64), "'"));
            }
        }
        if e < 0 {
            e = enums.len;
            let ty = mk_tagged(TY_ENUM, e as! u32);
            enums.push(EnumRec { name: name, ty: ty, underlying: 0, complete: false, packed: false, rsv: 0, loc: loc, scope: scope_depth as! u32 });
            dt_note_enum(e, cur_func);
            if name == 0 { dt_note_enum_in(e); }
            s = new_sym(SK_TAG, name, ty << 4, loc);
            syms[s].v = ty as i64;
            if name != 0 { bind_sym(s, true); }
        }
        let ety = enums[e].ty << 4;
        dt_note_enum_def(e, loc);
        adv();
        var next: i64 = 0;
        var minv: i64 = 0;
        var maxv: i64 = 0;
        var any_neg = false;
        var maxu: u64 = 0;
        let mark = nscratch.len;
        while !at(TK_R_BRACE) && !at(TK_EOF) {
            if !at(TK_IDENT) {
                err("expected identifier");
                while !at(TK_R_BRACE) && !at(TK_EOF) { adv(); }
                break;
            }
            let cname = tval();
            let cloc = tloc();
            adv();
            var ca = Attrs { .. };
            parse_attributes(ca);
            var v = next;
            var cty = t_int;
            if accept(TK_EQUAL) {
                let x = parse_cond();
                let rx = rv(x);
                let ok, val = fold_int(rx);
                if !ok { err_at(nodes[x].loc, "expression is not an integer constant expression"); }
                v = val;
                if !is_signed(nty(rx)) && val < 0 {
                    // a large unsigned value
                    cty = nty(rx);
                }
            }
            if v < -2147483648 || v > 2147483647 {
                cty = if v < 0 { t_long } else if v > 4294967295 { t_long } else { t_uint };
            }
            let es = new_sym(SK_ENUMC, cname, cty, cloc);
            syms[es].v = v;
            let prev = lookup_ord(cname);
            if prev >= 0 && syms[prev].scope as i64 == scope_depth {
                err_at(cloc, str("redefinition of '", ident_text(cname as i64), "'"));
            }
            bind_sym(es, false);
            nscratch.push(es as! u32);
            if v < 0 { any_neg = true; if v < minv { minv = v; } }
            if v > maxv { maxv = v; }
            if cty == t_ulong || cty == t_ullong {
                if (v as! u64) > maxu { maxu = v as! u64; }
            }
            next = v + 1;
            if !accept(TK_COMMA) { break; }
        }
        expect(TK_R_BRACE, "'}'");
        parse_attributes(ea);
        let packed = ea.misc & AM_PACKED != 0;
        // The underlying type (clang's rules for C).
        var ut = t_uint;
        if fixed != 0 {
            ut = fixed;
        } else if any_neg {
            if packed && minv >= -128 && maxv <= 127 { ut = t_schar; }
            else if packed && minv >= -32768 && maxv <= 32767 { ut = t_short; }
            else if minv >= -2147483648 && maxv <= 2147483647 { ut = t_int; }
            else { ut = t_long; }
        } else {
            if maxu > 0 { ut = t_ulong; }
            else if packed && maxv <= 255 { ut = t_uchar; }
            else if packed && maxv <= 65535 { ut = t_ushort; }
            else if maxv <= 4294967295 { ut = t_uint; }
            else { ut = t_ulong; }
        }
        enums[e].underlying = ut;
        enums[e].complete = true;
        enums[e].packed = packed;
        // enumerators that do not fit int get the enum's type
        for j in mark..nscratch.len {
            let es = nscratch[j] as i64;
            if syms[es].ty != t_int { syms[es].ty = ety; }
        }
        dt_note_enumerators(e, nscratch[mark..]);
        nscratch.resize(mark);
        ds.tag_sym = s as! i32;
        ds.tag_defined = true;
        return ety;
    }
    if name == 0 {
        err_at(loc, "declaration of anonymous enum must be a definition");
        return t_int;
    }
    let s = lookup_tag(name);
    if s >= 0 {
        if !tag_kind_ok(s, TY_ENUM) {
            err_at(loc, str("use of '", ident_text(name as i64), "' with tag type that does not match previous declaration"));
            return t_int;
        }
        ds.tag_sym = s as! i32;
        return qt(syms[s].v, 0);
    }
    // forward reference to an enum (GNU)
    let e = enums.len;
    let ty = mk_tagged(TY_ENUM, e as! u32);
    enums.push(EnumRec { name: name, ty: ty, underlying: if fixed != 0 { fixed } else { 0 }, complete: fixed != 0, packed: false, rsv: 0, loc: loc, scope: scope_depth as! u32 });
    dt_note_enum(e, cur_func);
    let s2 = new_sym(SK_TAG, name, ty << 4, loc);
    syms[s2].v = ty as i64;
    bind_sym(s2, true);
    ds.tag_sym = s2 as! i32;
    return ty << 4;
}

// ---------------------------------------------------------------------------
// Declarators

struct Declr {
    name: u32 = 0,
    loc: u32 = 0,
    ty: u32 = 0,
    dty: u32 = 0,         // -g: the written type (dtype.goose)
    params: i64 = -1,     // the parameter symbols of the name's own function declarator (in nlist)
    nparams: i64 = 0,
    kr: bool = false,
}

// Is the '(' at pc a nested declarator (vs. a parameter list)?
fn nested_paren(abstract: i64) -> bool {
    if abstract == 0 { return true; }
    var j = pc + 1;
    // skip attributes: what follows decides
    while tu_toks[j].kind as i64 == TK_KW + KW_ATTRIBUTE {
        j++;
        var depth = 0;
        loop {
            let kk = tu_toks[j].kind as i64;
            if kk == TK_EOF { return false; }
            if kk == TK_L_PAREN { depth++; }
            if kk == TK_R_PAREN {
                depth--;
                if depth == 0 { j++; break; }
            }
            j++;
        }
    }
    let k = tu_toks[j].kind as i64;
    if k == TK_STAR || k == TK_L_PAREN || k == TK_L_SQUARE || k == TK_CARET { return true; }
    if k == TK_KW + KW_NULLABILITY { return true; }
    if j > pc + 1 && (k == TK_R_PAREN) { return true; }
    if k == TK_IDENT {
        if is_typedef_name(tu_toks[j].val) { return false; }
        return abstract == 2;
    }
    if j > pc + 1 { return false; }
    if k == TK_IDENT {
        if is_typedef_name(tu_toks[pc + 1].val) { return false; }
        return abstract == 2;
    }
    return false;
}

fn ptr_quals() -> i64 {
    var q = 0;
    loop {
        if at_kw(KW_CONST) { q = q | Q_CONST; adv(); continue; }
        if at_kw(KW_VOLATILE) { q = q | Q_VOLATILE; adv(); continue; }
        if at_kw(KW_RESTRICT) { q = q | Q_RESTRICT; adv(); continue; }
        if at_kw(KW_ATOMIC) && tk_n(1) != TK_L_PAREN { q = q | Q_ATOMIC; adv(); continue; }
        if at_kw(KW_NULLABILITY) || at_kw(KW_UNALIGNED) { adv(); continue; }
        break;
    }
    return q;
}

// abstract: 0 = a name is required, 1 = no name (type names), 2 = either (parameters)
recursive fn parse_declarator(base: u32, dbase: u32, abstract: i64, a: Attrs&) -> Declr {
    var t = base;
    var dt = dbase;
    while at(TK_STAR) || at(TK_CARET) {
        adv();
        var q = ptr_quals();
        while at_kw(KW_ATTRIBUTE) {
            parse_attributes(a);
            q = q | ptr_quals();
        }
        t = with_quals(mk_ptr(t), q);
        if dbg_types { dt = d_ptr(dt, t); }
    }
    if !dbg_types { dt = t; }
    if at(TK_L_PAREN) && nested_paren(abstract) {
        let open = pc;
        // find the matching ')'
        var depth = 0;
        var j = pc;
        loop {
            let k = tu_toks[j].kind as i64;
            if k == TK_EOF { break; }
            if k == TK_L_PAREN { depth++; }
            if k == TK_R_PAREN {
                depth--;
                if depth == 0 { break; }
            }
            j++;
        }
        pc = j;
        adv();
        var dummy = Declr { .. };
        let outer = parse_suffixes(t, dt, dummy, true);
        let douter = sfx_dty;
        let after = pc;
        pc = open + 1;
        parse_attributes(a);
        var d = parse_declarator(outer, douter, abstract, a);
        parse_attributes(a);
        // int (f)(params): the parenthesized name is the function itself
        if d.params < 0 && d.ty == outer && dummy.params >= 0 {
            d.params = dummy.params;
            d.nparams = dummy.nparams;
            d.kr = dummy.kr;
        }
        if !at(TK_R_PAREN) {
            expect(TK_R_PAREN, "')'");
        }
        pc = after;
        return d;
    }
    var d = Declr { .. };
    d.loc = tloc();
    if at(TK_IDENT) && abstract != 1 {
        d.name = tval();
        adv();
    } else if abstract == 0 {
        tok_buf.clear();
        tok_buf.append("expected identifier or '(', got ");
        tok_desc(tok_buf, pc);
        err(tok_buf);
    }
    parse_attributes(a);
    d.ty = parse_suffixes(t, dt, d, true);
    d.dty = sfx_dty;
    return d;
}

// Array and function suffixes, applied right to left. `first` marks the
// suffix right after the name, whose parameters belong to the name.
// With -g the written type of the result is left in sfx_dty.
var sfx_dty: u32 = 0;
recursive fn parse_suffixes(base: u32, dbase: u32, d: Declr&, first: bool) -> u32 {
    if at(TK_L_SQUARE) {
        let loc = tloc();
        adv();
        var q = 0;
        var is_static = false;
        loop {
            if at_kw(KW_STATIC) { is_static = true; adv(); continue; }
            let pq = ptr_quals();
            if pq != 0 { q = q | pq; continue; }
            break;
        }
        var n: i64 = -1;
        var vla_node: u32 = 0;
        var vla = false;
        if at(TK_STAR) && tk_n(1) == TK_R_SQUARE {
            adv();
            vla = true;
        } else if !at(TK_R_SQUARE) {
            let e = parse_assign();
            let r = rv(e);
            if !is_integer(nty(r)) {
                err_at(loc, str("size of array has non-integer type ", tname(nty(r))));
            } else {
                var ok, v = fold_int(r);
                if !ok && opt_gnu {
                    // G1: what clang's evaluator folds (GNU extension)
                    ok, v = fold_gnu(r);
                }
                if ok {
                    if v < 0 && is_signed(nty(r)) {
                        err_at(loc, "array has a negative size");
                        n = 0;
                    } else {
                        n = v;
                    }
                } else {
                    vla = true;
                    vla_node = r;
                }
            }
        }
        expect(TK_R_SQUARE, "']'");
        let inner = parse_suffixes(base, dbase, d, false);
        let dinner = sfx_dty;
        if is_func(inner) {
            err_at(loc, "array of functions is not allowed");
            return inner;
        }
        if !is_complete(inner) && !is_void(inner) {
            if kind_of(inner) == TY_ARRAY || is_record(inner) || kind_of(inner) == TY_ENUM {
                err_at(loc, str("array has incomplete element type ", tname(inner)));
            }
        }
        var at2: u32 = 0;
        let es = type_size(inner);
        let ea = type_align(inner);
        if es > 0 && ea > 0 && es % ea != 0 {
            err_at(loc, str("size of array element of type ", tname(inner), " (", es, " bytes) isn't a multiple of its alignment (", ea, " bytes)"));
        }
        if !vla && n > 0 && es > 0 && n > 2305843009213693951 / es {
            err_at(loc, str("array is too large (", n, " elements)"));
            n = 1;
        }
        if vla {
            at2 = mk_vla(inner, vla_node as i64);
        } else {
            at2 = mk_array(inner, n);
        }
        if first && q != 0 { d.kr = d.kr; }
        array_quals = q;
        sfx_dty = at2;
        if dbg_types { sfx_dty = if vla { d_vla(dinner, at2) } else { d_array(dinner, n, at2) }; }
        return at2;
    }
    if at(TK_L_PAREN) {
        let loc = tloc();
        var variadic = false;
        var noproto = false;
        var kr = false;
        let start, count = parse_params(variadic, noproto, kr);
        if first {
            d.params = start;
            d.nparams = count;
            d.kr = kr;
        }
        let ret = parse_suffixes(base, dbase, d, false);
        let dret = sfx_dty;
        if is_array(ret) || is_func(ret) {
            err_at(loc, str("function cannot return ", if is_func(ret) { "function" } else { "array" }, " type ", tname(ret)));
        }
        fn_scratch.clear();
        if !noproto {
            for i in count { fn_scratch.push(unqual(syms[nlist[start + i]].ty)); }
        }
        var fl = 0;
        if variadic { fl = fl | TF_VARIADIC; }
        if noproto { fl = fl | TF_NOPROTO; }
        let ft = qt(mk_type(TY_FUNC, fl, unqual(ret), 0, 0, 0) as i64, 0);
        sfx_dty = ft;
        if dbg_types {
            let mark = dscratch.len;
            if !noproto {
                for i in count {
                    let p = nlist[start + i] as i64;
                    let w = sym_written(p);
                    dscratch.push(if w != 0 { w } else { syms[p].ty });
                }
            }
            sfx_dty = d_func(d_unqual(dret), mark, fl, ft);
        }
        return ft;
    }
    sfx_dty = dbase;
    return base;
}
var array_quals: i64 = 0;

// ( parameter-type-list ) or ( identifier-list ). Returns the parameter
// symbols (in nlist).
recursive fn parse_params(variadic: bool&, noproto: bool&, kr: bool&) -> i64, i64 {
    adv();
    push_scope();
    let mark = nscratch.len;
    if at(TK_R_PAREN) {
        noproto = true;
    } else if at_kw(KW_VOID) && tk_n(1) == TK_R_PAREN {
        adv();
    } else if at(TK_IDENT) && !is_typedef_name(tval()) {
        // K&R identifier list
        noproto = true;
        kr = true;
        loop {
            if !at(TK_IDENT) { err("expected identifier"); break; }
            let s = new_sym(SK_VAR, tval(), t_int, tloc());
            syms[s].flags = SF_PARAM;
            bind_sym(s, false);
            nscratch.push(s as! u32);
            adv();
            if !accept(TK_COMMA) { break; }
        }
    } else {
        loop {
            if at(TK_ELLIPSIS) {
                adv();
                variadic = true;
                break;
            }
            var ds = DeclSpec { .. };
            var pa = Attrs { .. };
            parse_declspec(ds, pa, true);
            if !ds.any {
                tok_buf.clear();
                tok_buf.append("expected parameter declarator, got ");
                tok_desc(tok_buf, pc);
                err(tok_buf);
                while !at(TK_R_PAREN) && !at(TK_EOF) { adv(); }
                break;
            }
            let base = finish_declspec(ds, true);
            array_quals = 0;
            let base2 = apply_type_attrs(base, pa, ds.loc);
            let d = parse_declarator(base2, d_after(declspec_dty(ds, base), base, base2), 2, pa);
            parse_attributes(pa);
            var ty = apply_type_attrs(d.ty, pa, d.loc);
            var dty = d_after(d.dty, d.ty, ty);
            let ty_before = ty;
            // adjustments (C11 6.7.6.3p7-8); a VLA parameter's size is still
            // evaluated on entry (kept in the symbol's v for B2)
            var orig: u32 = 0;
            if is_array(ty) {
                if kind_of(ty) == TY_VLA { orig = ty; }
                ty = with_quals(mk_ptr(tbase(ty)), array_quals);
            } else if is_func(ty) {
                ty = mk_ptr(ty);
            }
            if is_void(ty) && d.name == 0 && quals(ty) == 0 {
                if nscratch.len == mark && at(TK_R_PAREN) { break; }
                err_at(d.loc, "'void' must be the first and only parameter if specified");
            }
            let s = new_sym(SK_VAR, d.name, ty, d.loc);
            if dbg_types { dt_set_sym(s, d_adjust_param(dty, ty_before, ty)); }
            syms[s].flags = SF_PARAM;
            syms[s].v = orig as i64;
            syms[s].sc = if ds.sc == SC_REGISTER { SC_REGISTER } else { SC_NONE };
            if d.name != 0 { bind_sym(s, false); }
            nscratch.push(s as! u32);
            if !accept(TK_COMMA) { break; }
        }
    }
    expect(TK_R_PAREN, "')'");
    pop_scope();
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    return start, count;
}

// A type name (C11 6.7.7).
// With -g its written type is left in tn_dty.
var tn_dty: u32 = 0;
recursive fn parse_type_name() -> u32 {
    var ds = DeclSpec { .. };
    var a = Attrs { .. };
    parse_declspec(ds, a, false);
    if !ds.any {
        err("expected a type");
        tn_dty = t_int;
        return t_int;
    }
    let base = finish_declspec(ds, false);
    let base2 = apply_type_attrs(base, a, ds.loc);
    let d = parse_declarator(base2, d_after(declspec_dty(ds, base), base, base2), 1, a);
    parse_attributes(a);
    let r = apply_type_attrs(d.ty, a, ds.loc);
    tn_dty = d_after(d.dty, d.ty, r);
    return r;
}

// ---------------------------------------------------------------------------
// Declarations

let CTX_FILESCOPE = 0;
let CTX_BLOCK = 1;
let CTX_FOR = 2;

var cur_func: i64 = -1;
var func_gen: i64 = 0;
var label_syms: u32[>..<] = [];

fn get_attr(s: i64) -> i64 {
    if syms[s].attr == 0 {
        if sym_attrs.len == 0 { sym_attrs.push(SymAttr { asm_label: 0, asm_len: 0, cleanup: -1, align: 0, flags: 0, .. }); }
        syms[s].attr = sym_attrs.len as! u32;
        sym_attrs.push(SymAttr { asm_label: 0, asm_len: 0, cleanup: -1, align: 0, flags: 0, .. });
    }
    return syms[s].attr as i64;
}

fn record_attrs(s: i64, a: Attrs&, align: u32) {
    if a.asm_len != 0 || a.cleanup >= 0 || a.aligned != 0 || align != 0 || a.misc != 0 || a.sec_len != 0 || a.alias_len != 0 || a.vis != 0 {
        let ai = get_attr(s);
        if a.asm_len != 0 { sym_attrs[ai].asm_label = a.asm_off; sym_attrs[ai].asm_len = a.asm_len; }
        if a.sec_len != 0 { sym_attrs[ai].sec_off = a.sec_off; sym_attrs[ai].sec_len = a.sec_len; }
        if a.alias_len != 0 { sym_attrs[ai].alias_off = a.alias_off; sym_attrs[ai].alias_len = a.alias_len; }
        if a.vis != 0 { sym_attrs[ai].vis = a.vis; }
        if a.misc & AM_CTOR != 0 { sym_attrs[ai].ctor_prio = a.ctor_prio; }
        if a.misc & AM_DTOR != 0 { sym_attrs[ai].dtor_prio = a.dtor_prio; }
        if a.cleanup >= 0 { sym_attrs[ai].cleanup = a.cleanup; }
        var al = a.aligned;
        if align > al { al = align; }
        if al > sym_attrs[ai].align { sym_attrs[ai].align = al; }
        sym_attrs[ai].flags = sym_attrs[ai].flags | a.misc;
    }
    if a.misc & AM_WEAK != 0 { syms[s].flags = syms[s].flags | SF_WEAK; }
    if a.misc & AM_NORETURN != 0 { syms[s].flags = syms[s].flags | SF_NORETURN; }
}

// Declares (or redeclares) d. Returns the symbol.
fn declare(d: Declr&, ds: DeclSpec&, a: Attrs&, ctx: i64) -> i64 {
    let name = d.name;
    var ty = d.ty;
    let loc = d.loc;
    if ds.sc == SC_TYPEDEF {
        if a.misc & AM_TRANSPARENT != 0 && kind_of(ty) == TY_UNION {
            let r = rec_of(ty);
            records[r].flags = records[r].flags | RF_TRANSPARENT;
        }
        if a.aligned != 0 { ty = with_align(ty, a.aligned); }
        if ds.align != 0 { ty = with_align(ty, ds.align); }
        let prev = lookup_ord(name);
        if prev >= 0 && syms[prev].scope as i64 == scope_depth {
            if syms[prev].kind == SK_TYPEDEF && compatible(tcanon(syms[prev].ty), tcanon(ty)) {
                if !dbg_g { return prev; }
                // -g: uses after this point name this declaration (in DWARF
                // as in clang); the type stays the first one's
                let s2 = new_sym(SK_TYPEDEF, name, syms[prev].ty, loc);
                syms[s2].sc = SC_TYPEDEF;
                syms[s2].flags = syms[prev].flags;
                dt_set_sym(s2, if dq_canon(d.dty) == syms[prev].ty { d.dty } else { syms[prev].ty });
                dt_note_typedef(s2, cur_func);
                bind_sym(s2, false);
                return s2;
            }
            err_at(loc, str("typedef redefinition with different types (", tname(ty), " vs ", tname(syms[prev].ty), ")"));
        }
        let s = new_sym(SK_TYPEDEF, name, ty, loc);
        syms[s].sc = SC_TYPEDEF;
        if scope_depth == 0 { syms[s].flags = SF_FILESCOPE; }
        if dbg_types {
            // the written type of what the name stands for (an alignment
            // override is the typedef's own: DW_AT_alignment)
            dt_set_sym(s, if dq_canon(d.dty) == d.ty { d.dty } else { d.ty });
            dt_note_typedef(s, cur_func);
        }
        bind_sym(s, false);
        return s;
    }
    if is_func(ty) {
        var sc = ds.sc;
        if types[ty >> 4].flags & TF_NOPROTO != 0 && scope_depth == 0 {
            // clang: a library builtin redeclared without a prototype keeps the
            // builtin's type
            let bi = builtin_index(name);
            if bi >= 0 && is_library_name(ident_text(name as i64)) {
                let bty = builtin_type(bi);
                if bty != 0 && compatible(bty, ty) && types[bty >> 4].flags & TF_NOPROTO == 0 { ty = bty; }
            }
        }
        if scope_depth > 0 && sc == SC_STATIC {
            err_at(loc, "function declared in block scope cannot have 'static' storage class");
        }
        let prev = lookup_ord(name);
        if prev >= 0 && (syms[prev].kind == SK_FUNC || syms[prev].kind == SK_BUILTIN) &&
           (syms[prev].scope as i64 == scope_depth || syms[prev].flags & SF_FILESCOPE != 0 || syms[prev].sc == SC_EXTERN) {
            let pt = syms[prev].ty;
            // -g: DW_AT_prototyped is the first declaration's (clang's
            // getCanonicalDecl()->hasPrototype(); an implicit one has none)
            if dbg_types && !fn_proto_known(prev) {
                dt_note_proto(prev, syms[prev].flags & SF_IMPLICIT == 0 && types[pt >> 4].flags & TF_NOPROTO == 0);
            }
            if syms[prev].flags & SF_IMPLICIT != 0 {
                syms[prev].ty = ty;
                syms[prev].flags = syms[prev].flags & ~SF_IMPLICIT;
                if syms[prev].kind == SK_BUILTIN { syms[prev].kind = SK_FUNC; }
            } else if !compatible(pt, ty) {
                err_at(loc, str("conflicting types for '", ident_text(name as i64), "'"));
            } else {
                syms[prev].ty = composite(pt, ty);
                // clang's mergeTypes: the old declaration's type, unless
                // the composite differs from it
                if dbg_types && syms[prev].ty != pt {
                    dt_set_sym(prev, if syms[prev].ty == ty && dq_canon(d.dty) == ty { d.dty } else { syms[prev].ty });
                }
            }
            if sc == SC_STATIC && syms[prev].sc != SC_STATIC && syms[prev].flags & SF_IMPLICIT == 0 {
                // static after non-static: clang errors unless the first was implicit
            }
            if ds.is_inline { syms[prev].flags = syms[prev].flags | SF_INLINE; }
            if ds.noreturn { syms[prev].flags = syms[prev].flags | SF_NORETURN; }
            // a later declaration has (or, without one, inherits) a prototype
            syms[prev].flags = syms[prev].flags & ~SF_KRDEF;
            record_attrs(prev, a, 0);
            if scope_depth == 0 && (!ds.is_inline || ds.sc == SC_EXTERN) { syms[prev].flags = syms[prev].flags | SF_FORCE_DEF; }
            if syms[prev].scope as i64 != scope_depth && scope_depth > 0 {
                // a block-scope redeclaration of a visible function: same entity
            }
            return prev;
        }
        if prev >= 0 && syms[prev].scope as i64 == scope_depth {
            err_at(loc, str("redefinition of '", ident_text(name as i64), "' as different kind of symbol"));
        }
        let s = new_sym(SK_FUNC, name, ty, loc);
        if dbg_types {
            dt_set_sym(s, if dq_canon(d.dty) == ty { d.dty } else { ty });
            // G1: a block-scope declaration that is no longer visible is
            // still the first declaration of the entity (clang's local
            // extern declarations); fn_proto keeps its prototype by name
            let lk = (name as u64) | 0x10000000000;
            let first = fn_proto.get(lk);
            let proto = types[ty >> 4].flags & TF_NOPROTO == 0;
            if first { dt_note_proto(s, first == 1); }
            else {
                dt_note_proto(s, proto);
                if scope_depth > 0 { fn_proto.insert(lk, if proto { 1 } else { 2 }); }
            }
        }
        syms[s].sc = if sc == SC_STATIC { SC_STATIC } else if sc == SC_EXTERN { SC_EXTERN } else { SC_NONE };
        if scope_depth == 0 { syms[s].flags = SF_FILESCOPE; } else { syms[s].flags = SF_LOCALLINK; }
        if ds.is_inline { syms[s].flags = syms[s].flags | SF_INLINE; }
        if ds.noreturn { syms[s].flags = syms[s].flags | SF_NORETURN; }
        if scope_depth == 0 && (!ds.is_inline || ds.sc == SC_EXTERN) { syms[s].flags = syms[s].flags | SF_FORCE_DEF; }
        record_attrs(s, a, 0);
        bind_sym(s, false);
        return s;
    }
    // objects
    if is_void(ty) {
        err_at(loc, str("variable has incomplete type 'void'"));
        ty = t_int;
    }
    let prev = lookup_ord(name);
    if scope_depth == 0 || ds.sc == SC_EXTERN {
        if prev >= 0 && (syms[prev].scope as i64 == scope_depth || (ds.sc == SC_EXTERN && syms[prev].flags & SF_FILESCOPE != 0)) {
            if syms[prev].kind != SK_VAR {
                err_at(loc, str("redefinition of '", ident_text(name as i64), "' as different kind of symbol"));
            } else if !compatible(syms[prev].ty, ty) {
                // int a[]; int a[10]; is fine; other differences are errors
                if !(is_array(syms[prev].ty) && is_array(ty) && compatible(tbase(syms[prev].ty), tbase(ty))) {
                    err_at(loc, str("redefinition of '", ident_text(name as i64), "' with a different type: ", tname(ty), " vs ", tname(syms[prev].ty)));
                } else {
                    syms[prev].ty = composite(syms[prev].ty, ty);
                }
            } else {
                syms[prev].ty = composite(syms[prev].ty, ty);
            }
            if ds.sc == SC_STATIC { syms[prev].sc = SC_STATIC; }
            if ds.thread { syms[prev].flags = syms[prev].flags | SF_THREAD; }
            record_attrs(prev, a, ds.align);
            if syms[prev].scope as i64 == scope_depth || scope_depth == 0 { return prev; }
            // block-scope extern of a file-scope object: bind the same symbol here
            let s2 = new_sym(SK_VAR, name, syms[prev].ty, loc);
            syms[s2].sc = SC_EXTERN;
            syms[s2].canon = prev as! i32;
            syms[s2].flags = SF_LOCALLINK;
            bind_sym(s2, false);
            return s2;
        }
    } else if prev >= 0 && syms[prev].scope as i64 == scope_depth {
        err_at(loc, str("redefinition of '", ident_text(name as i64), "'"));
    }
    let s = new_sym(SK_VAR, name, ty, loc);
    if dbg_types { dt_set_sym(s, if dq_canon(d.dty) == ty { d.dty } else { ty }); }
    syms[s].sc = ds.sc;
    if scope_depth == 0 { syms[s].flags = SF_FILESCOPE; }
    else if ds.sc == SC_EXTERN { syms[s].flags = SF_LOCALLINK; }
    if ds.thread { syms[s].flags = syms[s].flags | SF_THREAD; }
    record_attrs(s, a, ds.align);
    bind_sym(s, false);
    return s;
}

// A declaration; its N_DECL / N_FUNCDEF / N_TYPEDEF / N_TAGDEF nodes are
// pushed to nscratch.
recursive fn parse_declaration(ctx: i64) {
    var ds = DeclSpec { .. };
    var a = Attrs { .. };
    let start_loc = tloc();
    if at_kw(KW_STATIC_ASSERT) {
        parse_static_assert();
        return;
    }
    parse_declspec(ds, a, true);
    let implicit_ok = true;
    var base = finish_declspec(ds, implicit_ok);
    var dbase = base;
    if dbg_types {
        let b0 = base;
        base = apply_type_attrs(base, a, ds.loc);
        dbase = d_after(declspec_dty(ds, b0), b0, base);
    } else {
        base = apply_type_attrs(base, a, ds.loc);
    }
    if at(TK_SEMI) {
        adv();
        if ds.tag_sym >= 0 && ds.tag_defined {
            nscratch.push(node(N_TAGDEF, 0, syms[ds.tag_sym].ty, ds.tag_sym as i64, 0, 0, start_loc));
        } else if ds.tag_sym < 0 && !ds.any {
        }
        return;
    }
    loop {
        var da = a;
        let d = parse_declarator(base, dbase, 0, da);
        parse_attributes(da);
        parse_asm_label(da);
        parse_attributes(da);
        var dd = d;
        if base == 0 {
            // __auto_type: the type comes from the initializer
            dd.ty = t_int;
            dd.dty = t_int;
        } else {
            dd.ty = apply_type_attrs(d.ty, da, d.loc);
            dd.dty = d_after(d.dty, d.ty, dd.ty);
        }
        if d.name == 0 {
            // error already reported; skip to the end of the declaration
            while !at(TK_SEMI) && !at(TK_EOF) && !at(TK_R_BRACE) { adv(); }
            accept(TK_SEMI);
            return;
        }
        if is_func(dd.ty) && ctx == CTX_FILESCOPE && (at(TK_L_BRACE) || (d.kr && !at(TK_SEMI) && !at(TK_COMMA))) {
            parse_function_def(dd, ds, da);
            return;
        }
        let s = declare(dd, ds, da, ctx);
        var init: u32 = 0;
        if accept(TK_EQUAL) {
            if ds.sc == SC_TYPEDEF {
                err_at(d.loc, "illegal initializer (only variables can be initialized)");
            }
            if syms[s].kind == SK_FUNC {
                err_at(d.loc, "illegal initializer (only variables can be initialized)");
            }
            let is_static = scope_depth == 0 || ds.sc == SC_STATIC || ds.sc == SC_EXTERN;
            if base == 0 {
                // __auto_type x = e;
                let e = rv(parse_assign());
                syms[s].ty = unqual(nty(e));
                if dbg_types {
                    let w = d_unqual(expr_written(e));
                    dd.dty = if dq_canon(w) == syms[s].ty { w } else { syms[s].ty };
                    dt_set_sym(s, dd.dty);
                }
                init = e;
            } else {
                init = parse_initializer_for(s, syms[s].ty, is_static);
            }
            if syms[s].flags & SF_DEFINED != 0 && scope_depth == 0 && syms[s].kind == SK_VAR && syms[s].scope == 0 {
                err_at(d.loc, str("redefinition of '", ident_text(d.name as i64), "'"));
            }
            syms[s].flags = syms[s].flags | SF_DEFINED;
            if scope_depth > 0 && ds.sc == SC_EXTERN {
                err_at(d.loc, "declaration of block scope identifier with linkage cannot have an initializer");
            }
        } else if syms[s].kind == SK_VAR && ds.sc != SC_TYPEDEF {
            let t = syms[s].ty;
            if scope_depth > 0 && ds.sc != SC_EXTERN && !is_complete(t) {
                if is_array(t) {
                    err_at(d.loc, str("definition of variable with array type needs an explicit size or an initializer"));
                } else {
                    err_at(d.loc, str("variable has incomplete type ", tname(t)));
                }
            }
            if scope_depth == 0 && ds.sc != SC_EXTERN { syms[s].flags = syms[s].flags | SF_TENTATIVE; }
        }
        if syms[s].kind == SK_TYPEDEF {
            nscratch.push(node(N_TYPEDEF, 0, syms[s].ty, s, 0, 0, d.loc));
        } else {
            let dn = node(N_DECL, 0, syms[s].ty, s, init as i64, start_loc as i64, d.loc);
            // G1: what clang's evaluator reads of a const variable
            if init != 0 && syms[s].kind == SK_VAR { cv_define(s, dn, init); }
            if dbg_types {
                dt_set_node(dn, dd.dty);
                if ds.sc == SC_EXTERN { dt_note_extern(dn); }
            }
            nscratch.push(dn);
        }
        if !accept(TK_COMMA) { break; }
    }
    if !at(TK_SEMI) {
        tok_buf.clear();
        tok_buf.append("expected ';' after declaration, got ");
        tok_desc(tok_buf, pc);
        err(tok_buf);
        while !at(TK_SEMI) && !at(TK_EOF) && !at(TK_R_BRACE) { adv(); }
    }
    accept(TK_SEMI);
}

recursive fn parse_static_assert() {
    let loc = tloc();
    adv();
    expect(TK_L_PAREN, "'('");
    let e = parse_cond();
    let ok, v = fold_int(rv(e));
    if accept(TK_COMMA) {
        if at(TK_STRING) { string_literal(); }
    }
    expect(TK_R_PAREN, "')'");
    expect(TK_SEMI, "';'");
    if !ok {
        err_at(loc, "static assertion expression is not an integral constant expression");
    } else if v == 0 {
        err_at(loc, "static assertion failed");
    }
}

recursive fn parse_function_def(d: Declr&, ds: DeclSpec&, a: Attrs&) {
    var dd = d;
    // K&R parameter declarations
    if d.kr {
        // the identifier-list parameters are visible to the declarations
        push_scope();
        for i in d.nparams {
            let p = nlist[d.params + i] as i64;
            bind_sym(p, false);
        }
        while !at(TK_L_BRACE) && !at(TK_EOF) {
            var pds = DeclSpec { .. };
            var pa = Attrs { .. };
            parse_declspec(pds, pa, true);
            let base = finish_declspec(pds, true);
            let dbase = declspec_dty(pds, base);
            loop {
                var pa2 = pa;
                let pd = parse_declarator(base, dbase, 0, pa2);
                parse_attributes(pa2);
                var found = false;
                for i in d.nparams {
                    let p = nlist[d.params + i] as i64;
                    if syms[p].name == pd.name {
                        var ty = apply_type_attrs(pd.ty, pa2, pd.loc);
                        let dty = d_after(pd.dty, pd.ty, ty);
                        let ty0 = ty;
                        if is_array(ty) { ty = mk_ptr(tbase(ty)); } else if is_func(ty) { ty = mk_ptr(ty); }
                        if dbg_types { dt_set_sym(p, d_adjust_param(dty, ty0, ty)); }
                        if dbg_g { syms[p].loc = pd.loc; }
                        syms[p].ty = ty;
                        syms[p].flags = syms[p].flags | SF_KR;
                        if pds.sc == SC_REGISTER { syms[p].sc = SC_REGISTER; }
                        found = true;
                    }
                }
                if !found && pd.name != 0 {
                    err_at(pd.loc, str("parameter named '", ident_text(pd.name as i64), "' is missing"));
                }
                if !accept(TK_COMMA) { break; }
            }
            expect(TK_SEMI, "';'");
        }
        pop_scope();
        for i in d.nparams {
            let p = nlist[d.params + i] as i64;
            if syms[p].flags & SF_KR == 0 {
                implicit_int(syms[p].loc, str("parameter '", ident_text(syms[p].name as i64), "' was not declared, defaults to 'int'"));
            }
        }
    }
    let s = declare(dd, ds, a, CTX_FILESCOPE);
    if d.kr && syms[s].kind == SK_FUNC {
        // clang: references to a function whose latest declaration is a
        // definition without a prototype have the type without prototype;
        // calls still convert the arguments to the parameter types, which
        // for a K&R definition are the promoted declared types (or the
        // prototype's, GNU)
        syms[s].flags = syms[s].flags | SF_KRDEF;
        let ft = types[syms[s].ty >> 4];
        if ft.flags & TF_NOPROTO != 0 {
            fn_scratch.clear();
            for i in d.nparams { fn_scratch.push(arg_promoted_type(syms[nlist[d.params + i]].ty)); }
            syms[s].ty = qt(mk_type(TY_FUNC, (ft.flags as i64) & ~TF_NOPROTO, ft.base, 0, 0, 0) as i64, 0);
        }
    }
    if syms[s].flags & SF_DEFINED != 0 && syms[s].kind == SK_FUNC {
        // only a GNU extern inline definition may be followed by another
        // definition (clang's canRedefineFunction)
        if syms[s].flags & SF_GNU_EXTERN_INLINE == 0 {
            if syms[s].flags & SF_INLINE != 0 && !opt_c89 {
                err_at(d.loc, str("redefinition of a 'extern inline' function '", ident_text(d.name as i64), "' is not supported in C99 mode"));
            } else {
                err_at(d.loc, str("redefinition of '", ident_text(d.name as i64), "'"));
            }
        }
    }
    syms[s].flags = syms[s].flags & ~SF_GNU_EXTERN_INLINE;
    if ds.is_inline && ds.sc == SC_EXTERN {
        let gnu = opt_c89 || a.misc & AM_GNU_INLINE != 0 || (syms[s].attr != 0 && sym_attrs[syms[s].attr].flags & AM_GNU_INLINE != 0);
        if gnu { syms[s].flags = syms[s].flags | SF_GNU_EXTERN_INLINE; }
    }
    syms[s].flags = syms[s].flags | SF_DEFINED;
    let rt = unqual(types[syms[s].ty >> 4].base);
    if !is_void(rt) && !is_complete(rt) {
        err_at(d.loc, str("incomplete result type ", tname(rt), " in function definition"));
    }
    let saved_func = cur_func;
    let saved_pf = pf_dty;
    cur_func = s;
    pf_dty = if dbg_types { dd.dty } else { 0 };
    func_gen++;
    let lmark = label_syms.len;
    push_scope();
    for i in d.nparams {
        let p = nlist[d.params + i] as i64;
        if syms[p].name != 0 { bind_sym(p, false); }
        else if !(i == 0 && d.nparams == 1 && is_void(syms[p].ty)) {
            // unnamed parameters are allowed (C23 / extension)
        }
        if !is_complete(syms[p].ty) && !is_void(syms[p].ty) {
            err_at(syms[p].loc, str("variable has incomplete type ", tname(syms[p].ty)));
        }
    }
    let body = parse_compound_stmt(false);
    pop_scope();
    // labels
    for j in lmark..label_syms.len {
        let l = label_syms[j] as i64;
        if syms[l].flags & SF_DEFINED == 0 {
            err_at(syms[l].loc, str("use of undeclared label '", ident_text(syms[l].name as i64), "'"));
        }
    }
    label_syms.resize(lmark);
    cur_func = saved_func;
    pf_dty = saved_pf;
    let n = node_v(N_FUNCDEF, 0, syms[s].ty, s, body as i64, d.nparams, d.loc, d.params);
    syms[s].def = n as! i32;
    nscratch.push(n);
}

// ---------------------------------------------------------------------------
// Statements

var loop_depth: i64 = 0;
var break_depth: i64 = 0;
var switch_cases: u32[>..<] = [];
// The switch statements being parsed: the promoted condition type, where its cases start in switch_cases, a default seen.
struct SwitchCtx { ty: u32, mark: u32, dflt: bool }
var switches: SwitchCtx[>..<] = [];

fn label_ref(name: u32, loc: u32) -> i64 {
    ensure_ids();
    let l = id_bind[name].label as i64;
    if l >= 0 && syms[l].v == func_gen { return l; }
    let s = new_sym(SK_LABEL, name, t_void, loc);
    syms[s].v = func_gen;
    id_bind[name].label = s as! i32;
    label_syms.push(s as! u32);
    return s;
}

recursive fn parse_compound_stmt(stmt_expr: bool) -> u32 {
    let loc = tloc();
    expect(TK_L_BRACE, "'{'");
    push_scope();
    let mark = nscratch.len;
    while !at(TK_R_BRACE) && !at(TK_EOF) {
        if at_kw(KW_LABEL) {
            // __label__ a, b;
            adv();
            loop {
                if at(TK_IDENT) {
                    let ls = label_ref(tval(), tloc());
                    dt_note_local_label(ls, tloc());
                    adv();
                }
                if !accept(TK_COMMA) { break; }
            }
            expect(TK_SEMI, "';'");
            continue;
        }
        if starts_declaration() {
            parse_declaration(CTX_BLOCK);
            continue;
        }
        let s = parse_stmt();
        nscratch.push(s);
    }
    let rloc = tloc();
    expect(TK_R_BRACE, "'}'");
    pop_scope();
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    return node_v(N_COMPOUND, 0, 0, 0, rloc as i64, count, loc, start);
}

recursive fn cond_expr(loc: u32) -> u32 {
    expect(TK_L_PAREN, "'('");
    let e = parse_expr();
    expect(TK_R_PAREN, "')'");
    let r = rv(e);
    if !is_error(r) && !is_scalar(nty(r)) {
        err_at(loc, str("statement requires expression of scalar type (", tname(nty(r)), " invalid)"));
    }
    return r;
}

recursive fn parse_stmt() -> u32 {
    let loc = tloc();
    let k = tk();
    if k == TK_L_BRACE { return parse_compound_stmt(false); }
    if k == TK_SEMI { adv(); return node(N_NULL, 0, 0, 0, 0, 0, loc); }
    if k == TK_IDENT && tk_n(1) == TK_COLON {
        let name = tval();
        adv();
        adv();
        let l = label_ref(name, loc);
        if syms[l].flags & SF_DEFINED != 0 {
            err_at(loc, str("redefinition of label '", ident_text(name as i64), "'"));
        }
        syms[l].flags = syms[l].flags | SF_DEFINED;
        syms[l].loc = loc;
        var la = Attrs { .. };
        parse_attributes(la);
        if at(TK_R_BRACE) {
            // a label at the end of a compound statement (C23 / extension)
            let ns = node(N_NULL, 0, 0, 0, 0, 0, loc);
            return node(N_LABEL, 0, 0, l, ns as i64, 0, loc);
        }
        var st: u32 = 0;
        if starts_declaration() {
            // a label followed by a declaration (C23 / extension): the
            // declaration nodes go to the enclosing list
            st = node(N_NULL, 0, 0, 0, 0, 0, loc);
            let lab = node(N_LABEL, 0, 0, l, st as i64, 0, loc);
            nscratch.push(lab);
            parse_declaration(CTX_BLOCK);
            return node(N_NULL, 0, 0, 0, 0, 0, loc);
        }
        st = parse_stmt();
        return node(N_LABEL, 0, 0, l, st as i64, 0, loc);
    }
    if k < TK_KW {
        let e = parse_expr();
        expect(TK_SEMI, "';' after expression");
        return node(N_EXPR, 0, 0, discard_value(e) as i64, 0, 0, loc);
    }
    let w = k - TK_KW;
    if w == KW_IF {
        adv();
        let c = cond_expr(loc);
        let t = parse_stmt();
        var e: u32 = 0;
        if at_kw(KW_ELSE) {
            adv();
            e = parse_stmt();
        }
        return node(N_IF, 0, 0, c as i64, t as i64, e as i64, loc);
    }
    if w == KW_WHILE {
        adv();
        let c = cond_expr(loc);
        loop_depth++;
        break_depth++;
        let b = parse_stmt();
        loop_depth--;
        break_depth--;
        return node(N_WHILE, 0, 0, c as i64, b as i64, 0, loc);
    }
    if w == KW_DO {
        adv();
        loop_depth++;
        break_depth++;
        let b = parse_stmt();
        loop_depth--;
        break_depth--;
        if !at_kw(KW_WHILE) { err("expected 'while' in do/while loop"); return b; }
        adv();
        let c = cond_expr(loc);
        expect(TK_SEMI, "';' after do/while statement");
        return node(N_DO, 0, 0, b as i64, c as i64, 0, loc);
    }
    if w == KW_FOR {
        adv();
        expect(TK_L_PAREN, "'('");
        push_scope();
        var init: u32 = 0;
        if at(TK_SEMI) {
            adv();
        } else if starts_declaration() {
            let mark = nscratch.len;
            parse_declaration(CTX_FOR);
            let count = nscratch.len - mark;
            let start = commit_list(mark);
            init = node_v(N_COMPOUND, 0, 0, 0, 0, count, loc, start);
        } else {
            let e = parse_expr();
            init = node(N_EXPR, 0, 0, discard_value(e) as i64, 0, 0, loc);
            expect(TK_SEMI, "';' in 'for' statement specifier");
        }
        var c: u32 = 0;
        if !at(TK_SEMI) {
            let e = parse_expr();
            c = rv(e);
            if !is_error(c) && !is_scalar(nty(c)) { err_at(loc, "statement requires expression of scalar type"); }
        }
        expect(TK_SEMI, "';' in 'for' statement specifier");
        var inc: u32 = 0;
        if !at(TK_R_PAREN) { inc = discard_value(parse_expr()); }
        expect(TK_R_PAREN, "')'");
        loop_depth++;
        break_depth++;
        let b = parse_stmt();
        loop_depth--;
        break_depth--;
        pop_scope();
        return node_v(N_FOR, 0, 0, init as i64, c as i64, inc as i64, loc, b as i64);
    }
    if w == KW_SWITCH {
        adv();
        expect(TK_L_PAREN, "'('");
        let e = parse_expr();
        expect(TK_R_PAREN, "')'");
        var c = rv(e);
        if !is_error(c) && !is_integer(nty(c)) {
            err_at(loc, str("statement requires expression of integer type (", tname(nty(c)), " invalid)"));
        } else if !is_error(c) {
            c = promote(c);
        }
        let mark = switch_cases.len;
        switches.push(SwitchCtx { ty: nty(c), mark: mark as! u32, dflt: false });
        break_depth++;
        let b = parse_stmt();
        break_depth--;
        switches.pop();
        let count = switch_cases.len - mark;
        let start = nlist.len;
        for j in mark..switch_cases.len { nlist.push(switch_cases[j]); }
        switch_cases.resize(mark);
        return node_v(N_SWITCH, 0, 0, c as i64, b as i64, count, loc, start);
    }
    if w == KW_CASE {
        adv();
        let e = parse_cond();
        var hi: u32 = 0;
        var hv: i64 = 0;
        if at(TK_ELLIPSIS) {
            adv();
            let e2 = parse_cond();
            let ok2, v2 = fold_int(rv(e2));
            if !ok2 { err_at(nodes[e2].loc, "expression is not an integer constant expression"); }
            hv = v2;
            hi = 1;
        }
        expect(TK_COLON, "':' after 'case'");
        let ok, v0 = fold_int(rv(e));
        if !ok { err_at(nodes[e].loc, "expression is not an integer constant expression"); }
        if switches.len == 0 {
            err_at(loc, "'case' statement not in switch statement");
            return parse_stmt();
        }
        let st = switches[switches.len - 1].ty;
        let v = trunc_to(v0, st);
        let mark = switches[switches.len - 1].mark as i64;
        // (128-bit values are only folded to 64 bits here: B2 refolds them
        // from the expression kept in the case's b)
        let wide = type_size(st) > 8;
        for j in mark..switch_cases.len {
            if wide { break; }
            let cn = nodes[switch_cases[j]];
            if cn.kind == N_CASE {
                let lo2 = cn.v;
                let hi2 = if cn.c != 0 { nodes[cn.c].v } else { lo2 };
                let vhi = if hi != 0 { trunc_to(hv, st) } else { v };
                if v <= hi2 && vhi >= lo2 {
                    err_at(loc, str("duplicate case value '", v, "'"));
                    break;
                }
            }
        }
        var hn: u32 = 0;
        if hi != 0 { hn = int_node(trunc_to(hv, st), st, loc); }
        let cn = node_v(N_CASE, 0, st, 0, if wide { convert(rv(e), st) as i64 } else { 0 }, hn as i64, loc, v);
        if dbg_types && hi == 0 {
            // -g: a case value that names an enumerator (clang's EmitCaseStmt)
            var ce = e;
            while nodes[ce].kind as i64 == N_ICAST { ce = nodes[ce].a; }
            let es = enumc_of(ce);
            if es >= 0 { dt_note_enumc(cn, es); }
        }
        switch_cases.push(cn);
        let s = if at(TK_R_BRACE) { node(N_NULL, 0, 0, 0, 0, 0, loc) } else { parse_stmt() };
        nodes[cn].a = s;
        return cn;
    }
    if w == KW_DEFAULT {
        adv();
        expect(TK_COLON, "':' after 'default'");
        if switches.len == 0 {
            err_at(loc, "'default' statement not in switch statement");
            return parse_stmt();
        }
        let di = switches.len - 1;
        if switches[di].dflt { err_at(loc, "multiple default labels in one switch"); }
        switches[di].dflt = true;
        let dn = node(N_DEFAULT, 0, 0, 0, 0, 0, loc);
        switch_cases.push(dn);
        let s = if at(TK_R_BRACE) { node(N_NULL, 0, 0, 0, 0, 0, loc) } else { parse_stmt() };
        nodes[dn].a = s;
        return dn;
    }
    if w == KW_BREAK {
        adv();
        expect(TK_SEMI, "';' after 'break'");
        if break_depth == 0 { err_at(loc, "'break' statement not in loop or switch statement"); }
        return node(N_BREAK, 0, 0, 0, 0, 0, loc);
    }
    if w == KW_CONTINUE {
        adv();
        expect(TK_SEMI, "';' after 'continue'");
        if loop_depth == 0 { err_at(loc, "'continue' statement not in loop statement"); }
        return node(N_CONTINUE, 0, 0, 0, 0, 0, loc);
    }
    if w == KW_GOTO {
        adv();
        if at(TK_STAR) {
            adv();
            let e = rv(parse_expr());
            expect(TK_SEMI, "';' after 'goto'");
            return node(N_IGOTO, 0, 0, e as i64, 0, 0, loc);
        }
        if !at(TK_IDENT) { err("expected identifier"); return node(N_NULL, 0, 0, 0, 0, 0, loc); }
        let l = label_ref(tval(), tloc());
        syms[l].flags = syms[l].flags | SF_LABEL_USED;
        adv();
        expect(TK_SEMI, "';' after 'goto'");
        return node(N_GOTO, 0, 0, l, 0, 0, loc);
    }
    if w == KW_RETURN {
        adv();
        var e: u32 = 0;
        let rt = if cur_func >= 0 { unqual(types[syms[cur_func].ty >> 4].base) } else { t_int };
        if !at(TK_SEMI) {
            let x = parse_expr();
            let r = rv(x);
            if is_void(rt) {
                if !is_void(nty(r)) && !is_error(r) { return_mismatch(loc, "void function should not return a value"); }
                e = r;
            } else {
                e = assign_convert(r, rt, loc, 3);
            }
        } else if !is_void(rt) {
            return_mismatch(loc, "non-void function should return a value");
        }
        expect(TK_SEMI, "';' after return statement");
        return node(N_RETURN, 0, rt, e as i64, 0, 0, loc);
    }
    if w == KW_ASM { return parse_asm_stmt(); }
    if w == KW_ATTRIBUTE {
        // statement attributes: __attribute__((fallthrough));
        var a = Attrs { .. };
        parse_attributes(a);
        if at(TK_SEMI) { adv(); return node(N_NULL, 0, 0, 0, 0, 0, loc); }
        return parse_stmt();
    }
    if starts_declaration() {
        // a declaration where a statement is required (C23 allows it after labels)
        let mark = nscratch.len;
        parse_declaration(CTX_BLOCK);
        let count = nscratch.len - mark;
        let start = commit_list(mark);
        return node_v(N_COMPOUND, 0, 0, 0, 0, count, loc, start);
    }
    let e = parse_expr();
    expect(TK_SEMI, "';' after expression");
    return node(N_EXPR, 0, 0, discard_value(e) as i64, 0, 0, loc);
}


recursive fn parse_asm_stmt() -> u32 {
    let loc = tloc();
    adv();
    var quals_bits = 0;     // 1 goto, 2 volatile, 4 inline
    while at_kw(KW_VOLATILE) || at_kw(KW_INLINE) || at_kw(KW_GOTO) {
        if at_kw(KW_GOTO) { quals_bits = quals_bits | 1; }
        if at_kw(KW_VOLATILE) { quals_bits = quals_bits | 2; }
        if at_kw(KW_INLINE) { quals_bits = quals_bits | 4; }
        adv();
    }
    expect(TK_L_PAREN, "'('");
    var tmpl: u32 = 0;
    if at(TK_STRING) { tmpl = string_literal(); } else { err("expected string literal in 'asm'"); }
    let mark = nscratch.len;
    var section = 0;
    while accept(TK_COLON) || (section == 0 && false) {
        section++;
        if at(TK_COLON) { continue; }
        if at(TK_R_PAREN) { break; }
        loop {
            if section <= 2 {
                var opname: u32 = 0;
                if at(TK_L_SQUARE) { adv(); if at(TK_IDENT) { opname = tval(); adv(); } expect(TK_R_SQUARE, "']'"); }
                var cs: u32 = 0;
                if at(TK_STRING) { cs = string_literal(); } else { err("expected string literal"); break; }
                expect(TK_L_PAREN, "'('");
                let e = parse_expr();
                expect(TK_R_PAREN, "')'");
                var ex = e;
                if section == 1 {
                    if !is_lvalue(e) { err_at(nodes[e].loc, "invalid lvalue in asm output"); }
                } else {
                    ex = e;
                }
                nscratch.push(node(N_ASMOP, section, 0, cs as i64, ex as i64, opname as i64, nodes[e].loc));
            } else if section == 3 {
                if at(TK_STRING) {
                    let cs = string_literal();
                    nscratch.push(node(N_ASMOP, 3, 0, cs as i64, 0, 0, loc));
                } else { err("expected string literal"); break; }
            } else {
                if at(TK_IDENT) {
                    let l = label_ref(tval(), tloc());
                    syms[l].flags = syms[l].flags | SF_LABEL_USED;
                    nscratch.push(node(N_ASMOP, 4, 0, l, 0, 0, loc));
                    adv();
                } else { err("expected identifier"); break; }
            }
            if !accept(TK_COMMA) { break; }
        }
        if section >= 4 { break; }
    }
    expect(TK_R_PAREN, "')'");
    expect(TK_SEMI, "';' after asm statement");
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    return node_v(N_ASM, quals_bits, 0, tmpl as i64, 0, count, loc, start);
}

// ---------------------------------------------------------------------------
// The translation unit

var tu_node: u32 = 0;

// __PRETTY_FUNCTION__ prints written types: a translation unit that uses
// it builds them (dtype.goose) without -g too.
fn pf_scan() {
    if dbg_types { return; }
    let id = intern("__PRETTY_FUNCTION__");
    for t in tu_toks {
        if t.kind as i64 == TK_KW + KW_FUNC && t.val == id {
            dbg_types = true;
            return;
        }
    }
}

recursive fn parse_tu() {
    let mark = nscratch.len;
    // G1: the parse cache replays the state after the leading includes
    // (pcache.goose), or records it when the loop reaches their end
    let replayed = pt_begin();
    while !at(TK_EOF) {
        if pt_rec { pt_boundary(); }
        if at(TK_SEMI) { adv(); continue; }
        if at_kw(KW_ASM) {
            // file-scope asm("...");
            let loc = tloc();
            adv();
            expect(TK_L_PAREN, "'('");
            var s: u32 = 0;
            if at(TK_STRING) { s = string_literal(); }
            expect(TK_R_PAREN, "')'");
            expect(TK_SEMI, "';'");
            nscratch.push(node(N_ASM, 8, 0, s as i64, 0, 0, loc));
            continue;
        }
        if at(TK_R_BRACE) {
            err("extraneous closing brace ('}')");
            adv();
            continue;
        }
        let before = pc;
        parse_declaration(CTX_FILESCOPE);
        if pc == before { adv(); }
    }
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    tu_node = node_v(N_TU, 0, 0, 0, 0, count, 0, start);
}

fn declare_builtin_typedef(name: const u8[:], ty: u32) {
    let id = intern(name);
    ensure_ids();
    let s = new_sym(SK_TYPEDEF, id, ty, 0);
    syms[s].sc = SC_TYPEDEF;
    syms[s].flags = SF_FILESCOPE;
    bind_sym(s, false);
}

fn parse_init() {
    syms.push(Sym { kind: 0, sc: 0, flags: 0, name: 0, ty: 0, prev: -1, canon: 0, scope: 0, def: -1, v: 0, loc: 0, attr: 0 });
    nodes.push(Node { kind: 0, op: 0, flags: 0, ty: 0, a: 0, b: 0, c: 0, loc: 0, v: 0 });
    sym_attrs.push(SymAttr { asm_label: 0, asm_len: 0, cleanup: -1, align: 0, flags: 0, .. });
    declare_builtin_typedef("__builtin_va_list", t_valist);
    // the builtin tag, so that builtin signatures naming it get the same type
    let vt = new_sym(SK_TAG, records[0].name, t_valist_rec, 0);
    syms[vt].v = (t_valist_rec >> 4) as i64;
    bind_sym(vt, true);
    declare_builtin_typedef("__int128_t", t_int128);
    declare_builtin_typedef("__uint128_t", t_uint128);
    declare_builtin_typedef("__builtin_ms_va_list", t_charptr);
    declare_builtin_typedef("__fp16", t_float16);
    if opt_a64 {
        // AArch64 (F1): clang's SVE types, as incomplete structures (headers declare
        // functions with them; goosecc has no SVE)
        for nm in ["__SVInt8_t", "__SVInt16_t", "__SVInt32_t", "__SVInt64_t", "__SVUint8_t", "__SVUint16_t", "__SVUint32_t", "__SVUint64_t", "__SVFloat16_t", "__SVFloat32_t", "__SVFloat64_t", "__SVBfloat16_t", "__SVMfloat8_t", "__SVBool_t", "__SVCount_t", "__clang_svint8x2_t", "__clang_svint16x2_t", "__clang_svint32x2_t", "__clang_svint64x2_t", "__clang_svuint8x2_t", "__clang_svuint16x2_t", "__clang_svuint32x2_t", "__clang_svuint64x2_t", "__clang_svfloat16x2_t", "__clang_svfloat32x2_t", "__clang_svfloat64x2_t", "__clang_svbfloat16x2_t", "__clang_svmfloat8x2_t", "__clang_svint8x3_t", "__clang_svint16x3_t", "__clang_svint32x3_t", "__clang_svint64x3_t", "__clang_svuint8x3_t", "__clang_svuint16x3_t", "__clang_svuint32x3_t", "__clang_svuint64x3_t", "__clang_svfloat16x3_t", "__clang_svfloat32x3_t", "__clang_svfloat64x3_t", "__clang_svbfloat16x3_t", "__clang_svmfloat8x3_t", "__clang_svint8x4_t", "__clang_svint16x4_t", "__clang_svint32x4_t", "__clang_svint64x4_t", "__clang_svuint8x4_t", "__clang_svuint16x4_t", "__clang_svuint32x4_t", "__clang_svuint64x4_t", "__clang_svfloat16x4_t", "__clang_svfloat32x4_t", "__clang_svfloat64x4_t", "__clang_svbfloat16x4_t", "__clang_svmfloat8x4_t", "__clang_svboolx2_t", "__clang_svboolx4_t"] {
            let r = records.len;
            let rt = mk_tagged(TY_STRUCT, r as! u32);
            records.push(Record { name: intern(nm), ty: rt, first: fields.len as! u32, count: 0, size: 0, align: 1,
                flags: 0, rsv: 0, attr_align: 0, pack: 0, loc: 0, scope: 0 });
            declare_builtin_typedef(nm, rt << 4);
        }
        declare_builtin_typedef("__mfp8", t_uchar);   // (FP8: a byte here; goosecc has no FP8 arithmetic)
    }
}
