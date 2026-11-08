// goosecc D1: C++ declarations. Decl-specifiers, declarators, classes,
// enums, namespaces, using, linkage specifications, static_assert, and the
// translation unit. Templates are in cx_tmpl.goose, expressions in
// cx_expr.goose, statements and function bodies in cx_stmt.goose.

namespace cx;

import std;
import dictionary;
import .common;
import .types;
import .ast;
import .sema;
import .pp;
import .expr;
import .parse;
import .builtins;
import .cx_core;
import .cx_names;

// ---------------------------------------------------------------------------
// Attributes: GNU __attribute__((...)), C++11 [[...]], alignas(...),
// __declspec(...). Into C's Attrs (parse.goose).

recursive fn cx_attr_int() -> i64 {
    adv();      // (
    let e = parse_cexpr();
    var v: i64 = 0;
    let ok, x = const_int(e);
    if ok { v = x; }
    skip_to(TK_R_PAREN);
    accept(TK_R_PAREN);
    return v;
}

recursive fn cx_attr_string() -> u32, u32 {
    adv();      // (
    var off: u32 = 0;
    var len: u32 = 0;
    if at(TK_STRING) {
        let s = string_literal();
        let sl = strs[nodes[s].a];
        off = sl.start;
        len = sl.len - 1;
    }
    skip_to(TK_R_PAREN);
    accept(TK_R_PAREN);
    return off, len;
}

var abi_tag_off: u32 = 0;       // the last abi_tag("...") parsed (strbytes)
var abi_tag_len: u32 = 0;

fn attr_ident_name(i: i64) -> const u8[:] {
    let t = tu_toks[i];
    var s: const u8[:] = "";
    if t.kind as i64 == TK_IDENT || t.kind as i64 >= TK_KW { s = ident_text(t.val as i64); }
    if s.len > 4 && s[0] == '_' && s[1] == '_' && s[s.len - 1] == '_' && s[s.len - 2] == '_' { return s[2..s.len - 2]; }
    return s;
}

// One attribute (name at pc, maybe with arguments), GNU or [[]] style.
recursive fn cx_attr_one(a: Attrs&) {
    let name = attr_ident_name(pc);
    adv();
    if name == "aligned" {
        if at(TK_L_PAREN) {
            let v = cx_attr_int();
            if v > a.aligned as i64 { a.aligned = v as! u32; }
        } else if a.aligned < 16 { a.aligned = 16; }
    } else if name == "packed" { a.misc = a.misc | AM_PACKED; }
    else if name == "mode" {
        if at(TK_L_PAREN) {
            adv();
            if at(TK_IDENT) { a.mode = match_mode(attr_ident_name(pc)); adv(); }
            skip_to(TK_R_PAREN);
            accept(TK_R_PAREN);
        }
    } else if name == "vector_size" {
        if at(TK_L_PAREN) { a.vector_size = cx_attr_int(); }
    } else if name == "ext_vector_type" {
        if at(TK_L_PAREN) { a.ext_vector = cx_attr_int(); }
    } else if name == "noreturn" { a.misc = a.misc | AM_NORETURN; }
    else if name == "weak" { a.misc = a.misc | AM_WEAK; }
    else if name == "used" { a.misc = a.misc | AM_USED; }
    else if name == "unused" || name == "maybe_unused" { a.misc = a.misc | AM_UNUSED; }
    else if name == "always_inline" { a.misc = a.misc | AM_ALWAYS_INLINE; }
    else if name == "gnu_inline" { a.misc = a.misc | AM_GNU_INLINE; }
    else if name == "may_alias" { a.misc = a.misc | AM_MAY_ALIAS; }
    else if name == "fallthrough" { a.misc = a.misc | AM_FALLTHROUGH; }
    else if name == "nodebug" { a.misc = a.misc | AM_NODEBUG; }
    else if name == "abi_tag" {
        if at(TK_L_PAREN) { let o, l = cx_attr_string(); abi_tag_off = o; abi_tag_len = l; }
    }
    else if name == "section" {
        if at(TK_L_PAREN) { let o, l = cx_attr_string(); a.sec_off = o; a.sec_len = l; }
    } else if name == "alias" {
        if at(TK_L_PAREN) { let o, l = cx_attr_string(); a.alias_off = o; a.alias_len = l; }
    } else if name == "visibility" {
        if at(TK_L_PAREN) {
            let o, l = cx_attr_string();
            let v = strbytes[o..o + l];
            if v == "hidden" || v == "internal" { a.vis = 1; } else if v == "protected" { a.vis = 2; } else { a.vis = 0; }
        }
    } else if name == "init_priority" {
        if at(TK_L_PAREN) { cur_init_prio = cx_attr_int(); }
    } else if name == "constructor" || name == "destructor" {
        var prio: i64 = 65535;
        if at(TK_L_PAREN) { prio = cx_attr_int(); }
        if name == "constructor" { a.misc = a.misc | AM_CTOR; a.ctor_prio = prio as! u16; }
        else { a.misc = a.misc | AM_DTOR; a.dtor_prio = prio as! u16; }
    } else if at(TK_L_PAREN) {
        skip_group();
    }
}

// Any sequence of attribute specifiers (none: nothing consumed).
recursive fn cx_attrs(a: Attrs&) {
    loop {
        if at_kw(KW_ATTRIBUTE) {
            adv();
            if !at(TK_L_PAREN) { return; }
            adv();
            if !at(TK_L_PAREN) { skip_to(TK_R_PAREN); accept(TK_R_PAREN); continue; }
            adv();
            loop {
                if at(TK_R_PAREN) || at(TK_EOF) { break; }
                if accept(TK_COMMA) { continue; }
                if !at(TK_IDENT) && tk() < TK_KW { skip_to(TK_R_PAREN); break; }
                cx_attr_one(a);
            }
            accept(TK_R_PAREN);
            accept(TK_R_PAREN);
            continue;
        }
        if at(TK_L_SQUARE) && tk_n(1) == TK_L_SQUARE {
            adv();
            adv();
            if at_kw(KW_USING) {
                // [[using ns: attrs]]
                adv();
                adv();
                accept(TK_COLON);
            }
            loop {
                if at(TK_R_SQUARE) || at(TK_EOF) { break; }
                if accept(TK_COMMA) { continue; }
                if (at(TK_IDENT) || tk() >= TK_KW) && tk_n(1) == TK_COLONCOLON {
                    // a scoped name: gnu::x, clang::x
                    adv();
                    adv();
                }
                if at(TK_IDENT) || tk() >= TK_KW { cx_attr_one(a); } else { adv(); }
                accept(TK_ELLIPSIS);
            }
            accept(TK_R_SQUARE);
            accept(TK_R_SQUARE);
            continue;
        }
        if at_kw(KW_ALIGNAS) {
            adv();
            if at(TK_L_PAREN) {
                adv();
                var al: i64 = 0;
                if looks_like_type_id() {
                    let t = parse_type_id();
                    if !is_opaque(t) { al = type_align(nonref(t)); }
                } else {
                    let e = parse_cexpr();
                    let ok, v = const_int(e);
                    if ok { al = v; }
                }
                accept(TK_ELLIPSIS);
                skip_to(TK_R_PAREN);
                accept(TK_R_PAREN);
                if al > a.aligned as i64 { a.aligned = al as! u32; }
            }
            continue;
        }
        if at_kw(KW_DECLSPEC) {
            adv();
            if at(TK_L_PAREN) { skip_group(); }
            continue;
        }
        return;
    }
}

fn at_attr_start() -> bool {
    return at_kw(KW_ATTRIBUTE) || (at(TK_L_SQUARE) && tk_n(1) == TK_L_SQUARE) || at_kw(KW_ALIGNAS) || at_kw(KW_DECLSPEC);
}

// ---------------------------------------------------------------------------
// Decl-specifiers.

struct CDS {
    sc: u8 = 0,
    has_sc: bool = false,
    thread: bool = false,
    is_inline: bool = false,
    is_virtual: bool = false,
    is_explicit: bool = false,
    is_friend: bool = false,
    is_constexpr: bool = false,
    is_mutable: bool = false,
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
    nwchar: u8 = 0,
    nchar8: u8 = 0,
    nchar16: u8 = 0,
    nchar32: u8 = 0,
    nauto: u8 = 0,
    nnamed: u8 = 0,
    named: u32 = 0,
    tag_def: bool = false,      // a class or enum is defined here
    tag_decl: bool = false,     // an elaborated type specifier (class X)
    tag_ty: u32 = 0,
    any: bool = false,
    typename_kw: bool = false,
    loc: u32 = 0,
}

fn cds_has_type(ds: CDS&) -> bool {
    return ds.nvoid + ds.nchar + ds.nshort + ds.nint + ds.nlong + ds.nfloat + ds.ndouble + ds.nsigned + ds.nunsigned +
        ds.nbool + ds.ncomplex + ds.nint128 + ds.nfloat128 + ds.nfloat16 + ds.nbf16 + ds.nwchar + ds.nchar8 + ds.nchar16 +
        ds.nchar32 + ds.nauto + ds.nnamed > 0;
}

// Context of a declaration.
let DC_NS = 0;          // namespace scope
let DC_CLASS = 1;       // member-specification
let DC_BLOCK = 2;       // block scope
let DC_PARAM = 3;       // a parameter
let DC_TYPEID = 4;      // a type-id (no storage class)
let DC_COND = 5;        // a condition / for-range declaration

var cur_class: i64 = -1;    // the class scope being defined (member-specification), -1

// Is the name at pc (an identifier, maybe qualified) a constructor's
// declarator-id here? In a class X: X ( ; out of class: X::X ( / X<T>::X (.
recursive fn at_ctor_name() -> bool {
    if at(TK_IDENT) && tk_n(1) == TK_L_PAREN {
        let id = tu_toks[pc].val;
        if cur_class >= 0 && scopes[cur_class].name == id { return true; }
        return false;
    }
    // qualified: skim X :: X ( or X < ... > :: X (
    var j = pc;
    if tk_at(j) == TK_COLONCOLON { j++; }
    var last: u32 = 0;
    var prev: u32 = 0;
    loop {
        if tu_toks[j].kind as i64 != TK_IDENT { return false; }
        let id = tu_toks[j].val;
        j++;
        if tu_toks[j].kind as i64 == TK_LESS {
            // skip <...> (no nested parentheses needed in practice)
            var depth = 0;
            loop {
                let k = tu_toks[j].kind as i64;
                if k == TK_EOF || k == TK_SEMI || k == TK_L_BRACE { return false; }
                if k == TK_LESS { depth++; }
                if k == TK_GREATER { depth--; if depth == 0 { j++; break; } }
                if k == TK_GREATERGREATER { depth -= 2; if depth <= 0 { j++; break; } }
                if k == TK_L_PAREN {
                    var pd = 0;
                    loop {
                        let k2 = tu_toks[j].kind as i64;
                        if k2 == TK_EOF { return false; }
                        if k2 == TK_L_PAREN { pd++; }
                        if k2 == TK_R_PAREN { pd--; if pd == 0 { break; } }
                        j++;
                    }
                }
                j++;
            }
        }
        if tu_toks[j].kind as i64 == TK_COLONCOLON {
            prev = id;
            j++;
            continue;
        }
        last = id;
        break;
    }
    if prev == 0 || last != prev { return false; }
    return tu_toks[j].kind as i64 == TK_L_PAREN;
}

recursive fn parse_cds(ds: CDS&, a: Attrs&, ctx: i64) {
    ds.loc = tloc();
    loop {
        let k = tk();
        if k == TK_IDENT || k == TK_COLONCOLON || (k == TK_KW + KW_DECLTYPE) {
            if cds_has_type(ds) { break; }
            if k == TK_KW + KW_DECLTYPE {
                if decltype_then_cc() {
                    // decltype(x)::type
                } else {
                    ds.named = parse_decltype();
                    ds.nnamed++;
                    ds.any = true;
                    continue;
                }
            }
            if (ctx == DC_CLASS || ctx == DC_NS || ctx == DC_BLOCK) && at_ctor_name() { break; }
            // a type name?
            let sv = save();
            var qn = QN { .. };
            diag_suppress++;
            let ok = parse_qname(qn);
            diag_suppress--;
            if !ok || qn.kind as i64 != QK_IDENT { restore(sv); break; }
            lookup_qn(qn);
            var t = qn_type(qn);
            if t == 0 && qn.sym < 0 && qn.dep == 0 && !qn.has_targs && unknown_name_is_type(qn, ctx) { t = t_unknown; }
            if t == 0 || (qn.dep != 0 && !ds.typename_kw && !assume_type_after(qn) && !(ctx == DC_TYPEID && !truly_dep(qn.dep))) {
                restore(sv);
                break;
            }
            ds.named = t;
            ds.nnamed++;
            ds.any = true;
            continue;
        }
        if k < TK_KW {
            if at_attr_start() { cx_attrs(a); continue; }
            break;
        }
        let w = k - TK_KW;
        if w == KW_TYPEDEF || w == KW_EXTERN || w == KW_STATIC || w == KW_REGISTER || w == KW_MUTABLE {
            if w == KW_MUTABLE { ds.is_mutable = true; }
            else {
                ds.sc = match w { KW_TYPEDEF => SC_TYPEDEF, KW_EXTERN => SC_EXTERN, KW_STATIC => SC_STATIC, _ => SC_REGISTER };
                if w == KW_REGISTER { ds.sc = SC_NONE; }
                ds.has_sc = true;
            }
            ds.any = true;
            adv();
            if w == KW_EXTERN && at(TK_STRING) { adv(); }     // extern "C" int f();
            continue;
        }
        if w == KW_THREAD_LOCAL { ds.thread = true; ds.any = true; adv(); continue; }
        if w == KW_INLINE { ds.is_inline = true; ds.any = true; adv(); continue; }
        if w == KW_VIRTUAL { ds.is_virtual = true; ds.any = true; adv(); continue; }
        if w == KW_FRIEND { ds.is_friend = true; ds.any = true; adv(); continue; }
        if w == KW_EXPLICIT {
            ds.is_explicit = true;
            ds.any = true;
            adv();
            if at(TK_L_PAREN) { skip_group(); }
            continue;
        }
        if w == KW_CONSTEXPR || w == KW_CONSTEVAL || w == KW_CONSTINIT { ds.is_constexpr = true; ds.any = true; adv(); continue; }
        if w == KW_NORETURN { ds.noreturn = true; ds.any = true; adv(); continue; }
        if w == KW_CONST { ds.q = ds.q | Q_CONST; ds.any = true; adv(); continue; }
        if w == KW_VOLATILE { ds.q = ds.q | Q_VOLATILE; ds.any = true; adv(); continue; }
        if w == KW_RESTRICT { adv(); continue; }
        if w == KW_NULLABILITY || w == KW_UNALIGNED { adv(); continue; }
        if w == KW_ATOMIC {
            ds.any = true;
            adv();
            if at(TK_L_PAREN) {
                adv();
                let t = parse_type_id();
                expect(TK_R_PAREN, "')'");
                ds.named = with_quals(t, Q_ATOMIC);
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
        if w == KW_BOOLX || w == KW_BOOL { ds.nbool++; ds.any = true; adv(); continue; }
        if w == KW_WCHAR { ds.nwchar++; ds.any = true; adv(); continue; }
        if w == KW_CHAR8 { ds.nchar8++; ds.any = true; adv(); continue; }
        if w == KW_CHAR16 { ds.nchar16++; ds.any = true; adv(); continue; }
        if w == KW_CHAR32 { ds.nchar32++; ds.any = true; adv(); continue; }
        if w == KW_COMPLEX || w == KW_IMAGINARY { ds.ncomplex++; ds.any = true; adv(); continue; }
        if w == KW_INT128 { ds.nint128++; ds.any = true; adv(); continue; }
        if w == KW_FLOAT128 || w == KW_IBM128 { ds.nfloat128++; ds.any = true; adv(); continue; }
        if w == KW_FLOAT16 { ds.nfloat16++; ds.any = true; adv(); continue; }
        if w == KW_BF16 { ds.nbf16++; ds.any = true; adv(); continue; }
        if w == KW_AUTO || w == KW_AUTO_TYPE {
            if cds_has_type(ds) { break; }
            ds.nauto++;
            ds.any = true;
            adv();
            continue;
        }
        if w == KW_TYPENAME {
            if cds_has_type(ds) { break; }
            adv();
            ds.typename_kw = true;
            ds.any = true;
            let sv = save();
            var qn = QN { .. };
            if !parse_qname(qn) { restore(sv); break; }
            lookup_qn(qn);
            var t = qn_type(qn);
            if t == 0 {
                if qn.dep == 0 && qn.qual && qn.scope >= 0 {
                    // a member of a non-dependent class D1 does not know
                    t = t_unknown;
                } else if qn.dep == 0 {
                    t = t_unknown;
                }
            }
            ds.named = t;
            ds.nnamed++;
            ds.typename_kw = false;
            continue;
        }
        if w == KW_STRUCT || w == KW_UNION || w == KW_CLASS {
            if cds_has_type(ds) { break; }
            ds.any = true;
            ds.named = parse_class_spec(ds, w, ctx);
            ds.nnamed++;
            continue;
        }
        if w == KW_ENUM {
            if cds_has_type(ds) { break; }
            ds.any = true;
            ds.named = parse_enum_spec_cx(ds, ctx);
            ds.nnamed++;
            continue;
        }
        if w == KW_TYPEOF || w == KW_TYPEOF_UNQUAL {
            ds.any = true;
            adv();
            expect(TK_L_PAREN, "'('");
            var ty: u32 = t_unknown;
            if looks_like_type_id() && type_id_then(TK_R_PAREN, TK_R_PAREN) { ty = parse_type_id(); }
            else { let sp = paren_depth; paren_depth++; let e = parse_cexpr_full(); paren_depth = sp; ty = nonref(nodes[e].ty); }
            expect(TK_R_PAREN, "')'");
            if w == KW_TYPEOF_UNQUAL { ty = unqual(ty); }
            ds.named = ty;
            ds.nnamed++;
            continue;
        }
        if w == KW_TTRANS {
            if cds_has_type(ds) { break; }
            ds.any = true;
            ds.named = parse_type_transform();
            ds.nnamed++;
            continue;
        }
        if w == KW_ATTRIBUTE || w == KW_DECLSPEC || w == KW_ALIGNAS { cx_attrs(a); continue; }
        if w == KW_EXTENSION { adv(); continue; }
        if w == KW_EXPORT { adv(); continue; }
        break;
    }
}

// After `X::y` with a dependent qualifier and no `typename`: is it used as
// a type anyway? (C++20 allows it in some places; libstdc++ code compiled
// as C++17 always writes typename, so only the heuristics for opaque
// non-dependent qualifiers matter: X<int>::iterator it.)
fn assume_type_after(qn: QN&) -> bool {
    if dependent_ctx() { return false; }
    let k = tk();
    if k == TK_IDENT {
        let k1 = tk_n(1);
        return k1 == TK_SEMI || k1 == TK_EQUAL || k1 == TK_COMMA || k1 == TK_L_PAREN || k1 == TK_L_BRACE ||
            k1 == TK_L_SQUARE || k1 == TK_COLON || k1 == TK_R_PAREN;
    }
    if k == TK_STAR || k == TK_AMP || k == TK_AMPAMP {
        return tk_n(1) == TK_IDENT || tk_n(1) == TK_KW + KW_CONST;
    }
    if k == TK_KW + KW_CONST { return true; }
    return false;
}

// A name lookup did not find, in decl-specifier position: a type when the
// lookup could not be complete (a class with dependent or opaque bases, a
// template) and a declarator follows (X y; X *y; X &y; X y[).
var lenient: i64 = 0;       // > 0: names may belong to an opaque class (no undeclared-name errors)
fn unknown_name_is_type(qn: QN&, ctx: i64) -> bool {
    let incomplete = dependent_ctx() || lenient > 0 || (enclosing_class(cur_scope) >= 0 && has_dep_base(enclosing_class(cur_scope))) ||
        (qn.scope >= 0 && (scopes[qn.scope].flags & SCF_PATTERN != 0 || (scopes[qn.scope].kind as i64 == CS_CLASS && has_dep_base(qn.scope as i64))));
    if !incomplete { return false; }
    let k = tk();
    if k == TK_IDENT {
        let k1 = tk_n(1);
        return k1 == TK_SEMI || k1 == TK_EQUAL || k1 == TK_COMMA || k1 == TK_L_SQUARE || k1 == TK_R_PAREN ||
            k1 == TK_COLON || k1 == TK_L_BRACE || (k1 == TK_L_PAREN && ctx != DC_BLOCK);
    }
    if (k == TK_STAR || k == TK_AMP || k == TK_AMPAMP) && (ctx == DC_PARAM || ctx == DC_CLASS || ctx == DC_NS) { return true; }
    if k == TK_KW + KW_CONST && ctx != DC_BLOCK { return true; }
    if (k == TK_R_PAREN || k == TK_COMMA) && ctx == DC_PARAM { return true; }
    return false;
}

// Does t involve a template parameter (as opposed to an uninstantiated
// specialization with concrete arguments, which is only opaque)?
recursive fn truly_dep(t: u32) -> bool {
    let k = kind_of(t);
    if k == TY_TPARAM || k == TY_DEPEXPR || k == TY_PACKEXP { return true; }
    if k == TY_DEPNAME { return truly_dep(tbase(t)) || args_dependent_strict(types[t >> 4].n); }
    if k == TY_DEPSPEC { return args_dependent_strict(types[t >> 4].n); }
    if k == TY_POINTER || k == TY_LREF || k == TY_RREF || k == TY_ARRAY { return truly_dep(tbase(t)); }
    if k == TY_STRUCT || k == TY_UNION { return is_dep(t); }
    return false;
}

recursive fn args_dependent_strict(l: i64) -> bool {
    if l < 0 { return false; }
    let n = tl_count(l);
    for i in n {
        let a = tl_arg(l, i);
        if a.kind as i64 == TA_TYPE && truly_dep(a.ty) { return true; }
        if a.kind as i64 == TA_VALUE && a.ty != 0 && (kind_of(a.ty) == TY_TPARAM || kind_of(a.ty) == TY_PACKEXP || kind_of(a.ty) == TY_DEPEXPR) { return true; }
        if a.kind as i64 == TA_TEMPLATE && (a.v < 0 || cxs[a.v].flags & CF_TPARAM != 0) { return true; }
    }
    return false;
}

// The type the specifiers denote.
fn finish_cds(ds: CDS&) -> u32 {
    var t: u32 = 0;
    if ds.nnamed > 0 {
        t = ds.named;
    } else if ds.nauto > 0 {
        t = qt(mk_type(TY_AUTO, 0, 0, 0, 0, 0) as i64, 0);
    } else if ds.nvoid > 0 {
        t = t_void;
    } else if ds.nbool > 0 {
        t = t_bool;
    } else if ds.nwchar > 0 {
        t = t_wchar_cxx;
    } else if ds.nchar8 > 0 {
        t = t_char8;
    } else if ds.nchar16 > 0 {
        t = t_char16;
    } else if ds.nchar32 > 0 {
        t = t_char32;
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
    } else {
        // no type: constructors, destructors, conversion functions (the
        // declarator decides); implicit int is not C++
        t = 0;
    }
    if ds.ncomplex > 0 && t != 0 && (is_integer(t) || is_real_float(t)) { t = mk_complex(t); }
    if t == 0 { return 0; }
    if ds.q != 0 && !is_ref(t) { return with_quals(t, ds.q as i64); }
    return t;
}

// ---------------------------------------------------------------------------
// Declarators.

struct CD {
    ty: u32 = 0,
    qn: QN = QN { .. },
    has_name: bool = false,
    params: i64 = -1,       // the name's own function declarator: parameter symbols in nlist
    nparams: i64 = 0,
    fquals: u8 = 0,         // TF_MCONST ... of that function declarator
    noexcept: bool = false,
    pack: bool = false,     // a declarator-id after `...`
    is_fn: bool = false,
    loc: u32 = 0,
    pure: bool = false,
    deleted: bool = false,
    defaulted: bool = false,
    virt: u8 = 0,           // 1 override, 2 final
}

// Pointer operators: * & && X::* with their cv and attributes, applied to t.
recursive fn ptr_ops(t0: u32, d: CD&) -> u32 {
    var t = t0;
    loop {
        if at(TK_STAR) {
            adv();
            let q = cv_quals();
            t = with_q(mk_ptr(t), q);
            continue;
        }
        if at(TK_AMP) || at(TK_AMPAMP) {
            let rv = at(TK_AMPAMP);
            adv();
            var a = Attrs { .. };
            cx_attrs(a);
            let q = cv_quals();     // & __restrict
            t = if rv { mk_rref(t) } else { mk_lref(t) };
            continue;
        }
        if at(TK_CARET) { adv(); t = mk_ptr(t); continue; }     // blocks: not supported, parsed as pointers
        if (at(TK_IDENT) || at(TK_COLONCOLON)) && memptr_ahead() {
            // nested-name-specifier * : a pointer to member
            var qn = QN { .. };
            parse_nns(qn);
            expect(TK_STAR, "'*'");
            let q = cv_quals();
            var cls = t_unknown;
            if qn.scope >= 0 { let ct = scope_class_type(qn.scope as i64); if ct != 0 { cls = ct; } }
            else if qn.dep != 0 { cls = qn.dep; }
            t = with_q(mk_memptr(t, cls), q);
            continue;
        }
        break;
    }
    return t;
}

fn with_q(t: u32, q: i64) -> u32 { if q == 0 { return t; } return with_quals(t, q); }

fn cv_quals() -> i64 {
    var q = 0;
    loop {
        if at_kw(KW_CONST) { q = q | Q_CONST; adv(); continue; }
        if at_kw(KW_VOLATILE) { q = q | Q_VOLATILE; adv(); continue; }
        if at_kw(KW_RESTRICT) || at_kw(KW_NULLABILITY) || at_kw(KW_UNALIGNED) { adv(); continue; }
        if at_kw(KW_ATOMIC) && tk_n(1) != TK_L_PAREN { q = q | Q_ATOMIC; adv(); continue; }
        if at_kw(KW_ATTRIBUTE) { var a = Attrs { .. }; cx_attrs(a); continue; }
        break;
    }
    return q;
}

// Is there a nested-name-specifier followed by '*' at pc (X::* or X<T>::*)?
fn memptr_ahead() -> bool {
    var j = pc;
    if tu_toks[j].kind as i64 == TK_COLONCOLON { j++; }
    loop {
        if tu_toks[j].kind as i64 != TK_IDENT { return false; }
        j++;
        if tu_toks[j].kind as i64 == TK_LESS {
            var depth = 0;
            loop {
                let k = tu_toks[j].kind as i64;
                if k == TK_EOF || k == TK_SEMI || k == TK_L_BRACE || k == TK_R_BRACE { return false; }
                if k == TK_LESS { depth++; }
                if k == TK_GREATER { depth--; if depth == 0 { j++; break; } }
                if k == TK_GREATERGREATER { depth -= 2; if depth <= 0 { j++; break; } }
                j++;
            }
        }
        if tu_toks[j].kind as i64 != TK_COLONCOLON { return false; }
        j++;
        if tu_toks[j].kind as i64 == TK_STAR { return true; }
    }
}

// The declarator at pc (abstract: 0 a name required, 1 no name, 2 either),
// applied to the specifiers' type `base`: d.ty and the name in d.qn.
recursive fn parse_cdeclr(base: u32, abstract: i64, d: CD&) {
    d.loc = tloc();
    let t = ptr_ops(base, d);
    if accept(TK_ELLIPSIS) { d.pack = true; }
    if at(TK_L_PAREN) && paren_is_nested(abstract) {
        let open = pc;
        skip_group();
        var dummy = CD { .. };
        let outer = parse_csuffixes(t, dummy, false);
        let after = pc;
        let ag = gt_pos;
        pc = open + 1;
        parse_cdeclr(outer, abstract, d);
        if d.params < 0 && dummy.params >= 0 && d.ty == outer {
            // (f)(params): the parenthesized name is the function
            d.params = dummy.params;
            d.nparams = dummy.nparams;
            d.fquals = dummy.fquals;
            d.is_fn = true;
        }
        if !at(TK_R_PAREN) { perr_expected("')'"); }
        pc = after;
        gt_pos = ag;
        return;
    }
    if abstract != 1 && at_declarator_id() {
        parse_qname(d.qn);
        d.has_name = true;
        var a = Attrs { .. };
        cx_attrs(a);
        // after a qualified declarator-id, names are looked up in its scope
        let sv_scope = cur_scope;
        if d.qn.qual && d.qn.scope >= 0 { cur_scope = d.qn.scope as i64; }
        // a member of an opaque class: its names are unknown here
        if d.qn.qual && d.qn.dep != 0 { lenient++; }
        d.ty = parse_csuffixes(t, d, true);
        if d.qn.qual && d.qn.dep != 0 { lenient--; }
        cur_scope = sv_scope;
        return;
    }
    if abstract == 0 {
        perr_expected("a declarator");
    }
    d.ty = parse_csuffixes(t, d, true);
}

fn at_declarator_id() -> bool {
    let k = tk();
    if k == TK_IDENT || k == TK_COLONCOLON || k == TK_KW + KW_OPERATOR { return true; }
    if k == TK_TILDE && (tk_n(1) == TK_IDENT || tk_n(1) == TK_KW + KW_DECLTYPE) { return true; }
    return false;
}

// Is the '(' at pc a parenthesized declarator (vs. a parameter list or an
// initializer)?
recursive fn paren_is_nested(abstract: i64) -> bool {
    let k1 = tk_n(1);
    if abstract == 1 || abstract == 2 {
        // in a type-id or parameter: ( * ...) ( & ...) ( ^ ...) ( X::* ...) are nested
        if k1 == TK_STAR || k1 == TK_AMP || k1 == TK_AMPAMP || k1 == TK_CARET { return true; }
        if k1 == TK_ELLIPSIS { return tk_n(2) != TK_R_PAREN; }
        if k1 == TK_L_PAREN { return true; }
        if k1 == TK_IDENT || k1 == TK_COLONCOLON {
            let sv = save();
            adv();
            let mp = memptr_ahead();
            restore(sv);
            if mp { return true; }
            if abstract == 2 && k1 == TK_IDENT && !name_is_type_at(pc + 1) {
                return true;    // T (x): a parenthesized parameter name
            }
        }
        return false;
    }
    // a named declarator: ( *x ) ( &x ) ( x ) ( X::y )
    return true;
}

// Does the identifier at token i name a type or template (a quick check)?
fn name_is_type_at(i: i64) -> bool {
    let t = tu_toks[i];
    if t.kind as i64 != TK_IDENT { return t.kind as i64 >= TK_KW && is_type_kw(t.kind as i64 - TK_KW); }
    let s = chain_type(unqual_lookup(t.val));
    return s >= 0;
}

fn is_type_kw(w: i64) -> bool {
    return w == KW_CHAR || w == KW_CONST || w == KW_DOUBLE || w == KW_ENUM || w == KW_FLOAT || w == KW_INT ||
        w == KW_LONG || w == KW_SHORT || w == KW_SIGNED || w == KW_STRUCT || w == KW_UNION || w == KW_UNSIGNED ||
        w == KW_VOID || w == KW_VOLATILE || w == KW_BOOLX || w == KW_BOOL || w == KW_CLASS || w == KW_TYPENAME ||
        w == KW_WCHAR || w == KW_CHAR8 || w == KW_CHAR16 || w == KW_CHAR32 || w == KW_AUTO || w == KW_DECLTYPE ||
        w == KW_TYPEOF || w == KW_INT128 || w == KW_FLOAT128 || w == KW_FLOAT16 || w == KW_BF16 || w == KW_COMPLEX ||
        w == KW_ATOMIC || w == KW_TTRANS || w == KW_RESTRICT || w == KW_IBM128 || w == KW_AUTO_TYPE ||
        w == KW_TYPEOF_UNQUAL || w == KW_UNALIGNED || w == KW_NULLABILITY;
}

// Array and function suffixes (right to left); `first`: right after the
// declarator-id, whose function parameters are the name's.
recursive fn parse_csuffixes(base: u32, d: CD&, first: bool) -> u32 {
    if at(TK_L_SQUARE) && tk_n(1) != TK_L_SQUARE {
        adv();
        var n: i64 = -1;
        var dep = false;
        var vla: u32 = 0;
        if !at(TK_R_SQUARE) {
            let sp = paren_depth;
            paren_depth++;
            let e = parse_cexpr_full();
            paren_depth = sp;
            let ty = nodes[e].ty;
            if is_opaque(ty) { dep = true; }
            else {
                let ok, v = const_int(e);
                if ok { n = v; } else { dep = true; }
                // code generation: a VLA (GNU) in a function body
                if !ok && cg_on && block_fn_depth > 0 && !dependent_ctx() && cish_node(e) && is_integer(nodes[e].ty) { vla = rv(e); }
            }
        }
        expect(TK_R_SQUARE, "']'");
        var a = Attrs { .. };
        cx_attrs(a);
        let inner = parse_csuffixes(base, d, false);
        if vla != 0 && !is_opaque(inner) && cish(inner) { return mk_vla(inner, vla as i64); }
        if dep || is_opaque(inner) {
            // a dependent bound, one D1 does not evaluate, or a VLA (a GNU
            // extension the corpora do not use in C++): opaque
            return t_unknown;
        }
        return mk_array(inner, n);
    }
    if at(TK_L_PAREN) {
        if first && d.has_name && init_ok && !looks_like_params() {
            // T x(args): a direct-initializer, not a parameter list
            return base;
        }
        var variadic = false;
        let start, count = parse_cparams(variadic);
        // cv-qualifiers, ref-qualifier, exception specification, attributes
        var fq: i64 = 0;
        loop {
            if at_kw(KW_CONST) { fq = fq | TF_MCONST; adv(); continue; }
            if at_kw(KW_VOLATILE) { fq = fq | TF_MVOLATILE; adv(); continue; }
            if at_kw(KW_RESTRICT) { adv(); continue; }
            break;
        }
        if at(TK_AMP) { fq = fq | TF_MLREF; adv(); }
        else if at(TK_AMPAMP) { fq = fq | TF_MRREF; adv(); }
        var noexc = false;
        loop {
            if at_kw(KW_NOEXCEPT) {
                adv();
                noexc = true;
                if at(TK_L_PAREN) { skip_group(); }
                continue;
            }
            if at_kw(KW_THROW) {
                adv();
                if at(TK_L_PAREN) {
                    noexc = tk_n(1) == TK_R_PAREN;
                    skip_group();
                }
                continue;
            }
            if at_attr_start() { var a = Attrs { .. }; cx_attrs(a); continue; }
            break;
        }
        var ret = base;
        if at(TK_ARROW) {
            // a trailing return type (the specifiers said auto)
            adv();
            ret = parse_type_id();
        } else {
            ret = parse_csuffixes(base, d, false);
        }
        if first {
            d.params = start;
            d.nparams = count;
            d.fquals = fq as! u8;
            d.noexcept = noexc;
            d.is_fn = true;
        }
        fn_scratch.clear();
        var dep = is_opaque(ret);
        for i in count {
            let pt = syms[nlist[start + i]].ty;
            fn_scratch.push(unqual_param(pt));
        }
        var fl = fq;
        if variadic { fl = fl | TF_VARIADIC; }
        let ft = qt(mk_type(TY_FUNC, fl, if ret == 0 { t_void } else { unqual_ret(ret) }, 0, 0, 0) as i64, 0);
        return ft;
    }
    return base;
}

// Can a declarator's '(' start an initializer here (namespace or block
// scope, a condition)? Set by parse_simple_decl.
var init_ok: bool = false;

// At '(' after a declarator-id: a parameter-declaration-clause (vs. an
// expression list)? C++ [dcl.ambig.res]: what can be a parameter list is
// one (T x(); declares a function).
recursive fn looks_like_params() -> bool {
    let k1 = tk_n(1);
    if k1 == TK_R_PAREN || k1 == TK_ELLIPSIS { return true; }
    if k1 >= TK_KW {
        let w = k1 - TK_KW;
        if w == KW_REGISTER || w == KW_CONST || w == KW_VOLATILE || w == KW_TYPENAME || w == KW_STRUCT || w == KW_CLASS ||
           w == KW_UNION || w == KW_ENUM || w == KW_ATTRIBUTE || w == KW_AUTO { return true; }
        if w == KW_DECLTYPE || w == KW_TYPEOF || w == KW_TYPEOF_UNQUAL || w == KW_TTRANS || w == KW_ATOMIC { return true; }
        if is_type_kw(w) {
            // int(3) is an expression; int, int x, int* and int (*f)(...) are parameters
            let k2 = tk_n(2);
            if k2 == TK_L_PAREN {
                let k3 = tk_n(3);
                if k3 == TK_STAR || k3 == TK_AMP || k3 == TK_AMPAMP || k3 == TK_CARET || k3 == TK_R_PAREN ||
                    (k3 >= TK_KW && is_type_kw(k3 - TK_KW)) { return true; }
                // int (X::*pm)
                let sv = save();
                adv(); adv(); adv();
                let mp = memptr_ahead();
                restore(sv);
                return mp;
            }
            return true;
        }
        return false;
    }
    if k1 == TK_L_SQUARE && tk_n(2) == TK_L_SQUARE { return true; }
    if k1 != TK_IDENT && k1 != TK_COLONCOLON { return false; }
    let sv = save();
    adv();
    let r = looks_like_type_id();
    restore(sv);
    return r;
}

// Is the type-id at pc followed by token k1 or k2 (a tentative parse)?
recursive fn type_id_then(k1: i64, k2: i64) -> bool {
    let sv = save();
    diag_suppress++;
    let t = parse_type_id();
    diag_suppress--;
    let r = at(k1) || at(k2) || at(TK_ELLIPSIS);
    restore(sv);
    return r;
}

// ... followed by the end of a template argument (',' '>' '>>' '...').
recursive fn type_id_then_gt() -> bool {
    let sv = save();
    diag_suppress++;
    let t = parse_type_id();
    diag_suppress--;
    let r = at(TK_COMMA) || at_gt() || at(TK_ELLIPSIS);
    restore(sv);
    return r;
}

// The parameter type as part of the function type: top-level cv removed.
fn unqual_param(t: u32) -> u32 { if is_ref(t) { return t; } return unqual(t); }
fn unqual_ret(t: u32) -> u32 { if is_record(t) || is_ref(t) || is_opaque(t) { return t; } return unqual(t); }

// ( parameter-declaration-clause ): the parameter symbols (in nlist).
recursive fn parse_cparams(variadic: bool&) -> i64, i64 {
    adv();      // (
    push_scope();
    let mark = nscratch.len;
    if at_kw(KW_VOID) && tk_n(1) == TK_R_PAREN {
        adv();
    } else {
        loop {
            if at(TK_R_PAREN) || at(TK_EOF) { break; }
            if at(TK_ELLIPSIS) { adv(); variadic = true; break; }
            var ds = CDS { .. };
            var pa = Attrs { .. };
            cx_attrs(pa);
            parse_cds(ds, pa, DC_PARAM);
            if !ds.any {
                perr_expected("a parameter declaration");
                skip_to(TK_R_PAREN);
                break;
            }
            var base = finish_cds(ds);
            if base == 0 { base = t_int; }
            var d = CD { .. };
            parse_cdeclr(base, 2, d);
            cx_attrs(pa);
            var ty = d.ty;
            if d.pack { ty = mk_packexp(ty); }
            // adjustments: arrays and functions to pointers
            if is_array(ty) { ty = mk_ptr(tbase(ty)); }
            else if is_func(ty) { ty = mk_ptr(ty); }
            let s = csym(SK_VAR, d.qn.name, ty, d.loc);
            syms[s].flags = SF_PARAM;
            if at(TK_EQUAL) {
                // a default argument: its tokens (parsed where a call needs it)
                adv();
                cxs[s].body = pc as! u32;
                skip_expr();
                cxs[s].body_end = pc as! u32;
            }
            if d.qn.name != 0 { bind_sym(s, false); }
            nscratch.push(s as! u32);
            if accept(TK_ELLIPSIS) { variadic = true; break; }     // int, ...  written without the comma
            if !accept(TK_COMMA) { break; }
        }
    }
    expect(TK_R_PAREN, "')'");
    pop_scope();
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    return start, count;
}

// Skips an assignment-expression (a default argument, a default member
// initializer, a template default): to ',' ')' ';' '>' at depth 0. A '<'
// after a template name opens a group.
recursive fn skip_expr() {
    diag_suppress++;
    let e = parse_assign_cx();
    diag_suppress--;
}

// A type-id (C++ [dcl.name]).
recursive fn parse_type_id() -> u32 {
    var ds = CDS { .. };
    var a = Attrs { .. };
    parse_cds(ds, a, DC_TYPEID);
    if !ds.any {
        perr_expected("a type");
        return t_unknown;
    }
    var base = finish_cds(ds);
    if base == 0 { base = t_int; }
    var d = CD { .. };
    parse_cdeclr(base, 1, d);
    var t = d.ty;
    if d.pack { t = mk_packexp(t); }
    return apply_type_attrs(t, a, ds.loc);
}

// The type of a conversion-function-id: type-specifiers and ptr-operators.
recursive fn parse_conv_type() -> u32 {
    var ds = CDS { .. };
    var a = Attrs { .. };
    parse_cds(ds, a, DC_TYPEID);
    var base = finish_cds(ds);
    if base == 0 { base = t_unknown; }
    var d = CD { .. };
    return ptr_ops(base, d);
}

// decltype ( expression ) / decltype(auto) at pc.
recursive fn parse_decltype() -> u32 {
    let t0 = pc;
    adv();
    expect(TK_L_PAREN, "'('");
    if at_kw(KW_AUTO) && tk_n(1) == TK_R_PAREN {
        adv();
        adv();
        return qt(mk_type(TY_AUTO, 0, 0, 1, 0, 0) as i64, 0);
    }
    unevaluated++;
    let sp = paren_depth;
    paren_depth++;
    let e = parse_cexpr_full();
    paren_depth = sp;
    unevaluated--;
    expect(TK_R_PAREN, "')'");
    let ty = nodes[e].ty;
    if is_opaque(ty) || ty == 0 { return if dependent_ctx() { mk_depexpr(t0) } else { t_unknown }; }
    // decltype(id) is the declared type; decltype(expr) adds & for lvalues,
    // && for xvalues
    if decltype_is_id(e) { return ty_decl_of(e); }
    if is_lvalue(e) { return mk_lref(ty); }
    if nodes[e].flags & NF_XVALUE != 0 { return mk_rref(ty); }
    return ty;
}
var unevaluated: i64 = 0;

// A type transform (__remove_cv(T) ...).
recursive fn parse_type_transform() -> u32 {
    let name = ident_text(tu_toks[pc].val as i64);
    adv();
    expect(TK_L_PAREN, "'('");
    let t = parse_type_id();
    expect(TK_R_PAREN, "')'");
    if is_opaque(t) { return t_unknown; }
    if name == "__remove_cv" { return unqual(t); }
    if name == "__remove_const" { return t & ~(Q_CONST as! u32); }
    if name == "__remove_volatile" { return t & ~(Q_VOLATILE as! u32); }
    if name == "__remove_reference_t" { return nonref(t); }
    if name == "__remove_cvref" { return unqual(nonref(t)); }
    if name == "__add_pointer" { if is_func(t) && types[t >> 4].flags & (TF_MCONST | TF_MVOLATILE | TF_MLREF | TF_MRREF) != 0 { return t; } return mk_ptr(nonref(t)); }
    if name == "__add_lvalue_reference" { if is_void(t) { return t; } return mk_lref(t); }
    if name == "__add_rvalue_reference" { if is_void(t) { return t; } return mk_rref(t); }
    if name == "__remove_pointer" { if is_pointer(t) { return tbase(t); } return t; }
    if name == "__remove_extent" { if is_array(t) { return tbase(t); } return t; }
    if name == "__remove_all_extents" { var x = t; while is_array(x) { x = tbase(x); } return x; }
    if name == "__decay" {
        let u = unqual(nonref(t));
        if is_array(u) { return mk_ptr(tbase(u)); }
        if is_func(u) { return mk_ptr(u); }
        return u;
    }
    if name == "__underlying_type" {
        if kind_of(t) == TY_ENUM { return enum_underlying(t); }
        return t_unknown;
    }
    if name == "__make_signed" { if is_integer(t) { return with_q(signed_of(enum_or_int(t)), quals(t)); } return t_unknown; }
    if name == "__make_unsigned" { if is_integer(t) { return with_q(unsigned_of(enum_or_int(t)), quals(t)); } return t_unknown; }
    return t_unknown;
}

fn enum_or_int(t: u32) -> u32 {
    if kind_of(t) == TY_ENUM { return enum_underlying(t); }
    if kind_of(t) == TY_BOOL || kind_of(t) == TY_CHAR { return t_schar; }
    return unqual(t);
}
