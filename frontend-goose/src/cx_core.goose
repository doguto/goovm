// goosecc D1: the C++ front end's core. Keywords, scopes and name lookup,
// the per-symbol C++ facts, template records and dependent types.
//
// The C++ parser (cx_*.goose, namespace cx) shares the C front end's
// tokens, types, symbols and nodes (DESIGN.md 13). What C++ adds lives in
// side tables indexed like the shared ones:
//
//   scopes   namespaces, classes, scoped enums: persistent, so that
//            qualified names reach them and namespaces reopen;
//   nmap     (scope << 32 | identifier) -> the newest symbol of that name
//            declared in that scope; older ones follow cxs[s].nnext
//            (overloads, a class and a function of one name);
//   cxs      per symbol: declaring scope, access, C++ flags, template
//            record, the token position of the declaration (two-phase
//            lookup), the target of a using-declaration;
//   crecs    per record: bases, dynamic class facts, special members.
//
// Block scopes stay C's (id_bind with shadow chains, push_scope /
// pop_scope): unqualified lookup looks there first, above `local_floor`,
// then walks the scope chain (cur_scope) outwards.

namespace cx;

import std;
import dictionary;
import .common;
import .types;
import .ast;
import .sema;
import .pp;
import .ppexpr;

// ---------------------------------------------------------------------------
// Keywords. The C codes (sema.goose) are reused where C++ means the same;
// the C++ ones follow KW_LAST. Type traits keep their identifier in the
// token's val.

let KW_BOOLX = 70;          // bool
let KW_CLASS = 71;
let KW_NAMESPACE = 72;
let KW_TEMPLATE = 73;
let KW_TYPENAME = 74;
let KW_USING = 75;
let KW_PUBLIC = 76;
let KW_PRIVATE = 77;
let KW_PROTECTED = 78;
let KW_VIRTUAL = 79;
let KW_EXPLICIT = 80;
let KW_FRIEND = 81;
let KW_MUTABLE = 82;
let KW_OPERATOR = 83;
let KW_THIS = 84;
let KW_NEW = 85;
let KW_DELETE = 86;
let KW_TRUE = 87;
let KW_FALSE = 88;
let KW_NULLPTR = 89;
let KW_TRY = 90;
let KW_CATCH = 91;
let KW_THROW = 92;
let KW_CONSTEXPR = 93;
let KW_CONSTEVAL = 94;
let KW_CONSTINIT = 95;
let KW_DECLTYPE = 96;
let KW_NOEXCEPT = 97;
let KW_STATIC_CAST = 98;
let KW_DYNAMIC_CAST = 99;
let KW_REINTERPRET_CAST = 100;
let KW_CONST_CAST = 101;
let KW_TYPEID = 102;
let KW_WCHAR = 103;
let KW_CHAR8 = 104;
let KW_CHAR16 = 105;
let KW_CHAR32 = 106;
let KW_EXPORT = 107;
let KW_CONCEPT = 108;
let KW_REQUIRES = 109;
let KW_TRAIT = 110;         // __is_class(T) ...: an expression; val = the trait's identifier
let KW_TTRANS = 111;        // __remove_cv(T) ...: a type; val = the transform's identifier
let KW_NULL_GNU = 112;      // __null
let KW_CO = 113;            // co_await co_return co_yield (C++20, not supported)
let KW_BUILTIN_X = 114;     // __builtin_FILE() ... __builtin_source_location()
let KW_CXXOP = 155;         // the alternative tokens: tu_add gives them their operators' kinds

fn kwset(name: const u8[:], k: i64) {
    let id = intern(name);
    idents[id].kw = k as! u16;
}

// The keyword table of C++ mode (main.goose calls it instead of
// keywords_init): clang++'s keywords for the standard, the type traits
// from the generated list of words that are not identifiers.
fn keywords_init_cxx() {
    let s11 = opt_cxx_std >= 11;
    kwset("auto", KW_AUTO); kwset("break", KW_BREAK); kwset("case", KW_CASE); kwset("char", KW_CHAR);
    kwset("const", KW_CONST); kwset("__const", KW_CONST); kwset("__const__", KW_CONST);
    kwset("continue", KW_CONTINUE); kwset("default", KW_DEFAULT); kwset("do", KW_DO);
    kwset("double", KW_DOUBLE); kwset("else", KW_ELSE); kwset("enum", KW_ENUM); kwset("extern", KW_EXTERN);
    kwset("float", KW_FLOAT); kwset("for", KW_FOR); kwset("goto", KW_GOTO); kwset("if", KW_IF);
    kwset("inline", KW_INLINE); kwset("__inline", KW_INLINE); kwset("__inline__", KW_INLINE);
    kwset("int", KW_INT); kwset("long", KW_LONG); kwset("register", KW_REGISTER);
    kwset("__restrict", KW_RESTRICT); kwset("__restrict__", KW_RESTRICT);
    kwset("return", KW_RETURN); kwset("short", KW_SHORT); kwset("signed", KW_SIGNED);
    kwset("__signed", KW_SIGNED); kwset("__signed__", KW_SIGNED); kwset("sizeof", KW_SIZEOF);
    kwset("static", KW_STATIC); kwset("struct", KW_STRUCT); kwset("switch", KW_SWITCH);
    kwset("typedef", KW_TYPEDEF); kwset("union", KW_UNION); kwset("unsigned", KW_UNSIGNED);
    kwset("void", KW_VOID); kwset("volatile", KW_VOLATILE); kwset("__volatile", KW_VOLATILE);
    kwset("__volatile__", KW_VOLATILE); kwset("while", KW_WHILE);
    kwset("_Alignas", KW_ALIGNAS); kwset("_Alignof", KW_ALIGNOF); kwset("__alignof", KW_ALIGNOF);
    kwset("__alignof__", KW_ALIGNOF); kwset("_Atomic", KW_ATOMIC); kwset("_Complex", KW_COMPLEX);
    kwset("__complex", KW_COMPLEX); kwset("__complex__", KW_COMPLEX); kwset("_Generic", KW_GENERIC);
    kwset("_Imaginary", KW_IMAGINARY); kwset("_Noreturn", KW_NORETURN); kwset("_Static_assert", KW_STATIC_ASSERT);
    kwset("_Thread_local", KW_THREAD_LOCAL); kwset("__thread", KW_THREAD_LOCAL);
    kwset("__attribute__", KW_ATTRIBUTE); kwset("__attribute", KW_ATTRIBUTE); kwset("__extension__", KW_EXTENSION);
    kwset("asm", KW_ASM); kwset("__asm", KW_ASM); kwset("__asm__", KW_ASM);
    if opt_gnu { kwset("typeof", KW_TYPEOF); }
    kwset("__typeof", KW_TYPEOF); kwset("__typeof__", KW_TYPEOF);
    kwset("__typeof_unqual", KW_TYPEOF_UNQUAL); kwset("__typeof_unqual__", KW_TYPEOF_UNQUAL);
    kwset("__label__", KW_LABEL); kwset("__real", KW_REAL); kwset("__real__", KW_REAL);
    kwset("__imag", KW_IMAG); kwset("__imag__", KW_IMAG); kwset("__builtin_va_arg", KW_VA_ARG);
    kwset("__builtin_offsetof", KW_OFFSETOF);
    kwset("__builtin_choose_expr", KW_CHOOSE_EXPR); kwset("__int128", KW_INT128);
    kwset("__float128", KW_FLOAT128); kwset("_Float16", KW_FLOAT16); kwset("__bf16", KW_BF16);
    kwset("__auto_type", KW_AUTO_TYPE); kwset("__func__", KW_FUNC); kwset("__FUNCTION__", KW_FUNC);
    kwset("__PRETTY_FUNCTION__", KW_FUNC); kwset("_Nonnull", KW_NULLABILITY); kwset("_Nullable", KW_NULLABILITY);
    kwset("_Null_unspecified", KW_NULLABILITY); kwset("_Nullable_result", KW_NULLABILITY);
    kwset("__builtin_convertvector", KW_CONVERTVECTOR); kwset("__builtin_bit_cast", KW_BITCAST);
    kwset("__unaligned", KW_UNALIGNED); kwset("__ibm128", KW_IBM128);
    kwset("__declspec", KW_DECLSPEC);
    // C++
    kwset("bool", KW_BOOLX); kwset("class", KW_CLASS); kwset("namespace", KW_NAMESPACE);
    kwset("template", KW_TEMPLATE); kwset("typename", KW_TYPENAME); kwset("using", KW_USING);
    kwset("public", KW_PUBLIC); kwset("private", KW_PRIVATE); kwset("protected", KW_PROTECTED);
    kwset("virtual", KW_VIRTUAL); kwset("explicit", KW_EXPLICIT); kwset("friend", KW_FRIEND);
    kwset("mutable", KW_MUTABLE); kwset("operator", KW_OPERATOR); kwset("this", KW_THIS);
    kwset("new", KW_NEW); kwset("delete", KW_DELETE); kwset("true", KW_TRUE); kwset("false", KW_FALSE);
    kwset("try", KW_TRY); kwset("catch", KW_CATCH); kwset("throw", KW_THROW);
    kwset("static_cast", KW_STATIC_CAST); kwset("dynamic_cast", KW_DYNAMIC_CAST);
    kwset("reinterpret_cast", KW_REINTERPRET_CAST); kwset("const_cast", KW_CONST_CAST);
    kwset("typeid", KW_TYPEID); kwset("wchar_t", KW_WCHAR); kwset("export", KW_EXPORT);
    kwset("__null", KW_NULL_GNU); kwset("__decltype", KW_DECLTYPE); kwset("__nullptr", KW_NULLPTR);
    kwset("__char16_t", KW_CHAR16); kwset("__char32_t", KW_CHAR32);
    if s11 {
        kwset("constexpr", KW_CONSTEXPR); kwset("decltype", KW_DECLTYPE); kwset("noexcept", KW_NOEXCEPT);
        kwset("nullptr", KW_NULLPTR); kwset("static_assert", KW_STATIC_ASSERT); kwset("thread_local", KW_THREAD_LOCAL);
        kwset("alignas", KW_ALIGNAS); kwset("alignof", KW_ALIGNOF); kwset("char16_t", KW_CHAR16);
        kwset("char32_t", KW_CHAR32);
    }
    if opt_cxx_std >= 20 {
        kwset("char8_t", KW_CHAR8); kwset("consteval", KW_CONSTEVAL); kwset("constinit", KW_CONSTINIT);
        kwset("concept", KW_CONCEPT); kwset("requires", KW_REQUIRES);
        kwset("co_await", KW_CO); kwset("co_return", KW_CO); kwset("co_yield", KW_CO);
    }
    for b in ["__builtin_FILE", "__builtin_FILE_NAME", "__builtin_FUNCTION", "__builtin_LINE", "__builtin_COLUMN",
              "__builtin_source_location"] { kwset(b, KW_BUILTIN_X); }
    // the type traits and type transforms clang++ knows
    let text = CXX_KEYWORDS;
    var i = 0;
    while i < text.len {
        var j = i;
        while j < text.len && text[j] != ' ' && text[j] != '\n' { j++; }
        let w = text[i..j];
        while j < text.len && text[j] != '\n' { j++; }
        i = j + 1;
        if w.len > 5 && w[0] == '_' && w[1] == '_' {
            let tt = is_type_transform(w);
            let tr = !tt && (starts_with(w, "__is_") || starts_with(w, "__has_") || w == "__array_rank" ||
                w == "__array_extent" || w == "__reference_binds_to_temporary" || w == "__reference_constructs_from_temporary" ||
                w == "__reference_converts_from_temporary" || w == "__can_pass_in_regs" || w == "__builtin_is_implicit_lifetime" ||
                w == "__builtin_is_virtual_base_of" || w == "__datasizeof");
            if tt { kwset(w, KW_TTRANS); } else if tr { kwset(w, KW_TRAIT); }
        }
    }
    for o in cxxops {
        if idents[o].flags & ID_CXXOP != 0 { idents[o].kw = KW_CXXOP; }
    }
}

fn is_type_transform(w: const u8[:]) -> bool {
    return w == "__add_lvalue_reference" || w == "__add_pointer" || w == "__add_rvalue_reference" || w == "__decay" ||
        w == "__make_signed" || w == "__make_unsigned" || w == "__remove_all_extents" || w == "__remove_const" ||
        w == "__remove_cv" || w == "__remove_cvref" || w == "__remove_extent" || w == "__remove_pointer" ||
        w == "__remove_reference_t" || w == "__remove_restrict" || w == "__remove_volatile" || w == "__underlying_type";
}

// ---------------------------------------------------------------------------
// Scopes.

let CS_NS = 1;
let CS_CLASS = 2;
let CS_ENUM = 3;        // a scoped enum (its enumerators)
let CS_BLOCK = 4;       // the parent of a local class: a function body
let SCF_INLINE = 1;     // an inline namespace
let SCF_PATTERN = 2;    // a class template's pattern, or nested in one: dependent
let SCF_ANON = 4;       // an unnamed namespace

struct Scope {
    kind: u8,
    flags: u8,
    rsv: u16,
    parent: i32,        // the enclosing scope (-1 for the global namespace)
    sym: i32,           // the namespace, class or enum symbol (-1: the global namespace)
    name: u32,
    using_ns: i32,      // using-directives in it: a list in ulinks
    inl: i32,           // inline namespaces in it: a list in ulinks
    rec: i32,           // classes: the record
}
var scopes: Scope[>..] = [];
struct Link { v: i32, next: i32 }
var ulinks: Link[>..] = [];

var cur_scope: i64 = 0;         // where declarations go and lookups start
var nmap = dictionary<u64, i32> {};

fn new_scope(kind: i64, parent: i64, sym: i64, name: u32) -> i64 {
    let s = scopes.len;
    scopes.push(Scope { kind: kind as! u8, flags: 0, rsv: 0, parent: parent as! i32, sym: sym as! i32, name: name,
        using_ns: -1, inl: -1, rec: -1 });
    if parent >= 0 && scopes[parent].flags & SCF_PATTERN != 0 { scopes[s].flags = SCF_PATTERN; }
    return s;
}

fn link_add(head: i32, v: i64) -> i32 {
    let l = ulinks.len;
    ulinks.push(Link { v: v as! i32, next: head });
    return l as! i32;
}

// ---------------------------------------------------------------------------
// The C++ facts of a symbol (cxs[s], grown with syms).

let CF_MEMBER = 1;          // a class member (data member, member function, static member)
let CF_STATIC = 2;          // a static member
let CF_VIRTUAL = 4;
let CF_PURE = 8;
let CF_CONST = 16;          // const member function
let CF_CTOR = 32;
let CF_DTOR = 64;
let CF_CONV = 128;          // conversion function
let CF_OPERATOR = 256;      // operator function (cxs[s].op)
let CF_EXPLICIT = 512;
let CF_DELETED = 1024;
let CF_DEFAULTED = 2048;
let CF_CONSTEXPR = 4096;
let CF_TEMPLATE = 8192;     // a template (cxs[s].tmpl is its record)
let CF_PATTERN = 16384;     // declared in a template pattern: dependent, never emitted
let CF_EXTERN_C = 32768;    // extern "C" linkage
let CF_IMPLICIT = 65536;    // an implicitly declared special member
let CF_INJECTED = 131072;   // the injected-class-name
let CF_SPEC = 262144;       // an instantiation or explicit specialization (cxs[s].tmpl: its template)
let CF_TPARAM = 524288;     // a template parameter
let CF_MUTABLE = 1048576;
let CF_FRIEND = 2097152;    // declared by a friend declaration only
let CF_INLINE_NS = 4194304; // a namespace symbol that is an inline namespace
let CF_NOEXCEPT = 8388608;
let CF_OVERRIDE = 16777216;
let CF_FINAL = 33554432;
let CF_DEFINED_IN_CLASS = 67108864;  // a member function defined in its class (implicitly inline)
let CF_HAS_BODY_LATER = 134217728;   // the body is parsed after the class is complete

let AC_PUBLIC = 0;
let AC_PROTECTED = 1;
let AC_PRIVATE = 2;

struct CxSym {
    dscope: i32,        // the scope it is declared in
    nnext: i32,         // the next older symbol of the same name in that scope
    flags: u32,
    access: u8,
    op: u8,             // operator functions: the operator (OP_*)
    rsv: u16,
    tmpl: i32,          // a template: its record; an instantiation: its template's record
    pos: u32,           // the token index of the declaration
    target: i32,        // SK_USING: the symbol it names; an injected-class-name: the class
    vidx: i32,          // a virtual function: its vtable slot
    body: u32,          // a member function's body / default member initializer: first token (0: none)
    body_end: u32,
    mname: u32,         // the mangled name (offset in names, 0: not computed)
    mlen: u32,
    targs: i32,         // an instantiation's template arguments (a list in targs)
}
var cxs: CxSym[>..] = [];

fn cx_grow() {
    while cxs.len < syms.len {
        cxs.push(CxSym { dscope: -1, nnext: -1, flags: 0, access: 0, op: 0, rsv: 0, tmpl: -1, pos: 0, target: -1,
            vidx: -1, body: 0, body_end: 0, mname: 0, mlen: 0, targs: -1 });
    }
}

// More symbol kinds (ast.goose has 1..7).
let SK_NAMESPACE = 20;      // v = its scope
let SK_TEMPLATE = 21;       // cxs[s].tmpl: the template record
let SK_USING = 22;          // a using-declaration's introduced name: cxs[s].target
let SK_FIELD = 23;          // a non-static data member: v = field index; ty = its type
let SK_NTTP = 24;           // a non-type template parameter: ty, v = depth << 16 | index
let SK_NSALIAS = 25;        // namespace alias: v = the scope

fn csym(kind: i64, name: u32, ty: u32, loc: u32) -> i64 {
    let s = new_sym(kind, name, ty, loc);
    cx_grow();
    cxs[s].pos = pc as! u32;
    return s;
}

// Declares symbol s in scope sc (namespace, class or enum).
fn scope_add(sc: i64, s: i64) {
    cx_grow();
    cxs[s].dscope = sc as! i32;
    let name = syms[s].name;
    if name == 0 { return; }
    let key = ((sc as u64) << 32) | (name as u64);
    let g = nmap.get(key);
    if g { cxs[s].nnext = g; }
    nmap.insert(key, s as! i32);
}

// The newest symbol named `name` declared in scope sc, or -1.
fn scope_find(sc: i64, name: u32) -> i64 {
    let g = nmap.get(((sc as u64) << 32) | (name as u64));
    if g { return g as i64; }
    return -1;
}

// ---------------------------------------------------------------------------
// C++ records (crecs[r], grown with records).

let CR_DYNAMIC = 1;         // has a vtable pointer (virtual functions or virtual bases)
let CR_POLY = 2;            // polymorphic (virtual functions)
let CR_ABSTRACT = 4;
let CR_HAS_VBASE = 8;
let CR_USER_CTOR = 16;      // a user-declared constructor
let CR_USER_DTOR = 32;
let CR_NONTRIVIAL_DTOR = 64;
let CR_NONTRIVIAL_DEFCTOR = 128;
let CR_NONTRIVIAL_COPY = 256;
let CR_NOT_POD = 512;       // not POD for the purpose of layout (Itanium: tail padding reuse)
let CR_EMPTY = 1024;
let CR_PATTERN = 2048;      // a class template's pattern
let CR_LAYOUT = 4096;       // laid out
let CR_CLASS_KW = 8192;     // declared with `class` (default access private)
let CR_HAS_USER_COPY = 16384;
let CR_NOT_AGGREGATE = 32768;
let CR_DEFAULTED_CTOR = 65536;
let CR_STD_LAYOUT_NO = 131072;
let CR_HAS_MOVE = 262144;

struct Base { ty: u32, flags: u8, access: u8, rsv: u16, offset: i64 }
let BF_VIRTUAL = 1;
let BF_PRIMARY = 2;

struct CxRec {
    sym: i32,
    scope: i32,         // the class scope
    bases: u32,         // first in cbases
    nbases: u32,
    flags: u32,
    dsize: i64,         // data size (without tail padding)
    nvsize: i64,        // non-virtual size and alignment
    nvalign: i64,
    primary: i32,       // the primary base's record, -1
    vfirst: u32,        // the virtual functions declared or overridden, in vtable order (vslots)
    nvirt: u32,
    nfields: u32,       // fields of its own (records[r] counts them too)
}
var crecs: CxRec[>..] = [];
var cbases: Base[>..] = [];

fn crec_grow() {
    while crecs.len < records.len {
        crecs.push(CxRec { sym: -1, scope: -1, bases: 0, nbases: 0, flags: 0, dsize: 0, nvsize: 0, nvalign: 1, primary: -1,
            vfirst: 0, nvirt: 0, nfields: 0 });
    }
}

// ---------------------------------------------------------------------------
// Templates.

let TT_CLASS = 1;
let TT_FUNC = 2;
let TT_ALIAS = 3;
let TT_VAR = 4;
let TT_PARAM = 5;           // a template template parameter

let TPK_TYPE = 1;
let TPK_VALUE = 2;
let TPK_TEMPLATE = 3;

struct TParam {
    kind: u8,
    pack: bool,
    rsv: u16,
    name: u32,
    ty: u32,                // TPK_VALUE: its type (maybe dependent)
    def0: u32,              // the default argument's tokens (0: none)
    def1: u32,
    sym: i32,               // the parameter's symbol in the pattern
}
var tps: TParam[>..] = [];

struct Tmpl {
    kind: u8,
    depth: u8,              // template depth of its own parameters (1 + enclosing templates)
    rsv: u16,
    sym: i32,               // the template's symbol
    params: u32,            // first in tps
    nparams: u32,
    scope: i32,             // the scope of its definition (declarations go there)
    pos: u32,               // its point of definition (token index of the first `template`)
    t0: u32,                // the declaration after the template header: tokens [t0, t1)
    t1: u32,
    pattern: i32,           // TT_CLASS: the pattern's record; -1 not defined (yet)
    specs: i32,             // partial specializations (a list in ulinks of Tmpl indices)
    outer: i32,             // the enclosing class template's record when it is a member template
    spec_args: i32,         // a partial specialization: its argument patterns (targs list), else -1
    primary: i32,           // a partial specialization: the primary template
    inst_scope: i32,        // a member template of an instantiated class: the instantiated class scope
}
var tmpls: Tmpl[>..] = [];

// Template arguments: lists of TArg in targs, interned (equal lists, equal
// start index) so that a list can key a type and an instantiation.
let TA_TYPE = 1;            // ty
let TA_VALUE = 2;           // v (ty: its type), or a dependent expression (ty TY_DEPEXPR)
let TA_TEMPLATE = 3;        // v: the template symbol
let TA_PACK = 4;            // an expanded pack: v = the list of its elements
struct TArg { kind: u8, rsv: u8, rsv2: u16, ty: u32, v: i64 }
var targs: TArg[>..] = [];
var targ_lists: u32[>..] = [];      // list l: targ_lists[l] = first, targ_lists[l + 1] = count
var targ_scratch: TArg[>..<] = [];
var targ_map = dictionary<u64, i32> {};

fn targ_hash(mark: i64) -> u64 {
    var h: u64 = 1469598103934665603;
    for i in mark..targ_scratch.len {
        let a = targ_scratch[i];
        h = (h ^ (a.kind as u64)) * 1099511628211;
        h = (h ^ (a.ty as u64)) * 1099511628211;
        h = (h ^ (a.v as! u64)) * 1099511628211;
    }
    return h ^ ((targ_scratch.len - mark) as! u64);
}

// Interns targ_scratch[mark..] as a list, pops it: the list id.
fn targ_intern(mark: i64) -> i32 {
    let n = targ_scratch.len - mark;
    var h = targ_hash(mark);
    loop {
        let g = targ_map.get(h);
        if !g { break; }
        let l = g as i64;
        let first = targ_lists[l] as i64;
        if targ_lists[l + 1] as i64 == n {
            var same = true;
            for i in n {
                let a = targs[first + i];
                let b = targ_scratch[mark + i];
                if a.kind != b.kind || a.ty != b.ty || a.v != b.v { same = false; break; }
            }
            if same { targ_scratch.resize(mark); return l as! i32; }
        }
        h = h * 31 + 7;
    }
    let l = targ_lists.len;
    targ_lists.push(targs.len as! u32);
    targ_lists.push(n as! u32);
    for i in mark..targ_scratch.len { targs.push(targ_scratch[i]); }
    targ_scratch.resize(mark);
    targ_map.insert(h, l as! i32);
    return l as! i32;
}

fn tl_count(l: i64) -> i64 { if l < 0 { return 0; } return targ_lists[l + 1] as i64; }
fn tl_arg(l: i64, i: i64) -> TArg { targs[targ_lists[l] as i64 + i] }

// ---------------------------------------------------------------------------
// Types: references, member pointers, nullptr_t, dependent types.

var t_unknown: u32 = 0;
var t_nullptr: u32 = 0;
var t_char16: u32 = 0;
var t_char32: u32 = 0;
var t_char8: u32 = 0;
var t_wchar_cxx: u32 = 0;   // wchar_t: its own type in C++ (int-sized, signed)

fn mk_lref(t: u32) -> u32 {
    // reference collapsing: & to & or && is &
    let k = kind_of(t);
    if k == TY_LREF || k == TY_RREF { return qt(mk_type(TY_LREF, 0, tbase(t), 0, 0, 0) as i64, 0); }
    return qt(mk_type(TY_LREF, 0, t, 0, 0, 0) as i64, 0);
}
fn mk_rref(t: u32) -> u32 {
    let k = kind_of(t);
    if k == TY_LREF || k == TY_RREF { return unqual(t); }
    return qt(mk_type(TY_RREF, 0, t, 0, 0, 0) as i64, 0);
}
fn mk_memptr(member: u32, cls: u32) -> u32 { qt(mk_type(TY_MEMPTR, 0, member, 0, unqual(cls), 0) as i64, 0) }
fn mk_tparam(depth: i64, index: i64, name: u32, pack: bool) -> u32 {
    // the name is not part of the type: template<class T> and template<class U>
    // declare the same parameter
    return qt(mk_type(TY_TPARAM, if pack { TF_PACK } else { 0 }, 0, (depth << 16) | index, 0, 0) as i64, 0);
}
fn mk_depspec(tsym: i64, args: i32) -> u32 { qt(mk_type(TY_DEPSPEC, 0, 0, args as i64, tsym as! u32, 0) as i64, 0) }
fn mk_depname(q: u32, name: u32, args: i32) -> u32 { qt(mk_type(TY_DEPNAME, 0, q, args as i64, name, 0) as i64, 0) }
fn mk_packexp(t: u32) -> u32 { qt(mk_type(TY_PACKEXP, 0, t, 0, 0, 0) as i64, 0) }
fn mk_depexpr(tok: i64) -> u32 {
    let id = types.len;
    types.push(Type { kind: TY_DEPEXPR, flags: 0, rsv1: 0, align: 1, size: -1, base: 0, extra: 0, n: tok, canon: id as! u32, hnext: -1 });
    return qt(id, 0);
}

fn is_ref(t: u32) -> bool { let k = kind_of(t); k == TY_LREF || k == TY_RREF }
fn nonref(t: u32) -> u32 { if is_ref(t) { return tbase(t); } return t; }
fn is_unknown(t: u32) -> bool { kind_of(t) == TY_UNKNOWN }

// Is t dependent (contains a template parameter or a dependent construct)?
recursive fn is_dep(t: u32) -> bool {
    if t == 0 { return false; }
    let k = kind_of(t);
    if k >= TY_TPARAM && k <= TY_DEPEXPR { return true; }
    if k == TY_PACKEXP { return true; }
    if k == TY_POINTER || k == TY_LREF || k == TY_RREF || k == TY_ARRAY || k == TY_COMPLEX || k == TY_VECTOR {
        return is_dep(tbase(t));
    }
    if k == TY_MEMPTR { return is_dep(tbase(t)) || is_dep(types[t >> 4].extra); }
    if k == TY_FUNC {
        let ft = types[t >> 4];
        if is_dep(ft.base) { return true; }
        for i in ft.n { if is_dep(tparams[ft.extra + i]) { return true; } }
        return false;
    }
    if k == TY_STRUCT || k == TY_UNION {
        let r = rec_of(t);
        return r < crecs.len && crecs[r].flags & CR_PATTERN != 0;
    }
    return false;
}

// Dependent or unknown: a type D1 does not check.
fn is_opaque(t: u32) -> bool { is_unknown(t) || is_dep(t) }

fn cx_types_init() {
    let u = mk_basic(TY_UNKNOWN, -1, 1);
    t_unknown = u << 4;
    let np = mk_basic(TY_NULLPTR, 8, 8);
    t_nullptr = np << 4;
    // char16_t, char32_t, char8_t, wchar_t: distinct types with the
    // representation of uint_least16_t, uint_least32_t, unsigned char, int
    // (TY_* kinds would change the C side; D1 gives them aliases of
    // canonical types instead, see DESIGN.md 13.3)
    t_char16 = t_ushort;
    t_char32 = t_uint;
    t_char8 = t_uchar;
    t_wchar_cxx = t_int;
    scopes.push(Scope { kind: CS_NS, flags: 0, rsv: 0, parent: -1, sym: -1, name: 0, using_ns: -1, inl: -1, rec: -1 });
    cur_scope = 0;
}

// ---------------------------------------------------------------------------
// Name lookup.

var local_floor: i64 = 0;       // block-scope bindings below this depth are invisible (instantiation)
var vis_limit: i64 = 0x7FFFFFFF; // two-phase lookup: namespace members declared after this token are invisible
var st_lookups: i64 = 0;

// Resolves a using-declaration's symbol and namespace aliases.
fn resolve(s: i64) -> i64 {
    var x = s;
    var n = 0;
    while x >= 0 && syms[x].kind == SK_USING && n < 16 {
        let t = cxs[x].target as i64;
        if t < 0 { return x; }      // a dependent using-declaration: opaque
        x = t;
        n++;
    }
    return x;
}

// Is symbol s visible under the two-phase limit?
fn visible(s: i64) -> bool {
    if vis_limit == 0x7FFFFFFF { return true; }
    return cxs[s].pos as i64 <= vis_limit || cxs[s].flags & CF_MEMBER != 0;
}

// The first visible symbol of the chain starting at s.
fn first_visible(s0: i64) -> i64 {
    var s = s0;
    while s >= 0 && !visible(s) { s = cxs[s].nnext as i64; }
    return s;
}

// Lookup in namespace scope ns: its own members, then (unless only_own)
// the inline namespaces in it and the namespaces its using-directives
// nominate (transitively; C++ [namespace.qual]).
var ns_seen: i32[>..<] = [];
recursive fn ns_lookup(ns: i64, name: u32, only_own: bool) -> i64 {
    let s = first_visible(scope_find(ns, name));
    if s >= 0 { return s; }
    if only_own { return -1; }
    let mark = ns_seen.len;
    let r = ns_lookup_rec(ns, name, mark);
    ns_seen.resize(mark);
    return r;
}

recursive fn ns_lookup_rec(ns: i64, name: u32, mark: i64) -> i64 {
    for i in mark..ns_seen.len { if ns_seen[i] as i64 == ns { return -1; } }
    ns_seen.push(ns as! i32);
    let s = first_visible(scope_find(ns, name));
    if s >= 0 { return s; }
    var l = scopes[ns].inl;
    while l >= 0 {
        let r = ns_lookup_rec(ulinks[l].v as i64, name, mark);
        if r >= 0 { return r; }
        l = ulinks[l].next;
    }
    l = scopes[ns].using_ns;
    while l >= 0 {
        let r = ns_lookup_rec(ulinks[l].v as i64, name, mark);
        if r >= 0 { return r; }
        l = ulinks[l].next;
    }
    return -1;
}

// Lookup in class scope sc and its bases (non-dependent ones).
recursive fn class_lookup(sc: i64, name: u32) -> i64 {
    let s = scope_find(sc, name);
    if s >= 0 { return s; }
    let r = scopes[sc].rec as i64;
    if r < 0 || r >= crecs.len { return -1; }
    let cr = crecs[r];
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        let bt = b.ty;
        if kind_of(bt) != TY_STRUCT && kind_of(bt) != TY_UNION { continue; }
        let br = rec_of(bt);
        if br >= crecs.len || crecs[br].scope < 0 { continue; }
        let x = class_lookup(crecs[br].scope as i64, name);
        if x >= 0 { return x; }
    }
    return -1;
}

// Does class scope sc have a dependent base (whose members are unknown)?
recursive fn has_dep_base(sc: i64) -> bool {
    let r = scopes[sc].rec as i64;
    if r < 0 || r >= crecs.len { return false; }
    let cr = crecs[r];
    for i in cr.nbases {
        let bt = cbases[cr.bases + i].ty;
        if is_opaque(bt) { return true; }
        if is_record(bt) {
            let br = rec_of(bt);
            if br < crecs.len && crecs[br].scope >= 0 && has_dep_base(crecs[br].scope as i64) { return true; }
        }
    }
    return false;
}

// Qualified lookup of `name` in scope sc (C++ [basic.lookup.qual]).
recursive fn qual_lookup(sc: i64, name: u32) -> i64 {
    st_lookups++;
    let k = scopes[sc].kind as i64;
    if k == CS_CLASS { return class_lookup(sc, name); }
    if k == CS_ENUM { return scope_find(sc, name); }
    return ns_lookup(sc, name, false);
}

// The innermost block-scope binding of `name` above local_floor (ordinary
// names first, then tags), or -1.
fn local_lookup(name: u32) -> i64 {
    if name as i64 >= id_bind.len { return -1; }
    let o = id_bind[name].ord as i64;
    let t = id_bind[name].tag as i64;
    var best = -1;
    if o >= 0 && syms[o].scope as i64 >= local_floor && syms[o].scope > 0 { best = o; }
    if t >= 0 && syms[t].scope as i64 >= local_floor && syms[t].scope > 0 {
        if best < 0 || syms[t].scope > syms[best].scope { best = t; }
    }
    return best;
}

// Unqualified lookup (C++ [basic.lookup.unqual]): block scopes, then the
// scope chain from `from` outwards.
recursive fn unqual_lookup_from(from: i64, name: u32) -> i64 {
    st_lookups++;
    let l = local_lookup(name);
    if l >= 0 { return l; }
    var sc = from;
    while sc >= 0 {
        let k = scopes[sc].kind as i64;
        var s: i64 = -1;
        if k == CS_CLASS { s = class_lookup(sc, name); }
        else if k == CS_NS { s = ns_lookup(sc, name, false); }
        else if k == CS_ENUM { s = scope_find(sc, name); }
        if s >= 0 { return s; }
        sc = scopes[sc].parent as i64;
    }
    return -1;
}

recursive fn unqual_lookup(name: u32) -> i64 { unqual_lookup_from(cur_scope, name) }

// Is cur_scope inside a template pattern (a dependent context)?
var tmpl_depth: i64 = 0;        // template headers being parsed (pattern mode when > 0)
fn dependent_ctx() -> bool { tmpl_depth > 0 || scopes[cur_scope].flags & SCF_PATTERN != 0 }

// The scope of the class or namespace a symbol introduces, or -1.
fn sym_scope(s0: i64) -> i64 {
    let s = resolve(s0);
    if s < 0 { return -1; }
    let k = syms[s].kind as i64;
    if k == SK_NAMESPACE || k == SK_NSALIAS { return syms[s].v; }
    if k == SK_TAG || k == SK_TYPEDEF { return type_scope(syms[s].ty); }
    return -1;
}

// The class or enum scope of a type, or -1.
fn type_scope(t: u32) -> i64 {
    let k = kind_of(t);
    if k == TY_STRUCT || k == TY_UNION {
        let r = rec_of(t);
        if r < crecs.len { return crecs[r].scope as i64; }
        return -1;
    }
    if k == TY_ENUM { return enum_scope(types[t >> 4].extra as i64); }
    return -1;
}

// Enums: their scope (for E::x, scoped or not), by enum id.
var enum_scopes: i32[>..] = [];
fn enum_scope(e: i64) -> i64 {
    if e < enum_scopes.len { return enum_scopes[e] as i64; }
    return -1;
}
fn set_enum_scope(e: i64, sc: i64) {
    while enum_scopes.len <= e { enum_scopes.push(-1); }
    enum_scopes[e] = sc as! i32;
}

// The class type a scope is, or 0.
fn scope_class_type(sc: i64) -> u32 {
    if sc < 0 || scopes[sc].kind as i64 != CS_CLASS || scopes[sc].rec < 0 { return 0; }
    return records[scopes[sc].rec].ty << 4;
}

// The innermost enclosing class scope of `sc`, or -1.
fn enclosing_class(sc0: i64) -> i64 {
    var sc = sc0;
    while sc >= 0 {
        if scopes[sc].kind as i64 == CS_CLASS { return sc; }
        sc = scopes[sc].parent as i64;
    }
    return -1;
}

// The innermost enclosing namespace of `sc`.
fn enclosing_ns(sc0: i64) -> i64 {
    var sc = sc0;
    while sc >= 0 {
        if scopes[sc].kind as i64 == CS_NS { return sc; }
        sc = scopes[sc].parent as i64;
    }
    return 0;
}
