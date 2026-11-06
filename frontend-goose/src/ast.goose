// goosecc: the AST, symbols and scopes.
//
// The AST is one global array of fixed-size nodes; children are node
// indices, lists are runs in `nlist`. Every expression node has its type
// (a qtype) and value category, and every implicit conversion is an
// explicit N_ICAST node (see DESIGN.md, "The AST contract").

import std;
import .common;
import .types;

// Node kinds: expressions
let N_INT = 1;          // v = value (two's complement bits)
let N_FLOAT = 2;        // v = f64 bits; ldouble/float128 are kept as f64 here
let N_STRING = 3;       // a = index in strs
let N_DECLREF = 4;      // a = symbol
let N_UNARY = 5;        // op = U_*, a = operand
let N_BINARY = 6;       // op = B_*, a, b
let N_ASSIGN = 7;       // op = 0 (=) or B_* (compound), a = lhs, b = rhs, c = computation type
let N_COND = 8;         // a ? b : c (b may be 0 for GNU a ?: c, then a is evaluated once)
let N_CALL = 9;         // a = callee (pointer to function), v = first arg in nlist, c = count
let N_MEMBER = 10;      // a = base (lvalue record, or pointer for ->), b = field index, op = 1 for ->
let N_INDEX = 11;       // a = pointer, b = integer index (a[b] with the decay explicit)
let N_CAST = 12;        // op = cast kind, a = operand (written cast)
let N_ICAST = 13;       // op = cast kind, a = operand (implicit conversion)
let N_SIZEOF = 14;      // op = 0 sizeof / 1 alignof, a = expr (0 for a type), b = qtype; v = value, -1 for VLA
let N_COMPLIT = 15;     // compound literal: a = initializer, b = symbol of the object
let N_STMTEXPR = 16;    // a = compound statement
let N_INITLIST = 17;    // v = first item in nlist, c = count; b = filler for the remaining elements (0 none)
let N_ZEROINIT = 18;    // implicit zero/value initialization of ty
let N_VAARG = 19;       // a = va_list expression, ty = the type read
let N_LABELADDR = 20;   // a = label symbol (GNU &&label)
let N_OFFSETOF = 21;    // v = value
let N_ERROR = 22;       // recovery
let N_BUILTIN = 23;     // op = BI_* : a builtin with custom semantics; v/c = args (nlist)
let N_DESIG = 24;       // syntactic designated initializer (only during initializer analysis)
let N_SYNINIT = 25;     // syntactic { } list (only during initializer analysis)

// statements
let N_COMPOUND = 40;    // v = first in nlist, c = count
let N_DECL = 41;        // a = symbol, b = initializer (0 none)
let N_IF = 42;          // a = cond, b = then, c = else (0 none)
let N_WHILE = 43;       // a = cond, b = body
let N_DO = 44;          // a = body, b = cond
let N_FOR = 45;         // a = init (statement or 0), b = cond (0), c = inc (0), v = body
let N_SWITCH = 46;      // a = cond (promoted), b = body, v = first case in nlist, c = count
let N_CASE = 47;        // a = statement, v = value, c = node holding the high value of a GNU range (0)
let N_DEFAULT = 48;     // a = statement
let N_LABEL = 49;       // a = label symbol, b = statement
let N_GOTO = 50;        // a = label symbol
let N_IGOTO = 51;       // a = pointer expression
let N_BREAK = 52;
let N_CONTINUE = 53;
let N_RETURN = 54;      // a = expression (converted to the return type) or 0
let N_EXPR = 55;        // a = expression
let N_NULL = 56;
let N_ASM = 57;         // a = template string, v/c = operands in nlist (N_ASMOP)
let N_ASMOP = 58;       // a = constraint string, b = expression, op = 1 output / 2 clobber / 3 label
let N_FUNCDEF = 60;     // a = symbol, b = body, v = first param symbol in nlist, c = count
let N_TU = 61;          // v = first top-level item in nlist, c = count
let N_TYPEDEF = 62;     // a = symbol
let N_TAGDEF = 63;      // a = symbol of the tag
let N_STATICASSERT = 64;

// unary operators
let U_NEG = 1;
let U_PLUS = 2;
let U_NOT = 3;          // !  (result int)
let U_BITNOT = 4;
let U_DEREF = 5;        // *p: an lvalue
let U_ADDR = 6;         // &x
let U_PREINC = 7;
let U_PREDEC = 8;
let U_POSTINC = 9;
let U_POSTDEC = 10;
let U_REAL = 11;
let U_IMAG = 12;
let U_EXTENSION = 13;   // __extension__ (no-op wrapper)

// binary operators
let B_MUL = 1;
let B_DIV = 2;
let B_REM = 3;
let B_ADD = 4;
let B_SUB = 5;
let B_SHL = 6;
let B_SHR = 7;
let B_LT = 8;
let B_GT = 9;
let B_LE = 10;
let B_GE = 11;
let B_EQ = 12;
let B_NE = 13;
let B_AND = 14;
let B_XOR = 15;
let B_OR = 16;
let B_LAND = 17;
let B_LOR = 18;
let B_COMMA = 19;
let B_PTRADD = 20;      // pointer + integer (a = pointer, b = integer index, scaled by the pointee size)
let B_PTRSUB = 21;      // pointer - integer
let B_PTRDIFF = 22;     // pointer - pointer (result ptrdiff_t, in elements)

// cast kinds (as clang's CastKind)
let CK_LVAL2RVAL = 1;   // load
let CK_ARRAY2PTR = 2;
let CK_FUNC2PTR = 3;
let CK_NULL2PTR = 4;
let CK_INTEGRAL = 5;
let CK_INT2BOOL = 6;
let CK_INT2FLOAT = 7;
let CK_FLOAT2INT = 8;
let CK_FLOAT2BOOL = 9;
let CK_FLOATCAST = 10;
let CK_PTR2INT = 11;
let CK_INT2PTR = 12;
let CK_PTR2BOOL = 13;
let CK_BITCAST = 14;    // pointer to pointer
let CK_NOOP = 15;       // qualification change, enum<->int of the same size, etc.
let CK_TOVOID = 16;
let CK_TOUNION = 17;    // GNU cast to a union type
let CK_REAL2COMPLEX = 18;
let CK_COMPLEX2REAL = 19;
let CK_COMPLEXCAST = 20;
let CK_VECSPLAT = 21;
let CK_VECBITCAST = 22; // vector <-> vector/scalar of the same size
let CK_ATOMIC = 23;     // to/from _Atomic
let CK_BUILTIN2PTR = 24;

// node flags
let NF_LVALUE = 1;
let NF_BITFIELD = 2;    // an lvalue designating a bit-field
let NF_PAREN = 4;
let NF_NULLCONST = 8;   // a null pointer constant
let NF_STRINIT = 16;    // N_STRING used to initialize an array
let NF_ICE = 32;        // known to be an integer constant expression
let NF_PREDEF = 64;     // __func__ etc.
let NF_IMPLICIT = 128;  // implicitly generated

struct Node {
    kind: u8,
    op: u8,
    flags: u16,
    ty: u32,
    a: u32,
    b: u32,
    c: u32,
    loc: u32,
    v: i64,
}

var nodes: Node[>..] = [];
var nlist: u32[>..] = [];
var nscratch: u32[>..<] = [];     // lists under construction (mark / resize)

fn node(kind: i64, op: i64, ty: u32, a: i64, b: i64, c: i64, loc: u32) -> u32 {
    let n = nodes.len;
    nodes.push(Node { kind: kind as! u8, op: op as! u8, flags: 0, ty: ty, a: a as! u32, b: b as! u32, c: c as! u32, loc: loc, v: 0 });
    return n as! u32;
}

fn node_v(kind: i64, op: i64, ty: u32, a: i64, b: i64, c: i64, loc: u32, v: i64) -> u32 {
    let n = nodes.len;
    nodes.push(Node { kind: kind as! u8, op: op as! u8, flags: 0, ty: ty, a: a as! u32, b: b as! u32, c: c as! u32, loc: loc, v: v });
    return n as! u32;
}

// Moves nscratch[mark..] to nlist; returns the start.
fn commit_list(mark: i64) -> i64 {
    let start = nlist.len;
    for j in mark..nscratch.len { nlist.push(nscratch[j]); }
    nscratch.resize(mark);
    return start;
}

fn is_lvalue(n: u32) -> bool { nodes[n].flags & NF_LVALUE != 0 }

// String literals: bytes (already decoded, with the terminating NUL)
// in strbytes; elem is the character type.
struct StrLit { start: u32, len: u32, elem: u32 }
var strs: StrLit[>..] = [];
var strbytes: u8[>..] = [];

// ---------------------------------------------------------------------------
// Symbols

let SK_VAR = 1;
let SK_FUNC = 2;
let SK_TYPEDEF = 3;
let SK_ENUMC = 4;
let SK_TAG = 5;        // v = type index of the struct/union/enum
let SK_LABEL = 6;
let SK_BUILTIN = 7;    // a builtin function, v = builtin entry

let SC_NONE = 0;
let SC_EXTERN = 1;
let SC_STATIC = 2;
let SC_AUTO = 3;
let SC_REGISTER = 4;
let SC_TYPEDEF = 5;

let SF_DEFINED = 1;     // function with a body / object with an initializer / label defined
let SF_INLINE = 2;
let SF_USED = 4;
let SF_PARAM = 8;
let SF_IMPLICIT = 16;   // implicitly declared function
let SF_NORETURN = 32;
let SF_THREAD = 64;
let SF_WEAK = 128;
let SF_FILESCOPE = 256;
let SF_TENTATIVE = 512;
let SF_LABEL_USED = 1024;
let SF_ADDR = 2048;     // address taken
let SF_COMPLIT = 4096;  // the object of a compound literal
let SF_KR = 8192;       // a K&R parameter given its type by the declaration list
let SF_LOCALLINK = 16384; // block-scope extern

struct Sym {
    kind: u8,
    sc: u8,
    flags: u16,
    name: u32,
    ty: u32,
    prev: i32,
    canon: i32,
    scope: u32,
    def: i32,
    v: i64,
    loc: u32,
    attr: u32,       // index in sym_attrs (0 = none)
}

var syms: Sym[>..] = [];

// Extra declaration attributes (asm label, alias, section, cleanup, ...).
struct SymAttr { asm_label: u32, asm_len: u32, cleanup: i32, align: u32, flags: u32 }
var sym_attrs: SymAttr[>..] = [];

// Per identifier: the innermost ordinary / tag binding (-1 none).
var id_ord: i32[>..] = [];
var id_tag: i32[>..] = [];
var id_label: i32[>..] = [];

var scope_depth: i64 = 0;
var scope_log: u32[>..<] = [];     // symbols bound, innermost scope last
var scope_marks: u32[>..<] = [];

fn ensure_ids() {
    while id_ord.len < idents.len {
        id_ord.push(-1);
        id_tag.push(-1);
        id_label.push(-1);
    }
}

fn new_sym(kind: i64, name: u32, ty: u32, loc: u32) -> i64 {
    let s = syms.len;
    syms.push(Sym { kind: kind as! u8, sc: 0, flags: 0, name: name, ty: ty, prev: -1, canon: s as! i32,
        scope: scope_depth as! u32, def: -1, v: 0, loc: loc, attr: 0 });
    return s;
}

// Binds symbol s in the current scope (ordinary or tag namespace).
fn bind_sym(s: i64, tag: bool) {
    let name = syms[s].name as i64;
    if name == 0 { return; }
    ensure_ids();
    if tag {
        syms[s].prev = id_tag[name];
        id_tag[name] = s as! i32;
    } else {
        syms[s].prev = id_ord[name];
        id_ord[name] = s as! i32;
    }
    syms[s].scope = scope_depth as! u32;
    scope_log.push(s as! u32);
}

fn push_scope() {
    scope_marks.push(scope_log.len as! u32);
    scope_depth++;
}

fn pop_scope() {
    let mark = scope_marks.pop() as i64;
    var j = scope_log.len - 1;
    while j >= mark {
        let s = scope_log[j] as i64;
        let name = syms[s].name as i64;
        if syms[s].kind == SK_TAG {
            id_tag[name] = syms[s].prev;
        } else {
            id_ord[name] = syms[s].prev;
        }
        j--;
    }
    scope_log.resize(mark);
    scope_depth--;
}

fn lookup_ord(name: u32) -> i64 {
    if name as i64 >= id_ord.len { return -1; }
    return id_ord[name] as i64;
}

fn lookup_tag(name: u32) -> i64 {
    if name as i64 >= id_tag.len { return -1; }
    return id_tag[name] as i64;
}

fn sym_name(s: i64) -> const u8[:] { ident_text(syms[s].name as i64) }
