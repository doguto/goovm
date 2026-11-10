// goosecc D3: what the C++ code generator (cx_gen*.goose, namespace cx)
// and the C++ parts of the lowering (cx_eh.goose and the C++-only branches
// of gen_*.goose, namespace gen) share: the lowering nodes C++ adds to C's
// AST, and the C++ linkage of symbols (DESIGN.md, section 14).
//
// None of this exists in a C translation unit: the C lowering's output is
// the same as before D3.

import std;
import dictionary;
import .common;
import .ast;

// ---------------------------------------------------------------------------
// Lowering nodes. C++'s constructs are C nodes plus these, which need the
// lowering's knowledge of control flow (cleanups on every exit, landing
// pads).

// A temporary object with a destructor, alive to the end of the enclosing
// full-expression (or of the enclosing block when lifetime-extended): an
// lvalue of type ty. b = its symbol (a local, SF_COMPLIT); a = the statement
// that constructs it (0: none, it is constructed by whoever writes it);
// c = its destructor (a function taking its address; 0: none).
let N_XTEMP = 100;
let XT_EXTENDED = 1;    // lifetime-extended (bound to a reference): destroyed at the end of the block
let XT_COND = 2;        // conditionally evaluated (in an operand of ?:, && or ||): a flag says whether it exists

// A cleanup for the rest of the enclosing compound statement (a statement).
// op: XP_CALL: call c(&a) (a = variable, c = function); XP_STMT: the
// statement a; XP_EHONLY: only when an exception leaves the scope.
let N_XPUSH = 101;
let XP_CALL = 1;
let XP_STMT = 2;
let XP_EHONLY = 4;
let XP_TERMINATE = 8;   // (with neither call nor statement) a scope whose exceptions call std::terminate

// try { a } handlers: v/c = the N_XCATCH handlers.
let N_XTRY = 102;
// A handler: a = the exception variable (0 none), b = the handler's body,
// c = the typeinfo variable of the caught type (0: catch (...)), v = the
// statement that initializes the variable from N_XEXN (0 none); op: XC_*.
let N_XCATCH = 103;
let XC_COPY = 1;        // the variable is a class copied by a constructor: __cxa_get_exception_ptr first, then __cxa_begin_catch
let XC_RETHROW = 2;     // a function-try-block of a constructor or destructor: the handler rethrows at its end

// The adjusted exception pointer of the enclosing handler (void *), from
// __cxa_begin_catch or __cxa_get_exception_ptr.
let N_XEXN = 104;

// The function's return slot (an sret pointer, as a pointer value of type
// ty) in a function whose result is a class passed by invisible reference.
let N_XRETSLOT = 105;

// A class prvalue made by a call returning it by invisible reference: a =
// the N_CALL (of type T *), b = its first argument, an N_XDST placeholder
// that receives the destination's address when the prvalue is used to
// initialize an object (cx_gen's init_into); a prvalue never used so is
// materialized as a temporary (N_XTEMP) by cg_finish. ty = the class.
let N_XPRV = 106;
let N_XDST = 107;
// return of a candidate for the named return value optimization: a = the
// variable, b = the expression that copies (moves) it into the return
// slot otherwise, c = the function's return slot parameter.
let N_XNRET = 108;

let CXL_NRVO = 32;      // a local variable that lives in the return slot (the sret argument)

var n_xtemps: i64 = 0;  // N_XTEMP nodes with a destructor made so far (the lowering looks for them in conditions only then)

// ---------------------------------------------------------------------------
// The C++ linkage of symbols, for the lowering (cxl[s], grown with syms).

let LK_DEFAULT = 0;     // C's rules (external, or internal for static)
let LK_LINKONCE = 1;    // linkonce_odr: weak, in a comdat, emitted only when used
let LK_WEAKODR = 2;     // weak_odr: weak, in a comdat, always emitted

let CXL_NOEXCEPT = 1;   // the function's body is a terminate scope (noexcept)
let CXL_NOUNWIND = 2;   // calls of it never throw (plain calls, not invokes)
let CXL_HIDDEN = 4;     // hidden visibility
let CXL_RELRO = 8;      // a constant with relocations: .data.rel.ro (clang's section for vtables, typeinfo)
let CXL_COMDAT = 16;
let CXL_OWNLINK = 64;   // an alias with its own (default, global) linkage, not its target's    // in a comdat (the group named `comdat`, or after itself when 0)

struct CxLink { link: u8, flags: u8, rsv: u16, comdat: u32, alias: i32 }
var cxl: CxLink[>..] = [];

fn cxl_grow() {
    while cxl.len < syms.len { cxl.push(CxLink { link: 0, flags: 0, rsv: 0, comdat: 0, alias: -1 }); }
}

fn cxl_link(s: i64) -> i64 { if s < cxl.len { cxl[s].link as i64 } else { 0 } }
fn cxl_has(s: i64, f: i64) -> bool { s < cxl.len && (cxl[s].flags as i64) & f != 0 }

// Variables a function's definition keeps (clang emits the vtable and VTT
// of a class with each constructor and destructor it emits): a chain per
// function of (variable, next) entries.
struct CxUse { v: u32, next: i32 }
var cx_uses: CxUse[>..] = [];
var cx_use_head = dictionary<u64, u32> {};      // function -> its last entry + 1

fn note_cx_use(f: i64, v: i64) {
    var h: i64 = -1;
    let g = cx_use_head.get(f as u64);
    if g { h = g as i64 - 1; }
    var i = h;
    while i >= 0 {
        if cx_uses[i].v as i64 == v { return; }
        i = cx_uses[i].next as i64;
    }
    cx_uses.push(CxUse { v: v as! u32, next: h as! i32 });
    cx_use_head.insert(f as u64, cx_uses.len as! u32);
}
