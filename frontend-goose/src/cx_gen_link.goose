// goosecc D3: names and linkage of what C++ code generation emits (clang's
// CodeGenModule::getFunctionLinkage / getVTableLinkage with the Itanium
// C++ ABI's rules), for the lowering (cx_gen_defs.goose, cxl).
//
//   inline functions (defined in their class, `inline`, constexpr,
//   implicit special members), implicit template instantiations,
//   inline variables                         linkonce_odr, own comdat
//   vtables, typeinfo of a dynamic class     with its key function's
//                                            definition (strong), else
//                                            linkonce_odr (comdat), or
//                                            undefined when the key
//                                            function is defined elsewhere
//   anything in an unnamed namespace         internal
//
// Constructors and destructors: the symbol of the declaration is the
// base-object variant (C2/D2), which has the code. The complete-object
// variant (C1/D1, complete_sym) is, as with clang's -mconstructor-aliases,
// an alias of it when it is external, and the same symbol when it is
// linkonce_odr (clang replaces its uses: no C1 symbol at all).

namespace cx;

import std;
import dictionary;
import .common;
import .types;
import .ast;
import .sema;
import .parse;
import .cx_core;
import .cx_layout;
import .cx_mangle;
import .cx_gen_defs;

var mg_structor: i64 = 1;       // the structor variant cx_mangle names: 1 complete (C1/D1), 2 base (C2/D2)

var complete_of = dictionary<u64, u32> {};      // structor -> its complete-object symbol
var complete_pairs: u32[>..] = [];              // (structor, complete-object symbol)
var complete_base = dictionary<u64, u32> {};    // complete-object symbol -> structor

// The complete-object variant of constructor or destructor s.
fn complete_sym(s: i64) -> i64 {
    if cxs[s].flags & (CF_CTOR | CF_DTOR) == 0 || cxs[s].flags & CF_DTOR_DELETING != 0 { return s; }
    if complete_base.count > 0 && complete_base.contains(s as u64) { return s; }
    let g = complete_of.get(s as u64);
    if g { return g as i64; }
    let a = csym(SK_FUNC, syms[s].name, syms[s].ty, syms[s].loc);
    cxs[a] = cxs[s];
    cxs[a].nnext = -1;
    syms[a].flags = syms[s].flags & ~(SF_DEFINED as! u32);
    syms[a].def = -1;
    complete_of.insert(s as u64, a as! u32);
    complete_base.insert(a as u64, s as! u32);
    complete_pairs.push(s as! u32);
    complete_pairs.push(a as! u32);
    if names_done { name_complete(s, a); }
    return a;
}

fn is_complete_variant(s: i64) -> bool { complete_base.contains(s as u64) }

// Is function s inline (defined in its class, declared inline or
// constexpr, implicit, or an implicit instantiation)?
fn fn_inline(s: i64) -> bool {
    let fl = cxs[s].flags;
    if fl & (CF_DEFINED_IN_CLASS | CF_IMPLICIT | CF_CONSTEXPR) != 0 { return true; }
    if syms[s].flags & SF_INLINE != 0 { return true; }
    if fl & CF_SPEC != 0 { return true; }
    return false;
}

fn set_link(s: i64, lk: i64, flags: i64) {
    cxl_grow();
    cxl[s].link = lk as! u8;
    cxl[s].flags = ((cxl[s].flags as i64) | flags) as! u8;
}

// Is class r internal (in an unnamed namespace, or local to a function)?
fn class_internal(r: i64) -> bool {
    var sc = crecs[r].scope as i64;
    while sc > 0 {
        if scopes[sc].flags & SCF_ANON != 0 { return true; }
        if scopes[sc].kind as i64 == CS_BLOCK { return true; }
        sc = scopes[sc].parent as i64;
    }
    return false;
}

// The key function of dynamic class r (Itanium 5.2.3): the first virtual
// function declared in it that is neither pure nor inline, or -1.
fn key_function(r: i64) -> i64 {
    let m = mem_range(r);
    for j in m.count {
        let f = cmem[m.first + j] as i64;
        if syms[f].kind as i64 != SK_FUNC { continue; }
        let fl = cxs[f].flags;
        if fl & CF_VIRTUAL == 0 || fl & (CF_PURE | CF_DEFINED_IN_CLASS | CF_IMPLICIT | CF_DEFAULTED | CF_DELETED) != 0 { continue; }
        if syms[f].flags & SF_INLINE != 0 { continue; }
        return f;
    }
    return -1;
}

// How the vtable (and the typeinfo of a dynamic class) of r is emitted:
// 0 internal, 1 linkonce_odr, 2 strong here, 3 undefined (defined with the
// key function elsewhere).
fn vt_kind(r: i64) -> i64 {
    if class_internal(r) { return 0; }
    let kf = key_function(r);
    if kf < 0 { return 1; }
    // the key function's definition (its declaration may be a redeclaration)
    if syms[kf].def >= 0 || syms[resolve(kf)].def >= 0 { return 2; }
    var c = syms[kf].canon as i64;
    if c >= 0 && syms[c].def >= 0 { return 2; }
    return 3;
}

// The linkage of a vtable / VTT / typeinfo variable s of class r (vtk:
// vt_kind; dynamic: false for the typeinfo of a class without vtable,
// which is always linkonce_odr unless internal).
fn set_class_data_link(s: i64, r: i64, dynamic: bool, relro: bool) {
    var k = vt_kind(r);
    if !dynamic && k != 0 { k = 1; }
    let rf = if relro { CXL_RELRO } else { 0 };
    if k == 0 {
        syms[s].sc = SC_STATIC as! u8;
        set_link(s, LK_DEFAULT, rf);
    } else if k == 1 {
        syms[s].sc = 0;
        set_link(s, LK_LINKONCE, rf | CXL_COMDAT);
    } else if k == 2 {
        syms[s].sc = 0;
        set_link(s, LK_DEFAULT, rf);
    } else {
        syms[s].sc = SC_EXTERN as! u8;
        syms[s].flags = syms[s].flags & ~(SF_DEFINED as! u32);
    }
}

// Mangled names as asm labels; the linkage of each function and variable.
fn name_syms() {
    cx_grow();
    cxl_grow();
    for s in 1..syms.len {
        let k = syms[s].kind as i64;
        if k != SK_FUNC && k != SK_VAR { continue; }
        let fl = cxs[s].flags;
        if fl & (CF_PATTERN | CF_TEMPLATE | CF_TPARAM) != 0 { continue; }
        if syms[s].attr != 0 && sym_attrs[syms[s].attr].asm_len != 0 { continue; }
        if k == SK_FUNC && complete_of.count > 0 && is_complete_variant(s) { continue; }
        if k == SK_VAR {
            if syms[s].flags & SF_COMPLIT != 0 || syms[s].name == 0 { continue; }
            if fl & CF_MEMBER != 0 { syms[s].sc = 0; syms[s].flags = syms[s].flags | SF_FILESCOPE; }
            if syms[s].flags & SF_FILESCOPE == 0 { continue; }
            // a static local: C's lowering names it
            if syms[s].scope > 0 && fl & CF_MEMBER == 0 { continue; }
        }
        let internal = internal_linkage(s) || (cxs[s].dscope > 0 && in_anon_ns(cxs[s].dscope as i64));
        let structor = k == SK_FUNC && fl & (CF_CTOR | CF_DTOR) != 0 && fl & CF_DTOR_DELETING == 0;
        mg_structor = if structor { 2 } else { 1 };
        let ok = mangle_sym(s);
        mg_structor = 1;
        if ok {
            if syms[s].name == 0 || !same_text(mg, ident_text(syms[s].name as i64)) { set_label(s, mg); }
        } else {
            // a name D1 cannot mangle (local classes ...): an internal one
            var nm: u8[>..] = [];
            format(nm, "_ZL__goosecc_", s);
            set_label(s, nm);
            syms[s].sc = SC_STATIC as! u8;
        }
        if k == SK_FUNC {
            let inline = fn_inline(s);
            if fl & CF_MEMBER != 0 && syms[s].sc as i64 != SC_EXTERN { syms[s].sc = 0; }
            if internal || !ok {
                syms[s].sc = SC_STATIC as! u8;
            } else if inline {
                if syms[s].sc as i64 == SC_STATIC { syms[s].sc = 0; }
                set_link(s, LK_LINKONCE, CXL_COMDAT);
            }
        } else {
            if internal && syms[s].sc as i64 != SC_EXTERN { syms[s].sc = SC_STATIC as! u8; }
            else if syms[s].flags & SF_INLINE != 0 && syms[s].sc as i64 != SC_EXTERN { set_link(s, LK_LINKONCE, CXL_COMDAT); }
        }
        if internal && syms[s].sc as i64 != SC_EXTERN { syms[s].sc = SC_STATIC as! u8; }
    }
    // the complete-object variants of constructors and destructors (and
    // those made from now on)
    for i in 0..complete_pairs.len / 2 { name_complete(complete_pairs[2 * i] as i64, complete_pairs[2 * i + 1] as i64); }
    names_done = true;
}
var names_done = false;

// The name and linkage of a, the complete-object variant of structor s.
fn name_complete(s: i64, a: i64) {
    cxl_grow();
    cxs[a].flags = cxs[s].flags;
    syms[a].ty = syms[s].ty;
    syms[a].sc = syms[s].sc;
    if syms[s].sc as i64 == SC_STATIC || cxl_link(s) != LK_DEFAULT {
        // one function: the same symbol
        set_label(a, ident_text(gen::link_name(s) as i64));
        cxl[a] = cxl[s];
        return;
    }
    mg_structor = 1;
    let ok = mangle_sym(s);
    if !ok { set_label(a, ident_text(gen::link_name(s) as i64)); return; }
    set_label(a, mg);
    cxl[a].alias = s as! i32;
}

fn same_text(a: const u8[:], b: const u8[:]) -> bool { a == b }

// The offset (from the address point, negative) of the virtual base offset
// of virtual base br in the vtable of r (the typeinfo of a class with
// virtual bases). TODO(D3 MI): the Itanium vtable layout.
fn vbase_offset_offset(r: i64, br: i64) -> i64 {
    err_at(records[r].loc, "goosecc: C++ code generation does not support the typeinfo of classes with virtual bases yet");
    return 0;
}
