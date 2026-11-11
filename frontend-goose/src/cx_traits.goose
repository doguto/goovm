// goosecc D2: type trait builtins (clang's __is_* / __has_* keywords,
// as libstdc++'s <type_traits> uses them) and the class properties they
// ask for (C++ [class.prop], [class.copy]): trivial special members,
// trivially copyable, trivial, standard-layout, aggregate, literal types,
// and the constructibility, assignability and convertibility of types by
// overload resolution on probe operands.

namespace cx;

import std;
import dictionary;
import .common;
import .types;
import .ast;
import .sema;
import .expr;
import .cx_core;
import .cx_names;
import .cx_decl;
import .cx_tmpl;
import .cx_inst;
import .cx_conv;
import .cx_layout;

// Class property bits (cprops, per record).
let CP_DONE = 1;
let CP_TRIV_DEF = 2;        // a trivial default constructor (and one is declared, not deleted)
let CP_HAS_DEF = 4;         // a default constructor (user or implicit, not deleted)
let CP_TRIV_COPY = 8;
let CP_TRIV_MOVE = 16;
let CP_TRIV_CASG = 32;
let CP_TRIV_MASG = 64;
let CP_TRIV_DTOR = 128;
let CP_TRIV_COPYABLE = 256;
let CP_STD_LAYOUT = 512;
let CP_AGGREGATE = 1024;
let CP_VIRT_DTOR = 2048;
let CP_USER_CTOR = 4096;    // a user-declared constructor
let CP_LITERAL = 8192;
let CP_BUSY = 16384;
let CP_FINAL = 32768;
let CP_HAS_COPY_DECL = 65536;   // copy constructor user-declared
let CP_HAS_MOVE_DECL = 131072;
let CP_HAS_CASG_DECL = 262144;
let CP_HAS_MASG_DECL = 524288;
let CP_HAS_DTOR_DECL = 1048576;
let CP_UNKNOWN = 2097152;   // a member or base not known: properties not trusted

var cprops: u32[>..] = [];
var final_recs = dictionary<u64, u32> {};

fn mark_final(r: i64) { final_recs.insert(r as u64, 1); }

// The first parameter of f is a reference to cv class cls: 1 lvalue, 2 rvalue (0 not).
fn ref_to_cls_param(f: i64, cls: u32) -> i64 {
    let ft = types[syms[f].ty >> 4];
    if ft.n < 1 { return 0; }
    let p0 = tparams[ft.extra];
    if !is_ref(p0) || unqual(tbase(p0)) != unqual(cls) { return 0; }
    if !defaults_from(f, 1) { return 0; }
    return if kind_of(p0) == TY_RREF { 2 } else { 1 };
}

fn user_provided_fn(f: i64) -> bool { cxs[f].flags & (CF_IMPLICIT | CF_DEFAULTED) == 0 }

// The properties of class r.
recursive fn class_props(r: i64) -> u32 {
    while cprops.len <= r { cprops.push(0); }
    if cprops[r] & (CP_DONE | CP_BUSY) != 0 { return cprops[r]; }
    cprops[r] = CP_BUSY;
    let cls = records[r].ty << 4;
    need_complete(cls);
    var f: u32 = 0;
    var unknown = false;
    let cr = crecs[r];
    let dynamic = cr.flags & CR_DYNAMIC != 0;
    if records[r].flags & RF_COMPLETE == 0 || records[r].size < 0 || cr.flags & CR_PATTERN != 0 || inst_dirty.contains(r as u64) { unknown = true; }
    if final_recs.contains(r as u64) { f = f | CP_FINAL; }
    // the declared special members
    var def_user = false;       // a user-provided default constructor
    var def_decl = false;       // a default constructor declared (user or defaulted)
    var def_deleted = false;
    var copy_user = false;
    var move_user = false;
    var casg_user = false;
    var masg_user = false;
    var dtor_user = false;
    var virt_dtor = false;
    var any_ctor = false;
    var explicit_or_user_ctor = false;
    let m = mem_range(r);
    for j in m.count {
        let s = cmem[m.first + j] as i64;
        let fl = cxs[s].flags;
        if fl & CF_IMPLICIT != 0 { continue; }
        if fl & CF_CTOR != 0 {
            any_ctor = true;
            if user_provided_fn(s) || fl & CF_EXPLICIT != 0 { explicit_or_user_ctor = true; }
            let k = ref_to_cls_param(s, cls);
            if k == 1 { f = f | CP_HAS_COPY_DECL; if user_provided_fn(s) || fl & CF_DELETED != 0 { copy_user = true; } }
            else if k == 2 { f = f | CP_HAS_MOVE_DECL; if user_provided_fn(s) || fl & CF_DELETED != 0 { move_user = true; } }
            else if defaults_from(s, 0) {
                def_decl = true;
                if user_provided_fn(s) { def_user = true; }
                if fl & CF_DELETED != 0 { def_deleted = true; }
            }
        } else if fl & CF_DTOR != 0 {
            f = f | CP_HAS_DTOR_DECL;
            if user_provided_fn(s) || fl & CF_DELETED != 0 { dtor_user = true; }
            if fl & CF_VIRTUAL != 0 { virt_dtor = true; }
        } else if fl & CF_OPERATOR != 0 && cxs[s].op as i64 == OP_EQUAL && fl & CF_STATIC == 0 {
            let k = ref_to_cls_param(s, cls);
            let byval = types[syms[s].ty >> 4].n == 1 && unqual(tparams[types[syms[s].ty >> 4].extra]) == unqual(cls);
            if k == 1 || byval { f = f | CP_HAS_CASG_DECL; if user_provided_fn(s) || fl & CF_DELETED != 0 { casg_user = true; } }
            else if k == 2 { f = f | CP_HAS_MASG_DECL; if user_provided_fn(s) || fl & CF_DELETED != 0 { masg_user = true; } }
        } else if syms[s].kind as i64 == SK_TEMPLATE && fl & CF_CTOR != 0 {
            any_ctor = true;
        }
    }
    // constructor templates count as user-declared constructors
    let sc = crecs[r].scope as i64;
    if sc >= 0 {
        var x = scope_find(sc, id_ctor);
        while x >= 0 {
            if syms[x].kind as i64 == SK_TEMPLATE { any_ctor = true; explicit_or_user_ctor = true; }
            x = cxs[x].nnext as i64;
        }
    }
    if any_ctor { f = f | CP_USER_CTOR; }
    // the bases and members
    var bases_triv = CP_TRIV_DEF | CP_TRIV_COPY | CP_TRIV_MOVE | CP_TRIV_CASG | CP_TRIV_MASG | CP_TRIV_DTOR;
    var bases_def = true;
    var std_layout = !dynamic;
    var aggregate = !dynamic;
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if !is_record(b.ty) || is_opaque(b.ty) { unknown = true; continue; }
        let bp = class_props(rec_of(b.ty));
        if bp & CP_UNKNOWN != 0 { unknown = true; }
        bases_triv = bases_triv & (bp & (CP_TRIV_DEF | CP_TRIV_COPY | CP_TRIV_MOVE | CP_TRIV_CASG | CP_TRIV_MASG | CP_TRIV_DTOR));
        if bp & CP_HAS_DEF == 0 { bases_def = false; }
        if bp & CP_STD_LAYOUT == 0 { std_layout = false; }
        if bp & CP_VIRT_DTOR != 0 { virt_dtor = true; }
        if b.flags & BF_VIRTUAL != 0 || b.access as i64 != AC_PUBLIC { aggregate = false; }
    }
    let rec = records[r];
    var access0: i64 = -1;
    var nsdmi = false;
    var fields_with_data = 0;
    for i in rec.first..rec.first + rec.count {
        let fd = fields[i];
        if fd.name == 0 && fd.width >= 0 { continue; }
        fields_with_data++;
        let ms = field_sym(sc, fd.name);
        if ms >= 0 {
            let acc = cxs[ms].access as i64;
            if access0 < 0 { access0 = acc; } else if acc != access0 { std_layout = false; }
            if acc != AC_PUBLIC { aggregate = false; }
            if cxs[ms].body != 0 { nsdmi = true; }
        }
        if is_ref(fd.ty) { std_layout = false; bases_triv = bases_triv & ~(CP_TRIV_DEF | CP_TRIV_CASG | CP_TRIV_MASG); bases_def = false; continue; }
        var bt = fd.ty;
        while is_array(bt) { bt = tbase(bt); }
        if is_opaque(bt) { unknown = true; continue; }
        if is_record(bt) {
            let mp = class_props(rec_of(bt));
            if mp & CP_UNKNOWN != 0 { unknown = true; }
            bases_triv = bases_triv & (mp & (CP_TRIV_DEF | CP_TRIV_COPY | CP_TRIV_MOVE | CP_TRIV_CASG | CP_TRIV_MASG | CP_TRIV_DTOR));
            if mp & CP_HAS_DEF == 0 { bases_def = false; }
            if mp & CP_STD_LAYOUT == 0 { std_layout = false; }
        } else if quals(bt) & Q_CONST != 0 {
            // a const member of scalar type: no implicit default constructor, no assignment
            bases_triv = bases_triv & ~(CP_TRIV_CASG | CP_TRIV_MASG);
            if !nsdmi { bases_def = false; }
        }
    }
    if cr.nbases > 0 && fields_with_data > 0 {
        // the members must all be declared in one class of the hierarchy
        for i in cr.nbases {
            let b = cbases[cr.bases + i];
            if is_record(b.ty) && !class_is_empty(b.ty) { std_layout = false; }
        }
    }
    // the implicitly declared members ([class.copy])
    let has_copy = f & CP_HAS_COPY_DECL != 0;
    let has_move = f & CP_HAS_MOVE_DECL != 0;
    let has_casg = f & CP_HAS_CASG_DECL != 0;
    let has_masg = f & CP_HAS_MASG_DECL != 0;
    let has_dtor = f & CP_HAS_DTOR_DECL != 0;
    var triv: u32 = 0;
    // default constructor: implicit unless some constructor is user-declared
    let implicit_def = !any_ctor;
    if (implicit_def || (def_decl && !def_user)) && !def_deleted {
        if bases_def { f = f | CP_HAS_DEF; }
        if !dynamic && !nsdmi && bases_triv & CP_TRIV_DEF != 0 && bases_def { triv = triv | CP_TRIV_DEF; }
    } else if def_user { f = f | CP_HAS_DEF; }
    if !copy_user && !dynamic && bases_triv & CP_TRIV_COPY != 0 { triv = triv | CP_TRIV_COPY; }
    if !move_user && !dynamic && bases_triv & CP_TRIV_MOVE != 0 { triv = triv | CP_TRIV_MOVE; }
    if !casg_user && !dynamic && bases_triv & CP_TRIV_CASG != 0 { triv = triv | CP_TRIV_CASG; }
    if !masg_user && !dynamic && bases_triv & CP_TRIV_MASG != 0 { triv = triv | CP_TRIV_MASG; }
    if !dtor_user && !virt_dtor && bases_triv & CP_TRIV_DTOR != 0 { triv = triv | CP_TRIV_DTOR; }
    // a move constructor declared by the user deletes the implicit copy ones
    let copy_deleted = !has_copy && (has_move || has_masg);
    let casg_deleted = !has_casg && (has_move || has_masg);
    var tc = triv & CP_TRIV_DTOR != 0;
    var any_eligible = false;
    if has_copy || !copy_deleted { any_eligible = true; if triv & CP_TRIV_COPY == 0 { tc = false; } }
    if has_move { any_eligible = true; if triv & CP_TRIV_MOVE == 0 { tc = false; } }
    if has_casg || !casg_deleted { any_eligible = true; if triv & CP_TRIV_CASG == 0 { tc = false; } }
    if has_masg { any_eligible = true; if triv & CP_TRIV_MASG == 0 { tc = false; } }
    if tc && any_eligible { f = f | CP_TRIV_COPYABLE; }
    f = f | triv;
    if std_layout { f = f | CP_STD_LAYOUT; }
    if aggregate && !(if opt_cxx_std >= 20 { any_ctor } else { explicit_or_user_ctor }) { f = f | CP_AGGREGATE; }
    if virt_dtor { f = f | CP_VIRT_DTOR; }
    if unknown { f = f | CP_UNKNOWN; }
    f = f | CP_DONE;
    cprops[r] = f;
    return f;
}

fn field_sym(sc: i64, name: u32) -> i64 {
    if sc < 0 || name == 0 { return -1; }
    var s = scope_find(sc, name);
    while s >= 0 {
        if syms[s].kind as i64 == SK_FIELD { return s; }
        s = cxs[s].nnext as i64;
    }
    return -1;
}

fn class_is_empty(t: u32) -> bool {
    let r = rec_of(t);
    return crecs[r].flags & CR_EMPTY != 0;
}

// ---------------------------------------------------------------------------
// The traits.

// A probe expression of type t as declval<t>() gives it: an lvalue for an
// lvalue reference, an xvalue otherwise.
fn trait_probe(t: u32) -> u32 {
    let n = node(N_CXX, 0, nonref(t), 0, 0, 0, 0);
    if kind_of(t) == TY_LREF { nodes[n].flags = NF_LVALUE; }
    else if !is_func(t) { nodes[n].flags = (NF_LVALUE | NF_XVALUE) as! u16; }
    else { nodes[n].flags = NF_LVALUE; }
    return n;
}

fn is_complete_or_void(t: u32) -> bool {
    let u = nonref(t);
    if is_void(u) || is_func(u) { return true; }
    if is_array(u) && types[u >> 4].n < 0 { return true; }
    need_complete(u);
    return is_complete(u);
}

// Evaluates trait `name` on the types trait_args[mark..]: (known, value).
recursive fn eval_trait_cx(name: const u8[:], mark: i64) -> bool, i64 {
    let n = trait_args.len - mark;
    if n < 1 { return false, 0; }
    let t = trait_args[mark];
    for i in mark..trait_args.len { if is_opaque(trait_args[i]) { return false, 0; } }
    let k = kind_of(t);
    let u = unqual(nonref(t));
    let ku = kind_of(u);
    // the class properties
    if name == "__is_trivial" || name == "__is_trivially_copyable" || name == "__is_standard_layout" || name == "__is_pod" ||
       name == "__is_aggregate" || name == "__is_literal_type" || name == "__is_literal" || name == "__has_trivial_destructor" ||
       name == "__has_trivial_constructor" || name == "__has_virtual_destructor" || name == "__is_empty" || name == "__is_polymorphic" ||
       name == "__is_abstract" || name == "__is_final" || name == "__is_sealed" || name == "__has_unique_object_representations" ||
       name == "__has_trivial_copy" || name == "__has_trivial_assign" || name == "__is_trivially_destructible" {
        return class_trait(name, t);
    }
    if name == "__is_base_of" {
        if n < 2 { return false, 0; }
        let b = unqual(trait_args[mark]);
        let d = unqual(trait_args[mark + 1]);
        if !is_record(b) || !is_record(d) { return true, 0; }
        if b == d { return true, 1; }
        need_complete(d);
        if records[rec_of(d)].flags & RF_COMPLETE == 0 { return false, 0; }
        return true, if base_offset(d, b) != -1 { 1 } else { 0 };
    }
    if name == "__is_convertible" || name == "__is_convertible_to" || name == "__is_nothrow_convertible" {
        if n < 2 { return false, 0; }
        let from = trait_args[mark];
        let to = trait_args[mark + 1];
        if is_void(from) || is_void(to) { return true, if is_void(from) && is_void(to) { 1 } else { 0 }; }
        if is_func(to) || is_array(to) { return true, 0; }
        let e = trait_probe(if is_ref(from) { from } else { mk_rref(from) });
        let c = ics_of(e, to, CV_COPY);
        if c.flags & IF_UNKNOWN != 0 { return false, 0; }
        if c.kind as i64 == ICS_BAD || c.kind as i64 == ICS_AMBIG { return true, 0; }
        if name == "__is_nothrow_convertible" && c.kind as i64 == ICS_USER { return true, if c.user >= 0 && cxs[c.user].flags & CF_NOEXCEPT != 0 { 1 } else { 0 }; }
        return true, 1;
    }
    if name == "__is_constructible" || name == "__is_trivially_constructible" || name == "__is_nothrow_constructible" {
        return constructible_trait(name, mark);
    }
    if name == "__is_assignable" || name == "__is_trivially_assignable" || name == "__is_nothrow_assignable" {
        if n < 2 { return false, 0; }
        return assignable_trait(name, trait_args[mark], trait_args[mark + 1]);
    }
    if name == "__is_destructible" || name == "__is_nothrow_destructible" {
        if is_ref(t) { return true, 1; }
        if is_void(t) || is_func(t) || (is_array(t) && types[t >> 4].n < 0) { return true, 0; }
        var b = t;
        while is_array(b) { b = tbase(b); }
        if !is_record(b) { return true, 1; }
        need_complete(b);
        return true, 1;
    }
    if name == "__is_bounded_array" { return true, if k == TY_ARRAY && types[t >> 4].n >= 0 { 1 } else { 0 }; }
    if name == "__is_unbounded_array" { return true, if k == TY_ARRAY && types[t >> 4].n < 0 { 1 } else { 0 }; }
    if name == "__is_nullptr" { return true, if kind_of(unqual(t)) == TY_NULLPTR { 1 } else { 0 }; }
    if name == "__is_object" { return true, if !is_ref(t) && !is_func(t) && !is_void(t) { 1 } else { 0 }; }
    if name == "__is_scalar" { return true, if is_arith(u) || ku == TY_ENUM || ku == TY_POINTER || ku == TY_MEMPTR || ku == TY_NULLPTR { 1 } else { 0 }; }
    if name == "__is_fundamental" { return true, if is_arith(u) || ku == TY_VOID || ku == TY_NULLPTR || ku == TY_BOOL { 1 } else { 0 }; }
    if name == "__is_compound" { return true, if !(is_arith(u) || ku == TY_VOID || ku == TY_NULLPTR || ku == TY_BOOL) { 1 } else { 0 }; }
    if name == "__is_member_object_pointer" { return true, if ku == TY_MEMPTR && !is_func(tbase(u)) { 1 } else { 0 }; }
    if name == "__is_member_function_pointer" { return true, if ku == TY_MEMPTR && is_func(tbase(u)) { 1 } else { 0 }; }
    if name == "__is_signed" { return true, if (is_cxx_integral(u) && is_signed(u) && ku != TY_BOOL) || is_real_float(u) { 1 } else { 0 }; }
    if name == "__is_unsigned" { return true, if is_cxx_integral(u) && !is_signed(u) || ku == TY_BOOL { 1 } else { 0 }; }
    if name == "__is_referenceable" { return true, 1; }
    if name == "__is_complete_type" { return true, if is_complete_or_void(t) { 1 } else { 0 }; }
    if name == "__array_rank" { var r = 0; var x = t; while is_array(x) { r++; x = tbase(x); } return true, r; }
    if name == "__array_extent" {
        var dim: i64 = 0;
        if n >= 2 { dim = 0; }
        var x = t;
        if !is_array(x) { return true, 0; }
        let nn = types[x >> 4].n;
        return true, if nn < 0 { 0 } else { nn };
    }
    if name == "__is_layout_compatible" || name == "__is_pointer_interconvertible_base_of" { return false, 0; }
    if name == "__reference_binds_to_temporary" || name == "__reference_constructs_from_temporary" || name == "__reference_converts_from_temporary" {
        if n < 2 || !is_ref(t) { return true, 0; }
        let e = trait_probe(if is_ref(trait_args[mark + 1]) { trait_args[mark + 1] } else { mk_rref(trait_args[mark + 1]) });
        let c = ics_of(e, t, if name == "__reference_converts_from_temporary" { CV_COPY } else { 0 });
        if c.flags & IF_UNKNOWN != 0 { return false, 0; }
        return true, if c.kind as i64 != ICS_BAD && c.flags & IF_TEMP != 0 { 1 } else { 0 };
    }
    return eval_trait(name, mark);
}

recursive fn class_trait(name: const u8[:], t: u32) -> bool, i64 {
    var b = unqual(t);
    // an array type is an aggregate (its element type need not be complete)
    if name == "__is_aggregate" && is_array(b) { return true, 1; }
    if name == "__is_trivial" || name == "__is_trivially_copyable" || name == "__is_pod" || name == "__is_standard_layout" ||
       name == "__is_literal_type" || name == "__is_literal" || name == "__has_unique_object_representations" {
        while is_array(b) { b = unqual(tbase(b)); }
    }
    if !is_record(b) {
        if is_ref(t) {
            let lit = name == "__is_literal_type" || name == "__is_literal";
            return true, if lit { 1 } else { 0 };
        }
        let scalar = is_arith(b) || kind_of(b) == TY_ENUM || kind_of(b) == TY_POINTER || kind_of(b) == TY_MEMPTR || kind_of(b) == TY_NULLPTR || kind_of(b) == TY_BOOL;
        if name == "__is_trivial" || name == "__is_trivially_copyable" || name == "__is_pod" || name == "__is_standard_layout" {
            return true, if scalar || kind_of(b) == TY_VECTOR { 1 } else { 0 };
        }
        if name == "__is_literal_type" || name == "__is_literal" { return true, if scalar || is_void(b) { 1 } else { 0 }; }
        if name == "__has_trivial_destructor" || name == "__is_trivially_destructible" || name == "__has_trivial_constructor" ||
           name == "__has_trivial_copy" || name == "__has_trivial_assign" {
            return true, if !is_void(b) && !is_func(b) { 1 } else { 0 };
        }
        if name == "__has_unique_object_representations" { return true, if is_cxx_integral(b) && kind_of(b) != TY_BOOL || kind_of(b) == TY_POINTER || kind_of(b) == TY_ENUM { 1 } else { 0 }; }
        return true, 0;
    }
    need_complete(b);
    let r = rec_of(b);
    if records[r].flags & RF_COMPLETE == 0 { return false, 0; }
    if name == "__is_empty" { return true, if crecs[r].flags & CR_EMPTY != 0 && kind_of(b) != TY_UNION { 1 } else { 0 }; }
    if name == "__is_polymorphic" { return true, if crecs[r].flags & CR_POLY != 0 { 1 } else { 0 }; }
    if name == "__is_abstract" { return true, if crecs[r].flags & CR_ABSTRACT != 0 { 1 } else { 0 }; }
    let p = class_props(r);
    if name == "__is_final" || name == "__is_sealed" { return true, if p & CP_FINAL != 0 { 1 } else { 0 }; }
    if p & CP_UNKNOWN != 0 { return false, 0; }
    if name == "__is_trivially_copyable" { return true, if p & CP_TRIV_COPYABLE != 0 { 1 } else { 0 }; }
    if name == "__is_trivial" { return true, if p & CP_TRIV_COPYABLE != 0 && p & CP_TRIV_DEF != 0 { 1 } else { 0 }; }
    if name == "__is_standard_layout" { return true, if p & CP_STD_LAYOUT != 0 { 1 } else { 0 }; }
    if name == "__is_pod" { return true, if p & CP_TRIV_COPYABLE != 0 && p & CP_TRIV_DEF != 0 && p & CP_STD_LAYOUT != 0 { 1 } else { 0 }; }
    if name == "__is_aggregate" { return true, if p & CP_AGGREGATE != 0 { 1 } else { 0 }; }
    if name == "__has_trivial_destructor" || name == "__is_trivially_destructible" { return true, if p & CP_TRIV_DTOR != 0 { 1 } else { 0 }; }
    if name == "__has_trivial_constructor" { return true, if p & CP_TRIV_DEF != 0 { 1 } else { 0 }; }
    if name == "__has_trivial_copy" { return true, if p & CP_TRIV_COPY != 0 { 1 } else { 0 }; }
    if name == "__has_trivial_assign" { return true, if p & CP_TRIV_CASG != 0 { 1 } else { 0 }; }
    if name == "__has_virtual_destructor" { return true, if p & CP_VIRT_DTOR != 0 { 1 } else { 0 }; }
    if name == "__is_literal_type" || name == "__is_literal" { return true, if p & CP_TRIV_DTOR != 0 && (p & CP_AGGREGATE != 0 || p & CP_TRIV_DEF != 0) { 1 } else { 0 }; }
    if name == "__has_unique_object_representations" { return false, 0; }
    return false, 0;
}

// __is_constructible(T, Args...): T t(declval<Args>()...); is well-formed.
recursive fn constructible_trait(name: const u8[:], mark: i64) -> bool, i64 {
    let t = trait_args[mark];
    let na = trait_args.len - mark - 1;
    let triv = name == "__is_trivially_constructible";
    let nothrow = name == "__is_nothrow_constructible";
    if is_void(t) || is_func(t) { return true, 0; }
    if is_array(t) {
        if types[t >> 4].n < 0 { return true, 0; }
        if na != 0 { return true, 0; }
    }
    for i in mark + 1..trait_args.len { if is_void(trait_args[i]) || is_func(trait_args[i]) && !is_ref(trait_args[i]) { if is_void(trait_args[i]) { return true, 0; } } }
    if is_ref(t) {
        if na != 1 { return true, 0; }
        let e = trait_probe(if is_ref(trait_args[mark + 1]) { trait_args[mark + 1] } else { mk_rref(trait_args[mark + 1]) });
        let c = ics_of(e, t, 0);
        if c.flags & IF_UNKNOWN != 0 { return false, 0; }
        if c.kind as i64 == ICS_BAD || c.kind as i64 == ICS_AMBIG { return true, 0; }
        if triv { return true, if c.kind as i64 == ICS_STD && c.flags & IF_TEMP == 0 { 1 } else { 0 }; }
        return true, 1;
    }
    var b = unqual(t);
    while is_array(b) { b = unqual(tbase(b)); }
    if !is_record(b) {
        if na == 0 { return true, 1; }
        if na > 1 { return true, 0; }
        let e = trait_probe(if is_ref(trait_args[mark + 1]) { trait_args[mark + 1] } else { mk_rref(trait_args[mark + 1]) });
        // a functional cast: static_cast-like conversions are allowed, explicit ones too
        let c = ics_of(e, b, 0);
        if c.flags & IF_UNKNOWN != 0 { return false, 0; }
        if c.kind as i64 == ICS_BAD || c.kind as i64 == ICS_AMBIG { return true, 0; }
        if triv { return true, if c.kind as i64 == ICS_STD { 1 } else { 0 }; }
        if nothrow && c.kind as i64 == ICS_USER { return true, if c.user >= 0 && cxs[c.user].flags & CF_NOEXCEPT != 0 { 1 } else { 0 }; }
        return true, 1;
    }
    need_complete(b);
    let r = rec_of(b);
    if records[r].flags & RF_COMPLETE == 0 { return false, 0; }
    let p = class_props(r);
    if p & CP_UNKNOWN != 0 { return false, 0; }
    if crecs[r].flags & CR_ABSTRACT != 0 { return true, 0; }
    // the copy/move of the same class
    if na == 1 {
        let a = trait_args[mark + 1];
        if unqual(nonref(a)) == b || (is_record(nonref(a)) && is_base_of(b, nonref(a))) {
            let rv = !is_ref(a) || kind_of(a) == TY_RREF;
            let user_copy = p & CP_HAS_COPY_DECL != 0;
            let user_move = p & CP_HAS_MOVE_DECL != 0;
            if !user_copy && !user_move && p & (CP_HAS_CASG_DECL | CP_HAS_MASG_DECL | CP_HAS_DTOR_DECL) == 0 {
                // the implicit copy and move constructors
                if triv { return true, if (if rv { p & CP_TRIV_MOVE } else { p & CP_TRIV_COPY }) != 0 { 1 } else { 0 }; }
                return true, 1;
            }
        }
    }
    if na == 0 {
        if p & CP_HAS_DEF == 0 { return true, 0; }
        if triv { return true, if p & CP_TRIV_DEF != 0 { 1 } else { 0 }; }
        if nothrow { return false, 0; }
        return true, 1;
    }
    // overload resolution among the constructors (direct-initialization)
    let sc = type_scope(b);
    if sc < 0 { return false, 0; }
    let s = scope_find(sc, id_ctor);
    if s < 0 {
        // the implicit ones only: an aggregate's or the copy/move
        return false, 0;
    }
    let m0 = nscratch.len;
    for i in mark + 1..trait_args.len {
        let a = trait_args[i];
        nscratch.push(trait_probe(if is_ref(a) { a } else { mk_rref(a) }));
    }
    let f = best_candidate(s, m0, false);
    let unk = cand_unknown;
    let nv = cand_nviable;
    nscratch.resize(m0);
    if f >= 0 {
        if triv { return true, if !user_provided_fn(f) && (p & CP_TRIV_COPY != 0) { 1 } else { 0 }; }
        if nothrow { return true, if cxs[f].flags & CF_NOEXCEPT != 0 { 1 } else { 0 }; }
        return true, 1;
    }
    if unk { return false, 0; }
    if nv == 0 && !cand_deleted && !cand_ambiguous {
        // the implicit copy/move constructors are not in the scope's chain
        if na == 1 {
            let a = trait_args[mark + 1];
            if unqual(nonref(a)) == b { return false, 0; }
        }
        return true, 0;
    }
    return true, 0;
}

// __is_assignable(T, U): declval<T>() = declval<U>() is well-formed.
recursive fn assignable_trait(name: const u8[:], t: u32, a: u32) -> bool, i64 {
    let triv = name == "__is_trivially_assignable";
    let nothrow = name == "__is_nothrow_assignable";
    if is_void(t) || is_void(a) || is_func(nonref(t)) { return true, 0; }
    let l = trait_probe(if is_ref(t) { t } else { mk_rref(t) });
    let r = trait_probe(if is_ref(a) { a } else { mk_rref(a) });
    let lt = nonref(t);
    if !is_record(lt) {
        // a built-in assignment: a modifiable lvalue on the left
        if !is_lvalue(l) || nodes[l].flags & NF_XVALUE != 0 { return true, 0; }
        if quals(lt) & Q_CONST != 0 || is_array(lt) { return true, 0; }
        if is_record(nonref(a)) {
            let c = ics_of(r, unqual(lt), CV_COPY);
            if c.flags & IF_UNKNOWN != 0 { return false, 0; }
            if c.kind as i64 == ICS_BAD { return true, 0; }
            return true, if triv { 0 } else { 1 };
        }
        let c = ics_of(r, unqual(lt), CV_COPY);
        if c.flags & IF_UNKNOWN != 0 { return false, 0; }
        return true, if c.kind as i64 != ICS_BAD { 1 } else { 0 };
    }
    need_complete(lt);
    let rr = rec_of(lt);
    let p = class_props(rr);
    if p & CP_UNKNOWN != 0 { return false, 0; }
    let sc = type_scope(lt);
    if sc < 0 { return false, 0; }
    let s = class_lookup(sc, op_ids[OP_EQUAL]);
    let same = unqual(nonref(a)) == unqual(lt);
    if s < 0 || p & (CP_HAS_CASG_DECL | CP_HAS_MASG_DECL) == 0 {
        // the implicit copy/move assignment
        if quals(lt) & Q_CONST != 0 { return true, 0; }
        if same || (is_record(nonref(a)) && is_base_of(lt, nonref(a))) {
            if triv { return true, if p & CP_TRIV_CASG != 0 { 1 } else { 0 }; }
            return true, 1;
        }
        if s < 0 {
            let c = ics_of(r, mk_lref(with_q(unqual(lt), Q_CONST)), CV_COPY);
            if c.flags & IF_UNKNOWN != 0 { return false, 0; }
            return true, if c.kind as i64 != ICS_BAD && !triv { 1 } else { 0 };
        }
    }
    let m0 = nscratch.len;
    nscratch.push(r);
    cand_obj = l;
    let f = best_candidate(s, m0, true);
    let unk = cand_unknown;
    nscratch.resize(m0);
    if f >= 0 {
        if triv { return true, if !user_provided_fn(f) && p & CP_TRIV_CASG != 0 { 1 } else { 0 }; }
        if nothrow { return true, if cxs[f].flags & CF_NOEXCEPT != 0 { 1 } else { 0 }; }
        return true, 1;
    }
    if unk { return false, 0; }
    return true, 0;
}
