// goosecc B5: the types of declarations as they are written, for -g.
//
// The front end's types are canonical (DESIGN.md 2: a typedef name is not
// a type), but DWARF names typedefs, as clang's debug information does
// from its sugared QualTypes. So with -g the parser builds, next to the
// canonical type of every declaration, its "written type", a dq:
//
//   bit 31 clear: a canonical qtype (nothing in it was written with a
//                 typedef name, typeof or __auto_type);
//   bit 31 set:   (node << 4) | qualifiers, a node of `dtypes`: a typedef
//                 name, or a pointer, array or function type built over a
//                 written type.
//
// Nodes are uniqued, so equal written types have equal dqs (clang's
// QualTypes are uniqued the same way, and its debug types are cached by
// them). Without -g nothing here is filled (dbg_types is false).
//
// The side tables: the written type of each symbol (variables, parameters,
// typedefs, functions), of each member, of each declaration (N_DECL: a
// file-scope object may be declared several times with different
// spellings, and DWARF uses its definition's), of each explicit cast (clang
// keeps the types of casts in the debug information); the function each
// block-scope record, enum and typedef belongs to (DWARF puts them in the
// subprogram); the enumerators of each enum; which integer constants are
// references to enumerators.

import std;
import dictionary;
import .common;
import .types;
import .ast;

let DQ_SUGAR: u32 = 0x80000000;
let DK_TYPEDEF = 1;    // sym: the typedef symbol; canon: its type
let DK_PTR = 2;        // base: the pointee
let DK_ARRAY = 3;      // base: the element, n: the length (-1: incomplete)
let DK_VLA = 4;        // base: the element, canon: the canonical TY_VLA type (its size expression)
let DK_FUNC = 5;       // base: the return type, n: params at dparams[extra ..], flags: TF_*
let DK_VECTOR = 6;     // base: the element; canon: the canonical vector type

struct DType { kind: u8, flags: u8, rsv: u16, base: u32, sym: u32, extra: u32, n: i64, canon: u32, hnext: i32 }
var dtypes: DType[>..] = [];
var dparams: u32[>..] = [];
var dhash: i32[>..<] = [];
var dmask: i64 = 0;
var dscratch: u32[>..<] = [];        // the parameters of a function type being built

var dbg_types: bool = false;         // -g (or __PRETTY_FUNCTION__): build the written types
var dbg_g: bool = false;             // -g itself: what only debug information may change

inline fn dq_sugar(d: u32) -> bool { d & DQ_SUGAR != 0 }
inline fn dq_node(d: u32) -> i64 { ((d & 0x7FFFFFFF) >> 4) as i64 }
inline fn dq_quals(d: u32) -> i64 { (d & 15) as i64 }

fn dt_grow() {
    let n = if dhash.len == 0 { 1024 } else { dhash.len * 2 };
    dhash.clear();
    dhash.resize(n, -1);
    dmask = n - 1;
    if dtypes.len == 0 { dtypes.push(DType { kind: 0, flags: 0, rsv: 0, base: 0, sym: 0, extra: 0, n: 0, canon: 0, hnext: -1 }); }
    for t, i in dtypes {
        if i == 0 { continue; }
        let b = (dt_hash(t.kind as i64, t.flags as i64, t.base, t.sym, t.n, dt_extra_key(t.kind as i64, t.extra, t.n)) as! i64) & dmask;
        dtypes[i].hnext = dhash[b];
        dhash[b] = i as! i32;
    }
}

fn dt_hash(kind: i64, flags: i64, base: u32, sym: u32, n: i64, ex: u32) -> u64 {
    var h: u64 = (kind as! u64) * 1000003;
    h = (h ^ (flags as! u64)) * 1099511628211;
    h = (h ^ (base as u64)) * 1099511628211;
    h = (h ^ (sym as u64)) * 1099511628211;
    h = (h ^ (n as! u64)) * 1099511628211;
    h = (h ^ (ex as u64)) * 1099511628211;
    return h ^ (h >> 29);
}

// A function node is keyed by its parameters, not by where they are stored.
fn dt_extra_key(kind: i64, extra: u32, n: i64) -> u32 {
    if kind != DK_FUNC { return extra; }
    var h: u64 = 7;
    for i in n { h = (h ^ (dparams[extra as i64 + i] as u64)) * 1099511628211; }
    return (h ^ (h >> 32)) as! u32;
}

// The node (kind, flags, base, sym, n, extra); for DK_FUNC the parameters are
// dscratch[pmark ..]. Returns its dq without qualifiers.
fn dt_node(kind: i64, flags: i64, base: u32, sym: u32, n0: i64, extra: u32, canon: u32, pmark: i64) -> u32 {
    if (dtypes.len + 1) * 2 > dhash.len { dt_grow(); }
    var n = n0;
    var ex = extra;
    if kind == DK_FUNC {
        n = dscratch.len - pmark;
        var h: u64 = 7;
        for k in pmark..dscratch.len { h = (h ^ (dscratch[k] as u64)) * 1099511628211; }
        ex = (h ^ (h >> 32)) as! u32;
    }
    let b = (dt_hash(kind, flags, base, sym, n, ex) as! i64) & dmask;
    var i = dhash[b] as i64;
    while i >= 0 {
        let t = dtypes[i];
        if t.kind as i64 == kind && t.flags as i64 == flags && t.base == base && t.sym == sym && t.n == n && t.canon == canon {
            if kind != DK_FUNC {
                if t.extra == extra { return DQ_SUGAR | ((i as! u32) << 4); }
            } else {
                var same = true;
                for k in n { if dparams[t.extra as i64 + k] != dscratch[pmark + k] { same = false; break; } }
                if same { return DQ_SUGAR | ((i as! u32) << 4); }
            }
        }
        i = t.hnext as i64;
    }
    let id = dtypes.len;
    var e = extra;
    if kind == DK_FUNC {
        e = dparams.len as! u32;
        for k in pmark..dscratch.len { dparams.push(dscratch[k]); }
    }
    dtypes.push(DType { kind: kind as! u8, flags: flags as! u8, rsv: 0, base: base, sym: sym, extra: e, n: n, canon: canon, hnext: dhash[b] });
    dhash[b] = id as! i32;
    return DQ_SUGAR | ((id as! u32) << 4);
}

// The canonical type of a written type.
fn dq_canon(d: u32) -> u32 {
    if !dq_sugar(d) { return d; }
    return with_quals(dtypes[dq_node(d)].canon, dq_quals(d));
}

// Adds qualifiers.
fn d_quals(d: u32, q: i64) -> u32 {
    if q == 0 { return d; }
    if !dq_sugar(d) { return with_quals(d, q); }
    return d | ((q & 15) as! u32);
}

fn d_unqual(d: u32) -> u32 {
    if !dq_sugar(d) { return unqual(d); }
    return d & 0xFFFFFFF0;
}

// A use of typedef name s.
fn d_typedef(s: i64, ty: u32) -> u32 {
    if !dbg_types { return ty; }
    return dt_node(DK_TYPEDEF, 0, 0, s as! u32, 0, 0, ty, 0);
}

// The constructors take the canonical type the parser made (cres) and
// return it when nothing in the written type is sugar.
fn d_ptr(base: u32, cres: u32) -> u32 {
    if !dq_sugar(base) { return cres; }
    return dt_node(DK_PTR, 0, base, 0, 0, 0, unqual(cres), 0) | ((quals(cres) & 15) as! u32);
}

fn d_array(base: u32, n: i64, cres: u32) -> u32 {
    if !dq_sugar(base) { return cres; }
    return dt_node(DK_ARRAY, 0, base, 0, n, 0, unqual(cres), 0);
}

fn d_vla(base: u32, cres: u32) -> u32 {
    if !dq_sugar(base) { return cres; }
    return dt_node(DK_VLA, 0, base, 0, 0, 0, unqual(cres), 0);
}

// A function type: the parameters' written types are in dscratch[mark ..],
// which is cut back to mark.
fn d_func(ret: u32, mark: i64, flags: i64, cres: u32) -> u32 {
    var any = dq_sugar(ret);
    for k in mark..dscratch.len { if dq_sugar(dscratch[k]) { any = true; } }
    var r = cres;
    if any { r = dt_node(DK_FUNC, flags, ret, 0, 0, 0, unqual(cres), mark); }
    dscratch.resize(mark);
    return r;
}

// A written type after attributes changed the canonical type (vector_size,
// mode, aligned on a declarator): the sugar no longer applies.
fn d_after(d: u32, before: u32, after: u32) -> u32 {
    if after == before { return d; }
    // vector_size / ext_vector_type of a written type: a vector of it
    let k = kind_of(after);
    if dq_sugar(d) && (k == TY_VECTOR || k == TY_EXTVECTOR) && unqual(tbase(after)) == unqual(before) {
        return dt_node(DK_VECTOR, 0, d_unqual(d), 0, 0, 0, unqual(after), 0) | ((quals(after) & 15) as! u32);
    }
    return after;
}

// Through typedef names to a node that is not one (the qualifiers of the
// typedef names collected).
fn d_desugar(d0: u32) -> u32 {
    var d = d0;
    var q = dq_quals(d0);
    while dq_sugar(d) && dtypes[dq_node(d)].kind as i64 == DK_TYPEDEF {
        let t = dtypes[dq_node(d)];
        let w = sym_written(t.sym as i64);
        d = if w != 0 { w } else { t.canon };
        q = q | dq_quals(d);
    }
    if !dq_sugar(d) { return with_quals(d, q); }
    return (d & 0xFFFFFFF0) | (q as! u32);
}

// The element of a written array type (clang's getAsArrayType: through
// typedef names; the array's qualifiers go to the element).
fn d_elem(d: u32, canon_elem: u32) -> u32 {
    let a = d_desugar(d);
    if !dq_sugar(a) { return canon_elem; }
    let t = dtypes[dq_node(a)];
    if t.kind as i64 != DK_ARRAY && t.kind as i64 != DK_VLA { return canon_elem; }
    return d_quals(t.base, dq_quals(a));
}

// The parameter adjustment (C11 6.7.6.3p7-8) of a written type, given the
// canonical types before and after it.
fn d_adjust_param(d: u32, before: u32, after: u32) -> u32 {
    if after == before { return d; }
    if !dq_sugar(d) { return after; }
    if is_array(before) { return d_ptr(d_elem(d, tbase(before)), after); }
    if is_func(before) { return d_ptr(d, after); }
    return after;
}

// ------------------------------------------------------------ side tables

var sym_dty: u32[>..] = [];          // per symbol: its written type, 0 = its canonical type
var fld_dty: u32[>..] = [];          // per member
var node_dty = dictionary<u64, u32> {};   // N_DECL and N_CAST nodes
var enumc_ref = dictionary<u64, u32> {};  // integer constants that name an enumerator: the symbol
var rec_fn: i32[>..] = [];           // per record: the function it is declared in (-1: file scope)
var enum_fn: i32[>..] = [];          // per enum
var tdef_fn = dictionary<u64, u32> {};    // typedef symbol -> the function it is declared in
var fn_proto = dictionary<u64, u32> {};   // function symbol -> 1 if its definition has a prototype
var enum_c0: u32[>..] = [];          // per enum: its enumerators, enum_csyms[enum_c0 .. enum_c0 + enum_cn]
var enum_cn: u32[>..] = [];
var enum_csyms: u32[>..] = [];

fn sym_written(s: i64) -> u32 {
    if s < sym_dty.len && sym_dty[s] != 0 { return sym_dty[s]; }
    return 0;
}

fn dt_set_sym(s: i64, d: u32) {
    if !dbg_types { return; }
    while sym_dty.len <= s { sym_dty.push(0); }
    sym_dty[s] = d;
}

fn dt_set_field(f: i64, d: u32) {
    if !dbg_types { return; }
    while fld_dty.len <= f { fld_dty.push(0); }
    fld_dty[f] = d;
}

fn field_written(f: i64) -> u32 {
    if f < fld_dty.len && fld_dty[f] != 0 { return fld_dty[f]; }
    return 0;
}

fn dt_set_node(n: u32, d: u32) {
    if !dbg_types { return; }
    node_dty.insert(n as u64, d);
}

fn node_written(n: u32) -> u32 {
    let r = node_dty.get(n as u64);
    if r { return r; }
    return 0;
}

fn dt_note_record(r: i64, func: i64) {
    if !dbg_types { return; }
    while rec_fn.len <= r { rec_fn.push(-1); }
    rec_fn[r] = func as! i32;
}

fn dt_note_enum(e: i64, func: i64) {
    if !dbg_types { return; }
    while enum_fn.len <= e { enum_fn.push(-1); }
    enum_fn[e] = func as! i32;
}

fn record_func(r: i64) -> i64 { if r < rec_fn.len { rec_fn[r] as i64 } else { -1 } }
fn enum_func(e: i64) -> i64 { if e < enum_fn.len { enum_fn[e] as i64 } else { -1 } }

fn dt_note_typedef(s: i64, func: i64) {
    if !dbg_types || func < 0 { return; }
    tdef_fn.insert(s as u64, func as! u32);
}

fn typedef_func(s: i64) -> i64 {
    let r = tdef_fn.get(s as u64);
    if r { return r as i64; }
    return -1;
}

fn dt_note_proto(s: i64, proto: bool) {
    if !dbg_types { return; }
    fn_proto.insert(s as u64, if proto { 1 } else { 2 });
}

fn fn_proto_known(s: i64) -> bool {
    let r = fn_proto.get(s as u64);
    if r { return true; }
    return false;
}

fn func_prototyped(s: i64) -> bool {
    let r = fn_proto.get(s as u64);
    if r { return r == 1; }
    return true;
}

fn dt_note_enumerators(e: i64, syms_: const u32[:]) {
    if !dbg_types { return; }
    while enum_c0.len <= e { enum_c0.push(0); enum_cn.push(0); }
    enum_c0[e] = enum_csyms.len as! u32;
    enum_cn[e] = syms_.len as! u32;
    for s in syms_ {
        enum_csyms.push(s);
        enumc_enum.insert(s as u64, e as! u32);
    }
}

fn dt_note_enumc(n: u32, s: i64) {
    if !dbg_types { return; }
    enumc_ref.insert(n as u64, s as! u32);
}

fn enumc_of(n: u32) -> i64 {
    let r = enumc_ref.get(n as u64);
    if r { return r as i64; }
    return -1;
}

// File-scope declarations written with `extern` (not tentative definitions).
var decl_extern = dictionary<u64, u32> {};
fn dt_note_extern(n: u32) {
    if !dbg_types { return; }
    decl_extern.insert(n as u64, 1);
}
fn decl_is_extern(n: u32) -> bool {
    let r = decl_extern.get(n as u64);
    if r { return true; }
    return false;
}

// The enum of each enumerator.
var enumc_enum = dictionary<u64, u32> {};
fn enumc_owner(s: i64) -> i64 {
    let r = enumc_enum.get(s as u64);
    if r { return r as i64; }
    return -1;
}

// The record an unnamed struct, union or enum is declared in (clang puts
// it in that record's DIE; a named one is in the enclosing function or the
// unit, as C scopes tags).
var rec_in_rec: i32[>..] = [];       // per record: the enclosing record (-1)
var enum_in_rec: i32[>..] = [];      // per enum
var cur_rec: i64 = -1;               // the record whose members are being parsed
fn dt_note_record_in(r: i64) {
    if !dbg_types || cur_rec < 0 { return; }
    while rec_in_rec.len <= r { rec_in_rec.push(-1); }
    rec_in_rec[r] = cur_rec as! i32;
}
fn dt_note_enum_in(e: i64) {
    if !dbg_types || cur_rec < 0 { return; }
    while enum_in_rec.len <= e { enum_in_rec.push(-1); }
    enum_in_rec[e] = cur_rec as! i32;
}
fn record_in_record(r: i64) -> i64 { if r < rec_in_rec.len { rec_in_rec[r] as i64 } else { -1 } }
fn enum_in_record(e: i64) -> i64 { if e < enum_in_rec.len { enum_in_rec[e] as i64 } else { -1 } }

// Labels declared with __label__ (DWARF puts them at that declaration).
var local_labels = dictionary<u64, u32> {};
fn dt_note_local_label(s: i64, loc: u32) {
    if !dbg_types { return; }
    local_labels.insert(s as u64, loc);
}
fn local_label_loc(s: i64, dflt: u32) -> u32 {
    let r = local_labels.get(s as u64);
    if r { return r; }
    return dflt;
}

// ------------------------------------------------------------ __PRETTY_FUNCTION__
//
// clang's PredefinedExpr::ComputeName(PrettyFunction) in C: the function's
// return type printed (TypePrinter) around "name(parameter types)", with the
// types as written: typedef names, the parameters as adjusted (arrays and
// functions to pointers), "()" without a written prototype, "(void)" for no
// parameters. The written types are those of the definition's declarator,
// which a translation unit that uses __PRETTY_FUNCTION__ records without -g
// too (pf_scan): only the side tables, nothing that changes the code.

var pf_dty: u32 = 0;                 // the written type of the function being defined
var pf_ph: u8[>..] = [];

fn pretty_function(out: u8[>..]&, s: i64) {
    let d = if pf_dty != 0 { pf_dty } else { syms[s].ty };
    pf_ph.clear();
    pf_ph.append(ident_text(syms[s].name as i64));
    pf_ph.push('(');
    pf_params(pf_ph, d);
    pf_ph.push(')');
    var ret: u32 = 0;
    if dq_sugar(d) && dtypes[dq_node(d)].kind as i64 == DK_FUNC { ret = dtypes[dq_node(d)].base; }
    else { ret = types[dq_canon(d) >> 4].base; }
    pf_before(out, ret, false);
    out.append(pf_ph);
    pf_after(out, ret, false);
}

// What a written type is for printing: 0 a name (builtin, tag, typedef),
// 1 pointer, 2 array, 3 incomplete array, 4 VLA, 5 function; its base type;
// an array's length.
fn pf_class(d: u32) -> i64, u32, i64 {
    if dq_sugar(d) {
        let t = dtypes[dq_node(d)];
        let k = t.kind as i64;
        if k == DK_PTR { return 1, t.base, 0; }
        if k == DK_ARRAY {
            let c = if t.n < 0 { 3 } else { 2 };
            return c, t.base, t.n;
        }
        if k == DK_VLA { return 4, t.base, 0; }
        if k == DK_FUNC { return 5, t.base, 0; }
        return 0, 0, 0;
    }
    let k = kind_of(d);
    if k == TY_POINTER { return 1, tbase(d), 0; }
    if k == TY_ARRAY {
        let n = types[d >> 4].n;
        let c = if n < 0 { 3 } else { 2 };
        return c, tbase(d), n;
    }
    if k == TY_VLA { return 4, tbase(d), 0; }
    if k == TY_FUNC { return 5, types[d >> 4].base, 0; }
    return 0, 0, 0;
}

fn pf_qual(d: u32) -> i64 {
    if dq_sugar(d) { return dq_quals(d); }
    return quals(d);
}

// Qualifiers::print: const volatile restrict.
fn pf_quals(out: u8[>..]&, q: i64) {
    var any = false;
    if q & Q_CONST != 0 { out.append("const"); any = true; }
    if q & Q_VOLATILE != 0 {
        if any { out.push(' '); }
        out.append("volatile");
        any = true;
    }
    if q & Q_RESTRICT != 0 {
        if any { out.push(' '); }
        out.append("restrict");
    }
}

// A name: a typedef name, or the canonical type's.
fn pf_name(out: u8[>..]&, d: u32) {
    var u = unqual(d);
    if dq_sugar(d) {
        let t = dtypes[dq_node(d)];
        if t.kind as i64 == DK_TYPEDEF {
            out.append(ident_text(syms[t.sym].name as i64));
            return;
        }
        u = unqual(t.canon);
    }
    if kind_of(u) == TY_VECTOR {
        let v = types[u >> 4];
        format(out, "__attribute__((__vector_size__(", v.n, " * sizeof(");
        base_name(out, v.base);
        out.append(")))) ");
        base_name(out, v.base);
        return;
    }
    base_name(out, u);
}

// TypePrinter::printBefore / printAfter; `empty`: the placeholder is empty.
recursive fn pf_before(out: u8[>..]&, d: u32, empty: bool) {
    let k, b, n = pf_class(d);
    let q = pf_qual(d) & (Q_CONST | Q_VOLATILE | Q_RESTRICT);
    if k == 0 {
        if q != 0 {
            pf_quals(out, q);
            out.push(' ');
        }
        if pf_qual(d) & Q_ATOMIC != 0 {
            out.append("_Atomic(");
            pf_name(out, d);
            out.push(')');
        } else {
            pf_name(out, d);
        }
        if !empty { out.push(' '); }
        return;
    }
    if k == 1 {
        pf_before(out, b, false);
        let bk, bb, bn = pf_class(b);
        if bk >= 2 && bk <= 4 { out.push('('); }
        out.push('*');
        if q != 0 {
            pf_quals(out, q);
            if !empty { out.push(' '); }
        }
        return;
    }
    if k == 5 {
        pf_before(out, b, false);
        if !empty { out.push('('); }
        return;
    }
    pf_before(out, b, empty);
}

recursive fn pf_after(out: u8[>..]&, d: u32, empty: bool) {
    let k, b, n = pf_class(d);
    if k == 1 {
        let bk, bb, bn = pf_class(b);
        if bk >= 2 && bk <= 4 { out.push(')'); }
        pf_after(out, b, false);
        return;
    }
    if k == 2 || k == 3 || k == 4 {
        out.push('[');
        if k == 2 { format(out, n); } else if k == 4 { out.push('*'); }
        out.push(']');
        pf_after(out, b, empty);
        return;
    }
    if k == 5 {
        if !empty { out.push(')'); }
        out.push('(');
        pf_params(out, d);
        out.push(')');
        pf_after(out, b, false);
    }
}

// The parameter types of function type d: none without a prototype.
recursive fn pf_params(out: u8[>..]&, d: u32) {
    var np: i64 = 0;
    var flags: i64 = 0;
    var sugar = false;
    var at: i64 = 0;
    if dq_sugar(d) && dtypes[dq_node(d)].kind as i64 == DK_FUNC {
        let t = dtypes[dq_node(d)];
        np = t.n;
        flags = t.flags as i64;
        sugar = true;
        at = t.extra as i64;
    } else {
        let ft = types[dq_canon(d) >> 4];
        np = ft.n as i64;
        flags = ft.flags as i64;
        at = ft.extra as i64;
    }
    if flags & TF_NOPROTO != 0 { return; }
    for i in np {
        if i > 0 { out.append(", "); }
        let p = if sugar { dparams[at + i] } else { tparams[at + i] };
        pf_before(out, p, true);
        pf_after(out, p, true);
    }
    if flags & TF_VARIADIC != 0 { out.append(if np > 0 { ", ..." } else { "..." }); }
    else if np == 0 { out.append("void"); }
}

// Where an enum was defined (it may have been named before: enum foo; ...).
var enum_defloc = dictionary<u64, u32> {};
fn dt_note_enum_def(e: i64, loc: u32) {
    if !dbg_types { return; }
    enum_defloc.insert(e as u64, loc);
}
fn enum_def_loc(e: i64, dflt: u32) -> u32 {
    let r = enum_defloc.get(e as u64);
    if r { return r; }
    return dflt;
}
