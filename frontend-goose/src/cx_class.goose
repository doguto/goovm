// goosecc D1: C++ classes and enums: class-specifiers (bases, members,
// access, the injected-class-name, nested classes, friends), the
// deferred parts of a class (member function bodies, default arguments
// and default member initializers, parsed once the outermost class is
// complete), and enum-specifiers (scoped, fixed underlying types).

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
import .cx_core;
import .cx_names;
import .cx_decl;
import .cx_layout;

// Members under construction: one stack for all classes being defined
// (a nested class's members sit above its outer class's).
var cfscratch: Field[>..<] = [];
var cbscratch: Base[>..<] = [];

// Deferred member function bodies of the outermost class being defined:
// (function symbol, class scope) pairs; the body tokens are in cxs.
var deferred: u32[>..<] = [];
var class_nest: i64 = 0;

fn new_record_cx(name: u32, is_union: bool, loc: u32) -> i64 {
    let r = records.len;
    let ty = mk_tagged(if is_union { TY_UNION } else { TY_STRUCT }, r as! u32);
    records.push(Record { name: name, ty: ty, first: 0, count: 0, size: -1, align: 1, flags: if is_union { RF_UNION } else { 0 },
        rsv: 0, attr_align: 0, pack: 0, loc: loc, scope: 0 });
    crec_grow();
    return r;
}

// The class symbol, its scope and the injected-class-name for record r.
fn class_setup(r: i64, s: i64, parent_scope: i64) -> i64 {
    let sc = new_scope(CS_CLASS, parent_scope, s, records[r].name);
    scopes[sc].rec = r as! i32;
    crecs[r].sym = s as! i32;
    crecs[r].scope = sc as! i32;
    if records[r].name != 0 {
        let inj = csym(SK_TAG, records[r].name, records[r].ty << 4, records[r].loc);
        cxs[inj].flags = CF_INJECTED;
        cxs[inj].target = s as! i32;
        scope_add(sc, inj);
    }
    return sc;
}

// The scope declarations of new names go to for an elaborated-type-specifier
// that declares (C++ [basic.scope.pdecl]p7): the innermost enclosing
// namespace or block (not a class or a function prototype scope).
fn elab_decl_scope() -> i64 {
    var sc = cur_scope;
    while scopes[sc].kind as i64 == CS_CLASS || scopes[sc].kind as i64 == CS_ENUM { sc = scopes[sc].parent as i64; }
    return sc;
}

// Declares a new tag (class/struct/union) named `name` in the current
// scope (or block scope): its symbol.
fn declare_tag(name: u32, is_union: bool, loc: u32, in_block: bool, sc: i64) -> i64 {
    let r = new_record_cx(name, is_union, loc);
    let s = csym(SK_TAG, name, records[r].ty << 4, loc);
    syms[s].v = records[r].ty as i64;
    if in_block {
        cx_grow();
        cxs[s].dscope = sc as! i32;
        bind_sym(s, true);
    } else {
        scope_add(sc, s);
    }
    class_setup(r, s, sc);
    return s;
}

// The tag symbol a name refers to in the current scope only (for
// redeclarations), or -1.
fn tag_in_scope(sc: i64, name: u32, in_block: bool) -> i64 {
    if in_block {
        if name as i64 >= id_bind.len { return -1; }
        let t = id_bind[name].tag as i64;
        if t >= 0 && syms[t].scope as i64 == scope_depth { return t; }
        return -1;
    }
    var s = scope_find(sc, name);
    while s >= 0 {
        let r = resolve(s);
        if r >= 0 && (syms[r].kind as i64 == SK_TAG) && cxs[r].flags & CF_INJECTED == 0 { return r; }
        if r >= 0 && syms[r].kind as i64 == SK_TEMPLATE && tmpl_kind(r) == TT_CLASS { return r; }
        s = cxs[s].nnext as i64;
    }
    return -1;
}

fn in_block_scope() -> bool { scope_depth > 0 && scope_depth >= local_floor && cur_class < 0 && block_fn_depth > 0 }
var block_fn_depth: i64 = 0;    // function bodies being parsed

// class-specifier or elaborated-type-specifier at `struct`/`class`/`union`.
recursive fn parse_class_spec(ds: CDS&, w: i64, ctx: i64) -> u32 {
    let loc = tloc();
    let is_union = w == KW_UNION;
    adv();
    var ca = Attrs { .. };
    cx_attrs(ca);
    // the name
    var qn = QN { .. };
    var has_name = false;
    if at(TK_IDENT) || at(TK_COLONCOLON) {
        let sv = save();
        diag_suppress++;
        has_name = parse_qname(qn);
        diag_suppress--;
        if !has_name || qn.kind as i64 != QK_IDENT { restore(sv); has_name = false; }
    }
    cx_attrs(ca);
    var is_final = false;
    if at(TK_IDENT) && tu_toks[pc].val == id_final && (tk_n(1) == TK_L_BRACE || tk_n(1) == TK_COLON) {
        adv();
        is_final = true;
    }
    let is_def = at(TK_L_BRACE) || (at(TK_COLON) && ctx != DC_CLASS_BITFIELD_NEVER);
    let in_block = in_block_scope();
    if !is_def {
        // an elaborated-type-specifier
        ds.tag_decl = true;
        if !has_name { perr_expected("a class name"); return t_unknown; }
        if qn.has_targs {
            // class X<args>: a specialization (explicit instantiation or
            // explicit specialization declared without a body)
            lookup_qn(qn);
            let t = qn_type(qn);
            ds.tag_ty = if t == 0 { t_unknown } else { t };
            note_spec_decl(qn);
            return ds.tag_ty;
        }
        if qn.qual {
            lookup_qn(qn);
            let t = qn_type(qn);
            if t == 0 { return t_unknown; }
            return t;
        }
        // class X; declares X in this scope; class X *p finds or declares it
        let sc = if at(TK_SEMI) && !ds.is_friend { cur_scope } else { elab_decl_scope() };
        if at(TK_SEMI) && !ds.is_friend {
            let s = tag_in_scope(cur_scope, qn.name, in_block);
            if s >= 0 { return tag_type_of(s); }
            if pending_tmpl >= 0 { return declare_class_template(qn.name, is_union, loc, false); }
            let ns = declare_tag(qn.name, is_union, loc, in_block, cur_scope);
            return syms[ns].ty;
        }
        lookup_qn(qn);
        let found = chain_type(qn.sym as i64);
        if found >= 0 { return tag_type_of(found); }
        if ds.is_friend {
            // friend class X: names a class of the enclosing namespace, not found by lookup
            if pending_tmpl >= 0 { return t_unknown; }
            let ns = declare_tag(qn.name, is_union, loc, false, elab_decl_scope());
            cxs[ns].flags = cxs[ns].flags | CF_FRIEND;
            return syms[ns].ty;
        }
        let ns = declare_tag(qn.name, is_union, loc, in_block, sc);
        return syms[ns].ty;
    }
    // a definition
    ds.tag_def = true;
    var s: i64 = -1;
    var r: i64 = -1;
    var sc = -1;
    var defining_pattern = false;
    if has_name && qn.has_targs {
        // an explicit or partial specialization: template<...> struct X<args> { }
        s = begin_class_specialization(qn, is_union, loc);
        r = rec_of(syms[s].ty);
    } else if has_name && qn.qual {
        lookup_qn(qn);
        let f = chain_type(qn.sym as i64);
        if f >= 0 && syms[f].kind as i64 == SK_TEMPLATE {
            // template<class T> struct Outer<T>::Inner<U> ... : define the member template's pattern
            s = class_template_def(f, is_union, loc);
            r = rec_of(syms[s].ty);
            defining_pattern = true;
        } else if f >= 0 && is_record(syms[f].ty) {
            s = f;
            r = rec_of(syms[f].ty);
        } else {
            // a member of an opaque class: parse and drop
            s = declare_tag(qn.name, is_union, loc, false, cur_scope);
            r = rec_of(syms[s].ty);
        }
    } else if has_name {
        let prev = tag_in_scope(cur_scope, qn.name, in_block);
        if pending_tmpl >= 0 {
            if prev >= 0 && syms[prev].kind as i64 == SK_TEMPLATE {
                s = class_template_def(prev, is_union, loc);
            } else {
                let tt = declare_class_template(qn.name, is_union, loc, true);
                s = tmpls[cxs[last_tmpl_sym].tmpl].sym as i64;
                s = class_template_def(s, is_union, loc);
            }
            r = rec_of(syms[s].ty);
            defining_pattern = true;
        } else if prev >= 0 && syms[prev].kind as i64 == SK_TAG && is_record(syms[prev].ty) &&
                  records[rec_of(syms[prev].ty)].flags & RF_COMPLETE == 0 {
            s = prev;
            r = rec_of(syms[prev].ty);
        } else {
            s = declare_tag(qn.name, is_union, loc, in_block, cur_scope);
            r = rec_of(syms[s].ty);
        }
    } else {
        // an unnamed class
        let rr = new_record_cx(0, is_union, loc);
        s = csym(SK_TAG, 0, records[rr].ty << 4, loc);
        syms[s].v = records[rr].ty as i64;
        cx_grow();
        cxs[s].dscope = cur_scope as! i32;
        class_setup(rr, s, cur_scope);
        r = rr;
    }
    if w == KW_CLASS { crecs[r].flags = crecs[r].flags | CR_CLASS_KW; }
    if is_final { mark_final(r); }
    if ca.aligned > 0 { records[r].attr_align = ca.aligned; }
    if ca.misc & AM_PACKED != 0 { records[r].flags = records[r].flags | RF_PACKED; }
    records[r].pack = pack_now();
    parse_class_body(r, w);
    ds.tag_ty = syms[s].ty;
    if syms[s].kind as i64 == SK_TEMPLATE { return records[r].ty << 4; }
    return syms[s].ty;
}
let DC_CLASS_BITFIELD_NEVER = 99;

fn tag_type_of(s: i64) -> u32 {
    if syms[s].kind as i64 == SK_TEMPLATE { return tmpl_injected(s); }
    return syms[s].ty;
}

// #pragma pack in effect at the current token.
fn pack_now() -> u32 {
    var lo = 0;
    var hi = pack_changes.len / 2;
    while lo < hi {
        let mid = (lo + hi) / 2;
        if pack_changes[mid * 2] as i64 <= pc { lo = mid + 1; } else { hi = mid; }
    }
    if lo == 0 { return 0; }
    return pack_changes[(lo - 1) * 2 + 1];
}

// The base-clause and the member-specification of record r, then the
// class is completed.
recursive fn parse_class_body(r: i64, w: i64) {
    let sc = crecs[r].scope as i64;
    let save_scope = cur_scope;
    let save_class = cur_class;
    let save_access = cur_access;
    let save_floor = local_floor;
    let fmark = cfscratch.len;
    let bmark = cbscratch.len;
    let mmark = cmscratch.len;
    let sv_fmark = cur_fmark;
    cur_fmark = fmark;
    let outermost = class_nest == 0;
    let dmark = deferred.len;
    class_nest++;
    records[r].flags = records[r].flags | RF_BEING_DEFINED;
    // bases
    if accept(TK_COLON) {
        loop {
            var a = Attrs { .. };
            cx_attrs(a);
            var bf: u8 = 0;
            var acc: u8 = if w == KW_CLASS { AC_PRIVATE as! u8 } else { AC_PUBLIC as! u8 };
            loop {
                if at_kw(KW_VIRTUAL) { bf = bf | BF_VIRTUAL; adv(); continue; }
                if at_kw(KW_PUBLIC) { acc = AC_PUBLIC as! u8; adv(); continue; }
                if at_kw(KW_PROTECTED) { acc = AC_PROTECTED as! u8; adv(); continue; }
                if at_kw(KW_PRIVATE) { acc = AC_PRIVATE as! u8; adv(); continue; }
                break;
            }
            var bt: u32 = 0;
            let p0 = pc;
            let pm = pk_refs.len;
            if at_kw(KW_DECLTYPE) {
                bt = parse_decltype();
            } else {
                var qn = QN { .. };
                if !parse_qname(qn) { perr_expected("a base class"); break; }
                lookup_qn(qn);
                bt = qn_type(qn);
                if bt == 0 {
                    if !dependent_ctx() && diag_suppress == 0 && qn.dep == 0 {
                        err_at(qn.loc, str("expected class name"));
                    }
                    bt = t_unknown;
                }
            }
            if at(TK_ELLIPSIS) {
                let ok, n = pk_count(pm);
                if ok {
                    // D2: bases expanded from bound packs
                    adv();
                    let p1 = pc;
                    let sm = pk_save(pm);
                    for i in n {
                        pc = p0;
                        gt_pos = -1;
                        let am = pk_activate_saved(sm, i);
                        var b2: u32 = 0;
                        if at_kw(KW_DECLTYPE) { b2 = parse_decltype(); }
                        else {
                            var qn2 = QN { .. };
                            if parse_qname(qn2) { lookup_qn(qn2); b2 = qn_type(qn2); }
                            if b2 == 0 { b2 = t_unknown; }
                        }
                        pk_active.resize(am);
                        need_complete(b2);
                        cbscratch.push(Base { ty: b2, flags: bf, access: acc, rsv: 0, offset: 0 });
                    }
                    pk_saved.resize(sm);
                    pc = p1;
                    if !accept(TK_COMMA) { break; }
                    continue;
                }
                pk_refs.resize(pm);
            }
            if accept(TK_ELLIPSIS) { bt = mk_packexp(bt); }
            need_complete(bt);
            cbscratch.push(Base { ty: bt, flags: bf, access: acc, rsv: 0, offset: 0 });
            if !accept(TK_COMMA) { break; }
        }
    }
    // the bases are known before the members (lookups see them)
    crecs[r].bases = cbases.len as! u32;
    crecs[r].nbases = (cbscratch.len - bmark) as! u32;
    for i in bmark..cbscratch.len { cbases.push(cbscratch[i]); }
    cbscratch.resize(bmark);
    cur_scope = sc;
    cur_class = sc;
    cur_access = if w == KW_CLASS { AC_PRIVATE } else { AC_PUBLIC };
    expect(TK_L_BRACE, "'{'");
    while !at(TK_R_BRACE) && !at(TK_EOF) {
        let before = pc;
        parse_member_decl(r);
        if pc == before { adv(); }
    }
    expect(TK_R_BRACE, "'}'");
    // the fields
    let first = fields.len;
    for i in fmark..cfscratch.len { fields.push(cfscratch[i]); }
    records[r].first = first as! u32;
    records[r].count = (cfscratch.len - fmark) as! u32;
    cfscratch.resize(fmark);
    cur_fmark = sv_fmark;
    // the member functions, in order
    while crec_mems.len <= r { crec_mems.push(MemRange { first: 0, count: 0 }); }
    crec_mems[r] = MemRange { first: cmem.len as! u32, count: (cmscratch.len - mmark) as! u32 };
    for i in mmark..cmscratch.len { cmem.push(cmscratch[i]); }
    cmscratch.resize(mmark);
    records[r].flags = records[r].flags & ~RF_BEING_DEFINED;
    complete_class(r);
    cur_scope = save_scope;
    cur_class = save_class;
    cur_access = save_access;
    class_nest--;
    if outermost {
        // C++ [class.mem]p7: the bodies see the complete classes
        parse_deferred(dmark);
    }
    local_floor = save_floor;
}
var cur_access: i64 = 0;
var cur_fmark: i64 = 0;     // where the class being defined's members start in cfscratch

// One member-declaration.
recursive fn parse_member_decl(r: i64) {
    if accept(TK_SEMI) { return; }
    if at_kw(KW_PUBLIC) || at_kw(KW_PRIVATE) || at_kw(KW_PROTECTED) {
        cur_access = if at_kw(KW_PUBLIC) { AC_PUBLIC } else if at_kw(KW_PRIVATE) { AC_PRIVATE } else { AC_PROTECTED };
        adv();
        expect(TK_COLON, "':'");
        return;
    }
    if at_kw(KW_STATIC_ASSERT) { parse_static_assert_cx(); return; }
    if at_kw(KW_TEMPLATE) { parse_template_decl(DC_CLASS); return; }
    if at_kw(KW_USING) { parse_using(DC_CLASS); return; }
    if at_kw(KW_EXTENSION) { adv(); parse_member_decl(r); return; }
    if at_kw(KW_FRIEND) || (at_attr_start() && friend_after_attrs()) {
        parse_friend(r);
        return;
    }
    parse_simple_decl(DC_CLASS);
}

fn friend_after_attrs() -> bool {
    let sv = save();
    var a = Attrs { .. };
    cx_attrs(a);
    let f = at_kw(KW_FRIEND);
    restore(sv);
    return f;
}

// friend declarations: friend classes are noted, friend functions are
// declared (hidden: found only by ADL, which D1 does not perform for
// friends) and their in-class definitions are parsed as member bodies.
recursive fn parse_friend(r: i64) {
    parse_simple_decl(DC_FRIEND);
}
let DC_FRIEND = 6;

// Completes record r: layout, implicit members, the class's C++ facts.
recursive fn complete_class(r: i64) {
    if records[r].flags & RF_COMPLETE != 0 && crecs[r].flags & CR_LAYOUT != 0 { return; }
    let sc = crecs[r].scope as i64;
    let pattern = scopes[sc].flags & SCF_PATTERN != 0;
    if pattern {
        crecs[r].flags = crecs[r].flags | CR_PATTERN;
        records[r].flags = records[r].flags | RF_COMPLETE;
        records[r].size = -1;
        return;
    }
    // D2: members of class types not instantiated yet
    let rec = records[r];
    for i in rec.first..rec.first + rec.count { need_complete(fields[i].ty); }
    class_facts(r);
    cx_layout(r);
}

// The deferred parts of the classes completed since mark: member function
// bodies (and default member initializers, kept with their fields).
recursive fn parse_deferred(mark: i64) {
    var i = mark;
    while i < deferred.len {
        let s = deferred[i] as i64;
        let sc = deferred[i + 1] as i64;
        i += 2;
        parse_member_body(s, sc);
    }
    deferred.resize(mark);
}

// ---------------------------------------------------------------------------
// Enums.

var enum_scratch: u32[>..<] = [];

recursive fn parse_enum_spec_cx(ds: CDS&, ctx: i64) -> u32 {
    let loc = tloc();
    adv();      // enum
    var scoped = false;
    if at_kw(KW_CLASS) || at_kw(KW_STRUCT) { scoped = true; adv(); }
    var ea = Attrs { .. };
    cx_attrs(ea);
    var qn = QN { .. };
    var has_name = false;
    if at(TK_IDENT) || at(TK_COLONCOLON) {
        let sv = save();
        diag_suppress++;
        has_name = parse_qname(qn);
        diag_suppress--;
        if !has_name || qn.kind as i64 != QK_IDENT { restore(sv); has_name = false; }
    }
    cx_attrs(ea);
    var fixed: u32 = 0;
    if at(TK_COLON) && (scoped || has_name || tk_n(1) != TK_IDENT || true) {
        // : type-specifier-seq (not a bit-field width: that would need a declarator first)
        if !(ctx == DC_CLASS && !has_name && !scoped && !at_type_after_colon()) {
            adv();
            var fds = CDS { .. };
            var fa = Attrs { .. };
            parse_cds(fds, fa, DC_TYPEID);
            fixed = finish_cds(fds);
            if fixed == 0 { fixed = t_int; }
        }
    }
    if scoped && fixed == 0 { fixed = t_int; }
    let is_def = at(TK_L_BRACE);
    let in_block = in_block_scope();
    if !is_def {
        if !has_name { perr_expected("an enum name"); return t_int; }
        lookup_qn(qn);
        let f = chain_type(qn.sym as i64);
        if f >= 0 && kind_of(syms[f].ty) == TY_ENUM {
            if fixed != 0 && !qn.qual { /* an opaque redeclaration */ }
            return syms[f].ty;
        }
        if qn.qual || qn.dep != 0 { return t_unknown; }
        // an opaque enum declaration (enum E : int;) or a forward reference
        let s = declare_enum(qn.name, loc, in_block, scoped, fixed);
        return syms[s].ty;
    }
    ds.tag_def = true;
    var s: i64 = -1;
    if has_name && qn.qual {
        lookup_qn(qn);
        s = chain_type(qn.sym as i64);
        if s < 0 || kind_of(syms[s].ty) != TY_ENUM { s = declare_enum(qn.name, loc, false, scoped, fixed); }
    } else if has_name {
        let prev = tag_in_scope_enum(cur_scope, qn.name, in_block);
        if prev >= 0 { s = prev; } else { s = declare_enum(qn.name, loc, in_block, scoped, fixed); }
    } else {
        s = declare_enum(0, loc, in_block, scoped, fixed);
    }
    let e = types[syms[s].ty >> 4].extra as i64;
    let esc = enum_scope(e);
    let pattern = dependent_ctx();
    adv();      // {
    // the enumerators are visible in the enumerator-list (scoped ones through the enum's scope)
    let sv_scope = cur_scope;
    if scoped { cur_scope = esc; }
    // the enumerators: in the enum's scope (scoped) or the enclosing one too
    var next: i64 = 0;
    var next_dep = false;
    var minv: i64 = 0;
    var maxv: i64 = 0;
    var any_neg = false;
    var max_u: u64 = 0;
    var first = true;
    let mark = enum_scratch.len;
    while at(TK_IDENT) {
        let name = tu_toks[pc].val;
        let eloc = tloc();
        adv();
        var a = Attrs { .. };
        cx_attrs(a);
        var v = next;
        var vdep = next_dep;
        if accept(TK_EQUAL) {
            let ex = parse_cexpr();
            if is_opaque(nodes[ex].ty) { vdep = true; }
            else {
                let ok, x = const_int(ex);
                if ok { v = x; vdep = false; } else { vdep = true; }
            }
        }
        let c = csym(SK_ENUMC, name, syms[s].ty, eloc);
        syms[c].v = v;
        if vdep { cxs[c].flags = cxs[c].flags | CF_PATTERN; }
        scope_add(esc, c);
        if !scoped {
            if in_block { cx_grow(); bind_sym(c, false); }
            else {
                // also visible in the enclosing scope
                let u = csym(SK_USING, name, syms[s].ty, eloc);
                cxs[u].target = c as! i32;
                scope_add(cur_scope, u);
            }
        }
        enum_scratch.push(c as! u32);
        if !vdep {
            if first || v < minv { minv = v; }
            if first || v > maxv { maxv = v; }
            if v < 0 { any_neg = true; }
            if (v as! u64) > max_u && v >= 0 { max_u = v as! u64; }
            first = false;
        }
        next = v + 1;
        next_dep = vdep;
        if !accept(TK_COMMA) { break; }
    }
    expect(TK_R_BRACE, "'}'");
    cur_scope = sv_scope;
    // the underlying type of an unscoped enum without a fixed type
    // (C++ [dcl.enum]p7, clang: int, unsigned int, long, unsigned long ...)
    var ut = fixed;
    if ut == 0 {
        if pattern && next_dep { ut = t_int; }
        else if !any_neg {
            if maxv <= 2147483647 { ut = t_uint; if maxv <= 2147483647 { ut = t_int; } }
            else if (maxv as! u64) <= 4294967295 { ut = t_uint; }
            else { ut = t_long; if max_u > 9223372036854775807 { ut = t_ulong; } }
        } else {
            if minv >= -2147483648 && maxv <= 2147483647 { ut = t_int; }
            else { ut = t_long; }
        }
    }
    enums[e].underlying = ut;
    enums[e].complete = true;
    types[syms[s].ty >> 4].base = ut;
    types[syms[s].ty >> 4].size = type_size(ut);
    types[syms[s].ty >> 4].align = type_align(ut) as! u32;
    enum_scratch.resize(mark);
    return syms[s].ty;
}

fn at_type_after_colon() -> bool {
    let k = tk_n(1);
    if k >= TK_KW { return is_type_kw(k - TK_KW); }
    if k == TK_IDENT || k == TK_COLONCOLON { return name_is_type_at(pc + 1); }
    return false;
}

fn tag_in_scope_enum(sc: i64, name: u32, in_block: bool) -> i64 {
    if in_block {
        if name as i64 >= id_bind.len { return -1; }
        let t = id_bind[name].tag as i64;
        if t >= 0 && syms[t].scope as i64 == scope_depth && kind_of(syms[t].ty) == TY_ENUM { return t; }
        return -1;
    }
    var s = scope_find(sc, name);
    while s >= 0 {
        let r = resolve(s);
        if r >= 0 && syms[r].kind as i64 == SK_TAG && kind_of(syms[r].ty) == TY_ENUM { return r; }
        s = cxs[s].nnext as i64;
    }
    return -1;
}

fn declare_enum(name: u32, loc: u32, in_block: bool, scoped: bool, fixed: u32) -> i64 {
    let e = enums.len;
    let et = mk_tagged(TY_ENUM, e as! u32);
    enums.push(EnumRec { name: name, ty: et, underlying: fixed, complete: fixed != 0, packed: false, rsv: 0, loc: loc, scope: 0 });
    if fixed != 0 {
        types[et].base = fixed;
        types[et].size = type_size(fixed);
        types[et].align = type_align(fixed) as! u32;
    }
    let s = csym(SK_TAG, name, et << 4, loc);
    syms[s].v = et as i64;
    if in_block {
        cxs[s].dscope = cur_scope as! i32;
        bind_sym(s, true);
    } else {
        scope_add(cur_scope, s);
    }
    let esc = new_scope(CS_ENUM, cur_scope, s, name);
    set_enum_scope(e, esc);
    if scoped { enum_scoped.insert(e as u64, 1); }
    return s;
}
var enum_scoped = dictionary<u64, u32> {};
fn is_scoped_enum(t: u32) -> bool {
    if kind_of(t) != TY_ENUM { return false; }
    return enum_scoped.contains(types[t >> 4].extra as u64);
}
