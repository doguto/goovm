// Debug information of optimized code (milestone E2): the DIE tree after
// the middle-end (opt.goose, remap_dies), as LLVM's DwarfDebug builds it for
// inlined code.
//
// The inliner gives the inlined instructions the callee's source locations
// inlined at a copy of the call's location (opt_inline.goose, inl_dloc), so
// each inlined call is a scope instance of its own. Here every such
// instance that has code in an emitted function becomes a
// DW_TAG_inlined_subroutine DIE (abstract origin: the callee's subprogram;
// DW_AT_call_file/line/column: the call's location; its code ranges:
// GIR_DF_SCOPE_PC of the callee's subprogram in the code inlined at the
// call, which dwarf.goose resolves from the line runs), as a child of the
// DIE of the call's scope: a lexical block of the caller, its subprogram,
// or the instance that the call itself was inlined into.
//
// The callee's subprogram DIE becomes abstract (DW_AT_inline, no code
// attributes, its variables without locations): in place if the callee is
// not emitted (every call inlined, or an available_externally body), else
// split as LLVM does: an abstract DIE with the declaration attributes and
// abstract copies of the parameters, variables, labels and lexical blocks,
// and the concrete DIE keeping the code attributes, each of its entities
// referring to its abstract copy (DW_AT_abstract_origin).
//
// The tree is rebuilt in pre-order (nodes with child lists, DW_FORM_ref4
// values renumbered), as GIR requires.

let OD_AT_location: u32 = 0x02;
let OD_AT_low_pc: u32 = 0x11;
let OD_AT_high_pc: u32 = 0x12;
let OD_AT_const_value: u32 = 0x1c;
let OD_AT_inline: u32 = 0x20;
let OD_AT_abstract_origin: u32 = 0x31;
let OD_AT_frame_base: u32 = 0x40;
let OD_AT_ranges: u32 = 0x55;
let OD_AT_call_column: u32 = 0x57;
let OD_AT_call_file: u32 = 0x58;
let OD_AT_call_line: u32 = 0x59;
let OD_AT_object_pointer: u32 = 0x64;
let OD_AT_call_all_calls: u32 = 0x7a;
let OD_TAG_label: u32 = 0x0a;
let OD_TAG_lexical_block: u32 = 0x0b;
let OD_TAG_formal_parameter: u32 = 0x05;
let OD_TAG_inlined_subroutine: u32 = 0x1d;
let OD_TAG_subprogram: u32 = 0x2e;
let OD_TAG_variable: u32 = 0x34;
let OD_FORM_ref4: u32 = 0x13;
let OD_FORM_udata: u32 = 0x0f;
let OD_FORM_implicit_const: u32 = 0x21;

// the nodes: tag, parent, attribute run (od_attrs), children (linked)
var od_tag: u16[>..] = [];
var od_par: u32[>..] = [];
var od_a0: u32[>..] = [];
var od_an: u32[>..] = [];
var od_first: u32[>..] = [];
var od_last: u32[>..] = [];
var od_next: u32[>..] = [];
var od_attrs: DAttr[>..] = [];
var od_tmp: DAttr[>..] = [];

fn od_new(tag: u32, par: u32) -> u32 {
    let n = od_tag.len as! u32;
    od_tag.push(tag as! u16);
    od_par.push(par);
    od_a0.push(od_attrs.len as! u32);
    od_an.push(0);
    od_first.push(NIL);
    od_last.push(NIL);
    od_next.push(NIL);
    if par != NIL { od_append_kid(par, n); }
    return n;
}
fn od_append_kid(par: u32, n: u32) {
    if od_last[par] == NIL { od_first[par] = n; } else { od_next[od_last[par]] = n; }
    od_last[par] = n;
}
// n goes into par's children just before child b.
fn od_insert_before(par: u32, b: u32, n: u32) {
    if od_first[par] == b {
        od_next[n] = b;
        od_first[par] = n;
        return;
    }
    var k = od_first[par];
    while k != NIL && od_next[k] != b { k = od_next[k]; }
    if k == NIL { od_append_kid(par, n); return; }
    od_next[n] = b;
    od_next[k] = n;
}
// The node's attributes become od_tmp (a new run).
fn od_set_attrs(n: u32) {
    od_a0[n] = od_attrs.len as! u32;
    od_an[n] = od_tmp.len as! u32;
    od_attrs.append(od_tmp);
}
fn od_concrete(A: DAttr) -> bool {
    let f: u32 = A.form;
    let at: u32 = A.at;
    if f == DF_PC || f == DF_FRAME_BASE || f == DF_LOCAL || f == DF_LABEL || f == DF_SCOPE_PC { return true; }
    return at == OD_AT_location || at == OD_AT_low_pc || at == OD_AT_high_pc || at == OD_AT_frame_base ||
           at == OD_AT_ranges || at == OD_AT_call_all_calls || at == OD_AT_const_value;
}

// ------------------------------------------------------------ scopes
fn od_nonfile(s0: u32) -> u32 {
    var s = s0;
    while s != 0 && M.dscopes[s].kind == DS_FILE { s = M.dscopes[s].parent; }
    return s;
}
fn od_sp_of(s0: u32) -> u32 {
    var s = s0;
    while s != 0 && M.dscopes[s].kind != DS_SUBPROGRAM { s = M.dscopes[s].parent; }
    return s;
}
var od_spdie: u32[>..] = [];    // per scope: the subprogram DIE (concrete, with code)
var od_lexdie: u32[>..] = [];   // per scope: the lexical block DIE of the function's own code
var od_abs: u32[>..] = [];      // per scope: its abstract subprogram DIE (NIL: not made yet)
var od_inst: u32[>..] = [];     // per location (a call's, inlined at): its inlined_subroutine DIE
var od_isp: u32[>..] = [];      // per location: the inlined callee's subprogram scope
var od_cmap: u32[>..] = [];     // node -> its abstract copy (splits)

// The DIE that holds what is in scope s of the function's own code.
fn od_scope_die(s0: u32) -> u32 {
    var s = od_nonfile(s0);
    while s != 0 {
        if M.dscopes[s].kind == DS_SUBPROGRAM { return od_spdie[s]; }
        if od_lexdie[s] != NIL { return od_lexdie[s]; }
        s = od_nonfile(M.dscopes[s].parent);
    }
    return NIL;
}

// The node's attributes without the code ones (and with DW_AT_inline for a
// subprogram) into od_tmp.
fn od_abstract_attrs(n: u32, sp: bool) {
    od_tmp.clear();
    for k in od_a0[n]..od_a0[n] + od_an[n] {
        let A = od_attrs[k];
        if od_concrete(A) { continue; }
        od_tmp.push(A);
    }
    if sp { od_tmp.push(DAttr { at: OD_AT_inline as! u16, form: OD_FORM_implicit_const as! u16, aux: 0, val: 1 }); }
}
// The subtree of n made abstract in place (a callee that is not emitted).
recursive fn od_make_abstract(n: u32, sp: bool) {
    od_abstract_attrs(n, sp);
    od_set_attrs(n);
    var c = od_first[n];
    while c != NIL {
        od_make_abstract(c, false);
        c = od_next[c];
    }
}
fn od_entity(t: u32) -> bool {
    return t == OD_TAG_formal_parameter || t == OD_TAG_variable || t == OD_TAG_label || t == OD_TAG_lexical_block;
}
// The abstract copies of the entities under concrete node n (into abstract
// node a); each concrete one keeps its code attributes and refers to its
// copy.
recursive fn od_split_kids(n: u32, a: u32) {
    var c = od_first[n];
    while c != NIL {
        let t: u32 = od_tag[c];
        if od_entity(t) {
            let x = od_new(t, a);
            od_abstract_attrs(c, false);
            od_set_attrs(x);
            od_cmap[c] = x;
            od_tmp.clear();
            for k in od_a0[c]..od_a0[c] + od_an[c] {
                if od_concrete(od_attrs[k]) { od_tmp.push(od_attrs[k]); }
            }
            od_tmp.push(DAttr { at: OD_AT_abstract_origin as! u16, form: OD_FORM_ref4 as! u16, aux: 0, val: x as u64 });
            od_set_attrs(c);
            if t == OD_TAG_lexical_block { od_split_kids(c, x); }
        }
        c = od_next[c];
    }
}
// References inside the abstract subtree a to concrete nodes that have
// abstract copies (DW_AT_object_pointer) go to the copies.
recursive fn od_fix_refs(a: u32) {
    for k in od_a0[a]..od_a0[a] + od_an[a] {
        let A = od_attrs[k];
        if A.form == OD_FORM_ref4 && A.val < od_cmap.len as u64 && od_cmap[A.val] != NIL {
            od_attrs[k].val = od_cmap[A.val] as u64;
        }
    }
    var c = od_first[a];
    while c != NIL {
        od_fix_refs(c);
        c = od_next[c];
    }
}
// The abstract subprogram DIE of callee scope sp, NIL if it has none.
fn od_abstract(sp: u32) -> u32 {
    if od_abs[sp] != NIL { return od_abs[sp]; }
    let d = od_spdie[sp];
    if d == NIL { return NIL; }
    var fi: u32 = NIL;
    for k in od_a0[d]..od_a0[d] + od_an[d] {
        if od_attrs[k].form == DF_PC { fi = od_attrs[k].val as! u32; }
    }
    if fi == NIL || x_funcs[xb_f + fi].flags & (FN_DEAD | FN_AVAILEXT) != 0 {
        // not emitted: abstract in place
        od_make_abstract(d, true);
        od_abs[sp] = d;
        return d;
    }
    // emitted too: an abstract DIE beside it
    let a = od_new(OD_TAG_subprogram, NIL);
    od_par[a] = od_par[d];
    od_insert_before(od_par[d], d, a);
    od_abstract_attrs(d, true);
    // (the object pointer is the abstract parameter's, below)
    od_set_attrs(a);
    if od_cmap.len < od_tag.len { od_cmap.resize(od_tag.len, NIL); }
    od_split_kids(d, a);
    if od_cmap.len < od_tag.len { od_cmap.resize(od_tag.len, NIL); }
    od_fix_refs(a);
    od_tmp.clear();
    for k in od_a0[d]..od_a0[d] + od_an[d] {
        if od_concrete(od_attrs[k]) { od_tmp.push(od_attrs[k]); }
    }
    od_tmp.push(DAttr { at: OD_AT_abstract_origin as! u16, form: OD_FORM_ref4 as! u16, aux: 0, val: a as u64 });
    od_set_attrs(d);
    od_abs[sp] = a;
    return a;
}

// The inlined_subroutine DIE of the code inlined at location ia (made with
// its enclosing instances), NIL if the callee has no subprogram DIE.
recursive fn od_instance(ia: u32) -> u32 {
    if od_inst[ia] != NIL { return od_inst[ia]; }
    let sp = od_isp[ia];
    if sp == 0 { return NIL; }
    let abs = od_abstract(sp);
    if abs == NIL { return NIL; }
    let L = M.dlocs[ia];
    var par: u32 = NIL;
    if L.inlined_at != 0 {
        if od_isp[L.inlined_at] != 0 { par = od_instance(L.inlined_at); }
    } else {
        par = od_scope_die(L.scope);
    }
    if par == NIL { return NIL; }
    let x = od_new(OD_TAG_inlined_subroutine, par);
    od_tmp.clear();
    od_tmp.push(DAttr { at: OD_AT_abstract_origin as! u16, form: OD_FORM_ref4 as! u16, aux: 0, val: abs as u64 });
    od_tmp.push(DAttr { at: 0, form: DF_SCOPE_PC as! u16, aux: ia, val: sp as u64 });
    let cs = od_nonfile(L.scope);
    od_tmp.push(DAttr { at: OD_AT_call_file as! u16, form: DF_FILE as! u16, aux: 0, val: M.dscopes[cs].file as u64 });
    od_tmp.push(DAttr { at: OD_AT_call_line as! u16, form: OD_FORM_udata as! u16, aux: 0, val: L.line as u64 });
    if L.col != 0 {
        od_tmp.push(DAttr { at: OD_AT_call_column as! u16, form: OD_FORM_udata as! u16, aux: 0, val: L.col as u64 });
    }
    od_set_attrs(x);
    od_inst[ia] = x;
    return x;
}

// After remap_dies has put the input DIEs (attributes remapped) in
// x_dies[xb_d..] / x_dattrs[xb_t..]: the inlined instances, the tree again.
fn od_inlined_dies() {
    if !xl_on || M.dies.len == 0 { return; }
    let nd: u32 = (x_dies.len - xb_d) as! u32;
    od_tag.clear();
    od_par.clear();
    od_a0.clear();
    od_an.clear();
    od_first.clear();
    od_last.clear();
    od_next.clear();
    od_attrs.clear();
    od_cmap.clear();
    for k in 0..nd {
        let D = x_dies[xb_d + k];
        let n = od_new(D.tag, if D.parent == GIR_NONE { NIL } else { D.parent });
        od_tmp.clear();
        for q in D.attrs..D.attrs + D.n_attrs { od_tmp.push(x_dattrs[xb_t + q]); }
        od_set_attrs(n);
    }
    // scopes -> DIEs
    let ns = M.dscopes.len;
    od_spdie.clear();
    od_spdie.resize(ns, NIL);
    od_lexdie.clear();
    od_lexdie.resize(ns, NIL);
    od_abs.clear();
    od_abs.resize(ns, NIL);
    for n in 0..nd {
        for k in od_a0[n]..od_a0[n] + od_an[n] {
            let A = od_attrs[k];
            if A.form == DF_PC && A.val < M.funcs.len as u64 {
                let s = M.funcs[A.val].dbg;
                if s != 0 && s < ns as! u32 { od_spdie[s] = n; }
            } else if A.form == DF_SCOPE_PC && A.aux == 0 && A.val < ns as u64 {
                od_lexdie[A.val] = n;
            }
        }
    }
    // the inlined calls with code in emitted functions
    od_inst.clear();
    od_inst.resize(M.dlocs.len, NIL);
    od_isp.clear();
    od_isp.resize(M.dlocs.len, 0);
    for fi in 0..M.funcs.len {
        let F = x_funcs[xb_f + fi];
        if F.flags & (FN_DEAD | FN_AVAILEXT) != 0 { continue; }
        for j in F.first_inst..F.first_inst + F.n_inst {
            let d = x_insts[xb_i + j].dbg;
            if d == 0 { continue; }
            var s = od_nonfile(M.dlocs[d].scope);
            var ia = M.dlocs[d].inlined_at;
            while ia != 0 && od_isp[ia] == 0 {
                od_isp[ia] = od_sp_of(s);
                if od_isp[ia] == 0 { od_isp[ia] = NIL; }
                s = od_nonfile(M.dlocs[ia].scope);
                ia = M.dlocs[ia].inlined_at;
            }
        }
    }
    var any = false;
    for ia in 0..M.dlocs.len {
        if od_isp[ia] == NIL { od_isp[ia] = 0; }
    }
    for ia in 0..M.dlocs.len {
        if od_isp[ia] != 0 && od_instance(ia as! u32) != NIL { any = true; }
    }
    if !any { return; }
    // pre-order again
    let n = od_tag.len;
    if od_cmap.len < n { od_cmap.resize(n, NIL); }
    od_order.clear();
    od_newix.clear();
    od_newix.resize(n, NIL);
    od_dfs(0);
    // (a new region of the output tables)
    xb_d = x_dies.len;
    xb_t = x_dattrs.len;
    for v in od_order {
        let p = od_par[v];
        let a0 = (x_dattrs.len - xb_t) as! u32;
        for k in od_a0[v]..od_a0[v] + od_an[v] {
            var A = od_attrs[k];
            if A.form == OD_FORM_ref4 && A.val < n as u64 && od_newix[A.val] != NIL { A.val = od_newix[A.val] as u64; }
            x_dattrs.push(A);
        }
        x_dies.push(Die { tag: od_tag[v], flags: 0, parent: if p == NIL { GIR_NONE } else { od_newix[p] },
                          attrs: a0, n_attrs: (x_dattrs.len - xb_t) as! u32 - a0 });
    }
}
var od_order: u32[>..] = [];
var od_newix: u32[>..] = [];
recursive fn od_dfs(v: u32) {
    od_newix[v] = od_order.len as! u32;
    od_order.push(v);
    var c = od_first[v];
    while c != NIL {
        od_dfs(c);
        c = od_next[c];
    }
}
