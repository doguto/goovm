// goosecc D3: vtables, VTTs and thunks of the Itanium C++ ABI (2.5, 2.6),
// a port of clang's ItaniumVTableBuilder, VCallAndVBaseOffsetBuilder,
// FinalOverriders and VTTBuilder (VTableBuilder.cpp, VTTBuilder.cpp).
//
// A vtable group is built for (most derived class md at md_off in layout
// class lc): lc == md for the complete object's vtable group, lc a class
// that has md as a base for a construction vtable group (_ZTC). Each
// group is a run of components (vcall and vbase offsets, offset to top,
// RTTI, function pointers, destructors) holding its vtables one after the
// other, the address points of every base subobject that uses one, the
// vtable indices of md's virtual functions, md's virtual base offset
// offsets, and the thunks md's own functions need.
//
// The builder runs one group at a time (its state is global); the vcall /
// vbase offset builder, which it also runs on its own for the vcall
// offsets of a virtual base or a class's vbase offset offsets, has state
// of its own. Base subobjects of md (FinalOverriders' ComputeBaseOffsets)
// are a table with derivation edges, on which final overriders are found
// as the topmost overrider on any path from md (a well-formed program has
// a unique one).

namespace cx;

import std;
import dictionary;
import .common;
import .types;
import .ast;
import .sema;
import .cx_core;
import .cx_layout;
import .cx_mangle;
import .cx_gen_defs;

// ---------------------------------------------------------------------------
// The class hierarchy as the builder sees it.

fn vt_dyn(r: i64) -> bool { crecs[r].flags & CR_DYNAMIC != 0 }
fn vt_prim(r: i64) -> i64 { crecs[r].primary as i64 }
fn vt_prim_virtual(r: i64) -> bool { crecs[r].flags & CR_PRIM_VIRTUAL != 0 }
fn vt_nbases(r: i64) -> i64 { crecs[r].nbases as i64 }
fn vt_base_rec(r: i64, i: i64) -> i64 { rec_of(cbases[crecs[r].bases + i].ty) }
fn vt_base_virtual(r: i64, i: i64) -> bool { cbases[crecs[r].bases + i].flags & BF_VIRTUAL != 0 }
fn vt_base_off(r: i64, i: i64) -> i64 { cbases[crecs[r].bases + i].offset }
fn vt_vbo(r: i64, v: i64) -> i64 { vbase_offset_of(r, v) }
fn has_vb(r: i64) -> bool { crecs[r].flags & CR_HAS_VBASE != 0 }

// The non-virtual offset of direct base record br in r.
fn vt_nvbase_off(r: i64, br: i64) -> i64 {
    for i in vt_nbases(r) { if !vt_base_virtual(r, i) && vt_base_rec(r, i) == br { return vt_base_off(r, i); } }
    return 0;
}

// Do f and g have one vtable slot (an override: same name, parameters and
// cv; any two destructors)?
fn vt_same_sig(f: i64, g: i64) -> bool {
    let fd = cxs[f].flags & CF_DTOR != 0;
    let gd = cxs[g].flags & CF_DTOR != 0;
    if fd || gd { return fd && gd; }
    return overrides(f, g);
}

// The virtual functions declared in r, in vtable order (declared ones,
// then the implicit virtual destructor), pushed to vm_list.
var vm_list: u32[>..<] = [];

fn push_vmethods(r: i64) {
    let m = mem_range(r);
    var has_dtor = false;
    for j in m.count {
        let f = cmem[m.first + j] as i64;
        if syms[f].kind as i64 != SK_FUNC { continue; }
        if cxs[f].flags & CF_DTOR != 0 { has_dtor = true; }
        if cxs[f].flags & CF_VIRTUAL == 0 || cxs[f].flags & CF_DTOR_DELETING != 0 { continue; }
        vm_list.push(f as! u32);
    }
    if !has_dtor && dtor_virtual_in_bases(r) {
        let d = class_dtor(r);
        if d >= 0 { vm_list.push(d as! u32); }
    }
}

// The function of class r that overrides m (or m itself in its class), or -1.
fn class_overrider(r: i64, m: i64) -> i64 {
    if cxs[m].flags & CF_DTOR != 0 {
        if rec_of(scope_class_type(cxs[m].dscope as i64)) == r { return m; }
        let d = class_dtor(r);
        if d >= 0 && (cxs[d].flags & CF_VIRTUAL != 0 || dtor_virtual_in_bases(r)) { return d; }
        return -1;
    }
    if rec_of(scope_class_type(cxs[m].dscope as i64)) == r { return m; }
    let mk = vm_list.len;
    push_vmethods(r);
    var res: i64 = -1;
    for i in mk..vm_list.len { if vt_same_sig(vm_list[i] as i64, m) { res = vm_list[i] as i64; break; } }
    vm_list.resize(mk);
    return res;
}

fn method_class(m: i64) -> i64 { rec_of(scope_class_type(cxs[m].dscope as i64)) }

// Is class d derived from b (or b itself)?
recursive fn vt_derived_from(d: i64, b: i64) -> bool {
    if d == b { return true; }
    for i in vt_nbases(d) { if vt_derived_from(vt_base_rec(d, i), b) { return true; } }
    return false;
}

// Does m override g (g a virtual function of a proper base of m's class)?
fn vt_overrides_of(m: i64, g: i64) -> bool {
    let mc = method_class(m);
    let gc = method_class(g);
    return mc != gc && vt_derived_from(mc, gc) && vt_same_sig(m, g);
}

// ---------------------------------------------------------------------------
// Base subobjects of the most derived class and final overriders.

struct VSub { cls: i32, virt: u8, rsv: u8, rsv2: u16, off_md: i64, off_lc: i64 }
var vsubs: VSub[>..<] = [];
var vedges: u32[>..<] = [];     // (child, parent) pairs
var fo_memo: i32[>..<] = [];
var fo_fn: i64[>..<] = [];      // the candidates: (function, node)
var fo_node: i64[>..<] = [];

recursive fn vsub_build(cls: i64, virt: bool, off_md: i64, off_lc: i64, parent: i64, md: i64, lc: i64) {
    let n = vsubs.len;
    vsubs.push(VSub { cls: cls as! i32, virt: if virt { 1 } else { 0 }, rsv: 0, rsv2: 0, off_md: off_md, off_lc: off_lc });
    if parent >= 0 { vedges.push(n as! u32); vedges.push(parent as! u32); }
    for i in vt_nbases(cls) {
        let br = vt_base_rec(cls, i);
        if vt_base_virtual(cls, i) {
            var found: i64 = -1;
            for k in vsubs.len { if vsubs[k].virt == 1 && vsubs[k].cls as i64 == br { found = k; } }
            if found >= 0 { vedges.push(found as! u32); vedges.push(n as! u32); continue; }
            vsub_build(br, true, vt_vbo(md, br), vt_vbo(lc, br), n, md, lc);
        } else {
            let o = vt_base_off(cls, i);
            vsub_build(br, false, off_md + o, off_lc + o, n, md, lc);
        }
    }
}

// The node of the subobject of class cls at off_md.
fn vsub_find(cls: i64, off_md: i64) -> i64 {
    for k in vsubs.len { if vsubs[k].cls as i64 == cls && vsubs[k].off_md == off_md { return k; } }
    return -1;
}

// The topmost overrider of m on the paths from md to node n: a candidate
// index (-1 none).
recursive fn fo_up(n: i64, m: i64) -> i64 {
    if fo_memo[n] != -2 { return fo_memo[n] as i64; }
    var best: i64 = -1;
    var e = 0;
    while e < vedges.len {
        if vedges[e] as i64 == n {
            let c = fo_up(vedges[e + 1] as i64, m);
            if c >= 0 {
                if best < 0 { best = c; }
                else if fo_fn[c] != fo_fn[best] {
                    // the dominant one: the overrider in the more derived class
                    if vt_derived_from(method_class(fo_fn[c]), method_class(fo_fn[best])) { best = c; }
                }
            }
        }
        e += 2;
    }
    if best < 0 {
        let f = class_overrider(vsubs[n].cls as i64, m);
        if f >= 0 {
            best = fo_fn.len;
            fo_fn.push(f);
            fo_node.push(n);
        }
    }
    fo_memo[n] = best as! i32;
    return best;
}

// The final overrider of m for the subobject of m's class at off_md:
// (function, its subobject's offset in the layout class), or (-1, 0).
fn final_overrider(m: i64, off_md: i64) -> i64, i64 {
    let n = vsub_find(method_class(m), off_md);
    if n < 0 { return m, 0; }
    fo_memo.clear();
    for k in vsubs.len { fo_memo.push(-2); }
    fo_fn.clear();
    fo_node.clear();
    let c = fo_up(n, m);
    if c < 0 { return m, vsubs[n].off_lc; }
    return fo_fn[c], vsubs[fo_node[c]].off_lc;
}

// ---------------------------------------------------------------------------
// Vtable components and groups.

let VC_VCALL = 1;
let VC_VBASE = 2;
let VC_TOP = 3;
let VC_RTTI = 4;
let VC_FUNC = 5;
let VC_CDTOR = 6;       // the complete destructor (the deleting one follows)
let VC_DDTOR = 7;
let VC_UNUSED = 8;      // an unused function pointer (null)

struct VtComp { kind: u8, rsv: u8, rsv2: u16, thunk: i32, fsym: i64, val: i64 }
struct VtThunk { comp: i32, method: i32, this_nv: i64, this_vc: i64, ret_nv: i64, ret_vb: i64 }
struct VtAP { cls: i32, rsv: u32, off: i64, idx: i64 }   // a base subobject's address point (component index in the group)
struct VtMI { method: i64, base_off: i64, base_off_lc: i64, idx: i64 }
struct VtPair { a: i64, b: i64 }

struct VtGroup { md: i32, lc: i32, md_off: i64, ok: bool, c0: u32, nc: u32, ap0: u32, nap: u32, s0: u32, ns: u32, mi0: u32, nmi: u32,
                 vb0: u32, nvb: u32, th0: u32, nth: u32 }
var vgroups: VtGroup[>..] = [];
var vg_comps: VtComp[>..] = [];
var vg_aps: VtAP[>..] = [];
var vg_starts: u32[>..] = [];
var vg_midx: VtPair[>..] = [];      // (method or destructor (deleting: complete | 1 << 40), index from the primary address point)
var vg_vbo: VtPair[>..] = [];       // (virtual base, offset offset)
var vg_mthunks: VtThunk[>..] = [];  // thunks of md's own functions (method: the overrider)

// the group being built
var b_md: i64 = -1;
var b_lc: i64 = -1;
var b_mdoff: i64 = 0;
var b_mdvirt = false;
var b_ok = true;
var b_comps: VtComp[>..<] = [];
var b_thunks: VtThunk[>..<] = [];   // per component (comp), this and return adjustments
var b_aps: VtAP[>..<] = [];
var b_starts: u32[>..<] = [];
var b_mi: VtMI[>..<] = [];          // MethodInfoMap
var b_midx: VtPair[>..<] = [];
var b_vbo: VtPair[>..<] = [];       // md's VBaseOffsetOffsets
var b_vcvb: VtPair[>..<] = [];      // VCallOffsetsForVBases: (vbase << 32 | entry index into b_vcm)
var b_vcm: VtPair[>..<] = [];       // (method, offset offset) runs
var b_vcvb_runs: VtPair[>..<] = []; // (vbase, start << 32 | count) in b_vcm
var b_pvb: u32[>..<] = [];          // primary virtual bases (DeterminePrimaryVirtualBases)
var b_vvb: u32[>..<] = [];          // visited virtual bases
var b_pbases: u32[>..<] = [];       // PrimaryBases of AddMethods
var b_mthunks: VtThunk[>..<] = [];

// The group of (md, lc, md_off); built on first use.
fn vt_group(md: i64, lc: i64, md_off: i64, md_virt: bool) -> i64 {
    for g, i in vgroups { if g.md as i64 == md && g.lc as i64 == lc && g.md_off == md_off { return i; } }
    build_group(md, lc, md_off, md_virt);
    return vgroups.len - 1;
}

// The complete object vtable group of class r.
fn vt_class(r: i64) -> i64 { vt_group(r, r, 0, false) }

fn build_group(md: i64, lc: i64, md_off: i64, md_virt: bool) {
    b_md = md;
    b_lc = lc;
    b_mdoff = md_off;
    b_mdvirt = md_virt;
    b_ok = true;
    b_comps.clear();
    b_thunks.clear();
    b_aps.clear();
    b_starts.clear();
    b_mi.clear();
    b_midx.clear();
    b_vbo.clear();
    b_vcm.clear();
    b_vcvb_runs.clear();
    b_pvb.clear();
    b_vvb.clear();
    b_mthunks.clear();
    vsubs.clear();
    vedges.clear();
    vsub_build(md, md_virt, 0, md_off, -1, md, lc);
    // the primary virtual bases (DeterminePrimaryVirtualBases)
    vt_det_pvb(md, md_off);
    b_vvb.clear();
    lay_primary_and_secondary(md, 0, false, md_virt, md_off);
    b_vvb.clear();
    lay_vtables_for_vbases(md);
    // record the group
    let g = VtGroup { md: md as! i32, lc: lc as! i32, md_off: md_off, ok: b_ok, c0: vg_comps.len as! u32, nc: b_comps.len as! u32,
        ap0: vg_aps.len as! u32, nap: b_aps.len as! u32, s0: vg_starts.len as! u32, ns: b_starts.len as! u32,
        mi0: vg_midx.len as! u32, nmi: b_midx.len as! u32, vb0: vg_vbo.len as! u32, nvb: b_vbo.len as! u32,
        th0: vg_mthunks.len as! u32, nth: b_mthunks.len as! u32 };
    for c, i in b_comps {
        var x = c;
        x.thunk = -1;
        for t, j in b_thunks { if t.comp as i64 == i { x.thunk = j as! i32; } }
        vg_comps.push(x);
    }
    // the per-component thunks follow the components (indexed from th_all)
    for t in b_thunks { vg_cthunks.push(t); }
    g_cth.push(vg_cthunks.len as! u32 - b_thunks.len as! u32);
    for a in b_aps { vg_aps.push(a); }
    for s in b_starts { vg_starts.push(s); }
    for m in b_midx { vg_midx.push(m); }
    for v in b_vbo { vg_vbo.push(v); }
    for t in b_mthunks { vg_mthunks.push(t); }
    vgroups.push(g);
}
var vg_cthunks: VtThunk[>..] = [];
var g_cth: u32[>..] = [];           // per group: its first entry in vg_cthunks

fn vt_det_pvb(rd: i64, off_lc: i64) { vt_det_pvb1(rd, off_lc); }

recursive fn vt_det_pvb1(rd: i64, off_lc: i64) {
    let pb = vt_prim(rd);
    if pb >= 0 && vt_prim_virtual(rd) {
        var is_pvb = true;
        if b_lc != b_md {
            // a construction vtable: a primary base in the layout class only at the same offset
            if vt_vbo(b_lc, pb) != off_lc { is_pvb = false; }
        }
        if is_pvb { b_pvb.push(pb as! u32); }
    }
    for i in vt_nbases(rd) {
        let br = vt_base_rec(rd, i);
        var o: i64 = 0;
        if vt_base_virtual(rd, i) {
            var seen = false;
            for x in b_vvb { if x as i64 == br { seen = true; } }
            if seen { continue; }
            b_vvb.push(br as! u32);
            o = vt_vbo(b_lc, br);
        } else {
            o = off_lc + vt_base_off(rd, i);
        }
        vt_det_pvb1(br, o);
    }
}

fn in_pvb(r: i64) -> bool {
    for x in b_pvb { if x as i64 == r { return true; } }
    return false;
}

// LayoutPrimaryAndSecondaryVTables for base subobject (rd at off_md) at
// off_lc in the layout class.
recursive fn lay_primary_and_secondary(rd: i64, off_md: i64, morally_virtual: bool, virtual_in_lc: bool, off_lc: i64) {
    // vcall and vbase offsets
    vcvb_build(true, rd, off_md, virtual_in_lc, off_lc, b_md, b_lc);
    var k = vb_comps.len - 1;
    while k >= 0 { b_comps.push(vb_comps[k]); k--; }
    if virtual_in_lc && vb_vcm.len > 0 {
        var have = false;
        for r in b_vcvb_runs { if r.a == rd { have = true; } }
        if !have {
            let st = b_vcm.len;
            for x in vb_vcm { b_vcm.push(x); }
            b_vcvb_runs.push(VtPair { a: rd, b: ((st as i64) << 32) | (vb_vcm.len as i64) });
        }
    }
    if rd == b_md { for x in vb_vbo { b_vbo.push(x); } }
    // offset to top, RTTI
    b_comps.push(VtComp { kind: VC_TOP as! u8, rsv: 0, rsv2: 0, thunk: -1, fsym: -1, val: b_mdoff - off_lc });
    b_comps.push(VtComp { kind: VC_RTTI as! u8, rsv: 0, rsv2: 0, thunk: -1, fsym: b_md, val: 0 });
    let ap = b_comps.len;
    // the functions
    let pbm = b_pbases.len;
    add_methods(rd, off_md, off_lc, rd, off_lc, pbm);
    b_pbases.resize(pbm);
    if rd == b_md {
        for mi in b_mi {
            if cxs[mi.method].flags & CF_DTOR != 0 {
                b_midx.push(VtPair { a: mi.method, b: mi.idx - ap });
                b_midx.push(VtPair { a: mi.method | ((1 as i64) << 40), b: mi.idx - ap + 1 });
            } else {
                b_midx.push(VtPair { a: mi.method, b: mi.idx - ap });
            }
        }
    }
    compute_this_adjustments();
    // the address points of rd and its primary bases
    var r = rd;
    loop {
        b_aps.push(VtAP { cls: r as! i32, rsv: 0, off: off_lc, idx: ap });
        let pb = vt_prim(r);
        if pb < 0 { break; }
        if vt_prim_virtual(r) && vt_vbo(b_lc, pb) != off_lc { break; }
        r = pb;
    }
    // the vtable starts where its vcall/vbase offsets start
    b_starts.push((ap - 2 - vbs_count_for_start()) as! u32);
    lay_secondary(rd, off_md, morally_virtual, off_lc);
}
var vb_last_count: i64 = 0;
fn vbs_count_for_start() -> i64 { vb_last_count }

// LayoutSecondaryVTables.
recursive fn lay_secondary(rd: i64, off_md: i64, morally_virtual: bool, off_lc: i64) {
    let pb = vt_prim(rd);
    for i in vt_nbases(rd) {
        if vt_base_virtual(rd, i) { continue; }
        let br = vt_base_rec(rd, i);
        if !vt_dyn(br) { continue; }
        if b_lc != b_md {
            // construction vtables: only bases with virtual bases or morally virtual ones
            if !morally_virtual && !has_vb(br) { continue; }
        }
        let rel = vt_base_off(rd, i);
        if br == pb && !vt_prim_virtual(rd) {
            lay_secondary(br, off_md + rel, morally_virtual, off_lc + rel);
            continue;
        }
        lay_primary_and_secondary(br, off_md + rel, morally_virtual, false, off_lc + rel);
    }
}

// LayoutVTablesForVirtualBases.
recursive fn lay_vtables_for_vbases(rd: i64) {
    for i in vt_nbases(rd) {
        let br = vt_base_rec(rd, i);
        if vt_base_virtual(rd, i) && vt_dyn(br) && !in_pvb(br) {
            var seen = false;
            for x in b_vvb { if x as i64 == br { seen = true; } }
            if !seen {
                b_vvb.push(br as! u32);
                lay_primary_and_secondary(br, vt_vbo(b_md, br), true, true, vt_vbo(b_lc, br));
            }
        }
        if has_vb(br) { lay_vtables_for_vbases(br); }
    }
}

// ---------------------------------------------------------------------------
// The vcall and vbase offsets of a vtable (VCallAndVBaseOffsetBuilder):
// vb_comps from the address point outwards, vb_vcm the vcall offset
// offsets of the methods, vb_vbo the vbase offset offsets.

var vb_comps: VtComp[>..<] = [];
var vb_vcm: VtPair[>..<] = [];
var vb_vbo: VtPair[>..<] = [];
var vb_visited: u32[>..<] = [];
var vb_md: i64 = -1;
var vb_lc: i64 = -1;
var vb_overriders = false;

fn vcvb_build(overriders: bool, base: i64, off_md: i64, base_virtual: bool, off_lc: i64, md: i64, lc: i64) {
    vb_comps.clear();
    vb_vcm.clear();
    vb_vbo.clear();
    vb_visited.clear();
    vb_md = md;
    vb_lc = lc;
    vb_overriders = overriders;
    vcvb_add(base, off_md, base_virtual, off_lc);
    vb_last_count = vb_comps.len;
}

fn vb_offset_offset() -> i64 { -(3 + vb_comps.len) * 8 }

recursive fn vcvb_add(base: i64, off_md: i64, base_virtual: bool, real_off: i64) {
    let pb = vt_prim(base);
    if pb >= 0 {
        var poff: i64 = 0;
        if vt_prim_virtual(base) { poff = vt_vbo(vb_md, pb); } else { poff = off_md; }
        vcvb_add(pb, poff, vt_prim_virtual(base), real_off);
    }
    vcvb_vbase_offsets(base, real_off);
    if base_virtual { vcvb_vcall_offsets(base, off_md, real_off); }
}

recursive fn vcvb_vbase_offsets(rd: i64, off_lc: i64) {
    for i in vt_nbases(rd) {
        let br = vt_base_rec(rd, i);
        if vt_base_virtual(rd, i) {
            var seen = false;
            for x in vb_visited { if x as i64 == br { seen = true; } }
            if !seen {
                vb_visited.push(br as! u32);
                let off = vt_vbo(vb_lc, br) - off_lc;
                vb_vbo.push(VtPair { a: br, b: vb_offset_offset() });
                vb_comps.push(VtComp { kind: VC_VBASE as! u8, rsv: 0, rsv2: 0, thunk: -1, fsym: -1, val: off });
            }
        }
        vcvb_vbase_offsets(br, off_lc);
    }
}

recursive fn vcvb_vcall_offsets(rd: i64, off_md: i64, vbase_off: i64) {
    let pb = vt_prim(rd);
    if pb >= 0 && !vt_prim_virtual(rd) { vcvb_vcall_offsets(pb, off_md, vbase_off); }
    let mk = vm_list.len;
    push_vmethods(rd);
    for i in mk..vm_list.len {
        let m = vm_list[i] as i64;
        let oo = vb_offset_offset();
        var dup = false;
        for x in vb_vcm { if vt_same_sig(x.a, m) { dup = true; } }
        if dup { continue; }
        vb_vcm.push(VtPair { a: m, b: oo });
        var off: i64 = 0;
        if vb_overriders {
            let f, fo = final_overrider(m, off_md);
            off = fo - vbase_off;
            if f < 0 { }
        }
        vb_comps.push(VtComp { kind: VC_VCALL as! u8, rsv: 0, rsv2: 0, thunk: -1, fsym: -1, val: off });
    }
    vm_list.resize(mk);
    for i in vt_nbases(rd) {
        if vt_base_virtual(rd, i) { continue; }
        let br = vt_base_rec(rd, i);
        if br == pb { continue; }
        vcvb_vcall_offsets(br, off_md + vt_base_off(rd, i), vbase_off);
    }
}

// The vbase offset offset of virtual base v in class r's vtable.
fn vbase_offset_offset(r: i64, v: i64) -> i64 {
    // (the builder's state is its own: this may run while a group is built)
    let sc = vb_comps.len;
    let s_md = vb_md;
    let s_lc = vb_lc;
    let s_ov = vb_overriders;
    vbo_save.clear();
    for x in vb_comps { vbo_save.push(x); }
    let svc = vbo_save_vcm.len;
    for x in vb_vcm { vbo_save_vcm.push(x); }
    let svb = vbo_save_vbo.len;
    for x in vb_vbo { vbo_save_vbo.push(x); }
    let svv = vbo_save_vis.len;
    for x in vb_visited { vbo_save_vis.push(x); }
    vcvb_build(false, r, 0, false, 0, r, r);
    var res: i64 = 0;
    for x in vb_vbo { if x.a == v { res = x.b; } }
    // restore
    vb_comps.clear();
    for x in vbo_save { vb_comps.push(x); }
    vb_vcm.clear();
    for i in svc..vbo_save_vcm.len { vb_vcm.push(vbo_save_vcm[i]); }
    vbo_save_vcm.resize(svc);
    vb_vbo.clear();
    for i in svb..vbo_save_vbo.len { vb_vbo.push(vbo_save_vbo[i]); }
    vbo_save_vbo.resize(svb);
    vb_visited.clear();
    for i in svv..vbo_save_vis.len { vb_visited.push(vbo_save_vis[i]); }
    vbo_save_vis.resize(svv);
    vb_md = s_md;
    vb_lc = s_lc;
    vb_overriders = s_ov;
    if sc != vb_comps.len { }
    return res;
}
var vbo_save: VtComp[>..<] = [];
var vbo_save_vcm: VtPair[>..<] = [];
var vbo_save_vbo: VtPair[>..<] = [];
var vbo_save_vis: u32[>..<] = [];

// ---------------------------------------------------------------------------
// AddMethods and the adjustments.

fn mi_find(m: i64) -> i64 {
    for x, i in b_mi { if x.method == m { return i; } }
    return -1;
}

// Every virtual function of a proper base that m overrides, pushed to ov_list.
var ov_list: u32[>..<] = [];
recursive fn all_overridden(m: i64, rd: i64) {
    for i in vt_nbases(rd) {
        let br = vt_base_rec(rd, i);
        let mk = vm_list.len;
        push_vmethods(br);
        for j in mk..vm_list.len {
            let g = vm_list[j] as i64;
            if vt_same_sig(m, g) {
                var dup = false;
                for x in ov_list { if x as i64 == g { dup = true; } }
                if !dup { ov_list.push(g as! u32); }
            }
        }
        vm_list.resize(mk);
        all_overridden(m, br);
    }
}

// FindNearestOverriddenMethod over b_pbases[pbm..].
fn nearest_overridden(m: i64, pbm: i64) -> i64 {
    let om = ov_list.len;
    all_overridden(m, method_class(m));
    var res: i64 = -1;
    var k = b_pbases.len - 1;
    while k >= pbm && res < 0 {
        let pb = b_pbases[k] as i64;
        for j in om..ov_list.len { if method_class(ov_list[j] as i64) == pb { res = ov_list[j] as i64; break; } }
        k--;
    }
    ov_list.resize(om);
    return res;
}

// The base offset from the class of the return type of `derived` to that of
// `base` (a covariant override): (virtual base, non-virtual offset, the
// derived class); (-1, 0, -1) when there is no adjustment.
fn return_adjust_offset(derived: i64, base: i64) -> i64, i64, i64 {
    let dt = types[syms[derived].ty >> 4].base;
    let bt = types[syms[base].ty >> 4].base;
    if unqual(dt) == unqual(bt) { return -1, 0, -1; }
    if !(is_pointer(dt) || is_ref(dt)) || !(is_pointer(bt) || is_ref(bt)) { return -1, 0, -1; }
    let dc = unqual(tbase(dt));
    let bc = unqual(tbase(bt));
    if !is_record(dc) || !is_record(bc) || dc == bc { return -1, 0, -1; }
    let dr = rec_of(dc);
    let br = rec_of(bc);
    path_vb = -1;
    path_nv = 0;
    path_found = false;
    first_path(dr, br, -1, 0);
    if !path_found { return -1, 0, -1; }
    if path_vb < 0 && path_nv == 0 { return -1, 0, -1; }
    return path_vb, path_nv, dr;
}
var path_vb: i64 = -1;
var path_nv: i64 = 0;
var path_found = false;

recursive fn first_path(d: i64, b: i64, vb: i64, nv: i64) {
    if path_found { return; }
    if d == b { path_vb = vb; path_nv = nv; path_found = true; return; }
    for i in vt_nbases(d) {
        let br = vt_base_rec(d, i);
        if vt_base_virtual(d, i) { first_path(br, b, br, 0); }
        else { first_path(br, b, vb, nv + vt_base_off(d, i)); }
        if path_found { return; }
    }
}

// ComputeThisAdjustmentBaseOffset: the path from the overrider's subobject
// (class d at d_off) to the overridden one (class b at b_off) in the layout
// class: (virtual base, non-virtual offset to apply), found = false when none.
var tpath_ok = false;
var tpath_vb: i64 = -1;
var tpath_nv: i64 = 0;
recursive fn this_path(d: i64, b: i64, vb: i64, nv: i64, d_off: i64, b_off: i64) {
    if tpath_ok { return; }
    if d == b {
        var o = nv;
        if vb >= 0 { o += vt_vbo(b_lc, vb); } else { o += d_off; }
        if o == b_off { tpath_ok = true; tpath_vb = vb; tpath_nv = -nv; }
        return;
    }
    for i in vt_nbases(d) {
        let br = vt_base_rec(d, i);
        if vt_base_virtual(d, i) { this_path(br, b, br, 0, d_off, b_off); }
        else { this_path(br, b, vb, nv + vt_base_off(d, i), d_off, b_off); }
        if tpath_ok { return; }
    }
}

// The vcall offset offset of m for virtual base vb (VCallOffsetsForVBases).
fn vcall_offset_offset(vb: i64, m: i64) -> i64 {
    var run = VtPair { a: -1, b: 0 };
    for r in b_vcvb_runs { if r.a == vb { run = r; } }
    if run.a < 0 {
        vcvb_build(false, vb, 0, true, 0, b_md, b_md);
        let st = b_vcm.len;
        for x in vb_vcm { b_vcm.push(x); }
        run = VtPair { a: vb, b: ((st as i64) << 32) | (vb_vcm.len as i64) };
        b_vcvb_runs.push(run);
    }
    let st = run.b >> 32;
    let n = run.b & 0xFFFFFFFF;
    for i in st..st + n { if vt_same_sig(b_vcm[i].a, m) { return b_vcm[i].b; } }
    return 0;
}

// ComputeThisAdjustment: (non-virtual, vcall offset offset).
fn this_adjustment(m: i64, base_off_lc: i64, ovr: i64, ovr_off: i64) -> i64, i64 {
    if cxs[ovr].flags & CF_PURE != 0 { return 0, 0; }
    tpath_ok = false;
    this_path(method_class(ovr), method_class(m), -1, 0, ovr_off, base_off_lc);
    if !tpath_ok { return 0, 0; }
    var vc: i64 = 0;
    if tpath_vb >= 0 { vc = vcall_offset_offset(tpath_vb, m); }
    return tpath_nv, vc;
}

fn thunk_at(idx: i64) -> i64 {
    for t, i in b_thunks { if t.comp as i64 == idx { return i; } }
    b_thunks.push(VtThunk { comp: idx as! i32, method: -1, this_nv: 0, this_vc: 0, ret_nv: 0, ret_vb: 0 });
    return b_thunks.len - 1;
}

fn add_mthunk(f: i64, t: VtThunk) {
    for x in b_mthunks {
        if x.method as i64 == f && x.this_nv == t.this_nv && x.this_vc == t.this_vc && x.ret_nv == t.ret_nv && x.ret_vb == t.ret_vb { return; }
    }
    var y = t;
    y.method = f as! i32;
    b_mthunks.push(y);
}

// IsOverriderUsed.
fn overrider_used(ovr: i64, base_off_lc: i64, first_base: i64, first_off: i64) -> bool {
    if base_off_lc == first_off { return true; }
    if method_class(ovr) == first_base { return true; }
    let pm = pb_tmp.len;
    var r = first_base;
    pb_tmp.push(r as! u32);
    loop {
        let pb = vt_prim(r);
        if pb < 0 { break; }
        if vt_prim_virtual(r) && vt_vbo(b_lc, pb) != first_off { break; }
        pb_tmp.push(pb as! u32);
        r = pb;
    }
    let om = ov_list.len;
    all_overridden(ovr, method_class(ovr));
    var used = false;
    for j in om..ov_list.len {
        let c = method_class(ov_list[j] as i64);
        for k in pm..pb_tmp.len { if pb_tmp[k] as i64 == c { used = true; } }
    }
    ov_list.resize(om);
    pb_tmp.resize(pm);
    return used;
}
var pb_tmp: u32[>..<] = [];

recursive fn add_methods(rd: i64, off_md: i64, off_lc: i64, first_base: i64, first_off: i64, pbm: i64) {
    let pb = vt_prim(rd);
    if pb >= 0 {
        var poff: i64 = 0;
        var poff_lc: i64 = 0;
        if vt_prim_virtual(rd) { poff = vt_vbo(b_md, pb); poff_lc = vt_vbo(b_lc, pb); }
        else { poff = off_md; poff_lc = off_lc; }
        add_methods(pb, poff, poff_lc, first_base, first_off, pbm);
        b_pbases.push(pb as! u32);
    }
    let mk = vm_list.len;
    push_vmethods(rd);
    let nm = nv_new.len;
    for i in mk..vm_list.len {
        let m = vm_list[i] as i64;
        let ovr, ovr_off = final_overrider(m, off_md);
        let om = nearest_overridden(m, pbm);
        if om >= 0 {
            let rvb, rnv, rdc = return_adjust_offset(m, om);
            if rvb < 0 && rnv == 0 {
                // the primary base's slot, now m's
                let k = mi_find(om);
                if k >= 0 {
                    let idx = b_mi[k].idx;
                    b_mi[k] = VtMI { method: m, base_off: off_md, base_off_lc: off_lc, idx: idx };
                }
                if b_lc == b_md && om != m {
                    let tnv, tvc = this_adjustment(om, off_lc, ovr, ovr_off);
                    if tvc != 0 && method_class(ovr) == b_md {
                        let qvb, qnv, qdc = return_adjust_offset(ovr, m);
                        var t = VtThunk { comp: -1, method: -1, this_nv: tnv, this_vc: tvc, ret_nv: 0, ret_vb: 0 };
                        if qvb >= 0 || qnv != 0 { t.ret_nv = qnv; if qvb >= 0 { t.ret_vb = ret_vbo(qdc, qvb); } }
                        add_mthunk(ovr, t);
                    }
                }
                continue;
            }
        }
        nv_new.push(m as! u32);
    }
    vm_list.resize(mk);
    for i in nm..nv_new.len {
        let m = nv_new[i] as i64;
        let ovr, ovr_off = final_overrider(m, off_md);
        b_mi.push(VtMI { method: m, base_off: off_md, base_off_lc: off_lc, idx: b_comps.len });
        if !overrider_used(ovr, off_lc, first_base, first_off) {
            b_comps.push(VtComp { kind: VC_UNUSED as! u8, rsv: 0, rsv2: 0, thunk: -1, fsym: ovr, val: 0 });
            if cxs[m].flags & CF_DTOR != 0 { b_comps.push(VtComp { kind: VC_UNUSED as! u8, rsv: 0, rsv2: 0, thunk: -1, fsym: ovr, val: 0 }); }
            continue;
        }
        if cxs[ovr].flags & CF_PURE == 0 {
            let rvb, rnv, rdc = return_adjust_offset(ovr, m);
            if rvb >= 0 || rnv != 0 {
                let t = thunk_at(b_comps.len);
                b_thunks[t].method = m as! i32;
                b_thunks[t].ret_nv = rnv;
                if rvb >= 0 { b_thunks[t].ret_vb = ret_vbo(rdc, rvb); }
            }
        }
        if cxs[m].flags & CF_DTOR != 0 {
            b_comps.push(VtComp { kind: VC_CDTOR as! u8, rsv: 0, rsv2: 0, thunk: -1, fsym: ovr, val: 0 });
            b_comps.push(VtComp { kind: VC_DDTOR as! u8, rsv: 0, rsv2: 0, thunk: -1, fsym: ovr, val: 0 });
        } else {
            b_comps.push(VtComp { kind: VC_FUNC as! u8, rsv: 0, rsv2: 0, thunk: -1, fsym: ovr, val: 0 });
        }
    }
    nv_new.resize(nm);
}
var nv_new: u32[>..<] = [];

// The vbase offset offset of a return adjustment's virtual base.
fn ret_vbo(dc: i64, vb: i64) -> i64 {
    if dc == b_md {
        for x in b_vbo { if x.a == vb { return x.b; } }
    }
    return vbase_offset_offset(dc, vb);
}

// ComputeThisAdjustments: the this adjustments of the vtable just laid out.
fn compute_this_adjustments() {
    for mi in b_mi {
        let idx = mi.idx;
        if b_comps[idx].kind as i64 == VC_UNUSED { continue; }
        let ovr, ovr_off = final_overrider(mi.method, mi.base_off);
        if mi.base_off_lc == ovr_off {
            var ret = false;
            for t in b_thunks { if t.comp as i64 == idx && (t.ret_nv != 0 || t.ret_vb != 0) { ret = true; } }
            if !ret { continue; }
        }
        let tnv, tvc = this_adjustment(mi.method, mi.base_off_lc, ovr, ovr_off);
        if tnv == 0 && tvc == 0 { continue; }
        let t = thunk_at(idx);
        if b_thunks[t].method < 0 { b_thunks[t].method = mi.method as! i32; }
        b_thunks[t].this_nv = tnv;
        b_thunks[t].this_vc = tvc;
        if cxs[mi.method].flags & CF_DTOR != 0 {
            let t2 = thunk_at(idx + 1);
            if b_thunks[t2].method < 0 { b_thunks[t2].method = mi.method as! i32; }
            b_thunks[t2].this_nv = tnv;
            b_thunks[t2].this_vc = tvc;
        }
    }
    b_mi.clear();
    if b_lc != b_md { return; }
    for t in b_thunks {
        let c = b_comps[t.comp];
        if c.kind as i64 == VC_DDTOR { continue; }
        if c.kind as i64 != VC_FUNC && c.kind as i64 != VC_CDTOR { continue; }
        if method_class(c.fsym) == b_md { add_mthunk(c.fsym, t); }
    }
}

// ---------------------------------------------------------------------------
// Queries on complete-object groups.

fn group_ok(g: i64) -> bool { vgroups[g].ok }

// The vtable index (from the primary address point) of virtual function f
// in its class's vtable (deleting: the deleting destructor's), or -1.
fn vt_method_index(f: i64, deleting: bool) -> i64 {
    let g = vt_class(method_class(f));
    let G = vgroups[g];
    let key = f | (if deleting { (1 as i64) << 40 } else { 0 });
    for i in G.mi0..G.mi0 + G.nmi { if vg_midx[i].a == key { return vg_midx[i].b; } }
    // an implicit destructor stands for the class's destructor
    if cxs[f].flags & CF_DTOR != 0 {
        for i in G.mi0..G.mi0 + G.nmi {
            let a = vg_midx[i].a & 0xFFFFFFFFFF;
            let del = vg_midx[i].a >> 40 != 0;
            if del == deleting && cxs[a].flags & CF_DTOR != 0 { return vg_midx[i].b; }
        }
    }
    return -1;
}

// The address point (component index in the group) of base subobject
// (cls at off) in group g, or -1.
fn vt_address_point(g: i64, cls: i64, off: i64) -> i64 {
    let G = vgroups[g];
    for i in G.ap0..G.ap0 + G.nap { if vg_aps[i].cls as i64 == cls && vg_aps[i].off == off { return vg_aps[i].idx; } }
    return -1;
}

// The vbase offset offset of virtual base v in class r's vtable.
fn class_vbo(r: i64, v: i64) -> i64 {
    let g = vt_class(r);
    let G = vgroups[g];
    for i in G.vb0..G.vb0 + G.nvb { if vg_vbo[i].a == v { return vg_vbo[i].b; } }
    return vbase_offset_offset(r, v);
}

// ---------------------------------------------------------------------------
// The VTT (VTTBuilder): components (vtable group: 0 the complete one, else
// a construction group; base subobject), the sub-VTT indices and the
// secondary virtual pointer indices.

struct VttEnt { grp: i64, cls: i32, rsv: u32, off: i64 }
struct VttInfo { ok: bool, e0: u32, ne: u32, s0: u32, ns: u32, p0: u32, np: u32 }
var vtts = dictionary<u64, u32> {};
var vtt_infos: VttInfo[>..] = [];
var vtt_ents: VttEnt[>..] = [];
var vtt_sub: VtAP[>..] = [];        // (cls, off, index): sub-VTT indices
var vtt_svp: VtAP[>..] = [];        // (cls, off, index): secondary virtual pointer indices
var vtt_vts: VtAP[>..<] = [];       // the VTT's vtables: (cls, off, virtual in idx)
var vtt_md: i64 = -1;
var vtt_vvb: u32[>..<] = [];

fn vtt_of(r: i64) -> i64 {
    let g = vtts.get(r as u64);
    if g { return g as i64; }
    vtt_md = r;
    vtt_vts.clear();
    let e0 = vtt_ents.len;
    vtt_cur_e0 = e0;
    let s0 = vtt_sub.len;
    let p0 = vtt_svp.len;
    vtt_layout(r, 0, false);
    // the construction groups
    let ebase = vtt_ents.len;
    for e in e0..ebase {
        let vi = vtt_ents[e].grp;
        let V = vtt_vts[vi];
        var grp: i64 = 0;
        if vi == 0 { grp = vt_class(r); }
        else { grp = vt_group(V.cls as i64, r, V.off, V.idx != 0); }
        vtt_ents[e].grp = grp;
    }
    let info = VttInfo { ok: true, e0: e0 as! u32, ne: (vtt_ents.len - e0) as! u32, s0: s0 as! u32, ns: (vtt_sub.len - s0) as! u32,
        p0: p0 as! u32, np: (vtt_svp.len - p0) as! u32 };
    vtt_infos.push(info);
    vtts.insert(r as u64, (vtt_infos.len - 1) as! u32);
    return vtt_infos.len - 1;
}

recursive fn vtt_layout(rd: i64, off: i64, virt: bool) {
    if !has_vb(rd) { return; }
    let primary = rd == vtt_md;
    if !primary { vtt_sub.push(VtAP { cls: rd as! i32, rsv: 0, off: off, idx: vtt_ents.len - vtt_e0() }); }
    let vi = vtt_vts.len;
    vtt_vts.push(VtAP { cls: rd as! i32, rsv: 0, off: off, idx: if virt { 1 } else { 0 } });
    vtt_add(rd, off, vi, rd);
    // the secondary VTTs
    for i in vt_nbases(rd) {
        if vt_base_virtual(rd, i) { continue; }
        vtt_layout(vt_base_rec(rd, i), off + vt_base_off(rd, i), false);
    }
    // the secondary virtual pointers
    let vm = vtt_vvb.len;
    vtt_svps(rd, off, false, vi, rd);
    vtt_vvb.resize(vm);
    if primary {
        let vm2 = vtt_vvb.len;
        vtt_virtual(rd);
        vtt_vvb.resize(vm2);
    }
}
fn vtt_e0() -> i64 { vtt_cur_e0 }
var vtt_cur_e0: i64 = 0;

fn vtt_add(cls: i64, off: i64, vi: i64, vtable_cls: i64) {
    if vtable_cls == vtt_md { vtt_svp.push(VtAP { cls: cls as! i32, rsv: 0, off: off, idx: vtt_ents.len - vtt_cur_e0 }); }
    vtt_ents.push(VttEnt { grp: vi, cls: cls as! i32, rsv: 0, off: off });
}

recursive fn vtt_svps(rd: i64, off: i64, morally_virtual: bool, vi: i64, vtable_cls: i64) {
    if !has_vb(rd) && !morally_virtual { return; }
    for i in vt_nbases(rd) {
        let br = vt_base_rec(rd, i);
        if !vt_dyn(br) { continue; }
        var mv = morally_virtual;
        var nvprim = false;
        var boff: i64 = 0;
        if vt_base_virtual(rd, i) {
            var seen = false;
            for x in vtt_vvb { if x as i64 == br { seen = true; } }
            if seen { continue; }
            vtt_vvb.push(br as! u32);
            boff = vt_vbo(vtt_md, br);
            mv = true;
        } else {
            boff = off + vt_base_off(rd, i);
            if !vt_prim_virtual(rd) && vt_prim(rd) == br { nvprim = true; }
        }
        if !nvprim && (has_vb(br) || mv) { vtt_add(br, boff, vi, vtable_cls); }
        vtt_svps(br, boff, mv, vi, vtable_cls);
    }
}

recursive fn vtt_virtual(rd: i64) {
    for i in vt_nbases(rd) {
        let br = vt_base_rec(rd, i);
        if vt_base_virtual(rd, i) {
            var seen = false;
            for x in vtt_vvb { if x as i64 == br { seen = true; } }
            if seen { continue; }
            vtt_vvb.push(br as! u32);
            vtt_layout(br, vt_vbo(vtt_md, br), true);
        }
        if has_vb(br) { vtt_virtual(br); }
    }
}

fn vtt_sub_index(r: i64, cls: i64, off: i64) -> i64 {
    let vi = vtt_of(r);
    let v = vtt_infos[vi];
    for i in v.s0..v.s0 + v.ns { if vtt_sub[i].cls as i64 == cls && vtt_sub[i].off == off { return vtt_sub[i].idx; } }
    return 0;
}

fn vtt_svp_index(r: i64, cls: i64, off: i64) -> i64 {
    let vi = vtt_of(r);
    let v = vtt_infos[vi];
    for i in v.p0..v.p0 + v.np { if vtt_svp[i].cls as i64 == cls && vtt_svp[i].off == off { return vtt_svp[i].idx; } }
    return 0;
}

// ---------------------------------------------------------------------------
// Thunk names (Itanium 5.1.4: _ZTh / _ZTv / _ZTc).

fn call_offset(nm: u8[>..]&, nv: i64, vc: i64) {
    if vc == 0 {
        nm.push('h');
        num_n(nm, nv);
        nm.push('_');
    } else {
        nm.push('v');
        num_n(nm, nv);
        nm.push('_');
        num_n(nm, vc);
        nm.push('_');
    }
}

fn num_n(nm: u8[>..]&, v: i64) {
    if v < 0 { nm.push('n'); format(nm, -v); } else { format(nm, v); }
}

// The mangled name of the thunk t for function f, into thunk_name (false:
// f cannot be mangled).
var thunk_name: u8[>..] = [];
fn mangle_thunk(f: i64, t: VtThunk) -> bool {
    thunk_name.clear();
    mg_structor = 1;
    if !mangle_sym(f) { return false; }
    let enc = mg[2..];
    thunk_name.append("_ZT");
    let ret = t.ret_nv != 0 || t.ret_vb != 0;
    if ret {
        thunk_name.push('c');
        call_offset(thunk_name, t.this_nv, t.this_vc);
        call_offset(thunk_name, t.ret_nv, t.ret_vb);
    } else {
        call_offset(thunk_name, t.this_nv, t.this_vc);
    }
    thunk_name.append(enc);
    return true;
}
