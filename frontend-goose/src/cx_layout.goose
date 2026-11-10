// goosecc D1: the facts of a completed C++ class (polymorphic, dynamic,
// empty, POD for the purpose of layout, user-declared special members)
// and its layout as the Itanium C++ ABI and clang's
// ItaniumRecordLayoutBuilder compute it: the vtable pointer, the primary
// base, non-virtual bases (empty bases at offset 0 when no other empty
// subobject of their type is there), the fields (C's rules for
// bit-fields, packing and alignment), virtual bases, and the data size
// (tail padding is reused in a derived class unless the base is POD in
// the C++03 sense).

namespace cx;

import std;
import dictionary;
import .common;
import .types;
import .ast;
import .sema;
import .cx_core;
import .cx_names;

// The member functions declared in each class (in order): crecs[r].mfirst .. + mcount.
var cmscratch: u32[>..<] = [];
var cmem: u32[>..] = [];
struct MemRange { first: u32, count: u32 }
var crec_mems: MemRange[>..] = [];

fn mem_range(r: i64) -> MemRange {
    if r < crec_mems.len { return crec_mems[r]; }
    return MemRange { first: 0, count: 0 };
}

// Is f's signature (name, parameters, cv) the same as g's (an override)?
fn overrides(f: i64, g: i64) -> bool {
    if syms[f].name != syms[g].name { return false; }
    let a = types[syms[f].ty >> 4];
    let b = types[syms[g].ty >> 4];
    if a.n != b.n { return false; }
    if (a.flags & (TF_MCONST | TF_MVOLATILE)) != (b.flags & (TF_MCONST | TF_MVOLATILE)) { return false; }
    for i in a.n { if tparams[a.extra + i] != tparams[b.extra + i] { return false; } }
    return true;
}

// Does some base of r (transitively) declare a virtual function that f overrides?
recursive fn overrides_base_virtual(r: i64, f: i64) -> bool {
    let cr = crecs[r];
    for i in cr.nbases {
        let bt = cbases[cr.bases + i].ty;
        if !is_record(bt) { continue; }
        let br = rec_of(bt);
        let m = mem_range(br);
        for j in m.count {
            let g = cmem[m.first + j] as i64;
            if cxs[g].flags & CF_VIRTUAL != 0 && (overrides(f, g) || (cxs[f].flags & CF_DTOR != 0 && cxs[g].flags & CF_DTOR != 0)) { return true; }
        }
        if overrides_base_virtual(br, f) { return true; }
    }
    return false;
}

recursive fn has_vbase(r: i64) -> bool {
    let cr = crecs[r];
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if b.flags & BF_VIRTUAL != 0 { return true; }
        if is_record(b.ty) && has_vbase(rec_of(b.ty)) { return true; }
    }
    return false;
}

fn class_facts(r: i64) {
    var f: u32 = 0;
    let cr = crecs[r];
    let m = mem_range(r);
    var own_virtual = false;
    for j in m.count {
        let s = cmem[m.first + j] as i64;
        let fl = cxs[s].flags;
        if fl & CF_IMPLICIT != 0 { continue; }
        if fl & CF_CTOR != 0 { f = f | CR_USER_CTOR; }
        if fl & CF_DTOR != 0 { f = f | CR_USER_DTOR; }
        if fl & CF_OPERATOR != 0 && cxs[s].op as i64 == OP_EQUAL { f = f | CR_HAS_USER_COPY; }
        if fl & CF_VIRTUAL == 0 && fl & CF_STATIC == 0 && overrides_base_virtual(r, s) {
            cxs[s].flags = cxs[s].flags | CF_VIRTUAL;
        }
        if cxs[s].flags & CF_VIRTUAL != 0 { own_virtual = true; }
        if cxs[s].flags & CF_PURE != 0 { f = f | CR_ABSTRACT; }
    }
    var any_base = false;
    var all_bases_empty = true;
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        any_base = true;
        if !is_record(b.ty) { all_bases_empty = false; continue; }
        let bf = crecs[rec_of(b.ty)].flags;
        if bf & CR_POLY != 0 { f = f | CR_POLY; }
        if bf & CR_EMPTY == 0 { all_bases_empty = false; }
        if bf & CR_NONTRIVIAL_DTOR != 0 { f = f | CR_NONTRIVIAL_DTOR; }
    }
    if own_virtual { f = f | CR_POLY; }
    if has_vbase(r) { f = f | CR_HAS_VBASE; }
    if f & (CR_POLY | CR_HAS_VBASE) != 0 { f = f | CR_DYNAMIC; }
    // POD for the purpose of layout (C++03): clang's isPOD
    var pod = !any_base && f & (CR_POLY | CR_USER_CTOR | CR_USER_DTOR | CR_HAS_USER_COPY) == 0;
    var nfields = 0;
    let rec = records[r];
    for i in rec.first..rec.first + rec.count {
        let fd = fields[i];
        if fd.width == 0 && fd.name == 0 { continue; }
        if !(fd.width >= 0 && fd.name == 0) { nfields++; }
        let ft = fd.ty;
        if is_ref(ft) { pod = false; }
        let bt = base_elem_t(ft);
        if is_record(bt) && !is_opaque(bt) {
            let ff = crecs[rec_of(bt)].flags;
            if ff & CR_NOT_POD != 0 { pod = false; }
            if ff & CR_NONTRIVIAL_DTOR != 0 { f = f | CR_NONTRIVIAL_DTOR; }
        }
        if fd.width >= 0 && fd.name == 0 { continue; }
    }
    if member_access_nonpublic(r) || has_nsdmi(r) { pod = false; }
    if !pod { f = f | CR_NOT_POD; }
    if f & CR_USER_DTOR != 0 { f = f | CR_NONTRIVIAL_DTOR; }
    if f & CR_DYNAMIC != 0 { f = f | CR_NONTRIVIAL_DTOR & 0; }
    if nfields == 0 && f & CR_DYNAMIC == 0 && all_bases_empty { f = f | CR_EMPTY; }
    crecs[r].flags = (crecs[r].flags & (CR_PATTERN | CR_CLASS_KW)) | f;
}

fn base_elem_t(t: u32) -> u32 {
    var x = t;
    while kind_of(x) == TY_ARRAY { x = tbase(x); }
    return x;
}

// Non-public non-static data members (the class is then not POD).
fn member_access_nonpublic(r: i64) -> bool {
    let sc = crecs[r].scope as i64;
    let rec = records[r];
    for i in rec.first..rec.first + rec.count {
        let fd = fields[i];
        if fd.name == 0 { continue; }
        var s = scope_find(sc, fd.name);
        while s >= 0 {
            if syms[s].kind as i64 == SK_FIELD && cxs[s].access != 0 { return true; }
            s = cxs[s].nnext as i64;
        }
    }
    return false;
}

fn has_nsdmi(r: i64) -> bool {
    let sc = crecs[r].scope as i64;
    let rec = records[r];
    for i in rec.first..rec.first + rec.count {
        let fd = fields[i];
        if fd.name == 0 { continue; }
        var s = scope_find(sc, fd.name);
        while s >= 0 {
            if syms[s].kind as i64 == SK_FIELD && cxs[s].body != 0 { return true; }
            s = cxs[s].nnext as i64;
        }
    }
    return false;
}

// ---------------------------------------------------------------------------
// Empty subobjects placed so far in the class being laid out: (record, offset).
var empties: i64[>..<] = [];

// Can the empty-class subobjects of class `t` be placed at offset `off`?
recursive fn can_place(t: u32, off: i64) -> bool {
    let r = rec_of(t);
    if crecs[r].flags & CR_EMPTY != 0 {
        var i = 0;
        while i + 1 < empties.len {
            if empties[i] == r && empties[i + 1] == off { return false; }
            i += 2;
        }
    }
    let cr = crecs[r];
    for j in cr.nbases {
        let b = cbases[cr.bases + j];
        if !is_record(b.ty) || b.flags & BF_VIRTUAL != 0 { continue; }
        if !can_place(b.ty, off + b.offset) { return false; }
    }
    let rec = records[r];
    for j in rec.first..rec.first + rec.count {
        let ft = base_elem_t(fields[j].ty);
        if is_record(ft) && !is_opaque(ft) && fields[j].width < 0 {
            if !can_place(ft, off + fields[j].offset) { return false; }
        }
    }
    return true;
}

recursive fn note_empties(t: u32, off: i64) {
    let r = rec_of(t);
    if crecs[r].flags & CR_EMPTY != 0 { empties.push(r); empties.push(off); }
    let cr = crecs[r];
    for j in cr.nbases {
        let b = cbases[cr.bases + j];
        if !is_record(b.ty) || b.flags & BF_VIRTUAL != 0 { continue; }
        note_empties(b.ty, off + b.offset);
    }
    let rec = records[r];
    for j in rec.first..rec.first + rec.count {
        let ft = base_elem_t(fields[j].ty);
        if is_record(ft) && !is_opaque(ft) && fields[j].width < 0 {
            note_empties(ft, off + fields[j].offset);
        }
    }
}

// The layout of class r.
fn cx_layout(r: i64) {
    let rec = records[r];
    let cr = crecs[r];
    let is_union = rec.flags & RF_UNION != 0;
    let packed = rec.flags & RF_PACKED != 0;
    let pack_bits = (rec.pack as i64) * 8;
    let emark = empties.len;
    // opaque members (dependent, unknown): no layout
    for i in rec.first..rec.first + rec.count {
        let ft = fields[i].ty;
        if is_ref(ft) { continue; }
        let flex = kind_of(ft) == TY_ARRAY && types[ft >> 4].n < 0;
        if is_opaque(ft) || (!is_complete(ft) && !flex) || (!flex && type_size(ft) < 0) {
            mark_unknown_layout(r);
            return;
        }
    }
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if !is_record(b.ty) || is_opaque(b.ty) || records[rec_of(b.ty)].size < 0 { mark_unknown_layout(r); return; }
    }
    var data_bits: i64 = 0;
    var size_bits: i64 = 0;
    var al_bits: i64 = 8;
    // the primary base: the first non-virtual dynamic base, else a nearly
    // empty virtual base (D3: clang's DeterminePrimaryBase)
    var primary = -1;
    var vprimary: i64 = -1;
    crecs[r].primary = -1;
    crecs[r].flags = crecs[r].flags & ~(CR_PRIM_VIRTUAL as! u32);
    if cr.flags & CR_DYNAMIC != 0 {
        for i in cr.nbases {
            let b = cbases[cr.bases + i];
            if b.flags & BF_VIRTUAL == 0 && crecs[rec_of(b.ty)].flags & CR_DYNAMIC != 0 { primary = i; break; }
        }
        if primary < 0 { vprimary = primary_vbase(r); }
        if primary < 0 && vprimary < 0 {
            // the vtable pointer
            data_bits = 64;
            size_bits = 64;
            al_bits = 64;
        }
    }
    let vb_mark = vbs.len;
    if vprimary >= 0 {
        // the primary virtual base, at offset 0
        let bc = crecs[vprimary];
        crecs[r].primary = vprimary as! i32;
        crecs[r].flags = crecs[r].flags | (CR_PRIM_VIRTUAL as! u32);
        note_empties(records[vprimary].ty << 4, 0);
        data_bits = bc.nvsize * 8;
        size_bits = bc.nvsize * 8;
        if bc.nvalign * 8 > al_bits { al_bits = bc.nvalign * 8; }
        vbase_off.insert(((r as u64) << 32) | (vprimary as u64), 0);
    }
    // non-virtual bases (the primary first)
    var order = 0;
    while order <= cr.nbases as i64 {
        var i = 0;
        if order == 0 {
            if primary < 0 { order++; continue; }
            i = primary;
        } else {
            i = order - 1;
            if i == primary { order++; continue; }
        }
        order++;
        let b = cbases[cr.bases + i];
        if b.flags & BF_VIRTUAL != 0 { continue; }
        let br = rec_of(b.ty);
        let bc = crecs[br];
        var bal = bc.nvalign * 8;
        if packed { bal = 8; }
        var off: i64 = 0;
        if bc.flags & CR_EMPTY != 0 {
            // an empty base: offset 0 if no other empty subobject of its type is there
            off = 0;
            while !can_place(b.ty, off / 8) { off = round_up(if off == 0 { data_bits } else { off + bal }, bal); }
        } else {
            off = round_up(data_bits, bal);
            while !can_place(b.ty, off / 8) { off += bal; }
        }
        cbases[cr.bases + i].offset = off / 8;
        if i == primary { cbases[cr.bases + i].flags = cbases[cr.bases + i].flags | BF_PRIMARY; crecs[r].primary = br as! i32; }
        note_empties(b.ty, off / 8);
        if bc.flags & CR_EMPTY == 0 {
            data_bits = off + bc.nvsize * 8;
            if off + bc.nvsize * 8 > size_bits { size_bits = off + bc.nvsize * 8; }
        } else {
            if off + 8 > size_bits { size_bits = off + 8; }
        }
        if size_bits < data_bits { size_bits = data_bits; }
        if bal > al_bits { al_bits = bal; }
    }
    // the fields
    var unfilled: i64 = 0;
    for i in rec.first..rec.first + rec.count {
        let f = fields[i];
        let ft = f.ty;
        var tsize = type_size(ft);
        var talign = type_align(ft);
        if is_ref(ft) { tsize = 8; talign = 8; }
        let fpacked = packed || f.flags & FF_PACKED != 0;
        let explicit_bits = (f.attr_align as i64) * 8;
        if kind_of(ft) == TY_ARRAY && types[ft >> 4].n < 0 {
            tsize = 0;
            records[r].flags = records[r].flags | RF_FLEX;
        }
        if f.width >= 0 {
            // a bit-field: C's rules (types.goose layout_record, clang's Itanium builder)
            let w = f.width as i64;
            let unit_bits = tsize * 8;
            var fal = talign * 8;
            if fpacked && w > 0 { fal = 8; }
            if explicit_bits > fal { fal = explicit_bits; }
            if fpacked && explicit_bits == 0 && w > 0 { fal = 1; }
            if pack_bits > 0 && w > 0 {
                if fpacked { fal = pack_bits; } else if fal > pack_bits { fal = pack_bits; }
            }
            var off: i64 = 0;
            if !is_union {
                off = data_bits - unfilled;
                let allow_padding = pack_bits == 0;
                if w == 0 || (allow_padding && fal > 1 && (off % fal) + w > unit_bits) {
                    off = round_up(off, fal);
                } else if explicit_bits > 0 && (pack_bits == 0 || explicit_bits <= pack_bits) {
                    off = round_up(off, explicit_bits);
                }
            }
            fields[i].bitpos = off;
            let ual = if fal >= 8 { fal } else { 8 };
            fields[i].offset = (off / ual) * (ual / 8);
            if f.name == 0 { fal = 1; }
            if is_union {
                let rs = round_up(w, 8);
                if rs > data_bits { data_bits = rs; }
            } else {
                let nb = off + w;
                data_bits = round_up(nb, 8);
                unfilled = data_bits - nb;
            }
            if fal / 8 * 8 > al_bits { al_bits = fal / 8 * 8; }
            if data_bits > size_bits { size_bits = data_bits; }
            continue;
        }
        var fal = talign * 8;
        if fpacked { fal = 8; }
        if explicit_bits > fal { fal = explicit_bits; }
        if pack_bits > 0 && fal > pack_bits { fal = pack_bits; }
        if fal > al_bits { al_bits = fal; }
        let fs = if tsize < 0 { 0 } else { tsize * 8 };
        unfilled = 0;
        if is_union {
            fields[i].offset = 0;
            fields[i].bitpos = 0;
            if fs > data_bits { data_bits = fs; }
            if data_bits > size_bits { size_bits = data_bits; }
            continue;
        }
        var off = round_up(data_bits, fal);
        let bt = base_elem_t(ft);
        if is_record(bt) && !is_opaque(bt) {
            while !can_place(bt, off / 8) { off += fal; }
        }
        fields[i].offset = off / 8;
        fields[i].bitpos = off;
        if is_record(bt) && !is_opaque(bt) { note_empties(bt, off / 8); }
        data_bits = off + fs;
        if data_bits > size_bits { size_bits = data_bits; }
    }
    if rec.attr_align as i64 * 8 > al_bits { al_bits = rec.attr_align as i64 * 8; }
    let nvsize = round_up(size_bits, 8) / 8;
    let nval = al_bits / 8;
    let dsize_nv = round_up(data_bits, 8) / 8;
    // virtual bases (D3: clang's LayoutVirtualBases: inheritance graph
    // order, not the primary virtual base nor the indirect primary ones)
    vb_scratch_mark = vbs.len;
    let ipm = ipb.len;
    indirect_primaries(r);
    if vprimary >= 0 { ipb.push(vprimary as! u32); vbs.push(records[vprimary].ty << 4); }
    let laid = vbs.len;
    order_vbases(r, r, ipm);
    var vdata = data_bits;
    var vsize = size_bits;
    var i = laid;
    while i < vbs.len {
        let vt = vbs[i];
        i++;
        let br = rec_of(vt);
        let bc = crecs[br];
        let bal = bc.nvalign * 8;
        var off: i64 = 0;
        if bc.flags & CR_EMPTY != 0 && can_place(vt, 0) {
            off = 0;
            if records[br].size * 8 > vsize { vsize = records[br].size * 8; }
        } else {
            off = round_up(vdata, bal);
            while !can_place(vt, off / 8) { off += bal; }
            if bc.flags & CR_EMPTY == 0 {
                vdata = off + bc.nvsize * 8;
                if vdata > vsize { vsize = vdata; }
            } else if off + records[br].size * 8 > vsize { vsize = off + records[br].size * 8; }
        }
        note_empties(vt, off / 8);
        vbase_off.insert(((r as u64) << 32) | (br as u64), (off / 8) as u64);
        if bal > al_bits { al_bits = bal; }
    }
    ipb.resize(ipm);
    vbs.resize(vb_scratch_mark);
    // the indirect primary virtual bases share their deriver's address
    claim_primary_vbases(r, r, 0);
    if vb_mark == vbs.len { }
    var size = round_up(vsize, 8) / 8;
    let al = al_bits / 8;
    if size == 0 { size = 1; }
    size = round_up(size, al);
    let pod = crecs[r].flags & CR_NOT_POD == 0;
    records[r].size = size;
    records[r].align = al as! u32;
    records[r].flags = records[r].flags | RF_COMPLETE;
    types[rec.ty].size = size;
    types[rec.ty].align = al as! u32;
    crecs[r].dsize = if pod { size } else { round_up(vdata, 8) / 8 };
    crecs[r].nvsize = if pod { size } else { nvsize };
    crecs[r].nvalign = nval;
    crecs[r].flags = crecs[r].flags | CR_LAYOUT;
    if crecs[r].dsize == 0 && crecs[r].flags & CR_EMPTY == 0 { crecs[r].dsize = size; }
    empties.resize(emark);
}

var vbs: u32[>..<] = [];
let CR_PRIM_VIRTUAL = 524288;      // D3: the primary base (crecs.primary) is a virtual base
var ipb: u32[>..<] = [];           // the indirect primary virtual bases of the class being laid out
var ne_first: i64 = -1;

// The record of the virtual base offset of virtual base br in class r, or -1.
fn vbase_offset_of(r: i64, br: i64) -> i64 {
    let g = vbase_off.get(((r as u64) << 32) | (br as u64));
    if g { return g as i64; }
    return -1;
}

// Is r a nearly empty class (a vtable pointer and nothing else)?
fn nearly_empty(r: i64) -> bool { crecs[r].flags & CR_DYNAMIC != 0 && crecs[r].nvsize == 8 }

fn has_vbases(r: i64) -> bool { crecs[r].flags & CR_HAS_VBASE != 0 }

// clang's getIndirectPrimaryBases: the virtual primary bases of the bases
// with virtual bases, transitively.
recursive fn indirect_primaries(r: i64) {
    let cr = crecs[r];
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if !is_record(b.ty) { continue; }
        let br = rec_of(b.ty);
        if !has_vbases(br) { continue; }
        if crecs[br].flags & CR_PRIM_VIRTUAL != 0 && crecs[br].primary >= 0 { ipb.push(crecs[br].primary as! u32); }
        indirect_primaries(br);
    }
}

fn in_ipb(br: i64, from: i64) -> bool {
    for j in from..ipb.len { if ipb[j] as i64 == br { return true; } }
    return false;
}

// The primary virtual base of r (clang's SelectPrimaryVBase): the first
// nearly empty virtual base in inheritance graph order that is not an
// indirect primary base, else the first nearly empty one; -1 none.
fn primary_vbase(r: i64) -> i64 {
    if !has_vbases(r) { return -1; }
    let m = ipb.len;
    indirect_primaries(r);
    ne_first = -1;
    var p = select_pvb(r, m);
    if p < 0 { p = ne_first; }
    ipb.resize(m);
    return p;
}

recursive fn select_pvb(rd: i64, m: i64) -> i64 {
    let cr = crecs[rd];
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if !is_record(b.ty) { continue; }
        let br = rec_of(b.ty);
        if b.flags & BF_VIRTUAL != 0 && nearly_empty(br) {
            if !in_ipb(br, m) { return br; }
            if ne_first < 0 { ne_first = br; }
        }
        let x = select_pvb(br, m);
        if x >= 0 { return x; }
    }
    return -1;
}

// The virtual bases of r to lay out, in order (clang's LayoutVirtualBases).
recursive fn order_vbases(rd: i64, r: i64, ipm: i64) {
    let cr = crecs[rd];
    let pb = crecs[rd].primary as i64;
    let pbv = crecs[rd].flags & CR_PRIM_VIRTUAL != 0;
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if !is_record(b.ty) { continue; }
        let br = rec_of(b.ty);
        if b.flags & BF_VIRTUAL != 0 && (pb != br || !pbv) && !in_ipb(br, ipm) {
            var seen = false;
            for j in vb_scratch_mark..vbs.len { if rec_of(vbs[j]) == br { seen = true; } }
            if !seen { vbs.push(unqual(b.ty)); }
        }
        if has_vbases(br) { order_vbases(br, r, ipm); }
    }
}

// The offsets in r of the virtual bases that are primary bases of a base
// subobject (at offset off, of class c): they share its address (clang's
// AddPrimaryVirtualBaseOffsets, in layout order).
recursive fn claim_primary_vbases(r: i64, c: i64, off: i64) {
    if !has_vbases(c) && c != r { return; }
    if crecs[c].flags & CR_PRIM_VIRTUAL != 0 && crecs[c].primary >= 0 {
        let v = crecs[c].primary as i64;
        if vbase_offset_of(r, v) < 0 || (c == r) {
            vbase_off.insert(((r as u64) << 32) | (v as u64), off as u64);
        }
        claim_primary_vbases(r, v, off);
    }
    let cr = crecs[c];
    // the non-virtual bases, the primary first
    for pass in 2 {
        for i in cr.nbases {
            let b = cbases[cr.bases + i];
            if !is_record(b.ty) || b.flags & BF_VIRTUAL != 0 { continue; }
            let isp = b.flags & BF_PRIMARY != 0;
            if (pass == 0) != isp { continue; }
            claim_primary_vbases(r, rec_of(b.ty), off + b.offset);
        }
    }
    if c == r {
        // then the virtual bases laid out
        let m = vbs.len;
        vb_scratch_mark = m;
        collect_vbases(r);
        let e = vbs.len;
        for j in m..e {
            let br = rec_of(vbs[j]);
            let o = vbase_offset_of(r, br);
            if o >= 0 { claim_primary_vbases(r, br, o); }
        }
        vbs.resize(m);
    }
}
var vb_scratch_mark: i64 = 0;
var vbase_off = dictionary<u64, u64> {};    // (class << 32 | virtual base record) -> offset

// The virtual bases of r (transitively, each once), in vbs.
recursive fn collect_vbases(r: i64) {
    let cr = crecs[r];
    for i in cr.nbases {
        let b = cbases[cr.bases + i];
        if !is_record(b.ty) { continue; }
        collect_vbases(rec_of(b.ty));
        if b.flags & BF_VIRTUAL != 0 {
            var seen = false;
            for j in vb_scratch_mark..vbs.len { if vbs[j] == unqual(b.ty) { seen = true; } }
            if !seen { vbs.push(unqual(b.ty)); }
        }
    }
}

fn mark_unknown_layout(r: i64) {
    records[r].size = -1;
    records[r].flags = records[r].flags | RF_COMPLETE;
    types[records[r].ty].size = -1;
    crecs[r].flags = crecs[r].flags | CR_LAYOUT;
    crecs[r].dsize = 0;
    crecs[r].nvsize = 0;
}
