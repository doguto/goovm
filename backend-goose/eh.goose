// Unwind information: .eh_frame (a CIE per personality routine, an FDE per
// function, CFI exact at every instruction of the prologue and epilogue)
// and the LSDAs of functions with landing pads (.gcc_except_table, in the
// function's comdat group if it has one).
//
// Every function has the same frame shape (cg.goose): `push rbp; mov rbp,
// rsp`, pushes of the callee-saved registers it uses, then the body, which
// addresses its frame through rbp; the epilogue is the last code of the
// function. So the CFA is rbp + 16 from the fourth byte to the epilogue's
// `pop rbp`, whatever the body does to rsp (dynamic allocas,
// call areas, the red zone of leaf functions), and the CFI only describes
// the prologue's pushes, the epilogue's pops and, for invokes that pass
// arguments on the stack, the outgoing argument area (DW_CFA_GNU_args_size,
// so that the unwinder pops it when it lands in a landing pad).

let SHT_X86_64_UNWIND = 0x70000001;
let SHF_GROUP = 0x200;

var s_eh: u8[>..] = [];        // .eh_frame
var s_lsda: u8[>..] = [];      // the LSDAs, in chunks (OSec.xfirst lists a section's chunks)
struct Chunk { start: u32, len: u32, next: u32 }
var chunks: Chunk[>..] = [];
var cie_plain: u32 = 0xFFFFFFFF;   // offset of the CIE without personality in s_eh
struct PCie { pers: u32, off: u32 }
var cie_pers: PCie[>..] = [];
var f_eh: u32[>..] = [];       // per function: index into M.ehs, or GIR_NONE

// CFI events of the current function. Prologue events are relative to the
// prologue start, body events to the body start (cg.goose places the
// prologue before the body).
struct CfiEv { pos: u32, kind: u32, a: u32 }
let CE_PUSH = 1;     // register a was pushed: saved at the next CFA slot
let CE_ARGS = 2;     // DW_CFA_GNU_args_size a
let CE_POP = 3;      // register a was popped: DW_CFA_restore
let CE_DEFCFA = 4;   // rbp was restored: CFA = rsp + 8
var cfi_pro: CfiEv[>..] = [];
var cfi_body: CfiEv[>..] = [];
var pro_base: u32 = 0;         // code offset of the prologue being emitted

// Invoke call sites of the current function (body-relative): the call
// instruction and the landing pad block.
struct CallSite { start: u32, end: u32, lp: u32 }
var f_sites: CallSite[>..] = [];
var call_lp: u32 = 0xFFFFFFFF;  // landing pad block of the CALL being lowered (an invoke), else GIR_NONE

// The landing pad actions already in the current LSDA (per local block).
var lp_tag: u32[>..] = [];
var lp_act: u32[>..] = [];
var lp_epoch: u32 = 0;
var lsda_cs: u8[>..] = [];
var lsda_act: u8[>..] = [];

// DWARF register numbers (x86-64 psABI) of the registers the prologue saves.
checkfree fn dw_reg(r: u32) -> u32 {
    if r == RBX { return 3; }
    if r == RBP { return 6; }
    return r;   // r12..r15 = 12..15
}

checkfree fn uleb(o: u8[>..]&, x0: u64) {
    var x = x0;
    while x >= 0x80 {
        o.push(((x & 0x7F) | 0x80) as! u8);
        x = x >> 7;
    }
    o.push(x as! u8);
}
checkfree fn sleb(o: u8[>..]&, x0: i64) {
    var x = x0;
    while true {
        let b = (x & 0x7F) as! u8;
        x = x >> 7;
        if (x == 0 && b & 0x40 == 0) || (x == -1 && b & 0x40 != 0) {
            o.push(b);
            return;
        }
        o.push(b | 0x80);
    }
}
checkfree fn uleb_len(x0: u64) -> u32 {
    var x = x0;
    var n: u32 = 1;
    while x >= 0x80 {
        x = x >> 7;
        n++;
    }
    return n;
}
fn patch_o4(o: u8[>..]&, at: i64, x: u32) {
    let w = o[at..at + 4];
    w[0] = x as! u8;
    w[1] = (x >> 8) as! u8;
    w[2] = (x >> 16) as! u8;
    w[3] = (x >> 24) as! u8;
}

// A relocation in an extra section (section-relative offset).
fn xrel(sec: u32, off: u64, sym: u32, typ: u32, addend: i64) {
    xrels.push(Rel2 { offset: off, info: (sym as u64 << 32) | typ, addend: addend, sec: sec });
}

// ------------------------------------------------------------- .eh_frame

// Advances the CFI location to `to` (bytes from the function start).
fn cfa_advance(at: u32, to: u32) -> u32 {
    let d = to - at;
    if d == 0 { return to; }
    if d < 64 { o1(s_eh, 0x40 | d); }
    else if d < 256 {
        o1(s_eh, 0x02);
        o1(s_eh, d);
    } else if d < 65536 {
        o1(s_eh, 0x03);
        o2(s_eh, d);
    } else {
        o1(s_eh, 0x04);
        o4(s_eh, d);
    }
    return to;
}
// Pads an entry (CIE or FDE) starting at `at` to a multiple of 8 bytes and
// writes its length.
fn eh_close(at: i64) {
    while (s_eh.len - at) % 8 != 0 { s_eh.push(0); }   // DW_CFA_nop
    patch_o4(s_eh, at, (s_eh.len - at - 4) as! u32);
}
// The CIE for personality global `pers` (GIR_NONE: none), written on first use.
fn eh_cie(pers: u32) -> u32 {
    if pers == GIR_NONE && cie_plain != GIR_NONE { return cie_plain; }
    for c in cie_pers { if c.pers == pers { return c.off; } }
    let at: i64 = s_eh.len;
    o4(s_eh, 0);     // length
    o4(s_eh, 0);     // CIE id
    o1(s_eh, 1);     // version
    if pers == GIR_NONE { obytes(s_eh, "zR"); } else { obytes(s_eh, "zPLR"); }
    o1(s_eh, 0);
    o1(s_eh, 1);     // code alignment factor
    o1(s_eh, 0x78);  // data alignment factor -8
    o1(s_eh, 16);    // return address column
    if pers == GIR_NONE {
        o1(s_eh, 1);
        o1(s_eh, 0x1B);   // FDE pointers: pcrel sdata4
    } else {
        o1(s_eh, 7);
        o1(s_eh, 0x9B);   // personality: indirect pcrel sdata4
        xrel(sec_eh, s_eh.len as u64, g_sym[pers], r_pc32(), 0);
        o4(s_eh, 0);
        o1(s_eh, 0x1B);   // LSDA pointers
        o1(s_eh, 0x1B);   // FDE pointers
    }
    o1(s_eh, 0x0C);  // DW_CFA_def_cfa rsp, 8
    o1(s_eh, 7);
    o1(s_eh, 8);
    o1(s_eh, 0x90);  // DW_CFA_offset rip, cfa-8
    o1(s_eh, 1);
    eh_close(at);
    let off = at as! u32;
    if pers == GIR_NONE { cie_plain = off; } else { cie_pers.push(PCie { pers: pers, off: off }); }
    return off;
}

// The FDE of the function placed at mcode[start .. start + size] in code
// section sec, whose body starts at start + prolen. pers / lsda_sec /
// lsda_off: its personality and LSDA (pers = GIR_NONE: none).
fn eh_fde(start: u32, size: u32, sec: u32, prolen: u32, pers: u32, lsda_sec: u32, lsda_off: u32) {
    let cie = eh_cie(pers);
    let at: i64 = s_eh.len;
    o4(s_eh, 0);                               // length
    o4(s_eh, (at + 4) as! u32 - cie);          // CIE pointer
    xrel(sec_eh, (at + 8) as u64, sec_sym(sec), r_pc32(), (start - osecs[sec].start) as! i64);
    o4(s_eh, 0);                               // pc_begin
    o4(s_eh, size);                            // pc_range
    if pers == GIR_NONE { o1(s_eh, 0); }
    else {
        o1(s_eh, 4);
        xrel(sec_eh, s_eh.len as u64, sec_sym(lsda_sec), r_pc32(), lsda_off);
        o4(s_eh, 0);
    }
    // push rbp; mov rbp, rsp
    o1(s_eh, 0x41);   // advance 1
    o1(s_eh, 0x0E);   // DW_CFA_def_cfa_offset 16
    o1(s_eh, 16);
    o1(s_eh, 0x86);   // DW_CFA_offset rbp, cfa-16
    o1(s_eh, 2);
    o1(s_eh, 0x43);   // advance 3
    o1(s_eh, 0x0D);   // DW_CFA_def_cfa_register rbp
    o1(s_eh, 6);
    var loc: u32 = 4;
    var slot: u64 = 3;
    for e in cfi_pro {
        loc = cfa_advance(loc, e.pos);
        o1(s_eh, 0x80 | dw_reg(e.a));   // DW_CFA_offset r, cfa - 8 * slot
        uleb(s_eh, slot);
        slot++;
    }
    for e in cfi_body {
        loc = cfa_advance(loc, prolen + e.pos);
        if e.kind == CE_ARGS {
            o1(s_eh, 0x2E);   // DW_CFA_GNU_args_size
            uleb(s_eh, e.a);
        } else if e.kind == CE_POP {
            o1(s_eh, 0xC0 | dw_reg(e.a));   // DW_CFA_restore
        } else if e.kind == CE_DEFCFA {
            o1(s_eh, 0x0C);   // DW_CFA_def_cfa rsp, 8
            o1(s_eh, 7);
            o1(s_eh, 8);
            o1(s_eh, 0xC6);   // DW_CFA_restore rbp
        }
    }
    eh_close(at);
}

// ------------------------------------------------------------------ LSDA

// Appends bytes s_lsda[start..] (just written) to section sec's chunk list.
fn lsda_chunk(sec: u32, start: u32) {
    let k = chunks.len as! u32;
    chunks.push(Chunk { start: start, len: s_lsda.len as! u32 - start, next: GIR_NONE });
    if osecs[sec].xfirst == GIR_NONE { osecs[sec].xfirst = k; }
    else { chunks[osecs[sec].xlast].next = k; }
    osecs[sec].xlast = k;
    osecs[sec].size += chunks[k].len;
}

// The action record chain of landing pad block lp (1 + its offset in the
// action table; 0 = cleanup only).
fn lp_action(lp: u32) -> u32 {
    if lp_tag[lp] == lp_epoch { return lp_act[lp]; }
    let L = M.insts[M.blocks[f_first_block + lp].first_inst];
    var act: u32 = 0;
    if L.op == GIR_LANDINGPAD && L.b != 0 {
        act = lsda_act.len as! u32 + 1;
        for k in 0..L.b {
            let f = (M.opnds[L.a + k] as! i32) as i64;
            sleb(lsda_act, f);
            sleb(lsda_act, if k + 1 < L.b { 1 } else { 0 });  // the next record follows
        }
    }
    lp_tag[lp] = lp_epoch;
    lp_act[lp] = act;
    return act;
}
fn cs_entry(st: u32, len: u32, lp: u32, act: u32) {
    uleb(lsda_cs, st);
    uleb(lsda_cs, len);
    uleb(lsda_cs, lp);
    uleb(lsda_cs, act);
}

// Writes the LSDA of the function just placed (EH record e, prologue length
// prolen, size fsize) into except section sec; returns its offset there.
fn eh_lsda(e: u32, sec: u32, prolen: u32, fsize: u32) -> u32 {
    let E = M.ehs[e];
    lp_epoch++;
    if lp_tag.len < cur_nblocks { lp_tag.resize(cur_nblocks, 0); }
    if lp_act.len < cur_nblocks { lp_act.resize(cur_nblocks, 0); }
    lsda_cs.clear();
    lsda_act.clear();
    // Call sites: the invokes, and the gaps between them (calls there unwind
    // without a handler; an address outside the table would terminate).
    var prev: u32 = 0;
    for c in f_sites {
        let st = prolen + c.start;
        let en = prolen + c.end;
        let act = lp_action(c.lp);
        if st > prev { cs_entry(prev, st - prev, 0, 0); }
        cs_entry(st, en - st, prolen + block_off[c.lp], act);
        prev = en;
    }
    if fsize > prev { cs_entry(prev, fsize - prev, 0, 0); }
    // header
    let has_tt = E.n_ttypes != 0 || E.n_specs != 0;
    let off0: u32 = osecs[sec].size as! u32;
    let start = s_lsda.len as! u32;
    var pad0: u32 = 0;
    while (off0 + pad0) % 4 != 0 {
        s_lsda.push(0);
        pad0++;
    }
    let base = off0 + pad0;            // section offset of the LSDA
    let lbase: i64 = s_lsda.len;
    o1(s_lsda, 0xFF);                  // LPStart: the function start
    if !has_tt { o1(s_lsda, 0xFF); }
    else {
        o1(s_lsda, 0x9B);              // TType: indirect pcrel sdata4
        // distance from after this field to the end of the type table, with
        // the type table 4-aligned
        let rest: u64 = 1 + uleb_len(lsda_cs.len as u64) as u64 + lsda_cs.len as u64 + lsda_act.len as u64;
        var l: u32 = 1;
        var tt: u64 = 0;
        while true {
            let pos = 2 + l as u64 + rest;
            let fill = (4 - pos % 4) % 4;
            tt = rest + fill + 4 * E.n_ttypes as u64;
            if uleb_len(tt) == l { break; }
            l = uleb_len(tt);
        }
        uleb(s_lsda, tt);
    }
    o1(s_lsda, 0x01);                  // call sites: uleb128
    uleb(s_lsda, lsda_cs.len as u64);
    obytes(s_lsda, lsda_cs);
    obytes(s_lsda, lsda_act);
    if has_tt {
        while (s_lsda.len - lbase) % 4 != 0 { s_lsda.push(0); }
        var k = E.n_ttypes;
        while k > 0 {
            let g = M.opnds[E.ttypes + k - 1];
            if g != GIR_NONE {
                xrel(sec, (base + s_lsda.len - lbase) as! u64, g_sym[g], r_pc32(), 0);
            }
            o4(s_lsda, 0);
            k--;
        }
        if E.n_specs != 0 { obytes(s_lsda, M.data[E.specs..E.specs + E.n_specs]); }
    }
    lsda_chunk(sec, start);
    return base;
}

// --------------------------------------------------------- per function

fn eh_func_start() {
    cfi_pro.clear();
    cfi_body.clear();
    f_sites.clear();
    call_lp = GIR_NONE;
}
// The unwind information of function fi, just placed at mcode[start ..
// start + size] (prologue of prolen bytes) in code section sec.
fn eh_func_end(fi: u32, start: u32, size: u32, prolen: u32, sec: u32) {
    let e = f_eh[fi];
    if e == GIR_NONE || f_sites.len == 0 {
        if tgt_a64 { a_eh_fde(start, size, sec, prolen, GIR_NONE, 0, 0); }
        else { eh_fde(start, size, sec, prolen, GIR_NONE, 0, 0); }
        return;
    }
    let ls = cs_lsda[sec];
    let off = eh_lsda(e, ls, prolen, size);
    if tgt_a64 { a_eh_fde(start, size, sec, prolen, M.ehs[e].personality, ls, off); }
    else { eh_fde(start, size, sec, prolen, M.ehs[e].personality, ls, off); }
}

// ------------------------------------------------------------- AArch64 (F1)
//
// The frame (a64cg.goose): sub sp, sp, #F (or stp x29, x30, [sp, #-F]!),
// the frame record at the bottom of the frame ([sp] = x29, x30), mov x29,
// sp, then the callee-saved registers stored above the record; the body
// addresses the frame through x29 (CFA = x29 + F); the epilogue restores
// them, and the CFA goes back to sp before x29 is reloaded. The events are
// recorded as the code is emitted, prologue-relative or body-relative.
struct ACfi { pos: u32, kind: u32, reg: u32, off: i32 }
let AE_CFA_OFF = 1;     // DW_CFA_def_cfa_offset off
let AE_CFA = 2;         // DW_CFA_def_cfa reg, off
let AE_SAVE = 3;        // reg saved at CFA + off
let AE_RESTORE = 4;     // DW_CFA_restore reg
let AE_ARGS = 5;        // DW_CFA_GNU_args_size off
var a_cfi_pro: ACfi[>..] = [];
var a_cfi_body: ACfi[>..] = [];
var a_cie_plain: u32 = 0xFFFFFFFF;
var a_cie_pers: PCie[>..] = [];
// A body event (kind CE_ARGS from the call lowering: GNU_args_size a).
fn a_cfi_ev(pos: u32, kind: u32, a: u32, b: u32) {
    if kind == CE_ARGS { a_cfi_body.push(ACfi { pos: pos, kind: AE_ARGS, reg: 0, off: a as! i32 }); }
    else { a_cfi_body.push(ACfi { pos: pos, kind: kind, reg: a, off: b as! i32 }); }
}
// DWARF register number: x0..x30 0..30, sp 31, v0..v31 64..95.
checkfree fn a_dw_reg(r: u32) -> u32 { if r >= 32 { r + 32 } else { r } }
fn a_eh_cie(pers: u32) -> u32 {
    if pers == GIR_NONE && a_cie_plain != GIR_NONE { return a_cie_plain; }
    for c in a_cie_pers { if c.pers == pers { return c.off; } }
    let at: i64 = s_eh.len;
    o4(s_eh, 0);
    o4(s_eh, 0);
    o1(s_eh, 1);
    if pers == GIR_NONE { obytes(s_eh, "zR"); } else { obytes(s_eh, "zPLR"); }
    o1(s_eh, 0);
    o1(s_eh, 1);     // code alignment factor
    o1(s_eh, 0x78);  // data alignment factor -8
    o1(s_eh, 30);    // return address column: x30
    if pers == GIR_NONE {
        o1(s_eh, 1);
        o1(s_eh, 0x1B);
    } else {
        o1(s_eh, 7);
        o1(s_eh, 0x9B);
        xrel(sec_eh, s_eh.len as u64, g_sym[pers], r_pc32(), 0);
        o4(s_eh, 0);
        o1(s_eh, 0x1B);
        o1(s_eh, 0x1B);
    }
    o1(s_eh, 0x0C);  // DW_CFA_def_cfa sp, 0
    o1(s_eh, 31);
    o1(s_eh, 0);
    eh_close(at);
    let off = at as! u32;
    if pers == GIR_NONE { a_cie_plain = off; } else { a_cie_pers.push(PCie { pers: pers, off: off }); }
    return off;
}
fn a_cfi_one(e: ACfi) {
    if e.kind == AE_CFA_OFF {
        o1(s_eh, 0x0E);
        uleb(s_eh, e.off as! u64);
    } else if e.kind == AE_CFA {
        o1(s_eh, 0x0C);
        uleb(s_eh, a_dw_reg(e.reg));
        uleb(s_eh, e.off as! u64);
    } else if e.kind == AE_SAVE {
        let r = a_dw_reg(e.reg);
        let n: u64 = ((0 - e.off) / 8) as! u64;
        if r < 64 {
            o1(s_eh, 0x80 | r);
            uleb(s_eh, n);
        } else {
            o1(s_eh, 0x05);   // DW_CFA_offset_extended
            uleb(s_eh, r);
            uleb(s_eh, n);
        }
    } else if e.kind == AE_RESTORE {
        let r = a_dw_reg(e.reg);
        if r < 64 { o1(s_eh, 0xC0 | r); }
        else {
            o1(s_eh, 0x06);   // DW_CFA_restore_extended
            uleb(s_eh, r);
        }
    } else {
        o1(s_eh, 0x2E);       // DW_CFA_GNU_args_size
        uleb(s_eh, e.off as! u64);
    }
}
fn a_eh_fde(start: u32, size: u32, sec: u32, prolen: u32, pers: u32, lsda_sec: u32, lsda_off: u32) {
    let cie = a_eh_cie(pers);
    let at: i64 = s_eh.len;
    o4(s_eh, 0);
    o4(s_eh, (at + 4) as! u32 - cie);
    xrel(sec_eh, (at + 8) as u64, sec_sym(sec), r_pc32(), (start - osecs[sec].start) as! i64);
    o4(s_eh, 0);
    o4(s_eh, size);
    if pers == GIR_NONE { o1(s_eh, 0); }
    else {
        o1(s_eh, 4);
        xrel(sec_eh, s_eh.len as u64, sec_sym(lsda_sec), r_pc32(), lsda_off);
        o4(s_eh, 0);
    }
    var loc: u32 = 0;
    for e in a_cfi_pro {
        loc = cfa_advance(loc, e.pos);
        a_cfi_one(e);
    }
    for e in a_cfi_body {
        loc = cfa_advance(loc, prolen + e.pos);
        a_cfi_one(e);
    }
    eh_close(at);
}
