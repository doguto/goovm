// AArch64 machine code (milestone F1): the A64 instruction encoder, the
// relocations of code, branch fixups, immediates (logical, move-wide, FP),
// and loads and stores at any offset. Every instruction is a 32-bit word
// appended to `code` (x86.goose's buffer, shared by both targets, so that the
// placement, unwind and debug-line code works on either), and relocations
// go to `rela_code` at function-relative offsets as on x86-64.
//
// Register numbers: 0..30 x0..x30, 31 = sp or xzr (by instruction), 32..63
// v0..v31 in the allocator's numbering; the encoders take the 5-bit number
// (a V register as r & 31).

let AX0 = 0;
let AX1 = 1;
let AX2 = 2;
let AX3 = 3;
let AX4 = 4;
let AX5 = 5;
let AX6 = 6;
let AX7 = 7;
let AX8 = 8;
let AX9 = 9;
let AX10 = 10;
let AX11 = 11;
let AX16 = 16;   // IP0: the encoder's scratch (never allocated)
let AX17 = 17;   // IP1: the encoder's scratch (never allocated)
let AX18 = 18;   // the platform register: not used
let AX19 = 19;
let AFP = 29;    // frame pointer
let ALR = 30;    // link register
let ASP = 31;    // sp (or xzr, by instruction)
let AZR = 31;
let AV0 = 32;

// Condition codes.
let AC_EQ = 0;
let AC_NE = 1;
let AC_HS = 2;
let AC_LO = 3;
let AC_MI = 4;
let AC_PL = 5;
let AC_VS = 6;
let AC_VC = 7;
let AC_HI = 8;
let AC_LS = 9;
let AC_GE = 10;
let AC_LT = 11;
let AC_GT = 12;
let AC_LE = 13;
let AC_AL = 14;

// ELF relocation types (AArch64).
let R_AARCH64_ABS64 = 257;
let R_AARCH64_ABS32 = 258;
let R_AARCH64_PREL64 = 260;
let R_AARCH64_PREL32 = 261;
let R_AARCH64_ADR_PREL_LO21 = 274;
let R_AARCH64_ADR_PREL_PG_HI21 = 275;
let R_AARCH64_ADD_ABS_LO12_NC = 277;
let R_AARCH64_LDST8_ABS_LO12_NC = 278;
let R_AARCH64_JUMP26 = 282;
let R_AARCH64_CALL26 = 283;
let R_AARCH64_LDST16_ABS_LO12_NC = 284;
let R_AARCH64_LDST32_ABS_LO12_NC = 285;
let R_AARCH64_LDST64_ABS_LO12_NC = 286;
let R_AARCH64_LDST128_ABS_LO12_NC = 299;
let R_AARCH64_ADR_GOT_PAGE = 311;
let R_AARCH64_LD64_GOT_LO12_NC = 312;
let R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21 = 541;
let R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC = 542;
let R_AARCH64_TLSLE_ADD_TPREL_HI12 = 549;
let R_AARCH64_TLSLE_ADD_TPREL_LO12_NC = 551;
let R_AARCH64_TLSDESC_ADR_PAGE21 = 562;
let R_AARCH64_TLSDESC_LD64_LO12 = 563;
let R_AARCH64_TLSDESC_ADD_LO12 = 564;
let R_AARCH64_TLSDESC_CALL = 569;
let R_AARCH64_TLS_DTPREL64 = 1029;

// Branch fixups inside a function: the word at pos branches to local block
// blk (or, for AF_ADR, holds its address): its offset field is patched when
// the block is placed.
let AF_B26 = 0;     // b, bl
let AF_B19 = 1;     // b.cond, cbz, cbnz, ldr literal
let AF_B14 = 2;     // tbz, tbnz
let AF_ADR = 3;     // adr
struct AFix { pos: u32, blk: u32, kind: u32 }
var a_fix: AFix[>..] = [];

checkfree fn a4(w: u32) { b4(w); }
checkfree fn a_rela(sym: u32, typ: u32, addend: i64) {
    rela_code.push(Rela { offset: here(), info: (sym as u64 << 32) | typ, addend: addend, sec: 0 });
}
// The word at code[pos].
fn a_word(pos: u32) -> u32 {
    let p: i64 = pos;
    let w = code[p..p + 4];
    return w[0] as u32 | (w[1] as u32 << 8) | (w[2] as u32 << 16) | (w[3] as u32 << 24);
}
// Patches the offset field of the branch at pos to reach code offset `to`.
fn a_patch_branch(pos: u32, to: u32, kind: u32) {
    let d: i64 = (to as i64 - pos as i64) >> 2;
    var w = a_word(pos);
    if kind == AF_B26 {
        assert(d >= -(1 << 25) && d < (1 << 25));
        w = (w & 0xFC000000) | ((d as! u32) & 0x03FFFFFF);
    } else if kind == AF_B19 {
        assert(d >= -(1 << 18) && d < (1 << 18));
        w = (w & 0xFF00001F) | (((d as! u32) & 0x7FFFF) << 5);
    } else if kind == AF_B14 {
        assert(d >= -(1 << 13) && d < (1 << 13));
        w = (w & 0xFFF8001F) | (((d as! u32) & 0x3FFF) << 5);
    } else {
        let b: i64 = to as i64 - pos as i64;
        assert(b >= -(1 << 20) && b < (1 << 20));
        let u = (b as! u32) & 0x1FFFFF;
        w = (w & 0x9F00001F) | ((u & 3) << 29) | ((u >> 2) << 5);
    }
    patch4(pos, w);
}
// Whether a branch of `kind` at pos reaches `to`.
checkfree fn a_reaches(pos: u32, to: u32, kind: u32) -> bool {
    let d: i64 = (to as i64 - pos as i64) >> 2;
    if kind == AF_B26 { return d >= -(1 << 25) && d < (1 << 25); }
    if kind == AF_B19 { return d >= -(1 << 18) && d < (1 << 18); }
    if kind == AF_B14 { return d >= -(1 << 13) && d < (1 << 13); }
    return true;
}

// ------------------------------------------------------------ integer

checkfree fn sfb(w64: bool) -> u32 { if w64 { 0x80000000 } else { 0 } }

// add/sub/adds/subs (immediate, 0..4095, optionally << 12): op 0 add, 1 adds, 2 sub, 3 subs.
let AI_ADD = 0x11000000;
let AI_ADDS = 0x31000000;
let AI_SUB = 0x51000000;
let AI_SUBS = 0x71000000;
checkfree fn a_addsub_imm(base: u32, w64: bool, rd: u32, rn: u32, imm: u32, sh12: bool) {
    a4(base | sfb(w64) | (if sh12 { 0x400000 as u32 } else { 0 }) | ((imm & 0xFFF) << 10) | ((rn & 31) << 5) | (rd & 31));
}
// add/sub (shifted register): shift 0 lsl, 1 lsr, 2 asr.
let AR_ADD = 0x0B000000;
let AR_ADDS = 0x2B000000;
let AR_SUB = 0x4B000000;
let AR_SUBS = 0x6B000000;
checkfree fn a_addsub_rr(base: u32, w64: bool, rd: u32, rn: u32, rm: u32, sh: u32, amt: u32) {
    a4(base | sfb(w64) | (sh << 22) | ((rm & 31) << 16) | ((amt & 63) << 10) | ((rn & 31) << 5) | (rd & 31));
}
// add/sub (extended register): option 0 uxtb, 1 uxth, 2 uxtw, 3 uxtx, 4 sxtb, 5 sxth, 6 sxtw, 7 sxtx;
// rn/rd may be sp.
checkfree fn a_addsub_ext(base: u32, w64: bool, rd: u32, rn: u32, rm: u32, opt: u32, amt: u32) {
    a4(base | sfb(w64) | 0x00200000 | ((rm & 31) << 16) | (opt << 13) | (amt << 10) | ((rn & 31) << 5) | (rd & 31));
}
// add/adc/sbc
checkfree fn a_adc(w64: bool, rd: u32, rn: u32, rm: u32) { a4(0x1A000000 | sfb(w64) | ((rm & 31) << 16) | ((rn & 31) << 5) | (rd & 31)); }
checkfree fn a_adcs(w64: bool, rd: u32, rn: u32, rm: u32) { a4(0x3A000000 | sfb(w64) | ((rm & 31) << 16) | ((rn & 31) << 5) | (rd & 31)); }
checkfree fn a_sbc(w64: bool, rd: u32, rn: u32, rm: u32) { a4(0x5A000000 | sfb(w64) | ((rm & 31) << 16) | ((rn & 31) << 5) | (rd & 31)); }
checkfree fn a_sbcs(w64: bool, rd: u32, rn: u32, rm: u32) { a4(0x7A000000 | sfb(w64) | ((rm & 31) << 16) | ((rn & 31) << 5) | (rd & 31)); }

// Logical (shifted register).
let AL_AND = 0x0A000000;
let AL_BIC = 0x0A200000;
let AL_ORR = 0x2A000000;
let AL_ORN = 0x2A200000;
let AL_EOR = 0x4A000000;
let AL_EON = 0x4A200000;
let AL_ANDS = 0x6A000000;
checkfree fn a_logic_rr(base: u32, w64: bool, rd: u32, rn: u32, rm: u32, sh: u32, amt: u32) {
    a4(base | sfb(w64) | (sh << 22) | ((rm & 31) << 16) | ((amt & 63) << 10) | ((rn & 31) << 5) | (rd & 31));
}
// Logical (immediate): base AND 0x12000000, ORR 0x32000000, EOR 0x52000000, ANDS 0x72000000;
// enc = N:immr:imms (13 bits, from a_bitmask).
let ALI_AND = 0x12000000;
let ALI_ORR = 0x32000000;
let ALI_EOR = 0x52000000;
let ALI_ANDS = 0x72000000;
checkfree fn a_logic_imm(base: u32, w64: bool, rd: u32, rn: u32, enc: u32) {
    a4(base | sfb(w64) | (enc << 10) | ((rn & 31) << 5) | (rd & 31));
}
checkfree fn a_mov_rr(w64: bool, rd: u32, rm: u32) { a_logic_rr(AL_ORR, w64, rd, AZR, rm, 0, 0); }
// mov to/from sp (add rd, rn, #0)
checkfree fn a_mov_sp(rd: u32, rn: u32) { a_addsub_imm(AI_ADD, true, rd, rn, 0, false); }

// The N:immr:imms encoding of a logical immediate, or 0xFFFFFFFF.
fn a_bitmask(v0: u64, w64: bool) -> u32 {
    var v = v0;
    if !w64 {
        v = v & 0xFFFFFFFF;
        v = v | (v << 32);
    }
    if v == 0 || v == 0xFFFFFFFFFFFFFFFF { return 0xFFFFFFFF; }
    // the element size: the smallest power of two e such that v repeats every e bits
    var e: u32 = 64;
    while e > 2 {
        let h = e / 2;
        let mask: u64 = ((1 as u64) << h) - 1;
        if (v & mask) != ((v >> h) & mask) { break; }
        e = h;
    }
    let emask: u64 = if e == 64 { 0xFFFFFFFFFFFFFFFF } else { ((1 as u64) << e) - 1 };
    let x = v & emask;
    // x must be a rotation of a run of ones: rotate right until bit 0 is set and bit e-1 clear
    let ones: u32 = popcount(x) as! u32;
    var r: u32 = 0;
    var y = x;
    // find rotation r such that rotr(x, r) = (1 << ones) - 1
    let want: u64 = if ones == 64 { 0xFFFFFFFFFFFFFFFF } else { ((1 as u64) << ones) - 1 };
    while r < e {
        if y == want { break; }
        // rotate y right by one within e bits
        y = ((y >> 1) | ((y & 1) << (e - 1))) & emask;
        r++;
    }
    if r == e { return 0xFFFFFFFF; }
    // immr = rotation to the right that brings the run back: (e - r) % e
    let immr: u32 = (e - r) % e;
    var n: u32 = 0;
    var imms: u32 = 0;
    if e == 64 {
        n = 1;
        imms = ones - 1;
    } else {
        // high bits of imms encode the element size: e=32: 0b0xxxxx, 16: 0b10xxxx, 8: 0b110xxx, 4: 0b1110xx, 2: 0b11110x
        let msk: u32 = ~(2 * e - 1);
        let pre: u32 = msk & 0x3F;
        imms = pre | (ones - 1);
    }
    return (n << 12) | (immr << 6) | imms;
}

// Move wide: movz/movn/movk.
checkfree fn a_movz(w64: bool, rd: u32, imm16: u32, hw: u32) { a4(0x52800000 | sfb(w64) | (hw << 21) | ((imm16 & 0xFFFF) << 5) | (rd & 31)); }
checkfree fn a_movn(w64: bool, rd: u32, imm16: u32, hw: u32) { a4(0x12800000 | sfb(w64) | (hw << 21) | ((imm16 & 0xFFFF) << 5) | (rd & 31)); }
checkfree fn a_movk(w64: bool, rd: u32, imm16: u32, hw: u32) { a4(0x72800000 | sfb(w64) | (hw << 21) | ((imm16 & 0xFFFF) << 5) | (rd & 31)); }

// rd = v (64-bit, or the low 32 bits zero-extended when !w64).
fn a_mov_imm(rd: u32, v0: u64, w64: bool) {
    let v: u64 = if w64 { v0 } else { v0 & 0xFFFFFFFF };
    let nh: u32 = if w64 { 4 } else { 2 };
    // halfwords that are 0 / 0xFFFF
    var nz: u32 = 0;
    var nf: u32 = 0;
    for k in 0..nh {
        let h = (v >> (16 * k)) & 0xFFFF;
        if h == 0 { nz++; }
        if h == 0xFFFF { nf++; }
    }
    if nz >= nh - 1 || nz >= nf {
        if nz == nh {
            a_movz(w64, rd, 0, 0);
            return;
        }
        // a logical immediate is one instruction when movz would need more
        if nh - nz > 1 {
            let enc = a_bitmask(v, w64);
            if enc != 0xFFFFFFFF {
                a_logic_imm(ALI_ORR, w64, rd, AZR, enc);
                return;
            }
        }
        var first = true;
        for k in 0..nh {
            let h: u32 = ((v >> (16 * k)) & 0xFFFF) as! u32;
            if h == 0 { continue; }
            if first { a_movz(w64, rd, h, k); } else { a_movk(w64, rd, h, k); }
            first = false;
        }
        return;
    }
    if nf < nh - 1 {
        let enc = a_bitmask(v, w64);
        if enc != 0xFFFFFFFF {
            a_logic_imm(ALI_ORR, w64, rd, AZR, enc);
            return;
        }
    }
    var first = true;
    for k in 0..nh {
        let h: u32 = ((v >> (16 * k)) & 0xFFFF) as! u32;
        if h == 0xFFFF { continue; }
        if first { a_movn(w64, rd, (~h) & 0xFFFF, k); } else { a_movk(w64, rd, h, k); }
        first = false;
    }
    if first { a_movn(w64, rd, 0, 0); }
}

// Bitfield: sbfm/bfm/ubfm.
checkfree fn a_bfm(base: u32, w64: bool, rd: u32, rn: u32, immr: u32, imms: u32) {
    let n: u32 = if w64 { 0x80400000 } else { 0 };
    a4(base | n | ((immr & 63) << 16) | ((imms & 63) << 10) | ((rn & 31) << 5) | (rd & 31));
}
let ABF_SBFM = 0x13000000;
let ABF_BFM = 0x33000000;
let ABF_UBFM = 0x53000000;
checkfree fn a_lsl_imm(w64: bool, rd: u32, rn: u32, s: u32) {
    let w: u32 = if w64 { 64 } else { 32 };
    a_bfm(ABF_UBFM, w64, rd, rn, (w - s) % w, w - 1 - s);
}
checkfree fn a_lsr_imm(w64: bool, rd: u32, rn: u32, s: u32) { a_bfm(ABF_UBFM, w64, rd, rn, s, if w64 { 63 } else { 31 }); }
checkfree fn a_asr_imm(w64: bool, rd: u32, rn: u32, s: u32) { a_bfm(ABF_SBFM, w64, rd, rn, s, if w64 { 63 } else { 31 }); }
// ubfx/sbfx rd, rn, #lsb, #width
checkfree fn a_ubfx(w64: bool, rd: u32, rn: u32, lsb: u32, width: u32) { a_bfm(ABF_UBFM, w64, rd, rn, lsb, lsb + width - 1); }
checkfree fn a_sbfx(w64: bool, rd: u32, rn: u32, lsb: u32, width: u32) { a_bfm(ABF_SBFM, w64, rd, rn, lsb, lsb + width - 1); }
// bfi rd, rn, #lsb, #width
checkfree fn a_bfi(w64: bool, rd: u32, rn: u32, lsb: u32, width: u32) {
    let w: u32 = if w64 { 64 } else { 32 };
    a_bfm(ABF_BFM, w64, rd, rn, (w - lsb) % w, width - 1);
}
// extr / ror (immediate)
checkfree fn a_extr(w64: bool, rd: u32, rn: u32, rm: u32, lsb: u32) {
    let b: u32 = if w64 { 0x93C00000 } else { 0x13800000 };
    a4(b | ((rm & 31) << 16) | ((lsb & 63) << 10) | ((rn & 31) << 5) | (rd & 31));
}
// Data processing, 2 sources: udiv 2, sdiv 3, lslv 8, lsrv 9, asrv 10, rorv 11.
checkfree fn a_dp2(w64: bool, opc: u32, rd: u32, rn: u32, rm: u32) {
    a4(0x1AC00000 | sfb(w64) | ((rm & 31) << 16) | (opc << 10) | ((rn & 31) << 5) | (rd & 31));
}
let A2_UDIV = 2;
let A2_SDIV = 3;
let A2_LSL = 8;
let A2_LSR = 9;
let A2_ASR = 10;
let A2_ROR = 11;
// Data processing, 1 source: rbit 0, rev16 1, rev32/rev(w) 2, rev(x) 3, clz 4, cls 5.
checkfree fn a_dp1(w64: bool, opc: u32, rd: u32, rn: u32) { a4(0x5AC00000 | sfb(w64) | (opc << 10) | ((rn & 31) << 5) | (rd & 31)); }
// madd/msub; smaddl/umaddl, smulh/umulh.
checkfree fn a_madd(w64: bool, rd: u32, rn: u32, rm: u32, ra: u32) {
    a4(0x1B000000 | sfb(w64) | ((rm & 31) << 16) | ((ra & 31) << 10) | ((rn & 31) << 5) | (rd & 31));
}
checkfree fn a_msub(w64: bool, rd: u32, rn: u32, rm: u32, ra: u32) {
    a4(0x1B008000 | sfb(w64) | ((rm & 31) << 16) | ((ra & 31) << 10) | ((rn & 31) << 5) | (rd & 31));
}
checkfree fn a_mul(w64: bool, rd: u32, rn: u32, rm: u32) { a_madd(w64, rd, rn, rm, AZR); }
checkfree fn a_smull(rd: u32, rn: u32, rm: u32) { a4(0x9B200000 | ((rm & 31) << 16) | (31 << 10) | ((rn & 31) << 5) | (rd & 31)); }
checkfree fn a_umull(rd: u32, rn: u32, rm: u32) { a4(0x9BA00000 | ((rm & 31) << 16) | (31 << 10) | ((rn & 31) << 5) | (rd & 31)); }
checkfree fn a_smulh(rd: u32, rn: u32, rm: u32) { a4(0x9B400000 | ((rm & 31) << 16) | (31 << 10) | ((rn & 31) << 5) | (rd & 31)); }
checkfree fn a_umulh(rd: u32, rn: u32, rm: u32) { a4(0x9BC00000 | ((rm & 31) << 16) | (31 << 10) | ((rn & 31) << 5) | (rd & 31)); }
// Conditional select: csel 0, csinc 1, csinv 2, csneg 3.
checkfree fn a_csel_k(w64: bool, k: u32, rd: u32, rn: u32, rm: u32, cc: u32) {
    let b: u32 = if k == 0 { 0x1A800000 } else if k == 1 { 0x1A800400 } else if k == 2 { 0x5A800000 } else { 0x5A800400 };
    a4(b | sfb(w64) | ((rm & 31) << 16) | (cc << 12) | ((rn & 31) << 5) | (rd & 31));
}
checkfree fn a_csel(w64: bool, rd: u32, rn: u32, rm: u32, cc: u32) { a_csel_k(w64, 0, rd, rn, rm, cc); }
// cset rd, cc = csinc rd, zr, zr, !cc; csetm = csinv
checkfree fn a_cset(rd: u32, cc: u32) { a_csel_k(false, 1, rd, AZR, AZR, cc ^ 1); }
checkfree fn a_csetm(w64: bool, rd: u32, cc: u32) { a_csel_k(w64, 2, rd, AZR, AZR, cc ^ 1); }
// ccmp rn, rm, #nzcv, cc (and the immediate form, 0..31)
checkfree fn a_ccmp(w64: bool, rn: u32, rm: u32, nzcv: u32, cc: u32) {
    a4(0x7A400000 | sfb(w64) | ((rm & 31) << 16) | (cc << 12) | ((rn & 31) << 5) | nzcv);
}
checkfree fn a_ccmp_imm(w64: bool, rn: u32, imm: u32, nzcv: u32, cc: u32) {
    a4(0x7A400800 | sfb(w64) | ((imm & 31) << 16) | (cc << 12) | ((rn & 31) << 5) | nzcv);
}
// cmp/cmn/tst
checkfree fn a_cmp_rr(w64: bool, rn: u32, rm: u32) { a_addsub_rr(AR_SUBS, w64, AZR, rn, rm, 0, 0); }
checkfree fn a_tst_rr(w64: bool, rn: u32, rm: u32) { a_logic_rr(AL_ANDS, w64, AZR, rn, rm, 0, 0); }

// sxt/uxt helpers (rd = rn extended from `bits` = 8, 16, 32)
checkfree fn a_sxt(w64: bool, rd: u32, rn: u32, bits: u32) { a_bfm(ABF_SBFM, w64, rd, rn, 0, bits - 1); }
checkfree fn a_uxt(rd: u32, rn: u32, bits: u32) {
    if bits == 32 { a_mov_rr(false, rd, rn); } else { a_bfm(ABF_UBFM, false, rd, rn, 0, bits - 1); }
}

// ------------------------------------------------------------ branches

checkfree fn a_b_raw() { a4(0x14000000); }
checkfree fn a_bl_raw() { a4(0x94000000); }
checkfree fn a_bcond_raw(cc: u32) { a4(0x54000000 | cc); }
checkfree fn a_cbz_raw(w64: bool, nz: bool, rt: u32) { a4((if nz { 0x35000000 } else { 0x34000000 }) | sfb(w64) | (rt & 31)); }
checkfree fn a_tbz_raw(nz: bool, rt: u32, bitn: u32) {
    a4((if nz { 0x37000000 } else { 0x36000000 }) | ((bitn >> 5) << 31) | ((bitn & 31) << 19) | (rt & 31));
}
checkfree fn a_br(rn: u32) { a4(0xD61F0000 | ((rn & 31) << 5)); }
checkfree fn a_blr(rn: u32) { a4(0xD63F0000 | ((rn & 31) << 5)); }
checkfree fn a_ret() { a4(0xD65F03C0); }
checkfree fn a_nop() { a4(0xD503201F); }
checkfree fn a_brk(imm: u32) { a4(0xD4200000 | ((imm & 0xFFFF) << 5)); }
checkfree fn a_adr_raw(rd: u32) { a4(0x10000000 | (rd & 31)); }
checkfree fn a_adrp_raw(rd: u32) { a4(0x90000000 | (rd & 31)); }
checkfree fn a_dmb(opt: u32) { a4(0xD50330BF | (opt << 8)); }   // ish 11, ishld 9, ishst 10
checkfree fn a_mrs_tpidr(rt: u32) { a4(0xD53BD040 | (rt & 31)); }

// A branch to local block b (forward: fixed up when placed).
fn a_b_block(b: u32) {
    if b <= cur_blk {
        let d = (block_off[b] as i64 - here() as i64) >> 2;
        a4(0x14000000 | ((d as! u32) & 0x03FFFFFF));
        return;
    }
    a_fix.push(AFix { pos: here(), blk: b, kind: AF_B26 });
    a_b_raw();
}
// b.cond to block b; far: the function may be too large for b.cond's 1 MiB
// (a_far), then b.!cond over a b.
fn a_bcond_block(cc: u32, b: u32) {
    if a_far {
        a4(0x54000040 | (cc ^ 1));   // b.!cond +8
        a_b_block(b);
        return;
    }
    if b <= cur_blk {
        let d = (block_off[b] as i64 - here() as i64) >> 2;
        a4(0x54000000 | (((d as! u32) & 0x7FFFF) << 5) | cc);
        return;
    }
    a_fix.push(AFix { pos: here(), blk: b, kind: AF_B19 });
    a_bcond_raw(cc);
}
fn a_cbz_block(w64: bool, nz: bool, rt: u32, b: u32) {
    if a_far {
        a_cbz_raw(w64, !nz, rt);
        patch4(here() - 4, a_word(here() - 4) | (2 << 5));   // +8
        a_b_block(b);
        return;
    }
    if b <= cur_blk {
        let d = (block_off[b] as i64 - here() as i64) >> 2;
        a4((if nz { 0x35000000 } else { 0x34000000 }) | sfb(w64) | (((d as! u32) & 0x7FFFF) << 5) | (rt & 31));
        return;
    }
    a_fix.push(AFix { pos: here(), blk: b, kind: AF_B19 });
    a_cbz_raw(w64, nz, rt);
}
// A forward branch inside the code being emitted (patched by a_here).
fn a_fwd_b() -> u32 {
    let p = here();
    a_b_raw();
    return p;
}
fn a_fwd_bcond(cc: u32) -> u32 {
    if a_far {
        a4(0x54000040 | (cc ^ 1));
        return a_fwd_b();
    }
    let p = here();
    a_bcond_raw(cc);
    return p;
}
fn a_fwd_cbz(w64: bool, nz: bool, rt: u32) -> u32 {
    if a_far {
        a_cbz_raw(w64, !nz, rt);
        patch4(here() - 4, a_word(here() - 4) | (2 << 5));
        return a_fwd_b();
    }
    let p = here();
    a_cbz_raw(w64, nz, rt);
    return p;
}
// Patches the forward branch at p (b, b.cond, cbz) to the current position.
fn a_here(p: u32) {
    let w = a_word(p);
    let kind: u32 = if (w & 0xFC000000) == 0x14000000 { AF_B26 } else if (w & 0x7E000000) == 0x36000000 { AF_B14 } else { AF_B19 };
    a_patch_branch(p, here(), kind);
}
var a_far = false;      // conditional branches of this function use the b.!cond-over-b form

// ------------------------------------------------------------ loads / stores

// Access kinds: (size log2, signedness/fp) -> opcode bases.
// GPR: the unsigned-offset base for size s (0..3): store, load (zero-extending), load sign-extending to 64
let LS_STR = 0;
let LS_LDR = 1;     // zero-extending
let LS_LDRSX = 2;   // sign-extending to 64 bits
let LS_LDRSW = 3;   // sign-extending to 32 bits (w register)
// FP: LS_FSTR / LS_FLDR with size 0..4 (b h s d q)
let LS_FSTR = 4;
let LS_FLDR = 5;

// Base of the unsigned-offset form.
checkfree fn a_ls_base(k: u32, s: u32) -> u32 {
    if k < 4 {
        let opc: u32 = if k == LS_STR { 0 } else if k == LS_LDR { 1 } else if k == LS_LDRSX { 2 } else { 3 };
        return 0x39000000 | (s << 30) | (opc << 22);
    }
    let ld: u32 = if k == LS_FLDR { 1 } else { 0 };
    if s == 4 { return 0x3D800000 | (ld << 22); }
    return 0x3D000000 | (s << 30) | (ld << 22);
}
// [rn, #off] with an unsigned scaled offset (caller checked it fits).
checkfree fn a_ls_uimm(k: u32, s: u32, rt: u32, rn: u32, off: u32) {
    a4(a_ls_base(k, s) | ((off >> s) << 10) | ((rn & 31) << 5) | (rt & 31));
}
// [rn, #simm9] unscaled.
checkfree fn a_ls_simm9(k: u32, s: u32, rt: u32, rn: u32, off: i64) {
    let b = a_ls_base(k, s) & ~0x01000000;   // the unscaled form: bit 24 clear
    a4(b | (((off as! u32) & 0x1FF) << 12) | ((rn & 31) << 5) | (rt & 31));
}
// [rn, rm, lsl #s?] (sh: scale by the access size) or extended (opt: 3 lsl, 6 sxtw, 2 uxtw).
checkfree fn a_ls_reg(k: u32, s: u32, rt: u32, rn: u32, rm: u32, opt: u32, sh: bool) {
    let b = (a_ls_base(k, s) & ~0x01000000) | 0x00200800;
    a4(b | ((rm & 31) << 16) | (opt << 13) | (if sh { 0x1000 as u32 } else { 0 }) | ((rn & 31) << 5) | (rt & 31));
}
// A load or store at [rn + off] for any offset; uses x16 for offsets out of reach
// (rn must not be x16 then; rt may be x16 only for loads... callers keep it out).
fn a_ls(k: u32, s: u32, rt: u32, rn: u32, off: i64) {
    let sz: i64 = (1 as i64) << s;
    if off >= 0 && off % sz == 0 && off < 4096 * sz {
        a_ls_uimm(k, s, rt, rn, off as! u32);
        return;
    }
    if off >= -256 && off < 256 {
        a_ls_simm9(k, s, rt, rn, off);
        return;
    }
    // x16 = rn + (off & ~0xFFF) when the rest is a scaled offset
    let lo = off & 0xFFF;
    let hi = off - lo;
    if off > 0 && hi < (1 << 24) && lo % sz == 0 {
        a_addsub_imm(AI_ADD, true, AX16, rn, (hi >> 12) as! u32, true);
        a_ls_uimm(k, s, rt, AX16, lo as! u32);
        return;
    }
    a_mov_imm(AX16, off as! u64, true);
    a_ls_reg(k, s, rt, rn, AX16, 3, false);
}
// rd = rn + off (any offset; rd may be rn; rd, rn may be sp).
fn a_add_off(rd: u32, rn: u32, off: i64) {
    if off == 0 {
        if rd != rn { a_mov_sp(rd, rn); }
        return;
    }
    var o = off;
    var base: u32 = AI_ADD;
    if o < 0 {
        o = -o;
        base = AI_SUB;
    }
    if o < 4096 {
        a_addsub_imm(base, true, rd, rn, o as! u32, false);
        return;
    }
    if o < (1 << 24) {
        a_addsub_imm(base, true, rd, rn, (o >> 12) as! u32, true);
        if o & 0xFFF != 0 { a_addsub_imm(base, true, rd, rd, (o & 0xFFF) as! u32, false); }
        return;
    }
    // (rd != x16 here: callers form big offsets into a scratch register)
    a_mov_imm(AX16, off as! u64, true);
    a_addsub_ext(AR_ADD, true, rd, rn, AX16, 3, 0);
}
// stp/ldp of 64-bit GPRs (or d/q registers, fp = 1 d, 2 q) at [rn, #off] (signed offset form).
checkfree fn a_ldstp(ld: bool, fp: u32, r1: u32, r2: u32, rn: u32, off: i64) {
    var base: u32 = 0xA9000000;
    var sc: i64 = 8;
    if fp == 1 { base = 0x6D000000; }
    else if fp == 2 {
        base = 0xAD000000;
        sc = 16;
    }
    if ld { base |= 0x00400000; }
    let imm: u32 = ((off / sc) as! u32) & 0x7F;
    a4(base | (imm << 15) | ((r2 & 31) << 10) | ((rn & 31) << 5) | (r1 & 31));
}
// pre-index (stp x29, x30, [sp, #-n]!) and post-index (ldp ..., [sp], #n) forms of x registers
checkfree fn a_stp_pre(r1: u32, r2: u32, rn: u32, off: i64) {
    let imm: u32 = ((off / 8) as! u32) & 0x7F;
    a4(0xA9800000 | (imm << 15) | ((r2 & 31) << 10) | ((rn & 31) << 5) | (r1 & 31));
}
checkfree fn a_ldp_post(r1: u32, r2: u32, rn: u32, off: i64) {
    let imm: u32 = ((off / 8) as! u32) & 0x7F;
    a4(0xA8C00000 | (imm << 15) | ((r2 & 31) << 10) | ((rn & 31) << 5) | (r1 & 31));
}

// Exclusive and acquire/release accesses (size s 0..3).
checkfree fn a_ldaxr(s: u32, rt: u32, rn: u32) { a4(0x085FFC00 | (s << 30) | ((rn & 31) << 5) | (rt & 31)); }
checkfree fn a_ldxr(s: u32, rt: u32, rn: u32) { a4(0x085F7C00 | (s << 30) | ((rn & 31) << 5) | (rt & 31)); }
checkfree fn a_stlxr(s: u32, rs: u32, rt: u32, rn: u32) { a4(0x0800FC00 | (s << 30) | ((rs & 31) << 16) | ((rn & 31) << 5) | (rt & 31)); }
checkfree fn a_stxr(s: u32, rs: u32, rt: u32, rn: u32) { a4(0x08007C00 | (s << 30) | ((rs & 31) << 16) | ((rn & 31) << 5) | (rt & 31)); }
checkfree fn a_ldar(s: u32, rt: u32, rn: u32) { a4(0x08DFFC00 | (s << 30) | ((rn & 31) << 5) | (rt & 31)); }
checkfree fn a_stlr(s: u32, rt: u32, rn: u32) { a4(0x089FFC00 | (s << 30) | ((rn & 31) << 5) | (rt & 31)); }
checkfree fn a_ldaxp(rt: u32, rt2: u32, rn: u32) { a4(0xC87F8000 | ((rt2 & 31) << 10) | ((rn & 31) << 5) | (rt & 31)); }
checkfree fn a_ldxp(rt: u32, rt2: u32, rn: u32) { a4(0xC87F0000 | ((rt2 & 31) << 10) | ((rn & 31) << 5) | (rt & 31)); }
checkfree fn a_stlxp(rs: u32, rt: u32, rt2: u32, rn: u32) { a4(0xC8208000 | ((rs & 31) << 16) | ((rt2 & 31) << 10) | ((rn & 31) << 5) | (rt & 31)); }
checkfree fn a_stxp(rs: u32, rt: u32, rt2: u32, rn: u32) { a4(0xC8200000 | ((rs & 31) << 16) | ((rt2 & 31) << 10) | ((rn & 31) << 5) | (rt & 31)); }

// ------------------------------------------------------------ floating point

// ftype: 0 single, 1 double, 3 half.
checkfree fn a_ft(t: u32) -> u32 {
    if t == GIR_T_F64 { return 1; }
    if t == GIR_T_F16 { return 3; }
    return 0;
}
// fadd 2, fsub 3, fmul 0, fdiv 1, fmax 4, fmin 5, fmaxnm 6, fminnm 7, fnmul 8 (opcode field)
checkfree fn a_fp2(ft: u32, opc: u32, rd: u32, rn: u32, rm: u32) {
    a4(0x1E200800 | (ft << 22) | ((rm & 31) << 16) | (opc << 12) | ((rn & 31) << 5) | (rd & 31));
}
let AF2_FMUL = 0;
let AF2_FDIV = 1;
let AF2_FADD = 2;
let AF2_FSUB = 3;
let AF2_FMAX = 4;
let AF2_FMIN = 5;
let AF2_FMAXNM = 6;
let AF2_FMINNM = 7;
// 1 source: fmov 0, fabs 1, fneg 2, fsqrt 3, fcvt to s 4, to d 5, to h 7, frintn 8, frintp 9,
// frintm 10, frintz 11, frinta 12, frintx 14, frinti 15
checkfree fn a_fp1(ft: u32, opc: u32, rd: u32, rn: u32) {
    a4(0x1E204000 | (ft << 22) | (opc << 15) | ((rn & 31) << 5) | (rd & 31));
}
let AF1_FMOV = 0;
let AF1_FABS = 1;
let AF1_FNEG = 2;
let AF1_FSQRT = 3;
let AF1_CVT_S = 4;
let AF1_CVT_D = 5;
let AF1_CVT_H = 7;
let AF1_FRINTN = 8;
let AF1_FRINTP = 9;
let AF1_FRINTM = 10;
let AF1_FRINTZ = 11;
let AF1_FRINTA = 12;
let AF1_FRINTX = 14;
let AF1_FRINTI = 15;
checkfree fn a_fcmp(ft: u32, rn: u32, rm: u32) { a4(0x1E202000 | (ft << 22) | ((rm & 31) << 16) | ((rn & 31) << 5)); }
checkfree fn a_fcmp0(ft: u32, rn: u32) { a4(0x1E202008 | (ft << 22) | ((rn & 31) << 5)); }
checkfree fn a_fcsel(ft: u32, rd: u32, rn: u32, rm: u32, cc: u32) {
    a4(0x1E200C00 | (ft << 22) | ((rm & 31) << 16) | (cc << 12) | ((rn & 31) << 5) | (rd & 31));
}
// fmadd/fmsub/fnmadd/fnmsub: k 0..3
checkfree fn a_fma3(ft: u32, k: u32, rd: u32, rn: u32, rm: u32, ra: u32) {
    let b: u32 = if k == 0 { 0x1F000000 } else if k == 1 { 0x1F008000 } else if k == 2 { 0x1F200000 } else { 0x1F208000 };
    a4(b | (ft << 22) | ((rm & 31) << 16) | ((ra & 31) << 10) | ((rn & 31) << 5) | (rd & 31));
}
checkfree fn a_fmov_imm8(ft: u32, rd: u32, imm8: u32) { a4(0x1E201000 | (ft << 22) | (imm8 << 13) | (rd & 31)); }
// Conversions between general and FP registers: rmode:opcode.
// scvtf 0x02, ucvtf 0x03, fcvtzs 0x18, fcvtzu 0x19, fmov (fp->gpr) 0x06, (gpr->fp) 0x07,
// fcvtns 0x00, fcvtnu 0x01, fcvtas 0x04, fcvtau 0x05, fcvtps 0x08, fcvtms 0x10
checkfree fn a_fcvt_gp(w64: bool, ft: u32, op: u32, rd: u32, rn: u32) {
    a4(0x1E200000 | sfb(w64) | (ft << 22) | (op << 16) | ((rn & 31) << 5) | (rd & 31));
}
let AFC_SCVTF = 0x02;
let AFC_UCVTF = 0x03;
let AFC_FCVTZS = 0x18;
let AFC_FCVTZU = 0x19;
let AFC_FMOV_TO_GP = 0x06;
let AFC_FMOV_FROM_GP = 0x07;
let AFC_FCVTAS = 0x04;
let AFC_FCVTAU = 0x05;
let AFC_FCVTNS = 0x00;
let AFC_FCVTMS = 0x10;
let AFC_FCVTPS = 0x08;
// fmov x, d / d, x / w, s / s, w
checkfree fn a_fmov_to_gp(w64: bool, rd: u32, vn: u32) { a_fcvt_gp(w64, if w64 { 1 } else { 0 }, AFC_FMOV_TO_GP, rd, vn); }
checkfree fn a_fmov_from_gp(w64: bool, vd: u32, rn: u32) { a_fcvt_gp(w64, if w64 { 1 } else { 0 }, AFC_FMOV_FROM_GP, vd, rn); }
// fmov x, v.d[1] / v.d[1], x
checkfree fn a_fmov_hi_to_gp(rd: u32, vn: u32) { a4(0x9EAE0000 | ((vn & 31) << 5) | (rd & 31)); }
checkfree fn a_fmov_hi_from_gp(vd: u32, rn: u32) { a4(0x9EAF0000 | ((rn & 31) << 5) | (vd & 31)); }

// The fmov 8-bit immediate of an f32/f64 bit pattern, or 0xFFFFFFFF.
fn a_fp_imm8(bits: u64, dbl: bool) -> u32 {
    if dbl {
        // a:NOT(b):bbbbbbbb:cd:efgh:0{48}
        if bits & 0x0000FFFFFFFFFFFF != 0 { return 0xFFFFFFFF; }
        let e9 = (bits >> 54) & 0x1FF;
        if e9 != 0x100 && e9 != 0x0FF { return 0xFFFFFFFF; }
        let a: u32 = ((bits >> 63) & 1) as! u32;
        let b: u32 = ((bits >> 61) & 1) as! u32;
        let cdefgh: u32 = ((bits >> 48) & 0x3F) as! u32;
        return (a << 7) | (b << 6) | cdefgh;
    }
    // a:NOT(b):bbbbb:cd:efgh:0{19}
    let x: u32 = bits as! u32;
    if x & 0x7FFFF != 0 { return 0xFFFFFFFF; }
    let e6 = (x >> 25) & 0x3F;
    if e6 != 0x20 && e6 != 0x1F { return 0xFFFFFFFF; }
    let a = (x >> 31) & 1;
    let b = (x >> 29) & 1;
    return (a << 7) | (b << 6) | ((x >> 19) & 0x3F);
}

// ------------------------------------------------------------ SIMD

// mov vd.16b, vn.16b (orr); q: 16 bytes, else 8
checkfree fn a_vmov(q: bool, vd: u32, vn: u32) {
    a4((if q { 0x4EA01C00 } else { 0x0EA01C00 }) | ((vn & 31) << 16) | ((vn & 31) << 5) | (vd & 31));
}
// movi vd.2d, #0 (q) / movi dd, #0
checkfree fn a_vzero(q: bool, vd: u32) { a4((if q { 0x6F00E400 } else { 0x2F00E400 }) | (vd & 31)); }
// Three registers, same type: 0 Q U 01110 size 1 Rm opcode 1 Rn Rd
checkfree fn a_v3(q: bool, u: u32, size: u32, opc: u32, vd: u32, vn: u32, vm: u32) {
    a4(0x0E200400 | (if q { 0x40000000 as u32 } else { 0 }) | (u << 29) | (size << 22) | ((vm & 31) << 16) | (opc << 11)
       | ((vn & 31) << 5) | (vd & 31));
}
// Two-register miscellaneous: 0 Q U 01110 size 10000 opcode 10 Rn Rd
checkfree fn a_v2(q: bool, u: u32, size: u32, opc: u32, vd: u32, vn: u32) {
    a4(0x0E200800 | (if q { 0x40000000 as u32 } else { 0 }) | (u << 29) | (size << 22) | (opc << 12) | ((vn & 31) << 5) | (vd & 31));
}
// Shift by immediate: 0 Q U 011110 immh:immb opcode 1 Rn Rd (immhb = immh:immb, 7 bits)
checkfree fn a_vsh(q: bool, u: u32, immhb: u32, opc: u32, vd: u32, vn: u32) {
    a4(0x0F000400 | (if q { 0x40000000 as u32 } else { 0 }) | (u << 29) | (immhb << 16) | (opc << 11) | ((vn & 31) << 5) | (vd & 31));
}
// Copy: dup (element) 0, dup (general) 1, smov 5, umov 7, ins (general) 3 (with imm5)
checkfree fn a_vcopy(q: bool, imm4: u32, imm5: u32, vd: u32, rn: u32) {
    a4(0x0E000400 | (if q { 0x40000000 as u32 } else { 0 }) | (imm5 << 16) | (imm4 << 11) | ((rn & 31) << 5) | (vd & 31));
}
// ins vd.T[i], vn.T[j] (element)
checkfree fn a_vins_elt(imm5: u32, imm4: u32, vd: u32, vn: u32) {
    a4(0x6E000400 | (imm5 << 16) | (imm4 << 11) | ((vn & 31) << 5) | (vd & 31));
}
// imm5 for lane `idx` of size log2 s
checkfree fn a_imm5(s: u32, idx: u32) -> u32 { ((idx << 1) | 1) << s }
// umov w/x, vn.T[idx]
checkfree fn a_umov(s: u32, rd: u32, vn: u32, idx: u32) { a_vcopy(s == 3, 7, a_imm5(s, idx), rd, vn); }
// smov w/x (x if w64), vn.T[idx]
checkfree fn a_smov(w64: bool, s: u32, rd: u32, vn: u32, idx: u32) { a_vcopy(w64, 5, a_imm5(s, idx), rd, vn); }
// ins vd.T[idx], w/x
checkfree fn a_ins_gp(s: u32, vd: u32, rn: u32, idx: u32) { a_vcopy(true, 3, a_imm5(s, idx), vd, rn); }
// dup vd.T, w/x
checkfree fn a_dup_gp(q: bool, s: u32, vd: u32, rn: u32) { a_vcopy(q, 1, a_imm5(s, 0), vd, rn); }
// dup vd.T, vn.T[idx]
checkfree fn a_dup_elt(q: bool, s: u32, vd: u32, vn: u32, idx: u32) { a_vcopy(q, 0, a_imm5(s, idx), vd, vn); }
// tbl vd.(8|16)b, {vn.16b}, vm (len 1)
checkfree fn a_tbl1(q: bool, vd: u32, vn: u32, vm: u32) {
    a4(0x0E000000 | (if q { 0x40000000 as u32 } else { 0 }) | ((vm & 31) << 16) | ((vn & 31) << 5) | (vd & 31));
}
// tbl vd, {vn, vn+1}, vm (two table registers)
checkfree fn a_tbl2(q: bool, vd: u32, vn: u32, vm: u32) {
    a4(0x0E002000 | (if q { 0x40000000 as u32 } else { 0 }) | ((vm & 31) << 16) | ((vn & 31) << 5) | (vd & 31));
}
// across lanes: addv 0x31B, (u) maxv 0x0A, minv 0x1A...: 0 Q U 01110 size 11000 opcode 10 Rn Rd
checkfree fn a_vacross(q: bool, u: u32, size: u32, opc: u32, vd: u32, vn: u32) {
    a4(0x0E300800 | (if q { 0x40000000 as u32 } else { 0 }) | (u << 29) | (size << 22) | (opc << 12) | ((vn & 31) << 5) | (vd & 31));
}
// ld1 {vt.16b}, [xn] / st1
checkfree fn a_ld1(q: bool, vt: u32, rn: u32) { a4((if q { 0x4C407000 } else { 0x0C407000 }) | ((rn & 31) << 5) | (vt & 31)); }
checkfree fn a_st1(q: bool, vt: u32, rn: u32) { a4((if q { 0x4C007000 } else { 0x0C007000 }) | ((rn & 31) << 5) | (vt & 31)); }
