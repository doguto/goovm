// AArch64 register allocation and value locations (milestone F1). The
// policy is the x86-64 back-end's (ra.goose, DESIGN.md §4): a local value
// lives in a register from its definition to its last use; a global value is
// written to its home when defined and a register copy is a cache for the
// rest of its block; PHIs live in their homes; every block starts with all
// registers free. The per-value records (vi), the pre-pass's facts and the
// frame-slot bookkeeping are shared with ra.goose; the register file here has
// 64 registers (0..30 x0..x30, 32..63 v0..v31) and u64 masks.
//
// Registers: x0..x15 caller-saved, x19..x28 callee-saved; x16/x17 are the
// encoder's scratch, x18 is not used, x29 is the frame pointer, x30 the link
// register. v0..v7 and v16..v30 caller-saved, v8..v15 callee-saved (their
// low 64 bits: an f128 or a 16-byte vector does not live across a call in
// them); v31 is the lowerings' FP scratch.
//
// Frame: x29 points at the frame record at the bottom of the fixed frame
// (a64cg.goose), so homes, spill slots and allocas are at positive offsets
// from x29 (vi[].off, as the x86 back-end's rbp offsets are negative).

let A_GP_CALLER: u64 = 0xFFFF;                 // x0..x15
let A_GP_CALLEE: u64 = 0x1FF80000;             // x19..x28
let A_GP_ALL: u64 = 0x1FF8FFFF;
let A_V_CALLER: u64 = 0x7FFF00FF00000000;      // v0..v7, v16..v30
let A_V_CALLEE: u64 = 0x0000FF0000000000;      // v8..v15
let A_V_ALL: u64 = 0x7FFFFFFF00000000;         // v0..v30
let A_CS_GP: u32[10] = [19, 20, 21, 22, 23, 24, 25, 26, 27, 28];
let A_CS_V: u32[8] = [40, 41, 42, 43, 44, 45, 46, 47];
let AV31 = 63;     // FP scratch (encoder number 31)

// Register classes of types (a_trc).
let ARC_MEM: u8 = 0;
let ARC_GPR: u8 = 1;   // INT (i1..i64, ptr)
let ARC_FPR: u8 = 2;   // f16, f32, f64: the low bits of a V register
let ARC_VR: u8 = 3;    // vectors of 8 or 16 bytes (i8/i16/i32/i64/f32/f64 lanes), f128: a V register

var a_rval: u32[64] = [0xFFFFFFFF; 64];
var a_free: u64 = 0;
var a_lock: u64 = 0;
var a_tmp: u64 = 0;
var a_alloc: u64 = 0;
var a_csused: u64 = 0;
var a_trc: u8[>..] = [];

checkfree fn abit(r: u32) -> u64 { (1 as u64) << (r & 63) }
inline fn actz(m: u64) -> u32 { ctz(m) as! u32 }

fn a_build_trc() {
    a_trc.clear();
    for T in M.types {
        var rc: u8 = ARC_MEM;
        if T.cls == C_INT { rc = ARC_GPR; }
        else if T.cls == C_FP {
            rc = if T.bits == 128 { ARC_VR } else { ARC_FPR };
        } else if T.cls == C_VEC && T.n >= 2 && (T.store == 16 || T.store == 8) {
            let L = M.types[T.elems];
            if L.cls == C_INT && (L.bits == 8 || L.bits == 16 || L.bits == 32 || L.bits == 64) && L.size * T.n == T.store
               || L.cls == C_FP && (L.bits == 32 || L.bits == 64) && L.size * T.n == T.store {
                rc = ARC_VR;
            }
        }
        a_trc.push(rc);
    }
}
inline fn arc(t: u32) -> u8 { a_trc[t] }
inline fn a_inv(c: u8) -> bool { c >= ARC_FPR }

// Bytes a value of type t occupies in a register-class home (1, 2, 4, 8, 16).
fn a_vbytes(t: u32) -> u32 {
    let c = arc(t);
    if c == ARC_GPR { return int_bytes(bits_of(t)); }
    return M.types[t].store;
}
// log2 of the access size
checkfree fn a_log2(n: u32) -> u32 {
    if n <= 1 { return 0; }
    if n <= 2 { return 1; }
    if n <= 4 { return 2; }
    if n <= 8 { return 3; }
    return 4;
}

// ------------------------------------------------------------ homes

var a_lay: i64 = 0;         // bytes above x29 in use so far (the fixed frame)
var a_frame: i64 = 0;       // the final frame size (a64cg)

fn a_new_slot(sz: i64) -> i32 {
    if sz >= 16 { a_lay = (a_lay + 15) & ~15; } else { a_lay = (a_lay + 7) & ~7; }
    let off = a_lay;
    a_lay += if sz < 8 { 8 } else { (sz + 7) & ~7 };
    return off as! i32;
}
// Slot size of a value of type t in a home: INT and FP 8, f128 / INT2 16, else the size rounded to 8.
fn a_slot_size(t: u32) -> i64 {
    let c = cls_of(t);
    if c == C_INT { return 8; }
    if c == C_FP { return if bits_of(t) == 128 { 16 } else { 8 }; }
    if c == C_INT2 { return 16; }
    let s: i64 = size_of(t);
    if s == 0 { return 8; }
    return (s + 7) & ~7;
}
fn a_home_off(id: u32) -> i32 {
    let o = vi[id].off;
    if o != 0 { return o; }
    let sz = a_slot_size(vtype(id));
    var n: i32 = 0;
    if f_share && vi[id].st & (ST_GLOB | ST_PHI) == 0 {
        if sz == 8 && n_free8 != 0 {
            n_free8--;
            n = free8[n_free8];
        } else if sz == 16 && n_free16 != 0 {
            n_free16--;
            n = free16[n_free16];
        }
    }
    if n == 0 { n = a_new_slot(sz); }
    vi[id].off = n;
    vi[id].home = H_SLOT;
    return n;
}
fn a_free_slot(id: u32) {
    let o = vi[id].off;
    let sz = a_slot_size(vtype(id));
    if sz == 8 {
        if n_free8 < free8.len { free8[n_free8] = o; } else { free8.push(o); }
        n_free8++;
    } else if sz == 16 {
        if n_free16 < free16.len { free16[n_free16] = o; } else { free16.push(o); }
        n_free16++;
    }
    vi[id].off = 0;
}

// Loads/stores of a register-class value of type t between register r and [base + off].
fn a_load_t(r: u32, base: u32, off: i64, t: u32) {
    if r >= 32 {
        a_ls(LS_FLDR, a_log2(M.types[t].store), r, base, off);
    } else {
        a_ls(LS_LDR, a_log2(int_bytes(bits_of(t))), r, base, off);
    }
}
fn a_store_t(r: u32, base: u32, off: i64, t: u32) {
    if r >= 32 {
        a_ls(LS_FSTR, a_log2(M.types[t].store), r, base, off);
    } else {
        a_ls(LS_STR, a_log2(int_bytes(bits_of(t))), r, base, off);
    }
}
fn a_store_home(id: u32, r: u32) {
    let off = a_home_off(id);
    a_store_t(r, AFP, off, vtype(id));
    vi[id].st |= ST_MEM;
}

// ------------------------------------------------------------ allocation

fn a_live_after(id: u32) -> bool { vi[id].st & ST_GLOB != 0 || vi[id].last > cur_pos }
inline fn a_note(id: u32) {
    if vi[id].st & ST_GLOB == 0 && vi[id].last == cur_pos { dying.push(id); }
}
fn a_pref_gp(id: u32) -> u64 {
    if vi[id].st & (ST_CS | ST_GLOB) == ST_CS { return A_GP_CALLEE; }
    return A_GP_CALLER;
}
fn a_pref_v(id: u32) -> u64 {
    // f128 and 16-byte vectors do not survive a call in v8..v15
    if vi[id].st & (ST_CS | ST_GLOB) == ST_CS && M.types[vtype(id)].store <= 8 { return A_V_CALLEE; }
    return A_V_CALLER;
}
inline fn a_release(r: u32) {
    a_rval[r] = RV_NONE;
    a_free |= abit(r);
}
fn a_alloc_r(xm: u64, pref: u64) -> u32 {
    let avail = a_free & ~a_lock & xm & a_alloc;
    var c = avail & pref;
    if c == 0 { c = avail; }
    var r: u32 = 0;
    if c != 0 { r = actz(c); } else { r = a_evict(xm); }
    a_free &= ~abit(r);
    a_lock |= abit(r);
    if abit(r) & (A_GP_CALLEE | A_V_CALLEE) != 0 { a_csused |= abit(r); }
    return r;
}
fn a_evict(xm: u64) -> u32 {
    var m = ~a_free & ~a_lock & xm & a_alloc;
    if m == 0 {
        write_stderr(str("goovm: aarch64: no register to evict: function ", f_index, " instruction ", cur_pos, " op ",
                         M.insts[f_first_inst + cur_pos].op, "\n"));
        assert(false);
    }
    var best: u32 = 64;
    var best_last: u32 = 0;
    while m != 0 {
        let r = actz(m);
        m &= m - 1;
        let id = a_rval[r];
        if id >= RV_TEMP { continue; }
        if vi[id].st & ST_MEM != 0 {
            best = r;
            break;
        }
        let l = vi[id].last;
        if best == 64 || l > best_last {
            best = r;
            best_last = l;
        }
    }
    if best == 64 { assert(false); }
    let id = a_rval[best];
    if vi[id].st & ST_MEM == 0 { a_store_home(id, best); }
    vi[id].reg = NOREG;
    a_rval[best] = RV_NONE;
    return best;
}
// Scratch registers of the current instruction.
fn a_temp() -> u32 {
    let r = a_alloc_r(A_GP_ALL, A_GP_CALLER);
    a_rval[r] = RV_TEMP;
    a_tmp |= abit(r);
    return r;
}
fn a_vtemp() -> u32 {
    let r = a_alloc_r(A_V_ALL, A_V_CALLER);
    a_rval[r] = RV_TEMP;
    a_tmp |= abit(r);
    return r;
}
// Value id leaves register `from`: to a free register of its class, or its home.
fn a_evacuate(id: u32, from: u32) {
    let xm: u64 = if from >= 32 { A_V_ALL } else { A_GP_ALL };
    let avail = a_free & ~a_lock & xm & a_alloc & ~abit(from);
    if avail != 0 {
        var c = avail & (if from >= 32 { a_pref_v(id) } else { a_pref_gp(id) });
        if c == 0 { c = avail; }
        let to = actz(c);
        if from >= 32 { a_vmov(true, to, from); } else { a_mov_rr(true, to, from); }
        a_free &= ~abit(to);
        if abit(to) & (A_GP_CALLEE | A_V_CALLEE) != 0 { a_csused |= abit(to); }
        a_rval[to] = id;
        vi[id].reg = to as! u8;
        if a_lock & abit(from) != 0 { a_lock |= abit(to); }
    } else {
        if vi[id].st & ST_MEM == 0 { a_store_home(id, from); }
        vi[id].reg = NOREG;
    }
    a_rval[from] = RV_NONE;
    a_free |= abit(from);
}
// The current instruction overwrites register r: its value moves away and r
// becomes a scratch register of the instruction.
fn a_clobber(r: u32) {
    let occ = a_rval[r];
    if occ < RV_TEMP { a_evacuate(occ, r); }
    a_free &= ~abit(r);
    a_rval[r] = RV_TEMP;
    a_tmp |= abit(r);
    a_lock |= abit(r);
}
// Spills every register in mask whose value is not in its home and forgets
// the register copies.
fn a_flush(mask: u64) {
    var m = ~a_free & a_alloc & mask;
    while m != 0 {
        let r = actz(m);
        m &= m - 1;
        let id = a_rval[r];
        if id >= RV_TEMP { continue; }
        if vi[id].st & ST_MEM == 0 { a_store_home(id, r); }
        vi[id].reg = NOREG;
        a_release(r);
    }
}

// ------------------------------------------------------------ normalization

// r = r zero-extended from `bits` (a w-register operation clears bits 32..63).
fn a_zext(r: u32, bits: u32) {
    if bits >= 64 { return; }
    if bits == 32 { a_mov_rr(false, r, r); return; }
    if bits == 8 || bits == 16 { a_uxt(r, r, bits); return; }
    if bits < 32 { a_bfm(ABF_UBFM, false, r, r, 0, bits - 1); return; }
    a_bfm(ABF_UBFM, true, r, r, 0, bits - 1);
}
fn a_sext(rd: u32, rn: u32, bits: u32) {
    if bits >= 64 {
        if rd != rn { a_mov_rr(true, rd, rn); }
        return;
    }
    a_bfm(ABF_SBFM, true, rd, rn, 0, bits - 1);
}
fn a_norm(id: u32, r: u32) {
    a_zext(r, bits_of(vtype(id)));
    vi[id].st &= ~ST_EXT;
}

// ------------------------------------------------------------ constants and globals

// Pool entry of constant ci (FP, f128, INT2, VEC, MEM classes): the symbol and addend
// to reach it with adrp + :lo12:.
fn a_const_ref(ci: u32) -> u32, i64 {
    let c = M.consts[ci];
    let t = c.ty;
    let size = size_of(t);
    var sec: u32 = SEC_RODATA;
    if size == 4 && c.data == GIR_NONE && cls_of(t) == C_FP { sec = SEC_CST4; }
    else if size == 8 && cls_of(t) != C_MEM && cls_of(t) != C_VEC { sec = SEC_CST8; }
    else if size == 8 && cls_of(t) == C_VEC { sec = SEC_CST8; }
    else if size == 16 && cls_of(t) != C_MEM { sec = SEC_CST16; }
    else if size <= 2 && cls_of(t) == C_FP { sec = SEC_CST4; }
    var ref = c_pool[ci];
    if ref == GIR_NONE {
        if sec == SEC_CST4 {
            ref = new_pool_sym(sec, cst4.len as! u32, 4);
            o4(cst4, c.lo as! u32);
        } else if sec == SEC_CST8 {
            ref = new_pool_sym(sec, cst8.len as! u32, 8);
            if c.data != GIR_NONE { cst8.append(M.data[c.data..c.data + 8]); }
            else { o8(cst8, c.lo); }
        } else if sec == SEC_CST16 {
            ref = new_pool_sym(sec, cst16.len as! u32, 16);
            if c.data != GIR_NONE { cst16.append(M.data[c.data..c.data + 16]); }
            else {
                o8(cst16, c.lo);
                o8(cst16, c.hi);
            }
        } else {
            let al: u32 = if M.types[t].align > 16 { M.types[t].align } else { 16 };
            while (srodata.len as u64) % al != 0 { srodata.push(0); }
            if al > rodata_align { rodata_align = al; }
            ref = srodata.len as! u32;
            if c.data != GIR_NONE { srodata.append(M.data[c.data..c.data + size]); }
            else { srodata.resize(srodata.len + size, 0); }
        }
        c_pool[ci] = ref;
    }
    if sec == SEC_RODATA { return sec_sym(sec), ref as i64; }
    return ref, 0;
}
// r = the address of symbol + addend (adrp + add :lo12:).
fn a_adr_sym(r: u32, sym: u32, addend: i64) {
    a_rela(sym, R_AARCH64_ADR_PREL_PG_HI21, addend);
    a_adrp_raw(r);
    a_rela(sym, R_AARCH64_ADD_ABS_LO12_NC, addend);
    a_addsub_imm(AI_ADD, true, r, r, 0, false);
}
// A load (kind k, size log2 s) from symbol + addend into rt, through rt (GPR loads) or x16.
fn a_ld_sym(k: u32, s: u32, rt: u32, sym: u32, addend: i64) {
    let base: u32 = if k < 4 { rt } else { AX16 };
    a_rela(sym, R_AARCH64_ADR_PREL_PG_HI21, addend);
    a_adrp_raw(base);
    let lt: u32 = if s == 0 { R_AARCH64_LDST8_ABS_LO12_NC } else if s == 1 { R_AARCH64_LDST16_ABS_LO12_NC }
                  else if s == 2 { R_AARCH64_LDST32_ABS_LO12_NC } else if s == 3 { R_AARCH64_LDST64_ABS_LO12_NC }
                  else { R_AARCH64_LDST128_ABS_LO12_NC };
    a_rela(sym, lt, addend);
    a_ls_uimm(k, s, rt, base, 0);
}
// Address of the constant's pool entry in r.
fn a_const_addr(r: u32, ci: u32) {
    let sym, add = a_const_ref(ci);
    a_adr_sym(r, sym, add);
}
// A global's address can be formed pc-relative (no GOT).
fn a_local_ref(g: u32) -> bool {
    let fl = M.globals[g].flags;
    return fl & (GF_LOCALREF | GF_INTERNAL) != 0 && fl & GF_TLS == 0;
}
fn a_global_addr(r: u32, g: u32) {
    if a_local_ref(g) {
        a_adr_sym(r, g_sym[g], 0);
        return;
    }
    a_rela(g_sym[g], R_AARCH64_ADR_GOT_PAGE, 0);
    a_adrp_raw(r);
    a_rela(g_sym[g], R_AARCH64_LD64_GOT_LO12_NC, 0);
    a_ls_uimm(LS_LDR, 3, r, r, 0);
}

// The 64 bits of an INT-class constant, or of a small FP/vector constant.
fn a_const_bits(ci: u32) -> u64 {
    let c = M.consts[ci];
    if c.data == GIR_NONE { return c.lo; }
    var x: u64 = 0;
    let n = size_of(c.ty);
    for k in 0..n {
        if k >= 8 { break; }
        x |= (M.data[c.data + k] as u64) << (8 * k);
    }
    return x;
}

// ------------------------------------------------------------ fetching values

// INT value v (not in a register) into general register r.
fn a_mat_gpr(v: u32, r: u32) {
    let k = gir_kind(v);
    let i = gir_idx(v);
    if k == GIR_V_CONST {
        let c = M.consts[i];
        let w64 = size_of(c.ty) > 4;
        a_mov_imm(r, a_const_bits(i), w64);
        return;
    }
    if k == GIR_V_GLOBAL {
        a_global_addr(r, i);
        return;
    }
    let id = vid(v);
    let h = vi[id].home;
    if h == H_ALLOCA {
        a_add_off(r, AFP, vi[id].off as i64);
        return;
    }
    if h == H_PTR || h == H_BYVAL {
        a_ls(LS_LDR, 3, r, AFP, vi[id].off as i64);
        return;
    }
    let t = vtype(id);
    a_load_t(r, AFP, a_home_off(id) as i64, t);
}
// INT value v in a general register (locked). With `clean`, zero-extended
// above its width.
fn a_gpr(v: u32, clean: bool) -> u32 {
    if is_val(v) {
        let id = vid(v);
        let r: u32 = vi[id].reg;
        if r < 64 {
            if r >= 32 { assert(false); }
            a_lock |= abit(r);
            a_note(id);
            if clean && vi[id].st & ST_EXT != 0 { a_norm(id, r); }
            return r;
        }
        let h = vi[id].home;
        if h == H_ALLOCA || h == H_PTR || h == H_BYVAL {
            let t = a_temp();
            a_mat_gpr(v, t);
            a_note(id);
            return t;
        }
        let n = a_alloc_r(A_GP_ALL, a_pref_gp(id));
        a_mat_gpr(v, n);
        a_rval[n] = id;
        vi[id].reg = n as! u8;
        a_note(id);
        return n;
    }
    let t = a_temp();
    a_mat_gpr(v, t);
    return t;
}
// Like a_gpr, but a constant 0 is xzr (for the operand fields that read 31 as zr).
fn a_gpr_z(v: u32, clean: bool) -> u32 {
    if gir_kind(v) == GIR_V_CONST && a_const_bits(gir_idx(v)) == 0 && cls_of(M.consts[gir_idx(v)].ty) == C_INT { return AZR; }
    return a_gpr(v, clean);
}
// v into exactly register r, which the instruction then owns.
fn a_gpr_into(v: u32, r: u32, clean: bool) {
    var src: u32 = 64;
    var id: u32 = RV_NONE;
    if is_val(v) {
        id = vid(v);
        let vr: u32 = vi[id].reg;
        if vr < 64 { src = vr; }
    }
    if src == r {
        if a_live_after(id) {
            a_evacuate(id, r);
            a_free &= ~abit(r);
            a_rval[r] = RV_TEMP;
            a_tmp |= abit(r);
        }
        a_lock |= abit(r);
        a_note(id);
        if clean && vi[id].st & ST_EXT != 0 {
            a_zext(r, bits_of(vtype(id)));
            if vi[id].reg == r as! u8 { vi[id].st &= ~ST_EXT; }
        }
        return;
    }
    let occ = a_rval[r];
    if occ < RV_TEMP { a_evacuate(occ, r); }
    a_free &= ~abit(r);
    a_rval[r] = RV_TEMP;
    a_tmp |= abit(r);
    a_lock |= abit(r);
    if src < 64 {
        a_mov_rr(true, r, src);
        a_lock |= abit(src);
        a_note(id);
        if clean && vi[id].st & ST_EXT != 0 { a_zext(r, bits_of(vtype(id))); }
        return;
    }
    if id != RV_NONE { a_note(id); }
    a_mat_gpr(v, r);
}
// FP / vector value v (not in a register) into V register r.
fn a_mat_v(v: u32, r: u32) {
    let k = gir_kind(v);
    let i = gir_idx(v);
    if k == GIR_V_CONST {
        let c = M.consts[i];
        let t = c.ty;
        let st = M.types[t].store;
        if c.lo == 0 && c.hi == 0 && c.data == GIR_NONE {
            a_vzero(st == 16, r);
            return;
        }
        if t == GIR_T_F32 || t == GIR_T_F64 {
            let imm = a_fp_imm8(c.lo, t == GIR_T_F64);
            if imm != 0xFFFFFFFF {
                a_fmov_imm8(a_ft(t), r, imm);
                return;
            }
        }
        let sym, add = a_const_ref(i);
        a_ld_sym(LS_FLDR, a_log2(if st < 2 { 2 } else { st }), r, sym, add);
        return;
    }
    let id = vid(v);
    let t = vtype(id);
    a_load_t(r, AFP, a_home_off(id) as i64, t);
}
fn a_vr(v: u32) -> u32 {
    if is_val(v) {
        let id = vid(v);
        let r: u32 = vi[id].reg;
        if r < 64 {
            if r < 32 { assert(false); }
            a_lock |= abit(r);
            a_note(id);
            return r;
        }
        let n = a_alloc_r(A_V_ALL, a_pref_v(id));
        a_mat_v(v, n);
        a_rval[n] = id;
        vi[id].reg = n as! u8;
        a_note(id);
        return n;
    }
    let t = a_vtemp();
    a_mat_v(v, t);
    return t;
}
fn a_vr_into(v: u32, r: u32) {
    var src: u32 = 64;
    var id: u32 = RV_NONE;
    if is_val(v) {
        id = vid(v);
        let vr: u32 = vi[id].reg;
        if vr < 64 { src = vr; }
    }
    if src == r {
        if a_live_after(id) {
            a_evacuate(id, r);
            a_free &= ~abit(r);
            a_rval[r] = RV_TEMP;
            a_tmp |= abit(r);
        }
        a_lock |= abit(r);
        a_note(id);
        return;
    }
    let occ = a_rval[r];
    if occ < RV_TEMP { a_evacuate(occ, r); }
    a_free &= ~abit(r);
    a_rval[r] = RV_TEMP;
    a_tmp |= abit(r);
    a_lock |= abit(r);
    if src < 64 {
        a_vmov(true, r, src);
        a_lock |= abit(src);
        a_note(id);
        return;
    }
    if id != RV_NONE { a_note(id); }
    a_mat_v(v, r);
}
// A register for the result of j (its class).
fn a_def(j: u32) -> u32 {
    let t = M.insts[f_first_inst + j].ty;
    if a_inv(arc(t)) { return a_alloc_r(A_V_ALL, a_pref_v(j)); }
    let h: u32 = vi[j].hint;
    if h < 32 && vi[j].st & (ST_CS | ST_GLOB) == 0 && a_free & ~a_lock & abit(h) & a_alloc != 0 {
        return a_alloc_r(A_GP_ALL, abit(h));
    }
    return a_alloc_r(A_GP_ALL, a_pref_gp(j));
}
// The register of operand v if the result may take it over (v dies here).
fn a_reuse(v: u32) -> u32 {
    if !is_val(v) { return 64; }
    let id = vid(v);
    let r: u32 = vi[id].reg;
    if r >= 64 { return 64; }
    if vi[id].st & ST_GLOB != 0 || vi[id].last != cur_pos { return 64; }
    return r;
}
// The result of j is in r (ext: garbage above its width). Global values are
// written to their home at once; a result nobody uses is dropped.
fn a_set(j: u32, r: u32, ext: bool) {
    let old = a_rval[r];
    if old < RV_TEMP && old != j { vi[old].reg = NOREG; }
    a_tmp &= ~abit(r);
    a_free &= ~abit(r);
    a_lock |= abit(r);
    a_rval[r] = j;
    vi[j].reg = r as! u8;
    var st = vi[j].st & ~(ST_MEM | ST_EXT);
    if ext { st |= ST_EXT; }
    vi[j].st = st;
    if st & ST_GLOB != 0 {
        a_store_home(j, r);
    } else if vi[j].nuse == 0 {
        a_rval[r] = RV_NONE;
        vi[j].reg = NOREG;
        a_free |= abit(r);
    }
}

// ------------------------------------------------------------ blocks

fn a_func_start() {
    for r in 64 { a_rval[r] = RV_NONE; }
    a_free = a_alloc;
    a_lock = 0;
    a_tmp = 0;
    dying.clear();
    a_flags_id = RV_NONE;
}
fn a_block_start() {
    var m = ~a_free & a_alloc;
    while m != 0 {
        let r = actz(m);
        m &= m - 1;
        let id = a_rval[r];
        if id < RV_TEMP { vi[id].reg = NOREG; }
        a_rval[r] = RV_NONE;
    }
    a_free = a_alloc;
    a_lock = 0;
    a_tmp = 0;
    a_flags_id = RV_NONE;
    a_paddr_id = RV_NONE;
    a_carry = false;
}
var a_carry = false;     // the instruction's registers stay locked into the next one (a folded GEP)
fn a_end_inst() {
    if a_carry {
        a_carry = false;
        return;
    }
    for id in dying {
        let r: u32 = vi[id].reg;
        if r < 64 && a_rval[r] == id {
            vi[id].reg = NOREG;
            a_release(r);
        }
        if f_share && vi[id].off != 0 && vi[id].home == H_SLOT && vi[id].st & (ST_GLOB | ST_PHI) == 0 {
            a_free_slot(id);
        }
    }
    dying.clear();
    var m = a_tmp;
    while m != 0 {
        let r = actz(m);
        m &= m - 1;
        a_rval[r] = RV_NONE;
    }
    a_free |= a_tmp;
    a_tmp = 0;
    a_lock = 0;
}

// A compare whose flags feed the next instruction (CONDBR, SELECT): its
// condition(s): cc, or cc && cc2 (comb 1) or cc || cc2 (comb 2).
var a_flags_id: u32 = 0xFFFFFFFF;
var a_fcc: u32 = 0;
var a_fcc2: u32 = 0;
var a_fcomb: u32 = 0;
// A GEP folded into the next load or store (its address mode).
var a_paddr_id: u32 = 0xFFFFFFFF;
