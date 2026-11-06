// Value locations: type helpers, normalization, memory copies, constant
// pools, global addresses, and the legacy value-location interface.
//
// Register allocation is in ra.goose. Instructions are lowered in one of
// two ways (gen_inst in cg.goose):
//
//   - allocator-aware lowerings (lowera.goose, the calls and terminators)
//     use the ra_* interface: an operand stays in the register it lives in,
//     a result gets a register of its own;
//   - legacy lowerings (lower.goose: INT2, x87, vectors, aggregates, bit
//     operations, atomics, inline asm, ...) use the interface below, which
//     keeps milestone A1's contract: operands are fetched into the scratch
//     registers the lowering names, scratch registers rax..r11 and xmm0..15
//     may be clobbered freely, results are handed back with put_*. Before a
//     legacy lowering, ra_tierb_begin spills every value that lives in a
//     caller-saved register (callee-saved registers survive), and
//     ra_tierb_end takes over the result register.

// Per function.
var f_first_inst: u32 = 0;
var f_first_block: u32 = 0;
var f_args: u32 = 0;            // opnds index of the (type, abi) argument run
var f_nargs: u32 = 0;
var f_index: u32 = 0;           // funcs index of the current function
var scratch_off: i32 = 0;       // 32 bytes of per-function scratch (0 = not allocated yet)
var rsa_off: i32 = 0;           // register save area (va_start), 176 bytes
var va_gp: u32 = 0;             // general registers taken by named arguments
var va_fp: u32 = 0;             // vector registers taken by named arguments
var va_stack: u32 = 0;          // stack bytes taken by named arguments
var f_sjlj: bool = false;       // __builtin_setjmp: all callee-saved registers are saved
var tierb = false;              // a legacy lowering is running
var tb_id: u32 = 0xFFFFFFFF;    // its result register (put_gpr / put_xmm)
var tb_reg: u32 = 0;

// Constant pools (per module): offset of each constant in its pool, or NONE.
var c_pool: u32[>..] = [];
// Sign and magnitude masks (16 bytes each in .rodata.cst16): f32 sign, f64
// sign, f32 abs, f64 abs; pool symbols, or NONE.
var mask_pool: u32[4] = [0xFFFFFFFF; 4];

// --------------------------------------------------------------- types

inline fn tdef(t: u32) -> TypeDef { M.types[t] }
inline fn cls_of(t: u32) -> u32 { M.types[t].cls }
inline fn bits_of(t: u32) -> u32 { M.types[t].bits }
inline fn size_of(t: u32) -> u32 { M.types[t].size }
inline fn store_of(t: u32) -> u32 { M.types[t].store }
inline fn type_of(v: u32) -> u32 {
    let i = gir_idx(v);
    let k = gir_kind(v);
    if k == GIR_V_INST { return M.insts[i].ty; }
    if k == GIR_V_ARG { return M.opnds[f_args + 2 * i]; }
    if k == GIR_V_CONST { return M.consts[i].ty; }
    return GIR_T_PTR;
}

// The 32 bytes of scratch (x87 control words, conversion temporaries),
// allocated in the frame on first use.
fn scr() -> i32 {
    if scratch_off == 0 {
        lay_off = (lay_off + 32 + 15) & ~15;
        scratch_off = (-lay_off) as! i32;
    }
    return scratch_off;
}

// ------------------------------------------------- normalization (INT class)
// Values narrower than 64 bits are kept zero-extended in registers and slots.

checkfree fn zext_reg(r: u32, bits: u32) {
    if bits >= 64 { return; }
    if bits == 1 { and_ri32(r, 1); }
    else if bits == 8 { movzx8(r, r); }
    else if bits == 16 { movzx16(r, r); }
    else if bits == 32 { mov_rr32(r, r); }
    else if bits < 32 { grp1_ri32(G1_AND, r, ((1 as u32) << bits) - 1); }
    else {
        shift_imm64(SH_SHL, r, 64 - bits);
        shift_imm64(SH_SHR, r, 64 - bits);
    }
}
checkfree fn sext_reg(r: u32, bits: u32) {
    if bits >= 64 { return; }
    if bits == 1 {
        and_ri32(r, 1);
        neg64(r);
    } else if bits == 8 { movsx8_64(r, r); }
    else if bits == 16 { movsx16_64(r, r); }
    else if bits == 32 { movsxd(r, r); }
    else {
        shift_imm64(SH_SHL, r, 64 - bits);
        shift_imm64(SH_SAR, r, 64 - bits);
    }
}

// ------------------------------------------------------- memory access
// Zero-extending load of `n` (1..8) bytes at x into r (r != x's base); uses
// R10 for 3, 5, 6 and 7 bytes.
checkfree fn load_n(r: u32, x: Mem, n: u32) {
    if n == 1 { load8z(r, x); }
    else if n == 2 { load16z(r, x); }
    else if n == 4 { load32(r, x); }
    else if n >= 8 { load64(r, x); }
    else if n == 3 {
        load16z(r, x);
        load8z(R10, m_add(x, 2));
        shift_imm32(SH_SHL, R10, 16);
        alu_rr32(ALU_OR, r, R10);
    } else {
        load32(r, x);
        if n == 5 { load8z(R10, m_add(x, 4)); }
        else { load16z(R10, m_add(x, 4)); }
        if n == 7 {
            load8z(R11, m_add(x, 6));
            shift_imm32(SH_SHL, R11, 16);
            alu_rr32(ALU_OR, R10, R11);
        }
        shift_imm64(SH_SHL, R10, 32);
        alu_rr64(ALU_OR, r, R10);
    }
}
// Store of the low `n` (1..8) bytes of r at x (destroys r for 3, 5, 6, 7).
checkfree fn store_n(x: Mem, r: u32, n: u32) {
    if n == 1 { store8(x, r); }
    else if n == 2 { store16(x, r); }
    else if n == 4 { store32(x, r); }
    else if n >= 8 { store64(x, r); }
    else if n == 3 {
        store16(x, r);
        shift_imm32(SH_SHR, r, 16);
        store8(m_add(x, 2), r);
    } else {
        store32(x, r);
        shift_imm64(SH_SHR, r, 32);
        if n == 5 { store8(m_add(x, 4), r); }
        else if n == 6 { store16(m_add(x, 4), r); }
        else {
            store16(m_add(x, 4), r);
            shift_imm32(SH_SHR, r, 16);
            store8(m_add(x, 6), r);
        }
    }
}
// Copies n bytes from src to dst in units of g bytes (1, 2, 4 or 8) through
// register t.
fn copy_mem_t(dst: Mem, src: Mem, n: u32, g: u32, t: u32) {
    var k: u32 = 0;
    while k + 8 <= n && g >= 8 {
        load64(t, m_add(src, k));
        store64(m_add(dst, k), t);
        k += 8;
    }
    while k + 4 <= n && g >= 4 {
        load32(t, m_add(src, k));
        store32(m_add(dst, k), t);
        k += 4;
    }
    while k + 2 <= n && g >= 2 {
        load16z(t, m_add(src, k));
        store16(m_add(dst, k), t);
        k += 2;
    }
    while k < n {
        load8z(t, m_add(src, k));
        store8(m_add(dst, k), t);
        k += 1;
    }
}
// Copies n bytes from src to dst through RAX (RAX clobbered). Large copies
// use rep movsb (RSI, RDI, RCX clobbered).
fn copy_mem(dst: Mem, src: Mem, n: u32) {
    if n > 64 {
        lea64(RSI, src);
        lea64(RDI, dst);
        mov_ri(RCX, n);
        rep_movsb();
        return;
    }
    copy_mem_t(dst, src, n, 8, RAX);
}
// copy_mem in units of g bytes (1, 2 or 4). Vectors are written lane by
// lane, so they are copied lane by lane too: a wider load of data written
// by narrower stores misses the store-to-load forwarding (~15 cycles).
fn copy_mem_g(dst: Mem, src: Mem, n: u32, g: u32) {
    if g >= 8 || n > 64 {
        copy_mem(dst, src, n);
        return;
    }
    copy_mem_t(dst, src, n, g, RAX);
}
// Copy granule of a value of type t.
fn gran_of(t: u32) -> u32 {
    if cls_of(t) != C_VEC { return 8; }
    let ls = M.types[M.types[t].elems].size;
    return if ls == 0 { 1 } else { ls };
}

// ------------------------------------------------------------ constants
// Pool memory of constant c (FP, X87, INT2, VEC, MEM classes), allocated
// on first use: f32 in .rodata.cst4, f64 in .rodata.cst8, f80/i128/16-byte
// vectors in .rodata.cst16, everything else at the end of .rodata.
fn const_mem(ci: u32) -> Mem {
    let c = M.consts[ci];
    let t = c.ty;
    let size = size_of(t);
    var sec: u32 = SEC_RODATA;
    if size == 4 && c.data == GIR_NONE && cls_of(t) == C_FP { sec = SEC_CST4; }
    else if size == 8 && cls_of(t) != C_MEM && cls_of(t) != C_VEC { sec = SEC_CST8; }
    else if size == 16 && cls_of(t) != C_MEM { sec = SEC_CST16; }
    else if size <= 2 && cls_of(t) == C_FP { sec = SEC_CST4; }  // half: in a 4-byte entry
    // c_pool[ci]: the pool symbol (mergeable pools) or the .rodata offset.
    var ref = c_pool[ci];
    if ref == GIR_NONE {
        if sec == SEC_CST4 {
            ref = new_pool_sym(sec, cst4.len as! u32, 4);
            let v: u32 = c.lo as! u32;
            o4(cst4, v);
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
    // Entries of the SHF_MERGE pools are referenced through their own local
    // symbol: a linker resolves a section-symbol relocation into a mergeable
    // section by its addend, which for rip-relative operands is off - 4.
    if sec == SEC_RODATA { return m_sym(sec_sym(sec), R_X86_64_PC32, ref as! i32); }
    return m_sym(ref, R_X86_64_PC32, 0);
}
// A 16-byte mask in .rodata.cst16 (k: 0 f32 sign, 1 f64 sign, 2 f32 abs, 3 f64 abs).
fn mask_mem(k: u32) -> Mem {
    var ref = mask_pool[k % 4];
    if ref == GIR_NONE {
        ref = new_pool_sym(SEC_CST16, cst16.len as! u32, 16);
        let v: u64 = match k {
            0 => 0x8000000080000000,
            1 => 0x8000000000000000,
            2 => 0x7FFFFFFF7FFFFFFF,
            _ => 0x7FFFFFFFFFFFFFFF,
        };
        o8(cst16, v);
        o8(cst16, v);
        mask_pool[k % 4] = ref;
    }
    return m_sym(ref, R_X86_64_PC32, 0);
}

// ------------------------------------------------------- global addresses

fn sym_of(g: u32) -> u32 { g_sym[g] }
// A global's address can be formed rip-relative (no GOT).
fn is_local_ref(g: u32) -> bool {
    let fl = M.globals[g].flags;
    return fl & (GF_LOCALREF | GF_INTERNAL) != 0 && fl & GF_TLS == 0;
}
// Loads the address of global g into r.
fn global_addr(r: u32, g: u32) {
    if is_local_ref(g) { lea64(r, m_sym(g_sym[g], R_X86_64_PC32, 0)); }
    else { load64(r, m_sym(g_sym[g], R_X86_64_REX_GOTPCRELX, 0)); }
}

// ================================================ legacy lowerings' interface

fn ra_tierb_begin(all: bool) {
    ra_flush(if all { GP_ALLOC | XMM_ALL } else { GP_CALLER | XMM_ALL });
    tierb = true;
    tb_id = RV_NONE;
}
fn ra_tierb_end() {
    tierb = false;
    if tb_id != RV_NONE {
        ra_set(tb_id, tb_reg, false);
        tb_id = RV_NONE;
    }
}

// Home memory of local instruction j (its slot or its alloca area): the
// legacy lowering writes the result there.
fn res_mem(j: u32) -> Mem {
    v_st[j] |= ST_MEM;
    v_reg[j] = NOREG;
    return ra_home(j);
}

// The bytes of value v (any class but INT constants and addresses): its
// home (stored there first if it lives in a register), a deferred load's
// memory, or a constant's pool entry.
fn val_mem(v: u32) -> Mem {
    let k = gir_kind(v);
    if k == GIR_V_CONST { return const_mem(gir_idx(v)); }
    let id = vid(v);
    ra_note(id);
    let r: u32 = v_reg[id];
    if r == PEND { return ra_take_pend(id); }
    if r < 32 && v_st[id] & ST_MEM == 0 { ra_store_home(id, r); }
    if v_home[id] == H_STACK || v_home[id] == H_ALLOCA || v_home[id] == H_BYVAL { return m_rbp(v_off[id]); }
    return ra_home(id);
}

// INT-class value v into register r, zero-extended to 64 bits (only r is
// written). Returns r.
fn use_gpr(v: u32, r: u32) -> u32 {
    if is_val(v) {
        let id = vid(v);
        let vr: u32 = v_reg[id];
        if vr < 16 {
            ra_note(id);
            if vr != r { mov_rr64(r, vr); }
            if v_st[id] & ST_EXT != 0 { zext_reg(r, bits_of(vtype(id))); }
            return r;
        }
        if vr < 32 {
            // an f32/f64 value whose bits are wanted (inline asm, f16 paths)
            ra_note(id);
            if vtype(id) == GIR_T_F32 { movd_rx(r, vr - 16); } else { movq_rx(r, vr - 16); }
            return r;
        }
        ra_note(id);
        if rc_of(vtype(id)) == RC_XMM && v_home[id] == H_SLOT {
            let t = vtype(id);
            load_n(r, val_mem(v), store_of(t));
            return r;
        }
    }
    ra_mat_gpr(v, r);
    return r;
}
// v into exactly register r (fixed-register operands: shift counts, call
// arguments, division).
inline fn use_fixed(v: u32, r: u32) { use_gpr(v, r); }
// An INT2 value into (lo, hi).
fn use_gpr2(v: u32, lo: u32, hi: u32) {
    if gir_kind(v) == GIR_V_CONST {
        let c = M.consts[gir_idx(v)];
        mov_ri(lo, c.lo);
        mov_ri(hi, c.hi);
        return;
    }
    let x = val_mem(v);
    load64(lo, x);
    load64(hi, m_add(x, 8));
}
// An FP value (f16, f32, f64) into xmm register x.
fn use_xmm(v: u32, x: u32) -> u32 {
    let t = type_of(v);
    if t == GIR_T_F16 {
        use_gpr(v, RAX);
        movd_xr(x, RAX);
        return x;
    }
    if is_val(v) {
        let id = vid(v);
        let vr: u32 = v_reg[id];
        ra_note(id);
        if vr >= 16 && vr < 32 {
            if vr - 16 != x { movaps_rr(x, vr - 16); }
            return x;
        }
    }
    ra_mat_xmm(v, x);
    return x;
}
// The result of j is in r (zero-extended).
fn put_gpr(j: u32, r: u32) {
    if tierb {
        tb_id = j;
        tb_reg = r;
        return;
    }
    ra_set(j, r, false);
}
fn put_gpr2(j: u32, lo: u32, hi: u32) {
    let m = res_mem(j);
    store64(m, lo);
    store64(m_add(m, 8), hi);
}
// The FP result of j is in xmm x.
fn put_xmm(j: u32, x: u32, t: u32) {
    if t == GIR_T_F16 {
        movd_rx(RAX, x);
        movzx16(RAX, RAX);
        store64(res_mem(j), RAX);
        return;
    }
    if tierb {
        tb_id = j;
        tb_reg = x + 16;
        return;
    }
    ra_set(j, x + 16, false);
}
// Memory operand of the address held by pointer value v: an alloca or a
// local global is addressed directly, anything else is loaded into scratch.
fn addr_of(v: u32, scratch: u32) -> Mem {
    let i = gir_idx(v);
    let k = gir_kind(v);
    if k <= GIR_V_ARG {
        let id = vid(v);
        let h = v_home[id];
        if h == H_ALLOCA || h == H_BYVAL { return m_rbp(v_off[id]); }
    }
    if k == GIR_V_GLOBAL && is_local_ref(i) { return m_sym(g_sym[i], R_X86_64_PC32, 0); }
    use_gpr(v, scratch);
    return m_reg(scratch, 0);
}
// Copies the `n` bytes of value v to dst (through RAX, or RSI/RDI/RCX for
// large copies): INT values from a register, others memory to memory.
fn copy_val(dst: Mem, v: u32, n: u32) {
    let t = type_of(v);
    if cls_of(t) == C_INT {
        use_gpr(v, RAX);
        store_n(dst, RAX, n);
        return;
    }
    if gir_kind(v) == GIR_V_CONST && cls_of(t) == C_INT2 {
        let c = M.consts[gir_idx(v)];
        mov_ri(RAX, c.lo);
        store64(dst, RAX);
        if n > 8 {
            mov_ri(RAX, c.hi);
            store_n(m_add(dst, 8), RAX, n - 8);
        }
        return;
    }
    // A constant's pool entry holds only its stored bytes.
    let m: u32 = if gir_kind(v) == GIR_V_CONST && store_of(t) < n { store_of(t) } else { n };
    copy_mem_g(dst, val_mem(v), m, gran_of(t));
}
