// Value locations.
//
// Every instruction lowering reaches its operands and its result only
// through the functions in the "value-location interface" section below.
// The A1 policy behind them is "always spill": every value has a home in
// the frame (or is a constant, a global address or an alloca address), a
// use loads it into the scratch register the lowering suggests, and a
// definition stores the register back to the home right away. A register
// allocator (A2) replaces the policy here, not the lowerings: `use_gpr` may
// then return the register the value already lives in, `def_gpr` may pick
// the result register, and `put_gpr` may keep the value in it.
//
// Homes, per local instruction j (index = global index - f_first_inst):
//   H_SLOT    v_off[j] is the rbp offset of its result slot
//   H_ALLOCA  the value is the address rbp + v_off[j] (static alloca)
//   H_PTR     the value is the pointer stored at rbp + v_off[j] (over-aligned alloca)
// and per argument a: A_SLOT (slot at a_off[a]) or A_BYVAL (the value is
// the address rbp + a_off[a] of the caller's copy).

let H_NONE = 0;
let H_SLOT = 1;
let H_ALLOCA = 2;
let H_PTR = 3;
let A_SLOT = 1;
let A_BYVAL = 2;

// Per function (index = local instruction / block / argument number).
var f_first_inst: u32 = 0;
var f_first_block: u32 = 0;
var f_args: u32 = 0;            // opnds index of the (type, abi) argument run
var f_nargs: u32 = 0;
var f_index: u32 = 0;           // funcs index of the current function
var v_off: i32[>..] = [];
var v_home: u8[>..] = [];
var t_off: i32[>..] = [];       // rbp offset of a PHI's temp slot
var a_off: i32[>..] = [];
var a_home: u8[>..] = [];
var block_off: u32[>..] = [];   // code offset of each local block
var scratch_off: i32 = 0;       // 32 bytes of per-function scratch, 16-aligned
var rsa_off: i32 = 0;           // register save area (va_start), 176 bytes
var va_gp: u32 = 0;             // general registers taken by named arguments
var va_fp: u32 = 0;             // vector registers taken by named arguments
var va_stack: u32 = 0;          // stack bytes taken by named arguments
var f_sjlj: bool = false;       // callee-saved registers saved below rbp

// Constant pools (per module): offset of each constant in its pool, or NONE.
var c_pool: u32[>..] = [];

// --------------------------------------------------------------- types

fn tdef(t: u32) -> TypeDef { M.types[t] }
fn cls_of(t: u32) -> u32 { M.types[t].cls }
fn bits_of(t: u32) -> u32 { M.types[t].bits }
fn size_of(t: u32) -> u32 { M.types[t].size }
fn store_of(t: u32) -> u32 { M.types[t].store }
fn type_of(v: u32) -> u32 {
    let i = gir_idx(v);
    let k = gir_kind(v);
    if k == GIR_V_INST { return M.insts[i].ty; }
    if k == GIR_V_ARG { return M.opnds[f_args + 2 * i]; }
    if k == GIR_V_CONST { return M.consts[i].ty; }
    return GIR_T_PTR;
}
// Slot size of a value of type t: INT and FP 8, INT2 and X87 16, else the
// allocation size rounded up to 8.
fn slot_size(t: u32) -> i64 {
    let c = cls_of(t);
    if c == C_INT || c == C_FP { return 8; }
    if c == C_INT2 || c == C_X87 { return 16; }
    let s: i64 = size_of(t);
    if s == 0 { return 8; }
    return (s + 7) & ~7;
}
fn slot_align(t: u32) -> i64 { if slot_size(t) >= 16 { 16 } else { 8 } }

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
    var k: u32 = 0;
    while k + 8 <= n {
        load64(RAX, m_add(src, k));
        store64(m_add(dst, k), RAX);
        k += 8;
    }
    if k + 4 <= n {
        load32(RAX, m_add(src, k));
        store32(m_add(dst, k), RAX);
        k += 4;
    }
    if k + 2 <= n {
        load16z(RAX, m_add(src, k));
        store16(m_add(dst, k), RAX);
        k += 2;
    }
    if k < n {
        load8z(RAX, m_add(src, k));
        store8(m_add(dst, k), RAX);
    }
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
    var off = c_pool[ci];
    if off == GIR_NONE {
        if sec == SEC_CST4 {
            off = cst4.len as! u32;
            let v: u32 = c.lo as! u32;
            o4(cst4, v);
        } else if sec == SEC_CST8 {
            off = cst8.len as! u32;
            if c.data != GIR_NONE { cst8.append(M.data[c.data..c.data + 8]); }
            else { o8(cst8, c.lo); }
        } else if sec == SEC_CST16 {
            off = cst16.len as! u32;
            if c.data != GIR_NONE { cst16.append(M.data[c.data..c.data + 16]); }
            else {
                o8(cst16, c.lo);
                o8(cst16, c.hi);
            }
        } else {
            let al: u32 = if M.types[t].align > 16 { M.types[t].align } else { 16 };
            while (srodata.len as u64) % al != 0 { srodata.push(0); }
            if al > rodata_align { rodata_align = al; }
            off = srodata.len as! u32;
            if c.data != GIR_NONE { srodata.append(M.data[c.data..c.data + size]); }
            else { srodata.resize(srodata.len + size, 0); }
        }
        c_pool[ci] = off;
    }
    return m_sym(sec_sym(sec), R_X86_64_PC32, off as! i32);
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

// ================================================ value-location interface

// Home memory of local instruction j (H_SLOT or the alloca area).
fn res_mem(j: u32) -> Mem { m_rbp(v_off[j]) }

// The bytes of value v (any class but INT constants and addresses): its
// slot, or a constant's pool entry.
fn val_mem(v: u32) -> Mem {
    let i = gir_idx(v);
    let k = gir_kind(v);
    if k == GIR_V_INST { return m_rbp(v_off[i - f_first_inst]); }
    if k == GIR_V_ARG { return m_rbp(a_off[i]); }
    return const_mem(i);
}

// INT-class value v into register r, zero-extended to 64 bits (only r is
// written). Returns the register that holds v: under A1 always r.
fn use_gpr(v: u32, r: u32) -> u32 {
    let i = gir_idx(v);
    let k = gir_kind(v);
    if k == GIR_V_INST {
        let j = i - f_first_inst;
        let h = v_home[j];
        if h == H_ALLOCA { lea64(r, m_rbp(v_off[j])); }
        else { load64(r, m_rbp(v_off[j])); }
    } else if k == GIR_V_ARG {
        if a_home[i] == A_BYVAL { lea64(r, m_rbp(a_off[i])); }
        else { load64(r, m_rbp(a_off[i])); }
    } else if k == GIR_V_CONST {
        let c = M.consts[i];
        if cls_of(c.ty) == C_INT { mov_ri(r, c.lo); }
        else { load_n(r, const_mem(i), size_of(c.ty)); }  // the bits of a small FP/vector constant
    } else {
        global_addr(r, i);
    }
    return r;
}
// v into exactly register r (fixed-register operands: shift counts, call
// arguments, division).
fn use_fixed(v: u32, r: u32) { use_gpr(v, r); }
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
    let m = val_mem(v);
    if t == GIR_T_F32 { movss_load(x, m); } else { movsd_load(x, m); }
    return x;
}
// Register for the result of local instruction j (A1: the suggestion).
fn def_gpr(j: u32, r: u32) -> u32 { r }
// The result of j is in r (zero-extended): A1 stores it to its slot.
fn put_gpr(j: u32, r: u32) { store64(m_rbp(v_off[j]), r); }
fn put_gpr2(j: u32, lo: u32, hi: u32) {
    store64(m_rbp(v_off[j]), lo);
    store64(m_rbp(v_off[j] + 8), hi);
}
// The FP result of j is in xmm x.
fn put_xmm(j: u32, x: u32, t: u32) {
    if t == GIR_T_F16 {
        movd_rx(RAX, x);
        movzx16(RAX, RAX);
        store64(m_rbp(v_off[j]), RAX);
    } else if t == GIR_T_F32 { movss_store(m_rbp(v_off[j]), x); }
    else { movsd_store(m_rbp(v_off[j]), x); }
}
// Memory operand of the address held by pointer value v: an alloca or a
// local global is addressed directly, anything else is loaded into scratch.
fn addr_of(v: u32, scratch: u32) -> Mem {
    let i = gir_idx(v);
    let k = gir_kind(v);
    if k == GIR_V_INST && v_home[i - f_first_inst] == H_ALLOCA { return m_rbp(v_off[i - f_first_inst]); }
    if k == GIR_V_ARG && a_home[i] == A_BYVAL { return m_rbp(a_off[i]); }
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
    copy_mem(dst, val_mem(v), m);
}
