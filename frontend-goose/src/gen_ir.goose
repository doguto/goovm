// goosecc B2: the GIR builder. The lowering (gen_*.goose) writes the GIR v2
// tables of gir/gir.h directly into global arrays of the back-end's record
// structs (backend-goose/gir.goose), and gir_codegen gets slices of them.
//
// Instructions of the function being lowered go to f_insts (local
// indices) and its static allocas to f_allocas; finish_function lays the
// function out (allocas first, blocks in the order they were started) and
// rewrites local value and block references into module-global ones.
// See ../DESIGN.md, "Lowering to GIR".

namespace gen;

import std;
import dictionary;
import .common;
import .types;
import .ast;

// ------------------------------------------------------------ module tables

var m_header: Header[>..] = [];
var m_types: TypeDef[>..] = [];
var m_funcs: Func[>..] = [];
var m_blocks: Block[>..] = [];
var m_insts: Inst[>..] = [];
extern fn prefault_insts(a: Inst[>..]&, bytes: i64) = "goosecc_prefault";
var m_opnds: u32[>..] = [];
var m_consts: Const[>..] = [];
var m_globals: Global[>..] = [];
var m_sections: Section[>..] = [];
var m_data: u8[>..] = [];
var m_drelocs: DataReloc[>..] = [];
var m_strtab: u8[>..] = [];
var m_dlocs: DLoc[>..] = [];
var m_dscopes: DScope[>..] = [];
var m_dfiles: DFile[>..] = [];
var m_dstr: u8[>..] = [];
var m_asms: Asm[>..] = [];

let NONE: u32 = 0xFFFFFFFF;
let KCONST: u32 = 0x80000000;    // GIR_V_CONST << 30
let KGLOBAL: u32 = 0xC0000000;   // GIR_V_GLOBAL << 30
let KARG: u32 = 0x40000000;      // GIR_V_ARG << 30
let ATAG: u32 = 0x20000000;      // local refs from here on are allocas (index ATAG + k)
let ABI_SRET: u32 = 0x40000000;

var opt_pie: bool = true;
var opt_pic: bool = false;       // -fPIC / -fpic: defined globals are preemptible
var opt_debug: bool = false;     // -g
var opt_gir_level: u32 = 0;      // GIR opt_level (E2): -O1 1, -O2 2, -O3 3, -Os 2 | 1 << 8, -Oz 2 | 2 << 8
var opt_no_inline: bool = false; // -fno-inline
var opt_common: bool = false;    // -fcommon

fn tdef(kind: u32, cls: u32, bits: u32, size: u32, align: u32, store: u32) {
    m_types.push(TypeDef { kind: kind as! u8, cls: cls as! u8, bits: bits as! u16, size: size, align: align, store: store, n: 0, elems: 0 });
}

fn ir_init() {
    m_header.push(Header { version: 2, flags: if opt_pie { MF_PIE } else { 0 }, tls_get_addr: NONE, n_llvm_insts: 0,
        r0: 0, r1: 0, r2: 0, r3: 0 });
    tdef(TK_VOID, C_NONE, 0, 0, 1, 0);
    tdef(TK_INT, C_INT, 1, 1, 1, 1);
    tdef(TK_INT, C_INT, 8, 1, 1, 1);
    tdef(TK_INT, C_INT, 16, 2, 2, 2);
    tdef(TK_INT, C_INT, 32, 4, 4, 4);
    tdef(TK_INT, C_INT, 64, 8, 8, 8);
    tdef(TK_PTR, C_INT, 64, 8, 8, 8);
    tdef(TK_FLOAT, C_FP, 32, 4, 4, 4);
    tdef(TK_FLOAT, C_FP, 64, 8, 8, 8);
    tdef(TK_FLOAT, C_X87, 80, 16, 16, 10);
    tdef(TK_INT, C_INT2, 128, 16, 16, 16);
    tdef(TK_FLOAT, C_FP, 16, 2, 2, 2);
    while m_types.len < 16 { tdef(TK_VOID, C_NONE, 0, 0, 1, 0); }
    m_strtab.push(0);
    m_dstr.push(0);
    m_dlocs.push(DLoc { line: 0, col: 0, scope: 0, inlined_at: 0 });
    m_dscopes.push(DScope { kind: 0, parent: 0, file: 0, line: 0, name: 0, extra: 0 });
    m_dfiles.push(DFile { name: 0, dir: 0 });
}

// ---------------------------------------------------------------- GIR types

fn tcls(t: u32) -> u32 { m_types[t].cls as u32 }
fn tkind(t: u32) -> u32 { m_types[t].kind as u32 }
fn tbits(t: u32) -> u32 { m_types[t].bits as u32 }
fn tsize(t: u32) -> u32 { m_types[t].size }
fn tstore(t: u32) -> u32 { m_types[t].store }

var int_types: u32[>..] = [];      // bits -> type id (0 = not made yet)

// The integer type of `bits` bits (LLVM's DataLayout: an odd width takes
// the alignment of the next listed width).
fn ty_int(bits: u32) -> u32 {
    if bits == 1 { return GIR_T_I1; }
    if bits == 8 { return GIR_T_I8; }
    if bits == 16 { return GIR_T_I16; }
    if bits == 32 { return GIR_T_I32; }
    if bits == 64 { return GIR_T_I64; }
    if bits == 128 { return GIR_T_I128; }
    while int_types.len <= bits { int_types.push(0); }
    if int_types[bits] != 0 { return int_types[bits]; }
    let store = (bits + 7) / 8;
    var al: u32 = 1;
    if bits <= 8 { al = 1; } else if bits <= 16 { al = 2; } else if bits <= 32 { al = 4; } else if bits <= 64 { al = 8; } else { al = 16; }
    let size = (store + al - 1) / al * al;
    let id = m_types.len as! u32;
    m_types.push(TypeDef { kind: TK_INT, cls: if bits <= 64 { C_INT } else { C_INT2 }, bits: bits as! u16, size: size,
        align: al, store: store, n: 0, elems: 0 });
    int_types[bits] = id;
    return id;
}

fn pow2_at_least(x: u32) -> u32 {
    var a: u32 = 1;
    while a < x { a *= 2; }
    return a;
}

// <n x elem>; i1 lanes are one byte each (gir.h).
fn ty_vec(n: u32, elem: u32) -> u32 {
    for t, i in m_types {
        if i >= 16 && t.kind == TK_VECTOR && t.n == n && t.elems == elem { return i as! u32; }
    }
    let es = if elem == GIR_T_I1 { 1 } else { tsize(elem) };
    let store = n * es;
    var al = pow2_at_least(store);
    let size = (store + al - 1) / al * al;
    if elem == GIR_T_I1 { al = 1; }
    let id = m_types.len as! u32;
    m_types.push(TypeDef { kind: TK_VECTOR, cls: C_VEC, bits: 0, size: if elem == GIR_T_I1 { n } else { size }, align: al,
        store: store, n: n, elems: elem });
    return id;
}

// A struct of the (type, offset) pairs in sfields.
var sfields: u32[>..<] = [];

fn ty_struct() -> u32 {
    let nf = (sfields.len / 2) as! u32;
    for t, i in m_types {
        if i >= 16 && t.kind == TK_STRUCT && t.n == nf {
            var same = true;
            for k in 0..sfields.len { if m_opnds[t.elems + k] != sfields[k] { same = false; break; } }
            if same { sfields.clear(); return i as! u32; }
        }
    }
    var al: u32 = 1;
    var end: u32 = 0;
    for k in 0..nf {
        let ft = sfields[2 * k];
        if m_types[ft].align > al { al = m_types[ft].align; }
        let e = sfields[2 * k + 1] + tsize(ft);
        if e > end { end = e; }
    }
    let size = (end + al - 1) / al * al;
    let s = m_opnds.len as! u32;
    for x in sfields { m_opnds.push(x); }
    sfields.clear();
    let id = m_types.len as! u32;
    m_types.push(TypeDef { kind: TK_STRUCT, cls: C_MEM, bits: 0, size: size, align: al, store: size, n: nf, elems: s });
    return id;
}

// { a @0, b @off }
var pair_types = dictionary<u64, u32> {};

// The lowering's maps keyed by a u32 (one dictionary, so one data stack):
// gk(table, key).
let GM_VEC = 1;        // C type index -> GIR vector type
let GM_FABI = 2;       // C function type -> its first Abi record
let GM_NOBUILTIN = 3;  // -fno-builtin-NAME identifiers (value 1)
let GM_DSTR = 4;       // interned string -> offset in m_dstr
let GM_NAMEGLOB = 5;   // linkage name (ident) -> global
let GM_DEFBY = 6;      // linkage name -> the symbol of the function defined under it
let GM_SECNAME = 7;    // interned section name -> section index
let GM_LIBFN = 8;      // interned library function name -> global
var gmap = dictionary<u64, u32> {};
fn gk(table: u64, key: u32) -> u64 { (table << 32) | (key as u64) }

fn ty_pair(a: u32, b: u32, off: u32) -> u32 {
    let key = (a as u64) | ((b as u64) << 16) | ((off as u64) << 32);
    let r = pair_types.get(key);
    if r { return r; }
    sfields.push(a);
    sfields.push(0);
    sfields.push(b);
    sfields.push(off);
    let t = ty_struct();
    pair_types.insert(key, t);
    return t;
}

fn ty_array(n: u32, elem: u32) -> u32 {
    for t, i in m_types {
        if i >= 16 && t.kind == TK_ARRAY && t.n == n && t.elems == elem { return i as! u32; }
    }
    let id = m_types.len as! u32;
    m_types.push(TypeDef { kind: TK_ARRAY, cls: C_MEM, bits: 0, size: n * tsize(elem), align: m_types[elem].align,
        store: n * tsize(elem), n: n, elems: elem });
    return id;
}

// ---------------------------------------------------------------- constants

fn c_new(lo: u64, hi: u64, t: u32, data: u32) -> u32 {
    let i = m_consts.len as! u32;
    m_consts.push(Const { lo: lo, hi: hi, ty: t, data: data });
    return KCONST | i;
}

// An integer constant of type t (INT class), truncated to its width.
fn c_int(v: u64, t: u32) -> u32 {
    let b = tbits(t);
    var x = v;
    if b < 64 { x = v & (((1 as u64) << (b as! u64)) - 1); }
    return c_new(x, 0, t, NONE);
}

fn c_i32(v: i64) -> u32 { c_int(v as! u64, GIR_T_I32) }
fn c_i64(v: i64) -> u32 { c_int(v as! u64, GIR_T_I64) }
fn c_i8(v: i64) -> u32 { c_int(v as! u64, GIR_T_I8) }
fn c_true() -> u32 { c_int(1, GIR_T_I1) }
fn c_false() -> u32 { c_int(0, GIR_T_I1) }
fn c_null() -> u32 { c_int(0, GIR_T_PTR) }

// An INT2 constant (lo, hi) truncated to the type's width.
fn c_wide(lo: u64, hi: u64, t: u32) -> u32 {
    let b = tbits(t);
    var h = hi;
    if b < 128 { h = hi & (((1 as u64) << ((b - 64) as! u64)) - 1); }
    return c_new(lo, h, t, NONE);
}

// Floating-point constants are deduplicated (the back-end pools them by index).
var fpc_keys = dictionary<u64, u32> {};

fn c_fp(lo: u64, hi: u64, t: u32) -> u32 {
    let key = lo ^ (hi * 0x9E3779B97F4A7C15) ^ ((t as u64) << 56);
    let r = fpc_keys.get(key);
    if r {
        let c = m_consts[r & 0x3FFFFFFF];
        if c.lo == lo && c.hi == hi && c.ty == t { return r; }
    }
    let v = c_new(lo, hi, t, NONE);
    fpc_keys.insert(key, v);
    return v;
}

fn c_zero(t: u32) -> u32 {
    let k = tcls(t);
    if k == C_INT { return c_int(0, t); }
    if k == C_INT2 { return c_new(0, 0, t, NONE); }
    if k == C_FP || k == C_X87 { return c_fp(0, 0, t); }
    return c_new(0, 0, t, NONE);
}

fn is_const(v: u32) -> bool { v != NONE && v >> 30 == 2 }
fn cidx(v: u32) -> u32 { v & 0x3FFFFFFF }
fn c_lo(v: u32) -> u64 { m_consts[v & 0x3FFFFFFF].lo }

// --------------------------------------------------------------- the strtab

fn add_name(s: const u8[:]) -> u32 {
    let off = m_strtab.len as! u32;
    m_strtab.append(s);
    m_strtab.push(0);
    return off;
}

fn new_global(name: const u8[:], kind: u32, flags: u32, align: u32) -> u32 {
    let off = add_name(name);
    let g = m_globals.len as! u32;
    m_globals.push(Global { name: off, name_len: name.len as! u32, kind: kind, flags: flags, data: 0, size: 0,
        align: align, func: NONE, section: NONE, aux: 0 });
    return g;
}

fn gref(g: u32) -> u32 { KGLOBAL | g }


fn get_section(name: const u8[:], flags: u32, typ: u32) -> u32 {
    let id = intern(name);
    let r = gmap.get(gk(GM_SECNAME, id));
    if r {
        m_sections[r].flags = m_sections[r].flags | flags;
        return r;
    }
    let off = add_name(name);
    let s = m_sections.len as! u32;
    m_sections.push(Section { name: off, name_len: name.len as! u32, flags: flags, typ: typ });
    gmap.insert(gk(GM_SECNAME, id), s);
    return s;
}

// ------------------------------------------------------------ instructions

var f_insts: Inst[>..<] = [];
var f_allocas: Inst[>..<] = [];
var f_ofix: u32[>..<] = [];     // positions in m_opnds holding local value refs
var f_bfix: u32[>..<] = [];     // positions in m_opnds holding block ids
// Per block id: the first local instruction (-1 = not started), and its
// position in the layout (fn_finish).
struct FBlock { start: i32, pos: u32 }
var f_blocks: FBlock[>..<] = [];
var f_border: u32[>..<] = [];   // block ids in layout order
var f_brelocs: u32[>..<] = [];  // m_drelocs entries whose blocks are ids of this function
var cur_blk: i64 = -1;          // the block being filled, -1 after a terminator
var cur_dbg: u32 = 0;

// Which of a, b, c are value refs (1, 2, 4) or block ids (8, 16, 32), per opcode.
let OPM: u8[83] = [
    1, 8, 49, 1, 0, 3, 3, 3,       // ret br condbr switch unreachable add sub mul
    3, 3, 3, 3, 3, 3, 3, 3,        // sdiv udiv srem urem and or xor shl
    3, 3, 3, 7, 1, 1, 1, 1,        // lshr ashr icmp select zext sext trunc ptrtoint
    1, 1, 0, 1, 3, 1, 1, 0,        // inttoptr bitcast alloca load store gep call phi
    3, 3, 3, 3, 1, 3, 1, 1,        // fadd fsub fmul fdiv fneg fcmp fpext fptrunc
    1, 1, 1, 1, 1, 3, 3, 7,        // fptosi fptoui sitofp uitofp extractvalue insertvalue extractelt insertelt
    3, 1, 0, 1, 1, 3, 3, 1,        // shuffle dynalloca stacksave stackrestore vastart memcpy memset ctlz
    1, 1, 1, 1, 7, 7, 3, 3,        // cttz ctpop bswap bitreverse fshl fshr ovf scmp
    3, 1, 3, 1, 1, 7, 3, 0,        // ucmp fabs copysign fsqrt isfpclass cmpxchg atomicrmw fence
    0, 0, 0, 1, 1, 0, 0, 1,        // tlsaddr frameaddr retaddr sjlj_setjmp sjlj_longjmp trap debugtrap indirectbr
    16, 3, 0,                      // blockaddr x86 asm
];

fn is_local(v: u32) -> bool { v >> 30 == 0 }

fn new_block() -> u32 {
    let id = f_blocks.len;
    f_blocks.push(FBlock { start: -1, pos: 0 });
    return id as! u32;
}

fn emit(op: i64, t: u32, sub: i64, flags: u32, aux: u32, a: u32, b: u32, c: u32) -> u32 {
    if cur_blk < 0 {
        // code after a terminator: a new block without predecessors
        let id = new_block();
        f_blocks[id].start = f_insts.len as! i32;
        f_border.push(id);
        cur_blk = id as i64;
    }
    let i = f_insts.len;
    f_insts.push(Inst { op: op as! u8, sub: sub as! u8, flags: flags as! u16, ty: t as! u16, aux: aux as! u16,
        a: a, b: b, c: c, dbg: cur_dbg });
    return i as! u32;
}

fn emit_term(op: i64, a: u32, b: u32, c: u32) {
    emit(op, GIR_T_VOID, 0, 0, 0, a, b, c);
    cur_blk = -1;
}

fn br(b: u32) { emit_term(GIR_BR, b, 0, 0); }
fn condbr(c: u32, t: u32, f: u32) { emit_term(GIR_CONDBR, c, t, f); }
fn has_insert() -> bool { cur_blk >= 0 }

// Starts block id; the current block (if not terminated) falls through.
fn start_block(id: u32) {
    if cur_blk >= 0 { br(id); }
    f_blocks[id].start = f_insts.len as! i32;
    f_border.push(id);
    cur_blk = id as i64;
}

fn alloca(size: i64, align: i64) -> u32 {
    let k = f_allocas.len;
    var al = align;
    if al < 1 { al = 1; }
    f_allocas.push(Inst { op: GIR_ALLOCA, sub: 0, flags: 0, ty: GIR_T_PTR, aux: 0, a: (if size < 1 { 1 } else { size }) as! u32,
        b: al as! u32, c: 0, dbg: 0 });
    return ATAG + (k as! u32);
}

// D3: a store at the top of the entry block, among the allocas (stores
// constant v of type t to alloca p; the flags of conditional cleanups).
fn entry_store(t: u32, v: u32, p: u32) {
    f_allocas.push(Inst { op: GIR_STORE, sub: 0, flags: 0, ty: GIR_T_VOID, aux: t as! u16, a: v, b: p, c: 0, dbg: 0 });
}

// Grows m_data by n zero bytes (M, the back-end's view, forbids resize).
let ZERO_PAGE: const u8[4096] = [0; 4096];
fn data_grow(n: i64) {
    var left = n;
    while left > 0 {
        let k = if left > 4096 { 4096 } else { left };
        m_data.append(ZERO_PAGE[..k]);
        left -= k;
    }
}

// Operand runs: op_imm for immediates, op_ref for value refs, op_blk for block ids.
fn op_imm(x: u32) { m_opnds.push(x); }
fn op_ref(v: u32) {
    if is_local(v) { f_ofix.push(m_opnds.len as! u32); }
    m_opnds.push(v);
}
fn op_blk(b: u32) {
    f_bfix.push(m_opnds.len as! u32);
    m_opnds.push(b);
}

// ------------------------------------------------------- function layout

fn fn_begin() {
    f_insts.clear();
    f_allocas.clear();
    f_ofix.clear();
    f_bfix.clear();
    f_blocks.clear();
    f_border.clear();
    f_brelocs.clear();
    cur_blk = -1;
    start_block(new_block());
}

fn remap(v: u32, first: u32, na: u32) -> u32 {
    if v >> 30 != 0 { return v; }
    if v >= ATAG { return first + (v - ATAG); }
    return first + na + v;
}

// G1: drops the function being lowered (its operand runs stay, unused).
fn fn_drop() {
    for r in f_brelocs { m_drelocs[r].blk = 0; }
    cur_blk = -1;
}

// Lays out the function and appends it to the module. Returns its index in m_funcs.
fn fn_finish(g: u32, flags: u32, nargs: u32, args: u32, ret_ty: u32, dbg: u32) -> u32 {
    if cur_blk >= 0 { emit_term(GIR_UNREACHABLE, 0, 0, 0); }
    // a block that was made but never started (a target nothing reached)
    for k in 0..f_blocks.len {
        if f_blocks[k].start < 0 {
            cur_blk = -1;
            start_block(k as! u32);
            emit_term(GIR_UNREACHABLE, 0, 0, 0);
        }
    }
    let first = m_insts.len as! u32;
    let na = f_allocas.len as! u32;
    for id, k in f_border { f_blocks[id].pos = k as! u32; }
    prefault_insts(m_insts, (f_allocas.len + f_insts.len) * 24);
    for I in f_allocas {
        if I.op == GIR_STORE {
            // D3: an entry-block store (the flag of a conditional C++ cleanup)
            var J = I;
            J.b = remap(I.b, first, na);
            m_insts.push(J);
        } else {
            m_insts.push(I);
        }
    }
    for I in f_insts {
        var J = I;
        let m: u32 = if I.op < 83 { OPM[I.op] } else { 0 };
        if m != 0 {
            if m & 1 != 0 { J.a = remap(I.a, first, na); }
            if m & 2 != 0 { J.b = remap(I.b, first, na); }
            if m & 4 != 0 { J.c = remap(I.c, first, na); }
            if m & 8 != 0 { J.a = f_blocks[I.a].pos; }
            if m & 16 != 0 { J.b = f_blocks[I.b].pos; }
            if m & 32 != 0 { J.c = f_blocks[I.c].pos; }
        }
        m_insts.push(J);
    }
    let first_block = m_blocks.len as! u32;
    let nb = f_border.len;
    for k in 0..nb {
        let s = f_blocks[f_border[k]].start as! u32;
        let e: u32 = if k + 1 < nb { f_blocks[f_border[k + 1]].start as! u32 } else { f_insts.len as! u32 };
        if k == 0 {
            m_blocks.push(Block { first_inst: first, n_inst: na + e - s });
        } else {
            m_blocks.push(Block { first_inst: first + na + s, n_inst: e - s });
        }
    }
    for p in f_ofix { m_opnds[p] = remap(m_opnds[p], first, na); }
    for p in f_bfix { m_opnds[p] = f_blocks[m_opnds[p]].pos; }
    for r in f_brelocs {
        m_drelocs[r].blk = f_blocks[m_drelocs[r].blk].pos;
        if m_drelocs[r].kind == DR_BLOCKDIFF32 { m_drelocs[r].blk2 = f_blocks[m_drelocs[r].blk2].pos; }
    }
    let fi = m_funcs.len as! u32;
    m_funcs.push(Func { global: g, flags: flags, first_block: first_block, n_blocks: nb as! u32, first_inst: first,
        n_inst: m_insts.len as! u32 - first, n_args: nargs, args: args, ret_ty: ret_ty, dbg: dbg });
    m_globals[g].func = fi;
    return fi;
}

// --------------------------------------------------------- value helpers

// The type of a value ref (during lowering).
fn vtype(v: u32) -> u32 {
    let k = v >> 30;
    if k == 0 {
        if v >= ATAG { return GIR_T_PTR; }
        return f_insts[v].ty as u32;
    }
    if k == 2 { return m_consts[v & 0x3FFFFFFF].ty; }
    if k == 3 { return GIR_T_PTR; }
    return arg_type(v & 0x3FFFFFFF);
}

var f_arg_types: u32[>..<] = [];   // GIR types of the current function's arguments
fn arg_type(i: u32) -> u32 { f_arg_types[i] }
