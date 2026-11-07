// goosecc B5: the DWARF debug information entries (-g): the GIR `dies` and
// `dattrs` tables (gir/gir.h), built from goosecc's own AST, types and
// lowering as tools/goovm-llc/gir_dwarf.cpp builds them from clang's debug
// metadata. That builder is a port of LLVM 20's DwarfDebug / DwarfUnit; this
// one is a port of the parts of it that run for C at -O0 without inlining,
// driven by a model of what clang's CGDebugInfo would have put in the
// metadata. The back-end resolves the GIR forms (code ranges, frame
// offsets, strings, files: backend-goose/DESIGN.md 12).
//
// Three layers:
//
// 1. Recording, while the lowering runs: per emitted function its
//    variables (a symbol, its address as a GIR value, its scope record),
//    labels and scope records (gen_debug.goose), and per emitted function
//    or file-scope variable a stream of events in lowering order:
//    references to globals, string literals, static locals, explicit
//    casts, enumerator references, variable declarations.
//
// 2. A replay of the events in the order clang emits the definitions
//    (eager external definitions in source order, tentative definitions at
//    the end of the unit, the deferred ones depth-first as CodeGenModule's
//    EmitDeferred), which gives the order of the unit's global variables,
//    of its functions (LLVM's module order), of its enum types and of its
//    retained types (explicit casts): the order LLVM's DwarfDebug walks
//    them, and so the order of the DIEs.
//
// 3. The DIE builder: metadata nodes for types (uniqued as LLVM uniques
//    metadata, so equal types share one DIE), and DIEs made as DwarfUnit
//    makes them: beginModule (the unit, globals, enums, retained types),
//    per function (the subprogram, its lexical scopes from the
//    instructions' locations as LexicalScopes, variables and labels),
//    endModule (subprogram attributes, then variable attributes, which is
//    when most types are first referenced).

namespace gen;

import std;
import dictionary;
import .common;
import .types;
import .ast;
import .dtype;

// ------------------------------------------------------------ DWARF codes

let DWT_array_type = 0x01;
let DWT_enumeration_type = 0x04;
let DWT_formal_parameter = 0x05;
let DWT_label = 0x0a;
let DWT_lexical_block = 0x0b;
let DWT_member = 0x0d;
let DWT_pointer_type = 0x0f;
let DWT_compile_unit = 0x11;
let DWT_structure_type = 0x13;
let DWT_subroutine_type = 0x15;
let DWT_typedef = 0x16;
let DWT_union_type = 0x17;
let DWT_unspecified_parameters = 0x18;
let DWT_subrange_type = 0x21;
let DWT_base_type = 0x24;
let DWT_const_type = 0x26;
let DWT_enumerator = 0x28;
let DWT_subprogram = 0x2e;
let DWT_variable = 0x34;
let DWT_volatile_type = 0x35;
let DWT_restrict_type = 0x37;
let DWT_atomic_type = 0x47;
let DWT_imported_declaration = 0x08;

let DWA_location = 0x02;
let DWA_name = 0x03;
let DWA_byte_size = 0x0b;
let DWA_bit_size = 0x0d;
let DWA_stmt_list = 0x10;
let DWA_low_pc = 0x11;
let DWA_language = 0x13;
let DWA_comp_dir = 0x1b;
let DWA_const_value = 0x1c;
let DWA_producer = 0x25;
let DWA_prototyped = 0x27;
let DWA_artificial = 0x34;
let DWA_count = 0x37;
let DWA_data_member_location = 0x38;
let DWA_decl_file = 0x3a;
let DWA_decl_line = 0x3b;
let DWA_declaration = 0x3c;
let DWA_encoding = 0x3e;
let DWA_external = 0x3f;
let DWA_frame_base = 0x40;
let DWA_type = 0x49;
let DWA_data_bit_offset = 0x6b;
let DWA_linkage_name = 0x6e;
let DWA_str_offsets_base = 0x72;
let DWA_addr_base = 0x73;
let DWA_noreturn = 0x87;
let DWA_alignment = 0x88;
let DWA_GNU_vector = 0x2107;
let DWA_import = 0x18;

let DWF_data1 = 0x0b;
let DWF_data2 = 0x05;
let DWF_data4 = 0x06;
let DWF_data8 = 0x07;
let DWF_sdata = 0x0d;
let DWF_udata = 0x0f;
let DWF_ref4 = 0x13;
let DWF_flag_present = 0x19;

let ATE_boolean = 0x02;
let ATE_complex_float = 0x03;
let ATE_float = 0x04;
let ATE_signed = 0x05;
let ATE_signed_char = 0x06;
let ATE_unsigned = 0x07;
let ATE_unsigned_char = 0x08;
let ATE_lo_user = 0x80;

// GIR attribute forms (gir.h GIR_DF_*)
let GDF_STR = 0x7F01;
let GDF_FILE = 0x7F02;
let GDF_PC = 0x7F03;
let GDF_SCOPE_PC = 0x7F04;
let GDF_FRAME_BASE = 0x7F05;
let GDF_LOCAL = 0x7F06;
let GDF_GLOBAL = 0x7F07;
let GDF_STMT_LIST = 0x7F08;
let GDF_STR_BASE = 0x7F09;
let GDF_CU_PC = 0x7F0A;
let GDF_ADDR_BASE = 0x7F0B;
let GDF_LABEL = 0x7F0C;

// ============================================================ 1. recording

// A variable or parameter of the function being lowered.
struct DVar { sym: i64, addr: u32, rec: u32, argno: u32, flags: u32, n: u32, dq: u32 }
let DV_MF = 1;        // the address is a static alloca (LLVM's MachineFunction side table: collected first)
let DV_VLAEXPR = 2;   // clang's artificial __vla_exprN (n = N): a VLA dimension's element count
let DV_VLA = 4;       // a VLA: n = its first dimension in vd_var / vd_const
var f_dvars: DVar[>..<] = [];
// A label: its block (a local block id), its scope record, where it is.
struct DLab { sym: i64, blk: u32, rec: u32, loc: u32 }
var f_dlabs: DLab[>..<] = [];
var f_vlaexpr: u32 = 0;              // clang's VLAExprCounter
var f_vd0: i64 = 0;
// VLA dimensions, one entry per TY_VLA level from the outside in: the DVar
// of its __vla_exprN (module index), or NONE and the constant count.
var vd_var: u32[>..] = [];
var vd_const: u64[>..] = [];

// The emitted functions and their variables, labels and scope records
// (addresses and positions in module terms).
var m_dvars: DVar[>..] = [];
var m_dlabs: DLab[>..] = [];         // blk: the module index of the label's instruction
var m_srecs: DScopeRec[>..] = [];
struct DFn { sym: i64, fi: u32, v0: u32, v1: u32, l0: u32, l1: u32, r0: u32, r1: u32, e0: u32, e1: u32, nodebug: bool }
var m_dfns: DFn[>..] = [];
// The emitted file-scope variable definitions.
struct DGVar { sym: i64, g: u32, e0: u32, e1: u32 }
var m_dgvars: DGVar[>..] = [];

// Events, in lowering order.
struct DEv { kind: u32, a: u32, b: u32 }
let EV_REF = 1;       // a = global: a reference (clang: GetOrCreateLLVMGlobal/Function)
let EV_STR = 2;       // a = string literal global, b = location (AddStringLiteralDebugInfo)
let EV_STATIC = 3;    // a = static local symbol, defined here (EmitStaticVarDecl)
let EV_CAST = 4;      // a = written type of an explicit cast (EmitExplicitCastExprType)
let EV_ENUM = 5;      // a = enum: an enumerator was referenced (EmitDeclRefExprDbgValue)
let EV_VAR = 6;       // a = m_dvars index (local): a variable's declaration (its type)
let EV_CVAL = 7;      // a = file-scope variable whose read clang folded (EmitDeclRefExprDbgValue)
let EV_REFSYM = 8;    // a = function symbol: a reference of a call expanded in place (G1)
var m_devs: DEv[>..] = [];
var ev_on = false;
var ev_noproto = false;              // the next EV_REF is of a function through a type without prototype

// A reference to a function (callee c: through casts to its declaration):
// clang makes the function's llvm::Function with the declaration's type,
// and a type without prototype is variadic there, so the definition then
// makes a new one (at the end of the module: CodeGenModule's replacement
// of functions without prototype). A reference after a K&R definition has
// a type without prototype (DR 316) but its declaration has one.
fn dbg_fnref(c: u32) {
    var n = c;
    loop {
        let nd = nodes[n];
        if (nd.kind == N_ICAST || nd.kind == N_CAST || (nd.kind == N_UNARY && (nd.op == U_ADDR || nd.op == U_EXTENSION))) && nd.a != 0 {
            // ((long (*)(int))f)(x): clang visits the cast
            if nd.kind == N_CAST && !dbg_no_enum { dev(EV_CAST, node_written(n), 0); }
            n = nd.a;
            continue;
        }
        break;
    }
    if nkind(n) != N_DECLREF { return; }
    ev_noproto = (types[nodes[n].ty >> 4].flags as i64) & TF_NOPROTO != 0 && !is_krref(n);
}

// A read of file-scope const variable s folded to bits (has: a value of 64
// bits or less, which the DIE holds): clang gives a variable that need not
// be emitted (internal, not used) a DIE with DW_AT_const_value instead.
var cval_bits = dictionary<u64, u64> {};
fn cv_note(s: i64, bits: u64, has: bool) {
    if !opt_debug || !ev_on || dbg_dead != 0 { return; }
    if syms[s].flags & SF_FILESCOPE == 0 || !is_internal_sym(s) || sym_has_attr(s, AM_USED) { return; }
    if !cval_bits.contains(s as u64) {
        if has { cval_bits.insert(s as u64, bits); } else { cval_bits.insert(s as u64, 0xFFFFFFFFFFFFFFFF); cval_none.insert(s as u64, 1); }
    }
    dev(EV_CVAL, s as! u32, 0);
}
var cval_none = dictionary<u64, u32> {};
var cval_die = dictionary<u64, u32> {};    // file-scope variable -> 1 once it has a DIE from a folded read

fn dev(kind: u32, a: u32, b: u32) {
    if !ev_on || dbg_dead != 0 { return; }
    // a nodebug function records what CodeGenModule does only
    if dbg_nodebug && kind != EV_REF && kind != EV_STR && kind != EV_CAST && kind != EV_REFSYM { return; }
    m_devs.push(DEv { kind: kind, a: a, b: b });
}

// Moves the events [m0, m1) after the ones recorded since m1 (the lowering
// visited two operands in the other order than clang).
var rot_tmp: DEv[>..] = [];
fn dbg_rotate_events(m0: i64, m1: i64) {
    rot_tmp.clear();
    for k in m0..m1 { rot_tmp.push(m_devs[k]); }
    let n2 = m_devs.len - m1;
    for k in 0..n2 { m_devs[m0 + k] = m_devs[m1 + k]; }
    for k in 0..rot_tmp.len { m_devs[m0 + n2 + k] = rot_tmp[k]; }
}

// > 0 while the lowering emits code that clang's CodeGen leaves out: the
// condition of an if or ?: that clang constant-folds (ConstantFoldsTo-
// SimpleInteger accepts 0 && x, 1 || x, &global, which goosecc's lowering
// does not fold) and the arm that does not run. The code is the same
// either way; the debug information records nothing of it.
var dbg_dead: i32 = 0;
// Set where clang has no insertion point but goosecc goes on: after an if
// whose arms both end in a jump, clang deletes the empty end block, and
// the statements up to the next label are not emitted (EmitStmt); goosecc
// lowers them into a block without predecessors, which dbg_dead keeps out
// of the debug information.
var dbg_noins = false;
// Does clang fold condition c (and leave out the other arm, which has no
// label)? Only asked where goosecc's const_bool did not fold it.
fn clang_folds(c: u32, then_arm: u32, else_arm: u32) -> bool, bool {
    if !dbg_on() { return false, false; }
    let ok, v = fold_bool(c);
    if !ok { return false, false; }
    let dead = if v { else_arm } else { then_arm };
    if dead != 0 && contains_label(dead) { return false, false; }
    return true, v;
}

fn dbg_fn_begin() {
    if !opt_debug { return; }
    f_dvars.clear();
    f_dlabs.clear();
    f_vlaexpr = 0;
    f_vd0 = vd_var.len;
    ev_on = true;
    dbg_noins = false;
    dfn_e0 = m_devs.len as! u32;
}
var dfn_e0: u32 = 0;

// A parameter (argno from 1) at addr (an alloca, or the byval argument).
fn dbg_param(p: i64, addr: u32, argno: u32) {
    if !opt_debug || dbg_nodebug { return; }
    // a byval argument has a fixed frame index in LLVM (an MF variable too)
    let mf = (addr >> 30 == 0 && addr >= ATAG) || addr & 0xC0000000 == KARG;
    dev(EV_VAR, f_dvars.len as! u32, 0);
    f_dvars.push(DVar { sym: p, addr: addr, rec: 0, argno: argno, flags: if mf { DV_MF } else { 0 }, n: 0, dq: 0 });
}

// A local variable at addr (a static alloca).
fn dbg_local(s: i64, addr: u32) {
    if !opt_debug || dbg_nodebug { return; }
    let mf = addr >> 30 == 0 && addr >= ATAG;
    dev(EV_VAR, f_dvars.len as! u32, 0);
    f_dvars.push(DVar { sym: s, addr: addr, rec: dbg_cur_rec(), argno: 0, flags: if mf { DV_MF } else { 0 }, n: 0, dq: 0 });
}

// A VLA at p (a dynamic alloca) of type q, as clang's
// EmitAndRegisterVariableArrayDimensions: the element count of each VLA
// level goes to an artificial 8-byte variable __vla_exprN, stored right
// after the allocation, which the subranges of the array's type name.
fn dbg_vla(s: i64, p: u32, q: u32) {
    if !opt_debug || dbg_nodebug { return; }
    let first = vd_var.len as! u32;
    var t = q;
    ensure_vla_table();
    while kind_of(t) == TY_VLA {
        let n = vla_size[t >> 4];
        if n == NONE || is_const(n) {
            vd_var.push(NONE);
            vd_const.push(if n == NONE { 0 } else { c_lo(n) });
        } else {
            let slot = alloca(8, 8);
            ins_store(GIR_T_I64, n, slot, false);
            let k = f_dvars.len as! u32;
            dev(EV_VAR, k, 0);
            f_dvars.push(DVar { sym: -1, addr: slot, rec: dbg_cur_rec(), argno: 0, flags: DV_MF | DV_VLAEXPR, n: f_vlaexpr, dq: t_ulong });
            f_vlaexpr++;
            vd_var.push(k);
            vd_const.push(0);
        }
        t = tbase(t);
    }
    dev(EV_VAR, f_dvars.len as! u32, 0);
    f_dvars.push(DVar { sym: s, addr: p, rec: dbg_cur_rec(), argno: 0, flags: DV_VLA, n: first, dq: 0 });
}

fn dbg_label(l: i64, blk: u32, loc: u32) {
    if !opt_debug || dbg_nodebug { return; }
    f_dlabs.push(DLab { sym: l, blk: blk, rec: dbg_cur_rec(), loc: loc });
}

// After fn_finish: the function's records in module terms.
fn dbg_fn_end(s: i64, fi: u32) {
    if !opt_debug { return; }
    ev_on = false;
    if fi == NONE {
        // a dropped function (always_inline, expanded wherever called):
        // its events only
        m_dfns.push(DFn { sym: s, fi: fi, v0: m_dvars.len as! u32, v1: m_dvars.len as! u32, l0: m_dlabs.len as! u32,
            l1: m_dlabs.len as! u32, r0: m_srecs.len as! u32, r1: m_srecs.len as! u32, e0: dfn_e0, e1: m_devs.len as! u32,
            nodebug: true });
        return;
    }
    let F = m_funcs[fi];
    let first = F.first_inst;
    let na = f_allocas.len as! u32;
    let v0 = m_dvars.len as! u32;
    for V in f_dvars {
        var W = V;
        W.addr = remap(V.addr, first, na);
        m_dvars.push(W);
    }
    for k in f_vd0..vd_var.len { if vd_var[k] != NONE { vd_var[k] = vd_var[k] + v0; } }
    let l0 = m_dlabs.len as! u32;
    for L in f_dlabs {
        var M = L;
        M.blk = first + na + (f_blocks[L.blk].start as! u32);
        m_dlabs.push(M);
    }
    let r0 = m_srecs.len as! u32;
    for R in f_srecs { m_srecs.push(R); }
    // EV_VAR events name the function's own variables: make them module indices
    for k in dfn_e0..m_devs.len as! u32 { if m_devs[k].kind == EV_VAR { m_devs[k].a = m_devs[k].a + v0; } }
    m_dfns.push(DFn { sym: s, fi: fi, v0: v0, v1: m_dvars.len as! u32, l0: l0, l1: m_dlabs.len as! u32, r0: r0,
        r1: m_srecs.len as! u32, e0: dfn_e0, e1: m_devs.len as! u32, nodebug: dbg_nodebug });
}

// A file-scope variable definition (emit_var); its initializer's events.
fn dbg_gvar_begin() -> u32 {
    if !opt_debug { return 0; }
    ev_on = true;
    return m_devs.len as! u32;
}
fn dbg_gvar_end(s: i64, g: u32, e0: u32) {
    if !opt_debug { return; }
    ev_on = false;
    m_dgvars.push(DGVar { sym: s, g: g, e0: e0, e1: m_devs.len as! u32 });
}

// The explicit casts of a static initializer, in the order clang's
// ConstExprEmitter visits them.
// clang's ConstExprEmitter visits an initializer through initializer
// lists, compound literals, __extension__ and the casts it can emit (no-op,
// atomic, null to pointer, to union, integral from an integer); the rest
// it leaves to the evaluator, which visits no cast. Each explicit cast it
// visits retains its type (EmitExplicitCastExprType), whatever its kind.
recursive fn dbg_init_casts(n: u32) {
    if n == 0 || !opt_debug || !ev_on { return; }
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_CAST || k == N_ICAST {
        if k == N_CAST { dev(EV_CAST, node_written(n), 0); }
        let ck = nd.op as i64;
        if ck == CK_NOOP || ck == CK_ATOMIC || ck == CK_NULL2PTR || ck == CK_TOUNION { dbg_init_casts(nd.a); }
        else if ck == CK_INTEGRAL && is_integer(nty(nd.a)) { dbg_init_casts(nd.a); }
        else if ck == CK_LVAL2RVAL && nkind(nd.a) == N_COMPLIT { dbg_init_casts(nodes[nd.a].a); }
        return;
    }
    if k == N_UNARY && nd.op == U_EXTENSION { dbg_init_casts(nd.a); return; }
    if k == N_COMPLIT { dbg_init_casts(nd.a); return; }
    if k == N_INITLIST {
        for i in nd.c { dbg_init_casts(nlist[nd.v + i]); }
        return;
    }
}


// An enumerator constant visited by the lowering (ex_val).
fn dbg_enumc(n: u32) {
    if dbg_no_enum { return; }
    let s = enumc_of(n);
    if s < 0 { return; }
    let e = enumc_owner(s);
    if e >= 0 { dev(EV_ENUM, e as! u32, 0); }
}
// The same for an expression the lowering folds but clang's CodeGen
// visits (a memory order).
fn dbg_enum_expr(n0: u32) {
    var n = n0;
    while nkind(n) == N_ICAST { n = nodes[n].a; }
    dbg_enumc(n);
}
// Set while clang would emit an initializer as a constant (a local
// aggregate with a constant initializer: EmitAutoVarInit's
// IsConstantAggregate), without visiting its expressions.
var dbg_no_enum = false;

// ============================================================ 2. clang's order

// Per symbol: its DFn or DGVar (+1; 0 none), whether clang would have made
// its llvm::GlobalValue yet, seen its definition, queued it, emitted it.
var ent_fn = dictionary<u64, u32> {};
var ent_var = dictionary<u64, u32> {};
let ES_CREATED: u8 = 1;
let ES_SEEN: u8 = 2;
let ES_QUEUED: u8 = 4;
let ES_EMITTED: u8 = 8;
let ES_NOPROTO: u8 = 16;             // its llvm::Function so far has the variadic type of a reference without prototype
var es_fn: u8[>..] = [];             // per DFn
var es_var: u8[>..] = [];            // per DGVar
var o_fns: u32[>..] = [];            // DFn indices in LLVM module order
// The unit's global variables in order: kind 1 a DGVar, 2 a static local
// symbol, 3 a string literal global (b = its location).
struct OGlob { kind: u32, a: i64, b: u32 }
var o_globs: OGlob[>..] = [];
var str_done = dictionary<u64, u32> {};
var o_retained: u32[>..] = [];       // metadata of explicit casts
var o_queue: u32[>..] = [];          // DeferredDeclsToEmit: DFn index, or DGVar index | 0x80000000

fn ent_of_global(g: u32) -> i64, bool {
    ensure_glob_tables();
    if g >= glob_gen.len as! u32 { return -1, false; }
    let s = glob_gen[g].sym;
    if s < 0 { return -1, false; }
    let f = ent_fn.get(s as u64);
    if f { return f as i64, true; }
    let v = ent_var.get(s as u64);
    if v { return v as i64, false; }
    return -1, false;
}

fn sim_reference(g: u32, noproto: bool) {
    let e, is_fn = ent_of_global(g);
    sim_reference_ent(e, is_fn, noproto);
}

fn sim_reference_ent(e: i64, is_fn: bool, noproto: bool) {
    if e < 0 { return; }
    if is_fn {
        if es_fn[e] & (ES_CREATED | ES_NOPROTO) == 0 {
            if noproto && es_fn[e] & ES_EMITTED == 0 {
                es_fn[e] = es_fn[e] | ES_NOPROTO;
            } else {
                es_fn[e] = es_fn[e] | ES_CREATED;
                o_fns.push(e as! u32);
            }
        }
        if es_fn[e] & (ES_SEEN | ES_QUEUED | ES_EMITTED) == ES_SEEN {
            es_fn[e] = es_fn[e] | ES_QUEUED;
            o_queue.push(e as! u32);
        }
    } else {
        es_var[e] = es_var[e] | ES_CREATED;
        if es_var[e] & (ES_SEEN | ES_QUEUED | ES_EMITTED) == ES_SEEN {
            es_var[e] = es_var[e] | ES_QUEUED;
            o_queue.push((e as! u32) | 0x80000000);
        }
    }
}

// The definition of entity x (a DFn, or a DGVar with the high bit) was seen
// but is emitted on use.
fn sim_defer(x: u32) {
    if x & 0x80000000 != 0 {
        let e = (x & 0x7FFFFFFF) as i64;
        es_var[e] = es_var[e] | ES_SEEN;
        if es_var[e] & (ES_CREATED | ES_QUEUED | ES_EMITTED) == ES_CREATED {
            es_var[e] = es_var[e] | ES_QUEUED;
            o_queue.push(x);
        }
    } else {
        let e = x as i64;
        es_fn[e] = es_fn[e] | ES_SEEN;
        if es_fn[e] & (ES_CREATED | ES_NOPROTO) != 0 && es_fn[e] & (ES_QUEUED | ES_EMITTED) == 0 {
            es_fn[e] = es_fn[e] | ES_QUEUED;
            o_queue.push(x);
        }
    }
}

fn sim_events(e0: u32, e1: u32) {
    for k in e0..e1 {
        let E = m_devs[k];
        if E.kind == EV_REF { sim_reference(E.a, E.b != 0); }
        else if E.kind == EV_REFSYM {
            let f = ent_fn.get(E.a as u64);
            if f { sim_reference_ent(f as i64, true, false); }
        }
        else if E.kind == EV_STR {
            if !str_done.get(E.a as u64) {
                str_done.insert(E.a as u64, 1);
                o_globs.push(OGlob { kind: 3, a: E.a as i64, b: E.b });
            }
        } else if E.kind == EV_STATIC {
            o_globs.push(OGlob { kind: 2, a: E.a as i64, b: 0 });
            sim_cur = syms[E.a].loc;
            walk_md(md_of(var_written(E.a as i64)));
        } else if E.kind == EV_CAST {
            let m = md_of(E.a);
            if m != 0 { o_retained.push(m); walk_md(m); }
        } else if E.kind == EV_ENUM {
            walk_md(md_intern(MD_ENUM, E.a, 0, 0));
        } else if E.kind == EV_CVAL {
            // CGDebugInfo::EmitGlobalVariable(VD, Init): once per variable,
            // unless it has its DIE already
            let s = E.a as i64;
            if !cval_die.contains(s as u64) && !cv_has_die(s) {
                cval_die.insert(s as u64, 1);
                o_globs.push(OGlob { kind: 4, a: s, b: 0 });
                walk_md(md_of(var_written(s)));
            }
        } else if E.kind == EV_VAR {
            // a local's declaration sets CurLoc (a parameter's does not)
            let V = m_dvars[E.a];
            if V.argno == 0 && V.sym >= 0 { sim_cur = syms[V.sym].loc; }
            walk_md(md_of(dvar_written(E.a as i64)));
        }
    }
}

fn sim_emit(x: u32) {
    if x & 0x80000000 != 0 {
        let e = (x & 0x7FFFFFFF) as i64;
        if es_var[e] & ES_EMITTED != 0 { return; }
        es_var[e] = es_var[e] | ES_EMITTED | ES_CREATED;
        let V = m_dgvars[e];
        sim_events(V.e0, V.e1);
        // a variable a folded read gave its DIE keeps it (G1)
        if cval_die.contains(V.sym as u64) { return; }
        o_globs.push(OGlob { kind: 1, a: e, b: 0 });
        sim_cur = var_loc(V.sym);
        walk_md(md_of(var_written(V.sym)));
        return;
    }
    let e = x as i64;
    if es_fn[e] & ES_EMITTED != 0 { return; }
    let F = m_dfns[e];
    // the definition makes its llvm::Function, a new one if references
    // without prototype made a variadic one
    if es_fn[e] & ES_CREATED == 0 {
        es_fn[e] = es_fn[e] | ES_CREATED;
        o_fns.push(e as! u32);
    }
    if F.fi != NONE { sim_reference(m_funcs[F.fi].global, false); }
    es_fn[e] = es_fn[e] | ES_EMITTED;
    if F.nodebug { sim_events(F.e0, F.e1); return; }
    // the subroutine type: the return type and the parameters' types
    walk_md(md_of(fn_ret_written(F.sym)));
    sim_events(F.e0, F.e1);
    // FinishFunction leaves CurLoc at the body's '}'
    let def = syms[F.sym].def;
    if def >= 0 && nodes[nodes[def].b].b != 0 { sim_cur = nodes[nodes[def].b].b; }
}

// clang's CGDebugInfo::CurLoc as the replay goes: a member without a
// location (the implicit struct __va_list_tag's) gets its line.
var sim_cur: u32 = 0;
var va_loc: u32 = 0xFFFFFFFF;        // CurLoc when clang first made struct __va_list_tag

// clang's EmitDeferred: what the emitted definitions queued, depth first.
var dq_stack: u32[>..] = [];
fn sim_deferred() {
    // a stack of (queue run start, position, end) triples over dq_items
    var items: u32[>..] = [];
    for x in o_queue { items.push(x); }
    o_queue.clear();
    dq_stack.clear();
    dq_stack.push(0);
    dq_stack.push(0);
    dq_stack.push(items.len as! u32);
    while dq_stack.len > 0 {
        let t = dq_stack.len - 3;
        let pos = dq_stack[t + 1];
        let end = dq_stack[t + 2];
        if pos >= end {
            dq_stack.resize(t);
            continue;
        }
        dq_stack[t + 1] = pos + 1;
        sim_emit(items[pos]);
        if o_queue.len > 0 {
            let s0 = items.len as! u32;
            for x in o_queue { items.push(x); }
            o_queue.clear();
            dq_stack.push(s0);
            dq_stack.push(s0);
            dq_stack.push(items.len as! u32);
        }
    }
}

// clang's EmitGlobalAlias: an alias of a variable is an imported
// declaration of that variable (of its definition's DIE, once emitted).
struct OImp { sym: i64, target: i64 }
var o_imports: OImp[>..] = [];
fn sim_alias(s: i64) {
    let a = syms[s].attr;
    if a == 0 || sym_attrs[a].alias_len == 0 { return; }
    let off = sym_attrs[a].alias_off as i64;
    let tid = intern(strbytes[off..off + sym_attrs[a].alias_len]);
    let r = gmap.get(gk(GM_NAMEGLOB, tid));
    if !r { return; }
    let e, is_fn = ent_of_global(r);
    if e < 0 || is_fn { return; }
    o_imports.push(OImp { sym: s, target: m_dgvars[e].sym });
}

// Is function s emitted when its definition is seen (MustBeEmitted)?
fn fn_eager(s: i64) -> bool {
    return (!is_internal_sym(s) && !fn_local_inline(s)) || sym_has_attr(s, AM_USED) || sym_has_attr(s, AM_CTOR) ||
        sym_has_attr(s, AM_DTOR);
}

// Has file-scope variable s got its DIE (an emitted definition's)?
fn cv_has_die(s: i64) -> bool {
    let v = ent_var.get(s as u64);
    if v { return es_var[v] & ES_EMITTED != 0; }
    return false;
}

fn sim_run() {
    for F, i in m_dfns { ent_fn.insert(F.sym as u64, i as! u32); es_fn.push(0); }
    for V, i in m_dgvars { ent_var.insert(V.sym as u64, i as! u32); es_var.push(0); }
    let tu = nodes[tu_node];
    var tent: u32[>..] = [];
    for i in tu.c as i64 {
        let it = nlist[tu.v + i];
        let nd = nodes[it];
        if nd.kind == N_FUNCDEF {
            let r = ent_fn.get(nd.a as u64);
            if !r { continue; }
            let e = r;
            if m_dfns[e].sym != nd.a as i64 { continue; }
            if fn_eager(nd.a as i64) { sim_emit(e); } else { sim_defer(e); }
        } else if nd.kind == N_DECL {
            let s = nd.a as i64;
            if syms[s].kind != SK_VAR || syms[s].flags & SF_FILESCOPE == 0 { continue; }
            sim_alias(s);
            let r = ent_var.get(s as u64);
            if !r { continue; }
            let e = r;
            if nd.b != 0 {
                if !is_internal_sym(s) || sym_has_attr(s, AM_USED) { sim_emit(e | 0x80000000); }
                else { sim_defer(e | 0x80000000); }
            } else if syms[s].flags & SF_DEFINED == 0 && !decl_is_extern(it) {
                var have = false;
                for x in tent { if x == e { have = true; } }
                if !have { tent.push(e); }
            }
        }
    }
    // the tentative definitions (Sema's ActOnEndOfTranslationUnit)
    for e in tent {
        let s = m_dgvars[e].sym;
        if es_var[e] & ES_EMITTED != 0 { continue; }
        if !is_internal_sym(s) || es_var[e] & ES_CREATED != 0 { sim_emit(e | 0x80000000); }
        else { sim_defer(e | 0x80000000); }
    }
    sim_deferred();
    // what goosecc emitted that the model did not reach (in its own order)
    for i in m_dfns.len { if es_fn[i] & ES_EMITTED == 0 { sim_emit(i as! u32); sim_deferred(); } }
    for i in m_dgvars.len { if es_var[i] & ES_EMITTED == 0 { sim_emit((i as! u32) | 0x80000000); sim_deferred(); } }
}

// ============================================================ metadata

// The debug types, as clang's CGDebugInfo makes them and LLVM uniques
// them: structurally (pointer to X, const X, an array of X with these
// counts, a function type with these types), except records, enums and
// typedefs, which are distinct per declaration.
let MD_BASE = 1;      // a = encoding, b = byte size, c = name (dstr offset)
let MD_PTR = 2;       // a = pointee (0: void)
let MD_CONST = 3;     // a = base
let MD_VOLATILE = 4;
let MD_RESTRICT = 5;
let MD_ATOMIC = 6;
let MD_TYPEDEF = 7;   // a = the typedef symbol
let MD_ARRAY = 8;     // a = element, b, c = md_run of counts (CNT_*)
let MD_FUNC = 9;      // a = 1 if variadic, b, c = md_run: return type (0: void), parameter types
let MD_REC = 10;      // a = record
let MD_ENUM = 11;     // a = enum
let MD_VECTOR = 12;   // a = element, b = lanes, c = byte size
let MD_NOPROTO = 13;  // a function type without prototype: a = return type
struct Md { kind: u32, a: u32, b: u32, c: u32 }
var mds: Md[>..] = [];
var md_run: u64[>..] = [];
var md_tab = dictionary<u64, u32> {};
var md_rmark: i64 = 0;
// Array counts: CNT_NONE (unknown: no DW_AT_count), a constant + 1, or a
// variable (CNT_VAR | m_dvars index).
let CNT_NONE: u64 = 0;
let CNT_VAR: u64 = 0x8000000000000000;

fn md_hash(kind: u32, a: u32, b: u32, c: u32) -> u64 {
    var h: u64 = (kind as u64) * 0x9E3779B97F4A7C15;
    h = (h ^ (a as u64)) * 0x100000001B3;
    h = (h ^ (b as u64)) * 0x100000001B3;
    h = (h ^ (c as u64)) * 0x100000001B3;
    return h ^ (h >> 31);
}

fn md_intern(kind: u32, a: u32, b: u32, c: u32) -> u32 {
    if mds.len == 0 { mds.push(Md { kind: 0, a: 0, b: 0, c: 0 }); }
    var key = md_hash(kind, a, b, c);
    loop {
        let r = md_tab.get(key);
        if !r { break; }
        let m = mds[r];
        if m.kind == kind && m.a == a && m.b == b && m.c == c { return r; }
        key = key + 1;
    }
    let id = mds.len as! u32;
    mds.push(Md { kind: kind, a: a, b: b, c: c });
    md_tab.insert(key, id);
    return id;
}

// A node with a run (md_run[md_rmark ..]): interned by its contents.
fn md_intern_run(kind: u32, a: u32) -> u32 {
    if mds.len == 0 { mds.push(Md { kind: 0, a: 0, b: 0, c: 0 }); }
    let n = md_run.len - md_rmark;
    var h: u64 = md_hash(kind, a, n as! u32, 0);
    for k in md_rmark..md_run.len { h = (h ^ md_run[k]) * 0x100000001B3; }
    var key = h ^ (h >> 29);
    loop {
        let r = md_tab.get(key);
        if !r { break; }
        let m = mds[r];
        if m.kind == kind && m.a == a && m.c as i64 == n {
            var same = true;
            for k in 0..n { if md_run[m.b as i64 + k] != md_run[md_rmark + k] { same = false; break; } }
            if same {
                md_run.resize(md_rmark);
                return r;
            }
        }
        key = key + 1;
    }
    let id = mds.len as! u32;
    mds.push(Md { kind: kind, a: a, b: md_rmark as! u32, c: n as! u32 });
    md_tab.insert(key, id);
    return id;
}

// The qualifiers of a type as DWARF nests them (clang's
// CreateQualifiedType: const outermost, then volatile, restrict; an
// _Atomic type is the innermost).
fn md_quals(m0: u32, q: i64) -> u32 {
    var m = m0;
    if q & Q_ATOMIC != 0 { m = md_intern(MD_ATOMIC, m, 0, 0); }
    if q & Q_RESTRICT != 0 { m = md_intern(MD_RESTRICT, m, 0, 0); }
    if q & Q_VOLATILE != 0 { m = md_intern(MD_VOLATILE, m, 0, 0); }
    if q & Q_CONST != 0 { m = md_intern(MD_CONST, m, 0, 0); }
    return m;
}

fn base_md(name: const u8[:], enc: u32, size: i64) -> u32 {
    return md_intern(MD_BASE, enc, size as! u32, dstring(name));
}

// The metadata of a written type (dtype.goose) or a canonical type.
recursive fn md_of(d: u32) -> u32 {
    if d == 0 { return 0; }
    if dq_sugar(d) {
        let q = dq_quals(d);
        let t = dtypes[dq_node(d)];
        let k = t.kind as i64;
        var m: u32 = 0;
        if k == DK_TYPEDEF { m = md_intern(MD_TYPEDEF, t.sym, 0, 0); }
        else if k == DK_PTR { m = md_intern(MD_PTR, md_of(t.base), 0, 0); }
        else if k == DK_ARRAY || k == DK_VLA { m = md_array(d & 0xFFFFFFF0); }
        else if k == DK_FUNC { m = md_func_d(d & 0xFFFFFFF0); }
        else if k == DK_VECTOR {
            let vt = types[t.canon >> 4];
            m = md_intern(MD_VECTOR, md_of(t.base), vt.n as! u32, type_size(t.canon) as! u32);
        }
        return md_quals(m, q);
    }
    let c = tcanon(d);
    let q = quals(c);
    let ty = types[c >> 4];
    let k = ty.kind as i64;
    if k == TY_VOID { return md_quals(0, q); }
    var m: u32 = 0;
    if k == TY_POINTER { m = md_intern(MD_PTR, md_of(ty.base), 0, 0); }
    else if k == TY_ARRAY || k == TY_VLA { m = md_array(unqual(c)); }
    else if k == TY_FUNC { m = md_func_c(unqual(c)); }
    else if k == TY_STRUCT || k == TY_UNION { m = md_intern(MD_REC, ty.extra, 0, 0); }
    else if k == TY_ENUM { m = md_intern(MD_ENUM, ty.extra, 0, 0); }
    else if k == TY_VECTOR || k == TY_EXTVECTOR {
        m = md_intern(MD_VECTOR, md_of(ty.base), ty.n as! u32, type_size(unqual(c)) as! u32);
    } else if k == TY_COMPLEX {
        let ek = kind_of(ty.base);
        m = base_md("complex", if is_float_kind(ek) { ATE_complex_float } else { ATE_lo_user }, type_size(unqual(c)));
    } else {
        m = basic_md(k);
    }
    return md_quals(m, q);
}

fn basic_md(k: i64) -> u32 {
    if k == TY_BOOL { return base_md("_Bool", ATE_boolean, 1); }
    if k == TY_CHAR { return base_md("char", if opt_unsigned_char { ATE_unsigned_char } else { ATE_signed_char }, 1); }
    if k == TY_SCHAR { return base_md("signed char", ATE_signed_char, 1); }
    if k == TY_UCHAR { return base_md("unsigned char", ATE_unsigned_char, 1); }
    if k == TY_SHORT { return base_md("short", ATE_signed, 2); }
    if k == TY_USHORT { return base_md("unsigned short", ATE_unsigned, 2); }
    if k == TY_INT { return base_md("int", ATE_signed, 4); }
    if k == TY_UINT { return base_md("unsigned int", ATE_unsigned, 4); }
    if k == TY_LONG { return base_md("long", ATE_signed, 8); }
    if k == TY_ULONG { return base_md("unsigned long", ATE_unsigned, 8); }
    if k == TY_LLONG { return base_md("long long", ATE_signed, 8); }
    if k == TY_ULLONG { return base_md("unsigned long long", ATE_unsigned, 8); }
    if k == TY_INT128 { return base_md("__int128", ATE_signed, 16); }
    if k == TY_UINT128 { return base_md("unsigned __int128", ATE_unsigned, 16); }
    if k == TY_FLOAT16 { return base_md("_Float16", ATE_float, 2); }
    if k == TY_BF16 { return base_md("__bf16", ATE_float, 2); }
    if k == TY_FLOAT { return base_md("float", ATE_float, 4); }
    if k == TY_DOUBLE { return base_md("double", ATE_float, 8); }
    if k == TY_LDOUBLE { return base_md("long double", ATE_float, 16); }
    if k == TY_FLOAT128 { return base_md("__float128", ATE_float, 16); }
    return base_md("int", ATE_signed, 4);
}

// An array type: the counts of the nested array types down to the element
// (clang's CreateType(ArrayType): through ArrayType nodes only, so a
// typedef name ends it), each a constant, unknown (an incomplete array, an
// unregistered VLA) or, for a VLA variable, its __vla_exprN. The counts
// wait in md_tmp (a global stack: the element's metadata may need runs of
// its own) and are moved to md_run when the node is interned.
var md_tmp: u64[>..<] = [];

recursive fn md_array(d0: u32) -> u32 {
    let mark = md_tmp.len;
    var d = d0;
    loop {
        if dq_sugar(d) {
            let t = dtypes[dq_node(d)];
            if dq_quals(d) == 0 && t.kind as i64 == DK_ARRAY {
                md_tmp.push(if t.n < 0 { CNT_NONE } else { (t.n as! u64) + 1 });
                d = t.base;
                continue;
            }
            if dq_quals(d) == 0 && t.kind as i64 == DK_VLA {
                md_tmp.push(CNT_NONE);
                d = t.base;
                continue;
            }
            break;
        }
        let k = kind_of(d);
        if k == TY_ARRAY {
            let n = types[d >> 4].n;
            md_tmp.push(if n < 0 { CNT_NONE } else { (n as! u64) + 1 });
            d = tbase(d);
            continue;
        }
        if k == TY_VLA {
            md_tmp.push(CNT_NONE);
            d = tbase(d);
            continue;
        }
        break;
    }
    let em = md_of(d);
    return md_array_done(em, mark);
}

fn md_array_done(em: u32, mark: i64) -> u32 {
    md_rmark = md_run.len;
    for k in mark..md_tmp.len { md_run.push(md_tmp[k]); }
    md_tmp.resize(mark);
    return md_intern_run(MD_ARRAY, em);
}

// A VLA variable's own array type: its VLA levels' counts are its
// __vla_exprN variables (or constants), then the constant levels.
fn md_vla_var(V: DVar) -> u32 {
    let mark = md_tmp.len;
    let s = V.sym;
    let t = syms[s].ty;
    let w = sym_written(s);
    var d: u32 = if w != 0 && dq_canon(w) == t { w } else { t };
    var lvl = V.n as i64;
    loop {
        if dq_sugar(d) {
            let n = dtypes[dq_node(d)];
            if dq_quals(d) == 0 && (n.kind as i64 == DK_VLA || n.kind as i64 == DK_ARRAY) {
                if n.kind as i64 == DK_VLA {
                    md_tmp.push(vla_cnt(lvl));
                    lvl++;
                } else {
                    md_tmp.push(if n.n < 0 { CNT_NONE } else { (n.n as! u64) + 1 });
                }
                d = n.base;
                continue;
            }
            break;
        }
        let k = kind_of(d);
        if k == TY_VLA {
            md_tmp.push(vla_cnt(lvl));
            lvl++;
            d = tbase(d);
            continue;
        }
        if k == TY_ARRAY {
            let n = types[d >> 4].n;
            md_tmp.push(if n < 0 { CNT_NONE } else { (n as! u64) + 1 });
            d = tbase(d);
            continue;
        }
        break;
    }
    let em = md_of(d);
    return md_array_done(em, mark);
}

fn vla_cnt(lvl: i64) -> u64 {
    if lvl >= vd_var.len { return CNT_NONE; }
    if vd_var[lvl] != NONE { return CNT_VAR | (vd_var[lvl] as u64); }
    return vd_const[lvl] + 1;
}

// A function type: (return type, parameter types), variadic or not.
recursive fn md_func_d(d: u32) -> u32 {
    let t = dtypes[dq_node(d)];
    if (t.flags as i64) & TF_NOPROTO != 0 { return md_intern(MD_NOPROTO, md_of(t.base), 0, 0); }
    let mark = md_tmp.len;
    md_tmp.push(md_of(t.base) as u64);
    let n = t.n;
    for i in n {
        let p = dparams[t.extra as i64 + i];
        let pm = md_of(p);
        md_tmp.push(pm as u64);
    }
    return md_func_done(mark, (t.flags as i64) & TF_VARIADIC != 0);
}

recursive fn md_func_c(c: u32) -> u32 {
    let t = types[c >> 4];
    if (t.flags as i64) & TF_NOPROTO != 0 { return md_intern(MD_NOPROTO, md_of(t.base), 0, 0); }
    let mark = md_tmp.len;
    md_tmp.push(md_of(t.base) as u64);
    for i in t.n {
        let p = tparams[t.extra as i64 + i];
        let pm = md_of(p);
        md_tmp.push(pm as u64);
    }
    return md_func_done(mark, (t.flags as i64) & TF_VARIADIC != 0);
}

fn md_func_done(mark: i64, variadic: bool) -> u32 {
    md_rmark = md_run.len;
    for k in mark..md_tmp.len { md_run.push(md_tmp[k]); }
    md_tmp.resize(mark);
    return md_intern_run(MD_FUNC, if variadic { 1 } else { 0 });
}

// The written types of declarations, falling back to the canonical type
// when the written one does not match it (an array completed by its
// initializer, a redeclaration that changed the type).
fn written_or(w: u32, ty: u32) -> u32 {
    if w == 0 { return ty; }
    if dq_canon(w) == ty { return w; }
    // int a[] = {...}: the completed length
    if dq_sugar(w) && is_array(ty) && kind_of(ty) == TY_ARRAY {
        let t = dtypes[dq_node(w)];
        if t.kind as i64 == DK_ARRAY && t.n < 0 && dq_quals(w) == 0 {
            return d_array(t.base, types[ty >> 4].n, ty);
        }
    }
    return ty;
}

fn var_written(s: i64) -> u32 {
    // file-scope objects: the defining declaration's spelling
    ensure_sym_gen();
    var w = sym_written(s);
    if syms[s].flags & SF_FILESCOPE != 0 {
        let dn = def_decl(s);
        if dn != 0 {
            let nw = node_written(dn);
            if nw != 0 { w = nw; }
        }
    }
    var ty = syms[s].ty;
    // clang: an incomplete array (a tentative int a[];) is int[1]
    if kind_of(ty) == TY_ARRAY && types[ty >> 4].n < 0 { ty = mk_array(tbase(ty), 1); }
    return written_or(w, ty);
}

fn dvar_written(i: i64) -> u32 {
    let V = m_dvars[i];
    if V.flags & DV_VLAEXPR != 0 { return V.dq; }
    return written_or(sym_written(V.sym), syms[V.sym].ty);
}

// The return type of function s as written.
fn fn_ret_written(s: i64) -> u32 {
    let w = sym_written(s);
    let ft = syms[s].ty;
    let rt = types[ft >> 4].base;
    if w != 0 && dq_sugar(w) {
        let t = dtypes[dq_node(w)];
        if t.kind as i64 == DK_FUNC && dq_canon(t.base) == rt { return t.base; }
    }
    return rt;
}

// The declaration that defines file-scope object s: the one with the
// initializer, else the last tentative one (clang's getActingDefinition).
var defdecl = dictionary<u64, u32> {};
fn def_decl(s: i64) -> u32 {
    let r = defdecl.get(s as u64);
    if r { return r; }
    return 0;
}
fn index_decls() {
    let tu = nodes[tu_node];
    for i in tu.c as i64 {
        let it = nlist[tu.v + i];
        let nd = nodes[it];
        if nd.kind != N_DECL { continue; }
        let s = nd.a as i64;
        if syms[s].kind != SK_VAR { continue; }
        let cur = def_decl(s);
        if nd.b != 0 { defdecl.insert(s as u64, it); continue; }
        if cur != 0 && nodes[cur].b != 0 { continue; }
        if decl_is_extern(it) {
            // an extern declaration is not a tentative definition
            if cur == 0 { defdecl.insert(s as u64, it); }
            continue;
        }
        defdecl.insert(s as u64, it);
    }
}

// --------------------------------------------------- the type walk (enums)

// The enum types in the order clang's CGDebugInfo first makes them (it
// makes a type when something emitted needs it, and a record's members
// with it): what DwarfDebug::beginModule walks after the globals.
var walked = dictionary<u64, u32> {};
var o_enums: u32[>..] = [];
var walk_stack: u32[>..] = [];
fn walk_md(m0: u32) {
    if m0 == 0 { return; }
    walk_stack.clear();
    walk_stack.push(m0);
    while walk_stack.len > 0 {
        let m = walk_stack.pop();
        if m == 0 || walked.get(m as u64) { continue; }
        walked.insert(m as u64, 1);
        let M = mds[m];
        let k = M.kind;
        if k == MD_PTR || k == MD_CONST || k == MD_VOLATILE || k == MD_RESTRICT || k == MD_ATOMIC || k == MD_NOPROTO ||
           k == MD_VECTOR {
            walk_stack.push(M.a);
        } else if k == MD_ARRAY {
            walk_stack.push(M.a);
        } else if k == MD_FUNC {
            // in order: the return type, then the parameters
            var j = M.c as i64 - 1;
            while j >= 0 { walk_stack.push(md_run[M.b as i64 + j] as! u32); j--; }
        } else if k == MD_TYPEDEF {
            walk_stack.push(md_of(typedef_written(M.a as i64)));
        } else if k == MD_ENUM {
            o_enums.push(m);
            let u = enums[M.a].underlying;
            if u != 0 { walk_stack.push(md_of(u)); }
        } else if k == MD_REC {
            let r = records[M.a];
            if M.a as i64 == rec_of(t_valist_rec) && va_loc == NONE { va_loc = sim_cur; }
            if r.flags & RF_COMPLETE != 0 {
                var j = (r.first + r.count) as i64 - 1;
                while j >= r.first as i64 {
                    let f = fields[j];
                    if !(f.name == 0 && !is_record(f.ty)) { walk_stack.push(md_of(field_type_written(j))); }
                    j--;
                }
            }
        }
    }
}

fn typedef_written(s: i64) -> u32 {
    let w = sym_written(s);
    return if w != 0 { w } else { syms[s].ty };
}

fn field_type_written(f: i64) -> u32 { written_or(field_written(f), fields[f].ty) }

// ============================================================ 3. DIEs

struct WDie { tag: u32, parent: u32, kid0: u32, kid1: u32, next: u32, a0: u32, a1: u32 }
struct WAttr { at: u32, form: u32, aux: u32, val: u64, next: u32 }
var wd: WDie[>..] = [];
var wa: WAttr[>..] = [];
var md_die: u32[>..] = [];           // per md: its DIE (NONE: not made)
var index_die: u32 = 0xFFFFFFFF;
var cu_die: u32 = 0;
// per symbol: the DIE of a subprogram (functions) or of a variable entity
var sym_die = dictionary<u64, u32> {};
var dvar_die: u32[>..] = [];         // per m_dvars: its DIE (NONE: dropped)
// The location clang's CGDebugInfo uses for a member without one
// (CurLoc: the implicit __va_list_tag's members): the entity being typed.
var cur_line_loc: u32 = 0;

fn wd_new(tag: u32, parent: u32) -> u32 {
    let d = wd.len as! u32;
    wd.push(WDie { tag: tag, parent: parent, kid0: NONE, kid1: NONE, next: NONE, a0: NONE, a1: NONE });
    if parent != NONE { wd_link(d, parent); }
    return d;
}

fn wd_link(d: u32, parent: u32) {
    wd[d].parent = parent;
    if wd[parent].kid1 == NONE { wd[parent].kid0 = d; } else { wd[wd[parent].kid1].next = d; }
    wd[parent].kid1 = d;
}

fn wattr(d: u32, at: u32, form: u32, val: u64, aux: u32) {
    let a = wa.len as! u32;
    wa.push(WAttr { at: at, form: form, aux: aux, val: val, next: NONE });
    if wd[d].a1 == NONE { wd[d].a0 = a; } else { wa[wd[d].a1].next = a; }
    wd[d].a1 = a;
}

fn best_form(v: u64) -> u32 {
    if v <= 0xFF { return DWF_data1; }
    if v <= 0xFFFF { return DWF_data2; }
    if v <= 0xFFFFFFFF { return DWF_data4; }
    return DWF_data8;
}
fn add_uint(d: u32, at: u32, v: u64) { wattr(d, at, best_form(v), v, 0); }
fn add_flag(d: u32, at: u32) { wattr(d, at, DWF_flag_present, 1, 0); }
fn add_str(d: u32, at: u32, s: const u8[:]) { wattr(d, at, GDF_STR, dstring(s) as u64, 0); }
fn add_ref(d: u32, at: u32, t: u32) { wattr(d, at, DWF_ref4, t as u64, 0); }

// DW_AT_decl_file and DW_AT_decl_line of a source location (its expansion
// location, as clang's getPresumedLoc).
fn add_source_line(d: u32, loc: u32) {
    if loc == 0 { return; }
    let file, l, c = dloc_of(loc);
    if file == 0 || l <= 0 { return; }
    wattr(d, DWA_decl_file, GDF_FILE, file as u64, 0);
    add_uint(d, DWA_decl_line, l as! u64);
}
fn add_source_line_cur(d: u32, loc: u32) { add_source_line(d, if loc != 0 { loc } else { cur_line_loc }); }
// A member without a location (clang's createFieldType of an implicit
// field, getOrCreateFile of an invalid location): the unit's file, the
// line of CurLoc.
fn add_source_line_cu(d: u32, loc: u32) {
    if loc == 0 { return; }
    let file, l, c = dloc_of(loc);
    if file == 0 || l <= 0 { return; }
    wattr(d, DWA_decl_file, GDF_FILE, m_dscopes[dbg_cu].file as u64, 0);
    add_uint(d, DWA_decl_line, l as! u64);
}

recursive fn add_type(d: u32, m: u32) {
    let t = die_of(m);
    if t != NONE { add_ref(d, DWA_type, t); }
}

fn ensure_md_die() { while md_die.len < mds.len { md_die.push(NONE); } }

// The DIE the type's declaration is in: a record or enum or typedef
// declared in a function is in its subprogram, an anonymous member record
// in its record, the rest in the unit.
recursive fn context_of(m: u32) -> u32 {
    let M = mds[m];
    var f: i64 = -1;
    if M.kind == MD_REC {
        let pr = record_in_record(M.a as i64);
        if pr >= 0 { return die_of(md_intern(MD_REC, pr as! u32, 0, 0)); }
        f = record_func(M.a as i64);
    } else if M.kind == MD_ENUM {
        let pr = enum_in_record(M.a as i64);
        if pr >= 0 { return die_of(md_intern(MD_REC, pr as! u32, 0, 0)); }
        f = enum_func(M.a as i64);
    } else if M.kind == MD_TYPEDEF {
        f = typedef_func(M.a as i64);
    }
    if f < 0 { return cu_die; }
    return subprogram_die(f);
}

// get_type: the DIE of metadata m, made (with its context first) on first use.
recursive fn die_of(m: u32) -> u32 {
    if m == 0 { return NONE; }
    ensure_md_die();
    if md_die[m] != NONE { return md_die[m]; }
    let M = mds[m];
    let k = M.kind;
    var ctx = cu_die;
    if k == MD_REC || k == MD_ENUM || k == MD_TYPEDEF {
        ctx = context_of(m);
        ensure_md_die();
        if md_die[m] != NONE { return md_die[m]; }
    }
    var tag: u32 = 0;
    if k == MD_BASE { tag = DWT_base_type; }
    else if k == MD_PTR { tag = DWT_pointer_type; }
    else if k == MD_CONST { tag = DWT_const_type; }
    else if k == MD_VOLATILE { tag = DWT_volatile_type; }
    else if k == MD_RESTRICT { tag = DWT_restrict_type; }
    else if k == MD_ATOMIC { tag = DWT_atomic_type; }
    else if k == MD_TYPEDEF { tag = DWT_typedef; }
    else if k == MD_ARRAY || k == MD_VECTOR { tag = DWT_array_type; }
    else if k == MD_FUNC || k == MD_NOPROTO { tag = DWT_subroutine_type; }
    else if k == MD_REC { tag = if records[M.a].flags & RF_UNION != 0 { DWT_union_type } else { DWT_structure_type }; }
    else if k == MD_ENUM { tag = DWT_enumeration_type; }
    let d = wd_new(tag, ctx);
    md_die[m] = d;
    if k == MD_BASE {
        wattr(d, DWA_name, GDF_STR, M.c as u64, 0);
        wattr(d, DWA_encoding, DWF_data1, M.a as u64, 0);
        add_uint(d, DWA_byte_size, M.b as u64);
    } else if k == MD_PTR || k == MD_CONST || k == MD_VOLATILE || k == MD_RESTRICT || k == MD_ATOMIC {
        add_type(d, M.a);
    } else if k == MD_TYPEDEF {
        let s = M.a as i64;
        add_type(d, md_of(typedef_written(s)));
        add_str(d, DWA_name, ident_text(syms[s].name as i64));
        let ty = types[syms[s].ty >> 4];
        if (ty.flags as i64) & TF_ALIGNED != 0 { wattr(d, DWA_alignment, DWF_udata, ty.align as u64, 0); }
        add_source_line(d, syms[s].loc);
    } else if k == MD_ARRAY {
        construct_array(d, m);
    } else if k == MD_VECTOR {
        add_flag(d, DWA_GNU_vector);
        let em = M.a;
        let es = md_size(em);
        // LLVM's hasVectorBeenPadded: the element's DI size (0 for a
        // typedef or a qualified type) times the lanes is not the size
        if M.c as u64 != (M.b as u64) * es { add_uint(d, DWA_byte_size, M.c as u64); }
        add_type(d, em);
        let idx = get_index_ty();
        let sr = wd_new(DWT_subrange_type, d);
        add_ref(sr, DWA_type, idx);
        add_uint(sr, DWA_count, M.b as u64);
    } else if k == MD_FUNC {
        construct_subroutine(d, m);
    } else if k == MD_NOPROTO {
        add_type(d, M.a);
        wd_new(DWT_unspecified_parameters, d);
    } else if k == MD_REC {
        construct_record(d, M.a as i64);
    } else if k == MD_ENUM {
        construct_enum(d, M.a as i64);
    }
    return d;
}

// The size of a type's metadata in bytes, as LLVM's getSizeInBits: base
// types, pointers, records, enums, vectors and arrays have one; typedefs and
// qualified types have none (0).
fn md_size(m: u32) -> u64 {
    let M = mds[m];
    if M.kind == MD_BASE { return M.b as u64; }
    if M.kind == MD_PTR { return 8; }
    if M.kind == MD_VECTOR { return M.c as u64; }
    if M.kind == MD_REC { return if records[M.a].size > 0 { records[M.a].size as! u64 } else { 0 as u64 }; }
    if M.kind == MD_ENUM {
        let u = enums[M.a].underlying;
        return if u != 0 { type_size(u) as! u64 } else { 0 as u64 };
    }
    return 0;
}

fn get_index_ty() -> u32 {
    if index_die != NONE { return index_die; }
    index_die = wd_new(DWT_base_type, cu_die);
    add_str(index_die, DWA_name, "__ARRAY_SIZE_TYPE__");
    add_uint(index_die, DWA_byte_size, 8);
    wattr(index_die, DWA_encoding, DWF_data1, ATE_unsigned as u64, 0);
    return index_die;
}

recursive fn construct_array(d: u32, m: u32) {
    let M = mds[m];
    add_type(d, M.a);
    let idx = get_index_ty();
    for k in M.c as i64 {
        let c = md_run[M.b as i64 + k];
        let sr = wd_new(DWT_subrange_type, d);
        add_ref(sr, DWA_type, idx);
        if c & CNT_VAR != 0 {
            let v = (c & 0x7FFFFFFF) as i64;
            if v < dvar_die.len && dvar_die[v] != NONE { add_ref(sr, DWA_count, dvar_die[v]); }
        } else if c != CNT_NONE {
            add_uint(sr, DWA_count, c - 1);
        }
    }
}

recursive fn construct_subroutine(d: u32, m: u32) {
    let M = mds[m];
    let rm = md_run[M.b as i64] as! u32;
    add_type(d, rm);
    let n = M.c as i64;
    for k in 1..n {
        let pm = md_run[M.b as i64 + k] as! u32;
        let p = wd_new(DWT_formal_parameter, d);
        add_type(p, pm);
    }
    if M.a != 0 { wd_new(DWT_unspecified_parameters, d); }
    // LLVM: no prototype only for (ret, unspecified)
    if !(M.a != 0 && n == 1) { add_flag(d, DWA_prototyped); }
}

recursive fn construct_record(d: u32, r: i64) {
    let R = records[r];
    let complete = R.flags & RF_COMPLETE != 0;
    if complete {
        for j in (R.first as i64)..((R.first + R.count) as i64) {
            let f = fields[j];
            // unnamed fields are left out, except anonymous structs and unions
            if f.name == 0 && !is_record(f.ty) { continue; }
            let md = wd_new(DWT_member, d);
            if f.name != 0 { add_str(md, DWA_name, ident_text(f.name as i64)); }
            add_type(md, md_of(field_type_written(j)));
            if f.loc != 0 { add_source_line(md, f.loc); }
            else if r == rec_of(t_valist_rec) && va_loc != NONE { add_source_line_cu(md, va_loc); }
            else { add_source_line_cu(md, cur_line_loc); }
            if f.width >= 0 {
                add_uint(md, DWA_bit_size, f.width as! u64);
                add_uint(md, DWA_data_bit_offset, f.bitpos as! u64);
            } else {
                // clang's createFieldType: the member's aligned attribute,
                // else its type's required alignment
                let al: u64 = if f.attr_align != 0 { f.attr_align as u64 } else { align_required(f.ty) };
                if al != 0 { wattr(md, DWA_alignment, DWF_udata, al, 0); }
                add_uint(md, DWA_data_member_location, f.offset as! u64);
            }
        }
    }
    if R.name != 0 { add_str(d, DWA_name, ident_text(R.name as i64)); }
    if complete {
        add_uint(d, DWA_byte_size, if R.size < 0 { 0 as u64 } else { R.size as! u64 });
        add_source_line(d, R.loc);
        if R.attr_align != 0 || R.pack != 0 { wattr(d, DWA_alignment, DWF_udata, R.align as u64, 0); }
    } else {
        add_flag(d, DWA_declaration);
    }
}

recursive fn construct_enum(d: u32, e: i64) {
    let E = enums[e];
    let u = E.underlying;
    if u != 0 { add_type(d, md_of(u)); }
    let uns = u != 0 && !is_signed(u);
    if e < enum_c0.len {
        for k in (enum_c0[e] as i64)..((enum_c0[e] + enum_cn[e]) as i64) {
            let s = enum_csyms[k] as i64;
            let en = wd_new(DWT_enumerator, d);
            add_str(en, DWA_name, ident_text(syms[s].name as i64));
            wattr(en, DWA_const_value, if uns { DWF_udata } else { DWF_sdata }, syms[s].v as! u64, 0);
        }
    }
    if E.name != 0 { add_str(d, DWA_name, ident_text(E.name as i64)); }
    if E.complete {
        if u != 0 { add_uint(d, DWA_byte_size, type_size(u) as! u64); }
        add_source_line(d, enum_def_loc(e, E.loc));
    } else {
        add_flag(d, DWA_declaration);
    }
}

// clang's getTypeAlignIfRequired: the alignment of a type whose alignment
// is required (a typedef or record with an aligned attribute, an array of
// such), or of a record declared under #pragma pack; else 0.
fn align_required(q: u32) -> u64 {
    var t = types[q >> 4];
    if (t.flags as i64) & TF_ALIGNED != 0 { return t.align as u64; }
    let k = t.kind as i64;
    if k == TY_STRUCT || k == TY_UNION {
        let R = records[t.extra];
        if R.attr_align != 0 || R.pack != 0 { return R.align as u64; }
        return 0;
    }
    if k == TY_ARRAY {
        let e = types[t.base >> 4];
        if (e.flags as i64) & TF_ALIGNED != 0 { return e.align as u64; }
        if e.kind as i64 == TY_STRUCT || e.kind as i64 == TY_UNION {
            let R = records[e.extra];
            if R.attr_align != 0 { return R.align as u64; }
        }
    }
    return 0;
}

// The subprogram DIE of function symbol s (made on first use, in the unit).
fn subprogram_die(s: i64) -> u32 {
    let r = sym_die.get(s as u64);
    if r { return r; }
    let d = wd_new(DWT_subprogram, cu_die);
    sym_die.insert(s as u64, d);
    return d;
}

// ------------------------------------------------------- global variables

// get_global_variable: a file-scope variable, a static local (in its
// function's subprogram) or a string literal.
fn global_die(G: OGlob) {
    if G.kind == 3 {
        let g = G.a as u32;
        let d = wd_new(DWT_variable, cu_die);
        // the literal's type: char[N] (or the wide character's array)
        add_type(d, md_of(string_type_of(g)));
        add_source_line(d, G.b);
        wattr(d, DWA_location, GDF_GLOBAL, g as u64, 0);
        return;
    }
    if G.kind == 4 {
        // a file-scope variable clang only folded reads of: its value
        let s = G.a;
        let d = wd_new(DWT_variable, cu_die);
        sym_die.insert((s as u64) | 0x100000000, d);
        cur_line_loc = var_loc(s);
        add_str(d, DWA_name, ident_text(syms[s].name as i64));
        add_type(d, md_of(var_written(s)));
        add_source_line(d, var_loc(s));
        let a = syms[s].attr;
        if a != 0 && sym_attrs[a].align != 0 { wattr(d, DWA_alignment, DWF_udata, sym_attrs[a].align as u64, 0); }
        if !cval_none.contains(s as u64) {
            let b = cval_bits.get(s as u64);
            if b { wattr(d, DWA_const_value, DWF_udata, b, 0); }
        }
        return;
    }
    var s: i64 = 0;
    var g: u32 = 0;
    var ctx = cu_die;
    if G.kind == 1 {
        let V = m_dgvars[G.a];
        s = V.sym;
        g = V.g;
    } else {
        s = G.a;
        ensure_sym_gen();
        g = sym_gen[s].glob;
        ctx = subprogram_die(static_owner(s));
    }
    let d = wd_new(DWT_variable, ctx);
    sym_die.insert((s as u64) | 0x100000000, d);
    cur_line_loc = var_loc(s);
    add_str(d, DWA_name, ident_text(syms[s].name as i64));
    add_type(d, md_of(var_written(s)));
    if G.kind == 1 && !is_internal_sym(s) { add_flag(d, DWA_external); }
    add_source_line(d, var_loc(s));
    let a = syms[s].attr;
    if a != 0 && sym_attrs[a].align != 0 { wattr(d, DWA_alignment, DWF_udata, sym_attrs[a].align as u64, 0); }
    if g != NONE { wattr(d, DWA_location, GDF_GLOBAL, g as u64, 0); }
    if G.kind == 1 && a != 0 && sym_attrs[a].asm_len != 0 {
        let off = sym_attrs[a].asm_label as i64;
        var nm = strbytes[off..off + sym_attrs[a].asm_len];
        if nm.len > 0 && nm[0] == 1 { nm = nm[1..]; }
        if nm != ident_text(syms[s].name as i64) { add_str(d, DWA_linkage_name, nm); }
    }
}

// The location of variable s's (defining) declaration.
fn var_loc(s: i64) -> u32 {
    if syms[s].flags & SF_FILESCOPE != 0 {
        let dn = def_decl(s);
        if dn != 0 { return nodes[dn].loc; }
    }
    return syms[s].loc;
}

var static_fn = dictionary<u64, u32> {};   // static local symbol -> its function symbol
fn static_owner(s: i64) -> i64 {
    let r = static_fn.get(s as u64);
    if r { return r as i64; }
    return 0;
}

// The type of a string literal's global: an array of its characters.
var str_types = dictionary<u64, u32> {};   // string global -> the literal's type
fn string_type_of(g: u32) -> u32 {
    let r = str_types.get(g as u64);
    if r { return r; }
    return mk_array(t_char, m_globals[g].size as i64);
}

// A string literal used as an address (clang's GetAddrOfConstantStringFromLiteral).
fn dbg_string(n: u32, g: u32) {
    if !opt_debug || !ev_on { return; }
    if !str_types.get(g as u64) {
        let sl = strs[nodes[n].a];
        let w = type_size(sl.elem);
        // __func__ and its kin are const char arrays
        let et = if nodes[n].flags & NF_PREDEF != 0 { unqual(sl.elem) | (Q_CONST as! u32) } else { unqual(sl.elem) };
        str_types.insert(g as u64, mk_array(et, (m_globals[g].size as i64) / (if w > 0 { w } else { 1 })));
    }
    dev(EV_STR, g, nodes[n].loc);
}

// A static local definition, in the function being lowered.
fn dbg_static(s: i64) {
    if !opt_debug || !ev_on || dbg_nodebug { return; }
    static_fn.insert(s as u64, f_sym as! u32);
    dev(EV_STATIC, s as! u32, 0);
}

// ------------------------------------------------------------ functions

// LexicalScopes for one function: a scope per DScope that some
// instruction's location names (and its enclosing ones), in the order the
// instructions first name them.
struct LScope { ds: u32, parent: i32, kid0: i32, kid1: i32, next: i32, v0: i32, v1: i32, l0: i32, l1: i32, a0: i32, a1: i32 }
var lsc: LScope[>..] = [];
var lsc_of: u32[>..] = [];           // per dscope: its LScope + 1 (0: none), reset per function
var lsc_touched: u32[>..] = [];
// entity lists: per LScope linked lists of entities (ent_next)
var ent_kind: u8[>..] = [];          // 1 variable (dvar index), 2 label (dlab index)
var ent_idx: u32[>..] = [];
var ent_next: i32[>..] = [];
var ent_die: u32[>..] = [];
// all concrete entities in creation order (finishEntityDefinitions)
var ents_all: u32[>..] = [];

recursive fn lscope(ds0: u32) -> i32 {
    // lexical block files are their blocks (getNonLexicalBlockFileScope)
    var ds = ds0;
    while ds != 0 && m_dscopes[ds].kind == 4 { ds = m_dscopes[ds].parent; }
    while lsc_of.len < m_dscopes.len { lsc_of.push(0); }
    if lsc_of[ds] != 0 { return (lsc_of[ds] - 1) as! i32; }
    var parent: i32 = -1;
    let S = m_dscopes[ds];
    if S.kind == 3 {
        parent = lscope(S.parent);
        if parent < 0 { return -1; }
    } else if S.kind != 2 {
        return -1;
    }
    let k = lsc.len as! i32;
    lsc.push(LScope { ds: ds, parent: parent, kid0: -1, kid1: -1, next: -1, v0: -1, v1: -1, l0: -1, l1: -1, a0: -1, a1: -1 });
    if parent >= 0 {
        if lsc[parent].kid1 < 0 { lsc[parent].kid0 = k; } else { lsc[lsc[parent].kid1].next = k; }
        lsc[parent].kid1 = k;
    }
    lsc_of[ds] = (k + 1) as! u32;
    lsc_touched.push(ds);
    return k;
}

fn ent_new(kind: u8, idx: u32, die: u32) -> u32 {
    let e = ent_kind.len as! u32;
    ent_kind.push(kind);
    ent_idx.push(idx);
    ent_next.push(-1);
    ent_die.push(die);
    ents_all.push(e);
    return e;
}

// Appends entity e to a list of scope s: 0 locals, 1 labels, 2 arguments
// (kept sorted by argument number).
fn ent_add(s: i32, e: u32, which: i64) {
    if which == 2 {
        // insertion by argument number; a duplicate number keeps the first
        let an = m_dvars[ent_idx[e]].argno;
        var prev: i32 = -1;
        var cur = lsc[s].a0;
        while cur >= 0 {
            let cn = m_dvars[ent_idx[cur]].argno;
            if cn == an { return; }
            if cn > an { break; }
            prev = cur;
            cur = ent_next[cur];
        }
        ent_next[e] = cur;
        if prev < 0 { lsc[s].a0 = e as! i32; } else { ent_next[prev] = e as! i32; }
        return;
    }
    if which == 0 {
        if lsc[s].v1 < 0 { lsc[s].v0 = e as! i32; } else { ent_next[lsc[s].v1] = e as! i32; }
        lsc[s].v1 = e as! i32;
    } else {
        if lsc[s].l1 < 0 { lsc[s].l0 = e as! i32; } else { ent_next[lsc[s].l1] = e as! i32; }
        lsc[s].l1 = e as! i32;
    }
}

var processed: u32[>..] = [];        // DFn indices (finishSubprogramDefinitions)

// DwarfDebug::endFunctionImpl for function F: its scopes, entities, DIEs.
fn function_dies(fx: u32) {
    let F = m_dfns[fx];
    let fi = F.fi;
    let G = m_funcs[fi];
    if G.dbg == 0 { return; }
    for ds in lsc_touched { lsc_of[ds] = 0; }
    lsc_touched.clear();
    lsc.clear();
    lscope(G.dbg);
    // LLVM's code generator removes the blocks the entry does not reach
    // (UnreachableBlockElim, also at -O0): their locations make no scopes
    // and their labels are gone
    reach_blocks(fi);
    var prev: u32 = 0;
    for b in 0..G.n_blocks {
        if reach[b] == 0 { continue; }
        let B = m_blocks[G.first_block + b];
        for k in B.first_inst..B.first_inst + B.n_inst {
            let dl = m_insts[k].dbg;
            if dl != 0 && dl != prev { lscope(m_dlocs[dl].scope); }
            if dl != 0 { prev = dl; }
        }
    }
    // the variables: static allocas first (LLVM's MF side table), then the
    // others; then the labels
    for pass in 2 {
        for v in F.v0..F.v1 {
            let V = m_dvars[v];
            if (V.flags & DV_MF != 0) != (pass == 0) { continue; }
            let ds = m_srecs[F.r0 + V.rec].dscope;
            if ds == 0 { continue; }
            let s = lsc_find(ds);
            if s < 0 { continue; }
            let d = wd_new(if V.argno != 0 { DWT_formal_parameter } else { DWT_variable }, NONE);
            wattr(d, DWA_location, GDF_LOCAL, ((fi as u64) << 32) | (V.addr as u64), 0);
            dvar_die[v] = d;
            let e = ent_new(1, v, d);
            ent_add(s, e, if V.argno != 0 { 2 } else { 0 });
        }
    }
    for l in F.l0..F.l1 {
        let L = m_dlabs[l];
        if !inst_reached(fi, L.blk) { continue; }
        let ds = m_srecs[F.r0 + L.rec].dscope;
        if ds == 0 { continue; }
        let s = lsc_find(ds);
        if s < 0 { continue; }
        let d = wd_new(DWT_label, NONE);
        let e = ent_new(2, l, d);
        ent_add(s, e, 1);
    }
    // the subprogram DIE
    let d = subprogram_die(F.sym);
    wattr(d, DWA_low_pc, GDF_PC, fi as u64, 0);
    wattr(d, DWA_frame_base, GDF_FRAME_BASE, 0, 0);
    scope_children(0, d);
    if (types[syms[F.sym].ty >> 4].flags as i64) & TF_VARIADIC != 0 { wd_new(DWT_unspecified_parameters, d); }
    processed.push(fx);
}

// The blocks of function fi the entry reaches (reach[b] != 0, local block numbers).
var reach: u8[>..] = [];
var reach_work: u32[>..] = [];
fn reach_blocks(fi: u32) {
    let G = m_funcs[fi];
    reach.clear();
    reach.resize(G.n_blocks as i64, 0);
    reach_work.clear();
    if G.n_blocks == 0 { return; }
    reach[0] = 1;
    reach_work.push(0);
    while reach_work.len > 0 {
        let b = reach_work.pop();
        let B = m_blocks[G.first_block + b];
        if B.n_inst == 0 { continue; }
        let I = m_insts[B.first_inst + B.n_inst - 1];
        let op = I.op as u32;
        if op == GIR_BR { reach_mark(I.a); }
        else if op == GIR_CONDBR { reach_mark(I.b); reach_mark(I.c); }
        else if op == GIR_SWITCH {
            reach_mark(m_opnds[I.b]);
            for k in 0..I.c { reach_mark(m_opnds[I.b + 2 + 2 * k]); }
        } else if op == GIR_INDIRECTBR {
            for k in 0..I.c { reach_mark(m_opnds[I.b + k]); }
        }
    }
}
fn reach_mark(b: u32) {
    if b as i64 >= reach.len || reach[b] != 0 { return; }
    reach[b] = 1;
    reach_work.push(b);
}
// Is module instruction k (of function fi) in a reached block?
fn inst_reached(fi: u32, k: u32) -> bool {
    let G = m_funcs[fi];
    for b in 0..G.n_blocks {
        let B = m_blocks[G.first_block + b];
        if k >= B.first_inst && k < B.first_inst + B.n_inst { return reach[b] != 0; }
    }
    return false;
}

fn lsc_find(ds: u32) -> i32 {
    if ds >= lsc_of.len as! u32 || lsc_of[ds] == 0 { return -1; }
    return (lsc_of[ds] - 1) as! i32;
}

// createAndAddScopeChildren: the arguments, the locals (variables that
// other variables' array bounds name first), the labels, then the nested
// scopes: a lexical block for one with variables, the others flattened.
var sc_stack: i32[>..] = [];
fn scope_children(s0: i32, die0: u32) {
    // (scope, die, phase) frames: an explicit stack instead of recursion;
    // the phase is -2 before the entities, then the next nested scope (-1: done)
    sc_stack.clear();
    sc_stack.push(s0);
    sc_stack.push(die0 as! i32);
    sc_stack.push(-2);
    while sc_stack.len > 0 {
        let t = sc_stack.len - 3;
        let s = sc_stack[t];
        let die = sc_stack[t + 1] as! u32;
        let ph = sc_stack[t + 2];
        if ph == -2 {
            var e = lsc[s].a0;
            while e >= 0 { wd_link(ent_die[e], die); e = ent_next[e]; }
            emit_locals(s, die);
            e = lsc[s].l0;
            while e >= 0 { wd_link(ent_die[e], die); e = ent_next[e]; }
            sc_stack[t + 2] = lsc[s].kid0;
            continue;
        }
        if ph < 0 {
            sc_stack.resize(t);
            continue;
        }
        let k = ph;
        sc_stack[t + 2] = lsc[k].next;
        if lsc[k].a0 < 0 && lsc[k].v0 < 0 {
            // no variables: its contents go to the enclosing DIE
            sc_stack.push(k);
            sc_stack.push(die as! i32);
            sc_stack.push(-2);
            continue;
        }
        let b = wd_new(DWT_lexical_block, die);
        wattr(b, 0, GDF_SCOPE_PC, lsc[k].ds as u64, 0);
        sc_stack.push(k);
        sc_stack.push(b as! i32);
        sc_stack.push(-2);
    }
}

// The locals of scope s in LLVM's sortLocalVars order: a stable
// topological sort, a VLA's bound variables before it.
fn emit_locals(s: i32, die: u32) {
    var e = lsc[s].v0;
    while e >= 0 {
        let v = ent_idx[e] as i64;
        let V = m_dvars[v];
        if V.flags & DV_VLA != 0 {
            // its __vla_exprN variables first, if they are locals of this scope not linked yet
            var lvl = V.n as i64;
            var t = syms[V.sym].ty;
            while kind_of(t) == TY_VLA {
                if lvl < vd_var.len && vd_var[lvl] != NONE {
                    let bv = vd_var[lvl] as i64;
                    let bd = dvar_die[bv];
                    if bd != NONE && wd[bd].parent == NONE { wd_link(bd, die); }
                }
                lvl++;
                t = tbase(t);
            }
        }
        if wd[ent_die[e]].parent == NONE { wd_link(ent_die[e], die); }
        e = ent_next[e];
    }
}

// finishSubprogramDefinitions: a definition's attributes.
fn subprogram_attrs(fx: u32) {
    let F = m_dfns[fx];
    let s = F.sym;
    let d = subprogram_die(s);
    let a = syms[s].attr;
    if a != 0 && sym_attrs[a].asm_len != 0 {
        let off = sym_attrs[a].asm_label as i64;
        var nm = strbytes[off..off + sym_attrs[a].asm_len];
        if nm.len > 0 && nm[0] == 1 { nm = nm[1..]; }
        if nm != ident_text(syms[s].name as i64) { add_str(d, DWA_linkage_name, nm); }
    }
    add_str(d, DWA_name, ident_text(syms[s].name as i64));
    let def = syms[s].def;
    cur_line_loc = if def >= 0 { nodes[def].loc } else { syms[s].loc };
    add_source_line(d, cur_line_loc);
    if func_prototyped(s) { add_flag(d, DWA_prototyped); }
    add_type(d, md_of(fn_ret_written(s)));
    if m_funcs[F.fi].flags & FN_INTERNAL == 0 { add_flag(d, DWA_external); }
    if syms[s].flags & SF_NORETURN != 0 || (types[syms[s].ty >> 4].flags as i64) & TF_NORETURN != 0 { add_flag(d, DWA_noreturn); }
}

// finishEntityDefinitions: a variable's or label's attributes.
fn entity_attrs(e: u32) {
    let d = ent_die[e];
    if ent_kind[e] == 2 {
        let L = m_dlabs[ent_idx[e]];
        add_str(d, DWA_name, ident_text(syms[L.sym].name as i64));
        add_source_line(d, local_label_loc(L.sym, L.loc));
        wattr(d, DWA_low_pc, GDF_LABEL, L.blk as u64, 0);
        return;
    }
    let v = ent_idx[e] as i64;
    let V = m_dvars[v];
    if V.flags & DV_VLAEXPR != 0 {
        var nm: u8[>..] = [];
        format(nm, "__vla_expr", V.n);
        add_str(d, DWA_name, nm);
        add_type(d, md_of(V.dq));
        add_flag(d, DWA_artificial);
        return;
    }
    let s = V.sym;
    if syms[s].name != 0 { add_str(d, DWA_name, ident_text(syms[s].name as i64)); }
    let a = syms[s].attr;
    if a != 0 && sym_attrs[a].align != 0 { wattr(d, DWA_alignment, DWF_udata, sym_attrs[a].align as u64, 0); }
    add_source_line(d, syms[s].loc);
    cur_line_loc = syms[s].loc;
    if V.flags & DV_VLA != 0 { add_type(d, md_vla_var(V)); }
    else { add_type(d, md_of(dvar_written(v))); }
}

// ------------------------------------------------------------ the module

fn dbg_build() {
    if !opt_debug { return; }
    index_decls();
    while dvar_die.len < m_dvars.len { dvar_die.push(NONE); }
    sim_run();
    // LLVM makes the unit only when something is in it
    var nfn = 0;
    for F in m_dfns { if !F.nodebug { nfn++; } }
    if o_globs.len == 0 && o_enums.len == 0 && o_retained.len == 0 && o_imports.len == 0 && nfn == 0 { return; }
    // beginModule: the unit
    cu_die = wd_new(DWT_compile_unit, NONE);
    let C = m_dscopes[dbg_cu];
    wattr(cu_die, DWA_producer, GDF_STR, C.name as u64, 0);
    wattr(cu_die, DWA_language, DWF_data2, dbg_lang as u64, 0);
    wattr(cu_die, DWA_name, GDF_STR, m_dfiles[C.file].name as u64, 0);
    wattr(cu_die, DWA_str_offsets_base, GDF_STR_BASE, 0, 0);
    wattr(cu_die, DWA_stmt_list, GDF_STMT_LIST, 0, 0);
    if m_dfiles[C.file].dir != 0 { wattr(cu_die, DWA_comp_dir, GDF_STR, m_dfiles[C.file].dir as u64, 0); }
    wattr(cu_die, DWA_low_pc, GDF_CU_PC, 0, 0);
    wattr(cu_die, DWA_addr_base, GDF_ADDR_BASE, 0, 0);
    // the global variables, the enum types, the retained types
    for G in o_globs { global_die(G); }
    for m in o_enums { die_of(m); }
    for m in o_retained { die_of(m); }
    // the functions, in module order
    for fx in o_fns { if !m_dfns[fx].nodebug { function_dies(fx); } }
    // endModule: the imported entities, then the definitions' attributes
    for I in o_imports {
        let t = sym_die.get((I.target as u64) | 0x100000000);
        if !t { continue; }
        let d = wd_new(DWT_imported_declaration, cu_die);
        add_source_line(d, syms[I.sym].loc);
        add_ref(d, DWA_import, t);
        add_str(d, DWA_name, ident_text(syms[I.sym].name as i64));
    }
    for fx in processed { subprogram_attrs(fx); }
    for e in ents_all { entity_attrs(e); }
    write_dies();
}

// Pre-order into m_dies / m_dattrs, references renumbered.
var w_new: u32[>..] = [];
var w_stack: u32[>..] = [];
var w_order: u32[>..] = [];
fn write_dies() {
    w_new.clear();
    w_new.resize(wd.len, NONE);
    w_order.clear();
    w_stack.clear();
    w_stack.push(cu_die);
    while w_stack.len > 0 {
        let d = w_stack.pop();
        w_new[d] = w_order.len as! u32;
        w_order.push(d);
        // the children in reverse, so the first is next
        var kids: u32[>..] = [];
        var k = wd[d].kid0;
        while k != NONE { kids.push(k); k = wd[k].next; }
        var i = kids.len - 1;
        while i >= 0 { w_stack.push(kids[i]); i--; }
    }
    for d in w_order {
        let W = wd[d];
        let a0 = m_dattrs.len as! u32;
        var a = W.a0;
        while a != NONE {
            let A = wa[a];
            var val = A.val;
            var keep = true;
            if A.form == DWF_ref4 {
                let t = w_new[A.val];
                if t == NONE { keep = false; } else { val = t as u64; }
            }
            if keep { m_dattrs.push(DAttr { at: A.at as! u16, form: A.form as! u16, aux: A.aux, val: val }); }
            a = A.next;
        }
        m_dies.push(Die { tag: W.tag as! u16, flags: 0, parent: if W.parent == NONE { NONE } else { w_new[W.parent] }, attrs: a0,
            n_attrs: m_dattrs.len as! u32 - a0 });
    }
}

var m_dies: Die[>..] = [];
var m_dattrs: DAttr[>..] = [];
