// goosecc D3: C++ exception handling and cleanups in the lowering (the
// C++ part of gen_stmt.goose's cleanup stack). See DESIGN.md, 14.3.
//
// The cleanup stack (gen_stmt.goose, `cleanups`) holds, besides C's VLA
// stack restores and cleanup-attribute calls, the C++ scopes of clang's
// EHScopeStack: destructor calls of locals and temporaries, cleanup
// statements (EH-only ones for partially constructed objects), the
// __cxa_end_catch of a handler, try blocks and terminate scopes. Each of
// them that an exception may pass is also an EH entry (eh_ents), linked
// to the entry below it; `eh_top` is the innermost entry where code is
// being emitted. A call that may throw while eh_top >= 0 is an invoke whose
// landing pad belongs to eh_top: one landing pad per entry (the invokes
// below the same entry share it), whose action list (catch clauses of the
// enclosing try blocks, cleanup, terminate) is computed when it is made.
// The landing pads and the dispatch blocks (an entry's cleanup code, or a
// try block's comparisons of the selector, then the entry below) are
// emitted at the end of the function, as clang's EH dispatch blocks: the
// landing pad stores the exception and the selector into two slots, the
// dispatch blocks read them back.

namespace gen;

import std;
import dictionary;
import .common;
import .types;
import .ast;
import .sema;
import .cx_gen_defs;

// Cleanup kinds beyond C's (1 stack restore, 2 call fsym(&sym)).
let CL_STMT = 3;        // the statement `node`
let CL_ENDCATCH = 4;    // __cxa_end_catch()
let CL_TRY = 5;         // a try block (node: its N_XTRY): no code, catches
let CL_TERM = 6;        // a terminate scope: no code
// Cleanup.flags
let CLF_EHONLY = 1;     // only on the exceptional path
let CLF_EXT = 2;        // a lifetime-extended temporary: survives the statement's scope
let CLF_COND = 4;       // conditional: val is the slot of its i1 flag

fn eh_on() -> bool { opt_cxx && opt_exceptions }

let EK_CLEANUP = 1;
let EK_TRY = 2;
let EK_TERM = 3;

struct EhEnt { kind: u8, used: u8, rsv: u16, parent: i32, lp: u32, disp: u32, c: Cleanup, h0: u32, nh: u32, acts: u32, nacts: u32 }
var eh_ents: EhEnt[>..<] = [];
struct EhHandler { blk: u32, ti: i64 }
var eh_hs: EhHandler[>..<] = [];
var eh_top: i64 = -1;
var eh_exn_slot: u32 = NONE;
var eh_sel_slot: u32 = NONE;
var eh_tsyms: i64[>..<] = [];   // the function's type table: typeinfo variables (-1: catch-all)
var eh_acts: u32[>..<] = [];    // the landing pads' action lists
var eh_pending: i64[>..<] = []; // ent * 2 (landing pad) or ent * 2 + 1 (dispatch) to emit; -1: the resume block
var eh_resume: u32 = NONE;
var f_eh = false;               // the function has landing pads

// Per module: the personality's DW.ref variable, the typeinfo stubs, the
// EH table, comdats.
var m_ehs: Eh[>..] = [];
var m_comdats: Comdat[>..] = [];
var m_gcomdat: u32[>..] = [];
var eh_pers: u32 = NONE;
var eh_stubs = dictionary<u64, u32> {};
var cdnames = dictionary<u64, u32> {};      // group signature (ident) -> comdats index
var need_terminate_fn = false;

fn eh_fn_begin() {
    eh_ents.clear();
    eh_hs.clear();
    eh_top = -1;
    eh_exn_slot = NONE;
    eh_sel_slot = NONE;
    eh_tsyms.clear();
    eh_acts.clear();
    eh_pending.clear();
    eh_resume = NONE;
    f_eh = false;
}

// ------------------------------------------------------------ the stack

// The innermost EH entry among cleanups[0..i).
fn eh_below(i: i64) -> i64 {
    var j = i - 1;
    while j >= 0 {
        if cleanups[j].ent >= 0 { return cleanups[j].ent as i64; }
        j--;
    }
    return -1;
}

// Pushes cleanup c (an EH entry too when exceptions may pass it).
fn push_cl(c0: Cleanup) {
    var c = c0;
    c.ent = -1;
    if eh_on() && c.kind != 1 {
        let e = eh_ents.len;
        let k = if c.kind == CL_TRY { EK_TRY } else if c.kind == CL_TERM { EK_TERM } else { EK_CLEANUP };
        eh_ents.push(EhEnt { kind: k as! u8, used: 0, rsv: 0, parent: eh_top as! i32, lp: NONE, disp: NONE, c: c, h0: 0, nh: 0,
            acts: 0, nacts: 0 });
        c.ent = e as! i32;
        eh_top = e;
    }
    cleanups.push(c);
}

// After the stack shrank.
fn eh_retop() {
    if eh_on() { eh_top = eh_below(cleanups.len); }
}

// The scope of a statement's full-expression (C++): its temporaries are
// destroyed at its end, except the lifetime-extended ones, which move to
// the enclosing block's scope.
fn pop_stmt_scope() {
    let mark = cleanup_marks.pop() as i64;
    var any_ext = false;
    for i in mark..cleanups.len { if cleanups[i].flags & CLF_EXT != 0 { any_ext = true; } }
    if !any_ext {
        if has_insert() { run_cleanups(mark); }
        cleanups.resize(mark);
        eh_retop();
        return;
    }
    // run the others, innermost first; keep the extended ones
    let sm = ext_save.len;
    var i = cleanups.len - 1;
    while i >= mark {
        let c = cleanups[i];
        if c.flags & CLF_EXT != 0 { ext_save.push(c); }
        else if has_insert() { emit_cleanup(c, eh_below(i)); }
        i--;
    }
    cleanups.resize(mark);
    eh_retop();
    var j = ext_save.len - 1;
    while j >= sm {
        var c = ext_save[j];
        c.flags = c.flags & ~(CLF_EXT as! u8);
        push_cl(c);
        j--;
    }
    ext_save.resize(sm);
}
var ext_save: Cleanup[>..<] = [];

// The code of cleanup c on the normal path (below: the EH entry below it).
fn emit_cleanup(c: Cleanup, below: i64) {
    if c.kind == 1 {
        emit(GIR_STACKRESTORE, GIR_T_VOID, 0, 0, 0, c.val, 0, 0);
        return;
    }
    if c.kind >= CL_TRY || c.flags & CLF_EHONLY != 0 { return; }
    cleanup_code(c, below);
}

// The code of cleanup c (either path), with the EH state `below`.
fn cleanup_code(c: Cleanup, below: i64) {
    let saved = eh_top;
    eh_top = below;
    var skip = NONE;
    if c.flags & CLF_COND != 0 {
        // a conditional temporary: if (flag) { flag = false; destroy }
        let b = ins_load(GIR_T_I8, c.val, false);
        let v = emit(GIR_ICMP, GIR_T_I1, GIR_NE, 0, GIR_T_I8, b, c_i8(0), 0);
        let d = new_block();
        skip = new_block();
        condbr(v, d, skip);
        start_block(d);
        ins_store(GIR_T_I8, c_i8(0), c.val, false);
    }
    if c.kind == 2 {
        let fg = func_global(c.fsym);
        let addr = var_addr(c.sym);
        let s = m_opnds.len as! u32;
        op_ref(addr);
        op_imm(0);
        call_eh(GIR_T_VOID, 0, gref(fg), s, 1, sym_may_throw(c.fsym));
    } else if c.kind == CL_STMT {
        gen_stmt(c.node);
    } else if c.kind == CL_ENDCATCH {
        let s = m_opnds.len as! u32;
        call_eh(GIR_T_VOID, 0, gref(libfn("__cxa_end_catch")), s, 0, true);
    }
    if skip != NONE {
        if has_insert() { br(skip); }
        start_block(skip);
    }
    eh_top = saved;
}

// ------------------------------------------------------------ calls

// Can a call of function s throw? (Not: noexcept functions, builtins.)
fn sym_may_throw(s: i64) -> bool {
    if s < 0 { return true; }
    if syms[s].kind == SK_BUILTIN { return false; }
    return !cxl_has(s, CXL_NOUNWIND);
}

// A call (operands opnds[s..s + 2n)) that is an invoke when it may throw
// inside an EH scope; the normal path continues in a new block.
fn call_eh(rt: u32, fl: u32, callee: u32, s: u32, n: u32, may_throw: bool) -> u32 {
    if !may_throw || eh_top < 0 || !eh_on() || !has_insert() { return emit(GIR_CALL, rt, 0, fl, 0, callee, s, n); }
    let lp = eh_lpad();
    op_blk(lp);
    let r = emit(GIR_CALL, rt, 0, fl | IF_INVOKE, 0, callee, s, n);
    let nb = new_block();
    br(nb);
    start_block(nb);
    return r;
}

// The landing pad of the current EH state (made on first use).
fn eh_lpad() -> u32 {
    let e = eh_top;
    if eh_ents[e].lp != NONE { return eh_ents[e].lp; }
    let lp = new_block();
    eh_ents[e].lp = lp;
    f_eh = true;
    // the action list (clang's EmitLandingPad)
    let a0 = eh_acts.len;
    var has_cleanup = false;
    var catch_all = false;
    var x = e;
    while x >= 0 && !catch_all {
        let E = eh_ents[x];
        if E.kind == EK_CLEANUP {
            has_cleanup = true;
        } else if E.kind == EK_TERM {
            catch_all = true;
        } else {
            if E.used == 0 {
                // the handlers are reachable: their blocks
                eh_ents[x].used = 1;
                for h in E.nh { eh_hs[E.h0 + h].blk = new_block(); }
            }
            for h in E.nh {
                let ti = eh_hs[E.h0 + h].ti;
                if ti < 0 { catch_all = true; break; }
                let k = eh_type_index(ti);
                var dup = false;
                for j in a0..eh_acts.len { if eh_acts[j] == k { dup = true; } }
                if !dup { eh_acts.push(k); }
            }
        }
        x = E.parent as i64;
    }
    if catch_all { eh_acts.push(eh_type_index(-1)); }
    else if has_cleanup && eh_acts.len > a0 { eh_acts.push(0); }
    eh_ents[e].acts = a0 as! u32;
    eh_ents[e].nacts = (eh_acts.len - a0) as! u32;
    eh_pending.push(e * 2);
    return lp;
}

// The type index (1-based) of typeinfo variable ti (-1: catch-all).
fn eh_type_index(ti: i64) -> u32 {
    for k, i in eh_tsyms { if k == ti { return (i + 1) as! u32; } }
    eh_tsyms.push(ti);
    return eh_tsyms.len as! u32;
}

// The dispatch block of entry e (-1: resume).
fn eh_disp(e: i64) -> u32 {
    if e < 0 {
        if eh_resume == NONE { eh_resume = new_block(); eh_pending.push(-1); }
        return eh_resume;
    }
    if eh_ents[e].disp == NONE {
        eh_ents[e].disp = new_block();
        eh_pending.push(e * 2 + 1);
    }
    return eh_ents[e].disp;
}

fn exn_slot() -> u32 {
    if eh_exn_slot == NONE { eh_exn_slot = alloca(8, 8); }
    return eh_exn_slot;
}
fn sel_slot() -> u32 {
    if eh_sel_slot == NONE { eh_sel_slot = alloca(4, 4); }
    return eh_sel_slot;
}

// The landing pads and dispatch blocks of the function (at its end).
fn eh_fn_end() {
    if !f_eh { return; }
    if has_insert() { emit_term(GIR_UNREACHABLE, 0, 0, 0); }
    let saved_top = eh_top;
    var i = 0;
    while i < eh_pending.len {
        let p = eh_pending[i];
        i++;
        if p == -1 {
            start_block(eh_resume);
            let exn = ins_load(GIR_T_PTR, exn_slot(), false);
            let c = libcall1("_Unwind_Resume", GIR_T_VOID, exn);
            f_insts[c].flags = f_insts[c].flags | (IF_NORETURN as! u16);
            emit_term(GIR_UNREACHABLE, 0, 0, 0);
            continue;
        }
        let e = p / 2;
        let E = eh_ents[e];
        if p % 2 == 0 {
            // the landing pad
            start_block(E.lp);
            let s = m_opnds.len as! u32;
            for j in E.nacts { op_imm(eh_acts[E.acts + j]); }
            let lt = ty_pair(GIR_T_PTR, GIR_T_I32, 8);
            let l = emit(GIR_LANDINGPAD, lt, 0, 0, 0, s, E.nacts, 0);
            let exn = emit(GIR_EXTRACTVALUE, GIR_T_PTR, 0, 0, 0, l, 0, 0);
            ins_store(GIR_T_PTR, exn, exn_slot(), false);
            let sel = emit(GIR_EXTRACTVALUE, GIR_T_I32, 0, 0, 0, l, 8, 0);
            ins_store(GIR_T_I32, sel, sel_slot(), false);
            br(eh_disp(e));
            continue;
        }
        // the dispatch block
        start_block(E.disp);
        if E.kind == EK_CLEANUP {
            cleanup_code(E.c, E.parent as i64);
            if has_insert() { br(eh_disp(E.parent as i64)); }
        } else if E.kind == EK_TERM {
            let exn = ins_load(GIR_T_PTR, exn_slot(), false);
            need_terminate_fn = true;
            let c = libcall1("__clang_call_terminate", GIR_T_VOID, exn);
            f_insts[c].flags = f_insts[c].flags | (IF_NORETURN as! u16);
            emit_term(GIR_UNREACHABLE, 0, 0, 0);
        } else {
            let sel = ins_load(GIR_T_I32, sel_slot(), false);
            var all = false;
            for h in E.nh {
                let H = eh_hs[E.h0 + h];
                if H.ti < 0 { br(H.blk); all = true; break; }
                let k = eh_type_index(H.ti);
                let cmp = emit(GIR_ICMP, GIR_T_I1, GIR_EQ, 0, GIR_T_I32, sel, c_i32(k as i64), 0);
                let nb = new_block();
                condbr(cmp, H.blk, nb);
                start_block(nb);
            }
            if !all { br(eh_disp(E.parent as i64)); }
        }
    }
    eh_top = saved_top;
}

// The EH table record of the function just finished (fi).
fn eh_fn_table(fi: u32) {
    if !f_eh { return; }
    if eh_pers == NONE {
        let g = libfn("__gxx_personality_v0");
        eh_pers = addr_holder("DW.ref.__gxx_personality_v0", g, GF_WEAK | GF_HIDDEN);
        set_comdat(eh_pers, comdat_named("DW.ref.__gxx_personality_v0", eh_pers));
    }
    let t0 = m_opnds.len as! u32;
    for ti in eh_tsyms {
        if ti < 0 { m_opnds.push(NONE); continue; }
        let r = eh_stubs.get(ti as u64);
        if r { m_opnds.push(r); continue; }
        var nm: u8[>..] = [];
        nm.append(".L");
        nm.append(ident_text(link_name(ti) as i64));
        nm.append(".DW.stub");
        let st = addr_holder(nm, var_global(ti), GF_INTERNAL);
        eh_stubs.insert(ti as u64, st);
        m_opnds.push(st);
    }
    m_ehs.push(Eh { func: fi, personality: eh_pers, ttypes: t0, n_ttypes: eh_tsyms.len as! u32, specs: m_data.len as! u32, n_specs: 0 });
}

// A pointer variable holding the address of global `target`.
fn addr_holder(name: const u8[:], target: u32, flags: u32) -> u32 {
    let g = new_global(name, G_VAR, flags | GF_DEFINED | GF_LOCALREF, 8);
    ensure_glob_tables();
    glob_gen[g].state = 2;
    m_globals[g].size = 8;
    let at = m_data.len;
    data_grow(8);
    m_globals[g].data = at as! u32;
    m_drelocs.push(DataReloc { owner: g, offset: 0, target: target, kind: DR_ABS64, addend: 0, blk: 0, blk2: 0 });
    m_globals[g].flags = m_globals[g].flags | GF_RELOCS;
    return g;
}

// ------------------------------------------------------------ comdats

fn comdat_named(name: const u8[:], sig: u32) -> u32 {
    let id = intern(name);
    let r = cdnames.get(id as u64);
    if r { return r; }
    let c = m_comdats.len as! u32;
    m_comdats.push(Comdat { name: add_name(name), name_len: name.len as! u32, sig: sig, kind: CD_ANY });
    cdnames.insert(id as u64, c);
    return c;
}

fn set_comdat(g: u32, c: u32) {
    while m_gcomdat.len < m_globals.len { m_gcomdat.push(NONE); }
    m_gcomdat[g] = c;
}

// The aliases of C++ symbols (a complete-object constructor or destructor
// that is its base-object variant): emitted with their target.
fn cx_aliases() {
    ensure_glob_tables();
    ensure_sym_tables();
    for s in cxl.len {
        let t = cxl[s].alias;
        if t < 0 { continue; }
        let tg = sym_gen[t].glob;
        if tg == NONE || glob_gen[tg].state != 2 || m_globals[tg].flags & GF_DEFINED == 0 { continue; }
        let g = global_by_name(link_name(s), true);
        ensure_glob_tables();
        m_globals[g].kind = G_ALIAS;
        m_globals[g].func = tg;
        m_globals[g].aux = 0;
        m_globals[g].flags = (m_globals[tg].flags & (GF_WEAK | GF_HIDDEN | GF_INTERNAL | GF_LOCALREF)) | GF_DEFINED;
        m_globals[g].align = m_globals[tg].align;
        glob_gen[g].state = 2;
    }
}

// The comdats of the C++ symbols' globals (at the end of the unit), and
// clang's .data.rel.ro for vtables and typeinfo outside comdats.
fn cx_comdats() {
    ensure_glob_tables();
    for g in m_globals.len {
        let s = glob_gen[g].sym;
        if s < 0 || s >= cxl.len { continue; }
        if (cxl[s].flags as i64) & CXL_RELRO != 0 && m_globals[g].flags & GF_DEFINED != 0 && m_globals[g].kind == G_VAR {
            m_globals[g].flags = m_globals[g].flags | GF_CONST;
            if (cxl[s].flags as i64) & CXL_COMDAT == 0 && m_globals[g].flags & GF_RELOCS != 0 {
                m_globals[g].section = get_section(".data.rel.ro", SF_WRITE, 1);
            }
        }
        if (cxl[s].flags as i64) & CXL_COMDAT == 0 { continue; }
        if m_globals[g].flags & GF_DEFINED == 0 || m_globals[g].kind == G_ALIAS { continue; }
        let key = if cxl[s].comdat != 0 { cxl[s].comdat } else { link_name(s) };
        let nm = ident_text(key as i64);
        let sigr = gmap.get(gk(GM_NAMEGLOB, key));
        var sig = NONE;
        if sigr { sig = sigr; }
        set_comdat(g as! u32, comdat_named(nm, sig));
    }
    if m_gcomdat.len > 0 { while m_gcomdat.len < m_globals.len { m_gcomdat.push(NONE); } }
}

// __clang_call_terminate(exn): __cxa_begin_catch(exn); std::terminate()
// (linkonce_odr hidden, as clang emits it).
fn emit_terminate_fn() {
    if !need_terminate_fn { return; }
    let g = global_by_name(intern("__clang_call_terminate"), true);
    ensure_glob_tables();
    if glob_gen[g].state == 2 { return; }
    glob_gen[g].state = 2;
    m_globals[g].kind = G_FUNC;
    m_globals[g].flags = GF_DEFINED | GF_WEAK | GF_HIDDEN | GF_LOCALREF;
    fn_begin();
    f_arg_types.clear();
    f_arg_types.push(GIR_T_PTR);
    let run = m_opnds.len as! u32;
    op_imm(GIR_T_PTR);
    op_imm(0);
    libcall1("__cxa_begin_catch", GIR_T_PTR, KARG | 0);
    let s = m_opnds.len as! u32;
    let c = emit(GIR_CALL, GIR_T_VOID, 0, IF_NORETURN, 0, gref(libfn("_ZSt9terminatev")), s, 0);
    emit_term(GIR_UNREACHABLE, 0, 0, 0);
    fn_finish(g, 4 << FN_ALIGN_SHIFT, 1, run, GIR_T_VOID, 0);
    set_comdat(g, comdat_named("__clang_call_terminate", g));
}

// ------------------------------------------------------------ statements

// N_XPUSH: a cleanup for the rest of the enclosing block.
fn gen_xpush(n: u32) {
    let nd = nodes[n];
    let op = nd.op as i64;
    var fl: u8 = 0;
    if op & XP_EHONLY != 0 {
        if !eh_on() { return; }
        fl = CLF_EHONLY as! u8;
    }
    if op & XP_TERMINATE != 0 {
        if eh_on() { push_cl(Cleanup { kind: CL_TERM, val: 0, sym: -1, fsym: -1 }); }
        return;
    }
    if op & XP_CALL != 0 {
        push_cl(Cleanup { kind: 2, val: 0, sym: nd.a as i64, fsym: nd.c as i64, flags: fl });
    } else {
        push_cl(Cleanup { kind: CL_STMT, val: 0, sym: -1, fsym: -1, flags: fl, node: nd.a });
    }
}

// try { body } handlers.
recursive fn gen_xtry(n: u32) {
    let nd = nodes[n];
    if !eh_on() { gen_stmt(nd.a); return; }
    let h0 = eh_hs.len;
    for i in nd.c {
        let h = nlist[nd.v + i];
        let ti = if nodes[h].c != 0 { nodes[h].c as i64 } else { -1 };
        eh_hs.push(EhHandler { blk: NONE, ti: ti });
    }
    push_cleanup_scope();
    push_cl(Cleanup { kind: CL_TRY, val: 0, sym: -1, fsym: -1, node: n });
    let e = eh_top;
    eh_ents[e].h0 = h0 as! u32;
    eh_ents[e].nh = nd.c;
    gen_stmt(nd.a);
    pop_cleanup_scope(true);
    if eh_ents[e].used == 0 { return; }
    let cont = new_block();
    if has_insert() { br(cont); }
    for i in nd.c {
        start_block(eh_hs[h0 + i].blk);
        gen_handler(nlist[nd.v + i]);
        if has_insert() { br(cont); }
    }
    start_block(cont);
}

var cur_xexn: u32 = NONE;       // the slot of the enclosing handler's adjusted exception pointer

recursive fn gen_handler(h: u32) {
    let hd = nodes[h];
    set_loc(hd.loc);
    let saved = cur_xexn;
    cur_xexn = alloca(8, 8);
    push_cleanup_scope();
    let exn = ins_load(GIR_T_PTR, exn_slot(), false);
    let init = hd.v as! u32;
    if (hd.op as i64) & XC_COPY != 0 {
        // a class copied by its constructor (in a terminate scope), then begin_catch
        let p = libcall1("__cxa_get_exception_ptr", GIR_T_PTR, exn);
        ins_store(GIR_T_PTR, p, cur_xexn, false);
        push_cleanup_scope();
        push_cl(Cleanup { kind: CL_TERM, val: 0, sym: -1, fsym: -1 });
        if init != 0 { gen_stmt(init); }
        pop_cleanup_scope(true);
        libcall1("__cxa_begin_catch", GIR_T_PTR, exn);
        push_cl(Cleanup { kind: CL_ENDCATCH, val: 0, sym: -1, fsym: -1 });
    } else {
        let p = libcall1("__cxa_begin_catch", GIR_T_PTR, exn);
        ins_store(GIR_T_PTR, p, cur_xexn, false);
        push_cl(Cleanup { kind: CL_ENDCATCH, val: 0, sym: -1, fsym: -1 });
        if init != 0 { gen_stmt(init); }
    }
    gen_stmt(hd.b);
    if (hd.op as i64) & XC_RETHROW != 0 && has_insert() {
        // the end of a constructor's or destructor's function-try-block handler rethrows
        let s = m_opnds.len as! u32;
        call_eh(GIR_T_VOID, IF_NORETURN, gref(libfn("__cxa_rethrow")), s, 0, true);
        emit_term(GIR_UNREACHABLE, 0, 0, 0);
    }
    pop_cleanup_scope(true);
    cur_xexn = saved;
}

// N_XEXN: the handler's adjusted exception pointer.
fn ex_xexn() -> u32 {
    if cur_xexn == NONE { return c_null(); }
    return ins_load(GIR_T_PTR, cur_xexn, false);
}

// N_XTEMP: the temporary's address (constructed, its destructor pushed).
recursive fn ex_xtemp(n: u32) -> u32 {
    let nd = nodes[n];
    let s = nd.b as i64;
    ensure_sym_tables();
    let p = alloca(type_size(nd.ty), type_align(nd.ty));
    sym_gen[s].addr = p;
    var flag = NONE;
    if nd.c != 0 && (nd.op as i64) & XT_COND != 0 {
        flag = alloca(1, 1);
        entry_store(GIR_T_I8, c_i8(0), flag);
    }
    if nd.a != 0 { ex_ignore(nd.a); }
    if nd.c != 0 && has_insert() {
        var fl: u8 = 0;
        if (nd.op as i64) & XT_EXTENDED != 0 { fl = fl | (CLF_EXT as! u8); }
        if flag != NONE {
            fl = fl | (CLF_COND as! u8);
            ins_store(GIR_T_I8, c_i8(1), flag, false);
        }
        push_cl(Cleanup { kind: 2, val: flag, sym: s, fsym: nd.c as i64, flags: fl });
    }
    return p;
}

// ------------------------------------------------------------ conditions

// Branches on condition e; a condition with temporaries is evaluated, its
// temporaries destroyed, then branched on.
recursive fn cond_br(e: u32, t: u32, f: u32) {
    if opt_cxx && n_xtemps > 0 && xt_in(e) {
        push_cleanup_scope();
        let v = ex_bool(e);
        pop_stmt_scope();
        if has_insert() { condbr(v, t, f); }
        return;
    }
    ex_cond(e, t, f);
}

// Does expression n contain a temporary with a destructor?
recursive fn xt_in(n: u32) -> bool {
    if n == 0 { return false; }
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_XTEMP { return nd.c != 0 || xt_in(nd.a); }
    if k == N_UNARY || k == N_CAST || k == N_ICAST || k == N_MEMBER || k == N_COMPLIT || k == N_VAARG || k == N_SWIZZLE { return xt_in(nd.a); }
    if k == N_BINARY || k == N_ASSIGN || k == N_INDEX { return xt_in(nd.a) || xt_in(nd.b); }
    if k == N_COND { return xt_in(nd.a) || xt_in(nd.b) || xt_in(nd.c); }
    if k == N_CALL {
        if xt_in(nd.a) { return true; }
        for i in nd.c { if xt_in(nlist[nd.v + i]) { return true; } }
        return false;
    }
    if k == N_INITLIST || k == N_BUILTIN {
        for i in nd.c { if xt_in(nlist[nd.v + i]) { return true; } }
        return false;
    }
    if k == N_STMTEXPR { return true; }
    return false;
}
