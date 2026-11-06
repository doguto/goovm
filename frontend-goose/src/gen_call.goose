// goosecc B2: calls, returns and va_arg, with the SysV classification of
// gen_abi.goose: coerced aggregates are loaded and stored in their parts,
// memory-class arguments are byval copies, memory-class results come back
// through a hidden sret pointer. va_arg is lowered inline as clang does
// (X86_64ABIInfo::EmitVAArg): register save area or overflow area.

namespace gen;

import std;
import .common;
import .types;
import .ast;
import .sema;
import .builtins;

var call_vals: u32[>..<] = [];     // (value, ABI word) pairs of calls being built

fn is_returns_twice(name: const u8[:]) -> bool {
    return name == "setjmp" || name == "_setjmp" || name == "sigsetjmp" || name == "__sigsetjmp" || name == "savectx" ||
        name == "vfork" || name == "getcontext" || name == "__builtin_setjmp_dummy";
}

// The function symbol a callee expression names directly, or -1.
fn direct_callee(c: u32) -> i64 {
    var n = c;
    loop {
        let nd = nodes[n];
        if (nd.kind == N_ICAST || nd.kind == N_CAST) && (nd.op == CK_FUNC2PTR || nd.op == CK_NOOP || nd.op == CK_BITCAST || nd.op == CK_BUILTIN2PTR) {
            n = nd.a;
            continue;
        }
        if nd.kind == N_UNARY && (nd.op == U_ADDR || nd.op == U_EXTENSION) { n = nd.a; continue; }
        if nd.kind == N_DECLREF {
            let s = nd.a as i64;
            if syms[s].kind == SK_FUNC || syms[s].kind == SK_BUILTIN { return s; }
        }
        return -1;
    }
}

// Pushes the GIR arguments for argument node `arg` with ABI a.
recursive fn push_arg(arg: u32, a: Abi) {
    let q = nty(arg);
    if a.kind == AK_IGNORE { ex_ignore(arg); return; }
    if a.kind == AK_DIRECT {
        var v = ex_val(arg);
        let t = vtype(v);
        if a.t0 != t && v != NONE {
            if tkind(a.t0) == TK_INT && tkind(t) == TK_INT { v = int_cast(v, t, a.t0, is_integer(q) && is_signed(q)); }
            else if tsize(a.t0) == tsize(t) { v = ins_bitcast(v, a.t0); }
        }
        if a.ext != 0 && tkind(vtype(v)) == TK_INT && tbits(vtype(v)) < 32 { v = int_cast(v, vtype(v), GIR_T_I32, true); }
        call_vals.push(v);
        call_vals.push(0);
        return;
    }
    if a.kind == AK_BYVAL {
        // a copy the callee owns (the back-end copies it into the argument area)
        var p: u32 = 0;
        if is_lvalue(arg) || (nkind(arg) == N_ICAST && nodes[arg].op == CK_LVAL2RVAL) {
            let src_n = if is_lvalue(arg) { arg } else { nodes[arg].a };
            let l = ex_lv(src_n);
            p = alloca(type_size(q), if a.align > type_align(q) as u32 { a.align as i64 } else { type_align(q) });
            mem_copy(p, l.addr, type_size(q), l.vol);
        } else {
            p = alloca(type_size(q), if a.align > type_align(q) as u32 { a.align as i64 } else { type_align(q) });
            store_any(q, arg, p);
        }
        call_vals.push(p);
        call_vals.push(abi_word(a));
        return;
    }
    // coerced parts loaded from the object
    var p: u32 = 0;
    if vkind(q) == VK_SCALAR && a.n == 1 && !is_lvalue(arg) && tsize(a.t0) == type_size(q) as u32 && a.off0 == 0 {
        // a vector passed as an integer / double of its size
        let v = ex_val(arg);
        call_vals.push(ins_bitcast(v, a.t0));
        call_vals.push(0);
        return;
    }
    if is_lvalue(arg) || (nkind(arg) == N_ICAST && nodes[arg].op == CK_LVAL2RVAL && vkind(q) != VK_SCALAR) {
        let src_n = if is_lvalue(arg) { arg } else { nodes[arg].a };
        p = ex_lv(src_n).addr;
    } else {
        p = alloca(type_size(q) + 16, if type_align(q) > 8 { type_align(q) } else { 8 });
        store_any(q, arg, p);
    }
    if a.tmp != 0 {
        let t = alloca(16, 8);
        mem_copy(t, p, type_size(q), false);
        p = t;
    }
    call_vals.push(ins_load(a.t0, gep(p, a.off0 as i64), false));
    call_vals.push(0);
    if a.n == 2 {
        call_vals.push(ins_load(a.t1, gep(p, a.off1 as i64), false));
        call_vals.push(0);
    }
}

// The ABI of argument i of a call with nargs arguments (fixed parameters
// from the prototype, the rest by their promoted types).
var cabis: Abi[>..<] = [];

recursive fn ex_call(n: u32, dst: u32) -> u32 {
    let nd = nodes[n];
    let callee = nd.a;
    let pt = nty(callee);
    var ft = pt;
    if kind_of(ft) == TY_POINTER { ft = tbase(ft); }
    let fty = types[ft >> 4];
    let noproto = fty.flags & TF_NOPROTO != 0;
    let variadic = fty.flags & TF_VARIADIC != 0;
    let nargs = nd.c as i64;
    let rq = unqual(fty.base);
    let ds = direct_callee(callee);
    if ds >= 0 {
        let b = builtin_lib_call(ds, n, dst);
        if b != KEEP_CALL { return b; }
    }
    // the ABI of the result and the arguments
    let amark = cabis.len;
    var ra = abi_ignore();
    if !noproto && !variadic {
        let ai = fn_abi(ft);
        ra = abis[ai];
        for i in nargs {
            if i < fty.n { cabis.push(abis[ai + 1 + i]); } else { cabis.push(abi_ignore()); }
        }
    } else {
        ra = ret_abi(rq);
        abi_start(ra);
        for i in nargs {
            let an = nlist[nd.v + i];
            var aq = nty(an);
            if !noproto && i < fty.n { aq = unqual(tparams[fty.extra + i]); }
            cabis.push(arg_abi(aq));
        }
    }
    // the callee (evaluated first, as clang does)
    var cref: u32 = 0;
    var cname: const u8[:] = "";
    if ds >= 0 {
        cref = gref(func_global(ds));
        cname = ident_text(link_name(ds) as i64);
        if is_returns_twice(cname) { f_flags = f_flags | FN_RETURNS_TWICE; }
    } else {
        cref = ex_val(callee);
    }
    // a memory-class result goes to the destination (or a temporary)
    let mark = call_vals.len;
    var sret: u32 = NONE;
    if ra.kind == AK_SRET {
        sret = if dst != NONE { dst } else { alloca(type_size(rq), type_align(rq)) };
        call_vals.push(sret);
        call_vals.push(ABI_SRET);
    }
    for i in nargs {
        let an = nlist[nd.v + i];
        push_arg(an, cabis[amark + i]);
    }
    cabis.resize(amark);
    // the result type, then the run of operands
    let rt = if ra.kind == AK_SRET { GIR_T_VOID } else { ret_gir_type(ra) };
    set_loc(nd.loc);
    let s = m_opnds.len as! u32;
    let cnt = (call_vals.len - mark) / 2;
    for i in cnt {
        op_ref(call_vals[mark + 2 * i]);
        op_imm(call_vals[mark + 2 * i + 1]);
    }
    call_vals.resize(mark);
    var fl: u32 = 0;
    if noproto || variadic { fl = fl | IF_VARARG; }
    let noret = fty.flags & TF_NORETURN != 0 || (ds >= 0 && syms[ds].flags & SF_NORETURN != 0);
    if noret { fl = fl | IF_NORETURN; }
    let r = emit(GIR_CALL, rt, 0, fl, 0, cref, s, cnt as! u32);
    var res: u32 = NONE;
    if ra.kind == AK_DIRECT {
        res = r;
        // a bool result arrives as i1
        if vkind(rq) == VK_SCALAR && vty(rq) != rt && rt != GIR_T_VOID {
            if tsize(vty(rq)) == tsize(rt) { res = ins_bitcast(r, vty(rq)); }
        }
    } else if ra.kind == AK_COERCE {
        let vk = vkind(rq);
        if vk == VK_SCALAR && ra.n == 1 && ra.off0 == 0 && tsize(ra.t0) == type_size(rq) as u32 {
            res = ins_bitcast(r, vty(rq));
        } else {
            var p = dst;
            if p == NONE || ra.tmp != 0 || vk != VK_AGG { p = alloca(type_size(rq) + 16, if type_align(rq) > 8 { type_align(rq) } else { 8 }); }
            if ra.n == 1 {
                ins_store(ra.t0, r, gep(p, ra.off0 as i64), false);
            } else {
                let x = emit(GIR_EXTRACTVALUE, ra.t0, 0, 0, 0, r, 0, 0);
                let y = emit(GIR_EXTRACTVALUE, ra.t1, 0, 0, 0, r, ra.off1, 0);
                ins_store(ra.t0, x, p, false);
                ins_store(ra.t1, y, gep(p, ra.off1 as i64), false);
            }
            if vk == VK_AGG && p != dst && dst != NONE { mem_copy(dst, p, type_size(rq), false); }
            if vk == VK_SCALAR { res = load_c(rq, p, false); }
            if vk == VK_COMPLEX && dst != NONE { mem_copy(dst, p, type_size(rq), false); }
        }
    }
    if noret { emit_term(GIR_UNREACHABLE, 0, 0, 0); }
    if res == NONE && vkind(rq) == VK_SCALAR { return c_zero(vty(rq)); }
    return res;
}

// ------------------------------------------------------------ return

recursive fn gen_return(n: u32) {
    let nd = nodes[n];
    let e = nd.a;
    let a = f_ret;
    if a.kind == AK_SRET {
        if e != 0 {
            let k = nkind(e);
            if k == N_CALL || k == N_STMTEXPR || k == N_COND {
                ex_agg(e, f_sret);
            } else {
                assign_agg(f_sret, f_ret_q, e);
            }
        }
        run_call_cleanups();
        if has_insert() { emit_term(GIR_RET, f_sret, 0, 0); }
        return;
    }
    if a.kind == AK_IGNORE {
        if e != 0 { ex_ignore(e); }
        run_call_cleanups();
        if has_insert() { emit_term(GIR_RET, NONE, 0, 0); }
        return;
    }
    if a.kind == AK_DIRECT {
        var v = c_zero(a.t0);
        if e != 0 {
            if vkind(nty(e)) == VK_SCALAR { v = ex_val(e); } else { ex_ignore(e); }
        }
        if !has_insert() { return; }
        let t = vtype(v);
        if t != a.t0 && tsize(t) == tsize(a.t0) && tkind(t) != tkind(a.t0) { v = ins_bitcast(v, a.t0); }
        if a.ext != 0 && tbits(vtype(v)) < 32 { v = int_cast(v, vtype(v), GIR_T_I32, true); }
        run_call_cleanups();
        if has_insert() { emit_term(GIR_RET, v, 0, 0); }
        return;
    }
    // coerced: load the parts from the object
    let q = f_ret_q;
    var p: u32 = NONE;
    if e == 0 {
        p = alloca(type_size(q) + 16, 8);
    } else if vkind(q) == VK_SCALAR && a.n == 1 && a.off0 == 0 && tsize(a.t0) == type_size(q) as u32 {
        let v = ex_val(e);
        run_call_cleanups();
        if has_insert() { emit_term(GIR_RET, ins_bitcast(v, a.t0), 0, 0); }
        return;
    } else if is_lvalue(e) || (nkind(e) == N_ICAST && nodes[e].op == CK_LVAL2RVAL && vkind(q) == VK_AGG) {
        let src_n = if is_lvalue(e) { e } else { nodes[e].a };
        p = ex_lv(src_n).addr;
    } else {
        p = alloca(type_size(q) + 16, if type_align(q) > 8 { type_align(q) } else { 8 });
        store_any(q, e, p);
    }
    if !has_insert() { return; }
    if a.tmp != 0 {
        let t = alloca(16, 8);
        mem_copy(t, p, type_size(q), false);
        p = t;
    }
    var v: u32 = 0;
    if a.n == 1 { v = ins_load(a.t0, gep(p, a.off0 as i64), false); }
    else {
        let x = ins_load(a.t0, p, false);
        let y = ins_load(a.t1, gep(p, a.off1 as i64), false);
        let st = ty_pair(a.t0, a.t1, a.off1);
        let z = c_zero(st);
        let v1 = emit(GIR_INSERTVALUE, st, 0, 0, 0, z, x, 0);
        v = emit(GIR_INSERTVALUE, st, 0, 0, 0, v1, y, a.off1);
    }
    run_call_cleanups();
    if has_insert() { emit_term(GIR_RET, v, 0, 0); }
}

// ------------------------------------------------------------ va_arg

// The address of the next variadic argument of type q (X86_64ABIInfo::EmitVAArg).
recursive fn va_arg_addr(n: u32) -> u32 {
    let nd = nodes[n];
    let q = unqual(nd.ty);
    // the va_list: an array (a local va_list) or a pointer (a va_list parameter)
    var ap: u32 = 0;
    if is_array(nty(nd.a)) { ap = ex_lv(nd.a).addr; } else { ap = ex_val(nd.a); }
    abi_free_int = 0;
    abi_free_sse = 8;
    let lo, hi = classify(q, 0);
    var a = abi_ignore();
    var ni: i64 = 0;
    var ns: i64 = 0;
    if lo == CL_MEM || lo == CL_X87 || lo == CL_CX87 {
        a = byval(q);
    } else {
        let a2, x, y = abi_of_classes(q, lo, hi, false);
        a = a2;
        ni = x;
        ns = y;
    }
    if a.kind == AK_IGNORE { return alloca(1, 1); }
    if ni == 0 && ns == 0 { return va_from_mem(ap, q); }
    let size = type_size(q);
    let tal = type_align(q);
    let gp_p = ap;
    let fp_p = gep(ap, 4);
    var inregs: u32 = c_true();
    var gp: u32 = NONE;
    var fp: u32 = NONE;
    if ni > 0 {
        gp = ins_load(GIR_T_I32, gp_p, false);
        inregs = ins_icmp(GIR_ULE, GIR_T_I32, gp, c_i32(48 - ni * 8));
    }
    if ns > 0 {
        fp = ins_load(GIR_T_I32, fp_p, false);
        let fits = ins_icmp(GIR_ULE, GIR_T_I32, fp, c_i32(176 - ns * 16));
        inregs = if ni > 0 { ins_bin(GIR_AND, GIR_T_I1, inregs, fits) } else { fits };
    }
    let in_reg = new_block();
    let in_mem = new_block();
    let end = new_block();
    condbr(inregs, in_reg, in_mem);
    start_block(in_reg);
    let rsa = ins_load(GIR_T_PTR, gep(ap, 16), false);
    var reg_addr: u32 = 0;
    if ni > 0 && ns > 0 {
        // mixed: assemble the two eightbytes in a temporary
        let tmp = alloca(if size > 16 { size } else { 16 }, if tal > 8 { tal } else { 8 });
        let gpa = gep_idx(rsa, 0, int_cast(gp, GIR_T_I32, GIR_T_I64, false), 1);
        let fpa = gep_idx(rsa, 0, int_cast(fp, GIR_T_I32, GIR_T_I64, false), 1);
        let lo_fp = tcls(a.t0) == C_FP || tkind(a.t0) == TK_VECTOR;
        let lo_addr = if lo_fp { fpa } else { gpa };
        let hi_addr = if lo_fp { gpa } else { fpa };
        let x = ins_load(a.t0, lo_addr, false);
        ins_store(a.t0, x, tmp, false);
        let y = ins_load(a.t1, hi_addr, false);
        ins_store(a.t1, y, gep(tmp, a.off1 as i64), false);
        reg_addr = tmp;
    } else if ni > 0 || ns == 1 {
        let off = if ni > 0 { gp } else { fp };
        let base = gep_idx(rsa, 0, int_cast(off, GIR_T_I32, GIR_T_I64, false), 1);
        let regsize = if ni > 0 { ni * 8 } else { 16 };
        if a.kind == AK_COERCE && (a.off0 == 8 || regsize < size) {
            let tmp = alloca(if size > 16 { size } else { 16 }, if tal > 8 { tal } else { 8 });
            let v = ins_load(a.t0, base, false);
            ins_store(a.t0, v, gep(tmp, a.off0 as i64), false);
            reg_addr = tmp;
        } else if ni > 0 && tal > 8 {
            let tmp = alloca(size, tal);
            mem_copy(tmp, base, size, false);
            reg_addr = tmp;
        } else {
            reg_addr = base;
        }
    } else {
        // two SSE eightbytes, 16 bytes apart in the save area
        let tmp = alloca(if size > 16 { size } else { 16 }, if tal > 8 { tal } else { 8 });
        let base = gep_idx(rsa, 0, int_cast(fp, GIR_T_I32, GIR_T_I64, false), 1);
        let t0 = if a.kind == AK_COERCE { a.t0 } else { GIR_T_F64 };
        let t1 = if a.kind == AK_COERCE && a.n == 2 { a.t1 } else { GIR_T_F64 };
        let x = ins_load(t0, base, false);
        ins_store(t0, x, tmp, false);
        let y = ins_load(t1, gep(base, 16), false);
        ins_store(t1, y, gep(tmp, 8), false);
        reg_addr = tmp;
    }
    if ni > 0 { ins_store(GIR_T_I32, ins_bin(GIR_ADD, GIR_T_I32, gp, c_i32(ni * 8)), gp_p, false); }
    if ns > 0 { ins_store(GIR_T_I32, ins_bin(GIR_ADD, GIR_T_I32, fp, c_i32(ns * 16)), fp_p, false); }
    let p_reg = cur_blk;
    br(end);
    start_block(in_mem);
    let mem_addr = va_from_mem(ap, q);
    let p_mem = cur_blk;
    br(end);
    start_block(end);
    return phi2(GIR_T_PTR, reg_addr, p_reg, mem_addr, p_mem);
}

fn va_from_mem(ap: u32, q: u32) -> u32 {
    let oap = gep(ap, 8);
    var area = ins_load(GIR_T_PTR, oap, false);
    let al = type_align(q);
    if al > 8 {
        // round up to the alignment
        let i = ins_ptrtoint(area, GIR_T_I64);
        let a1 = ins_bin(GIR_ADD, GIR_T_I64, i, c_i64(al - 1));
        let a2 = ins_bin(GIR_AND, GIR_T_I64, a1, c_i64(0 - al));
        area = ins_inttoptr(a2);
    }
    let size = (type_size(q) + 7) / 8 * 8;
    let next = gep(area, size);
    ins_store(GIR_T_PTR, next, oap, false);
    return area;
}
