// goosecc B2: the lowering driver. Walks the translation unit, emits the
// definitions clang emits (external ones in source order, on-use ones
// as they are referenced), adds constructors, destructors and aliases,
// and hands the tables to the back-end (gir_codegen) in the same process.

namespace gen;

import std;
import os;
import .common;
import .types;
import .ast;
import .sema;
import .parse;
import .cx_gen_defs;
import .cx_eh;

// f80 values (also used as a 128-bit (lo, hi) pair) and their C helpers.
struct F80 { lo: u64, hi: u64 }

extern fn strtold(s: const u8[:]) -> F80 = "goosecc_strtold";
extern fn f64_to_f80(d: f64) -> F80 = "goosecc_f64_to_f80";
extern fn f80_to_f64(x: F80) -> f64 = "goosecc_f80_to_f64";
extern fn f80_to_f32_d(x: F80) -> f64 = "goosecc_f80_to_f32_d";
extern fn f80_to_f32bits(x: F80) -> u32 = "goosecc_f80_to_f32bits";
extern fn u64_to_f80(x: u64) -> F80 = "goosecc_u64_to_f80";
extern fn i64_to_f80(x: i64) -> F80 = "goosecc_i64_to_f80";
extern fn f80_to_i64(x: F80) -> i64 = "goosecc_f80_to_i64";
extern fn f80_arith(op: i64, a: F80, b: F80, prec: i64) -> F80 = "goosecc_f80_arith";
extern fn f80_round(x: F80, prec: i64) -> F80 = "goosecc_f80_round";
extern fn f80_to_i128_x(x: F80, signed: i64) -> F80 = "goosecc_f80_to_i128";
extern fn strtod_bits(s: const u8[:], prec: i64) -> u64 = "goosecc_strtod_bits";

fn f80_to_i128(x: F80, signed: bool) -> u64, u64 {
    let r = f80_to_i128_x(x, if signed { 1 } else { 0 });
    return r.lo, r.hi;
}

var lower_us: i64 = 0;

// Lowers the translation unit; false on errors.
fn lower_tu(main_file: const u8[:]) -> bool {
    ir_init();
    init_no_builtin();
    dbg_init(main_file);
    ensure_sym_tables();
    ensure_sym_gen();
    // G1: from here on the constant evaluator reads const variables, as
    // clang's does in CodeGen (sema.goose, fold_cvars)
    fold_cvars = true;
    cv_grow();
    if !opt_no_builtin {
        let sl = intern("strlen");
        let mc = intern("memchr");
        if !gmap.contains(gk(GM_NOBUILTIN, sl)) { fold_lib_strlen = sl as! u32; }
        if !gmap.contains(gk(GM_NOBUILTIN, mc)) { fold_lib_memchr = mc as! u32; }
    }
    let tu = nodes[tu_node];
    let cnt = tu.c as i64;
    // pass 1: definitions and initializers
    for i in cnt {
        let it = nlist[tu.v + i];
        let nd = nodes[it];
        if nd.kind == N_FUNCDEF {
            // its global is made when it is emitted or referenced: an unused
            // static or inline function leaves no symbol, as in clang
            let s = nd.a as i64;
            gmap.insert(gk(GM_DEFBY, link_name(s)), s as! u32);
        } else if nd.kind == N_DECL {
            let s = nd.a as i64;
            if syms[s].kind == SK_VAR {
                if nd.b != 0 { sym_gen[s].init = nd.b; sym_gen[s].decl = it; }
                if nd.b != 0 && cv_eligible(s) {
                    cvar_init[s] = nd.b;
                    cvar_decl[s] = it;
                }
            }
        }
    }
    // pass 2: what is emitted unconditionally, in source order
    for i in cnt {
        let it = nlist[tu.v + i];
        let nd = nodes[it];
        if nd.kind == N_FUNCDEF {
            let s = nd.a as i64;
            if !fn_emitted_def(s) { continue; }
            if syms[s].def as u32 != it { continue; }
            var always = (!is_internal_sym(s) && !fn_local_inline(s)) || sym_has_attr(s, AM_USED) || sym_has_attr(s, AM_CTOR) ||
                sym_has_attr(s, AM_DTOR);
            if opt_cxx && cxl_link(s) == LK_LINKONCE { always = false; }
            if !always { continue; }
            let g = func_global(s);
            if glob_gen[g].state == 0 {
                glob_gen[g].state = 1;
                work.push(g);
            }
        } else if nd.kind == N_DECL {
            let s = nd.a as i64;
            if syms[s].kind != SK_VAR || syms[s].flags & SF_FILESCOPE == 0 { continue; }
            if syms[s].flags & (SF_DEFINED | SF_TENTATIVE) == 0 { continue; }
            if is_internal_sym(s) && !sym_has_attr(s, AM_USED) { continue; }
            if opt_cxx && cxl_link(s) == LK_LINKONCE { continue; }
            let g = var_global(s);
            if glob_gen[g].state == 0 {
                glob_gen[g].state = 1;
                work.push(g);
            }
        } else if nd.kind == N_ASM {
            err_at(nd.loc, "goosecc: file-scope asm is not supported");
        }
    }
    // the targets of aliases are used
    for i in cnt {
        let nd = nodes[nlist[tu.v + i]];
        if nd.kind != N_DECL && nd.kind != N_FUNCDEF { continue; }
        let a = syms[nd.a].attr;
        if a == 0 || sym_attrs[a].alias_len == 0 { continue; }
        let off = sym_attrs[a].alias_off as i64;
        let tid = intern(strbytes[off..off + sym_attrs[a].alias_len]);
        for j in cnt {
            let it = nlist[tu.v + j];
            let td = nodes[it];
            if td.kind != N_DECL && td.kind != N_FUNCDEF { continue; }
            let ts = td.a as i64;
            if link_name(ts) != tid { continue; }
            if syms[ts].kind == SK_FUNC && syms[ts].def >= 0 { func_global(ts); }
            else if syms[ts].kind == SK_VAR && syms[ts].flags & (SF_DEFINED | SF_TENTATIVE) != 0 { var_global(ts); }
        }
    }
    // emit, following references (and lower the functions only expanded
    // in place, for their debug records: gen_call.goose, inline_ref)
    var wi = 0;
    var ii = 0;
    while wi < work.len || ii < inl_work.len {
        if wi >= work.len {
            let F = inl_work[ii];
            ii++;
            let fg = sym_gen[F].glob;
            if fg != NONE && glob_gen[fg].state != 0 { continue; }
            gen_function_dropped(syms[F].def as! u32);
            continue;
        }
        let g = work[wi];
        wi++;
        ensure_glob_tables();
        let s = glob_gen[g].sym;
        if s < 0 { continue; }
        if m_globals[g].kind == G_FUNC {
            let d = syms[s].def;
            if d >= 0 { gen_function(d as! u32); }
        } else {
            emit_var(g);
        }
        if n_errors > 0 && n_errors >= 50 { break; }
    }
    if opt_cxx { emit_terminate_fn(); }
    emit_aliases();
    if opt_cxx { cx_aliases(); }
    emit_structors();
    finish_undefined();
    if opt_cxx { cx_comdats(); }
    if n_errors == 0 { dbg_build(); }
    if f128_loc != NONE { err_at(f128_loc, "goosecc: __float128 is not supported (GIR has no fp128 type)"); }
    return n_errors == 0;
}

// Linkage flags of the globals that are only declared (weak, hidden, TLS).
fn finish_undefined() {
    ensure_glob_tables();
    for g in m_globals.len {
        let gd = m_globals[g];
        if gd.flags & (GF_DEFINED | GF_COMMON) != 0 { continue; }
        let s = glob_gen[g].sym;
        if s < 0 { continue; }
        var f = gd.flags;
        if syms[s].flags & SF_WEAK != 0 { f = f | GF_WEAK; }
        if syms[s].flags & SF_THREAD != 0 { f = f | GF_TLS; }
        let vis = sym_visibility(s);
        if vis == 1 { f = f | GF_HIDDEN | GF_LOCALREF; }
        if vis == 2 { f = f | GF_PROTECTED; }
        if syms[s].kind == SK_FUNC { m_globals[g].kind = G_FUNC; }
        m_globals[g].flags = f;
    }
}

// __attribute__((alias("target"))).
fn emit_aliases() {
    let tu = nodes[tu_node];
    for i in tu.c as i64 {
        let nd = nodes[nlist[tu.v + i]];
        if nd.kind != N_DECL && nd.kind != N_FUNCDEF { continue; }
        let s = nd.a as i64;
        let a = syms[s].attr;
        if a == 0 || sym_attrs[a].alias_len == 0 { continue; }
        let off = sym_attrs[a].alias_off as i64;
        let tname = strbytes[off..off + sym_attrs[a].alias_len];
        let tid = intern(tname);
        let r = gmap.get(gk(GM_NAMEGLOB, tid));
        if !r {
            err_at(nd.loc, str("alias must point to a defined variable or function ('", tname, "')"));
            continue;
        }
        let tg = r;
        let g = global_by_name(link_name(s), syms[s].kind == SK_FUNC);
        if m_globals[g].kind == G_ALIAS { continue; }
        m_globals[g].kind = G_ALIAS;
        m_globals[g].func = tg;
        m_globals[g].aux = 0;
        m_globals[g].flags = link_flags(s, true) | GF_DEFINED | (m_globals[tg].flags & (GF_TLS | GF_CONST));
        m_globals[g].align = m_globals[tg].align;
        ensure_glob_tables();
        glob_gen[g].state = 2;
    }
}

// constructor / destructor attributes: .init_array / .fini_array entries,
// one pointer array per priority (as the exporter builds them).
fn emit_structors() {
    for pass in 2 {
        let ctors = pass == 0;
        // collect (priority, global) pairs in source order
        var ents: u32[>..] = [];
        let tu = nodes[tu_node];
        for i in tu.c as i64 {
            let nd = nodes[nlist[tu.v + i]];
            if nd.kind != N_FUNCDEF { continue; }
            let s = nd.a as i64;
            let a = syms[s].attr;
            if a == 0 { continue; }
            let m = if ctors { AM_CTOR } else { AM_DTOR };
            if sym_attrs[a].flags & m == 0 { continue; }
            let prio = if ctors { sym_attrs[a].ctor_prio } else { sym_attrs[a].dtor_prio };
            ents.push(prio as u32);
            ents.push(func_global(s));
        }
        // stable sort by priority
        let n = ents.len / 2;
        var i = 1;
        while i < n {
            let p = ents[2 * i];
            let g = ents[2 * i + 1];
            var j = i - 1;
            while j >= 0 && ents[2 * j] > p {
                ents[2 * j + 2] = ents[2 * j];
                ents[2 * j + 3] = ents[2 * j + 1];
                j--;
            }
            ents[2 * j + 2] = p;
            ents[2 * j + 3] = g;
            i++;
        }
        var k = 0;
        while k < n {
            var e = k;
            while e < n && ents[2 * e] == ents[2 * k] { e++; }
            var sec: u8[>..] = [];
            sec.append(if ctors { ".init_array" } else { ".fini_array" });
            let prio = ents[2 * k];
            if prio != 65535 {
                sec.push('.');
                var d: u8[>..] = [];
                format(d, prio);
                for z in 5 - d.len { sec.push('0'); }
                sec.append(d);
            }
            let si = get_section(sec, SF_WRITE, if ctors { 14 } else { 15 });
            var nm: u8[>..] = [];
            nm.append(if ctors { "__goovm_init_array." } else { "__goovm_fini_array." });
            format(nm, m_globals.len);
            let g = new_global(nm, G_VAR, GF_INTERNAL | GF_DEFINED | GF_LOCALREF, 8);
            ensure_glob_tables();
            glob_gen[g].state = 2;
            m_globals[g].section = si;
            m_globals[g].size = (8 * (e - k)) as! u32;
            let at = m_data.len;
            data_grow(8 * (e - k));
            m_globals[g].data = at as! u32;
            for x in k..e {
                m_drelocs.push(DataReloc { owner: g, offset: (8 * (x - k)) as! u32, target: ents[2 * x + 1], kind: DR_ABS64, addend: 0, blk: 0, blk2: 0 });
            }
            m_globals[g].flags = m_globals[g].flags | GF_RELOCS;
            k = e;
        }
    }
}

// The object file, from the back-end; with -g also the DIE tables
// (gen_dwarf.goose).
var no_ehs: Eh[>..] = [];
var no_comdats: Comdat[>..] = [];
var no_gcomdat: u32[>..] = [];
fn codegen() -> const u8[:] {
    if opt_cxx {
        return gir_codegen_ex(m_header, m_types, m_funcs, m_blocks, m_insts, m_opnds, m_consts, m_globals, m_sections,
            m_data, m_drelocs, m_strtab, m_dlocs, m_dscopes, m_dfiles, m_dstr, m_asms, m_ehs, m_comdats, m_gcomdat,
            m_dies, m_dattrs);
    }
    if opt_debug {
        return gir_codegen_ex(m_header, m_types, m_funcs, m_blocks, m_insts, m_opnds, m_consts, m_globals, m_sections,
            m_data, m_drelocs, m_strtab, m_dlocs, m_dscopes, m_dfiles, m_dstr, m_asms, no_ehs, no_comdats, no_gcomdat,
            m_dies, m_dattrs);
    }
    return gir_codegen(m_header, m_types, m_funcs, m_blocks, m_insts, m_opnds, m_consts, m_globals, m_sections,
        m_data, m_drelocs, m_strtab, m_dlocs, m_dscopes, m_dfiles, m_dstr, m_asms);
}

// ------------------------------------------------------------ --emit-gir

let OP_NAMES = ["ret", "br", "condbr", "switch", "unreachable", "add", "sub", "mul", "sdiv", "udiv", "srem", "urem", "and",
    "or", "xor", "shl", "lshr", "ashr", "icmp", "select", "zext", "sext", "trunc", "ptrtoint", "inttoptr",
    "bitcast", "alloca", "load", "store", "gep", "call", "phi", "fadd", "fsub", "fmul", "fdiv", "fneg", "fcmp",
    "fpext", "fptrunc", "fptosi", "fptoui", "sitofp", "uitofp", "extractvalue", "insertvalue", "extractelt",
    "insertelt", "shuffle", "dynalloca", "stacksave", "stackrestore", "vastart", "memcpy", "memset", "ctlz",
    "cttz", "ctpop", "bswap", "bitreverse", "fshl", "fshr", "ovf", "scmp", "ucmp", "fabs", "copysign", "fsqrt",
    "isfpclass", "cmpxchg", "atomicrmw", "fence", "tlsaddr", "frameaddr", "retaddr", "sjlj_setjmp",
    "sjlj_longjmp", "trap", "debugtrap", "indirectbr", "blockaddr", "x86", "asm"];
let TY_NAMES = ["void", "i1", "i8", "i16", "i32", "i64", "ptr", "f32", "f64", "f80", "i128", "f16"];
let PRED_NAMES = ["eq", "ne", "ugt", "uge", "ult", "ule", "sgt", "sge", "slt", "sle"];

recursive fn dump_ty(o: u8[>..]&, t: u32) {
    if t <= GIR_T_F16 { o.append(TY_NAMES[t]); return; }
    let d = m_types[t];
    if d.kind == TK_INT { format(o, "i", d.bits); return; }
    if d.kind == TK_VECTOR { format(o, "<", d.n, " x "); dump_ty(o, d.elems); o.push('>'); return; }
    if d.kind == TK_ARRAY { format(o, "[", d.n, " x "); dump_ty(o, d.elems); o.push(']'); return; }
    if d.kind == TK_STRUCT {
        o.push('{');
        for i in 0..d.n {
            o.append(if i > 0 { ", " } else { " " });
            dump_ty(o, m_opnds[d.elems + 2 * i]);
            format(o, "@", m_opnds[d.elems + 2 * i + 1]);
        }
        o.append(" }");
        return;
    }
    format(o, "t", t);
}

fn gname(g: u32) -> const u8[:] {
    let gd = m_globals[g];
    return m_strtab[gd.name..gd.name + gd.name_len];
}

fn dump_ref(o: u8[>..]&, r: u32) {
    if r == NONE { o.append("none"); return; }
    let i = r & 0x3FFFFFFF;
    let k = r >> 30;
    if k == 0 { format(o, "%", i); return; }
    if k == 1 { format(o, "arg", i); return; }
    if k == 2 {
        let c = m_consts[i];
        dump_ty(o, c.ty);
        if c.hi != 0 { format(o, " 0x", hex(c.hi), ":", hex(c.lo)); }
        else if c.data != NONE { format(o, " data@", c.data); }
        else { format(o, " ", c.lo as! i64); }
        return;
    }
    o.push('@');
    o.append(gname(i));
}

fn hex(x: u64) -> u8[..16] {
    var s: u8[..16] = [];
    var started = false;
    for k in 16 {
        let d = (x >> ((60 - 4 * k) as! u64)) & 15;
        if d != 0 || started || k == 15 {
            started = true;
            s.push(if d < 10 { ('0' as u64 + d) as! u8 } else { ('a' as u64 + d - 10) as! u8 });
        }
    }
    return s;
}

fn dump_gir(o: u8[>..]&) {
    let h = m_header[0];
    format(o, "gir version ", h.version, " flags=", h.flags, " tls_get_addr=", h.tls_get_addr as! i32, " types=", m_types.len, "\n");
    for s, i in m_sections {
        format(o, "section ", i, " ", m_strtab[s.name..s.name + s.name_len], " flags=", s.flags, " type=", s.typ, "\n");
    }
    let kinds = ["func", "var", "alias"];
    for g, i in m_globals {
        format(o, "global ", i, " ", kinds[g.kind], " @", gname(i as! u32), " flags=0x", hex(g.flags as u64), " align=", g.align,
            " size=", g.size, " data=", g.data, " func=", g.func as! i32, " section=", g.section as! i32, " aux=", g.aux as! i32, "\n");
    }
    for d in m_drelocs {
        format(o, "dreloc owner=", d.owner, " off=", d.offset, " target=", d.target, " kind=", d.kind, " addend=", d.addend,
            " block=", d.blk, " block2=", d.blk2, "\n");
    }
    for F, fi in m_funcs {
        format(o, "\nfunc ", fi, " @", gname(F.global), "(");
        for a in 0..F.n_args {
            let w = m_opnds[F.args + 2 * a + 1];
            if a > 0 { o.append(", "); }
            dump_ty(o, m_opnds[F.args + 2 * a]);
            if w & ABI_BYVAL != 0 { format(o, " byval(", w & 0xFFFFFF, ", align ", (1 as u32) << ((w >> 24) & 31), ")"); }
            if w & ABI_SRET != 0 { o.append(" sret"); }
        }
        o.append(") -> ");
        dump_ty(o, F.ret_ty);
        format(o, " flags=0x", hex(F.flags as u64), " dbg=", F.dbg, "\n");
        for b in 0..F.n_blocks {
            let B = m_blocks[F.first_block + b];
            format(o, " b", b, ":\n");
            for k in B.first_inst..B.first_inst + B.n_inst {
                let I = m_insts[k];
                format(o, "  %", k, " = ", OP_NAMES[I.op], " ");
                dump_ty(o, I.ty);
                if I.flags != 0 { format(o, " [flags 0x", hex(I.flags as u64), "]"); }
                let op = I.op as u32;
                if op == GIR_RET { o.push(' '); dump_ref(o, I.a); }
                else if op == GIR_BR { format(o, " b", I.a); }
                else if op == GIR_CONDBR { o.push(' '); dump_ref(o, I.a); format(o, ", b", I.b, ", b", I.c); }
                else if op == GIR_SWITCH {
                    o.push(' ');
                    dump_ref(o, I.a);
                    format(o, " default b", m_opnds[I.b]);
                    for c in 0..I.c {
                        o.append(", ");
                        dump_ref(o, m_opnds[I.b + 1 + 2 * c]);
                        format(o, " -> b", m_opnds[I.b + 2 + 2 * c]);
                    }
                } else if op == GIR_INDIRECTBR {
                    o.push(' ');
                    dump_ref(o, I.a);
                    for c in 0..I.c { format(o, ", b", m_opnds[I.b + c]); }
                } else if op == GIR_ICMP {
                    format(o, " ", PRED_NAMES[I.sub % 10], " ");
                    dump_ty(o, I.aux);
                    o.push(' ');
                    dump_ref(o, I.a);
                    o.append(", ");
                    dump_ref(o, I.b);
                } else if op == GIR_FCMP {
                    format(o, " pred", I.sub, " ");
                    dump_ty(o, I.aux);
                    o.push(' ');
                    dump_ref(o, I.a);
                    o.append(", ");
                    dump_ref(o, I.b);
                } else if op == GIR_ALLOCA { format(o, " size=", I.a, " align=", I.b); }
                else if op == GIR_DYNALLOCA { o.push(' '); dump_ref(o, I.a); format(o, " align=", I.b); }
                else if op == GIR_STORE {
                    o.push(' ');
                    dump_ty(o, I.aux);
                    o.push(' ');
                    dump_ref(o, I.a);
                    o.append(", ");
                    dump_ref(o, I.b);
                } else if op == GIR_GEP {
                    o.push(' ');
                    dump_ref(o, I.a);
                    let off = (m_opnds[I.b] as u64 | (m_opnds[I.b + 1] as u64 << 32)) as! i64;
                    format(o, " + ", off);
                    for c in 0..I.c {
                        o.append(" + ");
                        dump_ref(o, m_opnds[I.b + 2 + 2 * c]);
                        format(o, "*", m_opnds[I.b + 3 + 2 * c]);
                    }
                } else if op == GIR_CALL {
                    o.push(' ');
                    dump_ref(o, I.a);
                    o.push('(');
                    for c in 0..I.c {
                        if c > 0 { o.append(", "); }
                        dump_ref(o, m_opnds[I.b + 2 * c]);
                        let w = m_opnds[I.b + 2 * c + 1];
                        if w != 0 { format(o, " [abi 0x", hex(w as u64), "]"); }
                    }
                    o.push(')');
                } else if op == GIR_PHI {
                    for c in 0..I.c {
                        o.append(if c > 0 { ", [" } else { " [" });
                        dump_ref(o, m_opnds[I.b + 2 * c]);
                        format(o, ", b", m_opnds[I.b + 2 * c + 1], "]");
                    }
                } else if op == GIR_EXTRACTVALUE { o.push(' '); dump_ref(o, I.a); format(o, " @", I.b); }
                else if op == GIR_INSERTVALUE { o.push(' '); dump_ref(o, I.a); o.append(", "); dump_ref(o, I.b); format(o, " @", I.c); }
                else if op == GIR_MEMCPY || op == GIR_MEMSET { o.push(' '); dump_ref(o, I.a); o.append(", "); dump_ref(o, I.b); format(o, ", ", I.c); }
                else if op == GIR_TLSADDR { o.append(" @"); o.append(gname(I.a)); }
                else if op == GIR_BLOCKADDR { format(o, " global", I.a, " b", I.b); }
                else if op == GIR_FRAMEADDR || op == GIR_RETADDR { format(o, " ", I.a); }
                else if op == GIR_UNREACHABLE || op == GIR_TRAP || op == GIR_DEBUGTRAP || op == GIR_STACKSAVE || op == GIR_FENCE {}
                else {
                    if I.sub != 0 { format(o, " sub", I.sub); }
                    if (op >= GIR_ZEXT && op <= GIR_BITCAST) || (op >= GIR_FPEXT && op <= GIR_UITOFP) { o.append(" from "); dump_ty(o, I.aux); }
                    o.push(' ');
                    dump_ref(o, I.a);
                    if I.b != 0 || op == GIR_SELECT || op <= GIR_ASHR { o.append(", "); dump_ref(o, I.b); }
                    if op == GIR_SELECT || op == GIR_INSERTELT || op == GIR_FSHL || op == GIR_FSHR || op == GIR_CMPXCHG {
                        o.append(", ");
                        dump_ref(o, I.c);
                    }
                }
                if I.dbg != 0 { format(o, "  !", m_dlocs[I.dbg].line, ":", m_dlocs[I.dbg].col); }
                o.push('\n');
            }
        }
    }
}
