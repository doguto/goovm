// goosecc B2: globals. Every function and variable with linkage is one GIR
// global, found by its linkage name (identifiers with linkage name one entity
// per translation unit); objects without linkage (static locals, compound
// literals at file scope, string literals) get private globals. Definitions
// are emitted as clang emits them: external definitions always, internal
// and inline-only ones when something emitted refers to them (clang's
// deferred declarations). Static initializers are evaluated to bytes and
// data relocations.

namespace gen;

import std;
import dictionary;
import .common;
import .types;
import .ast;
import .sema;
import .parse;
import .cx_gen_defs;

// Per global: the symbol (-1 for others), and 0 declared, 1 queued, 2 emitted.
struct GlobGen { sym: i64, state: u8 }
var glob_gen: GlobGen[>..] = [];
var work: u32[>..<] = [];                  // globals whose definitions are to be emitted

// The symbol whose definition has linkage name id, or -1.
fn defining_sym(id: u32) -> i64 {
    let r = gmap.get(gk(GM_DEFBY, id));
    if r { return r; }
    return -1;
}

fn ensure_glob_tables() {
    while glob_gen.len < m_globals.len { glob_gen.push(GlobGen { sym: -1, state: 0 }); }
}

// The linkage name of symbol s (asm label or identifier), as an ident id.
fn link_name(s: i64) -> u32 {
    let a = syms[s].attr;
    if a != 0 && sym_attrs[a].asm_len != 0 {
        let off = sym_attrs[a].asm_label as i64;
        var nm = strbytes[off..off + sym_attrs[a].asm_len];
        // a leading \01 means "do not mangle"
        if nm.len > 0 && nm[0] == 1 { nm = nm[1..]; }
        return intern(nm);
    }
    return syms[s].name;
}

fn has_linkage(s: i64) -> bool {
    let sy = syms[s];
    if sy.kind == SK_FUNC || sy.kind == SK_BUILTIN { return true; }
    if sy.flags & SF_COMPLIT != 0 { return false; }
    if sy.flags & SF_FILESCOPE != 0 { return true; }
    if sy.sc == SC_EXTERN || sy.flags & SF_LOCALLINK != 0 { return true; }
    return false;
}

// Is s (or the entity it names) internal (static)?
fn is_internal_sym(s: i64) -> bool {
    let sy = syms[s];
    if sy.sc == SC_STATIC { return true; }
    if sy.canon >= 0 && sy.canon as i64 != s && syms[sy.canon].sc == SC_STATIC { return true; }
    return false;
}

fn global_by_name(id: u32, is_func: bool) -> u32 {
    let r = gmap.get(gk(GM_NAMEGLOB, id));
    if r { return r; }
    let g = new_global(ident_text(id as i64), if is_func { G_FUNC } else { G_VAR }, 0, if is_func { 16 } else { 1 });
    gmap.insert(gk(GM_NAMEGLOB, id), g);
    ensure_glob_tables();
    return g;
}

// The function's global; queues its definition if it is emitted on use.
fn func_global(s0: i64) -> u32 {
    ensure_sym_tables();
    var s = s0;
    if sym_gen[s].glob != NONE { note_use(sym_gen[s].glob); return sym_gen[s].glob; }
    let id = link_name(s);
    let g = global_by_name(id, true);
    ensure_glob_tables();
    if glob_gen[g].sym < 0 {
        // a declaration of a function defined in this unit (under another symbol)
        let ds = defining_sym(id);
        glob_gen[g].sym = if ds >= 0 { ds } else { s };
    }
    if syms[s].def >= 0 && glob_gen[g].sym >= 0 && syms[glob_gen[g].sym].def < 0 { glob_gen[g].sym = s; }
    sym_gen[s].glob = g;
    note_use(g);
    return g;
}

// The variable's global (file-scope, extern, static local, compound literal).
fn var_global(s: i64) -> u32 {
    ensure_sym_tables();
    if sym_gen[s].glob != NONE { note_use(sym_gen[s].glob); return sym_gen[s].glob; }
    var g: u32 = 0;
    if has_linkage(s) || (opt_cxx && syms[s].attr != 0 && sym_attrs[syms[s].attr].asm_len != 0) {
        g = global_by_name(link_name(s), false);
        ensure_glob_tables();
        if glob_gen[g].sym < 0 { glob_gen[g].sym = s; }
        else if sym_gen[s].init != 0 || (syms[s].flags & SF_FILESCOPE != 0 && syms[glob_gen[g].sym].flags & SF_FILESCOPE == 0) { glob_gen[g].sym = s; }
    } else {
        // a static local (f.x) or a compound literal
        var nm: u8[>..] = [];
        if syms[s].flags & SF_COMPLIT != 0 {
            nm.append(".compoundliteral");
        } else {
            if f_sym >= 0 { nm.append(ident_text(link_name(f_sym) as i64)); nm.push('.'); }
            nm.append(ident_text(syms[s].name as i64));
        }
        g = new_global(nm, G_VAR, GF_INTERNAL | GF_LOCALREF, 1);
        ensure_glob_tables();
        glob_gen[g].sym = s;
    }
    sym_gen[s].glob = g;
    note_use(g);
    return g;
}

// The global of a compound literal with static storage.
fn complit_global(n: u32) -> u32 {
    let s = nodes[n].b as i64;
    ensure_sym_tables();
    ensure_sym_gen();
    sym_gen[s].init = nodes[n].a;
    return var_global(s);
}

// A reference to g from emitted code: an on-use definition is queued.
fn note_use(g: u32) {
    if ev_on {
        dev(EV_REF, g, if ev_noproto { 1 } else { 0 });
        ev_noproto = false;
    }
    if glob_gen[g].state != 0 { return; }
    let s = glob_gen[g].sym;
    if s < 0 { return; }
    if !defined_on_use(s) { return; }
    glob_gen[g].state = 1;
    work.push(g);
}

// Does s have a definition in this unit that is emitted when used?
fn defined_on_use(s: i64) -> bool {
    let sy = syms[s];
    if sy.kind == SK_FUNC { return sy.def >= 0 && fn_emitted_def(s); }
    if sy.kind == SK_VAR {
        if sy.flags & SF_COMPLIT != 0 { return true; }
        if sy.flags & SF_FILESCOPE == 0 && sy.sc == SC_STATIC { return false; }   // static locals: at their declaration
        return sy.flags & (SF_DEFINED | SF_TENTATIVE) != 0;
    }
    return false;
}

// Is the function's definition one that this unit emits (C99 6.7.4 and
// GNU inline rules, as clang's isInlineDefinitionExternallyVisible)?
fn fn_emitted_def(s: i64) -> bool {
    let sy = syms[s];
    if sy.def < 0 { return false; }
    if opt_cxx && cxl_link(s) != LK_DEFAULT { return true; }
    if sy.sc == SC_STATIC { return true; }
    if sy.flags & SF_INLINE == 0 { return true; }
    if sy.flags & SF_GNU_EXTERN_INLINE != 0 { return sym_has_attr(s, AM_ALWAYS_INLINE); }
    let gnu = opt_c89 || (sy.attr != 0 && sym_attrs[sy.attr].flags & AM_GNU_INLINE != 0);
    if gnu { return true; }
    // C99: an inline definition unless some file-scope declaration is not
    // inline or is extern
    if sy.flags & SF_FORCE_DEF != 0 { return true; }
    return sym_has_attr(s, AM_ALWAYS_INLINE);
}

// An inline definition that clang would inline everywhere (always_inline,
// even at -O0) and never emit: goosecc emits it as a local function.
fn fn_local_inline(s: i64) -> bool {
    let sy = syms[s];
    if sy.kind != SK_FUNC || sy.def < 0 || sy.sc == SC_STATIC || sy.flags & SF_INLINE == 0 { return false; }
    if !sym_has_attr(s, AM_ALWAYS_INLINE) { return false; }
    if sy.flags & SF_GNU_EXTERN_INLINE != 0 { return true; }
    let gnu = opt_c89 || (sy.attr != 0 && sym_attrs[sy.attr].flags & AM_GNU_INLINE != 0);
    if gnu { return false; }
    return sy.flags & SF_FORCE_DEF == 0;
}

// Is it emitted even when nothing refers to it?
fn fn_always_emitted(s: i64) -> bool {
    let sy = syms[s];
    if !fn_emitted_def(s) { return false; }
    if sy.sc == SC_STATIC { return sym_has_attr(s, AM_USED) || sym_has_attr(s, AM_CTOR) || sym_has_attr(s, AM_DTOR); }
    if sy.flags & SF_INLINE != 0 && !(opt_c89 || sym_has_attr(s, AM_GNU_INLINE)) { return true; }
    if sy.flags & SF_INLINE != 0 { return true; }
    return true;
}

fn sym_has_attr(s: i64, m: u32) -> bool {
    let a = syms[s].attr;
    return a != 0 && sym_attrs[a].flags & m != 0;
}

// Linkage flags of a defined or referenced global.
fn link_flags(s: i64, defined: bool) -> u32 {
    var f: u32 = 0;
    if opt_cxx && cxl_link(s) != LK_DEFAULT && defined {
        // D3: linkonce_odr / weak_odr (also static locals of inline functions)
        f = GF_WEAK;
        if cxl_has(s, CXL_HIDDEN) { f = f | GF_HIDDEN | GF_LOCALREF; }
        return f;
    }
    let internal = is_internal_sym(s) || !has_linkage(s) || fn_local_inline(s);
    if internal { f = f | GF_INTERNAL | GF_LOCALREF; }
    if syms[s].flags & SF_WEAK != 0 { f = f | GF_WEAK; }
    // D3: linkonce_odr and weak_odr C++ definitions are weak
    if opt_cxx && defined && !internal && cxl_link(s) != LK_DEFAULT { f = f | GF_WEAK; }
    var vis = sym_visibility(s);
    if opt_cxx && cxl_has(s, CXL_HIDDEN) { vis = 1; }
    if vis == 1 { f = f | GF_HIDDEN; }
    if vis == 2 { f = f | GF_PROTECTED; }
    if defined && !opt_pic { f = f | GF_LOCALREF; }
    if (vis == 1 || vis == 2) && defined { f = f | GF_LOCALREF; }
    if vis == 1 && !defined && !internal && syms[s].flags & SF_WEAK == 0 { f = f | GF_LOCALREF; }
    if defined && f & GF_WEAK != 0 && !internal && vis == 0 { f = f & ~GF_LOCALREF; }
    return f;
}

fn sym_visibility(s: i64) -> u32 {
    let a = syms[s].attr;
    if a == 0 { return 0; }
    return sym_attrs[a].vis as u32;
}

// The address of variable s in the current function.
fn var_addr(s: i64) -> u32 {
    ensure_sym_tables();
    if sym_gen[s].addr != NONE { return sym_gen[s].addr; }
    var c = s;
    if syms[s].canon >= 0 && syms[s].canon as i64 != s { c = syms[s].canon as i64; }
    let g = var_global(c);
    if syms[c].flags & SF_THREAD != 0 || m_globals[g].flags & GF_TLS != 0 {
        m_globals[g].flags = m_globals[g].flags | GF_TLS;
        if !opt_pie && m_header[0].tls_get_addr == NONE { m_header[0].tls_get_addr = libfn("__tls_get_addr"); }
        return emit(GIR_TLSADDR, GIR_T_PTR, 0, 0, 0, g, 0, 0);
    }
    return gref(g);
}

// Alignment of a variable (clang: the type's, the aligned attribute, and
// 16 for arrays of 16 bytes or more).
fn var_align(s: i64, q: u32) -> i64 {
    var al = type_align(q);
    let a = syms[s].attr;
    if a != 0 && sym_attrs[a].align as i64 > al { al = sym_attrs[a].align as i64; }
    if is_array(q) && type_size(q) >= 16 && al < 16 { al = 16; }
    return al;
}
fn local_align(s: i64, q: u32) -> i64 { var_align(s, q) }

// --------------------------------------------------------------- strings

var str_glob = dictionary<u64, u32> {};
var n_strs: i64 = 0;

fn str_bytes(si: u32) -> const u8[:] {
    let sl = strs[si];
    let w = type_size(sl.elem);
    return strbytes[sl.start..sl.start + sl.len * (w as! u32)];
}

// A string literal's private constant global (identical literals share one).
fn string_global(si: u32) -> u32 {
    let sl = strs[si];
    let w = type_size(sl.elem);
    let b = str_bytes(si);
    var h: u64 = 1469598103934665603 ^ (w as! u64);
    for c in b { h = (h ^ (c as u64)) * 1099511628211; }
    var key = h;
    loop {
        let r = str_glob.get(key);
        if !r { break; }
        let g = r;
        let gd = m_globals[g];
        if gd.size as i64 == b.len && gd.align as i64 == w && m_data[gd.data..gd.data + gd.size] == b { return g; }
        key = key + 1;
    }
    var nm: u8[>..] = [];
    nm.append(".L.str");
    if n_strs > 0 { format(nm, ".", n_strs); }
    n_strs++;
    let g = new_global(nm, G_VAR, GF_INTERNAL | GF_DEFINED | GF_CONST | GF_LOCALREF, w as! u32);
    let at = m_data.len as! u32;
    m_data.append(b);
    m_globals[g].data = at;
    m_globals[g].size = b.len as! u32;
    ensure_glob_tables();
    glob_gen[g].state = 2;
    str_glob.insert(key, g);
    return g;
}

// --------------------------------------------------------------- variables

recursive fn is_const_object(q: u32) -> bool {
    if quals(q) & Q_CONST == 0 {
        if is_array(q) { return is_const_object(tbase(q)); }
        return false;
    }
    if is_record(q) && records[rec_of(q)].flags & RF_VOLATILE_MEMBER != 0 { return false; }
    return quals(q) & Q_VOLATILE == 0;
}

// Emits the definition of variable global g (symbol s).
fn emit_var(g: u32) {
    let s = glob_gen[g].sym;
    // G1: the context of the evaluator's reads of const variables
    let fs = syms[s].flags & SF_FILESCOPE != 0;
    let c0 = cv_ctx;
    let l0 = cv_ctx_late;
    if fs {
        cv_ctx = sym_gen[s].decl;
        cv_ctx_late = is_internal_sym(s) && !sym_has_attr(s, AM_USED);
    }
    emit_var0(g);
    cv_ctx = c0;
    cv_ctx_late = l0;
}

fn emit_var0(g: u32) {
    let s = glob_gen[g].sym;
    // -g: the events of a file-scope definition (gen_dwarf.goose)
    let top = opt_debug && !ev_on && syms[s].flags & SF_FILESCOPE != 0 && syms[s].flags & SF_COMPLIT == 0;
    var e0: u32 = 0;
    if top { e0 = dbg_gvar_begin(); }
    if opt_debug && sym_gen[s].init != 0 && syms[s].flags & SF_COMPLIT == 0 { dbg_init_casts(sym_gen[s].init); }
    emit_var1(g);
    if top { dbg_gvar_end(s, g, e0); }
}

fn emit_var1(g: u32) {
    let s = glob_gen[g].sym;
    glob_gen[g].state = 2;
    let q = syms[s].ty;
    var size = type_size(q);
    if size < 0 { size = 0; }
    let init = sym_gen[s].init as u32;
    if sym_gen[s].decl != 0 { last_loc = nodes[sym_gen[s].decl].loc; }
    if init != 0 {
        // a flexible array member with an initializer extends the object (GNU)
        let ext = init_extent(q, init);
        if ext > size { size = ext; }
    }
    var f = link_flags(s, true) | GF_DEFINED;
    if syms[s].flags & SF_THREAD != 0 { f = f | GF_TLS; }
    let common = init == 0 && opt_common && syms[s].flags & SF_TENTATIVE != 0 && !is_internal_sym(s) && syms[s].flags & SF_THREAD == 0 &&
        sym_section(s) < 0 && !sym_has_attr(s, AM_WEAK) && syms[s].flags & SF_WEAK == 0 && !sym_has_attr(s, AM_NOCOMMON);
    m_globals[g].kind = G_VAR;
    m_globals[g].size = size as! u32;
    m_globals[g].align = var_align(s, q) as! u32;
    if common {
        m_globals[g].flags = (f & ~GF_DEFINED & ~GF_LOCALREF) | GF_COMMON;
        return;
    }
    if is_const_object(q) && init != 0 { f = f | GF_CONST; }
    let sec = sym_section(s);
    if sec >= 0 {
        let nm = strbytes[sec..sec + sym_attrs[syms[s].attr].sec_len as i64];
        let bss = starts_with(nm, ".bss") || starts_with(nm, ".tbss") || starts_with(nm, ".sbss");
        var sf: u32 = if f & GF_CONST != 0 { 0 } else { SF_WRITE };
        if f & GF_TLS != 0 { sf = sf | SF_TLS; }
        let zero = init == 0 || is_zero_init(init);
        if bss && zero { sf = sf | SF_NOBITS | SF_WRITE; }
        m_globals[g].section = get_section(nm, sf, if bss && zero { 8 } else { 1 });
        if !(bss && zero) {
            emit_var_data(g, s, q, init, size);
            if m_globals[g].flags & GF_RELOCS != 0 { m_sections[m_globals[g].section].flags = m_sections[m_globals[g].section].flags | SF_WRITE; }
            m_globals[g].flags = m_globals[g].flags | f;
            return;
        }
        m_globals[g].flags = f | GF_ZERO;
        return;
    }
    if init == 0 || is_zero_init(init) {
        m_globals[g].flags = f | GF_ZERO;
        return;
    }
    m_globals[g].flags = m_globals[g].flags | f;
    emit_var_data(g, s, q, init, size);
}

// The bytes an initializer covers, with a flexible array member's elements.
fn init_extent(q: u32, init: u32) -> i64 {
    if kind_of(q) != TY_STRUCT || nkind(init) != N_INITLIST { return 0; }
    let r = rec_of(q);
    if records[r].flags & RF_FLEX == 0 { return 0; }
    let nd = nodes[init];
    var ci: i64 = 0;
    let first = records[r].first as i64;
    let cnt = records[r].count as i64;
    var last: i64 = -1;
    var last_child: u32 = 0;
    for i in first..first + cnt {
        let f = fields[i];
        if f.width >= 0 && f.name == 0 { continue; }
        if ci >= nd.c as i64 { break; }
        last = i;
        last_child = nlist[nd.v + ci];
        ci++;
    }
    if last != first + cnt - 1 { return 0; }
    let f = fields[last];
    if kind_of(f.ty) != TY_ARRAY || types[f.ty >> 4].n >= 0 { return 0; }
    let es = type_size(tbase(f.ty));
    let c = nodes[last_child];
    if c.kind == N_STRING { return f.offset + (strs[c.a].len as i64) * es; }
    if c.kind == N_INITLIST { return f.offset + (c.c as i64) * es; }
    return 0;
}

fn emit_var_data(g: u32, s: i64, q: u32, init: u32, size: i64) {
    let at = m_data.len;
    data_grow(size);
    m_globals[g].data = at as! u32;
    // G1: a variable without an initializer in a named section that is
    // not a .bss one (a tentative definition with `section`, as in
    // noinit-attribute.c) is zeros in that section, as clang emits it
    if init == 0 { return; }
    let r0 = m_drelocs.len;
    sinit(g, at, 0, q, init);
    sort_relocs(r0);
}

fn sort_relocs(r0: i64) {
    // insertion sort by offset (initializers are almost always in order)
    var i = r0 + 1;
    while i < m_drelocs.len {
        let x = m_drelocs[i];
        var j = i - 1;
        while j >= r0 && m_drelocs[j].offset > x.offset {
            m_drelocs[j + 1] = m_drelocs[j];
            j--;
        }
        m_drelocs[j + 1] = x;
        i++;
    }
}

// The offset of a symbol's section name in strbytes, -1 without one (G1:
// the name may be the translation unit's first string, at offset 0).
fn sym_section(s: i64) -> i64 {
    let a = syms[s].attr;
    if a == 0 || sym_attrs[a].sec_len == 0 { return -1; }
    return sym_attrs[a].sec_off as i64;
}

// Is the initializer all zero bytes (no relocations)?
recursive fn is_zero_init(n: u32) -> bool {
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_ZEROINIT { return true; }
    if k == N_INITLIST {
        for i in nd.c { if !is_zero_init(nlist[nd.v + i]) { return false; } }
        return true;
    }
    if k == N_INT { return nd.v == 0; }
    if k == N_FLOAT {
        if kind_of(nd.ty) == TY_LDOUBLE && nd.c > 0 {
            let x = strtold(src[nd.b..nd.b + nd.c]);
            return x.lo == 0 && x.hi == 0;
        }
        return nd.v == 0;
    }
    if k == N_ICAST || k == N_CAST {
        if nd.op == CK_NULL2PTR { return true; }
        if is_integer(nd.ty) || is_real_float(nd.ty) {
            if is_integer(nd.ty) {
                let ok, v = fold_int(n);
                return ok && v == 0;
            }
            let ok, f = fold_float(n);
            return ok && f == 0.0 && reinterpret_i64(f) == 0 && !is_ldouble_literal(n);
        }
    }
    return false;
}

fn is_ldouble_literal(n: u32) -> bool { false }

// --------------------------------------------------------------- static initializers

fn put_bytes(at: i64, v: u64, n: i64) {
    for i in n {
        if i >= 8 { break; }
        m_data[at + i] = ((v >> ((8 * i) as! u64)) & 255) as! u8;
    }
}

fn add_reloc(g: u32, off: i64, target: u32, kind: u32, addend: i64, blk: u32, blk2: u32) {
    m_drelocs.push(DataReloc { owner: g, offset: off as! u32, target: target, kind: kind, addend: addend, blk: blk, blk2: blk2 });
    m_globals[g].flags = m_globals[g].flags | GF_RELOCS;
    if kind != DR_ABS64 { f_brelocs.push((m_drelocs.len - 1) as! u32); }
}

// Writes initializer n of type q at m_data[at] (offset `off` in global g).
recursive fn sinit(g: u32, at: i64, off: i64, q: u32, n: u32) {
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_ZEROINIT { return; }
    if (k == N_ICAST || k == N_CAST) && nd.op == CK_LVAL2RVAL && nkind(nd.a) == N_COMPLIT {
        // a compound literal read in a static initializer: its initializer
        sinit(g, at, off, q, nodes[nd.a].a);
        return;
    }
    if k == N_INITLIST {
        let tk = kind_of(q);
        if tk == TY_STRUCT {
            let r = rec_of(q);
            var ci = 0;
            let first = records[r].first as i64;
            let cnt = records[r].count as i64;
            for i in first..first + cnt {
                let f = fields[i];
                if f.width >= 0 && f.name == 0 { continue; }
                if ci >= nd.c as i64 { break; }
                let child = nlist[nd.v + ci];
                ci++;
                if f.width >= 0 {
                    if f.width > 0 { sinit_bitfield(at, f, child); }
                    continue;
                }
                sinit(g, at + f.offset, off + f.offset, f.ty, child);
            }
            return;
        }
        if tk == TY_UNION {
            if nd.a == 0 || nd.c == 0 { return; }
            let f = fields[records[rec_of(q)].first + nd.a - 1];
            let child = nlist[nd.v];
            if f.width >= 0 {
                if f.width > 0 { sinit_bitfield(at, f, child); }
                return;
            }
            sinit(g, at + f.offset, off + f.offset, f.ty, child);
            return;
        }
        if tk == TY_ARRAY {
            let et = tbase(q);
            let es = type_size(et);
            for i in nd.c { sinit(g, at + i * es, off + i * es, et, nlist[nd.v + i]); }
            if nd.b != 0 && !is_zero_init(nd.b) {
                let n_el = types[q >> 4].n;
                for i in (nd.c as i64)..n_el { sinit(g, at + i * es, off + i * es, et, nd.b); }
            }
            return;
        }
        if tk == TY_COMPLEX && nd.c >= 1 {
            let et = cplx_elem(q);
            sinit(g, at, off, et, nlist[nd.v]);
            if nd.c >= 2 { sinit(g, at + type_size(et), off + type_size(et), et, nlist[nd.v + 1]); }
            return;
        }
        if tk == TY_VECTOR || tk == TY_EXTVECTOR {
            let et = tbase(q);
            let es = type_size(et);
            var pos: i64 = 0;
            for i in nd.c {
                let child = nlist[nd.v + i];
                let ct = nty(child);
                if is_vector(ct) {
                    sinit(g, at + pos, off + pos, ct, child);
                    pos += type_size(ct);
                } else {
                    sinit(g, at + pos, off + pos, et, child);
                    pos += es;
                }
            }
            return;
        }
        // a scalar in braces
        if nd.c > 0 { sinit(g, at, off, q, nlist[nd.v]); }
        return;
    }
    if k == N_STRING {
        let b = str_bytes(nd.a);
        var size = type_size(q);
        if size < 0 { size = b.len; }
        for i in b.len {
            if i >= size { break; }
            m_data[at + i] = b[i];
        }
        return;
    }
    if k == N_COMPLIT {
        sinit(g, at, off, q, nodes[n].a);
        return;
    }
    if (k == N_ICAST || k == N_CAST) && (nd.op == CK_NOOP || nd.op == CK_LVAL2RVAL) && vkind(q) == VK_AGG {
        sinit(g, at, off, q, nd.a);
        return;
    }
    let vk = vkind(q);
    if vk == VK_COMPLEX {
        let et = cplx_elem(q);
        let es = type_size(et);
        sinit_complex(g, at, off, q, n);
        return;
    }
    if is_vector(q) {
        sinit_vector(g, at, off, q, n);
        return;
    }
    sinit_scalar(g, at, off, q, n);
}

fn sinit_bitfield(at: i64, f: Field, child: u32) {
    let ok, v = fold_int(child);
    if !ok { return; }
    let w = f.width as i64;
    let bp = f.bitpos;
    let uv = (v as! u64) & mask_of(w as! u32);
    for i in w {
        if (uv >> (i as! u64)) & 1 != 0 {
            let bit = bp + i;
            m_data[at + bit / 8] = m_data[at + bit / 8] | (((1 as u64) << ((bit % 8) as! u64)) as! u8);
        }
    }
}

recursive fn sinit_scalar(g: u32, at: i64, off: i64, q: u32, n: u32) {
    let k = kind_of(q);
    let size = type_size(q);
    if is_real_float(q) {
        if nkind(n) == N_BUILTIN && nodes[n].op == BI_CALL && starts_with(strip_builtin(sym_name(nodes[n].a as i64)), "nan") &&
           unqual(nty(n)) == unqual(q) && k != TY_LDOUBLE {
            // NaN bits as written (a signaling NaN must not pass through the x87)
            let nn = strip_builtin(sym_name(nodes[n].a as i64));
            let c = fp_nan_const(vty(unqual(q)), !starts_with(nn, "nans"), nan_payload(barg(n, 0)));
            put_bytes(at, m_consts[cidx(c)].lo, size);
            return;
        }
        let ok, x = static_f80(n);
        if !ok {
            init_error(n);
            return;
        }
        if k == TY_LDOUBLE || (opt_a64 && k == TY_FLOAT128) {
            put_bytes(at, x.lo, 8);
            put_bytes(at + 8, x.hi, if opt_a64 { 8 } else { 2 });
            return;
        }
        let d = f80_to_f64(x);
        if k == TY_DOUBLE { put_bytes(at, reinterpret_i64(d) as! u64, 8); }
        else if k == TY_FLOAT { put_bytes(at, f80_to_f32bits(x) as u64, 4); }
        else if k == TY_FLOAT16 { put_bytes(at, f64_to_f16bits(d) as u64, 2); }
        return;
    }
    if is_integer(q) && k != TY_INT128 && k != TY_UINT128 {
        let ok, v = fold_int(n);
        if ok {
            put_bytes(at, v as! u64, size);
            return;
        }
    }
    if k == TY_INT128 || k == TY_UINT128 {
        let ok, lo, hi = fold_int128(n);
        if ok {
            put_bytes(at, lo, 8);
            put_bytes(at + 8, hi, 8);
            return;
        }
    }
    // an address constant
    let ok, target, addend, lab, lab2 = eval_addr(n);
    if !ok {
        init_error(n);
        return;
    }
    if target < 0 && lab < 0 {
        put_bytes(at, addend as! u64, size);
        return;
    }
    if lab >= 0 {
        if lab2 >= 0 {
            add_reloc(g, off, f_global, DR_BLOCKDIFF32, addend, label_block(lab), label_block(lab2));
            return;
        }
        add_reloc(g, off, f_global, DR_BLOCK, addend, label_block(lab), 0);
        return;
    }
    if size != 8 {
        init_error(n);
        return;
    }
    add_reloc(g, off, target as! u32, DR_ABS64, addend, 0, 0);
}

fn init_error(n: u32) {
    err_at(nodes[n].loc, "initializer element is not a compile-time constant (goosecc lowering)");
}

recursive fn sinit_complex(g: u32, at: i64, off: i64, q: u32, n: u32) {
    let et = cplx_elem(q);
    let es = type_size(et);
    let nd = nodes[n];
    let k = nd.kind as i64;
    if (k == N_ICAST || k == N_CAST) && nd.op == CK_REAL2COMPLEX {
        sinit_scalar(g, at, off, et, conv_node(nd.a, et));
        return;
    }
    if (k == N_ICAST || k == N_CAST) && (nd.op == CK_COMPLEXCAST || nd.op == CK_NOOP) {
        let st = cplx_elem(nty(nd.a));
        if st == et || nd.op == CK_NOOP { sinit_complex(g, at, off, q, nd.a); return; }
        // convert each part: only constant parts are supported
        let ok, re, im = static_cplx(nd.a);
        if ok { put_cplx(at, et, re, im); return; }
        init_error(n);
        return;
    }
    let ok, re, im = static_cplx(n);
    if ok { put_cplx(at, et, re, im); return; }
    init_error(n);
}

fn put_cplx(at: i64, et: u32, re: F80, im: F80) {
    let es = type_size(et);
    let k = kind_of(et);
    if is_integer(et) {
        put_bytes(at, f80_to_i64(re) as! u64, es);
        put_bytes(at + es, f80_to_i64(im) as! u64, es);
        return;
    }
    if k == TY_LDOUBLE {
        let hs = if opt_a64 { 8 } else { 2 };
        put_bytes(at, re.lo, 8);
        put_bytes(at + 8, re.hi, hs);
        put_bytes(at + es, im.lo, 8);
        put_bytes(at + es + 8, im.hi, hs);
    } else if k == TY_DOUBLE {
        put_bytes(at, reinterpret_i64(f80_to_f64(re)) as! u64, 8);
        put_bytes(at + 8, reinterpret_i64(f80_to_f64(im)) as! u64, 8);
    } else if k == TY_FLOAT {
        put_bytes(at, f80_to_f32bits(re) as u64, 4);
        put_bytes(at + 4, f80_to_f32bits(im) as u64, 4);
    } else if k == TY_FLOAT16 {
        put_bytes(at, f64_to_f16bits(f80_to_f64(re)) as u64, 2);
        put_bytes(at + 2, f64_to_f16bits(f80_to_f64(im)) as u64, 2);
    }
}

fn conv_node(n: u32, et: u32) -> u32 { n }

recursive fn sinit_vector(g: u32, at: i64, off: i64, q: u32, n: u32) {
    let nd = nodes[n];
    let k = nd.kind as i64;
    if (k == N_ICAST || k == N_CAST) && (nd.op == CK_BITCAST || nd.op == CK_NOOP) && is_vector(nty(nd.a)) {
        sinit_vector(g, at, off, nty(nd.a), nd.a);
        return;
    }
    if (k == N_ICAST || k == N_CAST) && nd.op == CK_VECSPLAT {
        let et = tbase(q);
        let es = type_size(et);
        let lanes = types[q >> 4].n;
        for i in lanes { sinit_scalar(g, at + i * es, off + i * es, et, nd.a); }
        return;
    }
    if k == N_INITLIST {
        sinit(g, at, off, q, n);
        return;
    }
    init_error(n);
}

// ------------------------------------------------------- constant evaluation

// The value of a constant arithmetic expression as an f80 (exact for
// every integer and FP type, long double folded in long double).
recursive fn static_f80(n: u32) -> bool, F80 {
    let nd = nodes[n];
    let k = nd.kind as i64;
    let z = F80 { lo: 0, hi: 0 };
    if k == N_FLOAT {
        let fk = kind_of(nd.ty);
        if nd.c > 0 {
            let text = src[nd.b..nd.b + nd.c];
            if fk == TY_LDOUBLE { return true, strtold(text); }
            if fk == TY_FLOAT { return true, f64_to_f80(f32bits_to_f64(strtod_bits(text, 0) as! u32)); }
            if fk == TY_FLOAT16 { return true, f64_to_f80(f16bits_to_f64(strtod_bits(text, 3) as! u32)); }
            return true, f64_to_f80(reinterpret_f64(strtod_bits(text, 1) as! i64));
        }
        return true, f64_to_f80(reinterpret_f64(nd.v));
    }
    if is_integer(nd.ty) {
        let ok, v = fold_int(n);
        if !ok { return false, z; }
        if kind_of(nd.ty) != TY_BOOL && !is_signed(nd.ty) { return true, u64_to_f80(v as! u64); }
        return true, i64_to_f80(v);
    }
    if k == N_ICAST || k == N_CAST {
        let op = nd.op as i64;
        if op == CK_LVAL2RVAL && fold_cvars && is_real_float(nd.ty) {
            // a const variable's value (G1: clang's evaluator reads it)
            var init: u32 = 0;
            if nkind(nd.a) == N_DECLREF { init = cvar_value_init(nodes[nd.a].a as i64); }
            else if nkind(nd.a) == N_MEMBER || nkind(nd.a) == N_INDEX { let i2, w = cvar_member_init(nd.a); init = i2; }
            if init == 0 { return false, z; }
            cv_depth++;
            let ok, x = static_f80(init);
            cv_depth--;
            return ok, x;
        }
        if op == CK_INT2FLOAT || op == CK_FLOATCAST || op == CK_NOOP || op == CK_ATOMIC {
            let ok, x = static_f80(nd.a);
            if !ok { return false, z; }
            return true, round_to(x, nd.ty);
        }
        if op == CK_COMPLEX2REAL {
            let ok, re, im = static_cplx(nd.a);
            return ok, round_to(re, nd.ty);
        }
        return false, z;
    }
    if k == N_UNARY {
        let ok, x = static_f80(nd.a);
        if !ok { return false, z; }
        if nd.op == U_NEG { return true, F80 { lo: x.lo, hi: x.hi ^ ld_sign() }; }
        if nd.op == U_PLUS || nd.op == U_EXTENSION { return true, x; }
        if nd.op == U_REAL { return true, x; }
        return false, z;
    }
    if k == N_BINARY && is_real_float(nd.ty) {
        let ok, a = static_f80(nd.a);
        let ok2, b = static_f80(nd.b);
        if !ok || !ok2 { return false, z; }
        let op = match nd.op { B_ADD => 0, B_SUB => 1, B_MUL => 2, B_DIV => 3, _ => -1 };
        if op < 0 { return false, z; }
        return true, f80_arith(op, a, b, type_bits_code(nd.ty));
    }
    if k == N_COND {
        let ok, c = fold_bool(nd.a);
        if !ok { return false, z; }
        if c { return static_f80(if nd.b == 0 { nd.a } else { nd.b }); }
        return static_f80(nd.c);
    }
    if k == N_BUILTIN && nd.op == BI_CALL { return static_fp_builtin(n); }
    return false, z;
}

// __builtin_inf / nan / copysign / fabs in static initializers.
recursive fn static_fp_builtin(n: u32) -> bool, F80 {
    let nd = nodes[n];
    let z = F80 { lo: 0, hi: 0 };
    let name = strip_builtin(sym_name(nd.a as i64));
    let t = vty(unqual(nd.ty));
    if starts_with(name, "inf") || starts_with(name, "huge_val") {
        if t == GIR_T_F80 { return true, F80 { lo: 0x8000000000000000, hi: 0x7FFF }; }
        if t == GIR_T_F128 { return true, F80 { lo: 0, hi: 0x7FFF000000000000 }; }
        return true, f64_to_f80(reinterpret_f64(0x7FF0000000000000));
    }
    if starts_with(name, "nan") {
        let quiet = !starts_with(name, "nans");
        let c = fp_nan_const(t, quiet, nan_payload(barg(n, 0)));
        let cc = m_consts[cidx(c)];
        if is_ld(t) { return true, F80 { lo: cc.lo, hi: cc.hi }; }
        if t == GIR_T_F32 { return true, f64_to_f80(f32bits_to_f64(cc.lo as! u32)); }
        return true, f64_to_f80(reinterpret_f64(cc.lo as! i64));
    }
    if starts_with(name, "fabs") {
        let ok, x = static_f80(barg(n, 0));
        return ok, F80 { lo: x.lo, hi: x.hi & (ld_sign() - 1) };
    }
    if starts_with(name, "copysign") {
        let ok, x = static_f80(barg(n, 0));
        let ok2, y = static_f80(barg(n, 1));
        return ok && ok2, F80 { lo: x.lo, hi: (x.hi & (ld_sign() - 1)) | (y.hi & ld_sign()) };
    }
    return false, z;
}

// 0 = f32, 1 = f64, 2 = f80, 3 = f16
fn type_bits_code(q: u32) -> i64 {
    let k = kind_of(q);
    if k == TY_FLOAT { return 0; }
    if k == TY_DOUBLE { return 1; }
    if k == TY_FLOAT16 { return 3; }
    return 2;
}

fn round_to(x: F80, q: u32) -> F80 { f80_round(x, type_bits_code(q)) }

recursive fn static_cplx(n: u32) -> bool, F80, F80 {
    let nd = nodes[n];
    let k = nd.kind as i64;
    let z = F80 { lo: 0, hi: 0 };
    if k == N_BUILTIN && nd.op == BI_IMAG_CONST {
        let ok, x = static_f80(nd.a);
        return ok, z, x;
    }
    if k == N_ICAST || k == N_CAST {
        let op = nd.op as i64;
        if op == CK_REAL2COMPLEX {
            let ok, x = static_f80(nd.a);
            return ok, round_to(x, cplx_elem(nd.ty)), z;
        }
        if op == CK_COMPLEXCAST || op == CK_NOOP {
            let ok, re, im = static_cplx(nd.a);
            let et = cplx_elem(nd.ty);
            if is_integer(et) { return ok, re, im; }
            return ok, round_to(re, et), round_to(im, et);
        }
        return false, z, z;
    }
    if k == N_INITLIST {
        if nd.c == 0 { return true, z, z; }
        let ok, re = static_f80(nlist[nd.v]);
        if nd.c < 2 { return ok, re, z; }
        let ok2, im = static_f80(nlist[nd.v + 1]);
        return ok && ok2, re, im;
    }
    if k == N_BINARY && (nd.op == B_ADD || nd.op == B_SUB) {
        let ok, ar, ai = static_cplx_or_real(nd.a);
        let ok2, br, bi = static_cplx_or_real(nd.b);
        if !ok || !ok2 { return false, z, z; }
        let c = type_bits_code(cplx_elem(nd.ty));
        let op = if nd.op == B_ADD { 0 } else { 1 };
        return true, f80_arith(op, ar, br, c), f80_arith(op, ai, bi, c);
    }
    if k == N_BINARY && nd.op == B_MUL {
        let ok, ar, ai = static_cplx_or_real(nd.a);
        let ok2, br, bi = static_cplx_or_real(nd.b);
        if !ok || !ok2 { return false, z, z; }
        let c = type_bits_code(cplx_elem(nd.ty));
        let acv = f80_arith(2, ar, br, c);
        let bdv = f80_arith(2, ai, bi, c);
        let adv = f80_arith(2, ar, bi, c);
        let bcv = f80_arith(2, ai, br, c);
        return true, f80_arith(1, acv, bdv, c), f80_arith(0, adv, bcv, c);
    }
    if k == N_UNARY && nd.op == U_NEG {
        let ok, re, im = static_cplx(nd.a);
        return ok, F80 { lo: re.lo, hi: re.hi ^ ld_sign() }, F80 { lo: im.lo, hi: im.hi ^ ld_sign() };
    }
    if k == N_UNARY && (nd.op == U_PLUS || nd.op == U_EXTENSION) { return static_cplx(nd.a); }
    return false, z, z;
}

recursive fn static_cplx_or_real(n: u32) -> bool, F80, F80 {
    if is_complex(nty(n)) { return static_cplx(n); }
    let ok, x = static_f80(n);
    return ok, x, F80 { lo: 0, hi: 0 };
}

// 128-bit integer constants (values that fold_int can hold, sign-extended,
// and shifts / arithmetic on them).
recursive fn fold_int128(n: u32) -> bool, u64, u64 {
    let nd = nodes[n];
    let k = nd.kind as i64;
    let tk = kind_of(nty(n));
    let wide = tk == TY_INT128 || tk == TY_UINT128;
    if !wide || k == N_INT {
        // fold_int is exact for types of 64 bits or less (and for literals)
        let ok, v = fold_int(n);
        if !ok { return false, 0, 0; }
        let signed = tk != TY_BOOL && is_signed(nty(n));
        return true, v as! u64, if v < 0 && (signed || k == N_INT) { 0xFFFFFFFFFFFFFFFF } else { 0 };
    }
    if k == N_ICAST || k == N_CAST {
        if nd.op == CK_INTEGRAL || nd.op == CK_NOOP {
            let st = nty(nd.a);
            if kind_of(st) == TY_INT128 || kind_of(st) == TY_UINT128 { return fold_int128(nd.a); }
            let ok2, x = fold_int(nd.a);
            if !ok2 { return false, 0, 0; }
            if kind_of(st) != TY_BOOL && is_signed(st) && x < 0 { return true, x as! u64, 0xFFFFFFFFFFFFFFFF; }
            return true, x as! u64, 0;
        }
        if nd.op == CK_FLOAT2INT {
            let ok2, f = static_f80(nd.a);
            if !ok2 { return false, 0, 0; }
            let lo, hi = f80_to_i128(f, kind_of(nd.ty) == TY_INT128);
            return true, lo, hi;
        }
        return false, 0, 0;
    }
    if k == N_UNARY {
        let ok2, lo, hi = fold_int128(nd.a);
        if !ok2 { return false, 0, 0; }
        if nd.op == U_NEG {
            let nlo = 0 - lo;
            let nhi = 0 - hi - (if lo != 0 { 1 } else { 0 });
            return true, nlo, nhi;
        }
        if nd.op == U_BITNOT { return true, ~lo, ~hi; }
        if nd.op == U_PLUS || nd.op == U_EXTENSION { return true, lo, hi; }
        return false, 0, 0;
    }
    if k == N_BINARY {
        let ok1, alo, ahi = fold_int128(nd.a);
        if !ok1 { return false, 0, 0; }
        if nd.op == B_SHL || nd.op == B_SHR {
            let ok2, sh = fold_int(nd.b);
            if !ok2 || sh < 0 || sh >= 128 { return false, 0, 0; }
            let s = sh as! u64;
            if nd.op == B_SHL {
                if s == 0 { return true, alo, ahi; }
                if s >= 64 { return true, 0, alo << (s - 64); }
                return true, alo << s, (ahi << s) | (alo >> (64 - s));
            }
            let signed = kind_of(nd.ty) == TY_INT128;
            if s == 0 { return true, alo, ahi; }
            if s >= 64 {
                if signed { return true, ((ahi as! i64) >> (s - 64)) as! u64, ((ahi as! i64) >> 63) as! u64; }
                return true, ahi >> (s - 64), 0;
            }
            let nhi = if signed { ((ahi as! i64) >> s) as! u64 } else { ahi >> s };
            return true, (alo >> s) | (ahi << (64 - s)), nhi;
        }
        let ok2, blo, bhi = fold_int128(nd.b);
        if !ok2 { return false, 0, 0; }
        if nd.op == B_ADD {
            let lo = alo + blo;
            return true, lo, ahi + bhi + (if lo < alo { 1 } else { 0 });
        }
        if nd.op == B_SUB {
            let lo = alo - blo;
            return true, lo, ahi - bhi - (if alo < blo { 1 } else { 0 });
        }
        if nd.op == B_AND { return true, alo & blo, ahi & bhi; }
        if nd.op == B_OR { return true, alo | blo, ahi | bhi; }
        if nd.op == B_XOR { return true, alo ^ blo, ahi ^ bhi; }
        if nd.op == B_MUL {
            let lo, hi = mul128(alo, ahi, blo, bhi);
            return true, lo, hi;
        }
        return false, 0, 0;
    }
    return false, 0, 0;
}

fn mul128(alo: u64, ahi: u64, blo: u64, bhi: u64) -> u64, u64 {
    // 64x64 -> 128 by halves
    let a0 = alo & 0xFFFFFFFF;
    let a1 = alo >> 32;
    let b0 = blo & 0xFFFFFFFF;
    let b1 = blo >> 32;
    let p00 = a0 * b0;
    let p01 = a0 * b1;
    let p10 = a1 * b0;
    let p11 = a1 * b1;
    let mid = (p00 >> 32) + (p01 & 0xFFFFFFFF) + (p10 & 0xFFFFFFFF);
    let lo = (p00 & 0xFFFFFFFF) | (mid << 32);
    let hi = p11 + (p01 >> 32) + (p10 >> 32) + (mid >> 32) + alo * bhi + ahi * blo;
    return lo, hi;
}

// An address constant: (ok, target global or -1, addend, label, label2).
recursive fn eval_addr(n: u32) -> bool, i64, i64, i64, i64 {
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_INT { return true, -1, nd.v, -1, -1; }
    if k == N_ICAST || k == N_CAST {
        let op = nd.op as i64;
        if op == CK_ARRAY2PTR || op == CK_FUNC2PTR || op == CK_BUILTIN2PTR { return eval_lvaddr(nd.a); }
        if op == CK_BITCAST || op == CK_NOOP || op == CK_NULL2PTR || op == CK_INT2PTR || op == CK_PTR2INT ||
           op == CK_INTEGRAL || op == CK_ATOMIC {
            if op == CK_NULL2PTR { return true, -1, 0, -1, -1; }
            let ok, t, a, l1, l2 = eval_addr(nd.a);
            if !ok { return false, -1, 0, -1, -1; }
            if t < 0 && l1 < 0 && is_integer(nd.ty) && kind_of(nd.ty) != TY_INT128 { return true, -1, trunc_to(a, nd.ty), -1, -1; }
            return true, t, a, l1, l2;
        }
        if op == CK_LVAL2RVAL {
            // a read of a constant (const object with a known initializer) is not supported here
            return false, -1, 0, -1, -1;
        }
        return false, -1, 0, -1, -1;
    }
    if k == N_UNARY {
        if nd.op == U_ADDR { return eval_lvaddr(nd.a); }
        if nd.op == U_EXTENSION || nd.op == U_PLUS { return eval_addr(nd.a); }
        return false, -1, 0, -1, -1;
    }
    if k == N_LABELADDR {
        add_addr_label(nd.a as i64);
        return true, -1, 0, nd.a as i64, -1;
    }
    if k == N_BINARY {
        let op = nd.op as i64;
        if op == B_PTRADD || op == B_PTRSUB {
            let ok, t, a, l1, l2 = eval_addr(nd.a);
            let ok2, idx = fold_int(nd.b);
            if !ok || !ok2 { return false, -1, 0, -1, -1; }
            let ok3, es, ev = elem_size(tbase(nty(nd.a)));
            let d = idx * es;
            return true, t, if op == B_PTRADD { a + d } else { a - d }, l1, l2;
        }
        if op == B_ADD || op == B_SUB {
            let ok, t, a, l1, l2 = eval_addr(nd.a);
            let ok2, tb, b, m1, m2 = eval_addr(nd.b);
            if !ok || !ok2 { return false, -1, 0, -1, -1; }
            if op == B_SUB && l1 >= 0 && m1 >= 0 && l2 < 0 && m2 < 0 && t < 0 && tb < 0 {
                return true, -1, a - b, l1, m1;
            }
            if tb < 0 && m1 < 0 { return true, t, if op == B_ADD { a + b } else { a - b }, l1, l2; }
            if op == B_ADD && t < 0 && l1 < 0 { return true, tb, a + b, m1, m2; }
            if op == B_SUB && t == tb && l1 < 0 && m1 < 0 { return true, -1, a - b, -1, -1; }
            return false, -1, 0, -1, -1;
        }
        if op == B_PTRDIFF {
            let ok, t, a, l1, l2 = eval_addr(nd.a);
            let ok2, tb, b, m1, m2 = eval_addr(nd.b);
            if ok && ok2 && t < 0 && tb < 0 && l1 >= 0 && m1 >= 0 && l2 < 0 && m2 < 0 {
                return true, -1, a - b, l1, m1;
            }
            if ok && ok2 && t == tb && l1 < 0 && m1 < 0 {
                let ok3, es, ev = elem_size(tbase(nty(nd.a)));
                return true, -1, (a - b) / es, -1, -1;
            }
        }
        if op == B_COMMA { return eval_addr(nd.b); }
        return false, -1, 0, -1, -1;
    }
    if k == N_COND {
        let ok, c = fold_bool(nd.a);
        if !ok { return false, -1, 0, -1, -1; }
        if c { return eval_addr(if nd.b == 0 { nd.a } else { nd.b }); }
        return eval_addr(nd.c);
    }
    if k == N_STRING {
        let g = string_global(nd.a);
        dbg_string(n, g);
        return true, g as i64, 0, -1, -1;
    }
    let ok, v = fold_int(n);
    if ok { return true, -1, v, -1, -1; }
    return false, -1, 0, -1, -1;
}

recursive fn eval_lvaddr(n: u32) -> bool, i64, i64, i64, i64 {
    let nd = nodes[n];
    let k = nd.kind as i64;
    if k == N_DECLREF {
        let s = nd.a as i64;
        let sk = syms[s].kind;
        if sk == SK_FUNC || sk == SK_BUILTIN {
            if opt_debug { dbg_fnref(n); }
            return true, func_global(s) as i64, 0, -1, -1;
        }
        if sk == SK_VAR {
            var c = s;
            if syms[s].canon >= 0 && syms[s].canon as i64 != s { c = syms[s].canon as i64; }
            if syms[c].flags & SF_THREAD != 0 { return false, -1, 0, -1, -1; }
            return true, var_global(c) as i64, 0, -1, -1;
        }
        return false, -1, 0, -1, -1;
    }
    if k == N_STRING {
        let g = string_global(nd.a);
        dbg_string(n, g);
        return true, g as i64, 0, -1, -1;
    }
    if k == N_COMPLIT { return true, complit_global(n) as i64, 0, -1, -1; }
    if k == N_MEMBER {
        let f = fields[nd.b];
        if f.width >= 0 { return false, -1, 0, -1, -1; }
        if nd.op == 1 {
            let ok, t, a, l1, l2 = eval_addr(nd.a);
            return ok, t, a + f.offset, l1, l2;
        }
        let ok, t, a, l1, l2 = eval_lvaddr(nd.a);
        return ok, t, a + f.offset, l1, l2;
    }
    if k == N_INDEX {
        if nd.op == 1 {
            let ok, t, a, l1, l2 = eval_lvaddr(nd.a);
            let ok2, idx = fold_int(nd.b);
            if !ok || !ok2 { return false, -1, 0, -1, -1; }
            return true, t, a + idx * type_size(nd.ty), l1, l2;
        }
        let ok, t, a, l1, l2 = eval_addr(nd.a);
        let ok2, idx = fold_int(nd.b);
        if !ok || !ok2 { return false, -1, 0, -1, -1; }
        let ok3, es, ev = elem_size(nd.ty);
        return true, t, a + idx * es, l1, l2;
    }
    if k == N_UNARY {
        if nd.op == U_DEREF { return eval_addr(nd.a); }
        if nd.op == U_REAL { return eval_lvaddr(nd.a); }
        if nd.op == U_IMAG {
            let ok, t, a, l1, l2 = eval_lvaddr(nd.a);
            return ok, t, a + type_size(nd.ty), l1, l2;
        }
        if nd.op == U_EXTENSION { return eval_lvaddr(nd.a); }
    }
    if (k == N_ICAST || k == N_CAST) && (nd.op == CK_NOOP || nd.op == CK_LVAL2RVAL) { return eval_lvaddr(nd.a); }
    return false, -1, 0, -1, -1;
}
