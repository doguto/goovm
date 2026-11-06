// goosecc B2: debug locations (-g). The GIR debug tables are filled as
// tools/goovm-llc fills them from clang's DILocations: one compile unit, a
// subprogram per function, a lexical block per nested compound statement,
// files and strings; every instruction's `dbg` names (line, column, scope)
// of the statement or expression it was lowered from.

namespace gen;

import std;
import dictionary;
import os;
import .common;
import .types;
import .ast;

var dstr_map = dictionary<u32, u32> {};    // interned string -> offset in m_dstr
var dfile_of: i32[>..] = [];               // frontend file -> dfiles index (-1 not yet)
var dbg_cu: u32 = 0;
var dbg_sp: u32 = 0;                       // the current subprogram
var dbg_scopes: u32[>..<] = [];            // the stack of lexical scopes (0 = not made yet)
var dbg_scope_nodes: u32[>..<] = [];
var last_line: u32 = 0;
var last_col: u32 = 0;
var last_scope: u32 = 0;
var comp_dir: u8[>..] = [];
var dbg_lang: u32 = 0x1d;

fn dstring(s: const u8[:]) -> u32 {
    if s.len == 0 { return 0; }
    let id = intern(s);
    let r = dstr_map.get(id);
    if r { return r; }
    let off = m_dstr.len as! u32;
    m_dstr.append(s);
    m_dstr.push(0);
    dstr_map.insert(id, off);
    return off;
}

fn dbg_init(main_file: const u8[:]) {
    if !opt_debug { return; }
    var d: u8[>..] = [];
    if !env("PWD", d) { d.append("."); }
    comp_dir.append(d);
    let f = dfile_for_name(main_file);
    m_dscopes.push(DScope { kind: 1, parent: 0, file: f, line: dbg_lang, name: dstring("goosecc (goovm B2)"), extra: 0 });
    dbg_cu = (m_dscopes.len - 1) as! u32;
}

fn dfile_for_name(nm: const u8[:]) -> u32 {
    m_dfiles.push(DFile { name: dstring(nm), dir: dstring(comp_dir) });
    return (m_dfiles.len - 1) as! u32;
}

fn dfile(f: i64) -> u32 {
    while dfile_of.len <= f { dfile_of.push(-1); }
    if dfile_of[f] >= 0 { return dfile_of[f] as! u32; }
    let p = files[f].path as i64;
    var nm = names[p..p + files[f].path_len];
    if f < file_spelling.len {
        let o = file_spelling[f] as i64;
        nm = names[o..o + file_spelling_len[f]];
    }
    let d = dfile_for_name(nm);
    dfile_of[f] = d as! i32;
    return d;
}

fn dbg_function_begin(s: i64, loc: u32) {
    last_line = 0;
    last_col = 0;
    last_scope = 0;
    dbg_scopes.clear();
    dbg_scope_nodes.clear();
    cur_dbg = 0;
    if !opt_debug { return; }
    let f = file_of(loc as i64);
    var line: i64 = 0;
    var file: u32 = 0;
    if f >= 0 {
        let l, c = line_col(f, loc as i64);
        line = l;
        file = dfile(f);
    }
    m_dscopes.push(DScope { kind: 2, parent: dbg_cu, file: file, line: line as! u32, name: dstring(ident_text(syms[s].name as i64)), extra: 0 });
    dbg_sp = (m_dscopes.len - 1) as! u32;
}

fn dbg_function_end() -> u32 {
    if !opt_debug { return 0; }
    cur_dbg = 0;
    return dbg_sp;
}

fn dbg_scope_enter(n: u32) {
    if !opt_debug { return; }
    // the function body is the subprogram itself
    dbg_scope_nodes.push(n);
    dbg_scopes.push(if dbg_scope_nodes.len == 1 { dbg_sp } else { 0 });
}

fn dbg_scope_leave() {
    if !opt_debug { return; }
    dbg_scope_nodes.pop();
    dbg_scopes.pop();
}

// The innermost lexical scope (made on first use).
fn dbg_cur_scope() -> u32 {
    var k = dbg_scopes.len - 1;
    if k < 0 { return dbg_sp; }
    if dbg_scopes[k] != 0 { return dbg_scopes[k]; }
    // make the missing blocks from the outside in
    var i: i64 = 0;
    var parent = dbg_sp;
    while i <= k {
        if dbg_scopes[i] == 0 {
            let n = dbg_scope_nodes[i];
            let loc = nodes[n].loc as i64;
            let f = file_of(loc);
            var line: i64 = 0;
            var col: i64 = 0;
            var file: u32 = 0;
            if f >= 0 {
                let l, c = line_col(f, loc);
                line = l;
                col = c;
                file = dfile(f);
            }
            m_dscopes.push(DScope { kind: 3, parent: parent, file: file, line: line as! u32, name: 0, extra: col as! u32 });
            dbg_scopes[i] = (m_dscopes.len - 1) as! u32;
        }
        parent = dbg_scopes[i];
        i++;
    }
    return dbg_scopes[k];
}

inline fn set_loc(loc: u32) { if opt_debug && f_sym >= 0 { set_loc_dbg(loc); } }

fn set_loc_dbg(loc: u32) {
    if !opt_debug || f_sym < 0 { return; }
    let f = file_of(loc as i64);
    if f < 0 { return; }
    let line, col = line_col(f, loc as i64);
    let sc = dbg_cur_scope();
    let l = line as! u32;
    let c = col as! u32;
    if l == last_line && c == last_col && sc == last_scope && cur_dbg != 0 { return; }
    m_dlocs.push(DLoc { line: l, col: c, scope: sc, inlined_at: 0 });
    cur_dbg = (m_dlocs.len - 1) as! u32;
    last_line = l;
    last_col = c;
    last_scope = sc;
}
