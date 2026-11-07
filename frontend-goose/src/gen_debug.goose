// goosecc B2: debug locations (-g). The GIR debug tables are filled as
// tools/goovm-llc fills them from clang's DILocations: one compile unit, a
// subprogram per function, a lexical block per scope clang opens (a nested
// compound statement, a for statement and its condition, the condition of
// an if: CodeGen's LexicalScopes), files and strings; every instruction's
// `dbg` names (line, column, scope) of the statement or expression it was
// lowered from. B5: each scope also gets a record that the DWARF builder
// (gen_dwarf.goose) uses to place the function's variables and labels.

namespace gen;

import std;
import dictionary;
import os;
import .common;
import .types;
import .ast;
import .ppexpr;

var dfile_of: i32[>..] = [];               // frontend file -> dfiles index (-1 not yet)
var dbg_cu: u32 = 0;
var dbg_sp: u32 = 0;                       // the current subprogram
// The stack of lexical scopes: its DScope (0 = not made yet), where it
// starts, its record in f_srecs.
struct DbgScope { scope: u32, loc: u32, rec: u32 }
var dbg_scopes: DbgScope[>..<] = [];
// The scopes of the function being lowered, in the order they were opened:
// the enclosing one (-1 for the function's own scope, record 0) and the
// DScope it got (0: no location was ever in it).
struct DScopeRec { parent: i32, dscope: u32 }
var f_srecs: DScopeRec[>..<] = [];
var last_line: u32 = 0;
var last_col: u32 = 0;
var last_scope: u32 = 0;
var comp_dir: u8[>..] = [];
var dbg_lang: u32 = 0x1d;

fn dstring(s: const u8[:]) -> u32 {
    if s.len == 0 { return 0; }
    let id = intern(s);
    let r = gmap.get(gk(GM_DSTR, id));
    if r { return r; }
    let off = m_dstr.len as! u32;
    m_dstr.append(s);
    m_dstr.push(0);
    gmap.insert(gk(GM_DSTR, id), off);
    return off;
}

fn dbg_init(main_file: const u8[:]) {
    if !opt_debug { return; }
    mx_prepare();
    var d: u8[>..] = [];
    if !env("PWD", d) { d.append("."); }
    comp_dir.append(d);
    let f = dfile_for_name(main_file);
    // DW_AT_language as clang chooses it: C11 for C11 and later
    let v = std_version();
    dbg_lang = if v.len == 0 { 0x0001 } else if v == "199901L" { 0x000c } else { 0x001d };
    m_dscopes.push(DScope { kind: 1, parent: 0, file: f, line: dbg_lang, name: dstring("goosecc (goovm B5)"), extra: 0 });
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
    if f < files.len {
        let o = files[f].sp_off as i64;
        nm = names[o..o + files[f].sp_len];
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
    cur_dbg = 0;
    if !opt_debug { return; }
    let xl = expansion_loc(loc) as i64;
    let f = file_of(xl);
    var line: i64 = 0;
    var file: u32 = 0;
    if f >= 0 {
        let l, c = line_col(f, xl);
        line = l;
        file = dfile(f);
    }
    m_dscopes.push(DScope { kind: 2, parent: dbg_cu, file: file, line: line as! u32, name: dstring(ident_text(syms[s].name as i64)), extra: 0 });
    dbg_sp = (m_dscopes.len - 1) as! u32;
    f_srecs.clear();
    f_srecs.push(DScopeRec { parent: -1, dscope: dbg_sp });
}

fn dbg_function_end() -> u32 {
    if !opt_debug { return 0; }
    cur_dbg = 0;
    return dbg_sp;
}

fn dbg_scope_enter(n: u32) { dbg_scope_enter_at(nodes[n].loc); }

// A scope that starts at loc.
fn dbg_scope_enter_at(loc: u32) {
    if !opt_debug { return; }
    // the function body is the subprogram itself
    if dbg_scopes.len == 0 {
        dbg_scopes.push(DbgScope { scope: dbg_sp, loc: loc, rec: 0 });
        return;
    }
    let rec = f_srecs.len as! u32;
    f_srecs.push(DScopeRec { parent: dbg_scopes[dbg_scopes.len - 1].rec as! i32, dscope: 0 });
    dbg_scopes.push(DbgScope { scope: 0, loc: loc, rec: rec });
}

fn dbg_scope_leave() {
    if !opt_debug { return; }
    let t = dbg_scopes.pop();
    if t.rec != 0 { f_srecs[t.rec].dscope = t.scope; }
}

// The record of the innermost scope (where a declaration is).
fn dbg_cur_rec() -> u32 {
    if dbg_scopes.len == 0 { return 0; }
    return dbg_scopes[dbg_scopes.len - 1].rec;
}

// The innermost lexical scope (made on first use).
fn dbg_cur_scope() -> u32 {
    var k = dbg_scopes.len - 1;
    if k < 0 { return dbg_sp; }
    if dbg_scopes[k].scope != 0 { return dbg_scopes[k].scope; }
    // make the missing blocks from the outside in
    var i: i64 = 0;
    var parent = dbg_sp;
    while i <= k {
        if dbg_scopes[i].scope == 0 {
            let loc = expansion_loc(dbg_scopes[i].loc) as i64;
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
            dbg_scopes[i].scope = (m_dscopes.len - 1) as! u32;
        }
        parent = dbg_scopes[i].scope;
        i++;
    }
    return dbg_scopes[k].scope;
}

var last_loc: u32 = 0;      // the location of the statement being lowered (for late diagnostics)

inline fn set_loc(loc: u32) {
    last_loc = loc;
    if opt_debug && f_sym >= 0 { set_loc_dbg(loc); }
}

// Expressions are attributed as clang's CodeGen attributes them: every
// expression it visits (EmitLValue, the scalar, complex and aggregate
// emitters) sets the location to the expression's getExprLoc() and restores
// the previous one afterwards (ApplyDebugLocation), so an operation lands on
// its operator, a call on the callee's first token, a load on what is
// loaded, and a statement's own instructions (branches, returns, stores of
// initializers) on the statement.

// clang's getBeginLoc(): the first token of expression n.
fn begin_loc(n: u32) -> u32 {
    var m = n;
    loop {
        let nd = nodes[m];
        let k = nd.kind as i64;
        if nd.a != 0 && (k == N_ICAST || k == N_MEMBER || k == N_INDEX || k == N_CALL || k == N_SWIZZLE || k == N_COND ||
                         k == N_BINARY || k == N_ASSIGN || (k == N_UNARY && (nd.op == U_POSTINC || nd.op == U_POSTDEC))) {
            m = nd.a;
            continue;
        }
        return nd.loc;
    }
}

// clang's getExprLoc(): operators at the operator, member accesses at the
// member, subscripts at their base, implicit casts, calls and ?: at their
// first token.
fn expr_loc(n: u32) -> u32 {
    var m = n;
    loop {
        let nd = nodes[m];
        let k = nd.kind as i64;
        if k == N_ICAST || k == N_CALL || k == N_COND { return begin_loc(m); }
        if k == N_INDEX && nd.a != 0 { m = nd.a; continue; }
        return nd.loc;
    }
}

// Where the emitters attribute expression n's own instructions: its
// getExprLoc(), except that a load (an lvalue-to-rvalue conversion) is made
// while visiting what is loaded (ScalarExprEmitter visits the operand).
fn visit_loc(n: u32) -> u32 {
    let nd = nodes[n];
    if nd.kind == N_ICAST && nd.op == CK_LVAL2RVAL && nd.a != 0 { return expr_loc(nd.a); }
    return expr_loc(n);
}

// Lowering the condition of a loop: clang evaluates it as a value
// (EvaluateExprAsBool), so its final conversion and branch are at the loop.
var dbg_loopcond: bool = false;

// Enters a location; returns the one to restore with pop_loc.
fn push_loc(loc: u32) -> u32 {
    let saved = cur_dbg;
    set_loc_dbg(loc);
    return saved;
}

fn pop_loc(saved: u32) {
    if cur_dbg == saved { return; }
    cur_dbg = saved;
    if saved != 0 {
        let d = m_dlocs[saved];
        last_line = d.line;
        last_col = d.col;
        last_scope = d.scope;
        last_raw = dloc_raw[saved];
    } else {
        last_line = 0;
        last_col = 0;
        last_scope = 0;
        last_raw = 0;
    }
}

inline fn dbg_on() -> bool { opt_debug && f_sym >= 0 }

// The outermost function-like macro invocations, sorted and disjoint:
// the name's offset and the ')''s.
struct MxRange { start: u32, end: u32 }
var mx: MxRange[>..] = [];

fn mx_prepare() {
    sort(mx_ranges);
    for r in mx_ranges {
        let s = (r >> 32) as! u32;
        let e = (r & 0xFFFFFFFF) as! u32;
        // an invocation in the arguments of another one is inside it
        if mx.len > 0 && s <= mx[mx.len - 1].end { continue; }
        mx.push(MxRange { start: s, end: e });
    }
}

// clang's expansion location: code from a macro, its arguments included,
// is at the outermost invocation's name. (Tokens of macro bodies already
// carry the invocation's location: its name for an object-like macro, its
// ')' for a function-like one.)
var mx_hint: i64 = 0;                      // the range found last

fn expansion_loc(loc: u32) -> u32 {
    // locations come mostly in order: try the last range and the gap after it
    let h = mx_hint;
    if h < mx.len && mx[h].start <= loc {
        if loc <= mx[h].end { return mx[h].start; }
        if h + 1 >= mx.len || loc < mx[h + 1].start { return loc; }
    }
    var lo: i64 = 0;
    var hi = mx.len;
    while lo < hi {
        let mid = (lo + hi) / 2;
        if mx[mid].start <= loc { lo = mid + 1; } else { hi = mid; }
    }
    if lo > 0 { mx_hint = lo - 1; }
    if lo > 0 && loc <= mx[lo - 1].end { return mx[lo - 1].start; }
    return loc;
}

var last_raw: u32 = 0;                     // the source offset of the current location
var dloc_raw: u32[>..] = [];               // per m_dlocs entry: its source offset

fn set_loc_dbg(loc0: u32) {
    if !opt_debug || f_sym < 0 { return; }
    let sc = dbg_cur_scope();
    if loc0 == last_raw && sc == last_scope && cur_dbg != 0 { return; }
    let loc = expansion_loc(loc0);
    let f = file_of(loc as i64);
    if f < 0 { return; }
    let line, col = line_col(f, loc as i64);
    let l = line as! u32;
    let c = col as! u32;
    last_raw = loc0;
    if l == last_line && c == last_col && sc == last_scope && cur_dbg != 0 { return; }
    m_dlocs.push(DLoc { line: l, col: c, scope: sc, inlined_at: 0 });
    while dloc_raw.len < m_dlocs.len { dloc_raw.push(0); }
    dloc_raw[m_dlocs.len - 1] = loc0;
    cur_dbg = (m_dlocs.len - 1) as! u32;
    last_line = l;
    last_col = c;
    last_scope = sc;
}
