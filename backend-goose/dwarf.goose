// DWARF 5 debug information: .debug_line from the instructions' locations,
// .debug_info / .debug_abbrev from the DIE tables (gir.h; or, for a module
// with locations but no DIE table, a compile unit with one subprogram per
// function), with .debug_str(_offsets), .debug_addr, .debug_line_str and
// .debug_rnglists, as clang -g -O0 writes them.
//
// During code generation (cg.goose calls the dbg_* hooks only with debug
// information) the back-end records
//   - line-table rows, by LLVM's DwarfDebug::beginInstruction rules
//     (is_stmt on a new line, prologue_end, epilogue_begin, line-0 rows at
//     the top of blocks without a location, is_stmt forced on the first
//     line of a block that a predecessor leaves on another line);
//   - runs of instructions with one location, from which the code ranges of
//     lexical blocks follow (LLVM's LexicalScopes);
//   - the frame address of every variable of the DIE table;
//   - the code address of labels.
// dbg_write() then builds the sections; the DIE tree is written in one pass
// that resolves the GIR attribute forms into a body per DIE (with its
// abbreviation), and a second that places the bodies and fixes references.

var dbg_on = false;
var s_dbg: u8[>..] = [];       // all debug sections, one after the other

var sec_abbrev: u32 = 0;
var sec_info: u32 = 0;
var sec_stroff: u32 = 0;
var sec_str: u32 = 0;
var sec_addr: u32 = 0;
var sec_line: u32 = 0;
var sec_lstr: u32 = 0;
var sec_rng: u32 = 0;

let R_X86_64_32 = 10;
let R_X86_64_DTPOFF64 = 17;

// DWARF constants used here.
let DW_TAG_compile_unit = 0x11;
let DW_TAG_subprogram = 0x2e;
let DW_TAG_lexical_block = 0x0b;
let DW_TAG_variable = 0x34;
let DW_TAG_formal_parameter = 0x05;
let DW_TAG_label = 0x0a;
let DW_AT_name = 0x03;
let DW_AT_stmt_list = 0x10;
let DW_AT_low_pc = 0x11;
let DW_AT_high_pc = 0x12;
let DW_AT_language = 0x13;
let DW_AT_comp_dir = 0x1b;
let DW_AT_producer = 0x25;
let DW_AT_frame_base = 0x40;
let DW_AT_external = 0x3f;
let DW_AT_decl_file = 0x3a;
let DW_AT_decl_line = 0x3b;
let DW_AT_location = 0x02;
let DW_AT_ranges = 0x55;
let DW_AT_linkage_name = 0x6e;
let DW_AT_str_offsets_base = 0x72;
let DW_AT_addr_base = 0x73;
let DW_AT_rnglists_base = 0x74;
let DW_FORM_addr = 0x01;
let DW_FORM_block2 = 0x03;
let DW_FORM_data2 = 0x05;
let DW_FORM_data4 = 0x06;
let DW_FORM_data8 = 0x07;
let DW_FORM_block1 = 0x0a;
let DW_FORM_data1 = 0x0b;
let DW_FORM_flag = 0x0c;
let DW_FORM_sdata = 0x0d;
let DW_FORM_udata = 0x0f;
let DW_FORM_ref4 = 0x13;
let DW_FORM_sec_offset = 0x17;
let DW_FORM_exprloc = 0x18;
let DW_FORM_flag_present = 0x19;
let DW_FORM_strx1 = 0x25;
let DW_FORM_strx2 = 0x26;
let DW_FORM_strx3 = 0x27;
let DW_FORM_strx4 = 0x28;
let DW_FORM_addrx = 0x1b;
let DW_FORM_rnglistx = 0x23;
let DW_FORM_data16 = 0x1e;

// ------------------------------------------------------------ rows

// A line-table row at code offset pos (body-relative while the function is
// generated): location d (an index into dlocs), or with ROW_ZERO line 0 in
// the file and column of d, or with ROW_START the scope line of subprogram
// scope d.
struct LRow { pos: u32, d: u32, flags: u32 }
let ROW_STMT = 1;
let ROW_PEND = 2;      // prologue_end
let ROW_EPI = 4;       // epilogue_begin
let ROW_ZERO = 8;
let ROW_START = 16;
var rows: LRow[>..] = [];
var sec_rows0: u32[>..] = [];  // per code section: its rows are rows[sec_rows0[s] .. sec_rows1[s])
var sec_rows1: u32[>..] = [];

// The current function.
var df_sp: u32 = 0;            // its DISubprogram scope (0: no debug information)
var df_row0: i64 = 0;          // its first row (the ROW_START row)
var df_prev: u32 = 0;          // the last location with a line (LLVM's PrevInstLoc)
var df_line: u32 = 0;          // the line of the last row (LastAsmLine)
var df_top = false;            // at the first instruction of a block
var df_block = false;          // an instruction of an earlier block was seen (PrevInstBB)
var df_pend = false;           // prologue_end placed
var df_force = false;          // force is_stmt on this block's first line
var df_ret: u32 = 0;           // location of the function's last instruction if it is a RET
var blk_force: u8[>..] = [];   // per local block: force is_stmt on its first line
var blk_first: u32[>..] = [];  // per local block: first line / last line
var blk_last: u32[>..] = [];

// Runs of instructions with one location (body-relative code offsets).
struct Run { start: u32, end: u32, d: u32 }
var runs: Run[>..] = [];
var run_open = false;
var run_d: u32 = 0;
var run_start: u32 = 0;

// Lexical block code ranges (section-relative), a list per scope.
struct Rng { start: u32, end: u32, sec: u32, next: u32 }
var rngs: Rng[>..] = [];
var sc_head: u32[>..] = [];
var sc_tail: u32[>..] = [];
var sc_n: u32[>..] = [];
var sc_first: u32[>..] = [];   // open range of each scope (per function, sc_tag == epoch)
var sc_last: u32[>..] = [];
var sc_tag: u32[>..] = [];
var sc_epoch: u32 = 0;
// Per code section: the code of its functions with debug information.
var cs_lo: u32[>..] = [];
var cs_hi: u32[>..] = [];

// Variables (GIR_DF_LOCAL attributes): per function, in a counting sort by
// function, and the frame address found for each.
var lv_first: u32[>..] = [];   // per function: start of its run in lv_attr
var lv_attr: u32[>..] = [];    // DAttr indices
var lv_kind: u8[>..] = [];     // per DAttr index: LOC_*
var lv_off: i32[>..] = [];
let LOC_NONE = 0;
let LOC_FB = 1;                // DW_OP_fbreg off
let LOC_FB_DEREF = 2;          // DW_OP_fbreg off, DW_OP_deref
// Labels (GIR_DF_LABEL): code position per DAttr index.
var lb_first: u32[>..] = [];   // per function: its run in lb_attr (sorted by instruction)
var lb_attr: u32[>..] = [];
var lb_pos: u32[>..] = [];     // per DAttr index: section offset
var lb_sec: u32[>..] = [];
var lb_next: i64 = 0;          // next label of the current function
var lb_end: i64 = 0;

// The DIE table in use: the module's, or the one made for a module that has
// only locations.
var sy_dies: Die[>..] = [];
var sy_attrs: DAttr[>..] = [];
var use_sy = false;

fn dtab_n() -> i64 { if use_sy { sy_dies.len } else { M.dies.len } }
fn die_at(k: i64) -> Die { if use_sy { sy_dies[k] } else { M.dies[k] } }
fn attr_at(k: i64) -> DAttr { if use_sy { sy_attrs[k] } else { M.dattrs[k] } }

// The compile unit scope (0: none).
var cu_scope: u32 = 0;

fn dbg_init() {
    dbg_on = false;
    s_dbg.clear();
    rows.clear();
    runs.clear();
    rngs.clear();
    use_sy = false;
    cu_scope = 0;
    for S, k in M.dscopes {
        if S.kind == DS_CU {
            cu_scope = k as! u32;
            break;
        }
    }
    if cu_scope == 0 { return; }
    if M.dies.len == 0 && M.dlocs.len <= 1 { return; }
    dbg_on = true;
    let ns = M.dscopes.len;
    sc_head.clear();
    sc_head.resize(ns, GIR_NONE);
    sc_tail.clear();
    sc_tail.resize(ns, GIR_NONE);
    sc_n.clear();
    sc_n.resize(ns, 0);
    if sc_tag.len < ns {
        sc_first.resize(ns, 0);
        sc_last.resize(ns, 0);
        sc_tag.resize(ns, 0);
    }
    if M.dies.len == 0 { make_dies(); }
    index_attrs();
}

// Variables and labels of the DIE table, by function.
fn index_attrs() {
    let nf = M.funcs.len;
    let na = if use_sy { sy_attrs.len } else { M.dattrs.len };
    lv_first.clear();
    lv_first.resize(nf + 1, 0);
    lb_first.clear();
    lb_first.resize(nf + 1, 0);
    lv_kind.clear();
    lv_off.clear();
    lb_pos.clear();
    lb_sec.clear();
    var nl: i64 = 0;
    var nb: i64 = 0;
    for k in 0..na {
        let A = attr_at(k);
        if A.form == DF_LOCAL {
            let f: i64 = (A.val >> 32) as! i64;
            if f < nf { lv_first[f + 1] += 1; nl++; }
        } else if A.form == DF_LABEL {
            let gi: u32 = A.val as! u32;
            let f = func_of_inst(gi);
            if f != GIR_NONE { lb_first[f as i64 + 1] += 1; nb++; }
        }
    }
    if nl == 0 && nb == 0 { return; }
    lv_kind.resize(na, LOC_NONE);
    lv_off.resize(na, 0);
    lb_pos.resize(na, 0);
    lb_sec.resize(na, 0);
    for f in 0..nf {
        lv_first[f + 1] += lv_first[f];
        lb_first[f + 1] += lb_first[f];
    }
    lv_attr.clear();
    lv_attr.resize(nl, 0);
    lb_attr.clear();
    lb_attr.resize(nb, 0);
    var fill: u32[>..] = [];
    fill.resize(nf, 0);
    var fillb: u32[>..] = [];
    fillb.resize(nf, 0);
    for k in 0..na {
        let A = attr_at(k);
        if A.form == DF_LOCAL {
            let f: i64 = (A.val >> 32) as! i64;
            if f < nf {
                lv_attr[lv_first[f] + fill[f]] = k as! u32;
                fill[f] += 1;
            }
        } else if A.form == DF_LABEL {
            let f = func_of_inst(A.val as! u32);
            if f != GIR_NONE {
                let fi: i64 = f;
                // insertion into the function's run, sorted by instruction
                var p: i64 = lb_first[fi] + fillb[fi];
                while p > lb_first[fi] && attr_at(lb_attr[p - 1]).val > A.val {
                    lb_attr[p] = lb_attr[p - 1];
                    p--;
                }
                lb_attr[p] = k as! u32;
                fillb[fi] += 1;
            }
        }
    }
}
// The function that owns instruction gi (binary search), or GIR_NONE.
fn func_of_inst(gi: u32) -> u32 {
    var lo: i64 = 0;
    var hi: i64 = M.funcs.len;
    while lo < hi {
        let mid = (lo + hi) / 2;
        let F = M.funcs[mid];
        if gi < F.first_inst { hi = mid; }
        else if gi >= F.first_inst + F.n_inst { lo = mid + 1; }
        else { return mid as! u32; }
    }
    return GIR_NONE;
}

// A DIE table for a module that has only locations: the unit and a
// subprogram per function with a DISubprogram.
fn sy_attr(at: u32, form: u32, aux: u32, val: u64) {
    sy_attrs.push(DAttr { at: at as! u16, form: form as! u16, aux: aux, val: val });
}
fn make_dies() {
    use_sy = true;
    sy_dies.clear();
    sy_attrs.clear();
    let C = M.dscopes[cu_scope];
    let CF = M.dfiles[C.file];
    sy_attr(DW_AT_producer, DF_STR, 0, C.name);
    sy_attr(DW_AT_language, DW_FORM_data2, 0, C.line);
    sy_attr(DW_AT_name, DF_STR, 0, CF.name);
    sy_attr(DW_AT_str_offsets_base, DF_STR_BASE, 0, 0);
    sy_attr(DW_AT_stmt_list, DF_STMT_LIST, 0, 0);
    if CF.dir != 0 { sy_attr(DW_AT_comp_dir, DF_STR, 0, CF.dir); }
    sy_attr(DW_AT_low_pc, DF_CU_PC, 0, 0);
    sy_attr(DW_AT_addr_base, DF_ADDR_BASE, 0, 0);
    sy_dies.push(Die { tag: DW_TAG_compile_unit, flags: 0, parent: GIR_NONE, attrs: 0, n_attrs: sy_attrs.len as! u32 });
    for F, fi in M.funcs {
        if F.dbg == 0 { continue; }
        let S = M.dscopes[F.dbg];
        let a0 = sy_attrs.len as! u32;
        sy_attr(DW_AT_low_pc, DF_PC, 0, fi as! u64);
        sy_attr(DW_AT_frame_base, DF_FRAME_BASE, 0, 0);
        if S.extra != 0 && S.extra != S.name { sy_attr(DW_AT_linkage_name, DF_STR, 0, S.extra); }
        if S.name != 0 { sy_attr(DW_AT_name, DF_STR, 0, S.name); }
        if S.line != 0 {
            sy_attr(DW_AT_decl_file, DF_FILE, 0, S.file);
            sy_attr(DW_AT_decl_line, if S.line <= 0xFF { DW_FORM_data1 } else if S.line <= 0xFFFF { DW_FORM_data2 } else { DW_FORM_data4 }, 0, S.line);
        }
        if M.globals[F.global].flags & GF_INTERNAL == 0 { sy_attr(DW_AT_external, DW_FORM_flag_present, 0, 1); }
        sy_dies.push(Die { tag: DW_TAG_subprogram, flags: 0, parent: 0, attrs: a0, n_attrs: sy_attrs.len as! u32 - a0 });
    }
}

// The debug sections (all, in clang's order).
fn dbg_make_sections() {
    if !dbg_on { return; }
    sec_abbrev = osecs.len as! u32;
    add_osec(SHT_PROGBITS, 0, 1, 0, BUF_DBG, ".debug_abbrev");
    sec_info = osecs.len as! u32;
    add_osec(SHT_PROGBITS, 0, 1, 0, BUF_DBG, ".debug_info");
    sec_stroff = osecs.len as! u32;
    add_osec(SHT_PROGBITS, 0, 1, 0, BUF_DBG, ".debug_str_offsets");
    sec_str = osecs.len as! u32;
    add_osec(SHT_PROGBITS, SHF_MERGE | SHF_STRINGS, 1, 1, BUF_DBG, ".debug_str");
    sec_addr = osecs.len as! u32;
    add_osec(SHT_PROGBITS, 0, 1, 0, BUF_DBG, ".debug_addr");
    sec_line = osecs.len as! u32;
    add_osec(SHT_PROGBITS, 0, 1, 0, BUF_DBG, ".debug_line");
    sec_lstr = osecs.len as! u32;
    add_osec(SHT_PROGBITS, SHF_MERGE | SHF_STRINGS, 1, 1, BUF_DBG, ".debug_line_str");
    sec_rng = osecs.len as! u32;
    add_osec(SHT_PROGBITS, 0, 1, 0, BUF_DBG, ".debug_rnglists");
    let ns = osecs.len;
    sec_rows0.clear();
    sec_rows0.resize(ns, 0);
    sec_rows1.clear();
    sec_rows1.resize(ns, 0);
    cs_lo.clear();
    cs_lo.resize(ns, GIR_NONE);
    cs_hi.clear();
    cs_hi.resize(ns, 0);
}

// ------------------------------------------------- per function, early

// Values that are variables' addresses keep a frame slot (they are written
// there when defined), so that the variable has a location.
fn dbg_keep_homes(fi: u32) {
    if lv_first.len == 0 { return; }
    let a = lv_first[fi];
    let b = lv_first[fi as i64 + 1];
    for k in a..b {
        let A = attr_at(lv_attr[k]);
        let v: u32 = A.val as! u32;
        let kd = gir_kind(v);
        var id: u32 = 0;
        if kd == GIR_V_INST {
            let gi = gir_idx(v);
            if gi < f_first_inst || gi >= f_first_inst + f_nins { continue; }
            id = gi - f_first_inst;
            if vi[id].home == H_ALLOCA { continue; }
            if M.insts[gi].ty != GIR_T_PTR { continue; }
        } else if kd == GIR_V_ARG {
            if gir_idx(v) >= f_nargs { continue; }
            id = f_nins + gir_idx(v);
        } else {
            continue;
        }
        vi[id].st |= ST_GLOB;
        if vi[id].nuse == 0 { vi[id].nuse = 1; }
    }
}

// Per block: the first and last line, and whether the first line gets a
// forced is_stmt (a predecessor ends on another line, or has no line).
fn dbg_func_start(sp: u32) {
    df_sp = sp;
    df_prev = 0;
    df_line = 0;
    df_block = false;
    df_pend = false;
    df_ret = 0;
    runs.clear();
    run_open = false;
    if lb_first.len != 0 {
        lb_next = lb_first[f_index];
        lb_end = lb_first[f_index as i64 + 1];
    } else {
        lb_next = 0;
        lb_end = 0;
    }
    if sp == 0 { return; }
    df_row0 = rows.len;
    let S = M.dscopes[sp];
    rows.push(LRow { pos: 0, d: sp, flags: ROW_START | ROW_STMT });
    df_line = S.line;
    let nb = cur_nblocks;
    if blk_force.len < nb {
        blk_force.resize(nb, 0);
        blk_first.resize(nb, 0);
        blk_last.resize(nb, 0);
    }
    for b in 0..nb {
        blk_force[b] = 0;
        blk_first[b] = 0;
        blk_last[b] = 0;
        let B = M.blocks[f_first_block + b];
        for k in B.first_inst..B.first_inst + B.n_inst {
            let d = M.insts[k].dbg;
            if d == 0 { continue; }
            let ln = M.dlocs[d].line;
            if ln == 0 { continue; }
            if blk_first[b] == 0 { blk_first[b] = ln; }
            blk_last[b] = ln;
        }
    }
    // predecessors through the terminators: mark the successors whose first
    // line differs from this block's last line (1 = force, 2 = seen)
    for b in 0..nb {
        let B = M.blocks[f_first_block + b];
        if B.n_inst == 0 { continue; }
        let T = M.insts[B.first_inst + B.n_inst - 1];
        let op: u32 = T.op;
        let ll = blk_last[b];
        if op == GIR_BR { succ_edge(T.a, ll); }
        else if op == GIR_CONDBR {
            succ_edge(T.b, ll);
            succ_edge(T.c, ll);
        } else if op == GIR_SWITCH {
            succ_edge(M.opnds[T.b], ll);
            for q in 0..T.c { succ_edge(M.opnds[T.b + 2 + 2 * q], ll); }
        } else if op == GIR_INDIRECTBR {
            for q in 0..T.c { succ_edge(M.opnds[T.b + q], ll); }
        }
        // an invoke's landing pad
        if B.n_inst >= 2 {
            let C = M.insts[B.first_inst + B.n_inst - 2];
            if C.op == GIR_CALL && C.flags & IF_INVOKE != 0 { succ_edge(M.opnds[C.b + 2 * C.c], ll); }
        }
    }
    let L = M.insts[f_first_inst + f_nins - 1];
    if L.op == GIR_RET { df_ret = L.dbg; }
}
fn succ_edge(s: u32, ll: u32) {
    if s >= cur_nblocks { return; }
    if blk_first[s] != 0 && blk_first[s] != ll { blk_force[s] = 1; }
}

fn dbg_block_start() {
    df_top = true;
    df_force = blk_force[cur_blk] != 0;
}

fn row(d: u32, flags: u32, line: u32) {
    rows.push(LRow { pos: here(), d: d, flags: flags });
    df_line = line;
}

// Before instruction k: rows and runs, as LLVM's beginInstruction.
fn dbg_inst(k: u32) {
    while lb_next < lb_end && attr_at(lb_attr[lb_next]).val as! u32 <= k {
        lb_pos[lb_attr[lb_next]] = here();
        lb_next++;
    }
    let d = M.insts[k].dbg;
    if df_sp == 0 { return; }
    let top = df_top;
    df_top = false;
    if d == 0 {
        if df_line != 0 && top && df_block {
            rows.push(LRow { pos: here(), d: df_prev, flags: ROW_ZERO });
            df_line = 0;
        }
        df_block = true;
        return;
    }
    df_block = true;
    // runs: a new one at every change of location within a block
    if !run_open || d != run_d || top {
        if run_open { runs.push(Run { start: run_start, end: here(), d: run_d }); }
        run_open = true;
        run_d = d;
        run_start = here();
    }
    let L = M.dlocs[d];
    var force = false;
    if df_force && L.line != 0 {
        force = true;
        df_force = false;
    }
    if d == df_prev && !force {
        if df_line == 0 && L.line != 0 { row(d, 0, L.line); }
        return;
    }
    if L.line == 0 && df_line == 0 { return; }
    var fl: u32 = 0;
    if !df_pend && L.line != 0 {
        fl = ROW_PEND | ROW_STMT;
        df_pend = true;
    }
    let old: u32 = if df_prev != 0 { M.dlocs[df_prev].line } else { df_line };
    if L.line != 0 && (L.line != old || force) { fl |= ROW_STMT; }
    row(d, fl, L.line);
    if L.line != 0 { df_prev = d; }
}
fn dbg_block_end() {
    if run_open {
        runs.push(Run { start: run_start, end: here(), d: run_d });
        run_open = false;
    }
}
// The epilogue: the location of the last return, epilogue_begin.
fn dbg_epilogue() {
    while lb_next < lb_end {
        lb_pos[lb_attr[lb_next]] = here();
        lb_next++;
    }
    if df_sp == 0 || df_ret == 0 { return; }
    let L = M.dlocs[df_ret];
    var fl: u32 = ROW_EPI;
    if df_ret != df_prev {
        let old: u32 = if df_prev != 0 { M.dlocs[df_prev].line } else { df_line };
        if L.line != 0 && L.line != old { fl |= ROW_STMT; }
    }
    row(df_ret, fl, L.line);
    if L.line != 0 { df_prev = df_ret; }
}

// ------------------------------------------------- per function, late

// The innermost scope of a location for scope ranges: inlined code counts as
// its outermost call site; lexical block files are transparent.
fn run_scope(d0: u32) -> u32 {
    var d = d0;
    while M.dlocs[d].inlined_at != 0 { d = M.dlocs[d].inlined_at; }
    var s = M.dlocs[d].scope;
    while s != 0 && M.dscopes[s].kind == DS_FILE { s = M.dscopes[s].parent; }
    return s;
}
fn sc_parent(s: u32) -> u32 {
    var p = M.dscopes[s].parent;
    while p != 0 && M.dscopes[p].kind == DS_FILE { p = M.dscopes[p].parent; }
    if p != 0 && M.dscopes[p].kind != DS_LEXICAL && M.dscopes[p].kind != DS_SUBPROGRAM { return 0; }
    return p;
}
// a is s or an ancestor of s
fn sc_dominates(a: u32, s0: u32) -> bool {
    var s = s0;
    while s != 0 {
        if s == a { return true; }
        if M.dscopes[s].kind == DS_SUBPROGRAM { return false; }
        s = sc_parent(s);
    }
    return false;
}
fn sc_open(s0: u32, at: u32) {
    var s = s0;
    while s != 0 {
        if sc_tag[s] != sc_epoch {
            sc_tag[s] = sc_epoch;
            sc_first[s] = at;
        }
        if M.dscopes[s].kind == DS_SUBPROGRAM { return; }
        s = sc_parent(s);
    }
}
fn sc_extend(s0: u32, at: u32) {
    var s = s0;
    while s != 0 {
        sc_last[s] = at;
        if M.dscopes[s].kind == DS_SUBPROGRAM { return; }
        s = sc_parent(s);
    }
}
// Closes the range of s (and of its ancestors that do not dominate ns).
fn sc_close(s0: u32, ns: u32, base: u32, sec: u32) {
    var s = s0;
    while s != 0 {
        if sc_tag[s] == sc_epoch {
            if M.dscopes[s].kind == DS_LEXICAL {
                let k = rngs.len as! u32;
                rngs.push(Rng { start: sc_first[s] + base, end: sc_last[s] + base, sec: sec, next: GIR_NONE });
                if sc_head[s] == GIR_NONE { sc_head[s] = k; } else { rngs[sc_tail[s]].next = k; }
                sc_tail[s] = k;
                sc_n[s] += 1;
            }
            sc_tag[s] = 0;
        }
        if M.dscopes[s].kind == DS_SUBPROGRAM { return; }
        let p = sc_parent(s);
        if p == 0 || ns != 0 && sc_dominates(p, ns) { return; }
        s = p;
    }
}

// The function just placed at mcode[start ..] (prologue prolen, size size)
// in code section sec.
fn dbg_func_end(fi: u32, start: u32, prolen: u32, size: u32, sec: u32) {
    let base = start + prolen;
    let soff = start - osecs[sec].start as! u32;
    // labels: section offsets
    if lb_first.len != 0 {
        for k in lb_first[fi]..lb_first[fi as i64 + 1] {
            let a = lb_attr[k];
            lb_pos[a] = lb_pos[a] + base - osecs[sec].start as! u32;
            lb_sec[a] = sec;
        }
    }
    // variables: their frame addresses
    if lv_first.len != 0 {
        for k in lv_first[fi]..lv_first[fi as i64 + 1] {
            let a = lv_attr[k];
            let v: u32 = attr_at(a).val as! u32;
            let kd = gir_kind(v);
            var id: u32 = 0;
            if kd == GIR_V_INST {
                let gi = gir_idx(v);
                if gi < f_first_inst || gi >= f_first_inst + f_nins { continue; }
                id = gi - f_first_inst;
            } else if kd == GIR_V_ARG && gir_idx(v) < f_nargs {
                id = f_nins + gir_idx(v);
            } else {
                continue;
            }
            let h = vi[id].home;
            let off = vi[id].off;
            if h == H_ALLOCA || h == H_BYVAL {
                lv_kind[a] = LOC_FB;
                lv_off[a] = off;
            } else if (h == H_PTR || h == H_SLOT || h == H_STACK) && off != 0 {
                lv_kind[a] = LOC_FB_DEREF;
                lv_off[a] = off;
            }
        }
    }
    if df_sp == 0 { return; }
    // rows: the function start, then the body
    rows[df_row0].pos = start;
    for k in df_row0 + 1..rows.len { rows[k].pos += base; }
    if sec_rows1[sec] == 0 { sec_rows0[sec] = df_row0 as! u32; }
    sec_rows1[sec] = rows.len as! u32;
    // the unit's code in this section
    if cs_lo[sec] == GIR_NONE { cs_lo[sec] = soff; }
    cs_hi[sec] = soff + size;
    // lexical block ranges from the runs (LexicalScopes)
    sc_epoch++;
    var prev: u32 = 0;
    let sbase = base - osecs[sec].start as! u32;
    for r in runs {
        let s = run_scope(r.d);
        if s == 0 { continue; }
        if prev != 0 && !sc_dominates(prev, s) { sc_close(prev, s, sbase, sec); }
        sc_open(s, r.start);
        sc_extend(s, r.end);
        prev = s;
    }
    if prev != 0 { sc_close(prev, 0, sbase, sec); }
}

// ------------------------------------------------------------ writing

var b_abbrev: u8[>..] = [];
var b_info: u8[>..] = [];
var b_body: u8[>..] = [];      // the DIE bodies (attribute values), before placement
var b_stroff: u8[>..] = [];
var b_str: u8[>..] = [];
var b_addr: u8[>..] = [];
var b_line: u8[>..] = [];
var b_lstr: u8[>..] = [];
var b_rng: u8[>..] = [];
var b_tmp: u8[>..] = [];

// strings (.debug_str): index per dstr offset
var str_idx: u32[>..] = [];
var str_list: u32[>..] = [];   // dstr offsets in index order
// addresses (.debug_addr)
var ad_sym: u32[>..] = [];
var ad_add: u64[>..] = [];
// range lists (.debug_rnglists): each list's first range and count
var rl_first: u32[>..] = [];   // index into rl_sym / rl_start / rl_len
var rl_n: u32[>..] = [];
var rl_sym: u32[>..] = [];
var rl_start: u64[>..] = [];
var rl_len: u32[>..] = [];
// line-table file numbers per dfiles index, directories
var fnum: u32[>..] = [];
var file_list: u32[>..] = [];  // dfiles indices in number order
// abbreviations
var ab_data: u32[>..] = [];    // per abbreviation: tag, children, n, (at, form) * n
var ab_off: u32[>..] = [];
var ab_hash: u64[>..] = [];
var ab_tab: u32[>..] = [];     // open addressing: abbreviation + 1
var ab_cur: u32[>..] = [];     // the DIE being encoded: (at, form) pairs
// DIEs
var dk_keep: u8[>..] = [];
var dk_par: u32[>..] = [];     // nearest kept ancestor
var dk_kids: u8[>..] = [];
var dk_code: u32[>..] = [];
var dk_b0: u32[>..] = [];      // body range in b_body
var dk_b1: u32[>..] = [];
var dk_off: u32[>..] = [];     // offset in .debug_info
struct RefFix { pos: u32, die: u32 }
var ref_fix: RefFix[>..] = [];  // ref4 values in b_body to patch
struct BRel { pos: u32, sym: u32, typ: u32, addend: i64 }
var body_rel: BRel[>..] = [];   // relocations in b_body
var use_rng = false;
var n_cs: u32 = 0;              // code sections with debug code
var cs_one: u32 = 0;

fn dstr_at(off: u32) -> const u8[:] {
    var e: i64 = off;
    while e < M.dstr.len && M.dstr[e] != 0 { e++; }
    return M.dstr[off..e];
}
fn str_index(off: u32) -> u32 {
    let k = str_idx[off];
    if k != 0 { return k - 1; }
    str_list.push(off);
    str_idx[off] = str_list.len as! u32;
    return str_list.len as! u32 - 1;
}
fn addr_index(sym: u32, addend: u64) -> u32 {
    ad_sym.push(sym);
    ad_add.push(addend);
    return ad_sym.len as! u32 - 1;
}
// Two files with the same path (a name that is absolute, or directory/name).
fn same_path(F: DFile, G: DFile) -> bool {
    let fname = dstr_at(F.name);
    let gname = dstr_at(G.name);
    let fdir = dstr_at(F.dir);
    let gdir = dstr_at(G.dir);
    let fabs = fname.len != 0 && fname[0] == '/' || fdir.len == 0;
    let gabs = gname.len != 0 && gname[0] == '/' || gdir.len == 0;
    if fabs && gabs { return same_bytes(fname, gname); }
    if fabs != gabs {
        // dir + "/" + name == the other's absolute name
        let a = if fabs { fname } else { gname };
        let d = if fabs { gdir } else { fdir };
        let n = if fabs { gname } else { fname };
        if a.len != d.len + 1 + n.len { return false; }
        return same_bytes(a[0..d.len], d) && a[d.len] == '/' && same_bytes(a[d.len + 1..a.len], n);
    }
    return same_bytes(fname, gname) && same_bytes(fdir, gdir);
}
// The line-table number of file f (one per name and directory).
fn file_number(f: u32) -> u32 {
    if fnum[f] == GIR_NONE {
        let F = M.dfiles[f];
        for g, k in file_list {
            let G = M.dfiles[g];
            if G.name == F.name && G.dir == F.dir || same_path(F, G) {
                fnum[f] = k as! u32;
                return fnum[f];
            }
        }
        fnum[f] = file_list.len as! u32;
        file_list.push(f);
    }
    return fnum[f];
}

// body output
fn bb1(x: u32) { b_body.push(x as! u8); }
fn bb_uleb(x: u64) { uleb(b_body, x); }
fn bb4(x: u32) { o4(b_body, x); }
fn ab_add(at: u32, form: u32) {
    ab_cur.push(at);
    ab_cur.push(form);
}
fn body_reloc(sym: u32, typ: u32, addend: i64) {
    body_rel.push(BRel { pos: b_body.len as! u32, sym: sym, typ: typ, addend: addend });
}
// A string attribute: the smallest strx form for its index.
fn put_strx(at: u32, off: u32) {
    let k = str_index(off);
    if k <= 0xFF {
        ab_add(at, DW_FORM_strx1);
        bb1(k);
    } else if k <= 0xFFFF {
        ab_add(at, DW_FORM_strx2);
        o2(b_body, k);
    } else if k <= 0xFFFFFF {
        ab_add(at, DW_FORM_strx3);
        o2(b_body, k);
        bb1(k >> 16);
    } else {
        ab_add(at, DW_FORM_strx4);
        bb4(k);
    }
}
fn put_lowhigh(sym: u32, off: u64, len: u32) {
    ab_add(DW_AT_low_pc, DW_FORM_addrx);
    bb_uleb(addr_index(sym, off));
    ab_add(DW_AT_high_pc, DW_FORM_data4);
    bb4(len);
}
fn put_sec_offset(at: u32, sec: u32, off: u32) {
    ab_add(at, DW_FORM_sec_offset);
    body_reloc(sec_sym(sec), R_X86_64_32, off);
    bb4(0);
}
fn new_rnglist(n: u32) -> u32 {
    use_rng = true;
    rl_first.push(rl_sym.len as! u32);
    rl_n.push(n);
    return rl_first.len as! u32 - 1;
}
fn put_extra(aux: u32) {
    if aux == 0 { return; }
    let n: i64 = M.dstr[aux];
    obytes(b_body, M.dstr[aux as i64 + 1..aux as i64 + 1 + n]);
}
fn extra_len(aux: u32) -> u64 { if aux == 0 { 0 } else { M.dstr[aux] } }

// Resolves attribute A of DIE k into the body and the abbreviation.
fn put_attr(A: DAttr) {
    let at: u32 = A.at;
    let form: u32 = A.form;
    if form == DF_STR { put_strx(at, A.val as! u32); return; }
    if form < 0x7F00 {
        if form == DW_FORM_ref4 {
            let t: u32 = A.val as! u32;
            if t >= dk_keep.len as! u32 || dk_keep[t] == 0 { return; }
            ab_add(at, form);
            ref_fix.push(RefFix { pos: b_body.len as! u32, die: t });
            bb4(0);
            return;
        }
        ab_add(at, form);
        if form == DW_FORM_data1 || form == DW_FORM_flag { bb1(A.val as! u32); }
        else if form == DW_FORM_data2 { o2(b_body, A.val as! u32); }
        else if form == DW_FORM_data4 { bb4(A.val as! u32); }
        else if form == DW_FORM_data8 { o8(b_body, A.val); }
        else if form == DW_FORM_udata { bb_uleb(A.val); }
        else if form == DW_FORM_sdata { sleb(b_body, A.val as! i64); }
        else if form == DW_FORM_flag_present {}
        else if form == DW_FORM_exprloc {
            bb_uleb(A.aux);
            obytes(b_body, M.dstr[A.val..A.val + A.aux]);
        } else if form == DW_FORM_block1 {
            bb1(A.aux);
            obytes(b_body, M.dstr[A.val..A.val + A.aux]);
        } else if form == DW_FORM_block2 {
            o2(b_body, A.aux);
            obytes(b_body, M.dstr[A.val..A.val + A.aux]);
        } else if form == DW_FORM_data16 {
            obytes(b_body, M.dstr[A.val..A.val + 16]);
        } else {
            assert(false);
        }
        return;
    }
    if form == DF_FILE {
        let n = file_number(A.val as! u32);
        if n <= 0xFF {
            ab_add(at, DW_FORM_data1);
            bb1(n);
        } else {
            ab_add(at, DW_FORM_data2);
            o2(b_body, n);
        }
    } else if form == DF_PC {
        let g = M.funcs[A.val].global;
        put_lowhigh(sec_sym(g_sec[g]), g_value[g], g_size[g] as! u32);
    } else if form == DF_SCOPE_PC {
        let s: i64 = A.val as! i64;
        let n = sc_n[s];
        if n == 1 {
            let R = rngs[sc_head[s]];
            put_lowhigh(sec_sym(R.sec), R.start, R.end - R.start);
        } else if n > 1 {
            let l = new_rnglist(n);
            var k = sc_head[s];
            while k != GIR_NONE {
                let R = rngs[k];
                rl_sym.push(sec_sym(R.sec));
                rl_start.push(R.start);
                rl_len.push(R.end - R.start);
                k = R.next;
            }
            ab_add(DW_AT_ranges, DW_FORM_rnglistx);
            bb_uleb(l);
        }
    } else if form == DF_FRAME_BASE {
        ab_add(at, DW_FORM_exprloc);
        bb1(1);
        bb1(0x56);   // DW_OP_reg6 (rbp)
    } else if form == DF_LOCAL {
        let k = cur_attr;
        if lv_kind.len == 0 || lv_kind[k] == LOC_NONE { return; }
        b_tmp.clear();
        b_tmp.push(0x91);   // DW_OP_fbreg
        sleb(b_tmp, lv_off[k]);
        if lv_kind[k] == LOC_FB_DEREF { b_tmp.push(0x06); }   // DW_OP_deref
        ab_add(at, DW_FORM_exprloc);
        bb_uleb(b_tmp.len as u64 + extra_len(A.aux));
        obytes(b_body, b_tmp);
        put_extra(A.aux);
    } else if form == DF_GLOBAL {
        let g: i64 = A.val as! i64;
        ab_add(at, DW_FORM_exprloc);
        if M.globals[g].flags & GF_TLS != 0 {
            bb_uleb(10 + extra_len(A.aux));
            bb1(0x0e);   // DW_OP_const8u
            body_reloc(g_sym[g], R_X86_64_DTPOFF64, 0);
            o8(b_body, 0);
            bb1(0xe0);   // DW_OP_GNU_push_tls_address
        } else {
            let k = addr_index(g_sym[g], 0);
            bb_uleb(1 + uleb_len(k) as u64 + extra_len(A.aux));
            bb1(0xa1);   // DW_OP_addrx
            bb_uleb(k);
        }
        put_extra(A.aux);
    } else if form == DF_STMT_LIST {
        put_sec_offset(DW_AT_stmt_list, sec_line, 0);
    } else if form == DF_STR_BASE {
        put_sec_offset(DW_AT_str_offsets_base, sec_stroff, 8);
    } else if form == DF_CU_PC {
        if n_cs == 1 {
            put_lowhigh(sec_sym(cs_one), cs_lo[cs_one], cs_hi[cs_one] - cs_lo[cs_one]);
        } else if n_cs > 1 {
            ab_add(DW_AT_low_pc, DW_FORM_addr);
            o8(b_body, 0);
            let l = new_rnglist(n_cs);
            for s in 0..cs_lo.len {
                if cs_lo[s] == GIR_NONE { continue; }
                rl_sym.push(sec_sym(s as! u32));
                rl_start.push(cs_lo[s]);
                rl_len.push(cs_hi[s] - cs_lo[s]);
            }
            ab_add(DW_AT_ranges, DW_FORM_rnglistx);
            bb_uleb(l);
        }
    } else if form == DF_ADDR_BASE {
        put_sec_offset(DW_AT_addr_base, sec_addr, 8);
        if use_rng { put_sec_offset(DW_AT_rnglists_base, sec_rng, 12); }
    } else if form == DF_LABEL {
        let k = cur_attr;
        if lb_sec.len == 0 || lb_sec[k] == 0 { return; }
        ab_add(DW_AT_low_pc, DW_FORM_addrx);
        bb_uleb(addr_index(sec_sym(lb_sec[k]), lb_pos[k]));
    }
}
var cur_attr: i64 = 0;

// The abbreviation of the DIE just encoded (ab_cur), found or added.
fn abbrev_code(tag: u32, kids: u32) -> u32 {
    var h: u64 = tag as u64 * 0x9E3779B97F4A7C15 + kids;
    for x in ab_cur { h = (h ^ x) * 0x100000001B3; }
    let mask = ab_tab.len - 1;
    var i: i64 = (h as! i64) & mask;
    while true {
        let e = ab_tab[i];
        if e == 0 { break; }
        let a = e - 1;
        if ab_hash[a] == h {
            let o: i64 = ab_off[a];
            if ab_data[o] == tag && ab_data[o + 1] == kids && ab_data[o + 2] == ab_cur.len as! u32 / 2 {
                var same = true;
                for x, q in ab_cur { if ab_data[o + 3 + q] != x { same = false; break; } }
                if same { return a + 1; }
            }
        }
        i = (i + 1) & mask;
    }
    let a = ab_off.len as! u32;
    ab_off.push(ab_data.len as! u32);
    ab_hash.push(h);
    ab_data.push(tag);
    ab_data.push(kids);
    ab_data.push(ab_cur.len as! u32 / 2);
    ab_data.append(ab_cur);
    ab_tab[i] = a + 1;
    if (ab_off.len * 2) > ab_tab.len { ab_rehash(); }
    return a + 1;
}
fn ab_rehash() {
    let n = ab_tab.len * 2;
    ab_tab.clear();
    ab_tab.resize(n, 0);
    let mask = n - 1;
    for h, a in ab_hash {
        var i: i64 = (h as! i64) & mask;
        while ab_tab[i] != 0 { i = (i + 1) & mask; }
        ab_tab[i] = a as! u32 + 1;
    }
}

// The DIEs to write: a lexical block without code is dropped with the
// variables and labels in it; other DIEs go to the nearest kept ancestor.
fn mark_dies() {
    let n = dtab_n();
    dk_keep.clear();
    dk_keep.resize(n, 1);
    dk_par.clear();
    dk_par.resize(n, GIR_NONE);
    dk_kids.clear();
    dk_kids.resize(n, 0);
    for k in 0..n {
        let D = die_at(k);
        if D.parent != GIR_NONE {
            let p: i64 = D.parent;
            dk_par[k] = if dk_keep[p] != 0 { D.parent } else { dk_par[p] };
            if dk_keep[p] == 0 && (D.tag == DW_TAG_variable || D.tag == DW_TAG_formal_parameter || D.tag == DW_TAG_label) {
                dk_keep[k] = 0;
            }
        }
        if D.tag == DW_TAG_lexical_block {
            for q in D.attrs..D.attrs + D.n_attrs {
                let A = attr_at(q);
                if A.form == DF_SCOPE_PC && sc_n[A.val as! i64] == 0 { dk_keep[k] = 0; }
            }
        }
    }
    // a dropped variable that a kept DIE refers to (a VLA bound) is kept
    for k in 0..n {
        if dk_keep[k] == 0 { continue; }
        let D = die_at(k);
        for q in D.attrs..D.attrs + D.n_attrs {
            let A = attr_at(q);
            if A.form != DW_FORM_ref4 || A.val >= n as! u64 { continue; }
            let t: i64 = A.val as! i64;
            if dk_keep[t] == 0 && die_at(t).tag != DW_TAG_lexical_block { dk_keep[t] = 2; }
        }
    }
    for k in 0..n {
        if dk_keep[k] == 0 || dk_par[k] == GIR_NONE { continue; }
        dk_kids[dk_par[k]] = 1;
    }
}

fn dbg_write() {
    let nd = dtab_n();
    if nd == 0 { return; }
    // pools
    str_idx.clear();
    str_idx.resize(M.dstr.len + 1, 0);
    str_list.clear();
    ad_sym.clear();
    ad_add.clear();
    rl_first.clear();
    rl_n.clear();
    rl_sym.clear();
    rl_start.clear();
    rl_len.clear();
    fnum.clear();
    fnum.resize(M.dfiles.len, GIR_NONE);
    file_list.clear();
    let CU = M.dscopes[cu_scope];
    file_number(CU.file);
    n_cs = 0;
    for s in 0..cs_lo.len {
        if cs_lo[s] != GIR_NONE {
            n_cs++;
            cs_one = s as! u32;
        }
    }
    mark_dies();
    // range lists are used if the unit's code is in several sections or a
    // kept lexical block has several ranges (the unit then gets
    // DW_AT_rnglists_base)
    use_rng = n_cs > 1;
    for k in 0..nd {
        if use_rng { break; }
        if dk_keep[k] == 0 || die_at(k).tag != DW_TAG_lexical_block { continue; }
        let D = die_at(k);
        for q in D.attrs..D.attrs + D.n_attrs {
            let A = attr_at(q);
            if A.form == DF_SCOPE_PC && sc_n[A.val as! i64] > 1 { use_rng = true; }
        }
    }
    // the DIEs: bodies and abbreviations
    ab_data.clear();
    ab_off.clear();
    ab_hash.clear();
    ab_tab.clear();
    ab_tab.resize(256, 0);
    b_body.clear();
    ref_fix.clear();
    body_rel.clear();
    dk_code.clear();
    dk_code.resize(nd, 0);
    dk_b0.clear();
    dk_b0.resize(nd, 0);
    dk_b1.clear();
    dk_b1.resize(nd, 0);
    for k in 0..nd {
        if dk_keep[k] == 0 { continue; }
        let D = die_at(k);
        ab_cur.clear();
        dk_b0[k] = b_body.len as! u32;
        for q in D.attrs..D.attrs + D.n_attrs {
            cur_attr = q;
            put_attr(attr_at(q));
        }
        dk_b1[k] = b_body.len as! u32;
        dk_code[k] = abbrev_code(D.tag, dk_kids[k]);
    }
    // offsets
    var off: u32 = 12;   // after the unit header
    var depth: u32[>..] = [];
    dk_off.clear();
    dk_off.resize(nd, 0);
    for k in 0..nd {
        if dk_keep[k] == 0 { continue; }
        let p = dk_par[k];
        while depth.len != 0 && depth[depth.len - 1] != p {
            off++;   // end of children
            depth.pop();
        }
        dk_off[k] = off;
        off += uleb_len(dk_code[k]) + dk_b1[k] - dk_b0[k];
        if dk_kids[k] != 0 { depth.push(k as! u32); }
    }
    off += depth.len as! u32;
    let unit_end = off;
    // .debug_info
    b_info.clear();
    o4(b_info, unit_end - 4);
    o2(b_info, 5);       // version
    o1(b_info, 1);       // DW_UT_compile
    o1(b_info, 8);       // address size
    xrel(sec_info, 8, sec_sym(sec_abbrev), R_X86_64_32, 0);
    o4(b_info, 0);       // abbreviation offset
    depth.clear();
    // ref4 values and relocations are patched as the bodies are placed (they
    // are in increasing body position)
    var rf: i64 = 0;
    var rr: i64 = 0;
    for k in 0..nd {
        if dk_keep[k] == 0 { continue; }
        let p = dk_par[k];
        while depth.len != 0 && depth[depth.len - 1] != p {
            o1(b_info, 0);
            depth.pop();
        }
        uleb(b_info, dk_code[k]);
        let b0 = dk_b0[k];
        let b1 = dk_b1[k];
        let delta: i64 = b_info.len - b0;
        obytes(b_info, b_body[b0..b1]);
        while rf < ref_fix.len && ref_fix[rf].pos < b1 {
            let x = ref_fix[rf];
            patch_o4(b_info, x.pos + delta, dk_off[x.die]);
            rf++;
        }
        while rr < body_rel.len && body_rel[rr].pos < b1 {
            let x = body_rel[rr];
            xrel(sec_info, (x.pos + delta) as! u64, x.sym, x.typ, x.addend);
            rr++;
        }
        if dk_kids[k] != 0 { depth.push(k as! u32); }
    }
    while depth.len != 0 {
        o1(b_info, 0);
        depth.pop();
    }
    assert(b_info.len == unit_end);
    // .debug_abbrev
    b_abbrev.clear();
    for o, a in ab_off {
        let x: i64 = o;
        uleb(b_abbrev, a as u64 + 1);
        uleb(b_abbrev, ab_data[x]);
        o1(b_abbrev, ab_data[x + 1]);
        let na: i64 = ab_data[x + 2];
        for q in 0..na {
            uleb(b_abbrev, ab_data[x + 3 + 2 * q]);
            uleb(b_abbrev, ab_data[x + 4 + 2 * q]);
        }
        o1(b_abbrev, 0);
        o1(b_abbrev, 0);
    }
    o1(b_abbrev, 0);
    // .debug_line (files numbered by the DIEs first, then by the rows)
    write_line();
    // .debug_str and .debug_str_offsets
    b_str.clear();
    b_stroff.clear();
    o4(b_stroff, 4 + 4 * str_list.len as! u32);
    o2(b_stroff, 5);
    o2(b_stroff, 0);
    for s in str_list {
        xrel(sec_stroff, b_stroff.len as u64, sec_sym(sec_str), R_X86_64_32, b_str.len);
        o4(b_stroff, 0);
        obytes(b_str, dstr_at(s));
        o1(b_str, 0);
    }
    // .debug_rnglists (its addresses go to the address pool)
    b_rng.clear();
    if use_rng {
        o4(b_rng, 0);
        o2(b_rng, 5);
        o1(b_rng, 8);
        o1(b_rng, 0);
        o4(b_rng, rl_first.len as! u32);
        let tbl = b_rng.len;
        for l in 0..rl_first.len { o4(b_rng, 0); }
        for f, l in rl_first {
            patch_o4(b_rng, tbl + 4 * l, (b_rng.len - tbl) as! u32);
            for q in f..f + rl_n[l] {
                o1(b_rng, 3);   // DW_RLE_startx_length
                uleb(b_rng, addr_index(rl_sym[q], rl_start[q]));
                uleb(b_rng, rl_len[q]);
            }
            o1(b_rng, 0);       // DW_RLE_end_of_list
        }
        patch_o4(b_rng, 0, (b_rng.len - 4) as! u32);
    }
    // .debug_addr
    b_addr.clear();
    o4(b_addr, 4 + 8 * ad_sym.len as! u32);
    o2(b_addr, 5);
    o1(b_addr, 8);
    o1(b_addr, 0);
    for s, k in ad_sym {
        xrel(sec_addr, b_addr.len as u64, s, R_X86_64_64, ad_add[k] as! i64);
        o8(b_addr, 0);
    }
    // place the sections
    place_dbg(sec_abbrev, b_abbrev);
    place_dbg(sec_info, b_info);
    place_dbg(sec_stroff, b_stroff);
    place_dbg(sec_str, b_str);
    place_dbg(sec_addr, b_addr);
    place_dbg(sec_line, b_line);
    place_dbg(sec_lstr, b_lstr);
    place_dbg(sec_rng, b_rng);
}
fn place_dbg(sec: u32, b: const u8[:]) {
    osecs[sec].start = s_dbg.len as u64;
    osecs[sec].size = b.len as u64;
    s_dbg.append(b);
}

// ------------------------------------------------------------ .debug_line

fn line_str_bytes(o: u8[>..]&, s: const u8[:]) {
    xrel(sec_line, o.len as u64, sec_sym(sec_lstr), R_X86_64_32, b_lstr.len);
    o4(o, 0);
    obytes(b_lstr, s);
    o1(b_lstr, 0);
}
fn same_bytes(a: const u8[:], b: const u8[:]) -> bool {
    if a.len != b.len { return false; }
    for x, i in a { if b[i] != x { return false; } }
    return true;
}
// The file of a row.
fn row_file(R: LRow) -> u32 {
    if R.flags & ROW_START != 0 { return M.dscopes[R.d].file; }
    if R.d == 0 { return M.dscopes[cu_scope].file; }
    return M.dscopes[M.dlocs[R.d].scope].file;
}
let LINE_OPLEN: u32[12] = [0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1];
// Directories (dstr ranges) and the line table's file entries.
var dir_off: u32[>..] = [];
var dir_len: u32[>..] = [];
var fe_dir: u32[>..] = [];
var fe_off: u32[>..] = [];
var fe_len: u32[>..] = [];
fn dir_index(off: u32, len: u32) -> u32 {
    let d = M.dstr[off..off + len];
    for o, k in dir_off {
        if same_bytes(M.dstr[o..o + dir_len[k]], d) { return k as! u32; }
    }
    dir_off.push(off);
    dir_len.push(len);
    return dir_off.len as! u32 - 1;
}
fn write_line() {
    for R in rows { file_number(row_file(R)); }
    b_line.clear();
    b_lstr.clear();
    o4(b_line, 0);       // unit length
    o2(b_line, 5);       // version
    o1(b_line, 8);       // address size
    o1(b_line, 0);       // segment selector size
    o4(b_line, 0);       // header length
    let hstart = b_line.len;
    o1(b_line, 1);       // minimum instruction length
    o1(b_line, 1);       // maximum operations per instruction
    o1(b_line, 1);       // default is_stmt
    o1(b_line, 0xFB);    // line base -5
    o1(b_line, 14);      // line range
    o1(b_line, 13);      // opcode base
    for x in LINE_OPLEN { o1(b_line, x); }
    // directory 0 is the compilation directory; a file without a directory
    // whose name has one is split, as MCDwarf does
    let CF = M.dfiles[M.dscopes[cu_scope].file];
    dir_off.clear();
    dir_len.clear();
    dir_off.push(CF.dir);
    dir_len.push(dstr_at(CF.dir).len as! u32);
    fe_dir.clear();
    fe_off.clear();
    fe_len.clear();
    for f in file_list {
        let F = M.dfiles[f];
        let name = dstr_at(F.name);
        let dir = dstr_at(F.dir);
        var di: u32 = 0;
        var noff = F.name;
        var nlen: u32 = name.len as! u32;
        if dir.len != 0 {
            di = dir_index(F.dir, dir.len as! u32);
        } else {
            var slash: i64 = -1;
            for c, i in name { if c == '/' { slash = i; } }
            if slash > 0 {
                di = dir_index(F.name, slash as! u32);
                noff = F.name + slash as! u32 + 1;
                nlen = (name.len - slash - 1) as! u32;
            }
        }
        fe_dir.push(di);
        fe_off.push(noff);
        fe_len.push(nlen);
    }
    o1(b_line, 1);       // directory entry format: path, line_strp
    uleb(b_line, 1);
    uleb(b_line, 0x1f);
    uleb(b_line, dir_off.len as u64);
    for o, k in dir_off { line_str_bytes(b_line, M.dstr[o..o + dir_len[k]]); }
    o1(b_line, 2);       // file entry format: path, line_strp; directory index, udata
    uleb(b_line, 1);
    uleb(b_line, 0x1f);
    uleb(b_line, 2);
    uleb(b_line, 0x0f);
    uleb(b_line, file_list.len as u64);
    for o, k in fe_off {
        line_str_bytes(b_line, M.dstr[o..o + fe_len[k]]);
        uleb(b_line, fe_dir[k]);
    }
    patch_o4(b_line, hstart - 4, (b_line.len - hstart) as! u32);
    // one sequence per code section
    for s in 0..sec_rows1.len {
        let r1 = sec_rows1[s];
        if r1 == 0 { continue; }
        line_sequence(s as! u32, sec_rows0[s], r1);
    }
    patch_o4(b_line, 0, (b_line.len - 4) as! u32);
}

fn line_sequence(sec: u32, r0: u32, r1: u32) {
    let base: u32 = osecs[sec].start as! u32;
    // DW_LNE_set_address
    o1(b_line, 0);
    o1(b_line, 9);
    o1(b_line, 2);
    xrel(sec_line, b_line.len as u64, sec_sym(sec), R_X86_64_64, rows[r0].pos - base);
    o8(b_line, 0);
    var addr: u32 = rows[r0].pos;
    var line: i64 = 1;
    var file: u32 = 1;      // (the file register starts at 1, also in DWARF 5)
    var col: u32 = 0;
    var stmt = true;
    for k in r0..r1 {
        let R = rows[k];
        var ln: i64 = 0;
        var c: u32 = 0;
        if R.flags & ROW_START != 0 { ln = M.dscopes[R.d].line; }
        else if R.d != 0 {
            let L = M.dlocs[R.d];
            c = L.col;
            if R.flags & ROW_ZERO == 0 { ln = L.line; }
        }
        let f = fnum[row_file(R)];
        if f != file {
            o1(b_line, 4);   // DW_LNS_set_file
            uleb(b_line, f);
            file = f;
        }
        if c != col {
            o1(b_line, 5);   // DW_LNS_set_column
            uleb(b_line, c);
            col = c;
        }
        let st = R.flags & ROW_STMT != 0;
        if st != stmt {
            o1(b_line, 6);   // DW_LNS_negate_stmt
            stmt = st;
        }
        if R.flags & ROW_PEND != 0 { o1(b_line, 10); }   // DW_LNS_set_prologue_end
        if R.flags & ROW_EPI != 0 { o1(b_line, 11); }    // DW_LNS_set_epilogue_begin
        line_advance(ln - line, R.pos - addr);
        line = ln;
        addr = R.pos;
    }
    // the end of the section
    let end: u32 = (osecs[sec].start + osecs[sec].size) as! u32;
    if end > addr {
        o1(b_line, 2);   // DW_LNS_advance_pc
        uleb(b_line, end - addr);
    }
    o1(b_line, 0);
    o1(b_line, 1);
    o1(b_line, 1);   // DW_LNE_end_sequence
}
// A row line_delta lines and addr_delta bytes after the previous one.
fn line_advance(dl: i64, da: u32) {
    if dl < -5 || dl >= 9 {
        o1(b_line, 3);   // DW_LNS_advance_line
        sleb(b_line, dl);
        line_special(0, da);
        return;
    }
    line_special(dl, da);
}
fn line_special(dl: i64, da0: u32) {
    var da = da0;
    // special opcode: 13 + (dl + 5) + 14 * da <= 255
    let lo: u64 = (dl + 5) as! u64 + 13;
    if da as u64 * 14 + lo <= 255 {
        o1(b_line, (lo + da as u64 * 14) as! u32);
        return;
    }
    // DW_LNS_const_add_pc adds (255 - 13) / 14 = 17
    if da >= 17 && (da - 17) as u64 * 14 + lo <= 255 {
        o1(b_line, 8);
        da -= 17;
        o1(b_line, (lo + da as u64 * 14) as! u32);
        return;
    }
    o1(b_line, 2);   // DW_LNS_advance_pc
    uleb(b_line, da);
    o1(b_line, lo as! u32);
}
