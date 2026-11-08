// Output sections, symbols and the ELF64 relocatable-object writer.
//
// Section indices (osecs) are fixed for the default sections; every GIR
// section (section attributes, .init_array/.fini_array) follows, then one
// section per function or variable in a comdat (in that comdat's group),
// .eh_frame, the .gcc_except_table sections and the debug sections. In the
// file, the SHT_GROUP sections come first (a group must precede its
// members), so output section s is ELF section s + n_groups; relocation
// sections, .symtab, .strtab, .shstrtab and .note.GNU-stack come last.
// Symbols: null, one STT_SECTION symbol per output section (index = section
// index), the local globals, the constant-pool entries, the group
// signatures of comdats without a global of that name, then all other
// globals.

let SEC_NULL = 0;
let SEC_TEXT = 1;
let SEC_DATA = 2;
let SEC_BSS = 3;
let SEC_RODATA = 4;
let SEC_CST4 = 5;
let SEC_CST8 = 6;
let SEC_CST16 = 7;
let SEC_TDATA = 8;
let SEC_TBSS = 9;
let SEC_FIRST_CUSTOM = 10;

// Where an output section's bytes are.
let BUF_NONE = 0;    // NOBITS (or empty)
let BUF_CODE = 1;    // mcode[start .. start + size]
let BUF_DATA = 2;    // sdata[start .. start + size]
let BUF_RODATA = 3;  // srodata
let BUF_CST4 = 4;
let BUF_CST8 = 5;
let BUF_CST16 = 6;
let BUF_EH = 7;      // s_eh (.eh_frame)
let BUF_LSDA = 8;    // the chunks of s_lsda listed by OSec.xfirst
let BUF_DBG = 9;     // s_dbg[start .. start + size] (debug sections)

let SHT_PROGBITS = 1;
let SHT_SYMTAB = 2;
let SHT_STRTAB = 3;
let SHT_RELA = 4;
let SHT_NOBITS = 8;
let SHT_GROUP = 17;
let SHF_WRITE = 1;
let SHF_ALLOC = 2;
let SHF_EXEC = 4;
let SHF_MERGE = 0x10;
let SHF_STRINGS = 0x20;
let SHF_INFO_LINK = 0x40;
let SHF_TLS = 0x400;
let SHN_COMMON = 0xFFF2;

// grp: comdat index + 1 (0: not in a group); xfirst/xlast: BUF_LSDA chunks.
struct OSec { name: u32, typ: u32, flags: u64, align: u64, entsize: u64, buf: u32, start: u64, size: u64,
              name_off: u32, name_len: u32, grp: u32, xfirst: u32, xlast: u32 }

var osecs: OSec[>..] = [];
var sdata: u8[>..] = [];       // .data, .tdata and the PROGBITS custom data sections
var srodata: u8[>..] = [];     // .rodata (globals, then pooled aggregate constants)
var cst4: u8[>..] = [];        // .rodata.cst4  (f32, f16 constants)
var cst8: u8[>..] = [];        // .rodata.cst8  (f64 constants)
var cst16: u8[>..] = [];       // .rodata.cst16 (f80, i128, 16-byte vector constants)
var rodata_align: u64 = 16;

// Per global (index = GIR global index).
var g_sym: u32[>..] = [];      // ELF symbol index
var g_sec: u32[>..] = [];      // output section index, 0 = undefined
var g_value: u64[>..] = [];    // offset inside its section
var g_size: u64[>..] = [];
var n_local_syms: u32 = 0;     // = index of the first non-local symbol
var g_order: u32[>..] = [];    // globals grouped by section (counting sort)
var sec_count: u32[>..] = [];
var sec_end: u32[>..] = [];    // per section: end of its run in g_order

// Per block (global block index): code offset, for blockaddress.
var blk_code: u32[>..] = [];
// Pending blockaddress operands: rel32 at mcode[pos] -> global block blk.
var baddr: Fixup[>..] = [];
// Per global: its own section in its comdat group (0: the default section).
var g_csec: u32[>..] = [];
// Per code section: the section of its functions' LSDAs (0: none).
var cs_lsda: u32[>..] = [];
var sec_eh: u32 = 0;           // .eh_frame (0: none)
var sec_lsda: u32 = 0;         // .gcc_except_table of the functions outside comdats
// Relocations in the sections the back-end writes itself (.eh_frame,
// .gcc_except_table, debug sections): section-relative offsets.
var xrels: Rel2[>..] = [];
// Group signature symbols the back-end makes (comdats without a global of
// that name): provisional numbers CDSYM_BASE + k.
let CDSYM_BASE = 0x50000000;
var cd_used: u32[>..] = [];    // per comdat: 1 if one of our sections is in it
var cd_own: u32[>..] = [];     // comdats whose signature is a symbol of ours, in symbol order
var cd_grp: u32[>..] = [];     // per comdat: its group's ELF section index (write_elf)

fn sec_sym(s: u32) -> u32 { s }   // the section symbol of output section s

// Local symbols of constant-pool entries (one per entry of the mergeable
// .rodata.cst* sections). Relocations name them POOL_BASE + k while code is
// generated; the writer numbers them after the local globals (and shifts
// the non-local globals behind them).
let POOL_BASE = 0x40000000;
struct PoolSym { sec: u32, off: u32, size: u32 }
var pool_syms: PoolSym[>..] = [];
fn new_pool_sym(sec: u32, off: u32, size: u32) -> u32 {
    pool_syms.push(PoolSym { sec: sec, off: off, size: size });
    return POOL_BASE + (pool_syms.len - 1) as! u32;
}
// Final symbol index of a provisional one.
fn final_sym(s: u64) -> u64 {
    if s >= CDSYM_BASE { return n_local_syms + pool_syms.len as u64 + (s - CDSYM_BASE); }
    if s >= POOL_BASE { return n_local_syms + (s - POOL_BASE); }
    if s >= n_local_syms { return s + pool_syms.len as u64 + cd_own.len as u64; }
    return s;
}
fn final_info(info: u64) -> u64 { (final_sym(info >> 32) << 32) | (info & 0xFFFFFFFF) }

checkfree fn o1(o: u8[>..]&, x: u32) { o.push(x as! u8); }
checkfree fn o2(o: u8[>..]&, x: u32) {
    o1(o, x);
    o1(o, x >> 8);
}
checkfree fn o4(o: u8[>..]&, x: u32) {
    o2(o, x);
    o2(o, x >> 16);
}
checkfree fn o8(o: u8[>..]&, x: u64) {
    o4(o, x as! u32);
    o4(o, (x >> 32) as! u32);
}
checkfree fn opad(o: u8[>..]&, al: u64) {
    while (o.len as u64) % al != 0 { o.push(0); }
}
checkfree fn obytes(o: u8[>..]&, p: const u8[:]) { o.append(p); }

fn add_osec(typ: u32, flags: u64, align: u64, entsize: u64, buf: u32, name: const u8[:]) {
    let off = sec_names.len as! u32;
    sec_names.append(name);
    add_osec_at(typ, flags, align, entsize, buf, off, name.len as! u32);
}
// An output section whose name is sec_names[off .. off + len].
fn add_osec_at(typ: u32, flags: u64, align: u64, entsize: u64, buf: u32, off: u32, len: u32) {
    osecs.push(OSec { name: 0, typ: typ, flags: flags, align: align, entsize: entsize, buf: buf, start: 0,
                      size: 0, name_off: off, name_len: len, grp: 0, xfirst: GIR_NONE, xlast: GIR_NONE });
}
var sec_names: u8[>..] = [];   // section names, concatenated (no NULs)

// The default sections, one per GIR section, the comdat sections, the
// unwind tables (and, with debug information, the debug sections).
fn make_sections() {
    osecs.clear();
    sec_names.clear();
    add_osec(0, 0, 0, 0, BUF_NONE, "");
    add_osec(SHT_PROGBITS, SHF_ALLOC | SHF_EXEC, 16, 0, BUF_CODE, ".text");
    add_osec(SHT_PROGBITS, SHF_ALLOC | SHF_WRITE, 1, 0, BUF_DATA, ".data");
    add_osec(SHT_NOBITS, SHF_ALLOC | SHF_WRITE, 1, 0, BUF_NONE, ".bss");
    add_osec(SHT_PROGBITS, SHF_ALLOC, 1, 0, BUF_RODATA, ".rodata");
    add_osec(SHT_PROGBITS, SHF_ALLOC | SHF_MERGE, 4, 4, BUF_CST4, ".rodata.cst4");
    add_osec(SHT_PROGBITS, SHF_ALLOC | SHF_MERGE, 8, 8, BUF_CST8, ".rodata.cst8");
    add_osec(SHT_PROGBITS, SHF_ALLOC | SHF_MERGE, 16, 16, BUF_CST16, ".rodata.cst16");
    add_osec(SHT_PROGBITS, SHF_ALLOC | SHF_WRITE | SHF_TLS, 1, 0, BUF_DATA, ".tdata");
    add_osec(SHT_NOBITS, SHF_ALLOC | SHF_WRITE | SHF_TLS, 1, 0, BUF_NONE, ".tbss");
    for s in M.sections {
        var fl: u64 = SHF_ALLOC;
        if s.flags & SF_WRITE != 0 { fl |= SHF_WRITE; }
        if s.flags & SF_EXEC != 0 { fl |= SHF_EXEC; }
        if s.flags & SF_TLS != 0 { fl |= SHF_TLS; }
        let buf: u32 = if s.flags & SF_EXEC != 0 { BUF_CODE } else if s.flags & SF_NOBITS != 0 { BUF_NONE } else { BUF_DATA };
        let typ: u32 = if s.flags & SF_NOBITS != 0 { SHT_NOBITS } else { s.typ };
        let nm = M.strtab[s.name..s.name + s.name_len];
        add_osec(typ, fl, if s.typ == 14 || s.typ == 15 || s.typ == 16 { 8 } else { 1 }, 0, buf, nm);
    }
    make_comdat_sections();
    // unwind tables: .eh_frame, and the LSDA section of each code section
    // that has functions with landing pads
    sec_eh = 0;
    if M.funcs.len != 0 {
        sec_eh = osecs.len as! u32;
        add_osec(SHT_X86_64_UNWIND, SHF_ALLOC, 8, 0, BUF_EH, ".eh_frame");
    }
    cs_lsda.clear();
    cs_lsda.resize(osecs.len, 0);
    sec_lsda = 0;
    for E in M.ehs {
        let g: i64 = M.funcs[E.func].global;
        let cs = global_section(g);
        if cs_lsda[cs] != 0 { continue; }
        if osecs[cs].grp == 0 {
            if sec_lsda == 0 {
                sec_lsda = osecs.len as! u32;
                add_osec(SHT_PROGBITS, SHF_ALLOC, 4, 0, BUF_LSDA, ".gcc_except_table");
            }
            cs_lsda[cs] = sec_lsda;
        } else {
            let G = M.globals[g];
            cs_lsda[cs] = osecs.len as! u32;
            let off = sec_names.len as! u32;
            sec_names.append(".gcc_except_table.");
            sec_names.append(M.strtab[G.name..G.name + G.name_len]);
            add_osec_at(SHT_PROGBITS, SHF_ALLOC | SHF_GROUP, 4, 0, BUF_LSDA, off, 18 + G.name_len);
            osecs[osecs.len - 1].grp = osecs[cs].grp;
        }
    }
    dbg_make_sections();
}

// The default output section of global G, ignoring comdats.
fn base_section(G: Global) -> u32 {
    if G.flags & GF_DEFINED == 0 || G.kind == G_ALIAS { return SEC_NULL; }
    if G.section != GIR_NONE { return SEC_FIRST_CUSTOM + G.section; }
    if G.kind == G_FUNC { return SEC_TEXT; }
    if G.flags & GF_TLS != 0 { return if G.flags & GF_ZERO != 0 { SEC_TBSS } else { SEC_TDATA }; }
    if G.flags & GF_ZERO != 0 { return SEC_BSS; }
    // Read-only data with relocations goes to .data, so that a PIE link
    // needs no text relocations.
    if G.flags & GF_CONST != 0 && G.flags & GF_RELOCS == 0 { return SEC_RODATA; }
    return SEC_DATA;
}
// Output section of global g.
fn global_section(g: i64) -> u32 {
    let s = g_csec[g];
    if s != 0 { return s; }
    return base_section(M.globals[g]);
}

// A section of its own for every defined function and variable in a comdat
// (LLVM's names: .text.<name>, .data.<name>, .data.rel.ro.<name>, ...; an
// explicit section keeps its name), in the comdat's group.
fn make_comdat_sections() {
    let n = M.globals.len;
    g_csec.clear();
    g_csec.resize(n, 0);
    cd_used.clear();
    cd_used.resize(M.comdats.len, 0);
    if M.gcomdat.len != n { return; }
    for G, g in M.globals {
        let c = M.gcomdat[g];
        if c == GIR_NONE || G.flags & GF_DEFINED == 0 || G.kind == G_ALIAS || G.flags & GF_COMMON != 0 { continue; }
        let b = base_section(G);
        let B = osecs[b];
        let off = sec_names.len as! u32;
        var len: u32 = B.name_len;
        if b == SEC_DATA && G.flags & GF_CONST != 0 {
            sec_names.append(".data.rel.ro");
            len = 12;
        } else {
            sec_names.append(sec_names[B.name_off..B.name_off + B.name_len]);
        }
        if G.section == GIR_NONE {
            sec_names.push('.');
            sec_names.append(M.strtab[G.name..G.name + G.name_len]);
            len += 1 + G.name_len;
        }
        g_csec[g] = osecs.len as! u32;
        // (.rodata bytes are one shared buffer; a section of its own is placed like data)
        add_osec_at(B.typ, B.flags | SHF_GROUP, B.align, B.entsize, if B.buf == BUF_RODATA { BUF_DATA } else { B.buf }, off, len);
        osecs[osecs.len - 1].grp = c + 1;
        cd_used[c] = 1;
    }
}

fn layout_globals() {
    let n = M.globals.len;
    let nsec = osecs.len;
    g_sym.clear();
    g_sym.resize(n, 0);
    g_sec.clear();
    g_sec.resize(n, SEC_NULL);
    g_value.clear();
    g_value.resize(n, 0);
    g_size.clear();
    g_size.resize(n, 0);

    // Symbol indices: null, section symbols, local globals, the rest.
    var next: u32 = nsec as! u32;
    for G, g in M.globals {
        if G.flags & GF_INTERNAL != 0 {
            g_sym[g] = next;
            next++;
        }
    }
    n_local_syms = next;
    for G, g in M.globals {
        if G.flags & GF_INTERNAL == 0 {
            g_sym[g] = next;
            next++;
        }
    }
    // group signatures without a global (numbered after the pool entries)
    cd_own.clear();
    for C, c in M.comdats {
        if cd_used[c] != 0 && C.sig == GIR_NONE { cd_own.push(c as! u32); }
    }

    // Globals grouped by section, in table order within a section.
    sec_count.clear();
    sec_count.resize(nsec + 1, 0);
    for G, g in M.globals {
        let s = global_section(g);
        g_sec[g] = s;
        g_size[g] = G.size;
        sec_count[s as i64 + 1] += 1;
    }
    for s in 0..nsec { sec_count[s + 1] += sec_count[s]; }
    g_order.clear();
    g_order.resize(n, 0);
    for G, g in M.globals {
        let s: i64 = g_sec[g];
        g_order[sec_count[s]] = g as! u32;
        sec_count[s] += 1;
    }
    // sec_count[s] is now the end of section s's run in g_order.
    sec_end.clear();
    sec_end.append(sec_count[0..nsec]);

    // Data placement, section by section.
    var first: u32 = 0;
    for s in 0..nsec {
        let last = sec_count[s];
        let buf = osecs[s].buf;
        let typ = osecs[s].typ;
        if s != SEC_NULL && buf != BUF_CODE {
            if buf == BUF_DATA { osecs[s].start = sdata.len as u64; }
            var bss: u64 = 0;
            for k in first..last {
                let g: i64 = g_order[k];
                let G = M.globals[g];
                if G.kind != G_VAR { continue; }
                let al: u64 = if G.align != 0 { G.align } else { 1 };
                if al > osecs[s].align { osecs[s].align = al; }
                if typ == SHT_NOBITS || buf == BUF_NONE {
                    bss = (bss + al - 1) & ~(al - 1);
                    g_value[g] = bss;
                    bss += G.size;
                } else if buf == BUF_RODATA {
                    append_aligned(srodata, al, g);
                } else {
                    // Data: offsets relative to the section start inside sdata.
                    let base = osecs[s].start;
                    while (sdata.len as u64 - base) % al != 0 { sdata.push(0); }
                    g_value[g] = sdata.len as u64 - base;
                    if G.flags & GF_ZERO != 0 { sdata.resize(sdata.len + G.size, 0); }
                    else { sdata.append(M.data[G.data..G.data + G.size]); }
                }
            }
            if typ == SHT_NOBITS || buf == BUF_NONE { osecs[s].size = bss; }
            else if buf == BUF_DATA { osecs[s].size = sdata.len as u64 - osecs[s].start; }
        }
        first = last;
    }
    if osecs[SEC_RODATA].align > rodata_align { rodata_align = osecs[SEC_RODATA].align; }
}

fn append_aligned(sec: u8[>..]&, al: u64, g: i64) {
    let G = M.globals[g];
    while (sec.len as u64) % al != 0 { sec.push(0); }
    g_value[g] = sec.len as u64;
    if G.flags & GF_ZERO != 0 { sec.resize(sec.len + G.size, 0); }
    else { sec.append(M.data[G.data..G.data + G.size]); }
}

// Resolves aliases (value of their target + offset) once functions are placed.
fn resolve_aliases() {
    for G, g in M.globals {
        if G.kind != G_ALIAS { continue; }
        let t: i64 = G.func;
        g_sec[g] = g_sec[t];
        g_value[g] = g_value[t] + (G.aux as! i32) as! u64;
        g_size[g] = g_size[t];
    }
}

// Blockaddress operands: lea r, [rip + block]. Same code section: a fixed
// displacement; another section: a PC32 relocation against the function.
fn resolve_blockaddrs() {
    for x in baddr {
        let tgt = blk_code[x.blk];
        let d = tgt - (x.pos + 4);
        let p: i64 = x.pos;
        let w = mcode[p..p + 4];
        w[0] = d as! u8;
        w[1] = (d >> 8) as! u8;
        w[2] = (d >> 16) as! u8;
        w[3] = (d >> 24) as! u8;
    }
}

// --------------------------------------------------------------- ELF

struct Rel2 { offset: u64, info: u64, addend: i64, sec: u64 }
var rels: Rel2[>..] = [];        // all relocations, grouped by section before writing
var rel_sorted: Rel2[>..] = [];
var rel_first: u32[>..] = [];

fn sym_type(G0: Global) -> u32 {
    let G = if G0.kind == G_ALIAS { M.globals[G0.func] } else { G0 };
    if G.flags & GF_TLS != 0 { return 6; }                     // TLS (also when undefined)
    if G.flags & (GF_DEFINED | GF_COMMON) == 0 { return 0; }   // NOTYPE
    if G.kind == G_FUNC { return 2; }                          // FUNC
    if G.flags & GF_TLS != 0 { return 6; }                     // TLS
    return 1;                                                  // OBJECT
}

fn collect_relocs() {
    rels.clear();
    // Code relocations: rela_code[k].sec is the code section (set when the
    // function was placed), offsets are module code offsets.
    for r in rela_code {
        let s: i64 = r.sec;
        rels.push(Rel2 { offset: r.offset - osecs[s].start, info: r.info, addend: r.addend, sec: r.sec });
    }
    // Data relocations.
    for d in M.drelocs {
        let ow: i64 = d.owner;
        let s: i64 = g_sec[ow];
        let off = g_value[ow] + d.offset;
        if d.kind == DR_ABS64 {
            rels.push(Rel2 { offset: off, info: (g_sym[d.target] as u64 << 32) | R_X86_64_64, addend: d.addend,
                             sec: s as u64 });
        } else if d.kind == DR_PCREL32 {
            rels.push(Rel2 { offset: off, info: (g_sym[d.target] as u64 << 32) | R_X86_64_PC32, addend: d.addend,
                             sec: s as u64 });
        } else {
            let F = M.funcs[M.globals[d.target].func];
            let ga: i64 = F.first_block + d.blk;
            let fstart = g_value[d.target];
            if d.kind == DR_BLOCK {
                let a = (blk_code[ga] - osecs[g_sec[d.target]].start - fstart) as! i64 + d.addend;
                rels.push(Rel2 { offset: off, info: (g_sym[d.target] as u64 << 32) | R_X86_64_64, addend: a,
                                 sec: s as u64 });
            } else {
                let gb: i64 = F.first_block + d.blk2;
                let diff: u32 = blk_code[ga] - blk_code[gb] + (d.addend as! u32);
                let at: i64 = (osecs[s].start + off) as! i64;
                let w = sdata[at..at + 4];
                w[0] = diff as! u8;
                w[1] = (diff >> 8) as! u8;
                w[2] = (diff >> 16) as! u8;
                w[3] = (diff >> 24) as! u8;
            }
        }
    }
    rels.append(xrels);
    // Group by section (counting sort, stable).
    let ns = osecs.len;
    rel_first.clear();
    rel_first.resize(ns + 1, 0);
    for r in rels { rel_first[r.sec as! i64 + 1] += 1; }
    for s in 0..ns { rel_first[s + 1] += rel_first[s]; }
    rel_sorted.clear();
    rel_sorted.resize(rels.len, Rel2 { offset: 0, info: 0, addend: 0, sec: 0 });
    sec_count.clear();
    sec_count.resize(ns + 1, 0);
    for s in 0..ns { sec_count[s] = rel_first[s]; }
    for r in rels {
        let s: i64 = r.sec as! i64;
        rel_sorted[sec_count[s]] = r;
        sec_count[s] += 1;
    }
}

fn write_elf(o: u8[>..]&) {
    collect_relocs();
    let ns: i64 = osecs.len;
    // Groups: one per comdat that has sections here.
    cd_grp.clear();
    cd_grp.resize(M.comdats.len, 0);
    var ng: i64 = 0;
    for u, c in cd_used {
        if u != 0 {
            ng++;
            cd_grp[c] = ng as! u32;
        }
    }
    // ELF section list: null, groups, osecs 1.., one .rela per section with
    // relocations, then .symtab .strtab .shstrtab .note.GNU-stack.
    var n_rela: i64 = 0;
    for s in 0..ns { if rel_first[s + 1] > rel_first[s] { n_rela++; } }
    let sec_symtab = ng + ns + n_rela;
    let sec_strtab = sec_symtab + 1;
    let sec_shstrtab = sec_symtab + 2;
    let sec_note = sec_symtab + 3;
    let n_all = sec_symtab + 4;
    // ELF index of each osec's relocation section (0: none)
    var rela_of: u32[>..] = [];
    rela_of.resize(ns, 0);
    var ri: i64 = ng + ns;
    for s in 0..ns {
        if rel_first[s + 1] == rel_first[s] { continue; }
        rela_of[s] = ri as! u32;
        ri++;
    }

    // Section header string table.
    var shstr: u8[>..] = [0];
    var sh_name: u32[>..] = [];
    sh_name.resize(n_all, 0);
    var sh_off: u64[>..] = [];
    sh_off.resize(n_all, 0);
    var sh_size: u64[>..] = [];
    sh_size.resize(n_all, 0);
    if ng != 0 {
        let gn = shstr.len as! u32;
        shstr.append(".group");
        shstr.push(0);
        for q in 1..ng + 1 { sh_name[q] = gn; }
    }
    for s in 1..ns {
        let x = osecs[s];
        let e = s + ng;
        sh_name[e] = shstr.len as! u32;
        shstr.append(sec_names[x.name_off..x.name_off + x.name_len]);
        shstr.push(0);
    }
    for s in 0..ns {
        if rela_of[s] == 0 { continue; }
        let x = osecs[s];
        sh_name[rela_of[s]] = shstr.len as! u32;
        shstr.append(".rela");
        shstr.append(sec_names[x.name_off..x.name_off + x.name_len]);
        shstr.push(0);
    }
    sh_name[sec_symtab] = shstr.len as! u32;
    shstr.append(".symtab");
    shstr.push(0);
    sh_name[sec_strtab] = shstr.len as! u32;
    shstr.append(".strtab");
    shstr.push(0);
    sh_name[sec_shstrtab] = shstr.len as! u32;
    shstr.append(".shstrtab");
    shstr.push(0);
    sh_name[sec_note] = shstr.len as! u32;
    shstr.append(".note.GNU-stack");
    shstr.push(0);

    o.clear();
    // ELF header (e_shoff patched below).
    o1(o, 0x7F); o1(o, 'E'); o1(o, 'L'); o1(o, 'F');
    o1(o, 2);  // ELFCLASS64
    o1(o, 1);  // ELFDATA2LSB
    o1(o, 1);  // EV_CURRENT
    for i in 9 { o1(o, 0); }
    o2(o, 1);   // ET_REL
    o2(o, 62);  // EM_X86_64
    o4(o, 1);   // e_version
    o8(o, 0);   // e_entry
    o8(o, 0);   // e_phoff
    o8(o, 0);   // e_shoff (patched)
    o4(o, 0);   // e_flags
    o2(o, 64);  // e_ehsize
    o2(o, 0);   // e_phentsize
    o2(o, 0);   // e_phnum
    o2(o, 64);  // e_shentsize
    o2(o, n_all as! u32);
    o2(o, sec_shstrtab as! u32);

    // Group sections: GRP_COMDAT (or 0) and the member sections.
    if ng != 0 {
        opad(o, 4);
        // the members of each group in section order (a counting sort by group)
        let nc = M.comdats.len;
        var gfirst: u32[>..] = [];
        gfirst.resize(nc + 2, 0);
        for s in 1..ns {
            let g: i64 = osecs[s].grp;
            if g != 0 { gfirst[g + 1] += 1; }
        }
        for g in 1..nc + 1 { gfirst[g + 1] += gfirst[g]; }
        var gfill: u32[>..] = [];
        gfill.resize(nc + 1, 0);
        var gmem: u32[>..] = [];
        gmem.resize(gfirst[nc + 1], 0);
        for s in 1..ns {
            let g: i64 = osecs[s].grp;
            if g == 0 { continue; }
            gmem[gfirst[g] + gfill[g]] = s as! u32;
            gfill[g] += 1;
        }
        for C, c in M.comdats {
            let q: i64 = cd_grp[c];
            if q == 0 { continue; }
            sh_off[q] = o.len as u64;
            o4(o, if C.kind == CD_NODEDUP { 0 } else { 1 });
            for k in gfirst[c + 1]..gfirst[c + 2] {
                let s: i64 = gmem[k];
                o4(o, (s + ng) as! u32);
                if rela_of[s] != 0 { o4(o, rela_of[s]); }
            }
            sh_size[q] = o.len as u64 - sh_off[q];
        }
    }
    // Section contents.
    for s in 1..ns {
        let x = osecs[s];
        let e = s + ng;
        let al: u64 = if x.align != 0 { x.align } else { 1 };
        if x.buf == BUF_NONE {
            sh_off[e] = o.len as u64;
            sh_size[e] = x.size;
            continue;
        }
        opad(o, al);
        sh_off[e] = o.len as u64;
        let st: i64 = x.start as! i64;
        let sz: i64 = x.size as! i64;
        if x.buf == BUF_CODE { obytes(o, mcode[st..st + sz]); sh_size[e] = x.size; }
        else if x.buf == BUF_DATA { obytes(o, sdata[st..st + sz]); sh_size[e] = x.size; }
        else if x.buf == BUF_RODATA { obytes(o, srodata); sh_size[e] = srodata.len as u64; }
        else if x.buf == BUF_CST4 { obytes(o, cst4); sh_size[e] = cst4.len as u64; }
        else if x.buf == BUF_CST8 { obytes(o, cst8); sh_size[e] = cst8.len as u64; }
        else if x.buf == BUF_CST16 { obytes(o, cst16); sh_size[e] = cst16.len as u64; }
        else if x.buf == BUF_EH { obytes(o, s_eh); sh_size[e] = s_eh.len as u64; }
        else if x.buf == BUF_DBG { obytes(o, s_dbg[st..st + sz]); sh_size[e] = x.size; }
        else {
            var k = x.xfirst;
            while k != GIR_NONE {
                let c = chunks[k];
                obytes(o, s_lsda[c.start..c.start + c.len]);
                k = c.next;
            }
            sh_size[e] = o.len as u64 - sh_off[e];
        }
    }
    // Relocation sections.
    opad(o, 8);
    for s in 0..ns {
        let a = rel_first[s];
        let b = rel_first[s + 1];
        if a == b { continue; }
        let r0 = rela_of[s];
        sh_off[r0] = o.len as u64;
        for k in a..b {
            let r = rel_sorted[k];
            o8(o, r.offset);
            o8(o, final_info(r.info));
            o8(o, r.addend as! u64);
        }
        sh_size[r0] = o.len as u64 - sh_off[r0];
    }

    // Symbol table: null, section symbols, locals, pool entries, group
    // signatures, then globals.
    sh_off[sec_symtab] = o.len as u64;
    for i in 24 { o1(o, 0); }
    for s in 1..ns {
        o4(o, 0);
        o1(o, 3);   // STB_LOCAL, STT_SECTION
        o1(o, 0);
        o2(o, (s + ng) as! u32);
        o8(o, 0);
        o8(o, 0);
    }
    for pass: u32 in 0..2 {
        if pass == 1 {
            // constant-pool entries: local, after the local globals
            for p in pool_syms {
                o4(o, 0);
                o1(o, 1);   // STB_LOCAL, STT_OBJECT
                o1(o, 0);
                o2(o, p.sec + ng as! u32);
                o8(o, p.off);
                o8(o, p.size);
            }
            // group signatures of ours: local, in the group section
            for c in cd_own {
                o4(o, M.comdats[c].name);
                o1(o, 0);   // STB_LOCAL, STT_NOTYPE
                o1(o, 0);
                o2(o, cd_grp[c]);
                o8(o, 0);
                o8(o, 0);
            }
        }
        for G, g in M.globals {
            let local: u32 = if G.flags & GF_INTERNAL != 0 { 1 } else { 0 };
            if local != (if pass == 0 { 1 } else { 0 }) { continue; }
            // STB_LOCAL/GLOBAL/WEAK
            let bind: u32 = if local != 0 { 0 } else if G.flags & GF_WEAK != 0 { 2 } else { 1 };
            let vis: u32 = if G.flags & GF_HIDDEN != 0 { 2 } else if G.flags & GF_PROTECTED != 0 { 3 } else { 0 };
            o4(o, G.name);
            o1(o, (bind << 4) | sym_type(G));
            o1(o, vis);
            if G.flags & GF_COMMON != 0 {
                o2(o, SHN_COMMON);
                o8(o, G.align);
                o8(o, G.size);
            } else {
                let sx = g_sec[g];
                o2(o, if sx != 0 { sx + ng as! u32 } else { 0 });
                o8(o, g_value[g]);
                o8(o, g_size[g]);
            }
        }
    }
    sh_size[sec_symtab] = o.len as u64 - sh_off[sec_symtab];

    // The GIR string table is a valid ELF string table (gir.h).
    sh_off[sec_strtab] = o.len as u64;
    if M.strtab.len != 0 { obytes(o, M.strtab); }
    else { o1(o, 0); }
    sh_size[sec_strtab] = o.len as u64 - sh_off[sec_strtab];

    sh_off[sec_shstrtab] = o.len as u64;
    obytes(o, shstr);
    sh_size[sec_shstrtab] = shstr.len as u64;

    sh_off[sec_note] = o.len as u64;

    // Section headers.
    opad(o, 8);
    let shoff = o.len as u64;
    let e_shoff = o[40..48];
    for i in 8 { e_shoff[i] = (shoff >> (8 * i)) as! u8; }
    // osec index of each ELF section (for the relocation sections' sh_info)
    var tgt_of: u32[>..] = [];
    tgt_of.resize(n_all, 0);
    for s in 0..ns { if rela_of[s] != 0 { tgt_of[rela_of[s]] = (s + ng) as! u32; } }
    var grp_sig: u32[>..] = [];
    grp_sig.resize(ng + 1, 0);
    for C, c in M.comdats {
        let q = cd_grp[c];
        if q == 0 { continue; }
        var sig: u64 = 0;
        if C.sig != GIR_NONE { sig = final_sym(g_sym[C.sig]); }
        else {
            for x, k in cd_own { if x == c as! u32 { sig = final_sym(CDSYM_BASE + k as! u64); } }
        }
        grp_sig[q] = sig as! u32;
    }
    for e in 0..n_all {
        var typ: u32 = 0;
        var flags: u64 = 0;
        var link: u32 = 0;
        var info: u32 = 0;
        var align: u64 = 1;
        var entsize: u64 = 0;
        if e == 0 {
            align = 0;
        } else if e <= ng {
            typ = SHT_GROUP;
            link = sec_symtab as! u32;
            info = grp_sig[e];
            align = 4;
            entsize = 4;
        } else if e < ng + ns {
            let s = e - ng;
            let x = osecs[s];
            typ = x.typ;
            flags = x.flags;
            align = if x.align != 0 { x.align } else { 1 };
            if s == SEC_RODATA { align = rodata_align; }
            entsize = x.entsize;
        } else if e < sec_symtab {
            typ = SHT_RELA;
            flags = SHF_INFO_LINK;
            if osecs[tgt_of[e] - ng as! u32].grp != 0 { flags |= SHF_GROUP; }
            link = sec_symtab as! u32;
            info = tgt_of[e];
            align = 8;
            entsize = 24;
        } else if e == sec_symtab {
            typ = SHT_SYMTAB;
            link = sec_strtab as! u32;
            info = n_local_syms + pool_syms.len as! u32 + cd_own.len as! u32;
            align = 8;
            entsize = 24;
        } else if e == sec_strtab || e == sec_shstrtab {
            typ = SHT_STRTAB;
        } else {
            typ = SHT_PROGBITS;
        }
        o4(o, if e == 0 { 0 } else { sh_name[e] });
        o4(o, typ);
        o8(o, flags);
        o8(o, 0);  // sh_addr
        o8(o, sh_off[e]);
        o8(o, sh_size[e]);
        o4(o, link);
        o4(o, info);
        o8(o, align);
        o8(o, entsize);
    }
}
