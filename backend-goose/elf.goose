// Output sections, symbols and the ELF64 relocatable-object writer.
//
// Section indices are fixed for the default sections; every GIR section
// (section attributes, .init_array/.fini_array) follows. Relocation
// sections, .symtab, .strtab, .shstrtab and .note.GNU-stack come last.
// Symbols: null, one STT_SECTION symbol per output section (index = section
// index), the local globals, then all other globals.

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
let BUF_CODE = 1;    // code[start .. start + size]
let BUF_DATA = 2;    // sdata[start .. start + size]
let BUF_RODATA = 3;  // srodata
let BUF_CST4 = 4;
let BUF_CST8 = 5;
let BUF_CST16 = 6;

let SHT_PROGBITS = 1;
let SHT_SYMTAB = 2;
let SHT_STRTAB = 3;
let SHT_RELA = 4;
let SHT_NOBITS = 8;
let SHF_WRITE = 1;
let SHF_ALLOC = 2;
let SHF_EXEC = 4;
let SHF_MERGE = 0x10;
let SHF_INFO_LINK = 0x40;
let SHF_TLS = 0x400;
let SHN_COMMON = 0xFFF2;

struct OSec { name: u32, typ: u32, flags: u64, align: u64, entsize: u64, buf: u32, start: u64, size: u64,
              name_off: u32, name_len: u32 }

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

// Per block (global block index): code offset, for blockaddress.
var blk_code: u32[>..] = [];
// Pending blockaddress operands: rel32 at code[pos] -> global block blk.
var baddr: Fixup[>..] = [];
// Code range of the section each function went to: f_sec[fi].
var f_sec: u32[>..] = [];

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
    if s >= POOL_BASE { return n_local_syms + (s - POOL_BASE); }
    if s >= n_local_syms { return s + pool_syms.len as u64; }
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
    osecs.push(OSec { name: 0, typ: typ, flags: flags, align: align, entsize: entsize, buf: buf, start: 0,
                      size: 0, name_off: 0, name_len: name.len as! u32 });
    // The name is copied into shstrtab at write time; remember it here.
    let k: i64 = osecs.len - 1;
    osecs[k].name_off = sec_names.len as! u32;
    sec_names.append(name);
}
var sec_names: u8[>..] = [];   // default section names, concatenated (no NULs)

// The default sections and one per GIR section.
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
}

// Output section of global g.
fn global_section(G: Global) -> u32 {
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

    // Globals grouped by section, in table order within a section.
    sec_count.clear();
    sec_count.resize(nsec + 1, 0);
    for G, g in M.globals {
        let s = global_section(G);
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
                    bss = (bss + al - 1) / al * al;
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
        patch4(x.pos, tgt - (x.pos + 4));
    }
}

// --------------------------------------------------------------- ELF

struct Rel2 { offset: u64, info: u64, addend: i64, sec: u64 }
var rels: Rel2[>..] = [];        // all relocations, grouped by section before writing
var rel_sorted: Rel2[>..] = [];
var rel_first: u32[>..] = [];

fn sym_type(G0: Global) -> u32 {
    let G = if G0.kind == G_ALIAS { M.globals[G0.func] } else { G0 };
    if G.flags & (GF_DEFINED | GF_COMMON) == 0 { return 0; }   // NOTYPE
    if G.kind == G_FUNC { return 2; }                          // FUNC
    if G.flags & GF_TLS != 0 { return 6; }                     // TLS
    return 1;                                                  // OBJECT
}

fn collect_relocs() {
    rels.clear();
    // Code relocations: section = the code section containing the offset.
    let ns = osecs.len;
    for r in rela_code {
        var s: u64 = SEC_TEXT;
        for k in 1..ns {
            let o = osecs[k];
            if o.buf == BUF_CODE && r.offset >= o.start && r.offset < o.start + o.size {
                s = k as u64;
                break;
            }
        }
        rels.push(Rel2 { offset: r.offset - osecs[s].start, info: r.info, addend: r.addend, sec: s });
    }
    // Data relocations.
    for d in M.drelocs {
        let ow: i64 = d.owner;
        let s: i64 = g_sec[ow];
        let off = g_value[ow] + d.offset;
        if d.kind == DR_ABS64 {
            rels.push(Rel2 { offset: off, info: (g_sym[d.target] as u64 << 32) | R_X86_64_64, addend: d.addend,
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
    // Group by section (counting sort, stable).
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
    // Section list: osecs, then one .rela per section with relocations,
    // then .symtab .strtab .shstrtab .note.GNU-stack.
    var n_rela: i64 = 0;
    for s in 0..ns { if rel_first[s + 1] > rel_first[s] { n_rela++; } }
    let sec_symtab = ns + n_rela;
    let sec_strtab = sec_symtab + 1;
    let sec_shstrtab = sec_symtab + 2;
    let sec_note = sec_symtab + 3;
    let n_all = sec_symtab + 4;

    // Section header string table.
    var shstr: u8[>..] = [0];
    var sh_name: u32[>..] = [];
    sh_name.resize(n_all, 0);
    var sh_off: u64[>..] = [];
    sh_off.resize(n_all, 0);
    var sh_size: u64[>..] = [];
    sh_size.resize(n_all, 0);
    for s in 1..ns {
        let x = osecs[s];
        sh_name[s] = shstr.len as! u32;
        shstr.append(sec_names[x.name_off..x.name_off + x.name_len]);
        shstr.push(0);
    }
    var ri = ns;
    for s in 0..ns {
        if rel_first[s + 1] == rel_first[s] { continue; }
        let x = osecs[s];
        sh_name[ri] = shstr.len as! u32;
        shstr.append(".rela");
        shstr.append(sec_names[x.name_off..x.name_off + x.name_len]);
        shstr.push(0);
        ri++;
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

    // Section contents.
    for s in 1..ns {
        let x = osecs[s];
        let al: u64 = if x.align != 0 { x.align } else { 1 };
        if x.buf == BUF_NONE {
            sh_off[s] = o.len as u64;
            sh_size[s] = x.size;
            continue;
        }
        opad(o, al);
        sh_off[s] = o.len as u64;
        let st: i64 = x.start as! i64;
        let sz: i64 = x.size as! i64;
        if x.buf == BUF_CODE { obytes(o, code[st..st + sz]); sh_size[s] = x.size; }
        else if x.buf == BUF_DATA { obytes(o, sdata[st..st + sz]); sh_size[s] = x.size; }
        else if x.buf == BUF_RODATA { obytes(o, srodata); sh_size[s] = srodata.len as u64; }
        else if x.buf == BUF_CST4 { obytes(o, cst4); sh_size[s] = cst4.len as u64; }
        else if x.buf == BUF_CST8 { obytes(o, cst8); sh_size[s] = cst8.len as u64; }
        else { obytes(o, cst16); sh_size[s] = cst16.len as u64; }
    }
    // Relocation sections.
    opad(o, 8);
    ri = ns;
    for s in 0..ns {
        let a = rel_first[s];
        let b = rel_first[s + 1];
        if a == b { continue; }
        sh_off[ri] = o.len as u64;
        for k in a..b {
            let r = rel_sorted[k];
            o8(o, r.offset);
            o8(o, final_info(r.info));
            o8(o, r.addend as! u64);
        }
        sh_size[ri] = o.len as u64 - sh_off[ri];
        ri++;
    }

    // Symbol table: null, section symbols, locals, then globals.
    sh_off[sec_symtab] = o.len as u64;
    for i in 24 { o1(o, 0); }
    for s in 1..ns {
        o4(o, 0);
        o1(o, 3);   // STB_LOCAL, STT_SECTION
        o1(o, 0);
        o2(o, s as! u32);
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
                o2(o, p.sec);
                o8(o, p.off);
                o8(o, p.size);
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
                o2(o, g_sec[g]);
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
    for s in 0..n_all {
        var typ: u32 = 0;
        var flags: u64 = 0;
        var link: u32 = 0;
        var info: u32 = 0;
        var align: u64 = 1;
        var entsize: u64 = 0;
        if s == 0 {
            align = 0;
        } else if s < ns {
            let x = osecs[s];
            typ = x.typ;
            flags = x.flags;
            align = if x.align != 0 { x.align } else { 1 };
            if s == SEC_RODATA { align = rodata_align; }
            entsize = x.entsize;
        } else if s < sec_symtab {
            typ = SHT_RELA;
            flags = SHF_INFO_LINK;
            link = sec_symtab as! u32;
            align = 8;
            entsize = 24;
        } else if s == sec_symtab {
            typ = SHT_SYMTAB;
            link = sec_strtab as! u32;
            info = n_local_syms + pool_syms.len as! u32;
            align = 8;
            entsize = 24;
        } else if s == sec_strtab || s == sec_shstrtab {
            typ = SHT_STRTAB;
        } else {
            typ = SHT_PROGBITS;
        }
        o4(o, if s == 0 { 0 } else { sh_name[s] });
        o4(o, typ);
        o8(o, flags);
        o8(o, 0);  // sh_addr
        o8(o, sh_off[s]);
        o8(o, sh_size[s]);
        o4(o, link);
        o4(o, info);
        o8(o, align);
        o8(o, entsize);
    }
    // sh_info of each relocation section: the section it applies to.
    ri = ns;
    for s in 0..ns {
        if rel_first[s + 1] == rel_first[s] { continue; }
        let at: i64 = (shoff + 64 * ri as! u64 + 44) as! i64;
        let w = o[at..at + 4];
        w[0] = s as! u8;
        w[1] = (s >> 8) as! u8;
        w[2] = 0;
        w[3] = 0;
        ri++;
    }
}
