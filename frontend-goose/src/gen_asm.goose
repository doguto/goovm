// goosecc B2: inline assembly. An empty template (whitespace and comments)
// is only a barrier: an output tied to an input takes that input, other
// outputs are left alone (as tools/goovm-llc does). Any other template is
// bound like the exporter binds it (fixed registers as the constraints
// say, "r" / "q" / "g" from the caller-saved pool, "m" as (%reg), constant
// "i" as $imm), substituted, and assembled by the small AT&T assembler
// below into a GIR_ASM record: the back-end only moves the values in and
// out. The assembler covers the instructions the corpora use (DESIGN.md).

namespace gen;

import std;
import .common;
import .types;
import .ast;
import .sema;

struct AsmOp {
    kind: u8,        // 0 register, 1 memory (address in reg), 2 immediate
    out: bool,       // an output operand
    inout: bool,     // "+": also an input
    tied: i32,       // an input tied to output k
    reg: i32,
    size: u32,
    imm: i64,
    node: u32,       // the expression (lvalue for outputs)
    name: u32,       // symbolic name ident (0 none)
}

var asm_ops: AsmOp[>..<] = [];
var asm_text: u8[>..] = [];
var asm_code: u8[>..] = [];
var asm_in: u32[>..<] = [];     // (value, reg) pairs
var asm_outs: u32[>..<] = [];   // (reg, operand index) per direct output

fn strlit_bytes(n: u32) -> const u8[:] {
    let sl = strs[nodes[n].a];
    return strbytes[sl.start..sl.start + sl.len - 1];
}

fn is_empty_template(t: const u8[:]) -> bool {
    var i = 0;
    while i < t.len {
        let c = t[i];
        if c == '#' {
            while i < t.len && t[i] != '\n' { i++; }
            continue;
        }
        if c == '/' && i + 1 < t.len && t[i + 1] == '*' {
            i += 2;
            while i + 1 < t.len && !(t[i] == '*' && t[i + 1] == '/') { i++; }
            i += 2;
            continue;
        }
        if c != ' ' && c != '\t' && c != '\n' && c != '\r' && c != ';' { return false; }
        i++;
    }
    return true;
}

fn has_char(s: const u8[:], c: u8) -> bool {
    for x in s { if x == c { return true; } }
    return false;
}

// A constraint letter for one fixed register, or -1.
fn fixed_reg_of(c: const u8[:]) -> i32 {
    for x in c {
        if x == 'a' { return 0; }
        if x == 'b' { return 3; }
        if x == 'c' { return 1; }
        if x == 'd' { return 2; }
        if x == 'S' { return 6; }
        if x == 'D' { return 7; }
        if x == 't' { return 32; }
        if x == 'u' { return 33; }
    }
    return -1;
}

recursive fn gen_asm(n: u32) {
    let nd = nodes[n];
    if nd.op & 8 != 0 {
        err_at(nd.loc, "goosecc: file-scope asm is not supported");
        return;
    }
    let tmpl = strlit_bytes(nd.a);
    let nops = nd.c as i64;
    if is_empty_template(tmpl) {
        // the output lvalues are evaluated once; an output tied to an input
        // takes the input's value, other outputs keep theirs
        let mark = asm_in.len;
        for i in nops {
            let o = nodes[nlist[nd.v + i]];
            if o.op == 1 { asm_in.push(ex_lv(o.b).addr); asm_in.push(nlist[nd.v + i]); }
        }
        let nout = (asm_in.len - mark) / 2;
        for i in nops {
            let o = nodes[nlist[nd.v + i]];
            if o.op != 2 { continue; }
            let c = strlit_bytes(o.a);
            if c.len > 0 && c[0] >= '0' && c[0] <= '9' {
                let k = (c[0] - '0') as i64;
                let v = ex_val(o.b);
                if k < nout {
                    let on = nodes[asm_in[mark + 2 * k + 1]];
                    let oq = unqual(nty(on.b));
                    if vkind(oq) == VK_SCALAR && nodes[on.b].flags & NF_BITFIELD == 0 {
                        store_c(oq, conv(v, nty(o.b), oq), asm_in[mark + 2 * k], false);
                    }
                }
            } else if has_side_effects(o.b) && !has_char(c, 'm') {
                ex_ignore(o.b);
            }
        }
        asm_in.resize(mark);
        return;
    }
    gen_asm_code(n, tmpl);
}

let ASM_POOL: i32[9] = [0, 1, 2, 6, 7, 8, 9, 10, 11];

recursive fn gen_asm_code(n: u32, tmpl: const u8[:]) {
    let nd = nodes[n];
    let nops = nd.c as i64;
    asm_ops.clear();
    var used: u32 = 0;
    var used_x: u32 = 0;
    var st_clob: u32 = 0;
    // clobbers and fixed registers first
    for i in nops {
        let o = nodes[nlist[nd.v + i]];
        if o.op == 3 {
            let c = strlit_bytes(o.a);
            let r = clobber_reg(c);
            if r >= 32 { st_clob = st_clob | ((1 as u32) << ((r - 32) as! u32)); }
            else if r >= 16 { used_x = used_x | ((1 as u32) << ((r - 16) as! u32)); }
            else if r >= 0 { used = used | ((1 as u32) << (r as! u32)); }
        } else if o.op == 1 || o.op == 2 {
            let c = strlit_bytes(o.a);
            let r = fixed_reg_of(c);
            if r >= 0 && r < 16 { used = used | ((1 as u32) << (r as! u32)); }
        }
    }
    // outputs, then inputs (template operand order)
    for pass in 2 {
        for i in nops {
            let on = nlist[nd.v + i];
            let o = nodes[on];
            if pass == 0 && o.op != 1 { continue; }
            if pass == 1 && o.op != 2 { continue; }
            let c = strlit_bytes(o.a);
            var op = AsmOp { kind: 0, out: o.op == 1, inout: has_char(c, '+'), tied: -1, reg: -1, size: 8, imm: 0, node: o.b, name: o.c };
            let q = nty(o.b);
            var sz = type_size(q);
            if sz <= 0 || sz > 8 { sz = 8; }
            op.size = sz as! u32;
            if o.op == 2 && c.len > 0 && c[0] >= '0' && c[0] <= '9' {
                let k = (c[0] - '0') as i64;
                op.tied = k as! i32;
                op.reg = asm_ops[k].reg;
                op.kind = asm_ops[k].kind;
                asm_ops.push(op);
                continue;
            }
            let fr = fixed_reg_of(c);
            let ok, cv = fold_int(o.b);
            let imm_ok = has_char(c, 'i') || has_char(c, 'n') || has_char(c, 'g') || has_char(c, 'I') || has_char(c, 'J') ||
                has_char(c, 'K') || has_char(c, 'N') || has_char(c, 'e') || has_char(c, 'Z');
            if fr >= 0 {
                op.reg = fr;
            } else if o.op == 2 && ok && imm_ok && pure_const(o.b) {
                op.kind = 2;
                op.imm = cv;
            } else if has_char(c, 'x') {
                var k: i32 = 0;
                while k < 16 && used_x & ((1 as u32) << (k as! u32)) != 0 { k++; }
                used_x = used_x | ((1 as u32) << (k as! u32));
                op.reg = 16 + k;
            } else if has_char(c, 'r') || has_char(c, 'q') || has_char(c, 'R') || has_char(c, 'g') {
                op.reg = asm_alloc(used);
                used = used | ((1 as u32) << (op.reg as! u32));
            } else if has_char(c, 'm') || has_char(c, 'o') || has_char(c, 'V') {
                op.kind = 1;
                op.reg = asm_alloc(used);
                used = used | ((1 as u32) << (op.reg as! u32));
            } else {
                err_at(o.loc, str("goosecc: unsupported inline-asm constraint '", c, "'"));
                return;
            }
            asm_ops.push(op);
        }
    }
    // "+" outputs are also inputs: append them as tied inputs
    let n_explicit = asm_ops.len;
    for k in n_explicit {
        let op = asm_ops[k];
        if op.out && op.inout {
            asm_ops.push(AsmOp { kind: op.kind, out: false, inout: false, tied: k as! i32, reg: op.reg, size: op.size, imm: 0, node: op.node, name: 0 });
        }
    }
    // substitute
    asm_text.clear();
    var i = 0;
    while i < tmpl.len {
        let ch = tmpl[i];
        if ch != '%' { asm_text.push(ch); i++; continue; }
        if i + 1 >= tmpl.len { break; }
        var nx = tmpl[i + 1];
        if nx == '%' { asm_text.push('%'); i += 2; continue; }
        if nx == '=' { asm_text.append("0"); i += 2; continue; }
        var md: u8 = 0;
        var j = i + 1;
        if (nx >= 'a' && nx <= 'z') || (nx >= 'A' && nx <= 'Z') {
            if j + 1 < tmpl.len && ((tmpl[j + 1] >= '0' && tmpl[j + 1] <= '9') || tmpl[j + 1] == '[') { md = nx; j++; }
        }
        var num: i64 = -1;
        if j < tmpl.len && tmpl[j] == '[' {
            var e = j + 1;
            while e < tmpl.len && tmpl[e] != ']' { e++; }
            let nm = intern(tmpl[j + 1..e]);
            for op, k in asm_ops { if op.name == nm && num < 0 { num = k; } }
            j = e + 1;
        } else {
            num = 0;
            var any = false;
            while j < tmpl.len && tmpl[j] >= '0' && tmpl[j] <= '9' { num = num * 10 + (tmpl[j] - '0') as i64; j++; any = true; }
            if !any { asm_text.push('%'); i++; continue; }
        }
        if num < 0 || num >= asm_ops.len {
            err_at(nd.loc, "goosecc: inline-asm operand number out of range");
            return;
        }
        let op = asm_ops[num];
        if op.kind == 2 {
            if md == 'c' || md == 'P' { format(asm_text, op.imm); }
            else if md == 'n' { format(asm_text, 0 - op.imm); }
            else { asm_text.push('$'); format(asm_text, op.imm); }
        } else if op.kind == 1 {
            asm_text.append("(%");
            asm_text.append(gpr_name(op.reg, 8));
            asm_text.push(')');
        } else if op.reg >= 32 {
            if op.reg == 32 { asm_text.append("%st"); } else { asm_text.append("%st("); format(asm_text, op.reg - 32); asm_text.push(')'); }
        } else if op.reg >= 16 {
            asm_text.append("%xmm");
            format(asm_text, op.reg - 16);
        } else {
            var sz = op.size;
            if sz == 3 { sz = 4; } else if sz > 4 && sz < 8 { sz = 8; }
            if md == 'b' { sz = 1; } else if md == 'w' { sz = 2; } else if md == 'k' { sz = 4; } else if md == 'q' { sz = 8; }
            asm_text.push('%');
            asm_text.append(gpr_name(op.reg, sz));
        }
        i = j;
    }
    asm_code.clear();
    if !assemble(asm_text) {
        err_at(nd.loc, str("goosecc: cannot assemble inline asm '", asm_text, "'"));
        return;
    }
    // x87 bookkeeping: inputs on st(k) not tied and not popped are popped by the back-end
    var st_in: u32 = 0;
    var st_tied: u32 = 0;
    var st_popped: u32 = 0;
    for op in asm_ops {
        if op.kind != 0 || op.reg < 32 || op.out { continue; }
        st_in = st_in | ((1 as u32) << ((op.reg - 32) as! u32));
        if op.tied >= 0 { st_tied++; }
        else if st_clob & ((1 as u32) << ((op.reg - 32) as! u32)) != 0 { st_popped++; }
    }
    var n_st_in: u32 = 0;
    for k in 0..8 { if st_in & ((1 as u32) << (k as! u32)) != 0 { n_st_in++; } }
    let pop = n_st_in - st_tied - st_popped;
    // inputs: values (addresses for memory operands)
    asm_in.clear();
    for op in asm_ops {
        if op.kind == 2 { continue; }
        if op.out && op.kind == 1 {
            asm_in.push(ex_lv(op.node).addr);
            asm_in.push(op.reg as! u32);
            continue;
        }
        if op.out { continue; }
        var v: u32 = 0;
        if op.kind == 1 {
            v = agg_addr_any(op.node);
        } else {
            v = ex_val(op.node);
            if op.tied >= 0 {
                let oq = unqual(nty(asm_ops[op.tied].node));
                if vkind(oq) == VK_SCALAR && tsize(vty(oq)) > tsize(vtype(v)) { v = conv(v, nty(op.node), oq); }
            }
        }
        asm_in.push(v);
        asm_in.push(op.reg as! u32);
    }
    // direct outputs and the result type
    asm_outs.clear();
    for op, k in asm_ops {
        if !op.out || op.kind != 0 { continue; }
        asm_outs.push(op.reg as! u32);
        asm_outs.push(k as! u32);
    }
    let nout = asm_outs.len / 2;
    var rt: u32 = GIR_T_VOID;
    if nout == 1 {
        rt = mty(unqual(nty(asm_ops[asm_outs[1]].node)));
    } else if nout > 1 {
        var off: u32 = 0;
        for k in nout {
            let t = mty(unqual(nty(asm_ops[asm_outs[2 * k + 1]].node)));
            let al = m_types[t].align;
            off = (off + al - 1) / al * al;
            sfields.push(t);
            sfields.push(off);
            off += tsize(t);
        }
        rt = ty_struct();
    }
    let a = m_asms.len as! u32;
    let code_at = m_data.len as! u32;
    m_data.append(asm_code);
    let s = m_opnds.len as! u32;
    for k in asm_in.len / 2 {
        op_ref(asm_in[2 * k]);
        op_imm(asm_in[2 * k + 1]);
    }
    for k in nout {
        op_imm(asm_outs[2 * k]);
        if nout == 1 { op_imm(0); } else { op_imm(m_opnds[m_types[rt].elems + 2 * k + 1]); }
    }
    m_asms.push(Asm { code: code_at, code_len: asm_code.len as! u32, n_in: (asm_in.len / 2) as! u32, n_out: nout as! u32, ops: s, x87_pop: pop });
    let r = emit(GIR_ASM, rt, 0, 0, 0, a, 0, 0);
    for k in nout {
        let op = asm_ops[asm_outs[2 * k + 1]];
        let t = if nout == 1 { rt } else { m_opnds[m_types[rt].elems + 2 * k] };
        var v = r;
        if nout > 1 { v = emit(GIR_EXTRACTVALUE, t, 0, 0, 0, r, m_opnds[m_types[rt].elems + 2 * k + 1], 0); }
        let l = ex_lv(op.node);
        let oq = unqual(nty(op.node));
        if kind_of(oq) == TY_BOOL { v = int_cast(v, GIR_T_I8, GIR_T_I1, false); }
        lv_store(l, v);
    }
}

fn asm_alloc(used: u32) -> i32 {
    for r in ASM_POOL { if used & ((1 as u32) << (r as! u32)) == 0 { return r; } }
    return 11;
}

fn clobber_reg(c: const u8[:]) -> i32 {
    var s = c;
    if s.len > 0 && s[0] == '%' { s = s[1..]; }
    for k in 16 {
        if s == gpr_name(k as! i32, 8) || s == gpr_name(k as! i32, 4) || s == gpr_name(k as! i32, 2) || s == gpr_name(k as! i32, 1) { return k as! i32; }
    }
    if s == "ah" { return 0; }
    if s == "bh" { return 3; }
    if s == "ch" { return 1; }
    if s == "dh" { return 2; }
    if starts_with(s, "xmm") && s.len > 3 {
        var k: i32 = 0;
        for x in s[3..] { k = k * 10 + (x - '0') as i32; }
        return 16 + k;
    }
    if s == "st" { return 32; }
    if starts_with(s, "st(") && s.len == 5 { return 32 + (s[3] - '0') as i32; }
    return -1;
}

let GPR64 = ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"];
let GPR32 = ["eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi", "r8d", "r9d", "r10d", "r11d", "r12d", "r13d", "r14d", "r15d"];
let GPR16 = ["ax", "cx", "dx", "bx", "sp", "bp", "si", "di", "r8w", "r9w", "r10w", "r11w", "r12w", "r13w", "r14w", "r15w"];
let GPR8 = ["al", "cl", "dl", "bl", "spl", "bpl", "sil", "dil", "r8b", "r9b", "r10b", "r11b", "r12b", "r13b", "r14b", "r15b"];

fn gpr_name(r: i32, size: u32) -> const u8[:] {
    let k = (r & 15) as i64;
    if size == 1 { return GPR8[k]; }
    if size == 2 { return GPR16[k]; }
    if size == 4 { return GPR32[k]; }
    return GPR64[k];
}

// ------------------------------------------------------------ the assembler

// One statement per line (or ';'): an AT&T mnemonic and up to two operands
// (registers, $immediates, disp(%base,%index,scale) memory).
fn assemble(text: const u8[:]) -> bool {
    var i = 0;
    while i < text.len {
        var e = i;
        while e < text.len && text[e] != '\n' && text[e] != ';' { e++; }
        var line = trim(text[i..e]);
        i = e + 1;
        // comments
        var h = 0;
        while h < line.len && line[h] != '#' { h++; }
        line = trim(line[..h]);
        if line.len == 0 { continue; }
        if line[line.len - 1] == ':' { continue; }
        if !asm_line(line) { return false; }
    }
    return true;
}

// An operand: kind 0 none, 1 GPR, 2 xmm, 3 x87, 4 immediate, 5 memory.
struct AOp { kind: u8, reg: i32, size: u32, imm: i64, base: i32, index: i32, scale: u32, disp: i64 }

fn aop_none() -> AOp { AOp { kind: 0, reg: -1, size: 0, imm: 0, base: -1, index: -1, scale: 1, disp: 0 } }

fn parse_reg(s: const u8[:]) -> i32, u32 {
    if s.len < 2 || s[0] != '%' { return -1, 0; }
    let nm = s[1..];
    for k in 16 {
        if nm == GPR64[k] { return k as! i32, 8; }
        if nm == GPR32[k] { return k as! i32, 4; }
        if nm == GPR16[k] { return k as! i32, 2; }
        if nm == GPR8[k] { return k as! i32, 1; }
    }
    if nm == "ah" { return 4, 1; }
    if nm == "ch" { return 5, 1; }
    if nm == "dh" { return 6, 1; }
    if nm == "bh" { return 7, 1; }
    return -1, 0;
}

fn parse_int(s: const u8[:]) -> bool, i64 {
    var t = trim(s);
    var neg = false;
    if t.len > 0 && t[0] == '-' { neg = true; t = t[1..]; }
    if t.len == 0 { return false, 0; }
    var v: u64 = 0;
    var base: u64 = 10;
    var i = 0;
    if t.len > 2 && t[0] == '0' && (t[1] == 'x' || t[1] == 'X') { base = 16; i = 2; }
    while i < t.len {
        let c = t[i];
        var d: u64 = 99;
        if c >= '0' && c <= '9' { d = (c - '0') as u64; }
        else if c >= 'a' && c <= 'f' { d = (c - 'a') as u64 + 10; }
        else if c >= 'A' && c <= 'F' { d = (c - 'A') as u64 + 10; }
        if d >= base { return false, 0; }
        v = v * base + d;
        i++;
    }
    let r = v as! i64;
    return true, if neg { 0 - r } else { r };
}

fn parse_aop(s0: const u8[:]) -> bool, AOp {
    let s = trim(s0);
    var o = aop_none();
    if s.len == 0 { return true, o; }
    if s[0] == '$' {
        let ok, v = parse_int(s[1..]);
        o.kind = 4;
        o.imm = v;
        return ok, o;
    }
    if s[0] == '%' {
        let r, sz = parse_reg(s);
        if r >= 0 { o.kind = 1; o.reg = r; o.size = sz; return true, o; }
        if starts_with(s, "%xmm") {
            let ok, k = parse_int(s[4..]);
            o.kind = 2;
            o.reg = k as! i32;
            o.size = 16;
            return ok, o;
        }
        if s == "%st" || s == "%st(0)" { o.kind = 3; o.reg = 0; return true, o; }
        if starts_with(s, "%st(") && s.len == 6 { o.kind = 3; o.reg = (s[4] - '0') as i32; return true, o; }
        return false, o;
    }
    // memory: disp(%base,%index,scale)
    var p = 0;
    while p < s.len && s[p] != '(' { p++; }
    o.kind = 5;
    if p > 0 {
        let ok, d = parse_int(s[..p]);
        if !ok { return false, o; }
        o.disp = d;
    }
    if p >= s.len { return false, o; }
    var q = p + 1;
    var e = q;
    while e < s.len && s[e] != ',' && s[e] != ')' { e++; }
    if e > q {
        let r, sz = parse_reg(s[q..e]);
        if r < 0 || sz != 8 { return false, o; }
        o.base = r;
    }
    if e < s.len && s[e] == ',' {
        q = e + 1;
        e = q;
        while e < s.len && s[e] != ',' && s[e] != ')' { e++; }
        let r, sz = parse_reg(s[q..e]);
        if r < 0 || sz != 8 { return false, o; }
        o.index = r;
        if e < s.len && s[e] == ',' {
            q = e + 1;
            e = q;
            while e < s.len && s[e] != ')' { e++; }
            let ok, sc = parse_int(s[q..e]);
            if !ok { return false, o; }
            o.scale = sc as! u32;
        }
    }
    return true, o;
}

fn needs_rex8(o: AOp) -> bool { o.kind == 1 && o.size == 1 && o.reg >= 4 && o.reg < 8 && false }

// REX + opcode bytes + ModRM (+ SIB, disp) for reg field `reg` and r/m operand rm.
fn enc(w: bool, size16: bool, reg: i32, rm: AOp, opc: const u8[:], byte_regs: bool) {
    if size16 { asm_code.push(0x66); }
    var rx: u8 = 0x40;
    if w { rx = rx | 8; }
    if reg >= 8 { rx = rx | 4; }
    if rm.kind == 5 {
        if rm.index >= 8 { rx = rx | 2; }
        if rm.base >= 8 { rx = rx | 1; }
    } else if rm.reg >= 8 { rx = rx | 1; }
    if rx != 0x40 || byte_regs { asm_code.push(rx); }
    asm_code.append(opc);
    let r3 = ((reg & 7) << 3) as! u8;
    if rm.kind != 5 {
        asm_code.push(0xC0 | r3 | ((rm.reg & 7) as! u8));
        return;
    }
    let d = rm.disp;
    let b = rm.base;
    var md: u8 = 0;
    if b < 0 {
        // no base: SIB with base 101 and disp32
        asm_code.push(r3 | 4);
        let ix = if rm.index >= 0 { (rm.index & 7) as! u8 } else { 4 };
        asm_code.push((scale_bits(rm.scale) << 6) | (ix << 3) | 5);
        for k in 4 { asm_code.push(((d >> (8 * k)) & 255) as! u8); }
        return;
    }
    if d == 0 && (b & 7) != 5 { md = 0; } else if d >= -128 && d <= 127 { md = 0x40; } else { md = 0x80; }
    if rm.index >= 0 || (b & 7) == 4 {
        asm_code.push(md | r3 | 4);
        let ix = if rm.index >= 0 { (rm.index & 7) as! u8 } else { 4 };
        asm_code.push((scale_bits(rm.scale) << 6) | (ix << 3) | ((b & 7) as! u8));
    } else {
        asm_code.push(md | r3 | ((b & 7) as! u8));
    }
    if md == 0x40 { asm_code.push((d & 255) as! u8); }
    if md == 0x80 { for k in 4 { asm_code.push(((d >> (8 * k)) & 255) as! u8); } }
}

fn scale_bits(s: u32) -> u8 { if s == 2 { 1 } else if s == 4 { 2 } else if s == 8 { 3 } else { 0 } }

fn imm_bytes(v: i64, n: u32) { for k in n { asm_code.push(((v >> (8 * k)) & 255) as! u8); } }

let ALU_NAMES = ["add", "or", "adc", "sbb", "and", "sub", "xor", "cmp"];

fn suffix_size(mn: const u8[:], base: const u8[:]) -> u32 {
    if mn.len == base.len + 1 {
        let c = mn[mn.len - 1];
        if c == 'b' { return 1; }
        if c == 'w' { return 2; }
        if c == 'l' { return 4; }
        if c == 'q' { return 8; }
    }
    return 0;
}

// Splits a mnemonic into its base and operand size suffix (0 = none).
fn mn_split(mn: const u8[:]) -> const u8[:], u32 {
    let bases = ["mov", "add", "or", "adc", "sbb", "and", "sub", "xor", "cmp", "test", "xchg", "lea", "inc", "dec",
        "neg", "not", "mul", "imul", "div", "idiv", "shl", "shr", "sar", "sal", "rol", "ror", "bsr", "bsf", "bswap", "push", "pop"];
    for b in bases {
        if mn == b { return mn, 0; }
        let sz = suffix_size(mn, b);
        if sz != 0 && starts_with(mn, b) { return b, sz; }
    }
    return mn, 0;
}

fn asm_line(line: const u8[:]) -> bool {
    var sp = 0;
    while sp < line.len && line[sp] != ' ' && line[sp] != '\t' { sp++; }
    let mn0 = line[..sp];
    let rest = trim(line[sp..]);
    var op1: const u8[:] = "";
    var op2: const u8[:] = "";
    if rest.len > 0 {
        var depth = 0;
        var cut = -1;
        for c, k in rest {
            if c == '(' { depth++; }
            if c == ')' { depth--; }
            if c == ',' && depth == 0 && cut < 0 { cut = k; }
        }
        if cut >= 0 { op1 = trim(rest[..cut]); op2 = trim(rest[cut + 1..]); } else { op1 = rest; }
    }
    // no operands
    if mn0 == "rdtsc" || mn0 == "RDTSC" { asm_code.push(0x0F); asm_code.push(0x31); return true; }
    if mn0 == "rdtscp" { asm_code.push(0x0F); asm_code.push(0x01); asm_code.push(0xF9); return true; }
    if mn0 == "cpuid" { asm_code.push(0x0F); asm_code.push(0xA2); return true; }
    if mn0 == "nop" { asm_code.push(0x90); return true; }
    if mn0 == "pause" { asm_code.push(0xF3); asm_code.push(0x90); return true; }
    if mn0 == "mfence" { asm_code.push(0x0F); asm_code.push(0xAE); asm_code.push(0xF0); return true; }
    if mn0 == "lfence" { asm_code.push(0x0F); asm_code.push(0xAE); asm_code.push(0xE8); return true; }
    if mn0 == "sfence" { asm_code.push(0x0F); asm_code.push(0xAE); asm_code.push(0xF8); return true; }
    if mn0 == "ud2" { asm_code.push(0x0F); asm_code.push(0x0B); return true; }
    if mn0 == "int3" { asm_code.push(0xCC); return true; }
    if mn0 == "cltd" || mn0 == "cdq" { asm_code.push(0x99); return true; }
    if mn0 == "cqto" || mn0 == "cqo" { asm_code.push(0x48); asm_code.push(0x99); return true; }
    if mn0 == "cltq" || mn0 == "cdqe" { asm_code.push(0x48); asm_code.push(0x98); return true; }
    if mn0 == "clc" { asm_code.push(0xF8); return true; }
    if mn0 == "stc" { asm_code.push(0xF9); return true; }
    if mn0 == "cld" { asm_code.push(0xFC); return true; }
    if mn0 == "fsqrt" { asm_code.push(0xD9); asm_code.push(0xFA); return true; }
    if mn0 == "fpatan" { asm_code.push(0xD9); asm_code.push(0xF3); return true; }
    if mn0 == "fptan" { asm_code.push(0xD9); asm_code.push(0xF2); return true; }
    if mn0 == "fsin" { asm_code.push(0xD9); asm_code.push(0xFE); return true; }
    if mn0 == "fcos" { asm_code.push(0xD9); asm_code.push(0xFF); return true; }
    if mn0 == "fsincos" { asm_code.push(0xD9); asm_code.push(0xFB); return true; }
    if mn0 == "fabs" { asm_code.push(0xD9); asm_code.push(0xE1); return true; }
    if mn0 == "fchs" { asm_code.push(0xD9); asm_code.push(0xE0); return true; }
    if mn0 == "fld1" { asm_code.push(0xD9); asm_code.push(0xE8); return true; }
    if mn0 == "fldz" { asm_code.push(0xD9); asm_code.push(0xEE); return true; }
    if mn0 == "frndint" { asm_code.push(0xD9); asm_code.push(0xFC); return true; }
    if mn0 == "fscale" { asm_code.push(0xD9); asm_code.push(0xFD); return true; }
    if mn0 == "f2xm1" { asm_code.push(0xD9); asm_code.push(0xF0); return true; }
    if mn0 == "fyl2x" { asm_code.push(0xD9); asm_code.push(0xF1); return true; }
    if mn0 == "fprem" { asm_code.push(0xD9); asm_code.push(0xF8); return true; }
    if mn0 == "fxch" && op1.len == 0 { asm_code.push(0xD9); asm_code.push(0xC9); return true; }
    let ok1, a = parse_aop(op1);
    let ok2, b = parse_aop(op2);
    if !ok1 || !ok2 { return false; }
    // SSE scalar / packed arithmetic: xmm or memory -> xmm
    let sse = sse_opcode(mn0);
    if sse >= 0 && b.kind == 2 && (a.kind == 2 || a.kind == 5) {
        let pfx = (sse >> 8) & 255;
        if pfx != 0 { asm_code.push(pfx as! u8); }
        let opc: u8[2] = [0x0F, (sse & 255) as! u8];
        enc(false, false, b.reg, a, opc, false);
        return true;
    }
    let mn, sfx = mn_split(mn0);
    var size = sfx;
    if size == 0 { size = if b.kind == 1 { b.size } else if a.kind == 1 { a.size } else { 4 }; }
    let w = size == 8;
    let s16 = size == 2;
    let byte = size == 1;
    let br = byte && ((a.kind == 1 && a.reg >= 4 && a.reg < 8 && op1.len > 2 && op1[op1.len - 1] == 'l') ||
        (b.kind == 1 && b.reg >= 4 && b.reg < 8 && op2.len > 2 && op2[op2.len - 1] == 'l'));
    // one operand
    if op2.len == 0 && (a.kind == 1 || a.kind == 5) {
        var ext: i32 = -1;
        var opc: u8 = 0;
        if mn == "inc" { ext = 0; opc = if byte { 0xFE } else { 0xFF }; }
        else if mn == "dec" { ext = 1; opc = if byte { 0xFE } else { 0xFF }; }
        else if mn == "not" { ext = 2; opc = if byte { 0xF6 } else { 0xF7 }; }
        else if mn == "neg" { ext = 3; opc = if byte { 0xF6 } else { 0xF7 }; }
        else if mn == "mul" { ext = 4; opc = if byte { 0xF6 } else { 0xF7 }; }
        else if mn == "imul" { ext = 5; opc = if byte { 0xF6 } else { 0xF7 }; }
        else if mn == "div" { ext = 6; opc = if byte { 0xF6 } else { 0xF7 }; }
        else if mn == "idiv" { ext = 7; opc = if byte { 0xF6 } else { 0xF7 }; }
        if ext >= 0 {
            let o: u8[1] = [opc];
            enc(w, s16, ext, a, o, br);
            return true;
        }
        if mn == "bswap" && a.kind == 1 {
            if a.reg >= 8 || w { asm_code.push((0x40 | (if w { 8 } else { 0 }) | (if a.reg >= 8 { 1 } else { 0 })) as! u8); }
            asm_code.push(0x0F);
            asm_code.push((0xC8 + (a.reg & 7)) as! u8);
            return true;
        }
    }
    if op2.len == 0 { return false; }
    // shifts: $imm or %cl
    if mn == "shl" || mn == "sal" || mn == "shr" || mn == "sar" || mn == "rol" || mn == "ror" {
        let ext: i32 = if mn == "shl" || mn == "sal" { 4 } else if mn == "shr" { 5 } else if mn == "sar" { 7 } else if mn == "rol" { 0 } else { 1 };
        if a.kind == 4 {
            let o: u8[1] = [if byte { 0xC0 } else { 0xC1 }];
            enc(w, s16, ext, b, o, br);
            asm_code.push((a.imm & 255) as! u8);
            return true;
        }
        if a.kind == 1 && a.reg == 1 && a.size == 1 {
            let o: u8[1] = [if byte { 0xD2 } else { 0xD3 }];
            enc(w, s16, ext, b, o, br);
            return true;
        }
        return false;
    }
    if mn == "lea" && a.kind == 5 && b.kind == 1 {
        let o: u8[1] = [0x8D];
        enc(w, s16, b.reg, a, o, false);
        return true;
    }
    if (mn == "bsr" || mn == "bsf") && b.kind == 1 && (a.kind == 1 || a.kind == 5) {
        let o: u8[2] = [0x0F, if mn == "bsr" { 0xBD } else { 0xBC }];
        enc(w, s16, b.reg, a, o, false);
        return true;
    }
    if mn == "imul" && a.kind != 4 && b.kind == 1 {
        let o: u8[2] = [0x0F, 0xAF];
        enc(w, s16, b.reg, a, o, false);
        return true;
    }
    var alu: i32 = -1;
    for nm, k in ALU_NAMES { if mn == nm { alu = k as! i32; } }
    if mn == "mov" || mn == "test" || mn == "xchg" || alu >= 0 {
        // immediate source
        if a.kind == 4 {
            if mn == "mov" {
                if b.kind == 1 && !w {
                    if s16 { asm_code.push(0x66); }
                    if b.reg >= 8 || br { asm_code.push((0x40 | (if b.reg >= 8 { 1 } else { 0 })) as! u8); }
                    let base_op: i32 = if byte { 0xB0 } else { 0xB8 };
                    asm_code.push((base_op + (b.reg & 7)) as! u8);
                    imm_bytes(a.imm, size);
                    return true;
                }
                let o: u8[1] = [if byte { 0xC6 } else { 0xC7 }];
                enc(w, s16, 0, b, o, br);
                imm_bytes(a.imm, if byte { 1 } else if s16 { 2 } else { 4 });
                return true;
            }
            if mn == "test" {
                let o: u8[1] = [if byte { 0xF6 } else { 0xF7 }];
                enc(w, s16, 0, b, o, br);
                imm_bytes(a.imm, if byte { 1 } else if s16 { 2 } else { 4 });
                return true;
            }
            if alu >= 0 {
                if byte {
                    let o: u8[1] = [0x80];
                    enc(false, false, alu, b, o, br);
                    imm_bytes(a.imm, 1);
                } else if a.imm >= -128 && a.imm <= 127 {
                    let o: u8[1] = [0x83];
                    enc(w, s16, alu, b, o, br);
                    imm_bytes(a.imm, 1);
                } else {
                    let o: u8[1] = [0x81];
                    enc(w, s16, alu, b, o, br);
                    imm_bytes(a.imm, if s16 { 2 } else { 4 });
                }
                return true;
            }
            return false;
        }
        let base: u8 = if mn == "mov" { 0x88 } else if mn == "test" { 0x84 } else if mn == "xchg" { 0x86 } else { ((alu as u32) * 8) as! u8 };
        if a.kind == 1 && (b.kind == 1 || b.kind == 5) {
            // reg -> r/m
            let o: u8[1] = [if byte { base } else { base + 1 }];
            enc(w, s16, a.reg, b, o, br);
            return true;
        }
        if a.kind == 5 && b.kind == 1 && mn != "test" {
            // r/m -> reg
            let o: u8[1] = [if mn == "xchg" { if byte { base } else { base + 1 } } else if byte { base + 2 } else { base + 3 }];
            enc(w, s16, b.reg, a, o, br);
            return true;
        }
    }
    return false;
}

// SSE instructions xmm/m -> xmm: (prefix << 8) | opcode, or -1.
fn sse_opcode(mn: const u8[:]) -> i32 {
    if mn == "addsd" { return 0xF258; }
    if mn == "subsd" { return 0xF25C; }
    if mn == "mulsd" { return 0xF259; }
    if mn == "divsd" { return 0xF25E; }
    if mn == "sqrtsd" { return 0xF251; }
    if mn == "minsd" { return 0xF25D; }
    if mn == "maxsd" { return 0xF25F; }
    if mn == "movsd" { return 0xF210; }
    if mn == "addss" { return 0xF358; }
    if mn == "subss" { return 0xF35C; }
    if mn == "mulss" { return 0xF359; }
    if mn == "divss" { return 0xF35E; }
    if mn == "sqrtss" { return 0xF351; }
    if mn == "movss" { return 0xF310; }
    if mn == "addps" { return 0x58; }
    if mn == "mulps" { return 0x59; }
    if mn == "subps" { return 0x5C; }
    if mn == "divps" { return 0x5E; }
    if mn == "xorps" { return 0x57; }
    if mn == "andps" { return 0x54; }
    if mn == "orps" { return 0x56; }
    if mn == "movaps" { return 0x28; }
    if mn == "movups" { return 0x10; }
    if mn == "addpd" { return 0x6658; }
    if mn == "mulpd" { return 0x6659; }
    if mn == "xorpd" { return 0x6657; }
    if mn == "ucomisd" { return 0x662E; }
    if mn == "ucomiss" { return 0x2E; }
    return -1;
}
