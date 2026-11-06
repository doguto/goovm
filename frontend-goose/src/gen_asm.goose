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
        // outputs tied to inputs take the input value
        var nout = 0;
        for i in nops {
            let o = nodes[nlist[nd.v + i]];
            if o.op == 1 { nout++; }
        }
        var oi = 0;
        for i in nops {
            let on = nlist[nd.v + i];
            let o = nodes[on];
            if o.op == 2 {
                let c = strlit_bytes(o.a);
                if c.len > 0 && c[0] >= '0' && c[0] <= '9' {
                    let k = (c[0] - '0') as i64;
                    // find output k
                    var j = 0;
                    for i2 in nops {
                        let o2 = nodes[nlist[nd.v + i2]];
                        if o2.op != 1 { continue; }
                        if j == k {
                            let v = ex_val(o.b);
                            let l = ex_lv(o2.b);
                            lv_store(l, conv(v, nty(o.b), unqual(nty(o2.b))));
                        }
                        j++;
                    }
                } else if has_side_effects(o.b) && !has_char(c, 'm') {
                    ex_ignore(o.b);
                }
            }
        }
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

// One statement per line (or ';'): mnemonic and up to two AT&T operands.
fn assemble(text: const u8[:]) -> bool {
    var i = 0;
    while i < text.len {
        var e = i;
        while e < text.len && text[e] != '\n' && text[e] != ';' { e++; }
        let line = trim(text[i..e]);
        i = e + 1;
        if line.len == 0 { continue; }
        if line[0] == '#' { continue; }
        if !asm_line(line) { return false; }
    }
    return true;
}

fn parse_reg(s: const u8[:]) -> i32, u32 {
    if s.len < 2 || s[0] != '%' { return -1, 0; }
    let nm = s[1..];
    for k in 16 {
        if nm == GPR64[k] { return k as! i32, 8; }
        if nm == GPR32[k] { return k as! i32, 4; }
        if nm == GPR16[k] { return k as! i32, 2; }
        if nm == GPR8[k] { return k as! i32, 1; }
    }
    return -1, 0;
}

fn rex(w: bool, r: i32, b: i32) {
    var x: u8 = 0x40;
    if w { x = x | 8; }
    if r >= 8 { x = x | 4; }
    if b >= 8 { x = x | 1; }
    if x != 0x40 { asm_code.push(x); }
}

fn asm_line(line: const u8[:]) -> bool {
    var sp = 0;
    while sp < line.len && line[sp] != ' ' && line[sp] != '\t' { sp++; }
    let mn = line[..sp];
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
    if mn == "rdtsc" || mn == "RDTSC" { asm_code.push(0x0F); asm_code.push(0x31); return true; }
    if mn == "rdtscp" { asm_code.push(0x0F); asm_code.push(0x01); asm_code.push(0xF9); return true; }
    if mn == "cpuid" { asm_code.push(0x0F); asm_code.push(0xA2); return true; }
    if mn == "nop" { asm_code.push(0x90); return true; }
    if mn == "pause" { asm_code.push(0xF3); asm_code.push(0x90); return true; }
    if mn == "mfence" { asm_code.push(0x0F); asm_code.push(0xAE); asm_code.push(0xF0); return true; }
    if mn == "lfence" { asm_code.push(0x0F); asm_code.push(0xAE); asm_code.push(0xE8); return true; }
    if mn == "sfence" { asm_code.push(0x0F); asm_code.push(0xAE); asm_code.push(0xF8); return true; }
    if mn == "fsqrt" { asm_code.push(0xD9); asm_code.push(0xFA); return true; }
    if mn == "fpatan" { asm_code.push(0xD9); asm_code.push(0xF3); return true; }
    if mn == "fsin" { asm_code.push(0xD9); asm_code.push(0xFE); return true; }
    if mn == "fcos" { asm_code.push(0xD9); asm_code.push(0xFF); return true; }
    if mn == "fabs" { asm_code.push(0xD9); asm_code.push(0xE1); return true; }
    if mn == "fchs" { asm_code.push(0xD9); asm_code.push(0xE0); return true; }
    if mn == "ud2" { asm_code.push(0x0F); asm_code.push(0x0B); return true; }
    if mn == "int3" { asm_code.push(0xCC); return true; }
    // one-register forms: mul / imul / div / idiv / neg / not / inc / dec / bswap
    let r1, s1 = parse_reg(op1);
    if op2.len == 0 && r1 >= 0 {
        let base = strip_suffix(mn);
        var ext: i32 = -1;
        if base == "mul" { ext = 4; } else if base == "imul" { ext = 5; } else if base == "div" { ext = 6; }
        else if base == "idiv" { ext = 7; } else if base == "neg" { ext = 3; } else if base == "not" { ext = 2; }
        if ext >= 0 {
            if s1 == 2 { asm_code.push(0x66); }
            rex(s1 == 8, 0, r1);
            asm_code.push(if s1 == 1 { 0xF6 } else { 0xF7 });
            asm_code.push((0xC0 | (ext << 3) | (r1 & 7)) as! u8);
            return true;
        }
        if base == "inc" || base == "dec" {
            if s1 == 2 { asm_code.push(0x66); }
            rex(s1 == 8, 0, r1);
            asm_code.push(if s1 == 1 { 0xFE } else { 0xFF });
            asm_code.push((0xC0 | (if base == "inc" { 0 } else { 8 }) | (r1 & 7)) as! u8);
            return true;
        }
        if base == "bswap" {
            rex(s1 == 8, 0, r1);
            asm_code.push(0x0F);
            asm_code.push((0xC8 + (r1 & 7)) as! u8);
            return true;
        }
    }
    // register-register ALU / mov
    let r2, s2 = parse_reg(op2);
    if r1 >= 0 && r2 >= 0 {
        let base = strip_suffix(mn);
        var opc: i32 = -1;
        if base == "mov" { opc = 0x89; } else if base == "add" { opc = 0x01; } else if base == "sub" { opc = 0x29; }
        else if base == "and" { opc = 0x21; } else if base == "or" { opc = 0x09; } else if base == "xor" { opc = 0x31; }
        else if base == "cmp" { opc = 0x39; } else if base == "test" { opc = 0x85; } else if base == "adc" { opc = 0x11; }
        else if base == "sbb" { opc = 0x19; } else if base == "xchg" { opc = 0x87; }
        if opc >= 0 {
            if s2 == 2 { asm_code.push(0x66); }
            rex(s2 == 8, r1, r2);
            asm_code.push((if s2 == 1 { opc - 1 } else { opc }) as! u8);
            asm_code.push((0xC0 | ((r1 & 7) << 3) | (r2 & 7)) as! u8);
            return true;
        }
    }
    return false;
}

fn strip_suffix(mn: const u8[:]) -> const u8[:] {
    if mn.len > 2 {
        let c = mn[mn.len - 1];
        let b = mn[..mn.len - 1];
        if (c == 'l' || c == 'q' || c == 'w' || c == 'b') &&
           (b == "mul" || b == "imul" || b == "div" || b == "idiv" || b == "neg" || b == "not" || b == "inc" || b == "dec" ||
            b == "mov" || b == "add" || b == "sub" || b == "and" || b == "or" || b == "xor" || b == "cmp" || b == "test" ||
            b == "adc" || b == "sbb" || b == "xchg" || b == "bswap") { return b; }
    }
    return mn;
}
