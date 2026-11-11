// goosecc F1: inline assembly on AArch64. The operands are bound as
// tools/goovm-llc binds them (asm_code_a64): fixed registers ("{x3}",
// local register variables, clobbers) first, then "r" from x0..x15, "w"
// from v0..v7 / v16..v30, "x" from v0..v15, "y" from v0..v7, "m" / "Q" as
// [xN], constant "I".."N" / "Z" / "i" / "n" as immediates (0 with %w / %x
// as wzr / xzr). The substituted template is assembled by the small
// AArch64 assembler below into a GIR_ASM record: base integer, branches to
// local labels, loads and stores (all addressing modes, pairs, exclusives,
// LSE atomics), system registers and barriers, scalar FP, and the common
// Advanced SIMD instructions (three-same, two-register, across lanes, by
// element, shifts by immediate, long / narrow, permutes, copies, modified
// immediates, tables, structure loads and stores), CRC32, AES, SHA-1/256
// and the dot products. Anything else is an error, never a guess.

namespace gen;

import std;
import .common;
import .types;
import .ast;
import .sema;

// ---------------------------------------------------------------- binding

// The register a fixed-register name denotes (x0..x30 / w0..w30 / sp / fp /
// lr: 0..31; v / q / d / s / h / b: 32 + n), or -1.
fn a64_fixed(nm0: const u8[:]) -> i64 {
    var nm = nm0;
    if nm.len > 0 && nm[0] == '%' { nm = nm[1..]; }
    if nm.len > 2 && nm[0] == '{' && nm[nm.len - 1] == '}' { nm = nm[1..nm.len - 1]; }
    if nm == "sp" || nm == "wsp" { return 31; }
    if nm == "fp" { return 29; }
    if nm == "lr" { return 30; }
    if nm.len < 2 { return -1; }
    let k = a_dec(nm[1..]);
    if k < 0 { return -1; }
    let c = nm[0];
    if (c == 'x' || c == 'w') && k <= 30 { return k; }
    if (c == 'v' || c == 'q' || c == 'd' || c == 's' || c == 'h' || c == 'b') && k < 32 { return 32 + k; }
    return -1;
}

// A local register variable (register T x __asm__("x3")) operand: its register, or -1.
fn a64_regvar(n: u32) -> i64 {
    var m = n;
    while nodes[m].kind == N_ICAST { m = nodes[m].a; }
    if nodes[m].kind != N_DECLREF { return -1; }
    let s = nodes[m].a as i64;
    if syms[s].sc != SC_REGISTER as! u8 { return -1; }
    let a = syms[s].attr as i64;
    if a == 0 || sym_attrs[a].asm_len == 0 { return -1; }
    let off = sym_attrs[a].asm_label as i64;
    return a64_fixed(strbytes[off..off + sym_attrs[a].asm_len as i64]);
}

fn a64_con_fixed(c: const u8[:]) -> i64 {
    var i = 0;
    while i < c.len && (c[i] == '=' || c[i] == '+' || c[i] == '&') { i++; }
    if i < c.len && c[i] == '{' { return a64_fixed(c[i..]); }
    return -1;
}

fn a64_pool(used: u64, pool: u64) -> i64 {
    for r in 64 {
        let b = (1 as u64) << (r as! u64);
        if pool & b != 0 && used & b == 0 { return r; }
    }
    return -1;
}

// Does constant v satisfy one of the immediate letters of constraint c?
fn a64_imm_fits(c: const u8[:], v: i64) -> bool {
    for x in c {
        if x == 'i' || x == 'n' || x == 'g' { return true; }
        if x == 'Z' && v == 0 { return true; }
        if x == 'I' && v >= 0 && v <= 4095 { return true; }
        if x == 'J' && v >= -4095 && v <= 0 { return true; }
        if x == 'K' { let ok, a, b, d = a_bitmask(v, 32); if ok { return true; } }
        if x == 'L' { let ok, a, b, d = a_bitmask(v, 64); if ok { return true; } }
        if x == 'M' && a_movable(v, 32) { return true; }
        if x == 'N' && a_movable(v, 64) { return true; }
    }
    return false;
}
fn a64_has_imm_letter(c: const u8[:]) -> bool {
    for x in c { if x == 'i' || x == 'n' || x == 'g' || x == 'Z' || (x >= 'I' && x <= 'N') { return true; } }
    return false;
}
// a mov-immediate (one MOVZ / MOVN / ORR) of width w
fn a_movable(v: i64, w: i64) -> bool {
    if w == 32 && (v < -2147483648 || v > 4294967295) { return false; }
    let k, x = a_mov_imm(v, w);
    return k >= 0;
}

let A64_GPOOL: u64 = 0xFFFF;                  // x0..x15
let A64_WPOOL: u64 = 0x7FFF00FF00000000;      // v0..v7, v16..v30
let A64_XPOOL: u64 = 0x0000FFFF00000000;      // v0..v15
let A64_YPOOL: u64 = 0x000000FF00000000;      // v0..v7

fn a64_asm_bind(n: u32, tmpl: const u8[:]) -> bool {
    let nd = nodes[n];
    let nops = nd.c as i64;
    asm_ops.clear();
    var used: u64 = 0;
    for i in nops {
        let o = nodes[nlist[nd.v + i]];
        if o.op == 3 {
            let r = a64_fixed(strlit_bytes(o.a));
            if r >= 0 { used = used | ((1 as u64) << (r as! u64)); }
        } else if o.op == 1 || o.op == 2 {
            var r = a64_con_fixed(strlit_bytes(o.a));
            if r < 0 { r = a64_regvar(o.b); }
            if r >= 0 { used = used | ((1 as u64) << (r as! u64)); }
        }
    }
    for pass in 2 {
        for i in nops {
            let o = nodes[nlist[nd.v + i]];
            if pass == 0 && o.op != 1 { continue; }
            if pass == 1 && o.op != 2 { continue; }
            let c = strlit_bytes(o.a);
            var op = AsmOp { kind: 0, out: o.op == 1, inout: has_char(c, '+'), tied: -1, reg: -1, size: 8, imm: 0, node: o.b, name: o.c };
            var sz = type_size(nty(o.b));
            if sz <= 0 { sz = 8; }
            op.size = sz as! u32;
            if o.op == 2 && c.len > 0 && c[0] >= '0' && c[0] <= '9' {
                let k = (c[0] - '0') as i64;
                if k >= asm_ops.len || asm_ops[k].kind != 0 {
                    err_at(o.loc, "goosecc: inline-asm input tied to a missing or memory output");
                    return false;
                }
                op.tied = k as! i32;
                op.reg = asm_ops[k].reg;
                op.size = asm_ops[k].size;
                asm_ops.push(op);
                continue;
            }
            var fr = a64_con_fixed(c);
            if fr < 0 && (has_char(c, 'r') || has_char(c, 'w') || has_char(c, 'x') || has_char(c, 'y')) { fr = a64_regvar(o.b); }
            let ok, cv = fold_int(o.b);
            let regs = has_char(c, 'r') || has_char(c, 'w') || has_char(c, 'x') || has_char(c, 'y');
            var pool: u64 = 0;
            if fr >= 0 {
                op.reg = fr as! i32;
            } else if o.op == 2 && ok && a64_has_imm_letter(c) && pure_const(o.b) && (a64_imm_fits(c, cv) || !regs) {
                op.kind = 2;
                op.imm = cv;
            } else if has_char(c, 'w') { pool = A64_WPOOL; }
            else if has_char(c, 'x') { pool = A64_XPOOL; }
            else if has_char(c, 'y') { pool = A64_YPOOL; }
            else if has_char(c, 'r') || has_char(c, 'g') { pool = A64_GPOOL; }
            else if has_char(c, 'm') || has_char(c, 'Q') || has_char(c, 'o') || has_char(c, 'V') || has_char(c, 'U') {
                op.kind = 1;
                pool = A64_GPOOL;
            } else {
                err_at(o.loc, str("goosecc: unsupported inline-asm constraint '", c, "'"));
                return false;
            }
            if pool != 0 {
                let r = a64_pool(used, pool);
                if r < 0 {
                    err_at(o.loc, "goosecc: inline assembly needs too many registers");
                    return false;
                }
                used = used | ((1 as u64) << (r as! u64));
                op.reg = r as! i32;
            }
            if op.kind == 0 && op.reg < 32 && sz > 8 {
                err_at(o.loc, "goosecc: inline-asm operand wider than a general register");
                return false;
            }
            if op.kind == 0 && sz > 16 {
                err_at(o.loc, "goosecc: inline-asm operand wider than a register");
                return false;
            }
            asm_ops.push(op);
        }
    }
    let n_explicit = asm_ops.len;
    for k in n_explicit {
        let op = asm_ops[k];
        if op.out && op.inout {
            asm_ops.push(AsmOp { kind: op.kind, out: false, inout: false, tied: k as! i32, reg: op.reg, size: op.size, imm: 0, node: op.node, name: 0 });
        }
    }
    // substitute (GCC syntax: %N, %[name], %<modifier>N, %%, %=)
    asm_text.clear();
    var i = 0;
    while i < tmpl.len {
        let ch = tmpl[i];
        if ch != '%' { asm_text.push(ch); i++; continue; }
        if i + 1 >= tmpl.len { break; }
        let nx = tmpl[i + 1];
        if nx == '%' { asm_text.push('%'); i += 2; continue; }
        if nx == '=' { format(asm_text, a64_asm_count); i += 2; continue; }
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
            return false;
        }
        let op = asm_ops[num];
        if op.kind == 2 {
            if (md == 'w' || md == 'x') && op.imm == 0 { asm_text.append(if md == 'w' { "wzr" } else { "xzr" }); }
            else if md == 'n' { format(asm_text, 0 - op.imm); }
            else if md == 0 || md == 'c' || md == 'w' || md == 'x' { format(asm_text, op.imm); }
            else { err_at(nd.loc, str("goosecc: inline-asm modifier '", md, "' on an immediate")); return false; }
        } else if op.kind == 1 || md == 'a' {
            if md != 0 && md != 'a' { err_at(nd.loc, str("goosecc: inline-asm modifier '", md, "' on memory")); return false; }
            asm_text.append("[x");
            format(asm_text, op.reg);
            asm_text.push(']');
        } else if op.reg >= 32 {
            var pfx: u8 = 'v';
            if md == 'b' || md == 'h' || md == 's' || md == 'd' || md == 'q' { pfx = md; }
            else if md != 0 { err_at(nd.loc, str("goosecc: inline-asm modifier '", md, "' on an FP/SIMD register")); return false; }
            asm_text.push(pfx);
            format(asm_text, op.reg - 32);
        } else if op.reg == 31 {
            asm_text.append(if md == 'w' { "wsp" } else { "sp" });
        } else {
            if md == 'w' { asm_text.push('w'); }
            else if md == 0 || md == 'x' { asm_text.push('x'); }
            else { err_at(nd.loc, str("goosecc: inline-asm modifier '", md, "' on a general register")); return false; }
            format(asm_text, op.reg);
        }
        i = j;
    }
    a64_asm_count++;
    asm_code.clear();
    if !assemble_a64(asm_text[..]) {
        err_at(nd.loc, str("goosecc: cannot assemble inline asm '", asm_text, "'"));
        return false;
    }
    return true;
}

var a64_asm_count: i64 = 0;

// ---------------------------------------------------------------- operands

let AK_R = 1;     // general register: r (31 sp or zr), w 32/64, sp
let AK_F = 2;     // FP/SIMD scalar register: r, w 8..128
let AK_V = 3;     // vector register: r, w element bits, n lanes (0: an element [idx] or a bare vN)
let AK_I = 4;     // immediate: imm (fl: written as a decimal fraction fm * 10^fe)
let AK_S = 5;     // shift / extend: sk (0 lsl 1 lsr 2 asr 3 ror 4 msl, 8 + option for extends), sa (-1 none)
let AK_M = 6;     // memory: base, off, mode (0 offset, 1 pre-index, 2 register offset), rm, rmw, ext, ea
let AK_ID = 7;    // identifier: text s0..s1 of a_buf
let AK_L = 8;     // vector list: r first, n count, w element bits, ln lanes, idx (-1 none)

struct AO {
    k: i64 = 0, r: i64 = 0, w: i64 = 0, n: i64 = 0, idx: i64 = -1, sp: bool = false,
    imm: i64 = 0, fl: bool = false, fm: i64 = 0, fe: i64 = 0,
    sk: i64 = 0, sa: i64 = -1,
    base: i64 = 0, off: i64 = 0, mode: i64 = 0, rm: i64 = 0, rmw: i64 = 0, ext: i64 = -1, ea: i64 = -1,
    s0: i64 = 0, s1: i64 = 0, ln: i64 = 0,
}

var a_buf: u8[>..] = [];
var a_ops: AO[>..<] = [];
var a_lab: u32[>..<] = [];
var a_lpc: i64[>..<] = [];
var a_pc: i64 = 0;
var a_pass: i64 = 0;

fn a_dec(s: const u8[:]) -> i64 {
    if s.len == 0 || s.len > 9 { return -1; }
    var v: i64 = 0;
    for c in s {
        if c < '0' || c > '9' { return -1; }
        v = v * 10 + (c - '0') as i64;
    }
    return v;
}
fn a_space(c: u8) -> bool { c == ' ' || c == '\t' || c == '\r' || c == '\n' }
fn a_trim(s0: i64, s1: i64) -> i64, i64 {
    var a = s0;
    var b = s1;
    while a < b && a_space(a_buf[a]) { a++; }
    while b > a && a_space(a_buf[b - 1]) { b--; }
    return a, b;
}

// general register name
fn a_gpr(s: const u8[:]) -> i64, i64, bool {
    if s == "sp" { return 31, 64, true; }
    if s == "wsp" { return 31, 32, true; }
    if s == "xzr" { return 31, 64, false; }
    if s == "wzr" { return 31, 32, false; }
    if s == "fp" { return 29, 64, false; }
    if s == "lr" { return 30, 64, false; }
    if s == "ip0" { return 16, 64, false; }
    if s == "ip1" { return 17, 64, false; }
    if s.len >= 2 && (s[0] == 'x' || s[0] == 'w') {
        let k = a_dec(s[1..]);
        if k >= 0 && k <= 30 { return k, if s[0] == 'x' { 64 } else { 32 }, false; }
    }
    return -1, 0, false;
}
fn a_fpr(s: const u8[:]) -> i64, i64 {
    if s.len < 2 { return -1, 0; }
    let k = a_dec(s[1..]);
    if k < 0 || k > 31 { return -1, 0; }
    let c = s[0];
    if c == 'b' { return k, 8; }
    if c == 'h' { return k, 16; }
    if c == 's' { return k, 32; }
    if c == 'd' { return k, 64; }
    if c == 'q' { return k, 128; }
    return -1, 0;
}
fn a_eltbits(c: u8) -> i64 {
    if c == 'b' { return 8; }
    if c == 'h' { return 16; }
    if c == 's' { return 32; }
    if c == 'd' { return 64; }
    if c == 'q' { return 128; }
    return 0;
}
// vN[.T][[i]]: register, element bits, lanes, index; r < 0 if not a vector register
fn a_vreg(s: const u8[:]) -> i64, i64, i64, i64 {
    if s.len < 2 || s[0] != 'v' { return -1, 0, 0, -1; }
    var i = 1;
    while i < s.len && s[i] >= '0' && s[i] <= '9' { i++; }
    let k = a_dec(s[1..i]);
    if k < 0 || k > 31 { return -1, 0, 0, -1; }
    if i == s.len { return k, 0, 0, -1; }
    if s[i] != '.' { return -1, 0, 0, -1; }
    i++;
    var j = i;
    while j < s.len && s[j] >= '0' && s[j] <= '9' { j++; }
    var lanes: i64 = 0;
    if j > i { lanes = a_dec(s[i..j]); }
    if j >= s.len { return -1, 0, 0, -1; }
    let w = a_eltbits(s[j]);
    if w == 0 { return -1, 0, 0, -1; }
    j++;
    var idx: i64 = -1;
    if j < s.len {
        if s[j] != '[' || s[s.len - 1] != ']' { return -1, 0, 0, -1; }
        idx = a_dec(s[j + 1..s.len - 1]);
        if idx < 0 { return -1, 0, 0, -1; }
        if lanes != 0 && !(lanes == 4 && w == 8) { return -1, 0, 0, -1; }
        lanes = 0;
    } else if lanes == 0 {
        return -1, 0, 0, -1;
    } else if lanes * w != 64 && lanes * w != 128 && !(lanes == 2 && w == 16) && !(lanes == 4 && w == 8) {
        return -1, 0, 0, -1;
    }
    return k, w, lanes, idx;
}

// an integer: [#][-]decimal / 0x hex; or a decimal fraction (fl)
fn a_number(s0: const u8[:]) -> bool, i64, bool, i64, i64 {
    var s = s0;
    if s.len > 0 && s[0] == '#' { s = s[1..]; }
    while s.len > 0 && a_space(s[0]) { s = s[1..]; }
    var neg = false;
    if s.len > 0 && (s[0] == '-' || s[0] == '+') { neg = s[0] == '-'; s = s[1..]; }
    if s.len == 0 { return false, 0, false, 0, 0; }
    if s.len > 2 && s[0] == '0' && (s[1] == 'x' || s[1] == 'X') {
        var v: u64 = 0;
        for c in s[2..] {
            var d: u64 = 0;
            if c >= '0' && c <= '9' { d = (c - '0') as u64; }
            else if c >= 'a' && c <= 'f' { d = (c - 'a') as u64 + 10; }
            else { return false, 0, false, 0, 0; }
            v = v * 16 + d;
        }
        let r = v as! i64;
        return true, if neg { 0 - r } else { r }, false, 0, 0;
    }
    var m: i64 = 0;
    var e: i64 = 0;
    var frac = false;
    var dot = false;
    var digits = 0;
    var i = 0;
    while i < s.len {
        let c = s[i];
        if c >= '0' && c <= '9' {
            if m < 100000000000000000 { m = m * 10 + (c - '0') as i64; if dot { e--; } }
            else if !dot { e++; }
            digits++;
        } else if c == '.' && !dot {
            dot = true;
            frac = true;
        } else if c == 'e' && digits > 0 {
            var j = i + 1;
            var en = false;
            if j < s.len && (s[j] == '-' || s[j] == '+') { en = s[j] == '-'; j++; }
            let x = a_dec(s[j..]);
            if x < 0 { return false, 0, false, 0, 0; }
            e += if en { 0 - x } else { x };
            frac = true;
            break;
        } else {
            return false, 0, false, 0, 0;
        }
        i++;
    }
    if digits == 0 { return false, 0, false, 0, 0; }
    if neg { m = 0 - m; }
    if frac { return true, 0, true, m, e; }
    return true, m, false, 0, 0;
}

let A_SHIFTS = ["lsl", "lsr", "asr", "ror", "msl"];
let A_EXTS = ["uxtb", "uxth", "uxtw", "uxtx", "sxtb", "sxth", "sxtw", "sxtx"];

// shift / extend: kind, amount (-1 none); kind < 0 if not one
fn a_shift(s: const u8[:]) -> i64, i64 {
    var k: i64 = -1;
    var l = 0;
    for nm, j in A_SHIFTS { if starts_with(s, nm) { k = j; l = 3; } }
    for nm, j in A_EXTS { if starts_with(s, nm) { k = 8 + j; l = 4; } }
    if k < 0 { return -1, -1; }
    var t = s[l..];
    if t.len > 0 && !a_space(t[0]) && t[0] != '#' { return -1, -1; }
    while t.len > 0 && a_space(t[0]) { t = t[1..]; }
    if t.len == 0 { return k, -1; }
    let ok, v, fl, fm, fe = a_number(t);
    if !ok || fl || v < 0 { return -1, -1; }
    return k, v;
}

fn a_parse_mem(s0: i64, s1: i64) -> bool {
    // a_buf[s0] == '['
    var e = s1;
    var o = AO { k: AK_M };
    if a_buf[e - 1] == '!' { o.mode = 1; e--; while e > s0 && a_space(a_buf[e - 1]) { e--; } }
    if a_buf[e - 1] != ']' { return false; }
    // fields between [ and ]
    var f0: i64[3] = [0; 3];
    var f1: i64[3] = [0; 3];
    var nf = 0;
    var st = s0 + 1;
    var i = s0 + 1;
    while i <= e - 1 {
        if i == e - 1 || a_buf[i] == ',' {
            if nf >= 3 { return false; }
            let a, b = a_trim(st, i);
            f0[nf] = a;
            f1[nf] = b;
            nf++;
            st = i + 1;
        }
        i++;
    }
    let br, bw, bsp = a_gpr(a_buf[f0[0]..f1[0]]);
    if br < 0 || bw != 64 || (br == 31 && !bsp) { return false; }
    o.base = br;
    if nf >= 2 {
        let t = a_buf[f0[1]..f1[1]];
        let rr, rw, rsp = a_gpr(t);
        if rr >= 0 {
            if rsp || o.mode == 1 { return false; }
            o.mode = 2;
            o.rm = rr;
            o.rmw = rw;
            if nf == 3 {
                let k, a = a_shift(a_buf[f0[2]..f1[2]]);
                if k < 0 { return false; }
                o.ext = k;
                o.ea = a;
            }
        } else {
            if nf == 3 { return false; }
            let ok, v, fl, fm, fe = a_number(t);
            if !ok || fl { return false; }
            o.off = v;
        }
    } else if o.mode == 1 {
        return false;
    }
    a_ops.push(o);
    return true;
}

fn a_parse_list(s0: i64, s1: i64) -> bool {
    var e = s1;
    var o = AO { k: AK_L };
    if a_buf[e - 1] == ']' {
        var j = e - 1;
        while j > s0 && a_buf[j] != '[' { j--; }
        o.idx = a_dec(a_buf[j + 1..e - 1]);
        if o.idx < 0 { return false; }
        e = j;
        while e > s0 && a_space(a_buf[e - 1]) { e--; }
    }
    if a_buf[e - 1] != '}' { return false; }
    var st = s0 + 1;
    var i = s0 + 1;
    var cnt: i64 = 0;
    var last: i64 = -1;
    var range = false;
    while i <= e - 1 {
        if i == e - 1 || a_buf[i] == ',' || a_buf[i] == '-' {
            let a, b = a_trim(st, i);
            let r, w, n, idx = a_vreg(a_buf[a..b]);
            if r < 0 || idx >= 0 { return false; }
            if cnt == 0 {
                o.r = r; o.w = w; o.ln = n;
            } else {
                if w != o.w || n != o.ln { return false; }
                if range {
                    let c = (r - last + 32) % 32;
                    if c == 0 { return false; }
                    cnt += c - 1;
                } else if r != (last + 1) % 32 {
                    return false;
                }
            }
            cnt++;
            last = r;
            range = i < e - 1 && a_buf[i] == '-';
            st = i + 1;
        }
        i++;
    }
    if cnt < 1 || cnt > 4 { return false; }
    if o.idx >= 0 { if o.ln != 0 { return false; } } else if o.ln == 0 { return false; }
    o.n = cnt;
    a_ops.push(o);
    return true;
}

fn a_parse_op(s0: i64, s1: i64) -> bool {
    let a, b = a_trim(s0, s1);
    if a == b { return false; }
    let s = a_buf[a..b];
    if s[0] == '[' { return a_parse_mem(a, b); }
    if s[0] == '{' { return a_parse_list(a, b); }
    let r, w, sp = a_gpr(s);
    if r >= 0 { a_ops.push(AO { k: AK_R, r: r, w: w, sp: sp }); return true; }
    let fr, fw = a_fpr(s);
    if fr >= 0 { a_ops.push(AO { k: AK_F, r: fr, w: fw }); return true; }
    let vr, vw, vn, vi = a_vreg(s);
    if vr >= 0 { a_ops.push(AO { k: AK_V, r: vr, w: vw, n: vn, idx: vi }); return true; }
    let sk, sa = a_shift(s);
    if sk >= 0 { a_ops.push(AO { k: AK_S, sk: sk, sa: sa }); return true; }
    if s[0] == '#' || s[0] == '-' || (s[0] >= '0' && s[0] <= '9') {
        let ok, v, fl, fm, fe = a_number(s);
        if !ok {
            if s[0] >= '0' && s[0] <= '9' { a_ops.push(AO { k: AK_ID, s0: a, s1: b }); return true; }   // 1b / 1f
            return false;
        }
        a_ops.push(AO { k: AK_I, imm: v, fl: fl, fm: fm, fe: fe });
        return true;
    }
    a_ops.push(AO { k: AK_ID, s0: a, s1: b });
    return true;
}

// ---------------------------------------------------------------- output

fn a_word(w: i64) {
    let x = w as! u64;
    for k in 4 { asm_code.push(((x >> (8 * k as! u64)) & 255) as! u8); }
    a_pc += 4;
}

fn a_label(o: AO) -> bool, i64 {
    if o.k != AK_ID { return false, 0; }
    let s = a_buf[o.s0..o.s1];
    if s.len >= 2 && (s[s.len - 1] == 'b' || s[s.len - 1] == 'f') && a_dec(s[..s.len - 1]) >= 0 {
        let nm = intern(s[..s.len - 1]);
        if s[s.len - 1] == 'b' {
            var best: i64 = -1;
            for l, k in a_lab { if l == nm && a_lpc[k] <= a_pc { best = a_lpc[k]; } }
            if best >= 0 { return true, best - a_pc; }
        } else {
            for l, k in a_lab { if l == nm && a_lpc[k] > a_pc { return true, a_lpc[k] - a_pc; } }
        }
    } else {
        let nm = intern(s);
        for l, k in a_lab { if l == nm { return true, a_lpc[k] - a_pc; } }
    }
    if a_pass == 0 { return true, 0; }
    return false, 0;
}

let A_CONDS = ["eq", "ne", "cs", "cc", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le", "al", "nv"];
fn a_cond_of(s: const u8[:]) -> i64 {
    if s == "hs" { return 2; }
    if s == "lo" { return 3; }
    for c, k in A_CONDS { if s == c { return k; } }
    return -1;
}
fn a_cond(o: AO) -> i64 { if o.k != AK_ID { -1 } else { a_cond_of(a_buf[o.s0..o.s1]) } }

// ---------------------------------------------------------------- immediates

fn a_mask(w: i64) -> u64 { if w >= 64 { 0xFFFFFFFFFFFFFFFF } else { ((1 as u64) << (w as! u64)) - 1 } }
fn a_rotr(x: u64, r: i64, e: i64) -> u64 {
    if r == 0 { return x; }
    return ((x >> (r as! u64)) | (x << ((e - r) as! u64))) & a_mask(e);
}
fn a_popc(x: u64) -> i64 {
    var n: i64 = 0;
    var y = x;
    while y != 0 { n += (y & 1) as! i64; y = y >> 1; }
    return n;
}
// the logical immediate (N, immr, imms) of v in a w-bit register
fn a_bitmask(v0: i64, w: i64) -> bool, i64, i64, i64 {
    var v = v0 as! u64;
    if w == 32 {
        if v0 < -2147483648 || v0 > 4294967295 { return false, 0, 0, 0; }
        v = v & 0xFFFFFFFF;
        v = v | (v << 32);
    }
    if v == 0 || v == 0xFFFFFFFFFFFFFFFF { return false, 0, 0, 0; }
    var e: i64 = 64;
    while e > 2 {
        let h = e / 2;
        let m = a_mask(h);
        if v & m != (v >> (h as! u64)) & m { break; }
        e = h;
    }
    if w == 32 && e == 64 { return false, 0, 0, 0; }
    let elt = v & a_mask(e);
    let ones = a_popc(elt);
    let pat = a_mask(ones);
    for r in e {
        if a_rotr(pat, r, e) == elt {
            var imms: i64 = ones - 1;
            if e == 16 { imms = imms | 0x20; }
            else if e == 8 { imms = imms | 0x30; }
            else if e == 4 { imms = imms | 0x38; }
            else if e == 2 { imms = imms | 0x3C; }
            return true, if e == 64 { 1 } else { 0 }, r, imms;
        }
    }
    return false, 0, 0, 0;
}
// mov Rd, #v as one instruction: kind (0 movz, 1 movn, 2 orr; -1 none), the operand bits
fn a_mov_imm(v0: i64, w: i64) -> i64, i64 {
    let v = (v0 as! u64) & a_mask(w);
    for hw in w / 16 {
        let sh = (16 * hw) as! u64;
        if v & ~((0xFFFF as u64) << sh) == 0 { return 0, (hw << 16) | ((v >> sh) as! i64); }
    }
    let nv = ~v & a_mask(w);
    for hw in w / 16 {
        let sh = (16 * hw) as! u64;
        if nv & ~((0xFFFF as u64) << sh) == 0 { return 1, (hw << 16) | ((nv >> sh) as! i64); }
    }
    let ok, n, r, s = a_bitmask(v as! i64, w);
    if ok { return 2, (n << 12) | (r << 6) | s; }
    return -1, 0;
}
// the 8-bit FP immediate of fraction fm * 10^fe (or integer), or -1
fn a_fp8(o: AO) -> i64 {
    var m = o.imm;
    var e: i64 = 0;
    if o.fl { m = o.fm; e = o.fe; }
    var neg = false;
    if m < 0 { neg = true; m = 0 - m; }
    if m == 0 { return -1; }
    // n = value * 128 must be an integer
    var n = m * 128;
    while e > 0 { if n > 100000000000000 { return -1; } n = n * 10; e--; }
    while e < 0 { if n % 10 != 0 { return -1; } n = n / 10; e++; }
    for k in 8 {
        // (16 + mant) << k == n, exponent k - 7 + 4
        let q = n >> (k as! u64);
        if q << (k as! u64) == n && q >= 16 && q <= 31 {
            let ex = k - 3;   // value = q/16 * 2^(k-3)
            return (if neg { 128 } else { 0 }) | (((ex - 1) & 7) << 4) | (q - 16);
        }
    }
    return -1;
}
fn a_is_zero_imm(o: AO) -> bool { o.k == AK_I && ((o.fl && o.fm == 0) || (!o.fl && o.imm == 0)) }

// ---------------------------------------------------------------- statement

fn a_lower(c: u8) -> u8 { if c >= 'A' && c <= 'Z' { c + 32 } else { c } }

fn assemble_a64(text: const u8[:]) -> bool {
    a_lab.clear();
    a_lpc.clear();
    for pass in 2 {
        a_pass = pass;
        a_pc = 0;
        asm_code.clear();
        var i = 0;
        while i < text.len {
            // one statement: up to '\n' or ';', without // and /* */ comments
            a_buf.clear();
            while i < text.len && text[i] != '\n' && text[i] != ';' {
                if text[i] == '/' && i + 1 < text.len && text[i + 1] == '/' {
                    while i < text.len && text[i] != '\n' { i++; }
                    break;
                }
                if text[i] == '/' && i + 1 < text.len && text[i + 1] == '*' {
                    i += 2;
                    while i + 1 < text.len && !(text[i] == '*' && text[i + 1] == '/') { i++; }
                    i += 2;
                    a_buf.push(' ');
                    continue;
                }
                a_buf.push(a_lower(text[i]));
                i++;
            }
            i++;
            if !a_stmt(pass) { return false; }
        }
    }
    return true;
}

fn a_ident_char(c: u8) -> bool { (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '_' || c == '.' || c == '$' }

fn a_stmt(pass: i64) -> bool {
    var s0, s1 = a_trim(0, a_buf.len);
    // labels
    loop {
        var j = s0;
        while j < s1 && a_ident_char(a_buf[j]) { j++; }
        if j > s0 && j < s1 && a_buf[j] == ':' {
            if pass == 0 { a_lab.push(intern(a_buf[s0..j])); a_lpc.push(a_pc); }
            s0, s1 = a_trim(j + 1, s1);
            continue;
        }
        break;
    }
    if s0 == s1 { return true; }
    var j = s0;
    while j < s1 && !a_space(a_buf[j]) { j++; }
    let m0 = s0;
    let m1 = j;
    a_ops.clear();
    let o0, o1 = a_trim(j, s1);
    if o0 < o1 {
        var depth = 0;
        var st = o0;
        var k = o0;
        while k <= o1 {
            if k == o1 || (a_buf[k] == ',' && depth == 0) {
                if !a_parse_op(st, k) { return false; }
                st = k + 1;
            } else if a_buf[k] == '[' || a_buf[k] == '{' {
                depth++;
            } else if a_buf[k] == ']' || a_buf[k] == '}' {
                depth--;
            }
            k++;
        }
    }
    let mn = a_buf[m0..m1];
    if mn[0] == '.' { return a_directive(mn); }
    return a_insn(mn);
}

fn a_directive(mn: const u8[:]) -> bool {
    if mn == ".inst" || mn == ".word" || mn == ".long" || mn == ".4byte" {
        if a_ops.len == 0 { return false; }
        for o in a_ops {
            if o.k != AK_I || o.fl || o.imm < -2147483648 || o.imm > 4294967295 { return false; }
            a_word(o.imm & 0xFFFFFFFF);
        }
        return true;
    }
    if mn == ".arch" || mn == ".arch_extension" || mn == ".cpu" { return true; }
    return false;
}

// ---------------------------------------------------------------- checks

fn nops_is(n: i64) -> bool { a_ops.len == n }
fn isR(k: i64) -> bool { k < a_ops.len && a_ops[k].k == AK_R }
fn isF(k: i64) -> bool { k < a_ops.len && a_ops[k].k == AK_F }
fn isV(k: i64) -> bool { k < a_ops.len && a_ops[k].k == AK_V && a_ops[k].n > 0 }
fn isE(k: i64) -> bool { k < a_ops.len && a_ops[k].k == AK_V && a_ops[k].n == 0 && a_ops[k].idx >= 0 }
fn isI(k: i64) -> bool { k < a_ops.len && a_ops[k].k == AK_I && !a_ops[k].fl }
fn isS(k: i64) -> bool { k < a_ops.len && a_ops[k].k == AK_S }
fn isM(k: i64) -> bool { k < a_ops.len && a_ops[k].k == AK_M }
fn isL(k: i64) -> bool { k < a_ops.len && a_ops[k].k == AK_L }
fn rr(k: i64) -> i64 { a_ops[k].r }
// a general register that is not sp (zr allowed)
fn isRZ(k: i64) -> bool { isR(k) && !a_ops[k].sp }
fn sf(k: i64) -> i64 { if a_ops[k].w == 64 { 1 } else { 0 } }
fn same_w(a: i64, b: i64) -> bool { a_ops[a].w == a_ops[b].w }
fn vsize(w: i64) -> i64 { if w == 8 { 0 } else if w == 16 { 1 } else if w == 32 { 2 } else { 3 } }
fn vq(k: i64) -> i64 { if a_ops[k].w * a_ops[k].n == 128 { 1 } else { 0 } }
fn same_arr(a: i64, b: i64) -> bool { a_ops[a].w == a_ops[b].w && a_ops[a].n == a_ops[b].n }
fn imm(k: i64) -> i64 { a_ops[k].imm }
// a zero register of width w at operand position k
fn ins_zr(k: i64, w: i64) {
    a_ops.push(AO { k: AK_R, r: 31, w: w });
    var i = a_ops.len - 1;
    while i > k { a_ops[i] = a_ops[i - 1]; i--; }
    a_ops[k] = AO { k: AK_R, r: 31, w: w };
}

fn ends_with2(s: const u8[:]) -> bool { s.len > 0 && s[s.len - 1] == '2' }

// ---------------------------------------------------------------- integer

// add / sub / adds / subs (op 0 add 1 sub)
fn e_addsub(op0: i64, S: i64) -> bool {
    if a_ops.len < 3 || a_ops.len > 4 || !isR(0) || !isR(1) { return false; }
    if !same_w(0, 1) { return false; }
    var op = op0;
    let f = sf(0);
    let d = a_ops[0];
    let n = a_ops[1];
    if isI(2) {
        var v = imm(2);
        var sh: i64 = 0;
        if a_ops.len == 4 {
            if !isS(3) || a_ops[3].sk != 0 || (a_ops[3].sa != 0 && a_ops[3].sa != 12) { return false; }
            if a_ops[3].sa == 12 { sh = 1; }
        } else {
            if v < 0 { op = 1 - op; v = 0 - v; }
            if v > 4095 && v & 0xFFF == 0 && (v >> 12) <= 4095 { sh = 1; v = v >> 12; }
        }
        if v < 0 || v > 4095 { return false; }
        if n.r == 31 && !n.sp { return false; }
        if S == 1 && d.sp { return false; }
        if S == 0 && d.r == 31 && !d.sp { return false; }
        a_word(0x11000000 | (f << 31) | (op << 30) | (S << 29) | (sh << 22) | (v << 10) | (n.r << 5) | d.r);
        return true;
    }
    if !isRZ(2) { return false; }
    let m = a_ops[2];
    let ext = (a_ops.len == 4 && isS(3) && a_ops[3].sk >= 8) || (S == 0 && d.sp) || n.sp;
    if ext {
        var opt: i64 = if f == 1 { 3 } else { 2 };
        var amt: i64 = 0;
        if a_ops.len == 4 {
            if !isS(3) { return false; }
            let k = a_ops[3].sk;
            if k == 0 {
                if !(d.sp || n.sp) { return false; }
            } else if k >= 8 {
                opt = k - 8;
            } else {
                return false;
            }
            if a_ops[3].sa > 0 { amt = a_ops[3].sa; }
        }
        if amt > 4 { return false; }
        if n.r == 31 && !n.sp { return false; }
        if S == 1 && d.sp { return false; }
        if S == 0 && d.r == 31 && !d.sp { return false; }
        if f == 1 && (opt & 3) == 3 { if m.w != 64 { return false; } } else if m.w != 32 { return false; }
        a_word(0x0B200000 | (f << 31) | (op << 30) | (S << 29) | (m.r << 16) | (opt << 13) | (amt << 10) | (n.r << 5) | d.r);
        return true;
    }
    if d.sp || !same_w(0, 2) { return false; }
    var sk: i64 = 0;
    var sa: i64 = 0;
    if a_ops.len == 4 {
        if !isS(3) || a_ops[3].sk > 2 { return false; }
        sk = a_ops[3].sk;
        sa = if a_ops[3].sa < 0 { 0 } else { a_ops[3].sa };
    }
    if sa >= d.w { return false; }
    a_word(0x0B000000 | (f << 31) | (op << 30) | (S << 29) | (sk << 22) | (m.r << 16) | (sa << 10) | (n.r << 5) | d.r);
    return true;
}

// and / orr / eor / ands (opc 0..3), N: bic / orn / eon / bics
fn e_logic(opc: i64, N: i64) -> bool {
    if a_ops.len < 3 || a_ops.len > 4 || !isR(0) || !isRZ(1) || !same_w(0, 1) { return false; }
    let f = sf(0);
    let d = a_ops[0];
    if isI(2) {
        if N != 0 || a_ops.len != 3 { return false; }
        if d.r == 31 && !d.sp && opc != 3 { return false; }
        if d.sp && opc == 3 { return false; }
        let ok, nn, r, s = a_bitmask(imm(2), d.w);
        if !ok { return false; }
        a_word(0x12000000 | (f << 31) | (opc << 29) | (nn << 22) | (r << 16) | (s << 10) | (rr(1) << 5) | d.r);
        return true;
    }
    if d.sp || !isRZ(2) || !same_w(0, 2) { return false; }
    var sk: i64 = 0;
    var sa: i64 = 0;
    if a_ops.len == 4 {
        if !isS(3) || a_ops[3].sk > 3 { return false; }
        sk = a_ops[3].sk;
        sa = if a_ops[3].sa < 0 { 0 } else { a_ops[3].sa };
    }
    if sa >= d.w { return false; }
    a_word(0x0A000000 | (f << 31) | (opc << 29) | (sk << 22) | (N << 21) | (rr(2) << 16) | (sa << 10) | (rr(1) << 5) | d.r);
    return true;
}

fn bfm(opc: i64, d: i64, n: i64, immr: i64, imms: i64) -> bool {
    let w = a_ops[d].w;
    if immr < 0 || immr >= w || imms < 0 || imms >= w { return false; }
    let f = if w == 64 { 1 } else { 0 };
    a_word(0x13000000 | (f << 31) | (opc << 29) | (f << 22) | (immr << 16) | (imms << 10) | (rr(n) << 5) | rr(d));
    return true;
}

fn e_shift(mn: const u8[:]) -> bool {
    if !nops_is(3) || !isRZ(0) || !isRZ(1) || !same_w(0, 1) { return false; }
    let w = a_ops[0].w;
    let f = sf(0);
    if isRZ(2) {
        if !same_w(0, 2) { return false; }
        var o: i64 = 8;
        if mn == "lsr" { o = 9; } else if mn == "asr" { o = 10; } else if mn == "ror" { o = 11; }
        a_word(0x1AC00000 | (f << 31) | (rr(2) << 16) | (o << 10) | (rr(1) << 5) | rr(0));
        return true;
    }
    if !isI(2) { return false; }
    let s = imm(2);
    if s < 0 || s >= w { return false; }
    if mn == "lsl" { return bfm(2, 0, 1, (w - s) % w, w - 1 - s); }
    if mn == "lsr" { return bfm(2, 0, 1, s, w - 1); }
    if mn == "asr" { return bfm(0, 0, 1, s, w - 1); }
    // ror: extr Rd, Rn, Rn, #s
    a_word(0x13800000 | (f << 31) | (f << 22) | (rr(1) << 16) | (s << 10) | (rr(1) << 5) | rr(0));
    return true;
}

fn e_bitfield(mn: const u8[:]) -> bool {
    if !nops_is(4) || !isRZ(0) || !isRZ(1) || !same_w(0, 1) || !isI(2) || !isI(3) { return false; }
    let w = a_ops[0].w;
    let a = imm(2);
    let b = imm(3);
    if mn == "ubfm" { return bfm(2, 0, 1, a, b); }
    if mn == "sbfm" { return bfm(0, 0, 1, a, b); }
    if mn == "bfm" { return bfm(1, 0, 1, a, b); }
    if a < 0 || b < 1 || a + b > w { return false; }
    if mn == "ubfx" { return bfm(2, 0, 1, a, a + b - 1); }
    if mn == "sbfx" { return bfm(0, 0, 1, a, a + b - 1); }
    if mn == "bfxil" { return bfm(1, 0, 1, a, a + b - 1); }
    if mn == "ubfiz" { return bfm(2, 0, 1, (w - a) % w, b - 1); }
    if mn == "sbfiz" { return bfm(0, 0, 1, (w - a) % w, b - 1); }
    if mn == "bfi" { return bfm(1, 0, 1, (w - a) % w, b - 1); }
    return false;
}

fn e_mov(mn: const u8[:]) -> bool {
    if !nops_is(2) { return false; }
    if isR(0) && isR(1) {
        if !same_w(0, 1) { return false; }
        if a_ops[0].sp || a_ops[1].sp {
            a_word(0x11000000 | (sf(0) << 31) | (rr(1) << 5) | rr(0));
            return true;
        }
        a_word(0x2A0003E0 | (sf(0) << 31) | (rr(1) << 16) | rr(0));
        return true;
    }
    if isR(0) && isI(1) {
        let w = a_ops[0].w;
        let v = imm(1);
        if w == 32 && (v < -2147483648 || v > 4294967295) { return false; }
        let k, x = a_mov_imm(v, w);
        let f = sf(0);
        let d = a_ops[0];
        if k == 0 || k == 1 {
            if d.sp { return false; }
            a_word((if k == 0 { 0x52800000 } else { 0x12800000 }) | (f << 31) | ((x >> 16) << 21) | ((x & 0xFFFF) << 5) | d.r);
            return true;
        }
        if k == 2 {
            if d.r == 31 && !d.sp { return false; }
            a_word(0x320003E0 | (f << 31) | (x << 10) | d.r);
            return true;
        }
        return false;
    }
    if isV(0) && isV(1) {
        if !same_arr(0, 1) || a_ops[0].w != 8 { return false; }
        a_word(0x0EA01C00 | (vq(0) << 30) | (rr(1) << 16) | (rr(1) << 5) | rr(0));
        return true;
    }
    if isE(0) && (isRZ(1) || isE(1)) { return e_ins(); }
    if isR(0) && isE(1) {
        if !((a_ops[0].w == 32 && a_ops[1].w == 32) || (a_ops[0].w == 64 && a_ops[1].w == 64)) { return false; }
        return e_umov(false);
    }
    if isF(0) && isE(1) { return e_dup(); }
    return false;
}

fn e_movw(opc: i64) -> bool {
    if a_ops.len < 2 || a_ops.len > 3 || !isRZ(0) || !isI(1) { return false; }
    let v = imm(1);
    if v < 0 || v > 65535 { return false; }
    var hw: i64 = 0;
    if a_ops.len == 3 {
        if !isS(2) || a_ops[2].sk != 0 || a_ops[2].sa < 0 || a_ops[2].sa % 16 != 0 { return false; }
        hw = a_ops[2].sa / 16;
    }
    if hw * 16 >= a_ops[0].w { return false; }
    a_word(0x12800000 | (sf(0) << 31) | (opc << 29) | (hw << 21) | (v << 5) | rr(0));
    return true;
}

// data processing, 3 source: op31, o0; Ra (-1: zr)
fn e_dp3(op31: i64, o0: i64, has_a: bool, long: bool) -> bool {
    if !nops_is(if has_a { 4 } else { 3 }) || !isRZ(0) || !isRZ(1) || !isRZ(2) { return false; }
    if long {
        if a_ops[0].w != 64 || a_ops[1].w != 32 || a_ops[2].w != 32 { return false; }
    } else if !same_w(0, 1) || !same_w(0, 2) {
        return false;
    }
    var ra: i64 = 31;
    if has_a {
        if !isRZ(3) || a_ops[3].w != a_ops[0].w { return false; }
        ra = rr(3);
    }
    a_word(0x1B000000 | (sf(0) << 31) | (op31 << 21) | (rr(2) << 16) | (o0 << 15) | (ra << 10) | (rr(1) << 5) | rr(0));
    return true;
}

fn e_dp2(o: i64) -> bool {
    if !nops_is(3) || !isRZ(0) || !isRZ(1) || !isRZ(2) || !same_w(0, 1) || !same_w(0, 2) { return false; }
    a_word(0x1AC00000 | (sf(0) << 31) | (rr(2) << 16) | (o << 10) | (rr(1) << 5) | rr(0));
    return true;
}

fn e_dp1(o: i64) -> bool {
    if !nops_is(2) || !isRZ(0) || !isRZ(1) || !same_w(0, 1) { return false; }
    a_word(0x5AC00000 | (sf(0) << 31) | (o << 10) | (rr(1) << 5) | rr(0));
    return true;
}

fn e_csel(op: i64, o2: i64) -> bool {
    if !nops_is(4) || !isRZ(0) || !isRZ(1) || !isRZ(2) || !same_w(0, 1) || !same_w(0, 2) { return false; }
    let c = a_cond(a_ops[3]);
    if c < 0 { return false; }
    a_word(0x1A800000 | (sf(0) << 31) | (op << 30) | (rr(2) << 16) | (c << 12) | (o2 << 10) | (rr(1) << 5) | rr(0));
    return true;
}

fn e_ccmp(op: i64) -> bool {
    if !nops_is(4) || !isRZ(0) || !isI(2) { return false; }
    let c = a_cond(a_ops[3]);
    let nzcv = imm(2);
    if c < 0 || nzcv < 0 || nzcv > 15 { return false; }
    if isI(1) {
        let v = imm(1);
        if v < 0 || v > 31 { return false; }
        a_word(0x3A400800 | (sf(0) << 31) | (op << 30) | (v << 16) | (c << 12) | (rr(0) << 5) | nzcv);
        return true;
    }
    if !isRZ(1) || !same_w(0, 1) { return false; }
    a_word(0x3A400000 | (sf(0) << 31) | (op << 30) | (rr(1) << 16) | (c << 12) | (rr(0) << 5) | nzcv);
    return true;
}

fn e_adc(op: i64, S: i64) -> bool {
    if !nops_is(3) || !isRZ(0) || !isRZ(1) || !isRZ(2) || !same_w(0, 1) || !same_w(0, 2) { return false; }
    a_word(0x1A000000 | (sf(0) << 31) | (op << 30) | (S << 29) | (rr(2) << 16) | (rr(1) << 5) | rr(0));
    return true;
}

fn e_ext(signed: bool, bits: i64) -> bool {
    if !nops_is(2) || !isRZ(0) || !isRZ(1) || a_ops[1].w != 32 { return false; }
    if !signed && a_ops[0].w != 32 { return false; }
    if bits == 32 && a_ops[0].w != 64 { return false; }
    return bfm(if signed { 0 } else { 2 }, 0, 1, 0, bits - 1);
}

fn e_crc(c: i64, sz: i64) -> bool {
    if !nops_is(3) || !isRZ(0) || !isRZ(1) || !isRZ(2) { return false; }
    if a_ops[0].w != 32 || a_ops[1].w != 32 || a_ops[2].w != (if sz == 3 { 64 } else { 32 }) { return false; }
    a_word(0x1AC04000 | ((if sz == 3 { 1 } else { 0 }) << 31) | (rr(2) << 16) | (c << 12) | (sz << 10) | (rr(1) << 5) | rr(0));
    return true;
}

// ---------------------------------------------------------------- branches, system

fn e_branch(mn: const u8[:]) -> bool {
    if mn == "b" || mn == "bl" {
        if !nops_is(1) { return false; }
        let ok, d = a_label(a_ops[0]);
        if !ok || d % 4 != 0 || d < -134217728 || d >= 134217728 { return false; }
        a_word((if mn == "b" { 0x14000000 } else { 0x94000000 }) | ((d >> 2) & 0x3FFFFFF));
        return true;
    }
    if mn.len > 2 && mn[0] == 'b' && mn[1] == '.' {
        let c = a_cond_of(mn[2..]);
        if c < 0 || !nops_is(1) { return false; }
        let ok, d = a_label(a_ops[0]);
        if !ok || d % 4 != 0 || d < -1048576 || d >= 1048576 { return false; }
        a_word(0x54000000 | (((d >> 2) & 0x7FFFF) << 5) | c);
        return true;
    }
    if mn == "cbz" || mn == "cbnz" {
        if !nops_is(2) || !isRZ(0) { return false; }
        let ok, d = a_label(a_ops[1]);
        if !ok || d % 4 != 0 || d < -1048576 || d >= 1048576 { return false; }
        a_word(0x34000000 | (sf(0) << 31) | ((if mn == "cbnz" { 1 } else { 0 }) << 24) | (((d >> 2) & 0x7FFFF) << 5) | rr(0));
        return true;
    }
    if mn == "tbz" || mn == "tbnz" {
        if !nops_is(3) || !isRZ(0) || !isI(1) { return false; }
        let b = imm(1);
        if b < 0 || b >= a_ops[0].w { return false; }
        let ok, d = a_label(a_ops[2]);
        if !ok || d % 4 != 0 || d < -32768 || d >= 32768 { return false; }
        a_word(0x36000000 | ((b >> 5) << 31) | ((if mn == "tbnz" { 1 } else { 0 }) << 24) | ((b & 31) << 19) | (((d >> 2) & 0x3FFF) << 5) | rr(0));
        return true;
    }
    if mn == "br" || mn == "blr" || mn == "ret" {
        var n: i64 = 30;
        if a_ops.len == 1 {
            if !isRZ(0) || a_ops[0].w != 64 { return false; }
            n = rr(0);
        } else if a_ops.len != 0 || mn != "ret" {
            return false;
        }
        let base = if mn == "br" { 0xD61F0000 } else if mn == "blr" { 0xD63F0000 } else { 0xD65F0000 };
        a_word(base | (n << 5));
        return true;
    }
    if mn == "adr" {
        if !nops_is(2) || !isRZ(0) || a_ops[0].w != 64 { return false; }
        let ok, d = a_label(a_ops[1]);
        if !ok || d < -1048576 || d >= 1048576 { return false; }
        a_word(0x10000000 | ((d & 3) << 29) | (((d >> 2) & 0x7FFFF) << 5) | rr(0));
        return true;
    }
    return false;
}

let A_BARRIERS = ["", "oshld", "oshst", "osh", "", "nshld", "nshst", "nsh", "", "ishld", "ishst", "ish", "", "ld", "st", "sy"];

fn a_barrier_opt() -> i64 {
    if a_ops.len == 0 { return 15; }
    if a_ops.len != 1 { return -1; }
    if isI(0) { return if imm(0) >= 0 && imm(0) <= 15 { imm(0) } else { -1 }; }
    if a_ops[0].k != AK_ID { return -1; }
    let s = a_buf[a_ops[0].s0..a_ops[0].s1];
    for b, k in A_BARRIERS { if b.len > 0 && s == b { return k; } }
    return -1;
}

let A_HINTS = ["nop", "yield", "wfe", "wfi", "sev", "sevl"];
let A_SYSREG_X = ["id_aa64pfr1_el1", "id_aa64isar2_el1", "id_aa64zfr0_el1", "id_aa64smfr0_el1", "id_aa64mmfr1_el1",
                  "id_aa64mmfr2_el1", "id_aa64dfr0_el1", "id_aa64dfr1_el1", "id_aa64afr0_el1", "id_aa64afr1_el1"];
let A_SYSREG_XENC: i64[10] = [0xC021, 0xC032, 0xC024, 0xC025, 0xC039, 0xC03A, 0xC028, 0xC029, 0xC02C, 0xC02D];

fn a_sysreg_enc(o: AO) -> i64 {
    if o.k != AK_ID { return -1; }
    let s = a_buf[o.s0..o.s1];
    for nm, k in A_SYSREG_X { if s == nm { return A_SYSREG_XENC[k]; } }
    let v = a64_sysreg(s);
    if v < 0 || v > 0xFFFF || (v >> 14) < 2 { return -1; }
    return v;
}

fn e_system(mn: const u8[:]) -> bool {
    for h, k in A_HINTS {
        if mn == h { if a_ops.len != 0 { return false; } a_word(0xD503201F | (k << 5)); return true; }
    }
    if mn == "hint" {
        if !nops_is(1) || !isI(0) || imm(0) < 0 || imm(0) > 127 { return false; }
        a_word(0xD503201F | (imm(0) << 5));
        return true;
    }
    if mn == "csdb" { if a_ops.len != 0 { return false; } a_word(0xD503229F); return true; }
    if mn == "sb" { if a_ops.len != 0 { return false; } a_word(0xD50330FF); return true; }
    if mn == "dmb" || mn == "dsb" || mn == "isb" || mn == "clrex" {
        var o: i64 = 15;
        if mn == "isb" || mn == "clrex" {
            if a_ops.len == 1 {
                if isI(0) && imm(0) >= 0 && imm(0) <= 15 { o = imm(0); }
                else if a_ops[0].k == AK_ID && a_buf[a_ops[0].s0..a_ops[0].s1] == "sy" && mn == "isb" { o = 15; }
                else { return false; }
            } else if a_ops.len != 0 {
                return false;
            }
        } else {
            if a_ops.len != 1 { return false; }
            o = a_barrier_opt();
        }
        if o < 0 { return false; }
        let base = if mn == "dmb" { 0xD50330BF } else if mn == "dsb" { 0xD503309F } else if mn == "isb" { 0xD50330DF } else { 0xD503305F };
        a_word(base | (o << 8));
        return true;
    }
    if mn == "brk" || mn == "svc" || mn == "hlt" || mn == "udf" {
        if !nops_is(1) || !isI(0) || imm(0) < 0 || imm(0) > 65535 { return false; }
        let base = if mn == "brk" { 0xD4200000 } else if mn == "svc" { 0xD4000001 } else if mn == "hlt" { 0xD4400000 } else { 0 };
        if mn == "udf" { a_word(imm(0)); } else { a_word(base | (imm(0) << 5)); }
        return true;
    }
    if mn == "mrs" {
        if !nops_is(2) || !isRZ(0) || a_ops[0].w != 64 { return false; }
        let e = a_sysreg_enc(a_ops[1]);
        if e < 0 { return false; }
        a_word(0xD5200000 | (e << 5) | rr(0));
        return true;
    }
    if mn == "msr" {
        if !nops_is(2) || !isRZ(1) || a_ops[1].w != 64 { return false; }
        let e = a_sysreg_enc(a_ops[0]);
        if e < 0 { return false; }
        a_word(0xD5000000 | (e << 5) | rr(1));
        return true;
    }
    if mn == "cfinv" { if a_ops.len != 0 { return false; } a_word(0xD500401F); return true; }
    return false;
}

// ---------------------------------------------------------------- loads and stores

// register class of a transfer register: (size, V, opc for a load); 0 store
fn a_rt_class(k: i64) -> bool, i64, i64 {
    let o = a_ops[k];
    if o.k == AK_R && !o.sp { return true, if o.w == 64 { 3 } else { 2 }, 0; }
    if o.k == AK_F { return true, vsize(o.w), 1; }
    return false, 0, 0;
}

// ldr / str family. size (0..3), V, opc, the scale (log2 bytes)
fn ldst(size: i64, V: i64, opc: i64, scale: i64, rt: i64, mi: i64, unscaled_only: bool) -> bool {
    let m = a_ops[mi];
    if !isM(mi) { return false; }
    let base = 0x38000000 | (size << 30) | (V << 26) | (opc << 22) | (m.base << 5) | rt;
    if a_ops.len == mi + 2 {
        // post-index
        if m.mode != 0 || m.off != 0 || !isI(mi + 1) || unscaled_only { return false; }
        let v = imm(mi + 1);
        if v < -256 || v > 255 { return false; }
        a_word(base | ((v & 0x1FF) << 12) | (1 << 10));
        return true;
    }
    if a_ops.len != mi + 1 { return false; }
    if m.mode == 1 {
        if unscaled_only || m.off < -256 || m.off > 255 { return false; }
        a_word(base | ((m.off & 0x1FF) << 12) | (3 << 10));
        return true;
    }
    if m.mode == 2 {
        if unscaled_only { return false; }
        var opt: i64 = 3;
        var amt: i64 = 0;
        if m.ext >= 0 {
            if m.ext == 0 { opt = 3; }
            else if m.ext == 8 + 2 || m.ext == 8 + 3 || m.ext == 8 + 6 || m.ext == 8 + 7 { opt = m.ext - 8; }
            else { return false; }
            if m.ea > 0 {
                if m.ea != scale { return false; }
                amt = 1;
            } else if m.ea == 0 {
                // "lsl #0" / "uxtw #0": S = 1 for a byte access (as LLVM)
                if scale == 0 { amt = 1; }
            }
        }
        if (opt & 1) == 1 { if m.rmw != 64 { return false; } } else if m.rmw != 32 { return false; }
        a_word(base | 0x200800 | (m.rm << 16) | (opt << 13) | (amt << 12));
        return true;
    }
    let off = m.off;
    if !unscaled_only && off >= 0 && off % (1 << (scale as! u64)) == 0 && (off >> (scale as! u64)) <= 4095 {
        a_word(0x39000000 | (size << 30) | (V << 26) | (opc << 22) | ((off >> (scale as! u64)) << 10) | (m.base << 5) | rt);
        return true;
    }
    if off >= -256 && off <= 255 {
        a_word(base | ((off & 0x1FF) << 12));
        return true;
    }
    return false;
}

fn e_ldst(mn0: const u8[:]) -> bool {
    var mn = mn0;
    var unscaled = false;
    if starts_with(mn, "ldur") || starts_with(mn, "stur") {
        unscaled = true;
    }
    let load = mn[0] == 'l';
    if a_ops.len < 2 { return false; }
    // the suffix after ldr/str/ldur/stur
    let tail = if unscaled { mn[4..] } else { mn[3..] };
    if tail.len == 0 {
        let ok, size, V = a_rt_class(0);
        if !ok { return false; }
        if V == 1 && a_ops[0].w == 128 {
            return ldst(0, 1, if load { 3 } else { 2 }, 4, rr(0), 1, unscaled);
        }
        return ldst(size, V, if load { 1 } else { 0 }, size, rr(0), 1, unscaled);
    }
    if !isRZ(0) { return false; }
    let w = a_ops[0].w;
    if tail == "b" || tail == "h" {
        if w != 32 { return false; }
        let size = if tail == "b" { 0 } else { 1 };
        return ldst(size, 0, if load { 1 } else { 0 }, size, rr(0), 1, unscaled);
    }
    if !load { return false; }
    if tail == "sb" || tail == "sh" {
        let size = if tail == "sb" { 0 } else { 1 };
        return ldst(size, 0, if w == 64 { 2 } else { 3 }, size, rr(0), 1, unscaled);
    }
    if tail == "sw" {
        if w != 64 { return false; }
        return ldst(2, 0, 2, 2, rr(0), 1, unscaled);
    }
    return false;
}

fn e_ldstp(mn: const u8[:]) -> bool {
    if a_ops.len < 3 || a_ops.len > 4 || !isM(2) { return false; }
    let load = mn[0] == 'l';
    var opc: i64 = 0;
    var V: i64 = 0;
    var scale: i64 = 0;
    if mn == "ldpsw" {
        if !isRZ(0) || !isRZ(1) || a_ops[0].w != 64 || a_ops[1].w != 64 { return false; }
        opc = 1; scale = 2;
    } else if isRZ(0) && isRZ(1) {
        if !same_w(0, 1) { return false; }
        opc = if a_ops[0].w == 64 { 2 } else { 0 };
        scale = if a_ops[0].w == 64 { 3 } else { 2 };
    } else if isF(0) && isF(1) && same_w(0, 1) && a_ops[0].w >= 32 {
        V = 1;
        opc = if a_ops[0].w == 32 { 0 } else if a_ops[0].w == 64 { 1 } else { 2 };
        scale = if a_ops[0].w == 32 { 2 } else if a_ops[0].w == 64 { 3 } else { 4 };
    } else {
        return false;
    }
    let m = a_ops[2];
    var idx: i64 = 2;
    var off = m.off;
    if m.mode == 2 { return false; }
    if a_ops.len == 4 {
        if m.mode != 0 || m.off != 0 || !isI(3) { return false; }
        idx = 1;
        off = imm(3);
    } else if m.mode == 1 {
        idx = 3;
    }
    if off % (1 << (scale as! u64)) != 0 { return false; }
    let s = off >> (scale as! u64);
    if s < -64 || s > 63 { return false; }
    a_word(0x28000000 | (opc << 30) | (V << 26) | (idx << 23) | ((if load { 1 } else { 0 }) << 22) | ((s & 0x7F) << 15) | (rr(1) << 10) | (m.base << 5) | rr(0));
    return true;
}

fn a_plain_mem(k: i64) -> bool { isM(k) && a_ops[k].mode == 0 && a_ops[k].off == 0 }

// exclusives and acquire / release
fn e_excl(mn: const u8[:]) -> bool {
    // name: ld[a]xr[b|h], st[l]xr[b|h], ldar[b|h], stlr[b|h], ldxp, ldaxp, stxp, stlxp, ldapr[b|h]
    var base = mn;
    var size: i64 = -1;
    if mn[mn.len - 1] == 'b' && mn[mn.len - 2] == 'r' { size = 0; base = mn[..mn.len - 1]; }
    else if mn[mn.len - 1] == 'h' && mn[mn.len - 2] == 'r' { size = 1; base = mn[..mn.len - 1]; }
    var L: i64 = 0;
    var o2: i64 = 0;
    var o1: i64 = 0;
    var o0: i64 = 0;
    var st = false;      // has a status register
    var pair = false;
    if base == "ldxr" { L = 1; } else if base == "ldaxr" { L = 1; o0 = 1; }
    else if base == "stxr" { st = true; } else if base == "stlxr" { st = true; o0 = 1; }
    else if base == "ldar" { o2 = 1; L = 1; o0 = 1; } else if base == "stlr" { o2 = 1; o0 = 1; }
    else if base == "ldxp" { L = 1; o1 = 1; pair = true; } else if base == "ldaxp" { L = 1; o1 = 1; o0 = 1; pair = true; }
    else if base == "stxp" { o1 = 1; st = true; pair = true; } else if base == "stlxp" { o1 = 1; o0 = 1; st = true; pair = true; }
    else if base == "ldapr" {
        if !nops_is(2) || !isRZ(0) || !a_plain_mem(1) { return false; }
        let sz = if size >= 0 { size } else if a_ops[0].w == 64 { 3 } else { 2 };
        if size >= 0 && a_ops[0].w != 32 { return false; }
        a_word(0x38BFC000 | (sz << 30) | (a_ops[1].base << 5) | rr(0));
        return true;
    } else { return false; }
    if pair && size >= 0 { return false; }
    var k = 0;
    var rs: i64 = 31;
    if st {
        if !isRZ(0) || a_ops[0].w != 32 { return false; }
        rs = rr(0);
        k = 1;
    }
    let nreg = if pair { 2 } else { 1 };
    if a_ops.len != k + nreg + 1 || !a_plain_mem(k + nreg) { return false; }
    if !isRZ(k) { return false; }
    var rt2: i64 = 31;
    if pair { if !isRZ(k + 1) || !same_w(k, k + 1) { return false; } rt2 = rr(k + 1); }
    var sz = size;
    if sz < 0 { sz = if a_ops[k].w == 64 { 3 } else { 2 }; } else if a_ops[k].w != 32 { return false; }
    if pair { sz = if a_ops[k].w == 64 { 3 } else { 2 }; }
    a_word(0x08000000 | (sz << 30) | (o2 << 23) | (L << 22) | (o1 << 21) | (rs << 16) | (o0 << 15) | (rt2 << 10) | (a_ops[k + nreg].base << 5) | rr(k));
    return true;
}

let A_LSE = ["ldadd", "ldclr", "ldeor", "ldset", "ldsmax", "ldsmin", "ldumax", "ldumin", "swp"];
let A_LSE_ST = ["stadd", "stclr", "steor", "stset", "stsmax", "stsmin", "stumax", "stumin"];

// LSE: name + [a|l|al] + [b|h]
fn e_lse(mn: const u8[:]) -> bool {
    var opc: i64 = -1;
    var rest = mn;
    var store = false;
    for nm, k in A_LSE {
        if starts_with(mn, nm) && opc < 0 { opc = k; rest = mn[nm.len..]; }
    }
    if opc < 0 {
        for nm, k in A_LSE_ST {
            if starts_with(mn, nm) && opc < 0 { opc = k; rest = mn[nm.len..]; store = true; }
        }
    }
    var cas = false;
    if opc < 0 && starts_with(mn, "cas") { cas = true; rest = mn[3..]; }
    if opc < 0 && !cas { return false; }
    var A: i64 = 0;
    var R: i64 = 0;
    if starts_with(rest, "al") { A = 1; R = 1; rest = rest[2..]; }
    else if starts_with(rest, "a") && !store { A = 1; rest = rest[1..]; }
    else if starts_with(rest, "l") { R = 1; rest = rest[1..]; }
    var size: i64 = -1;
    if rest == "b" { size = 0; } else if rest == "h" { size = 1; } else if rest.len != 0 { return false; }
    let nr = if store { 1 } else { 2 };
    if !nops_is(nr + 1) || !a_plain_mem(nr) { return false; }
    for k in nr { if !isRZ(k) { return false; } }
    if nr == 2 && !same_w(0, 1) { return false; }
    let w = a_ops[0].w;
    if size >= 0 && w != 32 { return false; }
    let sz = if size >= 0 { size } else if w == 64 { 3 } else { 2 };
    let rn = a_ops[nr].base;
    let rt = if store { 31 } else { rr(1) };
    if cas {
        a_word(0x08A07C00 | (sz << 30) | (A << 22) | (rr(0) << 16) | (R << 15) | (rn << 5) | rt);
        return true;
    }
    let o3: i64 = if opc == 8 { 1 } else { 0 };
    let op = if opc == 8 { 0 } else { opc };
    a_word(0x38200000 | (sz << 30) | (A << 23) | (R << 22) | (rr(0) << 16) | (o3 << 15) | (op << 12) | (rn << 5) | rt);
    return true;
}

fn e_prfm() -> bool {
    if !nops_is(2) || !isM(1) { return false; }
    var t: i64 = -1;
    if isI(0) { t = imm(0); }
    else if a_ops[0].k == AK_ID {
        let s = a_buf[a_ops[0].s0..a_ops[0].s1];
        if s.len == 9 && (starts_with(s, "pld") || starts_with(s, "pli") || starts_with(s, "pst")) && s[3] == 'l' &&
           s[4] >= '1' && s[4] <= '3' {
            let ty = if starts_with(s, "pld") { 0 } else if starts_with(s, "pli") { 1 } else { 2 };
            let pol = if s[5..] == "keep" { 0 } else if s[5..] == "strm" { 1 } else { -1 };
            if pol >= 0 { t = (ty << 3) | (((s[4] - '1') as i64) << 1) | pol; }
        }
    }
    if t < 0 || t > 31 { return false; }
    let m = a_ops[1];
    if m.mode == 1 { return false; }
    if m.mode == 2 { return ldst(3, 0, 2, 3, t, 1, false); }
    if m.off >= 0 && m.off % 8 == 0 && m.off / 8 <= 4095 {
        a_word(0xF9800000 | ((m.off / 8) << 10) | (m.base << 5) | t);
        return true;
    }
    if m.off >= -256 && m.off <= 255 { a_word(0xF8800000 | ((m.off & 0x1FF) << 12) | (m.base << 5) | t); return true; }
    return false;
}

// ---------------------------------------------------------------- scalar FP

fn ftype(w: i64) -> i64 { if w == 32 { 0 } else if w == 64 { 1 } else if w == 16 { 3 } else { -1 } }

let A_FP2 = ["fmul", "fdiv", "fadd", "fsub", "fmax", "fmin", "fmaxnm", "fminnm", "fnmul"];
let A_FP1 = ["fmov", "fabs", "fneg", "fsqrt", "", "", "", "", "frintn", "frintp", "frintm", "frintz", "frinta", "", "frintx", "frinti"];

fn e_fp2(opc: i64) -> bool {
    if !nops_is(3) || !isF(0) || !isF(1) || !isF(2) || !same_w(0, 1) || !same_w(0, 2) { return false; }
    let t = ftype(a_ops[0].w);
    if t < 0 { return false; }
    a_word(0x1E200800 | (t << 22) | (rr(2) << 16) | (opc << 12) | (rr(1) << 5) | rr(0));
    return true;
}
fn e_fp1(opc: i64) -> bool {
    if !nops_is(2) || !isF(0) || !isF(1) || !same_w(0, 1) { return false; }
    let t = ftype(a_ops[0].w);
    if t < 0 { return false; }
    a_word(0x1E204000 | (t << 22) | (opc << 15) | (rr(1) << 5) | rr(0));
    return true;
}
fn e_fp3(o1: i64, o0: i64) -> bool {
    if !nops_is(4) || !isF(0) || !isF(1) || !isF(2) || !isF(3) || !same_w(0, 1) || !same_w(0, 2) || !same_w(0, 3) { return false; }
    let t = ftype(a_ops[0].w);
    if t < 0 { return false; }
    a_word(0x1F000000 | (t << 22) | (o1 << 21) | (rr(2) << 16) | (o0 << 15) | (rr(3) << 10) | (rr(1) << 5) | rr(0));
    return true;
}
fn e_fcmp(e: i64) -> bool {
    if !nops_is(2) || !isF(0) { return false; }
    let t = ftype(a_ops[0].w);
    if t < 0 { return false; }
    if a_is_zero_imm(a_ops[1]) { a_word(0x1E202008 | (t << 22) | (rr(0) << 5) | (e << 4)); return true; }
    if !isF(1) || !same_w(0, 1) { return false; }
    a_word(0x1E202000 | (t << 22) | (rr(1) << 16) | (rr(0) << 5) | (e << 4));
    return true;
}
fn e_fcsel() -> bool {
    if !nops_is(4) || !isF(0) || !isF(1) || !isF(2) || !same_w(0, 1) || !same_w(0, 2) { return false; }
    let t = ftype(a_ops[0].w);
    let c = a_cond(a_ops[3]);
    if t < 0 || c < 0 { return false; }
    a_word(0x1E200C00 | (t << 22) | (rr(2) << 16) | (c << 12) | (rr(1) << 5) | rr(0));
    return true;
}
fn e_fmov() -> bool {
    if !nops_is(2) { return false; }
    if isF(0) && isF(1) { return e_fp1(0); }
    if isF(0) && a_ops[1].k == AK_I {
        let t = ftype(a_ops[0].w);
        if t < 0 { return false; }
        if a_is_zero_imm(a_ops[1]) {
            // fmov Rd, #0.0 is fmov Rd, zr
            a_word(0x1E270000 | (if a_ops[0].w == 64 { 0x80000000 } else { 0 }) | (t << 22) | (31 << 5) | rr(0));
            return true;
        }
        let f8 = a_fp8(a_ops[1]);
        if f8 < 0 { return false; }
        a_word(0x1E201000 | (t << 22) | (f8 << 13) | rr(0));
        return true;
    }
    if isV(0) && a_ops[1].k == AK_I {
        let f8 = a_fp8(a_ops[1]);
        let w = a_ops[0].w;
        if f8 < 0 || (w != 32 && w != 64) || (w == 64 && a_ops[0].n != 2) { return false; }
        a_word(0x0F00F400 | (vq(0) << 30) | ((if w == 64 { 1 } else { 0 }) << 29) | ((f8 >> 5) << 16) | ((f8 & 31) << 5) | rr(0));
        return true;
    }
    if isF(0) && isRZ(1) {
        let w = a_ops[0].w;
        let g = a_ops[1].w;
        if w == 32 && g == 32 { a_word(0x1E270000 | (rr(1) << 5) | rr(0)); return true; }
        if w == 64 && g == 64 { a_word(0x9E670000 | (rr(1) << 5) | rr(0)); return true; }
        if w == 16 { a_word((if g == 64 { 0x9EE70000 } else { 0x1EE70000 }) | (rr(1) << 5) | rr(0)); return true; }
        return false;
    }
    if isRZ(0) && isF(1) {
        let w = a_ops[1].w;
        let g = a_ops[0].w;
        if w == 32 && g == 32 { a_word(0x1E260000 | (rr(1) << 5) | rr(0)); return true; }
        if w == 64 && g == 64 { a_word(0x9E660000 | (rr(1) << 5) | rr(0)); return true; }
        if w == 16 { a_word((if g == 64 { 0x9EE60000 } else { 0x1EE60000 }) | (rr(1) << 5) | rr(0)); return true; }
        return false;
    }
    if isRZ(0) && isE(1) && a_ops[1].w == 64 && a_ops[1].idx == 1 && a_ops[0].w == 64 {
        a_word(0x9EAE0000 | (rr(1) << 5) | rr(0));
        return true;
    }
    if isE(0) && isRZ(1) && a_ops[0].w == 64 && a_ops[0].idx == 1 && a_ops[1].w == 64 {
        a_word(0x9EAF0000 | (rr(1) << 5) | rr(0));
        return true;
    }
    return false;
}
fn e_fcvt() -> bool {
    if !nops_is(2) || !isF(0) || !isF(1) { return false; }
    let src = ftype(a_ops[1].w);
    let dst = ftype(a_ops[0].w);
    if src < 0 || dst < 0 || src == dst { return false; }
    let opc = if dst == 0 { 4 } else if dst == 1 { 5 } else { 7 };
    a_word(0x1E204000 | (src << 22) | (opc << 15) | (rr(1) << 5) | rr(0));
    return true;
}
let A_FCVTI = ["fcvtns", "fcvtnu", "fcvtps", "fcvtpu", "fcvtms", "fcvtmu", "fcvtzs", "fcvtzu", "fcvtas", "fcvtau"];
let A_FCVTI_RM: i64[10] = [0, 0, 1, 1, 2, 2, 3, 3, 0, 0];
let A_FCVTI_OP: i64[10] = [0, 1, 0, 1, 0, 1, 0, 1, 4, 5];
// FP <-> integer (general registers)
fn e_fcvti(rmode: i64, opc: i64) -> bool {
    if !nops_is(2) { return false; }
    if opc == 2 || opc == 3 {
        if !isF(0) || !isRZ(1) { return false; }
        let t = ftype(a_ops[0].w);
        if t < 0 { return false; }
        a_word(0x1E200000 | (sf(1) << 31) | (t << 22) | (rmode << 19) | (opc << 16) | (rr(1) << 5) | rr(0));
        return true;
    }
    if !isRZ(0) || !isF(1) { return false; }
    let t = ftype(a_ops[1].w);
    if t < 0 { return false; }
    a_word(0x1E200000 | (sf(0) << 31) | (t << 22) | (rmode << 19) | (opc << 16) | (rr(1) << 5) | rr(0));
    return true;
}

// ---------------------------------------------------------------- SIMD

// three-same integer: U<<8 | opcode; flags: 0x1000 no 64-bit lanes, 0x2000 bytes only, 0x4000 h/s only,
// 0x8000 the scalar form takes only d registers, 0x10000 no scalar form
let A_V3 = ["shadd", "sqadd", "srhadd", "shsub", "sqsub", "cmgt", "cmge", "sshl", "sqshl", "srshl", "sqrshl", "smax", "smin", "sabd", "saba",
            "add", "cmtst", "mla", "mul", "smaxp", "sminp", "sqdmulh", "addp",
            "uhadd", "uqadd", "urhadd", "uhsub", "uqsub", "cmhi", "cmhs", "ushl", "uqshl", "urshl", "uqrshl", "umax", "umin", "uabd", "uaba",
            "sub", "cmeq", "mls", "pmul", "umaxp", "uminp", "sqrdmulh"];
let A_V3_ENC: i64[45] = [0x11000, 0x01, 0x11002, 0x11004, 0x05, 0x8006, 0x8007, 0x8008, 0x09, 0x800A, 0x0B, 0x1100C, 0x1100D, 0x1100E, 0x1100F,
            0x8010, 0x8011, 0x11012, 0x11013, 0x11014, 0x11015, 0x4016, 0x10017,
            0x11100, 0x101, 0x11102, 0x11104, 0x105, 0x8106, 0x8107, 0x8108, 0x109, 0x810A, 0x10B, 0x1110C, 0x1110D, 0x1110E, 0x1110F,
            0x8110, 0x8111, 0x11112, 0x12113, 0x11114, 0x11115, 0x4116];

fn e_v3(e: i64) -> bool {
    if !nops_is(3) { return false; }
    let u = (e >> 8) & 1;
    let opc = e & 31;
    if isF(0) && isF(1) && isF(2) {
        if e & 0x10000 != 0 || !same_w(0, 1) || !same_w(0, 2) { return false; }
        let w = a_ops[0].w;
        if w > 64 || (e & 0x8000 != 0 && w != 64) || (e & 0x4000 != 0 && w != 16 && w != 32) { return false; }
        a_word(0x5E200400 | (u << 29) | (vsize(w) << 22) | (rr(2) << 16) | (opc << 11) | (rr(1) << 5) | rr(0));
        return true;
    }
    if !isV(0) || !isV(1) || !isV(2) || !same_arr(0, 1) || !same_arr(0, 2) { return false; }
    let w = a_ops[0].w;
    if (e & 0x1000 != 0 && w == 64) || (e & 0x2000 != 0 && w != 8) || (e & 0x4000 != 0 && w != 16 && w != 32) { return false; }
    if w == 64 && vq(0) == 0 { return false; }
    a_word(0x0E200400 | (vq(0) << 30) | (u << 29) | (vsize(w) << 22) | (rr(2) << 16) | (opc << 11) | (rr(1) << 5) | rr(0));
    return true;
}

let A_VLOG = ["and", "bic", "orr", "orn", "eor", "bsl", "bit", "bif"];
fn e_vlogic(k: i64) -> bool {
    if !nops_is(3) || !isV(0) || !isV(1) || !isV(2) || !same_arr(0, 1) || !same_arr(0, 2) || a_ops[0].w != 8 { return false; }
    a_word(0x0E201C00 | (vq(0) << 30) | ((k >> 2) << 29) | ((k & 3) << 22) | (rr(2) << 16) | (rr(1) << 5) | rr(0));
    return true;
}

// FP three-same: U<<6 | a<<5 | opcode
let A_VF3 = ["fmaxnm", "fmla", "fadd", "fmulx", "fcmeq", "fmax", "frecps",
             "fminnm", "fmls", "fsub", "fmin", "frsqrts",
             "fmaxnmp", "faddp", "fmul", "fcmge", "facge", "fmaxp", "fdiv",
             "fminnmp", "fabd", "fcmgt", "facgt", "fminp"];
let A_VF3_ENC: i64[24] = [0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1E, 0x1F,
             0x38, 0x39, 0x3A, 0x3E, 0x3F,
             0x58, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F,
             0x78, 0x7A, 0x7C, 0x7D, 0x7E];
fn e_vf3(e: i64) -> bool {
    if !nops_is(3) || !isV(0) || !isV(1) || !isV(2) || !same_arr(0, 1) || !same_arr(0, 2) { return false; }
    let w = a_ops[0].w;
    if (w != 32 && w != 64) || (w == 64 && a_ops[0].n != 2) { return false; }
    a_word(0x0E200400 | (vq(0) << 30) | (((e >> 6) & 1) << 29) | (((e >> 5) & 1) << 23) | ((if w == 64 { 1 } else { 0 }) << 22) |
           (rr(2) << 16) | ((e & 31) << 11) | (rr(1) << 5) | rr(0));
    return true;
}

// two-register misc: U<<8 | opcode; 0x1000 FP (a in bit 9); 0x2000 bytes only; 0x4000 no 64-bit lanes;
// 0x8000 a compare with #0 (third operand); 0x10000 the narrowing form (dest half width); 0x20000 widening pairwise
let A_V2 = ["rev64", "rev16", "saddlp", "suqadd", "cls", "cnt", "sadalp", "sqabs", "cmgt", "cmeq", "cmlt", "abs", "xtn", "sqxtn",
            "rev32", "uaddlp", "usqadd", "clz", "not", "mvn", "rbit", "uadalp", "sqneg", "cmge", "cmle", "neg", "sqxtun", "uqxtn",
            "frintn", "frintm", "fcvtns", "fcvtms", "fcvtas", "scvtf", "fcmgt", "fcmeq", "fcmlt", "fabs", "frintp", "frintz", "fcvtps", "fcvtzs", "frecpe",
            "frinta", "frintx", "fcvtnu", "fcvtmu", "fcvtau", "ucvtf", "fcmge", "fcmle", "fneg", "frinti", "fcvtpu", "fcvtzu", "frsqrte", "fsqrt"];
let A_V2_ENC: i64[57] = [0x4000, 0x2001, 0x24002, 0x0003, 0x4004, 0x2005, 0x24006, 0x0007, 0x8008, 0x8009, 0x800A, 0x000B, 0x10012, 0x10014,
            0x4100, 0x24102, 0x0103, 0x4104, 0x2105, 0x2105, 0x2105, 0x24106, 0x0107, 0x8108, 0x8109, 0x010B, 0x10112, 0x10114,
            0x1018, 0x1019, 0x101A, 0x101B, 0x101C, 0x101D, 0x920C, 0x920D, 0x920E, 0x120F, 0x1218, 0x1219, 0x121A, 0x121B, 0x121D,
            0x1118, 0x1119, 0x111A, 0x111B, 0x111C, 0x111D, 0x930C, 0x930D, 0x130F, 0x1319, 0x131A, 0x131B, 0x131D, 0x131F];

fn e_v2(mn: const u8[:], e: i64) -> bool {
    let cmp0 = e & 0x8000 != 0;
    if !nops_is(if cmp0 { 3 } else { 2 }) { return false; }
    if cmp0 && !a_is_zero_imm(a_ops[2]) { return false; }
    let u = (e >> 8) & 1;
    let opc = e & 31;
    if e & 0x1000 != 0 {
        if !isV(0) || !isV(1) || !same_arr(0, 1) { return false; }
        let w = a_ops[0].w;
        if (w != 32 && w != 64) || (w == 64 && a_ops[0].n != 2) { return false; }
        let a = (e >> 9) & 1;
        a_word(0x0E200800 | (vq(0) << 30) | (u << 29) | (a << 23) | ((if w == 64 { 1 } else { 0 }) << 22) | (opc << 12) | (rr(1) << 5) | rr(0));
        return true;
    }
    if isF(0) && isF(1) && !cmp0 && e & 0x30000 == 0 {
        // scalar: abs / neg / sqabs / sqneg / suqadd / usqadd
        if !same_w(0, 1) || !(opc == 0x0B || opc == 0x07 || opc == 0x03) || (opc == 0x0B && a_ops[0].w != 64) || a_ops[0].w > 64 { return false; }
        a_word(0x5E200800 | (u << 29) | (vsize(a_ops[0].w) << 22) | (opc << 12) | (rr(1) << 5) | rr(0));
        return true;
    }
    if isF(0) && isF(1) && cmp0 {
        if !same_w(0, 1) || a_ops[0].w != 64 { return false; }
        a_word(0x5E200800 | (u << 29) | (3 << 22) | (opc << 12) | (rr(1) << 5) | rr(0));
        return true;
    }
    if !isV(0) || !isV(1) { return false; }
    let d = a_ops[0];
    let s = a_ops[1];
    var size = vsize(d.w);
    var q = vq(0);
    if e & 0x10000 != 0 {
        // narrow: d is half the width of s; "2" writes the upper half
        if s.w != 2 * d.w || s.w * s.n != 128 { return false; }
        if (vq(0) == 1) != ends_with2(mn) { return false; }
        size = vsize(d.w);
    } else if e & 0x20000 != 0 {
        // pairwise long: d lanes double width, half the count
        if d.w != 2 * s.w || d.n * 2 != s.n || s.w == 64 { return false; }
        size = vsize(s.w);
        q = vq(1);
    } else {
        if !same_arr(0, 1) { return false; }
        if mn == "rbit" { size = 1; if d.w != 8 { return false; } }
        else if mn == "not" || mn == "mvn" { size = 0; if d.w != 8 { return false; } }
        else if e & 0x2000 != 0 && d.w != 8 { return false; }
        if e & 0x4000 != 0 && d.w == 64 { return false; }
        if mn == "rev16" && d.w != 8 { return false; }
        if mn == "rev32" && d.w > 16 { return false; }
        if d.w == 64 && q == 0 { return false; }
    }
    a_word(0x0E200800 | (q << 30) | (u << 29) | (size << 22) | (opc << 12) | (rr(1) << 5) | rr(0));
    return true;
}

let A_VACROSS = ["saddlv", "smaxv", "sminv", "addv", "uaddlv", "umaxv", "uminv"];
let A_VACROSS_ENC: i64[7] = [0x03, 0x0A, 0x1A, 0x1B, 0x103, 0x10A, 0x11A];
fn e_vacross(mn: const u8[:], e: i64) -> bool {
    if !nops_is(2) || !isF(0) || !isV(1) { return false; }
    let s = a_ops[1];
    if s.w == 64 || (s.w == 32 && s.n != 4) { return false; }
    let long = mn == "saddlv" || mn == "uaddlv";
    if a_ops[0].w != (if long { 2 * s.w } else { s.w }) { return false; }
    a_word(0x0E300800 | (vq(1) << 30) | (((e >> 8) & 1) << 29) | (vsize(s.w) << 22) | ((e & 31) << 12) | (rr(1) << 5) | rr(0));
    return true;
}
fn e_vfacross(size: i64, opc: i64) -> bool {
    if !nops_is(2) || !isF(0) || !isV(1) || a_ops[0].w != 32 || a_ops[1].w != 32 || a_ops[1].n != 4 { return false; }
    a_word(0x6E300800 | (size << 22) | (opc << 12) | (rr(1) << 5) | rr(0));
    return true;
}

// dup / umov / smov / ins
fn a_imm5(w: i64, idx: i64) -> i64 {
    let s = vsize(w);
    return (idx << (s + 1)) | (1 << s);
}
fn a_idx_ok(w: i64, idx: i64) -> bool { idx >= 0 && idx < 128 / w }
fn e_dup() -> bool {
    if !nops_is(2) { return false; }
    if isF(0) && isE(1) {
        let s = a_ops[1];
        if a_ops[0].w != s.w || !a_idx_ok(s.w, s.idx) || s.w > 64 { return false; }
        a_word(0x5E000400 | (a_imm5(s.w, s.idx) << 16) | (rr(1) << 5) | rr(0));
        return true;
    }
    if !isV(0) { return false; }
    let d = a_ops[0];
    if d.w == 64 && vq(0) == 0 { return false; }
    if isE(1) {
        let s = a_ops[1];
        if s.w != d.w || !a_idx_ok(s.w, s.idx) { return false; }
        a_word(0x0E000400 | (vq(0) << 30) | (a_imm5(s.w, s.idx) << 16) | (rr(1) << 5) | rr(0));
        return true;
    }
    if isRZ(1) {
        if a_ops[1].w != (if d.w == 64 { 64 } else { 32 }) { return false; }
        a_word(0x0E000C00 | (vq(0) << 30) | (a_imm5(d.w, 0) << 16) | (rr(1) << 5) | rr(0));
        return true;
    }
    return false;
}
fn e_umov(signed: bool) -> bool {
    if !nops_is(2) || !isRZ(0) || !isE(1) { return false; }
    let s = a_ops[1];
    let g = a_ops[0].w;
    if !a_idx_ok(s.w, s.idx) { return false; }
    if signed {
        if s.w >= g || s.w > 32 { return false; }
        a_word(0x0E002C00 | ((if g == 64 { 1 } else { 0 }) << 30) | (a_imm5(s.w, s.idx) << 16) | (rr(1) << 5) | rr(0));
        return true;
    }
    if (s.w == 64) != (g == 64) { return false; }
    a_word(0x0E003C00 | ((if g == 64 { 1 } else { 0 }) << 30) | (a_imm5(s.w, s.idx) << 16) | (rr(1) << 5) | rr(0));
    return true;
}
fn e_ins() -> bool {
    if !nops_is(2) || !isE(0) { return false; }
    let d = a_ops[0];
    if !a_idx_ok(d.w, d.idx) { return false; }
    if isRZ(1) {
        if a_ops[1].w != (if d.w == 64 { 64 } else { 32 }) { return false; }
        a_word(0x4E001C00 | (a_imm5(d.w, d.idx) << 16) | (rr(1) << 5) | rr(0));
        return true;
    }
    if isE(1) {
        let s = a_ops[1];
        if s.w != d.w || !a_idx_ok(s.w, s.idx) { return false; }
        a_word(0x6E000400 | (a_imm5(d.w, d.idx) << 16) | ((s.idx << vsize(s.w)) << 11) | (rr(1) << 5) | rr(0));
        return true;
    }
    return false;
}

// movi / mvni / orr / bic (vector, immediate)
fn e_movi(mn: const u8[:]) -> bool {
    if a_ops.len < 2 || a_ops.len > 3 || !isI(1) { return false; }
    let v = imm(1);
    var shk: i64 = 0;
    var sha: i64 = 0;
    if a_ops.len == 3 {
        if !isS(2) || (a_ops[2].sk != 0 && a_ops[2].sk != 4) || a_ops[2].sa < 0 { return false; }
        shk = a_ops[2].sk;
        sha = a_ops[2].sa;
    }
    let mvn = mn == "mvni" || mn == "bic";
    let logic = mn == "orr" || mn == "bic";
    var q: i64 = 0;
    var w: i64 = 0;
    if isF(0) && a_ops[0].w == 64 && mn == "movi" { w = 0; q = 0; }
    else if isV(0) { w = a_ops[0].w; q = vq(0); }
    else { return false; }
    var op: i64 = if mvn { 1 } else { 0 };
    var cmode: i64 = 0;
    var abc: i64 = 0;
    if w == 0 || w == 64 {
        // 64-bit: each byte 0x00 or 0xff
        if mvn || logic || shk != 0 || sha != 0 || (w == 64 && a_ops[0].n != 2) { return false; }
        var bits: i64 = 0;
        let x = v as! u64;
        for k in 8 {
            let b = (x >> (8 * k as! u64)) & 255;
            if b == 255 { bits = bits | (1 << k); } else if b != 0 { return false; }
        }
        op = 1;
        cmode = 0xE;
        abc = bits;
    } else {
        if v < 0 || v > 255 { return false; }
        abc = v;
        if w == 8 {
            if mvn || logic || shk != 0 || sha != 0 { return false; }
            cmode = 0xE;
        } else if w == 16 {
            if shk != 0 || (sha != 0 && sha != 8) { return false; }
            cmode = 0x8 | (sha / 8 << 1);
        } else if w == 32 {
            if shk == 4 {
                if logic || (sha != 8 && sha != 16) { return false; }
                cmode = 0xC | (sha / 8 - 1);
            } else {
                if sha % 8 != 0 || sha > 24 { return false; }
                cmode = (sha / 8) << 1;
            }
        } else {
            return false;
        }
        if logic { cmode = cmode | 1; }
    }
    a_word(0x0F000400 | (q << 30) | (op << 29) | ((abc >> 5) << 16) | (cmode << 12) | ((abc & 31) << 5) | rr(0));
    return true;
}

// by element: U<<8 | opcode, 0x1000 FP, 0x2000 long, 0x4000 dot (.4b)
let A_VE = ["mul", "mla", "mls", "sqdmulh", "sqrdmulh", "fmul", "fmla", "fmls", "smull", "umull", "smlal", "umlal", "smlsl", "umlsl", "sqdmull", "sdot", "udot", "fmulx"];
let A_VE_ENC: i64[18] = [0x08, 0x100, 0x104, 0x0C, 0x0D, 0x1009, 0x1001, 0x1005, 0x200A, 0x210A, 0x2002, 0x2102, 0x2006, 0x2106, 0x200B, 0x400E, 0x410E, 0x1109];
fn e_velem(mn: const u8[:], e: i64) -> bool {
    if !nops_is(3) || !isE(2) { return false; }
    let m = a_ops[2];
    let u = (e >> 8) & 1;
    let opc = e & 15;
    if isF(0) && isF(1) && e & 0x1000 != 0 {
        // scalar by element
        let w = a_ops[0].w;
        if !same_w(0, 1) || m.w != w || (w != 32 && w != 64) || !a_idx_ok(w, m.idx) { return false; }
        let sz = if w == 64 { 1 } else { 0 };
        var hl: i64 = 0;
        if w == 64 { hl = m.idx << 11; } else { hl = ((m.idx >> 1) << 11) | ((m.idx & 1) << 21); }
        a_word(0x5F800000 | (u << 29) | (sz << 22) | hl | (m.r << 16) | (opc << 12) | (rr(1) << 5) | rr(0));
        return true;
    }
    if !isV(0) || !isV(1) { return false; }
    let d = a_ops[0];
    let n = a_ops[1];
    var size: i64 = 0;
    var q = vq(0);
    if e & 0x4000 != 0 {
        if d.w != 32 || n.w != 8 || d.n * 4 != n.n || m.w != 32 && !(m.w == 8) { return false; }
        // index of a 4-byte group
        if m.idx > 3 { return false; }
        size = 2;
    } else if e & 0x2000 != 0 {
        if d.w != 2 * n.w || d.w * d.n != 128 || n.w != m.w { return false; }
        if (vq(1) == 1) != ends_with2(mn) { return false; }
        q = vq(1);
        size = vsize(n.w);
    } else {
        if !same_arr(0, 1) || m.w != d.w { return false; }
        if e & 0x1000 != 0 {
            if d.w != 32 && d.w != 64 { return false; }
            if d.w == 64 && q == 0 { return false; }
            size = if d.w == 64 { 3 } else { 2 };
        } else {
            if d.w != 16 && d.w != 32 { return false; }
            size = vsize(d.w);
        }
    }
    var idx = m.idx;
    let ew = if e & 0x4000 != 0 { 32 } else { m.w };
    if idx < 0 || idx >= 128 / ew { return false; }
    var H: i64 = 0;
    var L: i64 = 0;
    var M: i64 = 0;
    var rm = m.r;
    if ew == 16 {
        if rm > 15 { return false; }
        H = idx >> 2; L = (idx >> 1) & 1; M = idx & 1;
    } else if ew == 32 {
        H = idx >> 1; L = idx & 1;
    } else {
        H = idx;
    }
    if ew != 16 { M = rm >> 4; }
    a_word(0x0F000000 | (q << 30) | (u << 29) | (size << 22) | (L << 21) | (M << 20) | ((rm & 15) << 16) |
           (opc << 12) | (H << 11) | (rr(1) << 5) | rr(0));
    return true;
}

// shift by immediate: U<<8 | opcode; 0x1000 left (else right); 0x2000 narrow; 0x4000 long
let A_VSH = ["sshr", "ssra", "srshr", "srsra", "shl", "sqshl", "shrn", "rshrn", "sqshrn", "sqrshrn", "sshll",
             "ushr", "usra", "urshr", "ursra", "sri", "sli", "sqshlu", "uqshl", "sqshrun", "sqrshrun", "uqshrn", "uqrshrn", "ushll"];
let A_VSH_ENC: i64[24] = [0x00, 0x02, 0x04, 0x06, 0x100A, 0x100E, 0x2010, 0x2011, 0x2012, 0x2013, 0x5014,
             0x100, 0x102, 0x104, 0x106, 0x108, 0x110A, 0x110C, 0x110E, 0x2110, 0x2111, 0x2112, 0x2113, 0x5114];
fn e_vshift(mn: const u8[:], e: i64) -> bool {
    if !nops_is(3) || !isI(2) { return false; }
    let sh = imm(2);
    let u = (e >> 8) & 1;
    let opc = e & 31;
    if isF(0) && isF(1) {
        // scalar d forms of shl / sshr / ushr / ssra / usra / sri / sli / srshr / urshr
        if a_ops[0].w != 64 || a_ops[1].w != 64 || e & 0x6000 != 0 { return false; }
        var immhb: i64 = 0;
        if e & 0x1000 != 0 { if sh < 0 || sh > 63 { return false; } immhb = 64 + sh; }
        else { if sh < 1 || sh > 64 { return false; } immhb = 128 - sh; }
        a_word(0x5F000400 | (u << 29) | (immhb << 16) | (opc << 11) | (rr(1) << 5) | rr(0));
        return true;
    }
    if !isV(0) || !isV(1) { return false; }
    let d = a_ops[0];
    let s = a_ops[1];
    var esz: i64 = 0;
    var q: i64 = 0;
    if e & 0x2000 != 0 {
        if s.w != 2 * d.w || s.w * s.n != 128 || (vq(0) == 1) != ends_with2(mn) { return false; }
        esz = d.w;
        q = vq(0);
    } else if e & 0x4000 != 0 {
        if d.w != 2 * s.w || d.w * d.n != 128 || (vq(1) == 1) != ends_with2(mn) { return false; }
        esz = s.w;
        q = vq(1);
    } else {
        if !same_arr(0, 1) || (d.w == 64 && vq(0) == 0) { return false; }
        esz = d.w;
        q = vq(0);
    }
    if esz > 64 { return false; }
    var immhb: i64 = 0;
    if e & 0x1000 != 0 {
        if sh < 0 || sh >= esz { return false; }
        immhb = esz + sh;
    } else {
        if sh < 1 || sh > esz { return false; }
        immhb = 2 * esz - sh;
    }
    a_word(0x0F000400 | (q << 30) | (u << 29) | (immhb << 16) | (opc << 11) | (rr(1) << 5) | rr(0));
    return true;
}
fn e_vxtl(mn: const u8[:], u: i64) -> bool {
    // sxtl / uxtl [2]: sshll / ushll #0
    if !nops_is(2) { return false; }
    a_ops.push(AO { k: AK_I, imm: 0 });
    return e_vshift(if ends_with2(mn) { "sshll2" } else { "sshll" }, 0x5014 | (u << 8));
}

// three different: U<<8 | opcode; 0x1000 wide (Rn is the wide type), 0x2000 narrow high (dest narrow)
let A_V3D = ["saddl", "saddw", "ssubl", "ssubw", "addhn", "sabal", "subhn", "sabdl", "smlal", "sqdmlal", "smlsl", "sqdmlsl", "smull", "sqdmull", "pmull",
             "uaddl", "uaddw", "usubl", "usubw", "raddhn", "uabal", "rsubhn", "uabdl", "umlal", "umlsl", "umull"];
let A_V3D_ENC: i64[26] = [0x0, 0x1001, 0x2, 0x1003, 0x2004, 0x5, 0x2006, 0x7, 0x8, 0x9, 0xA, 0xB, 0xC, 0xD, 0xE,
             0x100, 0x1101, 0x102, 0x1103, 0x2104, 0x105, 0x2106, 0x107, 0x108, 0x10A, 0x10C];
fn e_v3d(mn: const u8[:], e: i64) -> bool {
    if !nops_is(3) || !isV(0) || !isV(1) || !isV(2) { return false; }
    let d = a_ops[0];
    let n = a_ops[1];
    let m = a_ops[2];
    let u = (e >> 8) & 1;
    let opc = e & 15;
    var narrow = m;
    var q: i64 = 0;
    if e & 0x2000 != 0 {
        if !same_arr(1, 2) || n.w != 2 * d.w || n.w * n.n != 128 { return false; }
        narrow = d;
        q = vq(0);
    } else if e & 0x1000 != 0 {
        if !same_arr(0, 1) || d.w != 2 * m.w || d.w * d.n != 128 { return false; }
        q = vq(2);
    } else {
        if !same_arr(1, 2) || d.w != 2 * n.w || d.w * d.n != 128 { return false; }
        q = vq(1);
    }
    if (q == 1) != ends_with2(mn) { return false; }
    var size = vsize(narrow.w);
    if mn == "pmull" || mn == "pmull2" {
        if narrow.w != 8 && narrow.w != 64 { return false; }
    } else if narrow.w > 32 {
        return false;
    }
    a_word(0x0E200000 | (q << 30) | (u << 29) | (size << 22) | (m.r << 16) | (opc << 12) | (n.r << 5) | d.r);
    return true;
}

fn e_vperm(opc: i64) -> bool {
    if !nops_is(3) || !isV(0) || !isV(1) || !isV(2) || !same_arr(0, 1) || !same_arr(0, 2) { return false; }
    if a_ops[0].w == 64 && vq(0) == 0 { return false; }
    a_word(0x0E000800 | (vq(0) << 30) | (vsize(a_ops[0].w) << 22) | (rr(2) << 16) | (opc << 12) | (rr(1) << 5) | rr(0));
    return true;
}
fn e_vext() -> bool {
    if !nops_is(4) || !isV(0) || !isV(1) || !isV(2) || !isI(3) || !same_arr(0, 1) || !same_arr(0, 2) || a_ops[0].w != 8 { return false; }
    let i = imm(3);
    if i < 0 || i >= a_ops[0].n { return false; }
    a_word(0x2E000000 | (vq(0) << 30) | (rr(2) << 16) | (i << 11) | (rr(1) << 5) | rr(0));
    return true;
}
fn e_tbl(op: i64) -> bool {
    if !nops_is(3) || !isV(0) || !isL(1) || !isV(2) || a_ops[0].w != 8 || !same_arr(0, 2) { return false; }
    let l = a_ops[1];
    if l.w != 8 || l.ln != 16 || l.idx >= 0 { return false; }
    a_word(0x0E000000 | (vq(0) << 30) | (rr(2) << 16) | ((l.n - 1) << 13) | (op << 12) | (l.r << 5) | rr(0));
    return true;
}
// ld1..4 / st1..4 (multiple structures)
fn e_ldst_struct(mn: const u8[:]) -> bool {
    let load = mn[0] == 'l';
    let k = (mn[2] - '0') as i64;
    if a_ops.len < 2 || a_ops.len > 3 || !isL(0) || !isM(1) { return false; }
    let l = a_ops[0];
    let m = a_ops[1];
    if l.idx >= 0 || m.mode != 0 || m.off != 0 { return false; }
    if l.w == 64 && l.ln == 1 && k != 1 { return false; }
    var opc: i64 = 0;
    if k == 1 {
        opc = if l.n == 1 { 7 } else if l.n == 2 { 10 } else if l.n == 3 { 6 } else { 2 };
    } else {
        if l.n != k { return false; }
        opc = if k == 2 { 8 } else if k == 3 { 4 } else { 0 };
    }
    let q = if l.w * l.ln == 128 { 1 } else { 0 };
    var w = 0x0C000000 | (q << 30) | ((if load { 1 } else { 0 }) << 22) | (opc << 12) | (vsize(l.w) << 10) | (m.base << 5) | l.r;
    if a_ops.len == 3 {
        w = w | 0x00800000;
        if isI(2) {
            if imm(2) != l.n * (if q == 1 { 16 } else { 8 }) { return false; }
            w = w | (31 << 16);
        } else if isRZ(2) && a_ops[2].w == 64 && rr(2) != 31 {
            w = w | (rr(2) << 16);
        } else {
            return false;
        }
    }
    a_word(w);
    return true;
}

fn e_crypto(mn: const u8[:]) -> bool {
    if mn == "aese" || mn == "aesd" || mn == "aesmc" || mn == "aesimc" {
        if !nops_is(2) || !isV(0) || !isV(1) || a_ops[0].w != 8 || a_ops[0].n != 16 || !same_arr(0, 1) { return false; }
        let o = if mn == "aese" { 4 } else if mn == "aesd" { 5 } else if mn == "aesmc" { 6 } else { 7 };
        a_word(0x4E280800 | (o << 12) | (rr(1) << 5) | rr(0));
        return true;
    }
    if mn == "sha1h" {
        if !nops_is(2) || !isF(0) || !isF(1) || a_ops[0].w != 32 || a_ops[1].w != 32 { return false; }
        a_word(0x5E280800 | (rr(1) << 5) | rr(0));
        return true;
    }
    if mn == "sha1su1" || mn == "sha256su0" {
        if !nops_is(2) || !isV(0) || !isV(1) || a_ops[0].w != 32 || a_ops[0].n != 4 || !same_arr(0, 1) { return false; }
        a_word((if mn == "sha1su1" { 0x5E281800 } else { 0x5E282800 }) | (rr(1) << 5) | rr(0));
        return true;
    }
    var o: i64 = -1;
    if mn == "sha1c" { o = 0; } else if mn == "sha1p" { o = 1; } else if mn == "sha1m" { o = 2; } else if mn == "sha1su0" { o = 3; }
    else if mn == "sha256h" { o = 4; } else if mn == "sha256h2" { o = 5; } else if mn == "sha256su1" { o = 6; }
    if o < 0 || !nops_is(3) || !isV(2) || a_ops[2].w != 32 || a_ops[2].n != 4 { return false; }
    if o <= 2 {
        if !isF(0) || a_ops[0].w != 128 || !isF(1) || a_ops[1].w != 32 { return false; }
    } else if o == 3 || o == 6 {
        if !isV(0) || !isV(1) || !same_arr(0, 2) || !same_arr(1, 2) { return false; }
    } else {
        if !isF(0) || !isF(1) || a_ops[0].w != 128 || a_ops[1].w != 128 { return false; }
    }
    a_word(0x5E000000 | (rr(2) << 16) | (o << 12) | (rr(1) << 5) | rr(0));
    return true;
}

fn e_dot(u: i64) -> bool {
    if !nops_is(3) || !isV(0) || !isV(1) { return false; }
    if isE(2) { return e_velem(if u == 1 { "udot" } else { "sdot" }, 0x400E | (u << 8)); }
    if !isV(2) || a_ops[0].w != 32 || a_ops[1].w != 8 || !same_arr(1, 2) || a_ops[0].n * 4 != a_ops[1].n { return false; }
    a_word(0x0E809400 | (vq(0) << 30) | (u << 29) | (rr(2) << 16) | (rr(1) << 5) | rr(0));
    return true;
}

// ---------------------------------------------------------------- dispatch

fn tbl_find(names, mn: const u8[:]) -> i64 {
    for nm, k in names { if mn == nm { return k; } }
    return -1;
}

fn a_insn(mn: const u8[:]) -> bool {
    let vec = a_ops.len > 0 && (a_ops[0].k == AK_V || a_ops[0].k == AK_F || a_ops[0].k == AK_L);
    // integer
    if !vec {
        if mn == "add" { return e_addsub(0, 0); }
        if mn == "adds" { return e_addsub(0, 1); }
        if mn == "sub" { return e_addsub(1, 0); }
        if mn == "subs" { return e_addsub(1, 1); }
        if mn == "cmp" || mn == "cmn" {
            if a_ops.len < 2 || !isR(0) { return false; }
            ins_zr(0, a_ops[0].w);
            return e_addsub(if mn == "cmp" { 1 } else { 0 }, 1);
        }
        if mn == "neg" || mn == "negs" {
            if a_ops.len < 2 || !isR(0) { return false; }
            ins_zr(1, a_ops[0].w);
            if !isRZ(2) { return false; }
            return e_addsub(1, if mn == "negs" { 1 } else { 0 });
        }
        if mn == "and" { return e_logic(0, 0); }
        if mn == "orr" { return e_logic(1, 0); }
        if mn == "eor" { return e_logic(2, 0); }
        if mn == "ands" { return e_logic(3, 0); }
        if mn == "bic" { return e_logic(0, 1); }
        if mn == "orn" { return e_logic(1, 1); }
        if mn == "eon" { return e_logic(2, 1); }
        if mn == "bics" { return e_logic(3, 1); }
        if mn == "tst" {
            if a_ops.len < 2 || !isR(0) { return false; }
            ins_zr(0, a_ops[0].w);
            return e_logic(3, 0);
        }
        if mn == "mvn" {
            if a_ops.len < 2 || !isR(0) { return false; }
            ins_zr(1, a_ops[0].w);
            return e_logic(1, 1);
        }
        if mn == "mov" { return e_mov(mn); }
        if mn == "movz" { return e_movw(2); }
        if mn == "movn" { return e_movw(0); }
        if mn == "movk" { return e_movw(3); }
        if mn == "lsl" || mn == "lsr" || mn == "asr" || mn == "ror" { return e_shift(mn); }
        if mn == "lslv" { return e_dp2(8); }
        if mn == "lsrv" { return e_dp2(9); }
        if mn == "asrv" { return e_dp2(10); }
        if mn == "rorv" { return e_dp2(11); }
        if mn == "udiv" { return e_dp2(2); }
        if mn == "sdiv" { return e_dp2(3); }
        if mn == "ubfm" || mn == "sbfm" || mn == "bfm" || mn == "ubfx" || mn == "sbfx" || mn == "bfxil" || mn == "ubfiz" || mn == "sbfiz" || mn == "bfi" {
            return e_bitfield(mn);
        }
        if mn == "extr" {
            if !nops_is(4) || !isRZ(0) || !isRZ(1) || !isRZ(2) || !isI(3) || !same_w(0, 1) || !same_w(0, 2) { return false; }
            if imm(3) < 0 || imm(3) >= a_ops[0].w { return false; }
            a_word(0x13800000 | (sf(0) << 31) | (sf(0) << 22) | (rr(2) << 16) | (imm(3) << 10) | (rr(1) << 5) | rr(0));
            return true;
        }
        if mn == "sxtb" { return e_ext(true, 8); }
        if mn == "sxth" { return e_ext(true, 16); }
        if mn == "sxtw" { return e_ext(true, 32); }
        if mn == "uxtb" { return e_ext(false, 8); }
        if mn == "uxth" { return e_ext(false, 16); }
        if mn == "madd" { return e_dp3(0, 0, true, false); }
        if mn == "msub" { return e_dp3(0, 1, true, false); }
        if mn == "mul" { return e_dp3(0, 0, false, false); }
        if mn == "mneg" { return e_dp3(0, 1, false, false); }
        if mn == "smaddl" { return e_dp3(1, 0, true, true); }
        if mn == "smsubl" { return e_dp3(1, 1, true, true); }
        if mn == "umaddl" { return e_dp3(5, 0, true, true); }
        if mn == "umsubl" { return e_dp3(5, 1, true, true); }
        if mn == "smull" { return e_dp3(1, 0, false, true); }
        if mn == "umull" { return e_dp3(5, 0, false, true); }
        if mn == "smnegl" { return e_dp3(1, 1, false, true); }
        if mn == "umnegl" { return e_dp3(5, 1, false, true); }
        if mn == "smulh" || mn == "umulh" {
            if !nops_is(3) || !isRZ(0) || !isRZ(1) || !isRZ(2) || a_ops[0].w != 64 || a_ops[1].w != 64 || a_ops[2].w != 64 { return false; }
            a_word((if mn == "smulh" { 0x9B407C00 } else { 0x9BC07C00 }) | (rr(2) << 16) | (rr(1) << 5) | rr(0));
            return true;
        }
        if mn == "rbit" { return e_dp1(0); }
        if mn == "rev16" { return e_dp1(1); }
        if mn == "rev32" { if a_ops.len > 0 && a_ops[0].w != 64 { return false; } return e_dp1(2); }
        if mn == "rev" { return e_dp1(if a_ops.len > 0 && a_ops[0].w == 64 { 3 } else { 2 }); }
        if mn == "rev64" { if a_ops.len > 0 && a_ops[0].w != 64 { return false; } return e_dp1(3); }
        if mn == "clz" { return e_dp1(4); }
        if mn == "cls" { return e_dp1(5); }
        if mn == "csel" { return e_csel(0, 0); }
        if mn == "csinc" { return e_csel(0, 1); }
        if mn == "csinv" { return e_csel(1, 0); }
        if mn == "csneg" { return e_csel(1, 1); }
        if mn == "cset" || mn == "csetm" {
            if !nops_is(2) || !isRZ(0) { return false; }
            let c = a_cond(a_ops[1]);
            if c < 0 || c >= 14 { return false; }
            a_word((if mn == "cset" { 0x1A9F07E0 } else { 0x5A9F03E0 }) | (sf(0) << 31) | ((c ^ 1) << 12) | rr(0));
            return true;
        }
        if mn == "cinc" || mn == "cinv" || mn == "cneg" {
            if !nops_is(3) || !isRZ(0) || !isRZ(1) || !same_w(0, 1) { return false; }
            let c = a_cond(a_ops[2]);
            if c < 0 || c >= 14 { return false; }
            let op: i64 = if mn == "cinc" { 0 } else { 1 };
            let o2: i64 = if mn == "cinv" { 0 } else { 1 };
            a_word(0x1A800000 | (sf(0) << 31) | (op << 30) | (rr(1) << 16) | ((c ^ 1) << 12) | (o2 << 10) | (rr(1) << 5) | rr(0));
            return true;
        }
        if mn == "ccmp" { return e_ccmp(1); }
        if mn == "ccmn" { return e_ccmp(0); }
        if mn == "adc" { return e_adc(0, 0); }
        if mn == "adcs" { return e_adc(0, 1); }
        if mn == "sbc" { return e_adc(1, 0); }
        if mn == "sbcs" { return e_adc(1, 1); }
        if mn == "ngc" || mn == "ngcs" {
            if a_ops.len < 2 || !isR(0) { return false; }
            ins_zr(1, a_ops[0].w);
            return e_adc(1, if mn == "ngcs" { 1 } else { 0 });
        }
        if starts_with(mn, "crc32") {
            let t = mn[5..];
            var c: i64 = 0;
            var u = t;
            if t.len == 2 && t[0] == 'c' { c = 1; u = t[1..]; }
            if u == "b" { return e_crc(c, 0); }
            if u == "h" { return e_crc(c, 1); }
            if u == "w" { return e_crc(c, 2); }
            if u == "x" { return e_crc(c, 3); }
            return false;
        }
        if mn == "b" || mn == "bl" || starts_with(mn, "b.") || mn == "cbz" || mn == "cbnz" || mn == "tbz" || mn == "tbnz" ||
           mn == "br" || mn == "blr" || mn == "ret" || mn == "adr" {
            return e_branch(mn);
        }
        if mn == "prfm" { return e_prfm(); }
        if mn == "ldxr" || mn == "ldaxr" || mn == "stxr" || mn == "stlxr" || mn == "ldar" || mn == "stlr" || mn == "ldapr" ||
           mn == "ldxrb" || mn == "ldaxrb" || mn == "stxrb" || mn == "stlxrb" || mn == "ldarb" || mn == "stlrb" || mn == "ldaprb" ||
           mn == "ldxrh" || mn == "ldaxrh" || mn == "stxrh" || mn == "stlxrh" || mn == "ldarh" || mn == "stlrh" || mn == "ldaprh" ||
           mn == "ldxp" || mn == "ldaxp" || mn == "stxp" || mn == "stlxp" {
            return e_excl(mn);
        }
        if e_lse(mn) { return true; }
    }
    // loads and stores (any register class)
    if mn == "ldr" || mn == "str" || mn == "ldur" || mn == "stur" || mn == "ldrb" || mn == "strb" || mn == "ldrh" || mn == "strh" ||
       mn == "ldrsb" || mn == "ldrsh" || mn == "ldrsw" || mn == "ldurb" || mn == "sturb" || mn == "ldurh" || mn == "sturh" ||
       mn == "ldursb" || mn == "ldursh" || mn == "ldursw" {
        return e_ldst(mn);
    }
    if mn == "ldp" || mn == "stp" || mn == "ldpsw" { return e_ldstp(mn); }
    if e_system(mn) { return true; }
    if mn == "nop" || mn == "dmb" || mn == "dsb" || mn == "isb" || mn == "mrs" || mn == "msr" { return false; }
    // FP / SIMD
    if mn == "mov" { return e_mov(mn); }
    if mn == "fmov" { return e_fmov(); }
    if mn == "fcvt" { return e_fcvt(); }
    if mn == "fcmp" { return e_fcmp(0); }
    if mn == "fcmpe" { return e_fcmp(1); }
    if mn == "fcsel" { return e_fcsel(); }
    if mn == "fmadd" { return e_fp3(0, 0); }
    if mn == "fmsub" { return e_fp3(0, 1); }
    if mn == "fnmadd" { return e_fp3(1, 0); }
    if mn == "fnmsub" { return e_fp3(1, 1); }
    if isF(0) && (isF(1) || isR(1)) && a_ops.len == 2 {
        if mn == "scvtf" { return e_fcvti(0, 2); }
        if mn == "ucvtf" { return e_fcvti(0, 3); }
    }
    if isR(0) && isF(1) {
        let k = tbl_find(A_FCVTI, mn);
        if k >= 0 { return e_fcvti(A_FCVTI_RM[k], A_FCVTI_OP[k]); }
    }
    if isF(0) {
        let k2 = tbl_find(A_FP2, mn);
        if k2 >= 0 && a_ops.len == 3 && isF(2) { return e_fp2(k2); }
        let k1 = tbl_find(A_FP1, mn);
        if k1 >= 0 && a_ops.len == 2 && isF(1) { return e_fp1(k1); }
    }
    if mn == "dup" { return e_dup(); }
    if mn == "umov" { return e_umov(false); }
    if mn == "smov" { return e_umov(true); }
    if mn == "ins" { return e_ins(); }
    if mn == "movi" || mn == "mvni" || ((mn == "orr" || mn == "bic") && a_ops.len >= 2 && isI(1)) { return e_movi(mn); }
    if mn == "ext" { return e_vext(); }
    if mn == "tbl" { return e_tbl(0); }
    if mn == "tbx" { return e_tbl(1); }
    if mn.len == 3 && (starts_with(mn, "ld") || starts_with(mn, "st")) && mn[2] >= '1' && mn[2] <= '4' { return e_ldst_struct(mn); }
    if mn == "sdot" { return e_dot(0); }
    if mn == "udot" { return e_dot(1); }
    if starts_with(mn, "aes") || starts_with(mn, "sha") { return e_crypto(mn); }
    if mn == "sxtl" || mn == "sxtl2" { return e_vxtl(mn, 0); }
    if mn == "uxtl" || mn == "uxtl2" { return e_vxtl(mn, 1); }
    if mn == "uzp1" { return e_vperm(1); }
    if mn == "trn1" { return e_vperm(2); }
    if mn == "zip1" { return e_vperm(3); }
    if mn == "uzp2" { return e_vperm(5); }
    if mn == "trn2" { return e_vperm(6); }
    if mn == "zip2" { return e_vperm(7); }
    if (mn == "addp" || mn == "faddp") && nops_is(2) && isF(0) && isV(1) {
        if mn == "addp" {
            if a_ops[0].w != 64 || a_ops[1].w != 64 || a_ops[1].n != 2 { return false; }
            a_word(0x5EF1B800 | (rr(1) << 5) | rr(0));
            return true;
        }
        let w = a_ops[0].w;
        if (w != 32 && w != 64) || a_ops[1].w != w || a_ops[1].n != 2 { return false; }
        a_word(0x7E30D800 | ((if w == 64 { 1 } else { 0 }) << 22) | (rr(1) << 5) | rr(0));
        return true;
    }
    if mn == "fmaxv" { return e_vfacross(0, 0xF); }
    if mn == "fminv" { return e_vfacross(2, 0xF); }
    if mn == "fmaxnmv" { return e_vfacross(0, 0xC); }
    if mn == "fminnmv" { return e_vfacross(2, 0xC); }
    let ka = tbl_find(A_VACROSS, mn);
    if ka >= 0 { return e_vacross(mn, A_VACROSS_ENC[ka]); }
    // by element
    if a_ops.len == 3 && isE(2) {
        var base = mn;
        if ends_with2(mn) { base = mn[..mn.len - 1]; }
        let ke = tbl_find(A_VE, base);
        if ke >= 0 { return e_velem(mn, A_VE_ENC[ke]); }
        return false;
    }
    let kl = tbl_find(A_VLOG, mn);
    if kl >= 0 && isV(0) { return e_vlogic(kl); }
    let k3 = tbl_find(A_V3, mn);
    if k3 >= 0 && a_ops.len == 3 && (isV(2) || isF(2)) { return e_v3(A_V3_ENC[k3]); }
    let kf = tbl_find(A_VF3, mn);
    if kf >= 0 && a_ops.len == 3 && isV(2) { return e_vf3(A_VF3_ENC[kf]); }
    var base2 = mn;
    if ends_with2(mn) && tbl_find(A_V2, mn) < 0 { base2 = mn[..mn.len - 1]; }
    let k2 = tbl_find(A_V2, base2);
    if k2 >= 0 { return e_v2(mn, A_V2_ENC[k2]); }
    let ksh = tbl_find(A_VSH, base2);
    if ksh >= 0 { return e_vshift(mn, A_VSH_ENC[ksh]); }
    let kd = tbl_find(A_V3D, base2);
    if kd >= 0 { return e_v3d(mn, A_V3D_ENC[kd]); }
    if mn == "fcvtn" || mn == "fcvtn2" || mn == "fcvtxn" || mn == "fcvtxn2" {
        if !nops_is(2) || !isV(0) || !isV(1) || a_ops[1].w != 64 || a_ops[1].n != 2 || a_ops[0].w != 32 || (vq(0) == 1) != ends_with2(mn) { return false; }
        a_word((if starts_with(mn, "fcvtxn") { 0x2E616800 } else { 0x0E616800 }) | (vq(0) << 30) | (rr(1) << 5) | rr(0));
        return true;
    }
    if mn == "fcvtl" || mn == "fcvtl2" {
        if !nops_is(2) || !isV(0) || !isV(1) || a_ops[0].w != 64 || a_ops[0].n != 2 || a_ops[1].w != 32 || (vq(1) == 1) != ends_with2(mn) { return false; }
        a_word(0x0E617800 | (vq(1) << 30) | (rr(1) << 5) | rr(0));
        return true;
    }
    return false;
}
