// goosecc: the layout oracle. --layout-check writes a C file that includes
// the translation unit and asserts, for every complete struct/union with a
// file-scope name (tag or typedef) and every file-scope typedef, the size,
// the alignment and the offset of each named member as goosecc computed
// them. clang-20 must accept the file.

import std;
import os;
import .common;
import .types;
import .ast;
import .expr;

var lc: u8[>..] = [];
var lc_count: i64 = 0;

fn lc_guard_open(names_: const u8[:]) {
    // #if !defined(a) && !defined(b) ...: a macro of the same name would change the meaning
    lc.append("#if 1");
    var i = 0;
    while i < names_.len {
        var j = i;
        while j < names_.len && names_[j] != ' ' { j++; }
        if j > i {
            lc.append(" && !defined(");
            lc.append(names_[i..j]);
            lc.push(')');
        }
        i = j + 1;
    }
    lc.push('\n');
}

var lc_names: u8[>..] = [];
var lc_tname: u8[>..] = [];

fn emit_assert(expr_: const u8[:], value: i64, what: const u8[:]) {
    lc.append("_Static_assert(");
    lc.append(expr_);
    format(lc, " == ", value, ", \"goosecc layout: ");
    for c in what {
        if c == '"' || c == '\\' { lc.push('\\'); }
        lc.push(c);
    }
    lc.append("\");\n");
    lc_count++;
}

var lc_expr: u8[>..] = [];

// The record's fields, with anonymous members' fields at their full offsets.
recursive fn emit_fields(r: i64, base_off: i64, depth: i64) {
    let rec = records[r];
    for i in rec.first..rec.first + rec.count {
        let f = fields[i];
        if f.flags & FF_ANON != 0 && depth < 6 {
            emit_fields(rec_of(f.ty), base_off + f.offset, depth + 1);
            continue;
        }
        if f.name == 0 || f.width >= 0 { continue; }
        let fname = ident_text(f.name as i64);
        lc_names.clear();
        lc_names.append(lc_tname);
        lc_names.push(' ');
        lc_names.append(fname);
        lc_guard_open(lc_names);
        lc_expr.clear();
        lc_expr.append("__builtin_offsetof(");
        lc_expr.append(lc_full);
        lc_expr.append(", ");
        lc_expr.append(fname);
        lc_expr.push(')');
        lc_what.clear();
        lc_what.append(lc_full);
        lc_what.push('.');
        lc_what.append(fname);
        emit_assert(lc_expr, base_off + f.offset, lc_what);
        lc.append("#endif\n");
    }
}

var lc_full: u8[>..] = [];
var lc_what: u8[>..] = [];

fn emit_size_align(full: const u8[:], size: i64, align: i64) {
    lc_guard_open(lc_tname);
    lc_expr.clear();
    lc_expr.append("sizeof(");
    lc_expr.append(full);
    lc_expr.push(')');
    lc_what.clear();
    lc_what.append("sizeof ");
    lc_what.append(full);
    emit_assert(lc_expr, size, lc_what);
    lc_expr.clear();
    lc_expr.append("_Alignof(");
    lc_expr.append(full);
    lc_expr.push(')');
    lc_what.clear();
    lc_what.append("alignof ");
    lc_what.append(full);
    emit_assert(lc_expr, align, lc_what);
    lc.append("#endif\n");
}

recursive fn is_checkable(t: u32) -> bool {
    let k = kind_of(t);
    if k == TY_VOID || k == TY_FUNC || k == TY_VLA { return false; }
    if !is_complete(t) { return false; }
    if k == TY_ARRAY { return is_checkable(tbase(t)); }
    return true;
}

fn write_layout_check(input: const u8[:], out_path: const u8[:]) -> bool {
    lc.append("/* goosecc --layout-check: generated */\n#include \"");
    lc.append(input);
    lc.append("\"\n");
    // records named by a file-scope typedef (for anonymous ones)
    var rec_typedef: i32[>..] = [];
    for r in records.len { rec_typedef.push(-1); }
    for s, i in syms {
        if s.kind == SK_TYPEDEF && s.scope == 0 && s.name != 0 && is_record(s.ty) && quals(s.ty) == 0 {
            let r = rec_of(s.ty);
            if types[s.ty >> 4].flags & TF_ALIGNED == 0 && rec_typedef[r] < 0 { rec_typedef[r] = i as! i32; }
        }
    }
    // tags declared at file scope
    var rec_tag: bool[>..] = [];
    for r in records.len { rec_tag.push(false); }
    for s in syms {
        if s.kind == SK_TAG && s.scope == 0 && s.name != 0 {
            let t = qt(s.v, 0);
            if is_record(t) { rec_tag[rec_of(t)] = true; }
        }
    }
    for rec, r in records {
        if r == 0 { continue; }    // __va_list_tag
        if rec.flags & RF_COMPLETE == 0 { continue; }
        lc_full.clear();
        lc_tname.clear();
        if rec.name != 0 && rec_tag[r] {
            lc_full.append(if rec.flags & RF_UNION != 0 { "union " } else { "struct " });
            lc_full.append(ident_text(rec.name as i64));
            lc_tname.append(ident_text(rec.name as i64));
        } else if rec_typedef[r] >= 0 {
            lc_full.append(sym_name(rec_typedef[r] as i64));
            lc_tname.append(sym_name(rec_typedef[r] as i64));
        } else {
            continue;
        }
        emit_size_align(lc_full, rec.size, rec.align as i64);
        emit_fields(r, 0, 0);
    }
    // typedefs
    for s in syms {
        if s.kind != SK_TYPEDEF || s.scope != 0 || s.name == 0 { continue; }
        if !is_checkable(s.ty) { continue; }
        lc_full.clear();
        lc_full.append(ident_text(s.name as i64));
        lc_tname.clear();
        lc_tname.append(lc_full);
        emit_size_align(lc_full, type_size(s.ty), type_align(s.ty));
    }
    format(lc, "/* ", lc_count, " assertions */\n");
    return write_file(out_path, lc);
}
