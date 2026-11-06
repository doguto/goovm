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
import dictionary;
import .builtins;

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

// ---------------------------------------------------------------------------
// Naming arbitrary types for the declared-type checks: each type gets a
// typedef __goosecc_tN built on the typedefs of its parts, so no nested
// declarator syntax is needed.

var tref = dictionary<u32, i64> {};
var tdefs: u8[>..] = [];
var tref_next: i64 = 0;
var tref_stack: i64[>..<] = [];
var rec_name_sym: i32[>..] = [];     // record -> file-scope typedef naming it (-1)
var rec_tag_ok: bool[>..] = [];      // record has a file-scope tag
var enum_name_sym: i32[>..] = [];
var enum_tag_ok: bool[>..] = [];

fn tref_name(out: u8[>..]&, n: i64) { format(out, "__goosecc_t", n); }

// The typedef number naming q, or -1 when q cannot be named at file scope.
recursive fn type_ref(q: u32) -> i64 {
    let known = tref.get(q);
    if known { return known; }
    var r: i64 = -1;
    let t = types[q >> 4];
    let k = t.kind as i64;
    let qs = quals(q);
    if qs != 0 {
        let b = type_ref(unqual(q));
        if b >= 0 {
            r = tref_next;
            tref_next++;
            tdefs.append("typedef ");
            if qs & Q_ATOMIC != 0 { tdefs.append("_Atomic("); tref_name(tdefs, b); tdefs.append(") "); }
            if qs & Q_CONST != 0 { tdefs.append("const "); }
            if qs & Q_VOLATILE != 0 { tdefs.append("volatile "); }
            if qs & Q_ATOMIC == 0 { tref_name(tdefs, b); }
            if qs & Q_RESTRICT != 0 { tdefs.append(" restrict"); }
            tdefs.push(' ');
            tref_name(tdefs, r);
            tdefs.append(";\n");
        }
        tref.insert(q, r);
        return r;
    }
    if t.flags & TF_ALIGNED != 0 {
        let b = type_ref(qt(t.canon as i64, 0));
        if b >= 0 {
            r = tref_next;
            tref_next++;
            tdefs.append("typedef ");
            tref_name(tdefs, b);
            tdefs.push(' ');
            tref_name(tdefs, r);
            format(tdefs, " __attribute__((aligned(", t.align, ")));\n");
        }
        tref.insert(q, r);
        return r;
    }
    if k == TY_POINTER || k == TY_ARRAY || k == TY_VECTOR || k == TY_EXTVECTOR {
        let b = type_ref(t.base);
        if b >= 0 {
            r = tref_next;
            tref_next++;
            tdefs.append("typedef ");
            tref_name(tdefs, b);
            tdefs.push(' ');
            if k == TY_POINTER { tdefs.push('*'); }
            tref_name(tdefs, r);
            if k == TY_ARRAY {
                if t.n >= 0 { format(tdefs, "[", t.n, "]"); } else { tdefs.append("[]"); }
            }
            if k == TY_VECTOR { format(tdefs, " __attribute__((vector_size(", type_size(q), ")))"); }
            if k == TY_EXTVECTOR { format(tdefs, " __attribute__((ext_vector_type(", t.n, ")))"); }
            tdefs.append(";\n");
        }
        tref.insert(q, r);
        return r;
    }
    if k == TY_FUNC {
        let rb = type_ref(t.base);
        var ok = rb >= 0;
        let mark = tref_stack.len;
        for i in t.n {
            let p = type_ref(tparams[t.extra + i]);
            if p < 0 { ok = false; }
            tref_stack.push(p);
        }
        if ok {
            r = tref_next;
            tref_next++;
            tdefs.append("typedef ");
            tref_name(tdefs, rb);
            tdefs.push(' ');
            tref_name(tdefs, r);
            tdefs.push('(');
            if t.flags & TF_NOPROTO == 0 {
                if t.n == 0 && t.flags & TF_VARIADIC == 0 { tdefs.append("void"); }
                for i in t.n {
                    if i > 0 { tdefs.append(", "); }
                    tref_name(tdefs, tref_stack[mark + i]);
                }
                if t.flags & TF_VARIADIC != 0 { tdefs.append(if t.n > 0 { ", ..." } else { "..." }); }
            }
            tdefs.append(");\n");
        }
        tref_stack.resize(mark);
        tref.insert(q, r);
        return r;
    }
    // named and basic types
    lc_expr.clear();
    if k == TY_STRUCT || k == TY_UNION {
        let ri = t.extra as i64;
        let rec = records[ri];
        if ri > 0 && rec.name != 0 && rec_tag_ok[ri] {
            lc_expr.append(if k == TY_UNION { "union " } else { "struct " });
            lc_expr.append(ident_text(rec.name as i64));
        } else if ri > 0 && rec_name_sym[ri] >= 0 {
            lc_expr.append(sym_name(rec_name_sym[ri] as i64));
        } else if ri == 0 {
            // the builtin struct __va_list_tag cannot be named by its tag
            lc_expr.append("__typeof__((*(__builtin_va_list *)0)[0])");
        }
    } else if k == TY_ENUM {
        let ei = t.extra as i64;
        let e = enums[ei];
        if e.name != 0 && enum_tag_ok[ei] {
            lc_expr.append("enum ");
            lc_expr.append(ident_text(e.name as i64));
        } else if enum_name_sym[ei] >= 0 {
            lc_expr.append(sym_name(enum_name_sym[ei] as i64));
        }
    } else if k != TY_VLA {
        base_name(lc_expr, q);
    }
    if lc_expr.len > 0 {
        r = tref_next;
        tref_next++;
        tdefs.append("typedef ");
        tdefs.append(lc_expr);
        tdefs.push(' ');
        tref_name(tdefs, r);
        tdefs.append(";\n");
    }
    tref.insert(q, r);
    return r;
}

var dc: u8[>..] = [];       // the declared-type assertions
var dc_count: i64 = 0;

fn decl_type_check(name: const u8[:], expr_: const u8[:], ty: u32, guard_names: const u8[:]) {
    let r = type_ref(ty);
    if r < 0 { return; }
    let save = lc.len;
    lc_guard_open(guard_names);
    // move the guard line from lc to dc
    dc.append(lc[save..]);
    lc.resize(save);
    dc.append("_Static_assert(__builtin_types_compatible_p(__typeof__(");
    dc.append(expr_);
    dc.append("), ");
    tref_name(dc, r);
    dc.append("), \"goosecc type: ");
    for c in name { if c == '"' || c == '\\' { dc.push('\\'); } dc.push(c); }
    dc.append("\");\n#endif\n");
    dc_count++;
}

fn write_layout_check(input: const u8[:], out_path: const u8[:]) -> bool {
    lc.append("/* goosecc --layout-check: generated */\n#include \"");
    lc.append(input);
    lc.append("\"\n");
    // the TU may have redefined keywords as macros (#define float double)
    for kwd in ["float", "double", "int", "char", "short", "long", "signed", "unsigned", "void", "_Bool", "const",
                "volatile", "restrict", "struct", "union", "enum", "__typeof__", "_Complex", "_Atomic", "__int128",
                "__float128", "_Float16", "__bf16", "__attribute__", "sizeof", "_Alignof", "_Static_assert",
                "__builtin_offsetof", "__builtin_types_compatible_p", "__builtin_va_list", "typedef", "aligned",
                "vector_size", "ext_vector_type"] {
        lc.append("#undef ");
        lc.append(kwd);
        lc.push('\n');
    }
    // records and enums named by a file-scope typedef (for anonymous ones),
    // and those with a file-scope tag
    for r in records.len { rec_name_sym.push(-1); rec_tag_ok.push(false); }
    for e in enums.len { enum_name_sym.push(-1); enum_tag_ok.push(false); }
    for s, i in syms {
        if s.kind == SK_TYPEDEF && s.scope == 0 && s.name != 0 && quals(s.ty) == 0 && types[s.ty >> 4].flags & TF_ALIGNED == 0 {
            if is_record(s.ty) {
                let r = rec_of(s.ty);
                if rec_name_sym[r] < 0 { rec_name_sym[r] = i as! i32; }
            } else if kind_of(s.ty) == TY_ENUM {
                let e = types[s.ty >> 4].extra as i64;
                if enum_name_sym[e] < 0 { enum_name_sym[e] = i as! i32; }
            }
        }
        if s.kind == SK_TAG && s.scope == 0 && s.name != 0 {
            let t = qt(s.v, 0);
            if is_record(t) { rec_tag_ok[rec_of(t)] = true; }
            if kind_of(t) == TY_ENUM { enum_tag_ok[types[t >> 4].extra] = true; }
        }
    }
    for rec, r in records {
        if r == 0 { continue; }    // __va_list_tag
        if rec.flags & RF_COMPLETE == 0 { continue; }
        lc_full.clear();
        lc_tname.clear();
        if rec.name != 0 && rec_tag_ok[r] {
            lc_full.append(if rec.flags & RF_UNION != 0 { "union " } else { "struct " });
            lc_full.append(ident_text(rec.name as i64));
            lc_tname.append(ident_text(rec.name as i64));
        } else if rec_name_sym[r] >= 0 {
            lc_full.append(sym_name(rec_name_sym[r] as i64));
            lc_tname.append(sym_name(rec_name_sym[r] as i64));
        } else {
            continue;
        }
        emit_size_align(lc_full, rec.size, rec.align as i64);
        emit_fields(r, 0, 0);
        // member types
        for i in rec.first..rec.first + rec.count {
            let f = fields[i];
            if f.name == 0 || f.width >= 0 { continue; }
            let fname = ident_text(f.name as i64);
            lc_names.clear();
            lc_names.append(lc_tname);
            lc_names.push(' ');
            lc_names.append(fname);
            lc_what.clear();
            lc_what.append("((");
            lc_what.append(lc_full);
            lc_what.append(" *)0)->");
            lc_what.append(fname);
            decl_type_check(lc_what, lc_what, f.ty, lc_names);
        }
    }
    // typedefs
    for s in syms {
        if s.kind != SK_TYPEDEF || s.scope != 0 || s.name == 0 { continue; }
        lc_full.clear();
        lc_full.append(ident_text(s.name as i64));
        lc_tname.clear();
        lc_tname.append(lc_full);
        if is_checkable(s.ty) { emit_size_align(lc_full, type_size(s.ty), type_align(s.ty)); }
    }
    // declared types of the file-scope objects and functions
    for s, i in syms {
        if (s.kind != SK_VAR && s.kind != SK_FUNC) || s.scope != 0 || s.name == 0 { continue; }
        if s.flags & (SF_IMPLICIT | SF_COMPLIT) != 0 { continue; }
        if lookup_ord(s.name) != i { continue; }
        if builtin_index(s.name) >= 0 { continue; }    // typeof of a builtin is an error
        let nm = ident_text(s.name as i64);
        decl_type_check(nm, nm, s.ty, nm);
    }
    lc.append(tdefs);
    lc.append(dc);
    format(lc, "/* ", lc_count + dc_count, " assertions */\n");
    return write_file(out_path, lc);
}
