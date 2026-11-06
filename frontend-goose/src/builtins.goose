// goosecc: builtin functions. Their types come from clang-20 (generated
// into builtins_gen.goose); those that clang checks by hand (shown there
// with a '()' type) get their result type computed here.

import std;
import dictionary;
import .common;
import .lex;
import .types;
import .ast;
import .sema;
import .builtins_gen;

let BI_CALL = 1;          // a = builtin symbol, v/c = arguments
let BI_IMAG_CONST = 2;    // a GNU imaginary constant: a = the real-typed literal
let BI_BITCAST = 3;       // __builtin_bit_cast
let BI_CONVERTVECTOR = 4; // __builtin_convertvector

struct BuiltinEnt { name: u32, toff: u32, tlen: u32, flags: u8, typed: bool, ty: u32, custom: bool }
var bentries: BuiltinEnt[>..] = [];
var bmap = dictionary<u32, i64> {};
var bloaded: bool = false;

fn load_builtins() {
    bloaded = true;
    let text = BUILTIN_TYPES;
    var i = 0;
    while i < text.len {
        var j = i;
        while j < text.len && text[j] != '|' && text[j] != '\n' { j++; }
        let nm = text[i..j];
        j++;
        let ts = j;
        while j < text.len && text[j] != '|' && text[j] != '\n' { j++; }
        let te = j;
        var fl: u8 = 0;
        if j < text.len && text[j] == '|' {
            j++;
            while j < text.len && text[j] != '\n' {
                if text[j] == 'n' { fl = fl | 1; }
                j++;
            }
        }
        if nm.len > 0 {
            let id = intern(nm);
            bmap.insert(id, bentries.len);
            bentries.push(BuiltinEnt { name: id, toff: ts as! u32, tlen: (te - ts) as! u32, flags: fl, typed: false, ty: 0, custom: false });
        }
        i = j + 1;
    }
}

fn builtin_index(id: u32) -> i64 {
    if !bloaded { load_builtins(); }
    let r = bmap.get(id);
    if r { return r; }
    return -1;
}

fn is_library_name(name: const u8[:]) -> bool {
    if starts_with(name, "__builtin_") || starts_with(name, "__sync_") || starts_with(name, "__atomic_") ||
       starts_with(name, "__c11_") || starts_with(name, "__opencl") || starts_with(name, "__scoped") ||
       starts_with(name, "__nvvm") || starts_with(name, "__hip") || starts_with(name, "__arithmetic_fence") ||
       starts_with(name, "__rdtsc") || starts_with(name, "_mm_") { return false; }
    return true;
}

// Lexes s into tokens appended to tu_toks (after the translation unit's
// EOF) and returns the index of the first.
fn lex_string_tokens(s: const u8[:]) -> i64 {
    let start = src.len;
    src.append(s);
    let end = src.len;
    src.push('\n');
    src.push(0);
    lx_pos = start;
    lx_end = end;
    lx_flags = 0;
    lx_dir = false;
    let first = tu_toks.len;
    loop {
        var t = lex_file_token();
        if t.kind == TK_EOF { tu_toks.push(t); break; }
        if t.kind == TK_IDENT && idents[t.val].kw != 0 { t.kind = (TK_KW + (idents[t.val].kw as i64)) as! u8; }
        tu_toks.push(t);
    }
    return first;
}

var bt_name: u8[>..] = [];

// The function type of builtin entry b (parsed on first use).
recursive fn builtin_type(b: i64) -> u32 {
    if bentries[b].typed { return bentries[b].ty; }
    bentries[b].typed = true;
    let text = BUILTIN_TYPES[bentries[b].toff..bentries[b].toff + bentries[b].tlen];
    let first = lex_string_tokens(text);
    let save = pc;
    pc = first;
    let e0 = n_errors;
    diag_suppress++;
    let ty = parse_type_name();
    diag_suppress--;
    let failed = diag_suppressed_errors > 0 || !at(TK_EOF) || !is_func(ty);
    diag_suppressed_errors = 0;
    pc = save;
    if failed {
        bentries[b].custom = true;
        bentries[b].ty = 0;
        return 0;
    }
    var t = ty;
    if types[ty >> 4].flags & TF_NOPROTO != 0 { bentries[b].custom = true; }
    bentries[b].ty = t;
    return t;
}

// An undeclared identifier: a builtin, or an implicitly declared function
// when it is called. Returns the symbol or -1.
recursive fn builtin_or_implicit(id: u32, loc: u32, call: bool) -> i64 {
    let b = builtin_index(id);
    let name = ident_text(id as i64);
    if b >= 0 {
        let lib = is_library_name(name);
        if lib && !call { return -1; }
        var ty = builtin_type(b);
        let custom = bentries[b].custom;
        if ty == 0 {
            // unparsable: an untyped builtin returning int
            fn_scratch.clear();
            ty = qt(mk_type(TY_FUNC, TF_NOPROTO, t_int, 0, 0, 0) as i64, 0);
        }
        let s = new_sym(if lib { SK_FUNC } else { SK_BUILTIN }, id, ty, loc);
        syms[s].v = b;
        syms[s].sc = SC_EXTERN;
        syms[s].flags = SF_FILESCOPE;
        if bentries[b].flags & 1 != 0 { syms[s].flags = syms[s].flags | SF_NORETURN; }
        if lib {
            syms[s].flags = syms[s].flags | SF_IMPLICIT;
            implicit_fn(loc, str("call to undeclared library function '", name, "'"));
        }
        if custom { syms[s].flags = syms[s].flags | SF_IMPLICIT; }
        bind_file_scope(s);
        return s;
    }
    if call {
        implicit_fn(loc, str("call to undeclared function '", name, "'; ISO C99 and later do not support implicit function declarations"));
        fn_scratch.clear();
        let ty = qt(mk_type(TY_FUNC, TF_NOPROTO, t_int, 0, 0, 0) as i64, 0);
        let s = new_sym(SK_FUNC, id, ty, loc);
        syms[s].sc = SC_EXTERN;
        syms[s].flags = SF_FILESCOPE | SF_IMPLICIT;
        bind_file_scope(s);
        return s;
    }
    return -1;
}

// Binds s at file scope although inner scopes may be open (the name has
// no binding at all).
fn bind_file_scope(s: i64) {
    ensure_ids();
    let name = syms[s].name as i64;
    syms[s].prev = -1;
    syms[s].scope = 0;
    if scope_depth == 0 {
        id_ord[name] = s as! i32;
        scope_log.push(s as! u32);
        return;
    }
    id_ord[name] = s as! i32;
    late_file_syms.push(s as! u32);
}
var late_file_syms: u32[>..] = [];

fn arg(mark: i64, i: i64) -> u32 { nscratch[mark + i] }

// A call of builtin symbol s with arguments nscratch[mark..]. Returns the
// node, or 0 to check it as an ordinary call against its declared type.
fn builtin_call(s: i64, mark: i64, loc: u32) -> u32 {
    let b = syms[s].v;
    let name = sym_name(s);
    let nargs = nscratch.len - mark;
    let ty = syms[s].ty;
    let ft = types[ty >> 4];
    var rt = unqual(ft.base);
    if !bentries[b].custom {
        // typed: check like a call, but keep it a builtin node
        let proto = ft.flags & TF_NOPROTO == 0;
        if proto {
            if nargs < ft.n { err_at(loc, str("too few arguments to function call, expected ", ft.n, ", have ", nargs)); }
            else if nargs > ft.n && ft.flags & TF_VARIADIC == 0 { err_at(loc, str("too many arguments to function call, expected ", ft.n, ", have ", nargs)); }
        }
        let va_start = name == "__builtin_va_start" || name == "__builtin_c23_va_start";
        for i in nargs {
            let a = arg(mark, i);
            if nodes[a].kind == N_ERROR { continue; }
            // clang leaves va_start's second argument as it is
            if va_start && i == 1 { continue; }
            var c = rv(a);
            if proto && i < ft.n {
                let pt = unqual(tparams[ft.extra + i]);
                // va_list parameters take the decayed array
                c = assign_convert(c, pt, nodes[a].loc, 2);
            } else {
                c = default_promote_b(c);
            }
            nscratch[mark + i] = c;
        }
        let start = commit_list(mark);
        return node_v(N_BUILTIN, BI_CALL, rt, s, 0, nargs, loc, start);
    }
    // custom-checked builtins: convert the arguments to rvalues
    for i in nargs {
        let a = arg(mark, i);
        if nodes[a].kind != N_ERROR { nscratch[mark + i] = rv(a); }
    }
    let a0t: u32 = if nargs > 0 { nty(arg(mark, 0)) } else { t_int };
    if name == "__builtin_constant_p" {
        var v: i64 = 0;
        if nargs == 1 {
            let x = arg(mark, 0);
            let ok, iv = fold_int(x);
            let ok2, fv = fold_float(x);
            if ok || ok2 { v = 1; }
        }
        nscratch.resize(mark);
        let n = node_v(N_INT, 0, t_int, 0, 0, 0, loc, v);
        nodes[n].flags = NF_ICE;
        return n;
    }
    if name == "__builtin_classify_type" {
        var v: i64 = 0;
        if nargs == 1 {
            let t = nty(arg(mark, 0));
            let k = kind_of(t);
            v = match k {
                TY_VOID => 0, TY_BOOL => 4, TY_CHAR, TY_SCHAR, TY_UCHAR => 1, TY_ENUM => 3,
                TY_POINTER => 5, TY_STRUCT => 12, TY_UNION => 13, TY_COMPLEX => 9, TY_ARRAY => 5, TY_FUNC => 5,
                TY_VECTOR, TY_EXTVECTOR => 18,
                _ => if is_real_float(t) { 8 } else { 1 },
            };
        }
        nscratch.resize(mark);
        let n = node_v(N_INT, 0, t_int, 0, 0, 0, loc, v);
        nodes[n].flags = NF_ICE;
        return n;
    }
    if starts_with(name, "__sync_") || starts_with(name, "__atomic_") || starts_with(name, "__c11_atomic_") {
        let pointee = if is_pointer(a0t) { unqual(tbase(a0t)) } else { t_int };
        if ends_with(name, "bool_compare_and_swap") || ends_with(name, "compare_exchange") ||
           ends_with(name, "compare_exchange_n") || ends_with(name, "compare_exchange_strong") ||
           ends_with(name, "compare_exchange_weak") || ends_with(name, "test_and_set") ||
           ends_with(name, "lock_free") {
            rt = t_bool;
        } else if name == "__sync_synchronize" || name == "__sync_lock_release" || ends_with(name, "_fence") ||
                  name == "__atomic_clear" || name == "__atomic_load" || name == "__atomic_store" ||
                  name == "__atomic_store_n" || name == "__atomic_exchange" || name == "__c11_atomic_store" ||
                  name == "__c11_atomic_init" {
            rt = t_void;
        } else {
            rt = pointee;
        }
    } else if name == "__builtin_add_overflow" || name == "__builtin_sub_overflow" || name == "__builtin_mul_overflow" ||
              name == "__builtin_mul_overflow_p" || name == "__builtin_add_overflow_p" || name == "__builtin_sub_overflow_p" {
        rt = t_bool;
    } else if name == "__builtin_shufflevector" {
        if nargs >= 2 && is_vector(a0t) {
            rt = qt(mk_type(kind_of(a0t), 0, unqual(tbase(a0t)), nargs - 2, 0, 0) as i64, 0);
        }
    } else if starts_with(name, "__builtin_elementwise_") || name == "__builtin_nondeterministic_value" {
        rt = unqual(a0t);
        if ends_with(name, "_popcount") && false { rt = a0t; }
    } else if starts_with(name, "__builtin_reduce_") {
        rt = if is_vector(a0t) { unqual(tbase(a0t)) } else { a0t };
    } else if name == "__builtin_assume_aligned" {
        rt = t_voidptr;
    } else if name == "__builtin_call_with_static_chain" {
        rt = if nargs > 0 { a0t } else { t_int };
    } else if name == "__builtin_launder" || name == "__builtin_preserve_access_index" {
        rt = unqual(a0t);
    } else if name == "__builtin_memcpy_inline" || name == "__builtin_memset_inline" {
        rt = t_void;
    } else if starts_with(name, "__builtin_stdc_") {
        rt = t_uint;
        if ends_with(name, "_bit_floor") || ends_with(name, "_bit_ceil") { rt = promoted_type_of(a0t); }
        if ends_with(name, "has_single_bit") { rt = t_bool; }
    } else if name == "__builtin_counted_by_ref" || name == "__builtin_get_vtable_pointer" {
        rt = t_voidptr;
    }
    // otherwise the declared result type (int for __builtin_isnan & co.)
    let start = commit_list(mark);
    return node_v(N_BUILTIN, BI_CALL, rt, s, 0, nargs, loc, start);
}

fn promoted_type_of(t: u32) -> u32 {
    if int_rank(t) < 4 { return t_int; }
    return unqual(t);
}

fn default_promote_b(n: u32) -> u32 {
    let t = nty(n);
    if kind_of(t) == TY_FLOAT { return icast(n, CK_FLOATCAST, t_double); }
    if is_integer(t) { return promote(n); }
    return n;
}
