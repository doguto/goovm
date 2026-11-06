// goosecc: initializers (C11 6.7.9). An initializer is parsed into a
// syntactic tree first; a walk over it then resolves designators and brace
// elision into a flat list of (subobject path, value) entries, and the
// entries are built into the semantic N_INITLIST tree: one child per
// member or element (N_ZEROINIT where nothing was given), so that lowering
// needs no knowledge of designators.

import std;
import .common;
import .types;
import .ast;
import .sema;
import .expr;
import .parse;

// ---------------------------------------------------------------------------
// Syntax

let D_ITEM = 0;     // a designated item: v/c = designators, a = value
let D_FIELD = 1;    // .name (a = ident)
let D_INDEX = 2;    // [e] (a = expr)
let D_RANGE = 3;    // [lo ... hi] (a, b)

recursive fn parse_init_syntax() -> u32 {
    if !at(TK_L_BRACE) { return parse_assign(); }
    let loc = tloc();
    adv();
    let mark = nscratch.len;
    while !at(TK_R_BRACE) && !at(TK_EOF) {
        let iloc = tloc();
        let dmark = nscratch.len;
        var designated = false;
        if at(TK_IDENT) && tk_n(1) == TK_COLON {
            // obsolete GNU "field: value"
            nscratch.push(node(N_DESIG, D_FIELD, 0, tval() as i64, 0, 0, iloc));
            adv();
            adv();
            designated = true;
        } else {
            loop {
                if at(TK_PERIOD) {
                    adv();
                    if !at(TK_IDENT) && tk() < TK_KW { err("expected a field designator"); break; }
                    nscratch.push(node(N_DESIG, D_FIELD, 0, tval() as i64, 0, 0, tloc()));
                    adv();
                    designated = true;
                } else if at(TK_L_SQUARE) {
                    let dl = tloc();
                    adv();
                    let e = parse_cond();
                    if at(TK_ELLIPSIS) {
                        adv();
                        let e2 = parse_cond();
                        nscratch.push(node(N_DESIG, D_RANGE, 0, e as i64, e2 as i64, 0, dl));
                    } else {
                        nscratch.push(node(N_DESIG, D_INDEX, 0, e as i64, 0, 0, dl));
                    }
                    expect(TK_R_SQUARE, "']'");
                    designated = true;
                } else {
                    break;
                }
            }
            if designated {
                if !accept(TK_EQUAL) {
                    // GNU allows a missing '=' after an array designator
                }
            }
        }
        let dcount = nscratch.len - dmark;
        let dstart = commit_list(dmark);
        let v = parse_init_syntax();
        if designated {
            nscratch.push(node_v(N_DESIG, D_ITEM, 0, v as i64, 0, dcount, iloc, dstart));
        } else {
            nscratch.push(v);
        }
        if !accept(TK_COMMA) { break; }
    }
    expect(TK_R_BRACE, "'}'");
    let count = nscratch.len - mark;
    let start = commit_list(mark);
    return node_v(N_SYNINIT, 0, 0, 0, 0, count, loc, start);
}

// ---------------------------------------------------------------------------
// The walk: designators and brace elision.

struct IEnt { pstart: u32, plen: u32, val: u32 }
var ients: IEnt[>..<] = [];
var ipath: i64[>..<] = [];

struct Frame { ty: u32, idx: i64, count: i64 }
var ifr: Frame[>..<] = [];
var root_max: i64 = 0;       // for an incomplete root array: max index + 1
var flex_max: i64 = 0;

// Number of subobjects of t (-1 = unbounded).
fn sub_count(t: u32) -> i64 {
    let k = kind_of(t);
    if k == TY_ARRAY { return types[t >> 4].n; }
    if k == TY_VECTOR || k == TY_EXTVECTOR { return types[t >> 4].n; }
    if k == TY_STRUCT || k == TY_UNION { return records[rec_of(t)].count as i64; }
    if k == TY_VLA { return -1; }
    return 0;
}

fn sub_type(t: u32, i: i64) -> u32 {
    let k = kind_of(t);
    if k == TY_STRUCT || k == TY_UNION {
        let f = fields[records[rec_of(t)].first + i];
        return with_quals(f.ty, quals(t));
    }
    return with_quals(tbase(t), quals(t));
}

fn is_init_aggregate(t: u32) -> bool {
    let k = kind_of(t);
    return k == TY_ARRAY || k == TY_STRUCT || k == TY_UNION || k == TY_VECTOR || k == TY_EXTVECTOR || k == TY_VLA;
}

// The first initializable member at or after i (unnamed bit-fields are skipped).
fn next_member(t: u32, i: i64) -> i64 {
    let k = kind_of(t);
    if k != TY_STRUCT && k != TY_UNION { return i; }
    let r = records[rec_of(t)];
    var j = i;
    while j < r.count as i64 {
        let f = fields[r.first + j];
        if f.name != 0 || f.flags & FF_ANON != 0 { return j; }
        j++;
    }
    return j;
}

fn frame_exhausted(f: Frame) -> bool {
    if f.count < 0 { return false; }
    return f.idx >= f.count;
}

// Moves to the next subobject after an initialization.
fn advance(base_depth: i64) {
    let top = ifr.len - 1;
    let t = ifr[top].ty;
    if kind_of(t) == TY_UNION {
        ifr[top].idx = ifr[top].count;
    } else {
        ifr[top].idx = next_member(t, ifr[top].idx + 1);
    }
    while ifr.len - 1 > base_depth && frame_exhausted(ifr[ifr.len - 1]) {
        ifr.pop();
        let p = ifr.len - 1;
        let pt = ifr[p].ty;
        if kind_of(pt) == TY_UNION { ifr[p].idx = ifr[p].count; } else { ifr[p].idx = next_member(pt, ifr[p].idx + 1); }
    }
}

// Records val for the subobject the frames designate (full path from the root).
fn record_entry(base_depth: i64, val: u32) {
    let ps = ipath.len;
    for j in 0..ifr.len { ipath.push(ifr[j].idx); }
    ients.push(IEnt { pstart: ps as! u32, plen: ifr.len as! u32, val: val });
}

fn strip_parens(n: u32) -> u32 { n }

fn is_string_for(t: u32, val: u32) -> bool {
    if nodes[val].kind != N_STRING { return false; }
    if kind_of(t) != TY_ARRAY { return false; }
    let et = tbase(t);
    if !is_integer(et) { return false; }
    let se = strs[nodes[val].a].elem;
    let es = type_size(et);
    if es != type_size(se) { return false; }
    if es == 1 { return true; }
    return true;
}

// Initializes the subobject the top frame designates with `val`,
// descending for brace elision. Entries are relative to base_depth.
recursive fn assign_value(val: u32, base_depth: i64, tail: u32) {
    loop {
        let top = ifr.len - 1;
        let f = ifr[top];
        if frame_exhausted(f) {
            if top == base_depth {
                warn(nodes[val].loc, "excess elements in initializer");
                return;
            }
            return;
        }
        let st = sub_type(f.ty, f.idx);
        if nodes[val].kind == N_SYNINIT {
            if is_init_aggregate(st) {
                init_braced(st, val);
            } else {
                // braces around a scalar
                let c = nodes[val].c as i64;
                if c == 0 {
                    record_entry(base_depth, node(N_ZEROINIT, 0, unqual(st), 0, 0, 0, nodes[val].loc));
                } else {
                    let first = nlist[nodes[val].v];
                    if c > 1 { warn(nodes[val].loc, "excess elements in scalar initializer"); }
                    if nodes[first].kind == N_SYNINIT || nodes[first].kind == N_DESIG {
                        record_entry(base_depth, node(N_ZEROINIT, 0, unqual(st), 0, 0, 0, nodes[val].loc));
                    } else {
                        record_entry(base_depth, assign_convert(rv(first), unqual(st), nodes[first].loc, 1));
                    }
                }
            }
            return;
        }
        if is_string_for(st, val) {
            let flag_n = val;
            nodes[flag_n].flags = nodes[flag_n].flags | NF_STRINIT;
            string_init_type(val, st);
            record_entry(base_depth, val);
            if kind_of(st) == TY_ARRAY && types[st >> 4].n < 0 {
                let sl = strs[nodes[val].a].len as i64;
                if sl > flex_max { flex_max = sl; }
            }
            return;
        }
        if is_init_aggregate(st) {
            let r = rv(val);
            if (is_record(st) || is_vector(st)) && compatible_unq(st, nty(r)) {
                record_entry(base_depth, r);
                return;
            }
            // brace elision: initialize the first subobject of st
            nodes[val].v = nodes[val].v;
            let c = sub_count(st);
            if c == 0 && kind_of(st) != TY_ARRAY {
                err_at(nodes[val].loc, str("initializing ", tname(st), " with an expression of incompatible type ", tname(nty(r))));
                return;
            }
            ifr.push(Frame { ty: st, idx: next_member(st, 0), count: c });
            if c == 0 {
                ifr.pop();
                return;
            }
            continue;
        }
        record_entry(base_depth, assign_convert(rv(val), unqual(st), nodes[val].loc, 1));
        return;
    }
}

// The field index of member `name` in record type t; with anonymous
// members, the frames for the path are pushed (all but the last).
recursive fn find_member_designator(t: u32, name: u32) -> i64 {
    let r = records[rec_of(t)];
    for i in r.count {
        let f = fields[r.first + i];
        if f.name == name { return i; }
    }
    for i in r.count {
        let f = fields[r.first + i];
        if f.flags & FF_ANON != 0 && has_member(rec_of(f.ty), name, 0) {
            ifr[ifr.len - 1].idx = i;
            ifr.push(Frame { ty: with_quals(f.ty, quals(t)), idx: 0, count: sub_count(f.ty) });
            return find_member_designator(f.ty, name);
        }
    }
    return -1;
}

// A braced list initializing an object of type t: its entries get paths
// relative to the frame pushed here.
recursive fn init_braced(t: u32, syn: u32) {
    let c = nodes[syn].c as i64;
    let first = nodes[syn].v;
    // a char array may be initialized by a braced string literal
    if c >= 1 && kind_of(t) == TY_ARRAY && nodes[nlist[first]].kind == N_STRING && is_string_for(t, nlist[first]) {
        let s = nlist[first];
        nodes[s].flags = nodes[s].flags | NF_STRINIT;
        string_init_type(s, t);
        ients.push(IEnt { pstart: ipath.len as! u32, plen: (ifr.len) as! u32, val: s });
        // the path to this object: the current frames
        let ps = ipath.len;
        for j in 0..ifr.len { ipath.push(ifr[j].idx); }
        ients[ients.len - 1].pstart = ps as! u32;
        if ifr.len == 0 { let sl = strs[nodes[s].a].len as i64; if sl > root_max { root_max = sl; } }
        return;
    }
    let base_depth = ifr.len;
    ifr.push(Frame { ty: t, idx: next_member(t, 0), count: sub_count(t) });
    for k in c {
        let item = nlist[first + k];
        var val = item;
        if nodes[item].kind == N_DESIG && nodes[item].op == D_ITEM {
            // designation: restart from this braced object
            ifr.resize(base_depth + 1);
            let dc = nodes[item].c as i64;
            let ds = nodes[item].v;
            var range_hi: i64 = -1;
            var ok = true;
            for j in dc {
                let d = nodes[nlist[ds + j]];
                let top = ifr.len - 1;
                let ft = ifr[top].ty;
                if d.op == D_FIELD {
                    if !is_record(ft) {
                        err_at(d.loc, str("field designator cannot initialize a non-struct, non-union type ", tname(ft)));
                        ok = false;
                        break;
                    }
                    let fi = find_member_designator(ft, d.a);
                    if fi < 0 {
                        err_at(d.loc, str("field designator '", ident_text(d.a as i64), "' does not refer to any field in type ", tname(ft)));
                        ok = false;
                        break;
                    }
                    ifr[ifr.len - 1].idx = fi;
                } else {
                    if kind_of(ft) != TY_ARRAY && !is_vector(ft) {
                        err_at(d.loc, str("array designator cannot initialize non-array type ", tname(ft)));
                        ok = false;
                        break;
                    }
                    let okv, v = fold_int(rv(d.a));
                    if !okv { err_at(d.loc, "expression is not an integer constant expression"); ok = false; break; }
                    let n = ifr[top].count;
                    if v < 0 || (n >= 0 && v >= n) {
                        err_at(d.loc, str("array designator index (", v, ") exceeds array bounds (", n, ")"));
                        ok = false;
                        break;
                    }
                    ifr[top].idx = v;
                    if d.op == D_RANGE {
                        let okh, hv = fold_int(rv(d.b));
                        if !okh { err_at(d.loc, "expression is not an integer constant expression"); ok = false; break; }
                        if hv < v { err_at(d.loc, "array designator range is empty"); ok = false; break; }
                        if j == dc - 1 { range_hi = hv; }
                        else if hv > v { warn(d.loc, "nested range designators are only partially supported"); }
                    }
                }
                if j < dc - 1 {
                    let ti = ifr.len - 1;
                    let st = sub_type(ifr[ti].ty, ifr[ti].idx);
                    ifr.push(Frame { ty: st, idx: next_member(st, 0), count: sub_count(st) });
                }
            }
            val = nodes[item].a;
            if !ok { continue; }
            if range_hi >= 0 {
                let top = ifr.len - 1;
                let lo = ifr[top].idx;
                var x = lo;
                while x <= range_hi {
                    ifr[top].idx = x;
                    let depth0 = ifr.len;
                    assign_value(val, base_depth, 0);
                    ifr.resize(depth0);
                    x++;
                }
                ifr[top].idx = range_hi;
                advance(base_depth);
                continue;
            }
        }
        if ifr.len - 1 == base_depth && frame_exhausted(ifr[base_depth]) {
            warn(nodes[val].loc, "excess elements in initializer");
            break;
        }
        assign_value(val, base_depth, 0);
        if ifr.len > base_depth { advance(base_depth); }
        if ifr.len - 1 == base_depth && frame_exhausted(ifr[base_depth]) && k + 1 < c {
            let nxt = nlist[first + k + 1];
            if !(nodes[nxt].kind == N_DESIG) {
                warn(nodes[nxt].loc, "excess elements in initializer");
                break;
            }
        }
    }
    ifr.resize(base_depth);
}

// ---------------------------------------------------------------------------
// Building the semantic tree.

var isort_tmp: u32[>..<] = [];

// entries lo..hi (indices into ients via ient_order) share path[0..depth]
var ient_order: u32[>..<] = [];

fn ent_key(e: i64, depth: i64) -> i64 {
    let en = ients[ient_order[e]];
    if en.plen as i64 <= depth { return -1; }
    return ipath[en.pstart + depth];
}

// Stable sort of ient_order[lo..hi] by the path component at depth.
recursive fn sort_range(lo: i64, hi: i64, depth: i64) {
    var sorted = true;
    var j = lo + 1;
    while j < hi {
        if ent_key(j - 1, depth) > ent_key(j, depth) { sorted = false; break; }
        j++;
    }
    if sorted { return; }
    // insertion sort for short ranges, merge sort otherwise
    if hi - lo <= 32 {
        var i = lo + 1;
        while i < hi {
            let x = ient_order[i];
            let kx = ent_key(i, depth);
            var p = i - 1;
            while p >= lo && ent_key(p, depth) > kx {
                ient_order[p + 1] = ient_order[p];
                p--;
            }
            ient_order[p + 1] = x;
            i++;
        }
        return;
    }
    let mid = (lo + hi) / 2;
    sort_range(lo, mid, depth);
    sort_range(mid, hi, depth);
    isort_tmp.clear();
    var a = lo;
    var b = mid;
    while a < mid || b < hi {
        if b >= hi || (a < mid && ent_key(a, depth) <= ent_key(b, depth)) {
            isort_tmp.push(ient_order[a]);
            a++;
        } else {
            isort_tmp.push(ient_order[b]);
            b++;
        }
    }
    for i in isort_tmp.len { ient_order[lo + i] = isort_tmp[i]; }
}

fn zero_node(t: u32, loc: u32) -> u32 { node(N_ZEROINIT, 0, unqual(t), 0, 0, 0, loc) }

// Builds the value for type t from entries lo..hi at depth.
recursive fn build(t: u32, lo: i64, hi: i64, depth: i64, loc: u32) -> u32 {
    // the last entry that sets the whole object
    var whole = -1;
    var after = false;
    for e in lo..hi {
        if ients[ient_order[e]].plen as i64 == depth { whole = e; after = false; } else if whole >= 0 { after = true; }
    }
    if whole >= 0 && !after { return ients[ient_order[whole]].val; }
    let k = kind_of(t);
    if k == TY_STRUCT || k == TY_UNION {
        let r = records[rec_of(t)];
        sort_range(lo, hi, depth);
        if k == TY_UNION {
            // the last initialized member wins
            var best = -1;
            var bi: i64 = -1;
            for e in lo..hi {
                let key = ent_key(e, depth);
                if key >= 0 { bi = key; best = e; }
            }
            if bi < 0 {
                let n = node_v(N_INITLIST, 0, unqual(t), 0, 0, 0, loc, nlist.len);
                return n;
            }
            var s = lo;
            while s < hi && ent_key(s, depth) != bi { s++; }
            var e2 = s;
            while e2 < hi && ent_key(e2, depth) == bi { e2++; }
            let ft = fields[r.first + bi].ty;
            let child = build(ft, s, e2, depth + 1, loc);
            let st = nlist.len;
            nlist.push(child);
            let n = node_v(N_INITLIST, 0, unqual(t), bi + 1, 0, 1, loc, st);
            return n;
        }
        let mark = nscratch.len;
        var e = lo;
        while e < hi && ent_key(e, depth) < 0 { e++; }
        for i in r.count {
            let f = fields[r.first + i];
            var s = e;
            while e < hi && ent_key(e, depth) == i { e++; }
            if e > s {
                nscratch.push(build(f.ty, s, e, depth + 1, loc));
            } else {
                nscratch.push(zero_node(f.ty, loc));
            }
        }
        let count = nscratch.len - mark;
        let st = commit_list(mark);
        return node_v(N_INITLIST, 0, unqual(t), 0, 0, count, loc, st);
    }
    if k == TY_ARRAY || k == TY_VECTOR || k == TY_EXTVECTOR || k == TY_VLA {
        let et = tbase(t);
        sort_range(lo, hi, depth);
        var maxi: i64 = -1;
        for e in lo..hi {
            let key = ent_key(e, depth);
            if key > maxi { maxi = key; }
        }
        var n = types[t >> 4].n;
        if k == TY_VLA { n = -1; }
        var rt = unqual(t);
        if k == TY_ARRAY && n < 0 {
            n = maxi + 1;
            rt = mk_array(et, n);
        }
        let mark = nscratch.len;
        var e = lo;
        while e < hi && ent_key(e, depth) < 0 { e++; }
        var i: i64 = 0;
        while i <= maxi {
            var s = e;
            while e < hi && ent_key(e, depth) == i { e++; }
            if e > s {
                nscratch.push(build(et, s, e, depth + 1, loc));
            } else {
                nscratch.push(zero_node(et, loc));
            }
            i++;
        }
        let count = nscratch.len - mark;
        let st = commit_list(mark);
        var filler: u32 = 0;
        if n > count || n < 0 { filler = zero_node(et, loc); }
        return node_v(N_INITLIST, 0, rt, 0, filler as i64, count, loc, st);
    }
    // a scalar: braces with designators make no sense; take the last value
    if whole >= 0 { return ients[ient_order[whole]].val; }
    return zero_node(t, loc);
}

// The initializer for object s of type t (the '=' has been consumed).
recursive fn parse_initializer_for(s: i64, t: u32, is_static: bool) -> u32 {
    let loc = tloc();
    let syn = parse_init_syntax();
    return init_value(s, t, syn, loc);
}

recursive fn init_value(s: i64, t: u32, syn: u32, loc: u32) -> u32 {
    if kind_of(t) == TY_VLA && nodes[syn].kind == N_SYNINIT && nodes[syn].c > 0 {
        err_at(loc, "variable-sized object may not be initialized");
    }
    if nodes[syn].kind != N_SYNINIT {
        if is_init_aggregate(t) {
            if is_string_for(t, syn) {
                nodes[syn].flags = nodes[syn].flags | NF_STRINIT;
                complete_from_string(s, t, syn);
                string_init_type(syn, t);
                return syn;
            }
            let r = rv(syn);
            if compatible_unq(t, nty(r)) { return r; }
            if is_error(r) { return r; }
            err_at(nodes[syn].loc, str("initializing ", tname(t), " with an expression of incompatible type ", tname(nty(r))));
            return error_node(loc);
        }
        return assign_convert(rv(syn), unqual(t), nodes[syn].loc, 1);
    }
    let em = ients.len;
    let pm = ipath.len;
    let fm = ifr.len;
    let om = ient_order.len;
    root_max = 0;
    flex_max = 0;
    if is_init_aggregate(t) {
        init_braced(t, syn);
    } else {
        // a braced scalar
        ifr.push(Frame { ty: t, idx: 0, count: 1 });
        let c = nodes[syn].c as i64;
        if c > 0 {
            let first = nlist[nodes[syn].v];
            if c > 1 { warn(loc, "excess elements in scalar initializer"); }
            let v = if nodes[first].kind == N_SYNINIT { zero_node(t, loc) } else { assign_convert(rv(first), unqual(t), nodes[first].loc, 1) };
            ients.push(IEnt { pstart: ipath.len as! u32, plen: 0, val: v });
        }
        ifr.resize(fm);
    }
    for e in em..ients.len { ient_order.push(e as! u32); }
    var result: u32 = 0;
    if is_init_aggregate(t) {
        result = build(t, om, ient_order.len, 0, loc);
    } else {
        result = if ients.len > em { ients[ients.len - 1].val } else { zero_node(t, loc) };
    }
    ient_order.resize(om);
    ients.resize(em);
    ipath.resize(pm);
    ifr.resize(fm);
    // an incomplete array gets its size from the initializer
    if kind_of(t) == TY_ARRAY && types[t >> 4].n < 0 && s > 0 {
        syms[s].ty = with_quals(nodes[result].ty, quals(t));
    }
    // a flexible array member initialized (GNU): record its extent
    if is_record(t) && records[rec_of(t)].flags & RF_FLEX != 0 && s > 0 {
        syms[s].flags = syms[s].flags;
    }
    return result;
}

// A string literal initializing an array takes the array's type (as in
// clang); an incomplete array is completed from the string's length.
fn string_init_type(n: u32, t: u32) {
    if kind_of(t) == TY_ARRAY && types[t >> 4].n < 0 {
        nodes[n].ty = with_quals(mk_array(tbase(t), strs[nodes[n].a].len as i64), quals(t));
    } else {
        nodes[n].ty = t;
    }
}

fn complete_from_string(s: i64, t: u32, str_node: u32) {
    if kind_of(t) == TY_ARRAY && types[t >> 4].n < 0 && s > 0 {
        let n = strs[nodes[str_node].a].len as i64;
        syms[s].ty = with_quals(mk_array(tbase(t), n), quals(t));
    }
}
