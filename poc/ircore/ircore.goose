// A mutable SSA-style IR core in Goose: the operations a middle end needs.
//
// Instructions and uses live in two slot pools. Each block is an intrusive
// doubly-linked list of instructions (prev/next indices); each value has an
// intrusive doubly-linked use-list, so erase and replace-all-uses-with are
// O(uses), as in LLVM. The workload builds a random dataflow graph, then
// runs constant folding (insert-before + RAUW + erase) and dead-code
// elimination (worklist + erase), and prints a checksum that the C++
// versions must reproduce exactly.
//
// usage: ircore N

import slot_pool;
import os;

let OP_CONST: u8 = 0;
let OP_ADD: u8 = 1;
let OP_SUB: u8 = 2;
let OP_MUL: u8 = 3;
let OP_RET: u8 = 4;
let OP_ARG: u8 = 5;    // an opaque value (an argument or a load): never folded
let OP_SINK: u8 = 6;   // a side effect (a store or a call): never removed

struct Inst {
    val: i64,          // value of a constant
    op: u8,
    dead: u8,
    a: i32, b: i32,    // operand instructions, -1 for none
    ua: i32, ub: i32,  // the Use records of those operands
    prev: i32, next: i32,
    first_use: i32,    // head of this value's use-list
}

struct Use { user: i32, value: i32, next: i32, prev: i32 }

var insts = slot_pool<Inst> {};
var uses = slot_pool<Use> {};
var head: i32 = -1;
var tail: i32 = -1;
var rng: u64 = 88172645463325252;

fn next_rand() -> u64 {
    rng ^= rng << 13;
    rng ^= rng >> 7;
    rng ^= rng << 17;
    return rng;
}

fn add_use(user: i32, value: i32) -> i32 {
    let f = insts.items[value].first_use;
    let u = alloc_index(uses, Use { user: user, value: value, next: f, prev: -1 }) as! i32;
    if f >= 0 { uses.items[f].prev = u; }
    insts.items[value].first_use = u;
    return u;
}

fn remove_use(u: i32) {
    let x = uses.items[u];
    if x.prev >= 0 { uses.items[x.prev].next = x.next; } else { insts.items[x.value].first_use = x.next; }
    if x.next >= 0 { uses.items[x.next].prev = x.prev; }
    free(uses, u);
}

fn new_inst(op: u8, val: i64, a: i32, b: i32) -> i32 {
    let i = alloc_index(insts, Inst { val: val, op: op, dead: 0, a: a, b: b, ua: -1, ub: -1,
                                      prev: -1, next: -1, first_use: -1 }) as! i32;
    if a >= 0 { insts.items[i].ua = add_use(i, a); }
    if b >= 0 { insts.items[i].ub = add_use(i, b); }
    return i;
}

fn append(i: i32) {
    insts.items[i].prev = tail;
    insts.items[i].next = -1;
    if tail >= 0 { insts.items[tail].next = i; } else { head = i; }
    tail = i;
}

fn insert_before(pos: i32, i: i32) {
    let p = insts.items[pos].prev;
    insts.items[i].prev = p;
    insts.items[i].next = pos;
    insts.items[pos].prev = i;
    if p >= 0 { insts.items[p].next = i; } else { head = i; }
}

fn erase(i: i32) {
    let x = insts.items[i];
    if x.prev >= 0 { insts.items[x.prev].next = x.next; } else { head = x.next; }
    if x.next >= 0 { insts.items[x.next].prev = x.prev; } else { tail = x.prev; }
    if x.ua >= 0 { remove_use(x.ua); }
    if x.ub >= 0 { remove_use(x.ub); }
    insts.items[i].dead = 1;
    free(insts, i);
}

fn rauw(old: i32, new: i32) {
    var u = insts.items[old].first_use;
    while u >= 0 {
        let nx = uses.items[u].next;
        let user = uses.items[u].user;
        if insts.items[user].ua == u { insts.items[user].a = new; } else { insts.items[user].b = new; }
        let nf = insts.items[new].first_use;
        uses.items[u].value = new;
        uses.items[u].prev = -1;
        uses.items[u].next = nf;
        if nf >= 0 { uses.items[nf].prev = u; }
        insts.items[new].first_use = u;
        u = nx;
    }
    insts.items[old].first_use = -1;
}

fn build(n: i64) {
    var recent: i32[64] = [0; 64];
    var count: i64 = 0;
    for k in n {
        let r = next_rand();
        var i: i32 = 0;
        let kind = r % 20;
        if count < 2 || kind < 6 {
            i = new_inst(OP_CONST, ((r >> 8) % 1000) as! i64, -1, -1);
        } else if kind < 8 {
            i = new_inst(OP_ARG, k, -1, -1);
        } else if kind < 9 {
            let lim: u64 = if count < 64 { count as! u64 } else { 64 };
            i = new_inst(OP_SINK, 0, recent[((r >> 8) % lim) as! i64], -1);
        } else {
            let lim: u64 = if count < 64 { count as! u64 } else { 64 };
            let a = recent[((r >> 8) % lim) as! i64];
            let b = recent[((r >> 20) % lim) as! i64];
            let op = (1 + (r >> 32) % 3) as! u8;
            i = new_inst(op, 0, a, b);
        }
        append(i);
        recent[count % 64] = i;
        count++;
    }
    append(new_inst(OP_RET, 0, tail, -1));
}

fn fold() -> i64 {
    var folded: i64 = 0;
    var i = head;
    while i >= 0 {
        let x = insts.items[i];
        let nx = x.next;
        if x.op >= OP_ADD && x.op <= OP_MUL {
            let a = insts.items[x.a];
            let b = insts.items[x.b];
            if a.op == OP_CONST && b.op == OP_CONST {
                let v = if x.op == OP_ADD { a.val + b.val } else if x.op == OP_SUB { a.val - b.val } else { a.val * b.val };
                let c = new_inst(OP_CONST, v % 1000003, -1, -1);
                insert_before(i, c);
                rauw(i, c);
                erase(i);
                folded++;
            }
        }
        i = nx;
    }
    return folded;
}

fn dce() -> i64 {
    var work: i32[>..<] = [];
    var i = head;
    while i >= 0 {
        let x = insts.items[i];
        if x.first_use < 0 && x.op != OP_RET && x.op != OP_SINK { work.push(i); }
        i = x.next;
    }
    var removed: i64 = 0;
    while work.len > 0 {
        let j = work.pop();
        let x = insts.items[j];
        if x.dead != 0 || x.first_use >= 0 { continue; }
        erase(j);
        removed++;
        if x.a >= 0 && insts.items[x.a].first_use < 0 { work.push(x.a); }
        if x.b >= 0 && x.b != x.a && insts.items[x.b].first_use < 0 { work.push(x.b); }
    }
    return removed;
}

fn checksum() -> u64, i64 {
    var h: u64 = 1469598103934665603;
    var n: i64 = 0;
    var i = head;
    while i >= 0 {
        let x = insts.items[i];
        h = (h ^ x.op) * 1099511628211;
        h = (h ^ (x.val as! u64)) * 1099511628211;
        n++;
        i = x.next;
    }
    return h, n;
}

fn main() {
    let argv = args();
    var n: i64 = 2000000;
    if argv.len > 1 {
        let v, ok = parse_int(argv[1]);
        if ok { n = v; }
    }
    let t0 = clock_ns();
    build(n);
    let t1 = clock_ns();
    let folded = fold();
    let t2 = clock_ns();
    let removed = dce();
    let t3 = clock_ns();
    let h, live = checksum();
    let t4 = clock_ns();
    print("goose  n=", n, " folded=", folded, " removed=", removed, " live=", live, " checksum=", h);
    print("goose  build ", (t1 - t0) / 1000000, " ms  fold ", (t2 - t1) / 1000000, " ms  dce ",
          (t3 - t2) / 1000000, " ms  walk ", (t4 - t3) / 1000000, " ms  total ", (t4 - t0) / 1000000, " ms");
}
