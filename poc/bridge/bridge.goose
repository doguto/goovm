// Minimal C++ <-> Goose bridge: what crosses the export boundary, and what it costs.
//
// Built for a C host with:
//   goose --standalone --header bridge.h -o bridge.c bridge.goose

// A flat, fixed-size record, shaped like one instruction of a flat IR.
struct Item { op: u16, ty: u8, flags: u8, a: u32, b: u32, c: u32 }

// 1. Scalar call: measures the per-call cost of crossing the boundary.
export fn gb_add(a: i64, b: i64) -> i64 { a + b }

// 2. Bulk read: a slice of the host's memory, read in place.
export fn gb_sum(xs: const i64[:]) -> i64 {
    var t: i64 = 0;
    for x in xs { t += x; }
    return t;
}

// 3. Bulk write: the host owns the buffer, Goose writes into it.
export fn gb_scale(xs: i64[:], k: i64) {
    for &x in xs { x *= k; }
}

// 4. Records: a histogram of opcodes over an array of flat structs, written
//    into a table the host owns.
export fn gb_histogram(items: const Item[:], out: u32[:]) {
    for it in items {
        let o: i64 = it.op;
        if o < out.len { out[o] += 1; }
    }
}

// 5. Returning bytes: Goose owns the storage (a global builder), the host
//    reads it until the next call.
var outbuf: u8[>..] = [];

export fn gb_make_bytes(n: i64) -> const u8[:] {
    outbuf.clear();
    for i in n { outbuf.push((i % 251) as! u8); }
    return outbuf;
}
