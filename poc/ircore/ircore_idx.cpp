// The same IR core as ircore.goose, in C++ with the same data layout:
// two pools (vector + LIFO freelist) of instructions and uses, linked by
// 32-bit indices. Output (counts and checksum) must match ircore.goose.
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

enum : uint8_t { OP_CONST, OP_ADD, OP_SUB, OP_MUL, OP_RET, OP_ARG, OP_SINK };

#pragma pack(push, 1)  // Goose structs are packed; keep the comparison byte-for-byte fair
struct Inst {
    int64_t val;
    uint8_t op, dead;
    int32_t a, b, ua, ub, prev, next, first_use;
};
struct Use { int32_t user, value, next, prev; };
#pragma pack(pop)

template <class T> struct Pool {
    std::vector<T> items;
    std::vector<int64_t> free_slots;
    int64_t alloc(const T &v) {
        if (!free_slots.empty()) { int64_t i = free_slots.back(); free_slots.pop_back(); items[i] = v; return i; }
        items.push_back(v);
        return (int64_t)items.size() - 1;
    }
    void free(int64_t i) { free_slots.push_back(i); }
};

static Pool<Inst> insts;
static Pool<Use> uses;
static int32_t head = -1, tail = -1;
static uint64_t rng = 88172645463325252ull;

static uint64_t next_rand() { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static int32_t add_use(int32_t user, int32_t value) {
    int32_t f = insts.items[value].first_use;
    int32_t u = (int32_t)uses.alloc(Use{user, value, f, -1});
    if (f >= 0) uses.items[f].prev = u;
    insts.items[value].first_use = u;
    return u;
}

static void remove_use(int32_t u) {
    Use x = uses.items[u];
    if (x.prev >= 0) uses.items[x.prev].next = x.next; else insts.items[x.value].first_use = x.next;
    if (x.next >= 0) uses.items[x.next].prev = x.prev;
    uses.free(u);
}

static int32_t new_inst(uint8_t op, int64_t val, int32_t a, int32_t b) {
    int32_t i = (int32_t)insts.alloc(Inst{val, op, 0, a, b, -1, -1, -1, -1, -1});
    if (a >= 0) insts.items[i].ua = add_use(i, a);
    if (b >= 0) insts.items[i].ub = add_use(i, b);
    return i;
}

static void append(int32_t i) {
    insts.items[i].prev = tail;
    insts.items[i].next = -1;
    if (tail >= 0) insts.items[tail].next = i; else head = i;
    tail = i;
}

static void insert_before(int32_t pos, int32_t i) {
    int32_t p = insts.items[pos].prev;
    insts.items[i].prev = p;
    insts.items[i].next = pos;
    insts.items[pos].prev = i;
    if (p >= 0) insts.items[p].next = i; else head = i;
}

static void erase(int32_t i) {
    Inst x = insts.items[i];
    if (x.prev >= 0) insts.items[x.prev].next = x.next; else head = x.next;
    if (x.next >= 0) insts.items[x.next].prev = x.prev; else tail = x.prev;
    if (x.ua >= 0) remove_use(x.ua);
    if (x.ub >= 0) remove_use(x.ub);
    insts.items[i].dead = 1;
    insts.free(i);
}

static void rauw(int32_t old, int32_t nw) {
    int32_t u = insts.items[old].first_use;
    while (u >= 0) {
        int32_t nx = uses.items[u].next;
        int32_t user = uses.items[u].user;
        if (insts.items[user].ua == u) insts.items[user].a = nw; else insts.items[user].b = nw;
        int32_t nf = insts.items[nw].first_use;
        uses.items[u].value = nw;
        uses.items[u].prev = -1;
        uses.items[u].next = nf;
        if (nf >= 0) uses.items[nf].prev = u;
        insts.items[nw].first_use = u;
        u = nx;
    }
    insts.items[old].first_use = -1;
}

static void build(int64_t n) {
    int32_t recent[64] = {0};
    int64_t count = 0;
    for (int64_t k = 0; k < n; k++) {
        uint64_t r = next_rand();
        int32_t i;
        uint64_t kind = r % 20;
        if (count < 2 || kind < 6) {
            i = new_inst(OP_CONST, (int64_t)((r >> 8) % 1000), -1, -1);
        } else if (kind < 8) {
            i = new_inst(OP_ARG, k, -1, -1);
        } else if (kind < 9) {
            uint64_t lim = count < 64 ? (uint64_t)count : 64;
            i = new_inst(OP_SINK, 0, recent[(r >> 8) % lim], -1);
        } else {
            uint64_t lim = count < 64 ? (uint64_t)count : 64;
            int32_t a = recent[(r >> 8) % lim], b = recent[(r >> 20) % lim];
            uint8_t op = (uint8_t)(1 + (r >> 32) % 3);
            i = new_inst(op, 0, a, b);
        }
        append(i);
        recent[count % 64] = i;
        count++;
    }
    append(new_inst(OP_RET, 0, tail, -1));
}

static int64_t emod(int64_t a, int64_t b) { int64_t r = a % b; return r < 0 ? r + (b < 0 ? -b : b) : r; }

static int64_t fold() {
    int64_t folded = 0;
    for (int32_t i = head; i >= 0;) {
        Inst x = insts.items[i];
        int32_t nx = x.next;
        if (x.op >= OP_ADD && x.op <= OP_MUL) {
            Inst a = insts.items[x.a], b = insts.items[x.b];
            if (a.op == OP_CONST && b.op == OP_CONST) {
                int64_t v = x.op == OP_ADD ? a.val + b.val : x.op == OP_SUB ? a.val - b.val : a.val * b.val;
                int32_t c = new_inst(OP_CONST, emod(v, 1000003), -1, -1);  // Goose % is Euclidean
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

static int64_t dce() {
    std::vector<int32_t> work;
    for (int32_t i = head; i >= 0; i = insts.items[i].next)
        if (insts.items[i].first_use < 0 && insts.items[i].op != OP_RET && insts.items[i].op != OP_SINK) work.push_back(i);
    int64_t removed = 0;
    while (!work.empty()) {
        int32_t j = work.back(); work.pop_back();
        Inst x = insts.items[j];
        if (x.dead != 0 || x.first_use >= 0) continue;
        erase(j);
        removed++;
        if (x.a >= 0 && insts.items[x.a].first_use < 0) work.push_back(x.a);
        if (x.b >= 0 && x.b != x.a && insts.items[x.b].first_use < 0) work.push_back(x.b);
    }
    return removed;
}

int main(int argc, char **argv) {
    int64_t n = argc > 1 ? atoll(argv[1]) : 2000000;
    using clk = std::chrono::steady_clock;
    auto ms = [](clk::time_point a, clk::time_point b) { return (long long)std::chrono::duration_cast<std::chrono::milliseconds>(b - a).count(); };
#ifdef RESERVE
    // Pre-size the pools so growth never reallocates, as a Goose data stack
    // never moves: isolates that effect from the language itself.
    insts.items.reserve(2 * n + 16);
    uses.items.reserve(2 * n + 16);
#endif
    auto t0 = clk::now();
    build(n);
    auto t1 = clk::now();
    int64_t folded = fold();
    auto t2 = clk::now();
    int64_t removed = dce();
    auto t3 = clk::now();
    uint64_t h = 1469598103934665603ull;
    int64_t live = 0;
    for (int32_t i = head; i >= 0; i = insts.items[i].next) {
        h = (h ^ insts.items[i].op) * 1099511628211ull;
        h = (h ^ (uint64_t)insts.items[i].val) * 1099511628211ull;
        live++;
    }
    auto t4 = clk::now();
    printf("c++idx n=%lld folded=%lld removed=%lld live=%lld checksum=%llu\n", (long long)n, (long long)folded,
           (long long)removed, (long long)live, (unsigned long long)h);
    printf("c++idx build %lld ms  fold %lld ms  dce %lld ms  walk %lld ms  total %lld ms\n", ms(t0, t1), ms(t1, t2),
           ms(t2, t3), ms(t3, t4), ms(t0, t4));
}
