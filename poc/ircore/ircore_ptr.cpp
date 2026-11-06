// The same IR core in the LLVM style: every instruction and every use is a
// separate heap object, linked by pointers (intrusive instruction list,
// intrusive use-lists), freed with delete. Same workload and checksum as
// ircore.goose / ircore_idx.cpp.
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

enum : uint8_t { OP_CONST, OP_ADD, OP_SUB, OP_MUL, OP_RET, OP_ARG, OP_SINK };

struct Inst;
struct Use { Inst *user; Inst *value; Use *next; Use *prev; };
struct Inst {
    int64_t val;
    uint8_t op;
    Inst *ops[2];
    Use *uses[2];
    Inst *prev, *next;
    Use *first_use;
};

static Inst *head = nullptr, *tail = nullptr;
static uint64_t rng = 88172645463325252ull;
static uint64_t next_rand() { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static Use *add_use(Inst *user, Inst *value) {
    Use *u = new Use{user, value, value->first_use, nullptr};
    if (value->first_use) value->first_use->prev = u;
    value->first_use = u;
    return u;
}

static void remove_use(Use *u) {
    if (u->prev) u->prev->next = u->next; else u->value->first_use = u->next;
    if (u->next) u->next->prev = u->prev;
    delete u;
}

static Inst *new_inst(uint8_t op, int64_t val, Inst *a, Inst *b) {
    Inst *i = new Inst{val, op, {a, b}, {nullptr, nullptr}, nullptr, nullptr, nullptr};
    if (a) i->uses[0] = add_use(i, a);
    if (b) i->uses[1] = add_use(i, b);
    return i;
}

static void append(Inst *i) {
    i->prev = tail; i->next = nullptr;
    if (tail) tail->next = i; else head = i;
    tail = i;
}

static void insert_before(Inst *pos, Inst *i) {
    Inst *p = pos->prev;
    i->prev = p; i->next = pos; pos->prev = i;
    if (p) p->next = i; else head = i;
}

static void erase(Inst *i) {
    if (i->prev) i->prev->next = i->next; else head = i->next;
    if (i->next) i->next->prev = i->prev; else tail = i->prev;
    if (i->uses[0]) remove_use(i->uses[0]);
    if (i->uses[1]) remove_use(i->uses[1]);
    delete i;
}

static void rauw(Inst *old, Inst *nw) {
    for (Use *u = old->first_use; u;) {
        Use *nx = u->next;
        Inst *user = u->user;
        if (user->uses[0] == u) user->ops[0] = nw; else user->ops[1] = nw;
        u->value = nw; u->prev = nullptr; u->next = nw->first_use;
        if (nw->first_use) nw->first_use->prev = u;
        nw->first_use = u;
        u = nx;
    }
    old->first_use = nullptr;
}

static void build(int64_t n) {
    Inst *recent[64] = {nullptr};
    int64_t count = 0;
    for (int64_t k = 0; k < n; k++) {
        uint64_t r = next_rand();
        Inst *i;
        uint64_t kind = r % 20;
        if (count < 2 || kind < 6) {
            i = new_inst(OP_CONST, (int64_t)((r >> 8) % 1000), nullptr, nullptr);
        } else if (kind < 8) {
            i = new_inst(OP_ARG, k, nullptr, nullptr);
        } else if (kind < 9) {
            uint64_t lim = count < 64 ? (uint64_t)count : 64;
            i = new_inst(OP_SINK, 0, recent[(r >> 8) % lim], nullptr);
        } else {
            uint64_t lim = count < 64 ? (uint64_t)count : 64;
            Inst *a = recent[(r >> 8) % lim], *b = recent[(r >> 20) % lim];
            i = new_inst((uint8_t)(1 + (r >> 32) % 3), 0, a, b);
        }
        append(i);
        recent[count % 64] = i;
        count++;
    }
    append(new_inst(OP_RET, 0, tail, nullptr));
}

static int64_t emod(int64_t a, int64_t b) { int64_t r = a % b; return r < 0 ? r + (b < 0 ? -b : b) : r; }

static int64_t fold() {
    int64_t folded = 0;
    for (Inst *i = head; i;) {
        Inst *nx = i->next;
        if (i->op >= OP_ADD && i->op <= OP_MUL && i->ops[0]->op == OP_CONST && i->ops[1]->op == OP_CONST) {
            int64_t a = i->ops[0]->val, b = i->ops[1]->val;
            int64_t v = i->op == OP_ADD ? a + b : i->op == OP_SUB ? a - b : a * b;
            Inst *c = new_inst(OP_CONST, emod(v, 1000003), nullptr, nullptr);
            insert_before(i, c);
            rauw(i, c);
            erase(i);
            folded++;
        }
        i = nx;
    }
    return folded;
}

static int64_t dce() {
    // A pointer can't say "already deleted", so the worklist only ever holds
    // live instructions: an operand is pushed when it loses its last use,
    // and a value used twice by the same user is pushed once.
    std::vector<Inst *> work;
    for (Inst *i = head; i; i = i->next)
        if (!i->first_use && i->op != OP_RET && i->op != OP_SINK) work.push_back(i);
    int64_t removed = 0;
    while (!work.empty()) {
        Inst *j = work.back(); work.pop_back();
        Inst *a = j->ops[0], *b = j->ops[1];
        erase(j);
        removed++;
        if (a && !a->first_use) work.push_back(a);
        if (b && b != a && !b->first_use) work.push_back(b);
    }
    return removed;
}

int main(int argc, char **argv) {
    int64_t n = argc > 1 ? atoll(argv[1]) : 2000000;
    using clk = std::chrono::steady_clock;
    auto ms = [](clk::time_point a, clk::time_point b) { return (long long)std::chrono::duration_cast<std::chrono::milliseconds>(b - a).count(); };
    auto t0 = clk::now();
    build(n);
    auto t1 = clk::now();
    int64_t folded = fold();
    auto t2 = clk::now();
    int64_t removed = dce();
    auto t3 = clk::now();
    uint64_t h = 1469598103934665603ull;
    int64_t live = 0;
    for (Inst *i = head; i; i = i->next) {
        h = (h ^ i->op) * 1099511628211ull;
        h = (h ^ (uint64_t)i->val) * 1099511628211ull;
        live++;
    }
    auto t4 = clk::now();
    printf("c++ptr n=%lld folded=%lld removed=%lld live=%lld checksum=%llu\n", (long long)n, (long long)folded,
           (long long)removed, (long long)live, (unsigned long long)h);
    printf("c++ptr build %lld ms  fold %lld ms  dce %lld ms  walk %lld ms  total %lld ms\n", ms(t0, t1), ms(t1, t2),
           ms(t2, t3), ms(t3, t4), ms(t0, t4));
    // Like LLVM's normal mode, nothing is torn down at exit.
}
