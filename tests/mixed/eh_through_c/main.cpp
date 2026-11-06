// C++ exceptions thrown from callbacks through the C frames of frames.c,
// caught here; destructors on the way must run, the stack must not leak
// (landing pads reached many times from calls with stack arguments).
#include <cstdio>
#include <cstdlib>
#include <stdexcept>
#include <string>

extern "C" {
typedef void (*cb_t)(int);
long through_regs(cb_t f, int n, long a, long b, long c, long d, long e, long g);
int through_vla(cb_t f, int n);
int through_va(cb_t f, int n, ...);
int through_deep(cb_t f, int depth);
long through_stack_args(cb_t f, long x);
void sort_with(cb_t f, int *v, int n);
int through_leaf(cb_t f, int x);
extern long chain_calls;
}

static int dtors;
struct Guard {
    int id;
    explicit Guard(int i) : id(i) {}
    ~Guard() { dtors += id; }
};

struct Boom : std::runtime_error {
    int v;
    explicit Boom(int x) : std::runtime_error("boom " + std::to_string(x)), v(x) {}
};

static int limit = 3;
extern "C" void cb(int x) {
    Guard g(1);
    if (x >= limit) throw Boom(x);
}
extern "C" void cb_int(int x) {
    if (x == 7) throw x;
}
extern "C" void cb_str(int x) {
    if (x > 20) throw std::string("big ") + std::to_string(x);
}
extern "C" void cb_never(int) {}

// many arguments: a call with a stack-argument area inside a try; the
// address of a local tells whether the stack pointer drifts
static char *first_sp, *last_sp;
static long eleven(long a, long b, long c, long d, long e, long f, long g, long h, long i, long j, long k) {
    char here;
    if (!first_sp) first_sp = &here;
    last_sp = &here;
    if (k % 3 == 2) throw Boom((int)k);
    return a + b + c + d + e + f + g + h + i + j + k;
}

int main() {
    long total = 0;
    try {
        Guard g(100);
        total += through_regs(cb, 10, 1, 2, 3, 4, 5, 6);
        std::puts("not reached");
    } catch (const Boom &b) {
        std::printf("regs: caught %s (%d), dtors %d\n", b.what(), b.v, dtors);
    }
    total += through_regs(cb_never, 4, 1, 2, 3, 4, 5, 6);
    try {
        through_vla(cb, 5);
    } catch (const std::exception &e) {
        std::printf("vla: caught %s\n", e.what());
    }
    try {
        through_va(cb_int, 4, 5, 6, 7, 8);
    } catch (int i) {
        std::printf("va: caught int %d\n", i);
    }
    try {
        limit = 0;
        through_deep(cb, 50);
    } catch (Boom &b) {
        std::printf("deep: caught %d after %ld calls\n", b.v, chain_calls);
    }
    try {
        limit = 30;
        through_stack_args(cb, 9);
    } catch (Boom &b) {
        std::printf("stack args: caught %d\n", b.v);
    }
    int v[] = {5, 3, 9, 1, 25, 7, 2, 30, 4};
    try {
        sort_with(cb_str, v, 9);
    } catch (const std::string &s) {
        std::printf("qsort: caught '%s'\n", s.c_str());
    }
    try {
        limit = 2;
        through_leaf(cb, 6);
    } catch (...) {
        std::printf("leaf: caught (...)\n");
    }
    // a landing pad reached 200000 times from calls with stack arguments
    long caught = 0;
    for (long k = 0; k < 200000; k++) {
        try {
            total += eleven(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, k);
        } catch (const Boom &) {
            caught++;
        }
    }
    // rethrow across frames
    try {
        try {
            through_regs(cb, 5, 0, 0, 0, 0, 0, 0);
        } catch (Boom &b) {
            b.v += 1000;
            throw;
        }
    } catch (const Boom &b) {
        std::printf("rethrow: %d\n", b.v);
    }
    std::printf("caught %ld, dtors %d, total %ld, stack %s\n", caught, dtors, total,
                first_sp == last_sp ? "stable" : "drifts");
    return 0;
}
