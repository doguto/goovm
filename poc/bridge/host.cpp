// C++ host for bridge.goose: measures what calling Goose from C++ costs.
//
// Each test runs the same work three ways where it makes sense:
//   goose   - through the exported Goose function
//   c++     - the same loop written in C++, in this file (noinline)
// and prints ns per call or per element.

#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>

#include "bridge.h"

// The C++ mirror of the Goose struct: same fields, same 16-byte packed layout.
struct Item { uint16_t op; uint8_t ty; uint8_t flags; uint32_t a, b, c; };
static_assert(sizeof(Item) == 16, "layout must match Item_g");
static_assert(sizeof(Item_g) == 16, "Goose layout changed");

using clk = std::chrono::steady_clock;
static double secs(clk::time_point a, clk::time_point b) {
    return std::chrono::duration<double>(b - a).count();
}

__attribute__((noinline)) static int64_t cpp_add(int64_t a, int64_t b) { return a + b; }
__attribute__((noinline)) static int64_t cpp_sum(const int64_t *xs, int64_t n) {
    asm volatile("" : : "r"(xs) : "memory");  // not pure: every call must run
    int64_t t = 0;
    for (int64_t i = 0; i < n; i++) t += xs[i];
    return t;
}
__attribute__((noinline)) static void cpp_scale(int64_t *xs, int64_t n, int64_t k) {
    for (int64_t i = 0; i < n; i++) xs[i] *= k;
}
__attribute__((noinline)) static void cpp_histogram(const Item *items, int64_t n, uint32_t *out, int64_t m) {
    for (int64_t i = 0; i < n; i++) {
        int64_t o = items[i].op;
        if (o < m) out[o] += 1;
    }
}

template <class F> static double best_of(int reps, F f) {
    double best = 1e9;
    for (int r = 0; r < reps; r++) {
        // The barriers stop the optimizer from moving a pure call (cpp_sum)
        // out of the timed region.
        asm volatile("" ::: "memory");
        auto t0 = clk::now();
        asm volatile("" ::: "memory");
        f();
        asm volatile("" ::: "memory");
        auto t1 = clk::now();
        asm volatile("" ::: "memory");
        if (secs(t0, t1) < best) best = secs(t0, t1);
    }
    return best;
}

int main(int argc, char **argv) {
    auto t0 = clk::now();
    goose_init(argc, argv);
    auto t1 = clk::now();
    std::printf("goose_init: %.1f us\n", secs(t0, t1) * 1e6);

    // 1. Scalar calls.
    const int64_t CALLS = 100000000;
    volatile int64_t sink = 0;
    double g = best_of(3, [&] { int64_t t = 0; for (int64_t i = 0; i < CALLS; i++) t = gb_add(t, i); sink = t; });
    double c = best_of(3, [&] { int64_t t = 0; for (int64_t i = 0; i < CALLS; i++) t = cpp_add(t, i); sink = t; });
    std::printf("scalar call      goose %.2f ns/call   c++ %.2f ns/call\n", g / CALLS * 1e9, c / CALLS * 1e9);

    // 2/3. Bulk read and write over a 64 MiB array.
    const int64_t N = 8 << 20;
    std::vector<int64_t> xs(N);
    for (int64_t i = 0; i < N; i++) xs[i] = i;
    int64_t rg = 0, rc = 0;
    g = best_of(5, [&] { rg = gb_sum(sl_i64{(gs_i64 *)xs.data(), N}); });
    c = best_of(5, [&] { rc = cpp_sum(xs.data(), N); });
    std::printf("sum i64[:]       goose %.3f ns/elem   c++ %.3f ns/elem   (equal: %s)\n",
                g / N * 1e9, c / N * 1e9, rg == rc ? "yes" : "NO");
    g = best_of(5, [&] { gb_scale(sl_i64{(gs_i64 *)xs.data(), N}, 3); });
    c = best_of(5, [&] { cpp_scale(xs.data(), N, 3); });
    std::printf("scale i64[:]     goose %.3f ns/elem   c++ %.3f ns/elem\n", g / N * 1e9, c / N * 1e9);

    // 4. Records: 4M flat 16-byte structs, histogram into a host table.
    const int64_t M = 4 << 20, OPS = 64;
    std::vector<Item> items(M);
    for (int64_t i = 0; i < M; i++) items[i] = Item{uint16_t((i * 2654435761u) % OPS), 0, 0, 0, 0, 0};
    std::vector<uint32_t> hg(OPS), hc(OPS);
    g = best_of(5, [&] { std::fill(hg.begin(), hg.end(), 0);
                         gb_histogram(sl_Item_g{(Item_g *)items.data(), M}, sl_u32{(gs_u32 *)hg.data(), OPS}); });
    c = best_of(5, [&] { std::fill(hc.begin(), hc.end(), 0); cpp_histogram(items.data(), M, hc.data(), OPS); });
    std::printf("histogram Item[] goose %.3f ns/elem   c++ %.3f ns/elem   (equal: %s)\n",
                g / M * 1e9, c / M * 1e9, hg == hc ? "yes" : "NO");

    // 5. Bytes returned from Goose-owned storage.
    int64_t len = 0;
    const int64_t B = 16 << 20;
    const uint8_t *p = nullptr;
    g = best_of(5, [&] { p = gb_make_bytes(B, &len); });
    bool ok = len == B;
    for (int64_t i = 0; ok && i < len; i += 4097) ok = p[i] == uint8_t(i % 251);
    std::printf("make_bytes       goose %.3f ns/byte   (len %lld, content ok: %s)\n",
                g / B * 1e9, (long long)len, ok ? "yes" : "NO");

    goose_exit();
    (void)sink;
    return 0;
}
