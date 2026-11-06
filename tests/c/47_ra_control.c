// Register allocation and control flow: values used in other blocks (homes
// written at their definition), PHI swaps and rotations (parallel copies,
// mem2reg variant), switches with PHIs, conditions fused with branches and
// selects (integer and FP, NaN predicates), short-circuit logic.
#include <stdio.h>
#include <stdint.h>

__attribute__((noinline)) static int fib_swap(int n) {
    int a = 0, b = 1;
    for (int i = 0; i < n; i++) { int t = a + b; a = b; b = t; }  // PHI swap
    return a;
}
__attribute__((noinline)) static unsigned rot(unsigned x, unsigned y, unsigned z, int n) {
    for (int i = 0; i < n; i++) { unsigned t = x; x = y; y = z; z = t + i; }  // PHI rotation
    return x * 9 + y * 3 + z;
}
__attribute__((noinline)) static int sw(int k, int x) {
    int r;
    switch (k) {
    case 0: r = x + 1; break;
    case 1: r = x * 2; break;
    case 5: r = x - 7; break;
    case 100: r = -x; break;
    case -3: r = x ^ 0xFF; break;
    default: r = 42;
    }
    return r + k;
}
__attribute__((noinline)) static long long sw64(long long k) {
    switch (k) {
    case 0x100000000LL: return 1;
    case -0x100000000LL: return 2;
    case 7: return 3;
    default: return 4;
    }
}
__attribute__((noinline)) static int fcmp_all(double a, double b) {
    int r = 0;
    r |= (a == b) << 0;
    r |= (a != b) << 1;
    r |= (a < b) << 2;
    r |= (a <= b) << 3;
    r |= (a > b) << 4;
    r |= (a >= b) << 5;
    r |= !(a < b) << 6;
    r |= !(a >= b) << 7;
    r |= __builtin_isunordered(a, b) << 8;
    return r;
}
__attribute__((noinline)) static int branchy(double a, double b) {
    int r = 0;
    if (a == b) r += 1;
    if (a != b) r += 2;
    if (a < b) r += 4;
    if (!(a > b)) r += 8;
    if (a >= b && b >= 0) r += 16;
    if (a < 0 || b < 0) r += 32;
    return r;
}
__attribute__((noinline)) static long sel(long a, long b, unsigned char c, short d) {
    long m = a < b ? a : b;
    long n = (unsigned long)a > (unsigned long)b ? a : b;
    int e = c > 200 ? c : -c;
    int f = d < -5 ? d * 2 : d;
    double g = a > 0 ? 1.5 : -2.5;
    return m + n * 3 + e * 5 + f * 7 + (long)(g * 4);
}
__attribute__((noinline)) static uint64_t cross(uint64_t x, int n) {
    uint64_t a = x * 3, b = x ^ 0xABCDEF, c = x >> 2;  // used in later blocks
    uint64_t s = 0;
    for (int i = 0; i < n; i++) {
        if (i & 1) s += a; else s ^= b;
        if (i % 3 == 0) s += c * i;
    }
    return s + a + b + c;
}

int main(void) {
    printf("%d %d\n", fib_swap(30), fib_swap(1));
    printf("%u %u\n", rot(1, 2, 3, 10), rot(7, 0, 9, 1));
    for (int k = -4; k < 7; k++) printf("%d ", sw(k, 10));
    printf("%d %d\n", sw(100, 3), sw(1000, 3));
    printf("%lld %lld %lld %lld\n", sw64(0x100000000LL), sw64(-0x100000000LL), sw64(7), sw64(8));
    double nan = __builtin_nan("");
    printf("%d %d %d %d %d\n", fcmp_all(1, 2), fcmp_all(2, 1), fcmp_all(3, 3), fcmp_all(nan, 1), fcmp_all(1, nan));
    printf("%d %d %d %d %d\n", branchy(1, 2), branchy(2, 1), branchy(3, 3), branchy(nan, 1), branchy(-1, nan));
    printf("%ld %ld %ld\n", sel(3, 9, 250, -9), sel(-3, -9, 5, 4), sel(-1, 1, 201, -6));
    printf("%llu %llu\n", (unsigned long long)cross(12345, 50), (unsigned long long)cross(~0ull, 7));
    return 0;
}
