// Register allocation: more live values than registers (spills, reloads,
// slot reuse), values live across calls (callee-saved registers), calls with
// many integer and FP arguments mixed with stack arguments, and parallel
// argument moves (arguments permuted between calls).
#include <stdio.h>
#include <stdint.h>

__attribute__((noinline)) static long mix(long a, long b) { return a * 31 + b; }

__attribute__((noinline)) static long many(long a, long b, long c, long d, long e, long f, long g, long h,
                                           double x, double y, int i, double z, long j) {
    return a - 2 * b + 3 * c - 4 * d + 5 * e - 6 * f + 7 * g - 8 * h + (long)(x * 10) + (long)(y * 100)
           + i * 1000 + (long)(z * 7) + j * 11;
}

__attribute__((noinline)) static double fmany(double a, double b, double c, double d, double e, double f,
                                              double g, double h, double i, double j, float k, int l) {
    return a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f + 7 * g + 8 * h + 9 * i + 10 * j + k + l;
}

__attribute__((noinline)) static long perm(long a, long b, long c, long d, long e, long f) {
    return a + 2 * b + 4 * c + 8 * d + 16 * e + 32 * f;
}

// Twenty values live at once: some must be spilled.
__attribute__((noinline)) static uint64_t pressure(uint64_t s) {
    uint64_t v0 = s + 1, v1 = s * 3, v2 = s ^ 0x55, v3 = s >> 3, v4 = s << 5, v5 = s + 77;
    uint64_t v6 = v0 * v1, v7 = v2 + v3, v8 = v4 - v5, v9 = v0 ^ v4, v10 = v1 | v5, v11 = v2 & v3;
    uint64_t v12 = v6 + v7, v13 = v8 * 9, v14 = v9 - v10, v15 = v11 + v12, v16 = v13 ^ v14;
    uint64_t v17 = v15 * v16 + 1, v18 = v0 + v1 + v2, v19 = v3 + v4 + v5;
    return v0 + v1 * 2 + v2 * 3 + v3 * 4 + v4 * 5 + v5 * 6 + v6 * 7 + v7 * 8 + v8 * 9 + v9 * 10 + v10 * 11 +
           v11 * 12 + v12 * 13 + v13 * 14 + v14 * 15 + v15 * 16 + v16 * 17 + v17 * 18 + v18 * 19 + v19 * 20;
}

// The same with calls in between: values cross calls.
__attribute__((noinline)) static long across(long s) {
    long a = mix(s, 1), b = mix(a, 2), c = mix(b, 3), d = mix(c, 4), e = mix(d, 5), f = mix(e, 6);
    long g = mix(f, a), h = mix(g, b), i = mix(h, c), k = mix(i, d);
    return a + b + c + d + e + f + g + h + i + k + mix(a + b, c + d) + mix(e + f, g + h);
}

// FP values across calls (no callee-saved xmm registers).
__attribute__((noinline)) static double fcross(double x) {
    double a = x * 1.5, b = x + 2.25, c = a * b;
    double d = fmany(a, b, c, x, 1, 2, 3, 4, 5, 6, 7.5f, 8);
    double e = fmany(d, c, b, a, x, d, c, b, a, x, 0.25f, -3);
    return a + b + c + d + e;
}

int main(void) {
    printf("%llu %llu\n", (unsigned long long)pressure(12345), (unsigned long long)pressure(0xFFFFFFFFFFull));
    printf("%ld %ld\n", across(7), across(-123456));
    printf("%ld\n", many(1, 2, 3, 4, 5, 6, 7, 8, 1.5, 2.25, 9, 3.5, 10));
    printf("%.6f\n", fmany(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11.5f, 12));
    printf("%.6f\n", fcross(3.0));
    long a = 1, b = 2, c = 3, d = 4, e = 5, f = 6;
    long r = 0;
    for (int it = 0; it < 4; it++) {
        r += perm(a, b, c, d, e, f) + perm(f, e, d, c, b, a) + perm(b, a, d, c, f, e) + perm(c, a, b, f, d, e);
        long t = a; a = b; b = c; c = d; d = e; e = f; f = t;
    }
    printf("%ld\n", r);
    return 0;
}
