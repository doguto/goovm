// Indirect calls with stack arguments, callbacks taking many arguments,
// recursion through function pointers.
#include <stdio.h>

typedef long (*f9)(long, long, long, long, long, long, long, long, long);
static long weighted(long a, long b, long c, long d, long e, long f, long g, long h, long i) {
    return a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f + 7 * g + 8 * h + 9 * i;
}
static long alt(long a, long b, long c, long d, long e, long f, long g, long h, long i) {
    return a - b + c - d + e - f + g - h + i;
}
static long apply(f9 fn, long base) { return fn(base, base + 1, base + 2, base + 3, base + 4, base + 5, base + 6, base + 7, base + 8); }
typedef int (*rec_fn)(int, int (*)(int, void *), void *);
static int countdown(int n, int (*self)(int, void *), void *ctx) {
    int *acc = ctx;
    *acc += n;
    return n ? self(n - 1, ctx) : 0;
}
static int trampoline(int n, void *ctx) { return countdown(n, trampoline, ctx); }

int main(void) {
    f9 fns[2] = {weighted, alt};
    for (int k = 0; k < 2; k++)
        for (long b = -2; b <= 2; b++) printf("%ld ", apply(fns[k], b));
    printf("\n");
    int acc = 0;
    trampoline(20, &acc);
    printf("%d\n", acc);
    long (*pick)(long, long, long, long, long, long, long, long, long) = acc > 100 ? weighted : alt;
    printf("%ld\n", pick(1, 1, 1, 1, 1, 1, 1, 1, 1));
    return 0;
}
