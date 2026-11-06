// Functions with more than six arguments, mixed widths, nested stack calls.
#include <stdio.h>
#include <stdint.h>

static long f8(int a, long b, short c, char d, unsigned e, long long f, int g, int h) {
    return a + b * 2 + c * 3 + d * 4 + (long)e * 5 + f * 6 + g * 7 + h * 8;
}
static int f12(int a, int b, int c, int d, int e, int f, int g, int h, int i, int j, int k, int l) {
    return a - b + c - d + e - f + g - h + i - j + k - l + l * 100 + g * 1000;
}
static int64_t f7(int8_t a, uint8_t b, int16_t c, uint16_t d, int32_t e, uint32_t f, int64_t g) {
    return a + b + c + d + e + (int64_t)f + g;
}
static const char *pick9(int n, const char *a, const char *b, const char *c, const char *d, const char *e,
                         const char *f, const char *g, const char *h) {
    const char *t[] = {a, b, c, d, e, f, g, h};
    return t[n & 7];
}
static int rec(int depth, int a, int b, int c, int d, int e, int f, int g, int h) {
    if (!depth) return a + b + c + d + e + f + g + h;
    return rec(depth - 1, b, c, d, e, f, g, h, a + 1) + 1;
}
static uint8_t u8_9(uint8_t a, uint8_t b, uint8_t c, uint8_t d, uint8_t e, uint8_t f, uint8_t g, uint8_t h, uint8_t i) {
    return (uint8_t)(a + b + c + d + e + f + g + h + i);
}

int main(void) {
    printf("%ld\n", f8(1, 2, 3, 4, 5, 6, 7, 8));
    printf("%ld\n", f8(-1, -2, -3, -4, 4000000000u, -6, -7, -8));
    printf("%d\n", f12(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12));
    printf("%lld\n", (long long)f7(-1, 255, -300, 65000, -70000, 4000000000u, -5000000000LL));
    for (int i = 0; i < 8; i++) printf("%s", pick9(i, "a", "b", "c", "d", "e", "f", "g", "h"));
    printf("\n%d\n", rec(10, 1, 2, 3, 4, 5, 6, 7, 8));
    printf("%u\n", u8_9(200, 200, 200, 200, 200, 200, 200, 200, 255));
    long (*fp)(int, long, short, char, unsigned, long long, int, int) = f8;
    printf("%ld\n", fp(8, 7, 6, 5, 4, 3, 2, 1));
    printf("%ld %d\n", f8(f12(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1), 2, 3, 4, 5, 6, 7, 8),
           f12(1, 2, 3, 4, 5, 6, (int)f8(1, 2, 3, 4, 5, 6, 7, 8), 8, 9, 10, 11, 12));
    return 0;
}
