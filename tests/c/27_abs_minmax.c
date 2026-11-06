// abs/labs (clang emits llvm.abs), min/max idioms, select chains.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

static int clamp(int v, int lo, int hi) { return v < lo ? lo : v > hi ? hi : v; }
static unsigned umin(unsigned a, unsigned b) { return a < b ? a : b; }
static long long smax(long long a, long long b) { return a > b ? a : b; }

int main(void) {
    int v[] = {0, 5, -5, 2147483647, -2147483647, 100, -100};
    for (int i = 0; i < 7; i++) printf("%d ", abs(v[i]));
    printf("\n%ld %ld %lld\n", labs(-123456789012L), labs(5L), llabs(-9000000000000LL));
    for (int i = -3; i < 15; i += 2) printf("%d ", clamp(i * 3, 0, 20));
    printf("\n%u %u %lld %lld\n", umin(3, 4000000000u), umin(4000000000u, 5), smax(-5, -9), smax(1LL << 40, 7));
    int8_t a8 = -100;
    int16_t a16 = -30000;
    printf("%d %d\n", abs(a8), abs(a16));
    int s = 0;
    for (int i = -50; i < 50; i += 7) s += abs(i) - abs(i / 2);
    printf("%d\n", s);
    return 0;
}
