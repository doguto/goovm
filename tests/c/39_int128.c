// __int128: arithmetic, shifts, division (libcalls), compares, conversions,
// odd-width bitfields (i24, i40, i48 storage units).
#include <stdio.h>

typedef __int128 i128;
typedef unsigned __int128 u128;

static void p128(const char *s, u128 x) {
    printf("%s %016llx%016llx\n", s, (unsigned long long)(x >> 64), (unsigned long long)x);
}
static i128 mul(i128 a, i128 b) { return a * b; }
static int sw(u128 x) {
    switch (x) {
    case 0: return 1;
    case 5: return 2;
    case (u128)1 << 100: return 3;
    case ~(u128)0: return 4;
    default: return 5;
    }
}

struct __attribute__((packed)) B {
    unsigned a : 20, b : 4;
    unsigned long long c : 40;
    long long d : 47;
    unsigned char e;
};

int main(void) {
    volatile int sh = 70;
    i128 a = (i128)0x123456789abcdefll << 40, b = -((i128)987654321 << 70);
    p128("add", a + b);
    p128("sub", a - b);
    p128("mul", mul(a, 12345));
    p128("div", b / 1234567);
    p128("rem", b % 1234567);
    p128("udiv", (u128)b / 99);
    p128("shl", a << sh);
    p128("lshr", (u128)b >> sh);
    p128("ashr", b >> sh);
    p128("and", a & b);
    printf("%d %d %d %d\n", a < b, a > b, (u128)a < (u128)b, a == a);
    printf("%.10g %.10g\n", (double)b, (double)(u128)a);
    p128("fromd", (i128)-1.5e30);
    p128("fromdu", (u128)3.2e38);
    struct B s = {0x9ffff, 9, 0x123456789aull, -0x123456789ll, 7};
    s.a += 3;
    s.c ^= 0xffffffffffull;
    s.d -= 5;
    printf("%x %x %llx %lld %d\n", s.a, s.b, (unsigned long long)s.c, (long long)s.d, s.e);
    printf("%d %d %d %d %d %d\n", sw(0), sw(5), sw((u128)1 << 100), sw(~(u128)0), sw(6), sw((u128)5 << 64));
    return 0;
}
