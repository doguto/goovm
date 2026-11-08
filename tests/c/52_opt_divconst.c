// Division and remainder by constants (the optimizer turns them into
// multiplications by a reciprocal, shifts and masks), signed and unsigned,
// at the edges of the ranges; also by powers of two and by -1 / 1.
#include <limits.h>
#include <stdio.h>

static unsigned long long h = 1469598103934665603ULL;
static void mix(long long v) { h = (h ^ (unsigned long long)v) * 1099511628211ULL; }

#define UDIV(d)                                                   \
    static void ud##d(unsigned x) { mix(x / d); mix(x % d); }    \
    static void sd##d(int x) { mix(x / d); mix(x % d); }

UDIV(3) UDIV(5) UDIV(6) UDIV(7) UDIV(9) UDIV(10) UDIV(11) UDIV(13) UDIV(25) UDIV(60) UDIV(100)
UDIV(641) UDIV(1000) UDIV(3600) UDIV(65537) UDIV(1000000007) UDIV(2147483647) UDIV(2) UDIV(4)
UDIV(8) UDIV(1024) UDIV(1)

static void ubig(unsigned x) {
    mix(x / 3000000000u); mix(x % 3000000000u);
    mix(x / 2147483649u); mix(x % 2147483649u);
    mix(x / 4294967295u); mix(x % 4294967295u);
}
static void sneg(int x) { mix(x / -1 + 0LL); mix(x / -7); mix(x % -7); mix(x / -2); mix(x % -2); }
static void narrow(unsigned char c, short s, long long l, unsigned long long u) {
    mix(c / 7); mix(c % 7); mix(s / 7); mix(s % 7); mix(l / 7); mix(l % 7); mix(u / 7); mix(u % 7);
    mix(l / 1000000007LL); mix(u % 1000000007ULL);
}

int main(void) {
    static const unsigned edges[] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 99, 100, 101, 1023, 1024, 65535, 65536,
                                     65537, 1000000006u, 1000000007u, 0x7FFFFFFEu, 0x7FFFFFFFu, 0x80000000u,
                                     0x80000001u, 0xFFFFFFFEu, 0xFFFFFFFFu, 3000000000u, 2999999999u};
    unsigned seed = 12345;
    for (int i = 0; i < 20000; i++) {
        unsigned x = i < (int)(sizeof edges / sizeof edges[0]) ? edges[i] : (seed = seed * 1103515245u + 12345u);
        if (i >= 10000) x >>= (i % 31);
        int sx = (int)x;
        ud3(x); sd3(sx); ud5(x); sd5(sx); ud6(x); sd6(sx); ud7(x); sd7(sx); ud9(x); sd9(sx);
        ud10(x); sd10(sx); ud11(x); sd11(sx); ud13(x); sd13(sx); ud25(x); sd25(sx); ud60(x); sd60(sx);
        ud100(x); sd100(sx); ud641(x); sd641(sx); ud1000(x); sd1000(sx); ud3600(x); sd3600(sx);
        ud65537(x); sd65537(sx); ud1000000007(x); sd1000000007(sx); ud2147483647(x); sd2147483647(sx);
        ud2(x); sd2(sx); ud4(x); sd4(sx); ud8(x); sd8(sx); ud1024(x); sd1024(sx); ud1(x); sd1(sx);
        ubig(x);
        if (sx != INT_MIN) sneg(sx);
        narrow((unsigned char)x, (short)x, (long long)sx * 977, (unsigned long long)x * 977);
    }
    printf("%llx\n", h);
    return 0;
}
