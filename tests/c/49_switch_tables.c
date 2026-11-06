// Dense switches become jump tables (rel32 entries after the indirect jump):
// negative and offset ranges, holes going to the default, shared targets,
// 8/16/64-bit selectors, PHIs on the edges (mem2reg variant: stubs), the
// default with PHIs, tables inside loops (backward targets), a large table.
#include <stdio.h>
#include <stdint.h>

__attribute__((noinline)) static int dense(int k, int x) {
    int r;
    switch (k) {
    case -2: r = x - 2; break;
    case -1: r = x * 3; break;
    case 0: r = x + 1; break;
    case 1: r = x ^ 5; break;
    case 3: r = -x; break;          // (2 is a hole)
    case 4: r = x << 2; break;
    case 5: r = x * 3; break;
    default: r = 1000 + k;
    }
    return r;
}
__attribute__((noinline)) static int shared(unsigned char c) {
    switch (c) {
    case 'a': case 'e': case 'i': case 'o': case 'u': return 1;
    case 'b': case 'c': case 'd': return 2;
    case 'f': case 'g': case 'h': return 3;
    case 'j': case 'k': return 4;
    default: return 0;
    }
}
__attribute__((noinline)) static long sel16(short s) {
    switch (s) {
    case 1000: return 1;
    case 1001: return 22;
    case 1002: return 333;
    case 1003: return 4444;
    case 1005: return 55555;
    default: return -1;
    }
}
__attribute__((noinline)) static long long sel64(long long k) {
    switch (k) {
    case 0x100000000LL: return 1;
    case 0x100000001LL: return 2;
    case 0x100000002LL: return 3;
    case 0x100000003LL: return 4;
    default: return 0;
    }
}
__attribute__((noinline)) static long long selneg64(long long k) {
    switch (k) {
    case -6: return 60;
    case -5: return 50;
    case -4: return 40;
    case -3: return 30;
    case -1: return 10;
    default: return k;
    }
}
// PHIs: values flowing into the join from every case (and the default).
__attribute__((noinline)) static int phis(int k, int a, int b) {
    int x = a, y = b;
    switch (k) {
    case 0: x = b; y = a; break;   // swap on the edge
    case 1: x = a + b; break;
    case 2: y = a - b; break;
    case 3: break;
    case 4: x = y = 7; break;
    default: x = -a; y = -b; break;
    }
    return x * 100 + y;
}
// A table in a loop: the targets are backward and forward blocks.
__attribute__((noinline)) static int interp(const unsigned char *code, int n) {
    int acc = 0, pc = 0, steps = 0;
    while (pc < n && steps < 1000) {
        steps++;
        switch (code[pc]) {
        case 0: acc += 1; pc++; break;
        case 1: acc *= 2; pc++; break;
        case 2: acc -= 3; pc++; break;
        case 3: pc = acc & 1 ? pc + 2 : pc + 1; break;
        case 4: acc ^= 0x55; pc++; break;
        case 5: if (acc > 0) { pc = 0; acc -= 100; } else pc++; break;
        default: return -acc;
        }
    }
    return acc;
}
// A big table (64 entries, some holes).
__attribute__((noinline)) static unsigned big(unsigned k) {
    unsigned r = 0;
    switch (k) {
#define C(n) case n: r = n * 7 + 1; break;
    C(10) C(11) C(12) C(13) C(14) C(15) C(16) C(17) C(18) C(19)
    C(20) C(21) C(22) C(24) C(25) C(26) C(27) C(28) C(29)
    C(30) C(31) C(33) C(34) C(35) C(36) C(37) C(38) C(39)
    C(40) C(41) C(42) C(43) C(45) C(46) C(47) C(48) C(49)
    C(50) C(51) C(52) C(53) C(54) C(55) C(56) C(57) C(58) C(59)
    C(60) C(62) C(63) C(64) C(65) C(66) C(67) C(68) C(69) C(70) C(73)
#undef C
    default: r = k;
    }
    return r;
}
// The selector is live after the switch and lives across calls.
__attribute__((noinline)) static int ident(int x) { return x; }
__attribute__((noinline)) static int live(int k) {
    int t = 0;
    switch (k) {
    case 7: t = ident(k) + 1; break;
    case 8: t = ident(k * 2); break;
    case 9: t = 3; break;
    case 10: t = ident(k) - k; break;
    default: t = -1;
    }
    return t + k;
}

int main(void) {
    long sum = 0;
    for (int k = -4; k <= 7; k++) { int v = dense(k, 11); printf("dense %d %d\n", k, v); sum += v; }
    for (int c = 'Z'; c <= 'm'; c++) sum += shared((unsigned char)c) * c;
    printf("shared %ld\n", sum);
    for (int s = 998; s <= 1007; s++) printf("sel16 %d %ld\n", s, sel16((short)s));
    printf("sel16 %ld\n", sel16(-24536));
    for (long long k = 0xFFFFFFFELL; k <= 0x100000005LL; k++) printf("sel64 %lld\n", sel64(k));
    for (long long k = -8; k <= 1; k++) printf("selneg64 %lld\n", selneg64(k));
    printf("selneg64 %lld %lld\n", selneg64(INT64_MIN), selneg64(INT64_MAX));
    for (int k = -1; k <= 6; k++) printf("phis %d %d\n", k, phis(k, 5, 9));
    static const unsigned char prog[] = {0, 0, 1, 3, 4, 2, 1, 5, 0, 1, 1, 9};
    printf("interp %d %d\n", interp(prog, 11), interp(prog, 12));
    unsigned bs = 0;
    for (unsigned k = 0; k < 80; k++) bs = bs * 31 + big(k);
    printf("big %u %u %u\n", bs, big(0xFFFFFFFFu), big(0x8000000Au));
    for (int k = 5; k <= 12; k++) printf("live %d %d\n", k, live(k));
    return 0;
}
