// Small structs passed by value (clang coerces them to integer arguments)
// and returned by value (<= 8 bytes in a register, larger via sret).
#include <stdio.h>

struct P2 { int x, y; };
struct L2 { long a, b; };
struct M3 { int a, b, c; };
struct C4 { char c[4]; };
struct S8 { short s[4]; };
struct Big { long v[4]; };

static int dot(struct P2 a, struct P2 b) { return a.x * b.x + a.y * b.y; }
static long lsum(struct L2 v) { return v.a - v.b; }
static int m3(struct M3 m, int k) { return (m.a + m.b * 2 + m.c * 3) * k; }
static int c4(struct C4 c) { return c.c[0] + c.c[1] * 2 + c.c[2] * 3 + c.c[3] * 4; }
static int s8(struct S8 s) { return s.s[0] * s.s[1] - s.s[2] + s.s[3]; }
static struct P2 swap(struct P2 p) { struct P2 r = {p.y, p.x}; return r; }
static struct C4 rot(struct C4 c) { struct C4 r = {{c.c[1], c.c[2], c.c[3], c.c[0]}}; return r; }
static struct Big mk(long base) { struct Big b = {{base, base * 2, base * 3, base * 4}}; return b; }
static long many(struct P2 a, struct L2 b, struct M3 c, int d, struct P2 e, struct P2 f) {
    return a.x + b.a + c.c + d + e.y + f.x * 10;
}

int main(void) {
    struct P2 a = {3, 4}, b = {-5, 6};
    printf("%d\n", dot(a, b));
    struct L2 l = {10000000000L, 3};
    printf("%ld\n", lsum(l));
    struct M3 m = {1, 2, 3};
    printf("%d\n", m3(m, 5));
    struct C4 c = {{1, 2, 3, 4}};
    printf("%d %d\n", c4(c), c4(rot(c)));
    struct S8 s = {{7, -8, 9, -10}};
    printf("%d\n", s8(s));
    struct P2 sw = swap(a);
    printf("%d %d\n", sw.x, sw.y);
    struct Big big = mk(-3);
    printf("%ld %ld\n", big.v[0], big.v[3]);
    printf("%ld\n", many(a, l, m, 9, b, sw));
    return 0;
}
