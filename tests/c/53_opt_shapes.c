// Shapes the optimizer transforms: short-circuit loop conditions (jump
// threading), stores overwritten in a block (dead-store elimination) next to
// aliasing pointers, struct temporaries and copies (SROA), small functions
// with narrow arguments and returns (inlining), loop invariants (LICM),
// loops whose header test moves to the bottom (layout rotation), values
// live across calls and many live values (register allocation).
#include <stdio.h>
#include <string.h>

static unsigned long long h = 14695981039346656037ULL;
static void mix(long long v) { h = (h ^ (unsigned long long)v) * 1099511628211ULL; }

// --- && / || conditions
static int count_prefix(const char *s, const char *p) {
    int k = 0;
    while (s[k] && p[k] && s[k] == p[k]) k++;
    return k;
}
static int find_any(const int *a, int n, int x, int y) {
    int i = 0;
    while (i < n && !(a[i] == x || a[i] == y)) i++;
    return i;
}

// --- stores, aliasing
static int g1, g2;
static void stores(int *p, int *q, int v) {
    *p = v;
    *p = v + 1;          // the first store is dead
    *q = *p + 2;         // q may be p
    *p = *q * 3;
    g1 = v;
    g2 = g1 + 1;
    g1 = g2 + 1;
}
static int local_stores(int v) {
    int a[4];
    a[0] = v; a[1] = v * 2; a[0] = a[1] + 1; a[2] = a[0]; a[3] = a[2] + a[0];
    return a[3] + a[1];
}

// --- structs
struct P { double x, y; };
struct Q { int a; short b; char c; long long d; };
static struct P padd(struct P a, struct P b) { struct P r = {a.x + b.x, a.y + b.y}; return r; }
static struct Q qmake(int i) { struct Q q; memset(&q, 0, sizeof q); q.a = i; q.b = (short)(i * 3); q.c = (char)i; q.d = (long long)i << 33; return q; }
static long long qsum(const struct Q *q) { return q->a + q->b + q->c + q->d; }

// --- narrow arguments and returns
static signed char sc(signed char a, signed char b) { return (signed char)(a * b + 7); }
static unsigned short us(unsigned short a) { return (unsigned short)(a * 3 + 1); }
static short ss(short a, int k) { return (short)(a >> k); }
static _Bool nz(long x) { return x != 0; }

// --- invariants
static long inv(const long *a, int n, int m, long s) {
    long t = 0;
    for (int i = 0; i < n; i++)
        for (int j = 0; j < m; j++) t += a[(i * m + j) % 97] * (s * 3 + n) + (m << 2);
    return t;
}

// --- pressure and calls
__attribute__((noinline)) static long ext(long x) { return x * 7 + 1; }
static long pressure(long a, long b, long c, long d, long e, long f) {
    long g = a + b, i = c * d, j = e - f, k = a ^ f, l = b | e, m = c & d, n = a * f, o = b - c;
    long p = d + e, q = f * 3, r = a - e, s = b + f;
    for (int t = 0; t < 10; t++) {
        g += ext(i) + j; i ^= k + ext(l); j += m * n; k -= o + p; l += q ^ r; m += s; n -= g;
        o += i; p ^= j; q += k; r -= l; s += m;
    }
    return g + i + j + k + l + m + n + o + p + q + r + s;
}
static double fpress(double a, double b, int n) {
    double x = a, y = b, z = a * b, w = a - b, u = 1.5, v = 2.5, s = 0;
    for (int i = 0; i < n; i++) {
        x = x * 0.5 + y; y = y * 0.25 + z; z = z - w * 0.125; w = w + u; u = u * 0.99; v = v + x;
        s += x + y + z + w + u + v;
    }
    return s;
}

// --- switch in a loop, early exits
static int classify(int x) {
    int r = 0;
    for (int i = 0; i < 8; i++) {
        switch ((x >> i) & 7) {
        case 0: r += 1; break;
        case 1: case 2: r += 3; continue;
        case 5: r -= 2; if (r < -5) return r; break;
        default: r ^= i;
        }
        if (r > 20) break;
    }
    return r;
}

int main(void) {
    const char *words[] = {"alpha", "alphabet", "beta", "al", "", "alp"};
    for (int i = 0; i < 6; i++)
        for (int j = 0; j < 6; j++) mix(count_prefix(words[i], words[j]));
    int arr[50];
    for (int i = 0; i < 50; i++) arr[i] = (i * 37) % 23;
    for (int x = 0; x < 25; x++) mix(find_any(arr, 50, x, 22 - x));
    int u = 0, v = 0;
    for (int i = 0; i < 5; i++) {
        stores(&u, &v, i); mix(u); mix(v); mix(g1); mix(g2);
        stores(&u, &u, i); mix(u); mix(g1);
        mix(local_stores(i));
    }
    struct P acc = {0, 0};
    for (int i = 0; i < 100; i++) { struct P d = {i * 0.5, -i * 0.25}; acc = padd(acc, d); }
    mix((long long)(acc.x * 1000)); mix((long long)(acc.y * 1000));
    long long qs = 0;
    for (int i = -5; i < 300; i += 7) { struct Q q = qmake(i); struct Q r = q; r.a++; qs += qsum(&q) - qsum(&r); qs += qsum(&r); }
    mix(qs);
    for (int i = -130; i < 130; i += 3) {
        mix(sc((signed char)i, (signed char)(i + 1))); mix(us((unsigned short)(i * 1000)));
        mix(ss((short)(i * 300), i & 7)); mix(nz(i));
    }
    long la[97];
    for (int i = 0; i < 97; i++) la[i] = i * i - 50;
    mix(inv(la, 13, 11, 5)); mix(inv(la, 0, 11, 5)); mix(inv(la, 7, 0, 1));
    mix(pressure(1, 2, 3, 4, 5, 6)); mix(pressure(-9, 8, -7, 6, -5, 4));
    mix((long long)(fpress(1.0, 2.0, 50) * 1e6));
    for (int x = 0; x < 300; x += 7) mix(classify(x * 2654435761u));
    printf("%llx\n", h);
    return 0;
}
