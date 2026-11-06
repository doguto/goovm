// ?:, && and || (PHIs at -O0), short-circuit side effects, _Bool.
#include <stdio.h>

static int calls;
static int t(int v) { calls++; return v; }

int main(void) {
    int r = 0;
    for (int i = 0; i < 16; i++) {
        int a = i & 1, b = i & 2, c = i & 4, d = i & 8;
        r = r * 3 + ((a && b) || (c && !d));
        r += (a || b) && (c || d) ? 5 : -2;
        r ^= a ? (b ? 1 : 2) : (c ? 3 : (d ? 4 : 5));
    }
    printf("r %d\n", r);
    calls = 0;
    int x = t(0) && t(1);
    int y = t(1) || t(0);
    int z = t(1) && t(2) && t(0) && t(3);
    int w = t(0) || t(0) || t(5);
    printf("%d %d %d %d calls %d\n", x, y, z, w, calls);
    _Bool b1 = 5, b2 = 0, b3 = b1 + b1;
    printf("%d %d %d %d\n", b1, b2, b3, !b1);
    int m = 7, n = -3;
    int mx = m > n ? m : n, mn = m < n ? m : n;
    unsigned um = (unsigned)n > (unsigned)m ? 1u : 0u;
    printf("%d %d %u\n", mx, mn, um);
    const char *s = calls > 5 ? "many" : "few";
    printf("%s\n", s);
    long acc = 0;
    for (int i = -5; i <= 5; i++) acc += i < 0 ? -i : i > 2 ? i * i : i;
    printf("%ld\n", acc);
    int k = 0;
    while (k < 100 && (k % 7 != 6 || k < 30)) k++;
    printf("k %d\n", k);
    return 0;
}
