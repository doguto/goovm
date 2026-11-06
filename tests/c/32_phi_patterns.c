// Loop shapes that become PHI webs after mem2reg: swaps, rotations, multiple
// exits, values live across loops.
#include <stdio.h>

static int swapper(int n) {
    int a = 1, b = 2, c = 3;
    for (int i = 0; i < n; i++) { int t = a; a = b; b = c; c = t + i; }
    return a * 100 + b * 10 + c;
}
static long fibl(int n) {
    long a = 0, b = 1;
    while (n-- > 0) { long t = a + b; a = b; b = t; }
    return a;
}
static int find_first(const int *v, int n, int key, int *steps) {
    int i = 0, s = 0;
    for (; i < n; i++) {
        s++;
        if (v[i] == key) break;
        if (v[i] > 1000) { i = -1; break; }
    }
    *steps = s;
    return i;
}
static unsigned collatz_max(unsigned n) {
    unsigned mx = n;
    while (n != 1) {
        n = (n & 1) ? 3 * n + 1 : n >> 1;
        mx = n > mx ? n : mx;
    }
    return mx;
}
static int nested(int n) {
    int x = 0, y = 1;
    for (int i = 0; i < n; i++) {
        int z = x;
        for (int j = 0; j < i; j++) { z += y; y = z - y; if (z > 10000) z -= 9999; }
        x = z ^ y;
    }
    return x + y;
}

int main(void) {
    for (int i = 0; i < 6; i++) printf("%d ", swapper(i));
    printf("\n%ld %ld\n", fibl(10), fibl(80));
    int v[] = {5, 9, 2, 7, 3000, 4};
    int st;
    int r1 = find_first(v, 6, 7, &st);
    printf("%d %d ", r1, st);
    int r2 = find_first(v, 6, 4, &st);
    printf("%d %d ", r2, st);
    int r3 = find_first(v, 3, 4, &st);
    printf("%d %d\n", r3, st);
    printf("%u %u\n", collatz_max(27), collatz_max(97));
    printf("%d\n", nested(30));
    return 0;
}
