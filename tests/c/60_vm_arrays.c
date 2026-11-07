// Arrays whose elements are VLAs (variably modified arrays with a constant
// outer bound): `char c[10][n]` must get 10*n bytes of dynamic stack, be
// released at the end of its scope (also in loops), and index, sizeof and
// pass to functions like any VLA. goosecc once gave these 1 byte.
#include <stdio.h>
#include <string.h>

static long sum2(int rows, int n, int (*a)[n]) {
    long s = 0;
    for (int i = 0; i < rows; i++)
        for (int j = 0; j < n; j++) s += a[i][j];
    return s;
}

static int rows_of(int n) {
    char c[10][n];
    int canary = 0x5eed;
    memset(c, 'a', sizeof c);
    for (int i = 0; i < 10; i++) c[i][n - 1] = (char)('0' + i);
    int ok = canary == 0x5eed && c[9][n - 1] == '9' && c[0][0] == 'a';
    printf("rows n=%d sizeof=%zu row=%zu ok=%d\n", n, sizeof c, sizeof c[0], ok);
    return ok;
}

static int three_d(int n) {
    int a[2][n][4];
    int guard = 77;
    for (int i = 0; i < 2; i++)
        for (int j = 0; j < n; j++)
            for (int k = 0; k < 4; k++) a[i][j][k] = i * 100 + j * 10 + k;
    long s = 0;
    for (int i = 0; i < 2; i++)
        for (int j = 0; j < n; j++)
            for (int k = 0; k < 4; k++) s += a[i][j][k];
    printf("3d n=%d sizeof=%zu sum=%ld guard=%d\n", n, sizeof a, s, guard);
    return guard == 77;
}

int main(void) {
    int ok = 1;
    for (int n = 1; n <= 64; n *= 2) ok &= rows_of(n);
    ok &= three_d(5);
    // a loop that allocates an array of VLA rows every iteration must not
    // grow the stack without bound
    long total = 0;
    for (int it = 0; it < 20000; it++) {
        int n = 50 + it % 7;
        int m[3][n];
        for (int i = 0; i < 3; i++)
            for (int j = 0; j < n; j++) m[i][j] = i + j;
        total += sum2(3, n, m);
    }
    printf("loop total=%ld\n", total);
    return ok ? 0 : 1;
}
