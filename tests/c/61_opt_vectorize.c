// Loops the loop vectorizer takes (or must refuse) at -O2: reductions,
// runtime alias checks, splats of invariants, lane widths 1..8, and the
// cases that once went wrong: a second counter used by the body (not a
// reduction: shootout ary3), a loop vectorized after inlining into a loop
// whose scalar remainder must not be vectorized again (linpack dgesl), and
// an invariant load at a constant offset checked against the stores
// (McGill chomp).
#include <stdio.h>

static int sum(const int *a, int n) { int s = 0; for (int i = 0; i < n; i++) s += a[i]; return s; }
static long xs(const long *a, long n) { long s = 0; for (long i = 0; i < n; i++) s ^= a[i]; return s; }
static void madd(int *restrict d, const int *restrict a, const int *restrict b, int n) {
    for (int i = 0; i < n; i++) d[i] = a[i] * b[i] + 3;
}
static void axpy(float *d, const float *a, float k, int n) { for (int i = 0; i < n; i++) d[i] = d[i] + k * a[i]; }
static void shl(short *d, const short *a, int n) { for (int i = 0; i < n; i++) d[i] = (short)(a[i] << 2) + 7; }
static void bytes(unsigned char *d, const unsigned char *a, int n) { for (int i = 0; i < n; i++) d[i] = a[i] ^ 0x5a; }

// x[i] = ++k: k is a second induction variable, not a reduction
static void count(int *x, int n) { int k = 0; for (int i = 0; i < n; i++) x[i] = ++k; }

// daxpy inlined into a loop whose multiplier is computed outside the inner loop
static void daxpy(int n, double da, const double *dx, double *dy) {
    for (int i = 0; i < n; i++) dy[i] = dy[i] + da * dx[i];
}
static void solve(double *a, double *b, int n) {
    for (int k = 0; k < n - 1; k++) {
        double t = -b[k] / a[k * n + k];
        daxpy(n - k - 1, t, &a[k * n + k + 1], &b[k + 1]);
    }
}

// a load of a fixed element of the array the loop stores into
struct board { int w; int cell[40]; };
static void fill(struct board *bd, int n) { for (int i = 0; i < n; i++) bd->cell[i] = bd->cell[3] + i; }

int main(void) {
    int a[103], b[103], d[103], x[67];
    float f[103], g[103];
    short p[77], q[77];
    long l[33];
    unsigned char u[50], v[50];
    for (int i = 0; i < 103; i++) { a[i] = i * 7 - 50; b[i] = i ^ 5; f[i] = i * 0.5f; g[i] = 1.0f / (i + 1); }
    for (int i = 0; i < 77; i++) q[i] = (short)(i * 3 - 100);
    for (int i = 0; i < 33; i++) l[i] = (long)i * 0x123456789L;
    for (int i = 0; i < 50; i++) v[i] = (unsigned char)(i * 11);
    for (int n = 0; n < 103; n += 7) printf("%d ", sum(a, n));
    printf("\n");
    madd(d, a, b, 103);
    for (int i = 0; i < 103; i += 9) printf("%d ", d[i]);
    printf("\n");
    axpy(f, g, 2.5f, 103);
    for (int i = 0; i < 103; i += 9) printf("%g ", f[i]);
    axpy(f + 1, f, 0.5f, 50);     // (overlapping: the runtime check takes the scalar loop)
    for (int i = 0; i < 103; i += 9) printf("%g ", f[i]);
    printf("\n");
    shl(p, q, 77);
    for (int i = 0; i < 77; i += 5) printf("%d ", p[i]);
    bytes(u, v, 50);
    for (int i = 0; i < 50; i += 7) printf("%d ", u[i]);
    printf("%ld\n", xs(l, 33));
    count(x, 67);
    printf("%d %d %d\n", x[0], x[33], x[66]);
    double m[11 * 11], r[11];
    for (int i = 0; i < 11 * 11; i++) m[i] = (i % 11 == i / 11) ? 4.0 : 1.0 / (i + 1);
    for (int i = 0; i < 11; i++) r[i] = i + 1;
    solve(m, r, 11);
    for (int i = 0; i < 11; i++) printf("%.6f ", r[i]);
    printf("\n");
    struct board bd;
    for (int i = 0; i < 40; i++) bd.cell[i] = i * 2;
    fill(&bd, 40);
    printf("%d %d %d %d\n", bd.cell[0], bd.cell[3], bd.cell[4], bd.cell[39]);
    return 0;
}
