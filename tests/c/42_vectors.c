// GCC vector extensions: lane-wise arithmetic, compares, shuffles, vector
// arguments and returns.
#include <stdio.h>

typedef int v4si __attribute__((vector_size(16)));
typedef float v4sf __attribute__((vector_size(16)));
typedef double v2df __attribute__((vector_size(16)));
typedef short v8hi __attribute__((vector_size(16)));
typedef unsigned char v16qi __attribute__((vector_size(16)));
typedef float v2sf __attribute__((vector_size(8)));
typedef int v8si __attribute__((vector_size(32)));

static v4si addmul(v4si a, v4si b) { return (a + b) * b - (a >> 1); }
static v4sf fma4(v4sf a, v4sf b, v4sf c) { return a * b + c; }
static v2df divd(v2df a, v2df b) { return a / b; }
static v2sf swap2(v2sf a) { return (v2sf){a[1], a[0]}; }
static v8si wide(v8si a) { return a * 3 + 1; }

int main(void) {
    v4si a = {1, 2, 3, 4}, b = {10, -20, 30, -40};
    v4si r = addmul(a, b);
    v4si c = a < b;
    v4sf f = fma4((v4sf){1, 2, 3, 4}, (v4sf){0.5f, 0.25f, 2, 3}, (v4sf){1, 1, 1, 1});
    v2df d = divd((v2df){1, 9}, (v2df){4, 3});
    v8hi h = {1, 2, 3, 4, 5, 6, 7, 8};
    h = h * h - (v8hi){8, 7, 6, 5, 4, 3, 2, 1};
    v16qi q = {0};
    for (int i = 0; i < 16; i++) q[i] = i * 17;
    q = q / (unsigned char)3 + q % (unsigned char)5;
    v2sf s = swap2((v2sf){1.5f, 2.5f});
    v8si w = wide((v8si){1, 2, 3, 4, 5, 6, 7, 8});
    v4si sh = __builtin_shufflevector(a, b, 7, 0, 5, 2);
    printf("%d %d %d %d | %d %d %d %d\n", r[0], r[1], r[2], r[3], c[0], c[1], c[2], c[3]);
    printf("%g %g %g %g | %g %g | %g %g\n", f[0], f[1], f[2], f[3], d[0], d[1], s[0], s[1]);
    printf("%d %d %d %d | %d %d %d | %d %d %d %d\n", h[0], h[3], h[7], w[7], q[1], q[8], q[15], sh[0], sh[1], sh[2],
           sh[3]);
    return 0;
}
