// Struct arguments and returns in every ABI class, _Complex, byval, sret.
#include <complex.h>
#include <stdio.h>

typedef struct { long a, b; } LL;
typedef struct { double x, y; } DD;
typedef struct { float x, y; } FF;
typedef struct { float x, y, z; } FFF;
typedef struct { long a; double d; } LD;
typedef struct { char c; long l; } CL;
typedef struct { char c[3]; } C3;
typedef struct { short s[3]; } S3;
typedef struct { int i[5]; } Big;
typedef struct { long double v; } X;
typedef struct __attribute__((aligned(32))) { double d[4]; } A32;

static LL mk_ll(long a) { LL r = {a, a * 2}; return r; }
static DD mk_dd(double a) { DD r = {a, -a}; return r; }
static FF mk_ff(float a) { FF r = {a, a + 1}; return r; }
static FFF mk_fff(float a) { FFF r = {a, a * 2, a * 3}; return r; }
static LD mk_ld(long a) { LD r = {a, a / 4.0}; return r; }
static CL mk_cl(char c) { CL r = {c, c * 1000L}; return r; }
static C3 mk_c3(char c) { C3 r = {{c, c + 1, c + 2}}; return r; }
static S3 mk_s3(short s) { S3 r = {{s, s + 1, s + 2}}; return r; }
static Big mk_big(int i) { Big r = {{i, i + 1, i + 2, i + 3, i + 4}}; return r; }
static X mk_x(long double v) { X r = {v * 2}; return r; }

static long use_all(LL a, DD b, FF c, FFF d, LD e, CL f, C3 g, S3 h, Big i, X j, A32 k) {
    return a.a + a.b + (long)(b.x * 10 + b.y) + (long)(c.x + c.y) + (long)(d.x + d.y + d.z) + e.a + (long)(e.d * 8) +
           f.c + f.l + g.c[0] + g.c[1] + g.c[2] + h.s[0] + h.s[2] + i.i[0] + i.i[4] + (long)j.v + (long)k.d[3];
}
static double complex cmul(double complex a, double complex b) { return a * b; }
static float complex cmulf(float complex a, float complex b) { return a * b; }
static long double complex cmull(long double complex a, long double complex b) { return a * b; }

int main(void) {
    A32 k = {{1, 2, 3, 4}};
    printf("%ld\n", use_all(mk_ll(3), mk_dd(1.5), mk_ff(2), mk_fff(1), mk_ld(8), mk_cl(5), mk_c3(1), mk_s3(7),
                            mk_big(10), mk_x(2.5L), k));
    double complex z = cmul(1 + 2 * I, 3 - I);
    float complex w = cmulf(1 + 2 * I, 3 - I);
    long double complex v = cmull(1 + 2 * I, 3 - I);
    printf("%g %g %g %g %Lg %Lg\n", creal(z), cimag(z), crealf(w), cimagf(w), creall(v), cimagl(v));
    Big b = mk_big(1);
    b.i[2] += 40;
    printf("%d %d\n", b.i[2], mk_big(b.i[2]).i[4]);
    return 0;
}
