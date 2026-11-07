/* Driver of agg.ll: the callees of its small-aggregate returns, and calls of
   its functions with the results printed. */
#include <stdio.h>

typedef struct { float x, y, z, w; } V4;
typedef struct { float x, y, z; } V3;
typedef struct { double re, im; } C2;
typedef struct { long n; double d; } LD;
typedef struct { double d; int n; } DI;
typedef struct { char c; double d; } CD;
typedef struct { void *p; int n; } PI;
typedef struct { long a, b; } LL;
typedef struct { float a; double b; } FD;

V4 mk4(float a, float b, float c, float d) { V4 v = {a, b, c, d}; return v; }
V3 mk3(float a, float b, float c) { V3 v = {a, b, c}; return v; }
C2 mkc(double a, double b) { C2 v = {a, b}; return v; }
LD mkld(long a, double b) { LD v = {a, b}; return v; }
DI mkdi(double a, int b) { DI v = {a, b}; return v; }
CD mkcd(int a, double b) { CD v = {(char)a, b}; return v; }
PI mkpi(void *a, int b) { PI v = {a, b}; return v; }
LL mkll(long a, long b) { LL v = {a, b}; return v; }
FD mkfd(float a, double b) { FD v = {a, b}; return v; }

/* writes every xmm register a call may clobber, and a few general ones */
volatile double vd = 3.5;
volatile long vl = 11;
void clobber(void) {
    double a = vd, b = a * 2, c = b * 3, d = c * 4, e = d + a, f = e + b, g = f + c, h = g + d;
    vd = a + b + c + d + e + f + g + h;
    vd = 3.5;
    vl = vl * 3 + 1;
    vl = 11;
}

float t_swap(float, float, float, float);
float t_call_between(float, float, float, float);
double t_dup(double, double);
double t_other_block(double, double, int);
double t_partial(double, double);
double t_gpr(long, double, long *);
double t_whole_use(double, double, C2 *);
double t_legacy_between(double, double, long);
float t_live_across(float, float, float);
C2 t_load_ret(double, double);
C2 t_load_ret_ptr(C2 *);
C2 t_load_store_ret(double, double);
V4 t_load_ret4(float, float, float, float);
double t_ev_sources(long, double, double, double);

int main(void) {
    long cell = 123456;
    C2 out = {0, 0};
    printf("swap %g\n", t_swap(1.5f, 2.5f, -3.25f, 4.0f));
    printf("call_between %g\n", t_call_between(1.5f, 2.5f, -3.25f, 4.0f));
    printf("dup %g\n", t_dup(1.25, -2.5));
    printf("other_block %g %g\n", t_other_block(1.25, -2.5, 1), t_other_block(1.25, -2.5, 0));
    printf("partial %g\n", t_partial(1.25, -2.5));
    printf("gpr %.17g\n", t_gpr(1000000007L, 0.125, &cell));
    printf("whole_use %g [%g %g]\n", t_whole_use(6.5, 7.75, &out), out.re, out.im);
    printf("legacy_between %g %g\n", t_legacy_between(1.0, 2.0, 5), t_legacy_between(-1.0, 0.5, 0x123456789L));
    printf("live_across %g\n", t_live_across(1.0f, 2.0f, 3.0f));
    C2 a = t_load_ret(2.5, -0.5);
    C2 b = t_load_ret_ptr(&a);
    C2 c = t_load_store_ret(9.0, 8.0);
    V4 d = t_load_ret4(1.0f, -2.0f, 3.5f, 0.25f);
    printf("load_ret %g %g | %g %g | %g %g | %g %g %g %g\n", a.re, a.im, b.re, b.im, c.re, c.im, d.x, d.y, d.z, d.w);
    printf("ev_sources %g %g\n", t_ev_sources(5, 2.0, 0.5, 0.25), t_ev_sources(1, -2.0, 0.5, 0.25));
    return 0;
}
