/* Integer <-> FP conversions at the limits of every width (signed and
   unsigned, 8 to 64 bits, rounding of wide integers to float and double),
   float <-> double (overflow to infinity, underflow to subnormals and zero,
   NaN, -0.0) and mixed float/double arithmetic. Values come through
   volatiles so that every conversion is an instruction. */
#include <stdio.h>
#include <string.h>

static volatile long vl[] = {0, 1, -1, 2147483647L, -2147483647L - 1, 4294967295L, 9007199254740993L,
                             9223372036854775807L, -9223372036854775807L - 1, 16777217, -16777217};
static volatile unsigned long vu[] = {0, 1, 4294967295UL, 9007199254740993UL, 9223372036854775808UL,
                                      9223372036854775809UL, 18446744073709551615UL, 18446744073709549568UL,
                                      9223373136366403584UL};
static volatile double vd[] = {0.0, -0.0, 0.9, -0.9, 2147483647.0, -2147483648.0, 4294967295.0,
                               9223372036854774784.0, -9223372036854775808.0, 18446744073709549568.0,
                               9223372036854775808.0, 255.9, -128.5, 65535.0, -32768.0};
static volatile double vbig[] = {1e39, -1e39, 1e-46, -1e-46, 3.4028235677973366e38, 1.1754943508222875e-38,
                                 1.401298464324817e-45, 0.1};

static unsigned long dbits(double d) { unsigned long b; memcpy(&b, &d, 8); return b; }
static unsigned fbits(float f) { unsigned b; memcpy(&b, &f, 4); return b; }

int main(void) {
    int n = sizeof vl / sizeof vl[0];
    for (int i = 0; i < n; i++) {
        long x = vl[i];
        int x32 = (int)x;
        printf("l %2d: d=%.17g f=%.9g d32=%.17g f32=%.9g u32d=%.17g u32f=%.9g\n", i, (double)x, (float)x,
               (double)x32, (float)x32, (double)(unsigned)x32, (float)(unsigned)x32);
    }
    n = sizeof vu / sizeof vu[0];
    for (int i = 0; i < n; i++) {
        unsigned long x = vu[i];
        printf("u %2d: d=%.17g f=%.9g\n", i, (double)x, (float)x);
    }
    n = sizeof vd / sizeof vd[0];
    for (int i = 0; i < n; i++) {
        double d = vd[i];
        float f = (float)d;
        long l = (d >= -9223372036854775808.0 && d < 9223372036854775808.0) ? (long)d : 0;
        unsigned long ul = (d > -1.0 && d < 18446744073709551616.0) ? (unsigned long)d : 0;
        int i32 = (d > -2147483649.0 && d < 2147483648.0) ? (int)d : 0;
        unsigned u32 = (d > -1.0 && d < 4294967296.0) ? (unsigned)d : 0;
        short s = (d > -32769.0 && d < 32768.0) ? (short)d : 0;
        unsigned short us = (d > -1.0 && d < 65536.0) ? (unsigned short)d : 0;
        signed char c = (d > -129.0 && d < 128.0) ? (signed char)d : 0;
        unsigned char uc = (d > -1.0 && d < 256.0) ? (unsigned char)d : 0;
        _Bool b = d;
        long lf = (f >= -9223372036854775808.0f && f < 9223372036854775808.0f) ? (long)f : 0;
        unsigned long ulf = (f > -1.0f && f < 18446744073709551616.0f) ? (unsigned long)f : 0;
        int i32f = (f > -2147483904.0f && f < 2147483648.0f) ? (int)f : 0;
        printf("d %2d: %ld %lu %d %u %d %u %d %u %d | %ld %lu %d\n", i, l, ul, i32, u32, s, us, c, uc, b, lf, ulf,
               i32f);
    }
    n = sizeof vbig / sizeof vbig[0];
    for (int i = 0; i < n; i++) {
        double d = vbig[i];
        float f = (float)d;
        double back = f;
        printf("fd %d: %08x %016lx %.9g\n", i, fbits(f), dbits(back), (double)(f * 2.0f) - d);
    }
    volatile double nz = -0.0, nan = 0.0 / 0.0 * 0.0;
    float fz = (float)nz, fn = (float)nan;
    printf("negzero %08x %016lx nan %d %d\n", fbits(fz), dbits((double)fz), fn != fn, (double)fn != (double)fn);
    /* mixed float / double arithmetic: the float operations round to float */
    volatile float a = 16777216.0f, b = 1.0f, c = 0.1f;
    volatile double e = 0.1;
    float s1 = a + b;          /* float add: stays 16777216 */
    double s2 = (double)a + b; /* double add: 16777217 */
    double s3 = c * e + a;     /* c promoted, product in double */
    float s4 = (float)(c * e) + b;
    printf("mix %.9g %.17g %.17g %.9g %d\n", s1, s2, s3, s4, c == e);
    return 0;
}
