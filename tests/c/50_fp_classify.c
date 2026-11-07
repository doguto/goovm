/* FP classification (llvm.is.fpclass for isnan, isfinite, isnormal; fabs
   compares for isinf; fpclassify; signbit) of special values, as values and
   as branch conditions, for float and double; NaN compares with every
   predicate; -0.0. */
#include <math.h>
#include <stdio.h>
#include <string.h>

static double dvals[16];
static float fvals[16];
static int nvals;

static double dbits(unsigned long b) { double d; memcpy(&d, &b, 8); return d; }
static float fbits(unsigned b) { float f; memcpy(&f, &b, 4); return f; }

static void init(void) {
    unsigned long db[] = {0x0000000000000000UL, 0x8000000000000000UL, 0x0000000000000001UL, 0x800FFFFFFFFFFFFFUL,
                          0x0010000000000000UL, 0x7FEFFFFFFFFFFFFFUL, 0x7FF0000000000000UL, 0xFFF0000000000000UL,
                          0x7FF8000000000000UL, 0xFFF8000000000001UL, 0x7FF0000000000001UL, 0x3FF0000000000000UL,
                          0xC00921FB54442D18UL, 0x000FFFFFFFFFFFFFUL, 0x8010000000000000UL, 0x4340000000000000UL};
    unsigned fb[] = {0x00000000u, 0x80000000u, 0x00000001u, 0x807FFFFFu, 0x00800000u, 0x7F7FFFFFu, 0x7F800000u,
                     0xFF800000u, 0x7FC00000u, 0xFFC00001u, 0x7F800001u, 0x3F800000u, 0xC0490FDBu, 0x007FFFFFu,
                     0x80800000u, 0x4B000000u};
    nvals = 16;
    for (int i = 0; i < nvals; i++) {
        dvals[i] = dbits(db[i]);
        fvals[i] = fbits(fb[i]);
    }
}

static int dclass(double x) {
    int c = 0;
    if (isnan(x)) c |= 1;
    if (isinf(x)) c |= 2;
    if (isfinite(x)) c |= 4;
    if (isnormal(x)) c |= 8;
    if (signbit(x)) c |= 16;
    if (!isnan(x)) c |= 32;
    return c;
}
static int fclass(float x) {
    int c = 0;
    if (isnan(x)) c |= 1;
    if (isinf(x)) c |= 2;
    if (isfinite(x)) c |= 4;
    if (isnormal(x)) c |= 8;
    if (signbit(x)) c |= 16;
    if (!isnan(x)) c |= 32;
    return c;
}
static const char *kind(int k) {
    switch (k) {
    case FP_NAN: return "nan";
    case FP_INFINITE: return "inf";
    case FP_ZERO: return "zero";
    case FP_SUBNORMAL: return "sub";
    case FP_NORMAL: return "norm";
    }
    return "?";
}
/* the builtins straight as values (no branch to fuse with) */
static int dvalue(double x) {
    return isnan(x) + 2 * isinf(x) + 4 * isfinite(x) + 8 * isnormal(x) + 16 * !!signbit(x)
           + 32 * __builtin_isnan(x) + 64 * __builtin_isfinite(x);
}
static int fvalue(float x) {
    return isnan(x) + 2 * isinf(x) + 4 * isfinite(x) + 8 * isnormal(x) + 16 * !!signbit(x)
           + 32 * __builtin_isnan(x) + 64 * __builtin_isfinite(x);
}
/* zero and subnormal tests the way libstdc++ and some C code spell them */
static int dsub(double x) { return __builtin_fpclassify(0, 1, 2, 3, 4, x) == 3 ? 1 : 0; }
static int dzero(double x) { return __builtin_iszero(x); }
static int fsub(float x) { return __builtin_issubnormal(x); }

/* every predicate on (a, b), as a value and as a branch */
static unsigned dcmp(double a, double b) {
    unsigned v = (a == b) | (a != b) << 1 | (a < b) << 2 | (a <= b) << 3 | (a > b) << 4 | (a >= b) << 5
                 | !(a < b) << 6 | !(a >= b) << 7 | __builtin_isunordered(a, b) << 8
                 | __builtin_islessgreater(a, b) << 9;
    unsigned br = 0;
    if (a == b) br |= 1;
    if (a != b) br |= 2;
    if (a < b) br |= 4;
    if (a <= b) br |= 8;
    if (a > b) br |= 16;
    if (a >= b) br |= 32;
    if (!(a < b)) br |= 64;
    if (!(a >= b)) br |= 128;
    if (__builtin_isunordered(a, b)) br |= 256;
    if (__builtin_islessgreater(a, b)) br |= 512;
    return v | br << 16;
}
static unsigned fcmp(float a, float b) {
    unsigned v = (a == b) | (a != b) << 1 | (a < b) << 2 | (a <= b) << 3 | (a > b) << 4 | (a >= b) << 5;
    unsigned br = 0;
    if (a == b) br |= 1;
    if (a != b) br |= 2;
    if (a < b) br |= 4;
    if (a <= b) br |= 8;
    if (a > b) br |= 16;
    if (a >= b) br |= 32;
    return v | br << 8;
}
/* selects on FP compares */
static double dsel(double a, double b) { return (a < b ? a : b) + (a == b ? 100.0 : 0.0) + (a != b ? 1000.0 : 0.0); }

int main(void) {
    init();
    for (int i = 0; i < nvals; i++) {
        double d = dvals[i];
        float f = fvals[i];
        printf("%2d d: %08x %s v=%d sub=%d zero=%d | f: %08x %s v=%d sub=%d\n", i, dclass(d), kind(fpclassify(d)),
               dvalue(d), dsub(d), dzero(d), fclass(f), kind(fpclassify(f)), fvalue(f), fsub(f));
    }
    for (int i = 0; i < nvals; i += 3)
        for (int k = 0; k < nvals; k += 2) {
            double s = dsel(dvals[i], dvals[k]);
            printf("cmp %2d %2d: %08x %04x %s\n", i, k, dcmp(dvals[i], dvals[k]), fcmp(fvals[i], fvals[k]),
                   s != s ? "nan" : s == 1.0 / 0.0 ? "inf" : s == -1.0 / 0.0 ? "-inf" : "num");
        }
    /* -0.0 */
    volatile double nz = -0.0, pz = 0.0;
    printf("negzero %d %d %g %g %d %g\n", nz == pz, signbit(nz) != 0, 1.0 / nz, copysign(3.0, nz), signbit(-pz) != 0,
           fabs(nz) + 0.0);
    return 0;
}
