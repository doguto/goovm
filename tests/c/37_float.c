// float, double and long double: arithmetic, all compare predicates with
// NaN, conversions (signed/unsigned, 32/64-bit), libm calls, FP arguments
// beyond the eight xmm registers.
#include <math.h>
#include <stdio.h>

static volatile double vnan, vone = 1.0, vtwo = 2.0;

static double many(double a, double b, double c, double d, double e, double f, double g, double h, double i,
                   double j, float k, long double l) {
    return a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f + 7 * g + 8 * h + 9 * i + 10 * j + 11 * k + (double)(12 * l);
}
static int cmps(double a, double b) {
    return (a == b) | (a != b) << 1 | (a < b) << 2 | (a <= b) << 3 | (a > b) << 4 | (a >= b) << 5 |
           (__builtin_isunordered(a, b)) << 6 | (__builtin_islessgreater(a, b)) << 7;
}
static int cmpl(long double a, long double b) {
    return (a == b) | (a != b) << 1 | (a < b) << 2 | (a <= b) << 3 | (a > b) << 4 | (a >= b) << 5 |
           (__builtin_isunordered(a, b)) << 6;
}

int main(void) {
    vnan = vone / 0.0 - vone / 0.0;
    double x = vone / 3, y = vtwo * 1e10;
    float f = (float)x, g = 1.5f;
    long double l = (long double)x * 3, m = 1.0L / 7;
    printf("%.17g %.17g %.9g %.9g\n", x + y, x * y - y, f * g, f / g - g);
    printf("%.17Lg %.17Lg %.17Lg\n", l, m * 49, -m + l);
    printf("%d %d %d %d\n", cmps(1, 2), cmps(2, 2), cmps(vnan, 1), cmps(3, vnan));
    printf("%d %d %d\n", cmpl(1, 2), cmpl(2, 2), cmpl(vnan, 1));
    unsigned long long big = 18446744073709551000ull;
    long long neg = -1234567890123ll;
    unsigned u = 4000000000u;
    printf("%.17g %.17g %.9g %.17g\n", (double)big, (double)neg, (float)big, (double)u);
    printf("%llu %lld %u %d\n", (unsigned long long)1.8e19, (long long)-9.2e18, (unsigned)4.1e9, (int)-2.7);
    printf("%llu %lld %.17Lg %.17Lg\n", (unsigned long long)(long double)1.8e19, (long long)(-3.9L),
           (long double)big, (long double)neg);
    printf("%.6f %.6f %.6f %.6f %.6f\n", sqrt(2.0), floor(-2.5), ceil(2.1), fmod(7.5, 2), pow(2, 0.5));
    printf("%.6f %.6f %.6Lf\n", fabs(-3.0), copysign(2.0, -0.0), fabsl(-l));
    printf("%.6f\n", many(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11.5f, 12.25L));
    printf("%d %d %d %d\n", __builtin_isnan(vnan), __builtin_isinf(vone / 0.0), __builtin_isnormal(x),
           __builtin_fpclassify(0, 1, 2, 3, 4, 1e-310));
    return 0;
}
