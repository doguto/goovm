// Variadic functions with FP, long double, struct and many arguments;
// va_copy; vprintf forwarding.
#include <stdarg.h>
#include <stdio.h>

typedef struct { double x, y; } P;
typedef struct { long a, b, c; } T3;

static double sum(int n, ...) {
    va_list ap, aq;
    va_start(ap, n);
    va_copy(aq, ap);
    double s = 0;
    for (int i = 0; i < n; i++) {
        int kind = va_arg(ap, int);
        if (kind == 0) s += va_arg(ap, double);
        else if (kind == 1) s += va_arg(ap, long);
        else if (kind == 2) s += (double)va_arg(ap, long double);
        else if (kind == 3) {
            P p = va_arg(ap, P);
            s += p.x * p.y;
        } else {
            T3 t = va_arg(ap, T3);
            s += t.a + t.b + t.c;
        }
    }
    va_end(ap);
    int first = va_arg(aq, int);
    va_end(aq);
    return s + first * 1000;
}
static void say(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vprintf(fmt, ap);
    va_end(ap);
}

int main(void) {
    P p = {1.5, 4};
    T3 t = {1, 2, 3};
    printf("%.4f\n", sum(9, 0, 1.25, 1, 7L, 2, 2.5L, 3, p, 4, t, 0, 0.5, 0, 0.25, 0, 0.125, 0, 0.0625, 0, 8.0));
    say("%d %s %.3f %Lg %c %ld %.1f %.1f %.1f %.1f %.1f %.1f %.1f %.1f %.1f\n", 1, "two", 3.0, 4.0L, '5', 6L, 7.0,
        8.0, 9.0, 10.0, 11.0, 12.0, 13.0, 14.0, 15.0);
    return 0;
}
