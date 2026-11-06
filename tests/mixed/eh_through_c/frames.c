/* C frames that C++ exceptions unwind through (compiled by goovm or clang):
 * callbacks under qsort, frames that keep values in callee-saved registers,
 * pass arguments on the stack, use dynamic allocas, va_lists and the red
 * zone. Nothing here catches; main.cpp throws from the callbacks. */
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

typedef void (*cb_t)(int);

long chain_calls;

/* many values live across the calls: callee-saved registers */
long through_regs(cb_t f, int n, long a, long b, long c, long d, long e, long g) {
    long s = a + b, t = c * d, u = e - g, v = a ^ g;
    for (int i = 0; i < n; i++) {
        f(i);
        s += i * t + u;
        v = v * 31 + s;
    }
    return s + t + u + v;
}

/* a dynamic alloca between the thrower and the catcher */
int through_vla(cb_t f, int n) {
    int buf[n + 1];
    for (int i = 0; i <= n; i++) buf[i] = i * i;
    f(buf[n]);
    return buf[0];
}

/* a register save area (va_start) */
int through_va(cb_t f, int n, ...) {
    va_list ap;
    va_start(ap, n);
    int s = 0;
    for (int i = 0; i < n; i++) {
        int x = va_arg(ap, int);
        s += x;
        f(x);
    }
    va_end(ap);
    return s;
}

/* recursion: many C frames */
int through_deep(cb_t f, int depth) {
    char pad[24];
    memset(pad, depth, sizeof pad);
    chain_calls++;
    if (depth == 0) {
        f(pad[3]);
        return 0;
    }
    return through_deep(f, depth - 1) + pad[depth % 24];
}

/* stack arguments to the callback's caller */
static long many(cb_t f, long a1, long a2, long a3, long a4, long a5, long a6, long a7, long a8, long a9) {
    f((int)(a7 + a8 + a9));
    return a1 + a2 + a3 + a4 + a5 + a6;
}
long through_stack_args(cb_t f, long x) { return many(f, x, x, x, x, x, x, x + 1, x + 2, x + 3) + 1; }

/* qsort with a C comparator that calls back into C++ */
static cb_t qcb;
static int cmp_ints(const void *a, const void *b) {
    int x = *(const int *)a, y = *(const int *)b;
    qcb(x);
    return (x > y) - (x < y);
}
void sort_with(cb_t f, int *v, int n) {
    qcb = f;
    qsort(v, n, sizeof(int), cmp_ints);
}

/* a leaf in the red zone, called on the way */
static int leaf(int x) {
    int t[4] = {x, x + 1, x + 2, x + 3};
    return t[x & 3];
}
int through_leaf(cb_t f, int x) {
    int r = leaf(x);
    f(r);
    return r;
}
