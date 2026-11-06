// Inline assembly: register, memory, immediate and fixed-register operands,
// x87 operands, and empty templates (optimization barriers).
#include <stdio.h>

static int add(int a, int b) {
    int r;
    __asm__("addl %2, %0" : "=r"(r) : "0"(a), "r"(b));
    return r;
}
static unsigned long long fixed_regs(void) {
    unsigned lo, hi;
    __asm__ volatile("movl $7, %%eax\n\tmovl $5, %%edx" : "=a"(lo), "=d"(hi));
    return ((unsigned long long)hi << 32) | lo;
}
static void store(int *p, int v) { __asm__("movl %1, %0" : "=m"(*p) : "r"(v)); }
static int bsr(int x) {
    int r;
    __asm__("bsrl %1, %0" : "=r"(r) : "rm"(x));
    return r;
}
static long imm(long x) {
    long r;
    __asm__("leaq %c2(%1), %0" : "=r"(r) : "r"(x), "i"(10));
    return r;
}
static short narrow(short a) {
    short r;
    __asm__("movw %1, %0\n\tincw %0" : "=r"(r) : "r"(a));
    return r;
}
static long double x87_sqrt(long double x) {
    long double r;
    __asm__("fsqrt" : "=t"(r) : "0"(x));
    return r;
}
static long double x87_atan2(long double y, long double x) {
    long double r;
    __asm__("fpatan" : "=t"(r) : "0"(x), "u"(y) : "st(1)");
    return r;
}
static double sse_add(double a, double b) {
    __asm__("addsd %1, %0" : "+x"(a) : "x"(b));
    return a;
}

int main(void) {
    int m = 0, barrier = 3;
    store(&m, 42);
    __asm__ volatile("" : "+r"(barrier) : : "memory");
    printf("%d %llx %d %d %ld %d\n", add(40, 2), fixed_regs(), m, bsr(1000), imm(5), narrow(9));
    printf("%.6Lf %.6Lf %.3f %d\n", x87_sqrt(2.0L), x87_atan2(1.0L, 1.0L), sse_add(1.25, 2.5), barrier);
    return 0;
}
