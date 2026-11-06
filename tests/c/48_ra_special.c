// Register allocation and the special cases: setjmp/longjmp (values in
// registers across a returns_twice call), varargs with FP arguments,
// long double (x87) next to register values, inline assembly that clobbers
// callee-saved registers or writes rbx, i128 values (register pairs), and
// vectors in xmm registers.
#include <setjmp.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdint.h>

static jmp_buf jb;

__attribute__((noinline)) static void jump(int v) { longjmp(jb, v); }

__attribute__((noinline)) static long sj(long x) {
    long a = x * 3, b = x + 11;          // live across setjmp
    volatile long n = 0;
    if (setjmp(jb) == 0) {
        long c = a * b;                   // computed between setjmp and longjmp
        n = c;
        jump(5);
    }
    return a + b + n;
}

__attribute__((noinline)) static double vsum(int n, ...) {
    va_list ap;
    va_start(ap, n);
    double s = 0;
    for (int i = 0; i < n; i++) {
        if (i % 2) s += va_arg(ap, double);
        else s += va_arg(ap, int);
    }
    va_end(ap);
    return s;
}

__attribute__((noinline)) static long double ld(long double a, long b, long double c) {
    long x = b * 7;
    long double r = a * c + x;
    return r / 3 + (long double)(x - 1);
}

__attribute__((noinline)) static long asm_clobber(long x) {
    long a = x + 1, b = x * 5;            // in registers around the asm
    __asm__ volatile("xor %%ebx, %%ebx\n\tmov $7, %%r12d\n\tmov $9, %%r15d" ::: "rbx", "r12", "r15");
    return a * 3 + b;
}

// t lives across the calls in a callee-saved register (mem2reg variant): the
// clobbering functions must save and restore rbx, r12, r15.
__attribute__((noinline)) static long cs_user(long x) {
    long t = x * 3 + 1;
    long u = asm_clobber(x);
    long w = asm_clobber(t);
    return t * 7 + u + w;
}

__attribute__((noinline)) static unsigned asm_out_rbx(unsigned x) {
    unsigned r, keep = x * 9 + 1;
    __asm__("mov %1, %%ebx\n\tadd $3, %%ebx\n\tmov %%ebx, %0" : "=b"(r) : "r"(x));
    return r + keep;
}

__attribute__((noinline)) static __int128 wide(__int128 a, __int128 b, long c) {
    __int128 x = a * b + c;
    __int128 y = (x >> 17) ^ (a << 3);
    return x / 7 + y % 1000003 - (__int128)c * c;
}

typedef float v4f __attribute__((vector_size(16)));
typedef int v4i __attribute__((vector_size(16)));
__attribute__((noinline)) static v4f vec(v4f a, v4f b, float s) {
    v4f c = a * b + (v4f){s, s, s, s};
    c[2] = s * 10;
    return c - a;
}
__attribute__((noinline)) static v4i veci(v4i a, int s) {
    v4i c = a + (v4i){1, 2, 3, 4};
    c[1] = s;
    return (c ^ a) & (v4i){0xFF, 0xFF0, 0xFF00, -1};
}

int main(void) {
    printf("%ld %ld\n", sj(4), sj(-10));
    printf("%.3f\n", vsum(6, 1, 2.5, 3, 4.25, 5, 6.125));
    printf("%.6Lf\n", ld(1.5L, 3, 2.25L));
    printf("%ld %u %ld\n", asm_clobber(10), asm_out_rbx(5), cs_user(6));
    __int128 w = wide(((__int128)0x123456789ABCDEFLL << 40) + 12345, 987654321, -77);
    printf("%llx %llx\n", (unsigned long long)(w >> 64), (unsigned long long)w);
    v4f f = vec((v4f){1, 2, 3, 4}, (v4f){0.5f, 1.5f, 2.5f, 3.5f}, 2);
    printf("%g %g %g %g\n", f[0], f[1], f[2], f[3]);
    v4i v = veci((v4i){10, 20, 30, 40}, 99);
    printf("%d %d %d %d\n", v[0], v[1], v[2], v[3]);
    return 0;
}
