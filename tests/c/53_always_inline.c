/* G1: calls of always_inline nodebug functions are expanded in place, as
   clang's AlwaysInliner does at -O0 (the x86 intrinsics are such). */
#include <stdio.h>
#include <string.h>
#include <xmmintrin.h>
#include <emmintrin.h>

#define AI static inline __attribute__((always_inline, nodebug))

struct pair { long a, b; };
struct big { long v[5]; };
struct empty { };

AI int add(int a, int b) { return a + b; }

/* several returns, a loop, a local */
AI int clamp_sum(int n, int lo, int hi) {
    int s = 0;
    for (int i = 0; i < n; i++) {
        s += i;
        if (s > hi) return hi;
    }
    if (s < lo) return lo;
    return s;
}

/* aggregates returned in registers, in memory, and not at all */
AI struct pair mkpair(long a, long b) { struct pair p; p.a = a; p.b = b; return p; }
AI struct big mkbig(long x) {
    struct big r;
    for (int i = 0; i < 5; i++) r.v[i] = x * i;
    return r;
}
AI struct empty mkempty(int *count) { struct empty e; ++*count; return e; }

AI void bump(int *p, int by) { *p += by; }

/* calls one another */
AI int twice(int x) { return add(x, x); }

/* taken by address: still emitted out of line */
AI int neg(int x) { return -x; }

static int counter;
static int side(int x) { counter++; return x; }

int main(void) {
    /* an argument that expands the same function */
    int r1 = add(add(1, 2), add(side(3), 4));
    int r2 = twice(add(5, twice(6)));
    printf("%d %d %d\n", r1, r2, counter);

    printf("%d %d %d\n", clamp_sum(3, 10, 100), clamp_sum(100, 0, 50), clamp_sum(5, 0, 100));

    struct pair p = mkpair(7, 8);
    struct big b = mkbig(3);
    int n = 0;
    struct empty e = mkempty(&n);
    (void)e;
    printf("%ld %ld %ld %ld %d\n", p.a, p.b, b.v[4], mkbig(2).v[3], n);

    int v = 1;
    bump(&v, 41);
    int (*f)(int) = neg;
    printf("%d %d %d\n", v, f(9), neg(10));

    /* the intrinsics, nested */
    __m128 a = _mm_set_ps(4.0f, 3.0f, 2.0f, 1.0f);
    __m128 c = _mm_add_ps(a, _mm_mul_ps(_mm_add_ps(a, a), _mm_set1_ps(0.5f)));
    float out[4];
    _mm_storeu_ps(out, c);
    __m128i i4 = _mm_add_epi32(_mm_set_epi32(1, 2, 3, 4), _mm_slli_epi32(_mm_set1_epi32(3), 2));
    int oi[4];
    _mm_storeu_si128((__m128i *)oi, i4);
    printf("%g %g %g %g | %d %d %d %d\n", out[0], out[1], out[2], out[3], oi[0], oi[1], oi[2], oi[3]);
    return 0;
}
