// VLAs, computed goto, TLS, atomics, aliases, constructors, weak and
// common symbols, sections, bit builtins, overflow builtins, setjmp.
#include <setjmp.h>
#include <stdio.h>
#include <string.h>

static __thread int tls_counter = 5;
__thread long tls_zero;
int common_var;
int defined_var = 7;
extern int alias_var __attribute__((alias("defined_var")));
__attribute__((weak)) int weak_fn(void) { return 11; }
__attribute__((section(".data.goovm_test"))) int in_section = 99;
static int ctor_ran;
__attribute__((constructor)) static void ctor(void) { ctor_ran = 1; }
__attribute__((constructor(200))) static void ctor_early(void) { ctor_ran = ctor_ran * 10 + 2; }

static int vla(int n) {
    int a[n], s = 0;
    for (int i = 0; i < n; i++) a[i] = i * i;
    for (int i = 0; i < n; i++) s += a[i];
    char *p = __builtin_alloca(n * 3);
    memset(p, 1, n * 3);
    return s + p[n * 3 - 1];
}
static int gotos(int k) {
    static void *tab[] = {&&l0, &&l1, &&l2};
    static const int off[] = {&&l1 - &&l0, &&l2 - &&l0};
    int r = off[0] > 0 && off[1] > off[0];
    goto *tab[k];
l0: return r + 100;
l1: return r + 200;
l2: return r + 300;
}
static jmp_buf jb;
static void thrower(int v) { longjmp(jb, v); }

int main(void) {
    tls_counter += 2;
    tls_zero = 3;
    int x = 5;
    int old = __atomic_fetch_add(&x, 3, __ATOMIC_SEQ_CST);
    int expected = 8;
    _Bool ok = __atomic_compare_exchange_n(&x, &expected, 20, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
    long l = 10;
    __atomic_fetch_or(&l, 5, __ATOMIC_RELAXED);
    __sync_synchronize();
    printf("%d %d %d %d %ld %ld\n", vla(10), tls_counter, old, x + ok, l, tls_zero);
    printf("%d %d %d %d\n", gotos(0), gotos(1), gotos(2), alias_var + common_var + weak_fn() + in_section);
    unsigned u = 0x00f00010u;
    unsigned long long v = 0x8000000000000001ull;
    printf("%d %d %d %d %d %x %llx\n", __builtin_clz(u), __builtin_ctz(u), __builtin_popcount(u),
           __builtin_clzll(v), __builtin_popcountll(v), __builtin_bswap32(u), __builtin_bswap64(v));
    int ov;
    int o1 = __builtin_add_overflow(2147483600, 100, &ov);
    long ol;
    int o2 = __builtin_mul_overflow(1L << 40, 1L << 30, &ol);
    unsigned ou;
    int o3 = __builtin_sub_overflow(1u, 2u, &ou);
    printf("%d %d %d %d %u %d\n", o1, ov, o2, o3, ou, ctor_ran);
    int r = setjmp(jb);
    if (r == 0) thrower(42);
    printf("%d\n", r);
    return 0;
}
