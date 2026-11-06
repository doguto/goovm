// Atomics of every width: load/store orderings, exchange, compare-exchange,
// fetch-op (add/sub/and/or/xor/nand/min/max), C11 _Atomic floats, fences.
#include <stdatomic.h>
#include <stdio.h>

static signed char c8 = -5;
static unsigned short u16 = 60000;
static int i32 = -100;
static long long i64 = 1LL << 40;
static int *ptr;
static _Atomic float af = 1.5f;
static _Atomic double ad = 2.25;

int main(void) {
    int dummy = 0;
    printf("%d %d %d %lld\n", __atomic_fetch_add(&c8, 3, __ATOMIC_SEQ_CST), __atomic_fetch_sub(&u16, 7, __ATOMIC_RELAXED),
           __atomic_exchange_n(&i32, 77, __ATOMIC_ACQ_REL), __atomic_fetch_xor(&i64, 0xff, __ATOMIC_SEQ_CST));
    printf("%d %d %d %lld\n", __atomic_fetch_nand(&c8, 0x0f, __ATOMIC_SEQ_CST), __atomic_fetch_and(&u16, 0xff0f, __ATOMIC_SEQ_CST),
           __atomic_fetch_or(&i32, 0x100, __ATOMIC_SEQ_CST), __atomic_add_fetch(&i64, -1, __ATOMIC_SEQ_CST));
    printf("%d %d %d %lld\n", c8, u16, i32, i64);
    printf("%d %d %d\n", __atomic_fetch_max(&i32, 1000, __ATOMIC_SEQ_CST), __atomic_fetch_min(&c8, -100, __ATOMIC_SEQ_CST),
           __atomic_fetch_max(&u16, 65000, __ATOMIC_SEQ_CST));
    printf("%d %d %d\n", i32, c8, u16);
    unsigned short e16 = 65000;
    long long e64 = 5;
    int *pn = &dummy, *pe = 0;
    printf("%d %d %d %d\n", __atomic_compare_exchange_n(&u16, &e16, 12, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST),
           __atomic_compare_exchange_n(&i64, &e64, 6, 1, __ATOMIC_SEQ_CST, __ATOMIC_RELAXED),
           __atomic_compare_exchange_n(&ptr, &pe, pn, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST), (int)(e64 == i64));
    __atomic_store_n(&i32, 5, __ATOMIC_SEQ_CST);
    __atomic_store_n(&c8, 6, __ATOMIC_RELEASE);
    atomic_thread_fence(memory_order_seq_cst);
    atomic_signal_fence(memory_order_seq_cst);
    af += 2.0f;
    ad *= 2.0;
    printf("%d %d %d %g %g %d\n", __atomic_load_n(&i32, __ATOMIC_ACQUIRE), __atomic_load_n(&c8, __ATOMIC_RELAXED), u16,
           (double)af, ad, ptr == &dummy);
    return 0;
}
