/* ACLE (arm_acle.h) on AArch64: barriers and hints, bit operations, CRC32,
 * exclusives, system registers (FPCR, TPIDR_EL0) (compiled with
 * -march=armv8.2-a+crc+aes+sha2+dotprod, see the FLAGS line; the NEON
 * cryptographic and dot product intrinsics are in ../crypto). */
// FLAGS: -march=armv8.2-a+crc+aes+sha2+dotprod
#include <arm_acle.h>
#include <stdint.h>
#include <stdio.h>

static unsigned sum;
static void pu(const char *s, unsigned long long v) {
    printf("%-24s %llx\n", s, v);
    sum = sum * 33 + (unsigned)v + (unsigned)(v >> 32);
}

static volatile uint32_t word = 41;
static volatile uint64_t dword = 0x123456789abcdef0ull;
static volatile uint8_t byte = 200;
static __thread int tls_var = 5;

__attribute__((noinline)) static void bits(uint32_t x, uint64_t y) {
    pu("__rbit", __rbit(x));
    pu("__rbitll", __rbitll(y));
    pu("__clz", __clz(x));
    pu("__clzll", __clzll(y));
    pu("__cls", __cls(x));
    pu("__clsll", __clsll(y));
    pu("__rev", __rev(x));
    pu("__revll", __revll(y));
    pu("__rev16", __rev16(x));
    pu("__rev16ll", __rev16ll(y));
    pu("__revsh", (uint16_t)__revsh((int16_t)x));
    pu("__ror", __ror(x, 13));
    pu("__rorll", __rorll(y, 37));
}

__attribute__((noinline)) static void crc(const uint8_t *p, int n) {
    uint32_t c = 0xffffffff, cc = 0xffffffff;
    for (int i = 0; i < n; i++) {
        c = __crc32b(c, p[i]);
        cc = __crc32cb(cc, p[i]);
    }
    pu("__crc32b", ~c);
    pu("__crc32cb", ~cc);
    pu("__crc32h", __crc32h(0x1234, 0xbeef));
    pu("__crc32w", __crc32w(0x1234, 0xdeadbeef));
    pu("__crc32d", __crc32d(0x1234, 0x0123456789abcdefull));
    pu("__crc32ch", __crc32ch(7, 0xbeef));
    pu("__crc32cw", __crc32cw(7, 0xdeadbeef));
    pu("__crc32cd", __crc32cd(7, 0x0123456789abcdefull));
}

__attribute__((noinline)) static void excl(void) {
    uint32_t v;
    do {
        v = __builtin_arm_ldrex(&word);
    } while (__builtin_arm_strex(v + 1, &word));
    pu("ldrex/strex w", word);
    uint64_t d;
    do {
        d = __builtin_arm_ldaex(&dword);
    } while (__builtin_arm_stlex(d ^ 0xff00ff00ull, &dword));
    pu("ldaex/stlex d", dword);
    uint8_t b;
    do {
        b = __builtin_arm_ldrex(&byte);
    } while (__builtin_arm_strex((uint8_t)(b + 100), &byte));
    pu("ldrex/strex b", byte);
    (void)__builtin_arm_ldrex(&word);
    __builtin_arm_clrex();
    pu("clrex", word);
}

__attribute__((noinline)) static void sys(void) {
    __dmb(11);
    __dsb(15);
    __isb(15);
    __dmb(9);
    __yield();
    __nop();
    uint64_t fpcr = __arm_rsr64("fpcr");
    __arm_wsr64("fpcr", fpcr | (1u << 24));   /* flush to zero */
    volatile float tiny = 1e-40f;
    float t2 = tiny * 1.0f;
    pu("ftz", t2 == 0.0f);
    __arm_wsr64("fpcr", fpcr);
    float t3 = tiny * 1.0f;
    pu("no ftz", t3 == 0.0f);
    pu("fpcr restored", __arm_rsr64("fpcr") == fpcr);
    uint64_t tp = __arm_rsr64("tpidr_el0");
    pu("tpidr_el0", tp == (uint64_t)__builtin_thread_pointer());
    pu("tls via tp", tls_var + (tp != 0));
    pu("rsr S3_3_C13_C0_2", __arm_rsr64("S3_3_C13_C0_2") == tp);
    pu("rsr32 fpsr", __arm_rsr("fpsr") & 0);
    pu("cntvct", __arm_rsr64("cntvct_el0") != 1);
}


int main(void) {
    bits(0x00f0e1d3u, 0x8000123456789abcull);
    bits(1, ~0ull);
    crc((const uint8_t *)"The quick brown fox jumps over the lazy dog", 43);
    excl();
    sys();
    printf("sum %08x\n", sum);
    return 0;
}
