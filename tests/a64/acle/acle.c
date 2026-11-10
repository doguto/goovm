/* ACLE (arm_acle.h) on AArch64: barriers and hints, bit operations, CRC32,
 * exclusives, system registers (FPCR, TPIDR_EL0), the AES / SHA cryptographic
 * instructions and dot products (compiled with
 * -march=armv8.2-a+crc+aes+sha2+dotprod, see the FLAGS line). */
// FLAGS: -march=armv8.2-a+crc+aes+sha2+dotprod
#include <arm_acle.h>
#include <arm_neon.h>
#include <stdint.h>
#include <stdio.h>

static unsigned sum;
static void pu(const char *s, unsigned long long v) {
    printf("%-24s %llx\n", s, v);
    sum = sum * 33 + (unsigned)v + (unsigned)(v >> 32);
}
static void pq(const char *s, uint8x16_t v) {
    uint64x2_t w = vreinterpretq_u64_u8(v);
    printf("%-24s %016llx %016llx\n", s, (unsigned long long)vgetq_lane_u64(w, 1),
           (unsigned long long)vgetq_lane_u64(w, 0));
    sum = sum * 33 + (unsigned)vgetq_lane_u64(w, 0) + (unsigned)vgetq_lane_u64(w, 1);
}
#define PQ(s, v) pq(s, vreinterpretq_u8_u32(v))

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

__attribute__((noinline)) static void crypto(void) {
    uint8_t kb[16], db[16];
    for (int i = 0; i < 16; i++) {
        kb[i] = (uint8_t)(i * 17 + 3);
        db[i] = (uint8_t)(i * 29 + 101);
    }
    uint8x16_t key = vld1q_u8(kb), data = vld1q_u8(db);
    uint8x16_t s = data;
    for (int r = 0; r < 9; r++) s = vaesmcq_u8(vaeseq_u8(s, key));
    s = veorq_u8(vaeseq_u8(s, key), key);
    pq("aes encrypt", s);
    uint8x16_t t = s;
    for (int r = 0; r < 9; r++) t = vaesimcq_u8(vaesdq_u8(t, key));
    pq("aes decrypt", t);
    uint32x4_t abcd = vreinterpretq_u32_u8(data), wk = vreinterpretq_u32_u8(key);
    uint32_t e = 0xc3d2e1f0;
    PQ("sha1c", vsha1cq_u32(abcd, e, wk));
    PQ("sha1p", vsha1pq_u32(abcd, e, wk));
    PQ("sha1m", vsha1mq_u32(abcd, e, wk));
    pu("sha1h", vsha1h_u32(e));
    PQ("sha1su0", vsha1su0q_u32(abcd, wk, abcd));
    PQ("sha1su1", vsha1su1q_u32(abcd, wk));
    PQ("sha256h", vsha256hq_u32(abcd, wk, abcd));
    PQ("sha256h2", vsha256h2q_u32(abcd, wk, abcd));
    PQ("sha256su0", vsha256su0q_u32(abcd, wk));
    PQ("sha256su1", vsha256su1q_u32(abcd, wk, abcd));
    PQ("sdot", vreinterpretq_u32_s32(vdotq_s32(vreinterpretq_s32_u8(key), vreinterpretq_s8_u8(data),
                                                vreinterpretq_s8_u8(key))));
    PQ("udot", vdotq_u32(wk, data, key));
    PQ("udot_laneq", vdotq_laneq_u32(wk, data, key, 3));
    uint32x2_t d2 = vdot_u32(vget_low_u32(wk), vget_low_u8(data), vget_high_u8(key));
    PQ("udot d", vcombine_u32(d2, d2));
}

int main(void) {
    bits(0x00f0e1d3u, 0x8000123456789abcull);
    bits(1, ~0ull);
    crc((const uint8_t *)"The quick brown fox jumps over the lazy dog", 43);
    excl();
    sys();
    crypto();
    printf("sum %08x\n", sum);
    return 0;
}
