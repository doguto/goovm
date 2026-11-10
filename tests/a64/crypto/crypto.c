/* AArch64 cryptographic extension (AES, SHA-1, SHA-256) and dot product
 * intrinsics of arm_neon.h. */
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
    crypto();
    printf("sum %08x\n", sum);
    return 0;
}
