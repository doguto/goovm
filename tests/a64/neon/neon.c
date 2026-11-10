/* AArch64 NEON intrinsics (arm_neon.h): arithmetic, saturation, shifts,
 * widening/narrowing, conversions, structure loads/stores, permutes, table
 * lookups, reductions and lane operations. Every result is printed as hex. */
#include <arm_neon.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static unsigned sum;
#define P8(v) p64x2(#v, vreinterpretq_u64_u8(v))
static void p64x2(const char *s, uint64x2_t v) {
    printf("%-28s %016llx %016llx\n", s, (unsigned long long)vgetq_lane_u64(v, 1),
           (unsigned long long)vgetq_lane_u64(v, 0));
    sum = sum * 31 + (unsigned)vgetq_lane_u64(v, 0) + (unsigned)(vgetq_lane_u64(v, 1) >> 7);
}
static void p64(const char *s, uint64x1_t v) {
    printf("%-28s %016llx\n", s, (unsigned long long)vget_lane_u64(v, 0));
    sum = sum * 31 + (unsigned)vget_lane_u64(v, 0);
}
static void pu(const char *s, unsigned long long v) {
    printf("%-28s %llx\n", s, v);
    sum = sum * 31 + (unsigned)v;
}
static void pf(const char *s, double v) {
    printf("%-28s %a\n", s, v);
    sum = sum * 31 + (unsigned)(long long)(v * 1000);
}
#define Q(name, expr) p64x2(name, vreinterpretq_u64_##expr)
#define D(name, expr) p64(name, vreinterpret_u64_##expr)

static uint8_t b8[64];
static int16_t h16[32];
static int32_t s32[16];
static float f32[16];
static double f64[8];

static void init(void) {
    for (int i = 0; i < 64; i++) b8[i] = (uint8_t)(i * 37 + 11);
    for (int i = 0; i < 32; i++) h16[i] = (int16_t)(i * 3001 - 40000);
    for (int i = 0; i < 16; i++) s32[i] = (int32_t)(i * 0x12345677u + 0x80000001u);
    for (int i = 0; i < 16; i++) f32[i] = (float)(i - 7) * 1.375f + 0.25f;
    for (int i = 0; i < 8; i++) f64[i] = (double)(i - 3) * -2.625 + 0.5;
}

__attribute__((noinline)) static void arith(void) {
    uint8x16_t a = vld1q_u8(b8), b = vld1q_u8(b8 + 16);
    int16x8_t ha = vld1q_s16(h16), hb = vld1q_s16(h16 + 8);
    int32x4_t sa = vld1q_s32(s32), sb = vld1q_s32(s32 + 4);
    Q("vaddq_u8", u8(vaddq_u8(a, b)));
    Q("vsubq_s16", s16(vsubq_s16(ha, hb)));
    Q("vmulq_s32", s32(vmulq_s32(sa, sb)));
    Q("vmlaq_s16", s16(vmlaq_s16(ha, hb, ha)));
    Q("vqaddq_u8", u8(vqaddq_u8(a, b)));
    Q("vqaddq_s16", s16(vqaddq_s16(ha, hb)));
    Q("vqsubq_u8", u8(vqsubq_u8(a, b)));
    Q("vqsubq_s32", s32(vqsubq_s32(sa, sb)));
    Q("vhaddq_u8", u8(vhaddq_u8(a, b)));
    Q("vrhaddq_s16", s16(vrhaddq_s16(ha, hb)));
    Q("vhsubq_s32", s32(vhsubq_s32(sa, sb)));
    Q("vmaxq_u8", u8(vmaxq_u8(a, b)));
    Q("vminq_s16", s16(vminq_s16(ha, hb)));
    Q("vabdq_u8", u8(vabdq_u8(a, b)));
    Q("vabdq_s32", s32(vabdq_s32(sa, sb)));
    Q("vabaq_u8", u8(vabaq_u8(a, a, b)));
    Q("vqdmulhq_s16", s16(vqdmulhq_s16(ha, hb)));
    Q("vqrdmulhq_s32", s32(vqrdmulhq_s32(sa, sb)));
    Q("vqdmulhq_lane_s16", s16(vqdmulhq_lane_s16(ha, vget_low_s16(hb), 3)));
    Q("vqrdmulhq_laneq_s32", s32(vqrdmulhq_laneq_s32(sa, sb, 2)));
    Q("vpaddq_u8", u8(vpaddq_u8(a, b)));
    Q("vpmaxq_s16", s16(vpmaxq_s16(ha, hb)));
    Q("vpminq_u8", u8(vpminq_u8(a, b)));
    Q("vqabsq_s16", s16(vqabsq_s16(ha)));
    Q("vqnegq_s32", s32(vqnegq_s32(sa)));
    Q("vabsq_s16", s16(vabsq_s16(ha)));
    Q("vnegq_s32", s32(vnegq_s32(sa)));
    Q("vclsq_s16", s16(vclsq_s16(ha)));
    Q("vclzq_u8", u8(vclzq_u8(a)));
    Q("vcntq_u8", u8(vcntq_u8(a)));
    Q("vrbitq_u8", u8(vrbitq_u8(a)));
    Q("vmvnq_u8", u8(vmvnq_u8(a)));
    Q("vuqaddq_s8", s8(vuqaddq_s8(vreinterpretq_s8_u8(a), b)));
    Q("vsqaddq_u8", u8(vsqaddq_u8(a, vreinterpretq_s8_u8(b))));
    Q("vpaddlq_u8", u16(vpaddlq_u8(a)));
    Q("vpadalq_s16", s32(vpadalq_s16(sa, ha)));
    Q("vmull_u8", u16(vmull_u8(vget_low_u8(a), vget_high_u8(b))));
    Q("vmull_high_s16", s32(vmull_high_s16(ha, hb)));
    Q("vqdmull_s16", s32(vqdmull_s16(vget_low_s16(ha), vget_low_s16(hb))));
    Q("vmlal_u8", u16(vmlal_u8(vreinterpretq_u16_u8(a), vget_low_u8(a), vget_low_u8(b))));
    Q("vmull_p8", p16(vmull_p8(vget_low_p8(vreinterpretq_p8_u8(a)), vget_low_p8(vreinterpretq_p8_u8(b)))));
    Q("vmulq_p8", p8(vmulq_p8(vreinterpretq_p8_u8(a), vreinterpretq_p8_u8(b))));
    Q("vaddhn_s32", s16(vcombine_s16(vaddhn_s32(sa, sb), vraddhn_s32(sa, sb))));
    Q("vsubhn_s16", s8(vcombine_s8(vsubhn_s16(ha, hb), vrsubhn_s16(ha, hb))));
    Q("vaddl_u8", u16(vaddl_u8(vget_low_u8(a), vget_low_u8(b))));
    Q("vsubw_s16", s32(vsubw_s16(sa, vget_low_s16(hb))));
    Q("vabdl_u8", u16(vabdl_u8(vget_low_u8(a), vget_low_u8(b))));
    Q("vtstq_u8", u8(vtstq_u8(a, b)));
    Q("vceqq_u8", u8(vceqq_u8(a, vrev64q_u8(a))));
    Q("vcgtq_s16", u16(vcgtq_s16(ha, hb)));
    Q("vcleq_s32", u32(vcleq_s32(sa, sb)));
    Q("vbslq_u8", u8(vbslq_u8(vcgtq_u8(a, b), a, b)));
}

__attribute__((noinline)) static void shifts(void) {
    uint8x16_t a = vld1q_u8(b8 + 3);
    int16x8_t ha = vld1q_s16(h16 + 5);
    int32x4_t sa = vld1q_s32(s32 + 2);
    int8x16_t sh = vsubq_s8(vandq_s8(vreinterpretq_s8_u8(vld1q_u8(b8 + 30)), vdupq_n_s8(15)), vdupq_n_s8(7));
    Q("vshlq_u8", u8(vshlq_u8(a, sh)));
    Q("vshlq_s16", s16(vshlq_s16(ha, vmovl_s8(vget_low_s8(sh)))));
    Q("vqshlq_u8", u8(vqshlq_u8(a, sh)));
    Q("vqshlq_s8", s8(vqshlq_s8(vreinterpretq_s8_u8(a), sh)));
    Q("vrshlq_s16", s16(vrshlq_s16(ha, vmovl_s8(vget_high_s8(sh)))));
    Q("vqrshlq_u8", u8(vqrshlq_u8(a, sh)));
    Q("vshlq_n_u8", u8(vshlq_n_u8(a, 3)));
    Q("vshrq_n_s16", s16(vshrq_n_s16(ha, 5)));
    Q("vshrq_n_u32", u32(vshrq_n_u32(vreinterpretq_u32_s32(sa), 31)));
    Q("vrshrq_n_s32", s32(vrshrq_n_s32(sa, 7)));
    Q("vrsraq_n_u8", u8(vrsraq_n_u8(a, a, 2)));
    Q("vsraq_n_s16", s16(vsraq_n_s16(ha, ha, 9)));
    Q("vqshlq_n_s16", s16(vqshlq_n_s16(ha, 4)));
    Q("vqshluq_n_s16", u16(vqshluq_n_s16(ha, 3)));
    Q("vqshlq_n_u8", u8(vqshlq_n_u8(a, 2)));
    Q("vsliq_n_u8", u8(vsliq_n_u8(a, vrev16q_u8(a), 3)));
    Q("vsriq_n_u16", u16(vsriq_n_u16(vreinterpretq_u16_u8(a), vreinterpretq_u16_s16(ha), 5)));
    Q("vshrn_n_s32", s16(vcombine_s16(vshrn_n_s32(sa, 9), vrshrn_n_s32(sa, 16))));
    Q("vqshrn_n_s32", s16(vcombine_s16(vqshrn_n_s32(sa, 9), vqrshrn_n_s32(sa, 3))));
    Q("vqshrun_n_s16", u8(vcombine_u8(vqshrun_n_s16(ha, 2), vqrshrun_n_s16(ha, 7))));
    Q("vqshrn_n_u16", u8(vcombine_u8(vqshrn_n_u16(vreinterpretq_u16_s16(ha), 4),
                                    vqrshrn_n_u16(vreinterpretq_u16_s16(ha), 1))));
    Q("vshll_n_u8", u16(vshll_n_u8(vget_low_u8(a), 3)));
    Q("vshll_high_n_s16", s32(vshll_high_n_s16(ha, 16)));
    Q("vmovn_s32", s16(vcombine_s16(vmovn_s32(sa), vqmovn_s32(sa))));
    Q("vqmovun_s16", u8(vcombine_u8(vqmovun_s16(ha), vqmovn_u16(vreinterpretq_u16_s16(ha)))));
    Q("vmovl_u8", u16(vmovl_u8(vget_high_u8(a))));
}

__attribute__((noinline)) static void fp(void) {
    float32x4_t a = vld1q_f32(f32), b = vld1q_f32(f32 + 4);
    float64x2_t da = vld1q_f64(f64), db = vld1q_f64(f64 + 2);
    Q("vaddq_f32", f32(vaddq_f32(a, b)));
    Q("vmulq_f64", f64(vmulq_f64(da, db)));
    Q("vdivq_f32", f32(vdivq_f32(a, b)));
    Q("vfmaq_f32", f32(vfmaq_f32(a, b, a)));
    Q("vfmsq_f64", f64(vfmsq_f64(da, db, da)));
    Q("vfmaq_laneq_f32", f32(vfmaq_laneq_f32(a, b, a, 3)));
    Q("vmaxq_f32", f32(vmaxq_f32(a, b)));
    Q("vminq_f64", f64(vminq_f64(da, db)));
    Q("vmaxnmq_f32", f32(vmaxnmq_f32(a, b)));
    Q("vminnmq_f64", f64(vminnmq_f64(da, db)));
    Q("vabdq_f32", f32(vabdq_f32(a, b)));
    Q("vmulxq_f32", f32(vmulxq_f32(a, b)));
    Q("vrecpeq_f32", f32(vrecpeq_f32(b)));
    Q("vrecpsq_f32", f32(vrecpsq_f32(a, b)));
    Q("vrsqrteq_f32", f32(vrsqrteq_f32(vabsq_f32(b))));
    Q("vrsqrtsq_f64", f64(vrsqrtsq_f64(da, db)));
    Q("vsqrtq_f32", f32(vsqrtq_f32(vabsq_f32(a))));
    Q("vrecpeq_u32", u32(vrecpeq_u32(vreinterpretq_u32_f32(a))));
    Q("vrsqrteq_u32", u32(vrsqrteq_u32(vreinterpretq_u32_f32(b))));
    Q("vcageq_f32", u32(vcageq_f32(a, b)));
    p64x2("vcaltq_f64", vcaltq_f64(da, db));
    Q("vcgtq_f32", u32(vcgtq_f32(a, b)));
    Q("vpaddq_f32", f32(vpaddq_f32(a, b)));
    Q("vpmaxq_f32", f32(vpmaxq_f32(a, b)));
    Q("vpminnmq_f64", f64(vpminnmq_f64(da, db)));
    Q("vcvtq_s32_f32", s32(vcvtq_s32_f32(vmulq_n_f32(a, 1000.5f))));
    Q("vcvtq_u32_f32", u32(vcvtq_u32_f32(vmulq_n_f32(b, 3.25f))));
    Q("vcvtnq_s32_f32", s32(vcvtnq_s32_f32(a)));
    Q("vcvtmq_s32_f32", s32(vcvtmq_s32_f32(a)));
    Q("vcvtpq_u32_f32", u32(vcvtpq_u32_f32(a)));
    Q("vcvtaq_s64_f64", s64(vcvtaq_s64_f64(da)));
    Q("vcvtq_f32_s32", f32(vcvtq_f32_s32(vld1q_s32(s32))));
    Q("vcvtq_n_f32_s32", f32(vcvtq_n_f32_s32(vld1q_s32(s32), 12)));
    Q("vcvtq_n_u32_f32", u32(vcvtq_n_u32_f32(vabsq_f32(a), 8)));
    Q("vcvtq_n_s64_f64", s64(vcvtq_n_s64_f64(da, 20)));
    Q("vcvt_f64_f32", f64(vcvt_f64_f32(vget_low_f32(a))));
    Q("vcvt_f32_f64", f32(vcombine_f32(vcvt_f32_f64(da), vcvtx_f32_f64(db))));
    Q("vrndnq_f32", f32(vrndnq_f32(a)));
    Q("vrndpq_f32", f32(vrndpq_f32(a)));
    Q("vrndmq_f64", f64(vrndmq_f64(da)));
    Q("vrndq_f32", f32(vrndq_f32(a)));
    Q("vrndaq_f32", f32(vrndaq_f32(a)));
    Q("vrndxq_f64", f64(vrndxq_f64(db)));
    Q("vrndiq_f32", f32(vrndiq_f32(b)));
    pf("vaddvq_f32", vaddvq_f32(a));
    pf("vmaxvq_f32", vmaxvq_f32(a));
    pf("vminnmvq_f32", vminnmvq_f32(b));
    pf("vmaxv_f32", vmaxv_f32(vget_low_f32(b)));
    pf("vaddvq_f64", vaddvq_f64(da));
    pf("vmaxnmvq_f64", vmaxnmvq_f64(db));
    pf("vrecpes_f32", vrecpes_f32(f32[3]));
    pf("vrsqrted_f64", vrsqrted_f64(f64[0] * f64[0]));
    pf("vmulxd_f64", vmulxd_f64(f64[1], f64[5]));
    pf("vabds_f32", vabds_f32(f32[1], f32[9]));
    pu("vcvtd_s64_f64", (unsigned long long)vcvtd_s64_f64(f64[0] * 1e9));
    pu("vcvtns_s32_f32", (unsigned)vcvtns_s32_f32(f32[2]));
    pu("vcvtas_u32_f32", vcvtas_u32_f32(f32[12]));
    pu("vcvtmd_s64_f64", (unsigned long long)vcvtmd_s64_f64(f64[6]));
    pf("vrndns_f32", vrndns_f32(f32[5]));
}

__attribute__((noinline)) static void perm(void) {
    uint8x16_t a = vld1q_u8(b8), b = vld1q_u8(b8 + 16), c = vld1q_u8(b8 + 32), d = vld1q_u8(b8 + 48);
    uint8x16_t idx = vandq_u8(vld1q_u8(b8 + 7), vdupq_n_u8(63));
    uint8x16x2_t t2 = {{a, b}};
    uint8x16x3_t t3 = {{a, b, c}};
    uint8x16x4_t t4 = {{a, b, c, d}};
    Q("vqtbl1q_u8", u8(vqtbl1q_u8(a, idx)));
    Q("vqtbl2q_u8", u8(vqtbl2q_u8(t2, idx)));
    Q("vqtbl3q_u8", u8(vqtbl3q_u8(t3, idx)));
    Q("vqtbl4q_u8", u8(vqtbl4q_u8(t4, idx)));
    Q("vqtbx1q_u8", u8(vqtbx1q_u8(d, a, idx)));
    Q("vqtbx4q_u8", u8(vqtbx4q_u8(c, t4, vaddq_u8(idx, idx))));
    D("vtbl1_u8", u8(vtbl1_u8(vget_low_u8(a), vget_low_u8(idx))));
    D("vtbx2_u8", u8(vtbx2_u8(vget_low_u8(c), (uint8x8x2_t){{vget_low_u8(a), vget_high_u8(a)}}, vget_high_u8(idx))));
    D("vtbl3_u8", u8(vtbl3_u8((uint8x8x3_t){{vget_low_u8(a), vget_high_u8(a), vget_low_u8(b)}}, vget_high_u8(idx))));
    Q("vextq_u8", u8(vextq_u8(a, b, 5)));
    Q("vzip1q_u8", u8(vzip1q_u8(a, b)));
    Q("vzip2q_u16", u16(vzip2q_u16(vreinterpretq_u16_u8(a), vreinterpretq_u16_u8(b))));
    Q("vuzp1q_u8", u8(vuzp1q_u8(a, b)));
    Q("vuzp2q_u32", u32(vuzp2q_u32(vreinterpretq_u32_u8(a), vreinterpretq_u32_u8(b))));
    Q("vtrn1q_u8", u8(vtrn1q_u8(a, b)));
    Q("vtrn2q_u16", u16(vtrn2q_u16(vreinterpretq_u16_u8(a), vreinterpretq_u16_u8(b))));
    Q("vrev32q_u8", u8(vrev32q_u8(a)));
    Q("vdupq_laneq_u8", u8(vdupq_laneq_u8(a, 13)));
    Q("vdupq_n_u16", u16(vdupq_n_u16((uint16_t)b8[9])));
    Q("vsetq_lane_u8", u8(vsetq_lane_u8(77, a, 9)));
    Q("vcopyq_laneq_u32", u32(vcopyq_laneq_u32(vreinterpretq_u32_u8(a), 1, vreinterpretq_u32_u8(b), 3)));
    Q("vcombine_u8", u8(vcombine_u8(vget_high_u8(b), vget_low_u8(a))));
    pu("vgetq_lane_u8", vgetq_lane_u8(b, 11));
    pu("vgetq_lane_s16", (unsigned)vgetq_lane_s16(vreinterpretq_s16_u8(c), 6));
    pu("vaddvq_u8", vaddvq_u8(a));
    pu("vaddvq_s16", (unsigned)vaddvq_s16(vreinterpretq_s16_u8(b)));
    pu("vaddvq_u32", vaddvq_u32(vreinterpretq_u32_u8(c)));
    pu("vaddvq_u64", vaddvq_u64(vreinterpretq_u64_u8(d)));
    pu("vaddv_s32", (unsigned)vaddv_s32(vget_low_s32(vreinterpretq_s32_u8(c))));
    pu("vaddlvq_u8", vaddlvq_u8(a));
    pu("vaddlvq_s16", (unsigned)vaddlvq_s16(vreinterpretq_s16_u8(b)));
    pu("vaddlvq_u32", vaddlvq_u32(vreinterpretq_u32_u8(c)));
    pu("vmaxvq_u8", vmaxvq_u8(a));
    pu("vminvq_s8", (unsigned)(int)vminvq_s8(vreinterpretq_s8_u8(b)));
    pu("vmaxvq_s16", (unsigned)(int)vmaxvq_s16(vreinterpretq_s16_u8(c)));
    pu("vminvq_u32", vminvq_u32(vreinterpretq_u32_u8(d)));
    pu("vmaxv_s32", (unsigned)vmaxv_s32(vget_low_s32(vreinterpretq_s32_u8(c))));
    pu("vminv_u16", vminv_u16(vget_low_u16(vreinterpretq_u16_u8(d))));
}

__attribute__((noinline)) static void structs(void) {
    uint8_t out[64];
    uint8x16x2_t l2 = vld2q_u8(b8);
    uint8x16x3_t l3 = vld3q_u8(b8 + 1);
    uint16x8x4_t l4 = vld4q_u16((const uint16_t *)b8);
    int32x2x2_t d2 = vld2_s32(s32 + 1);
    float32x4x2_t f2 = vld2q_f32(f32);
    Q("vld2q_u8.0", u8(l2.val[0]));
    Q("vld2q_u8.1", u8(l2.val[1]));
    Q("vld3q_u8.2", u8(l3.val[2]));
    Q("vld4q_u16.3", u16(l4.val[3]));
    D("vld2_s32.1", s32(d2.val[1]));
    Q("vld2q_f32.0", f32(f2.val[0]));
    uint8x16x2_t r2 = vld2q_dup_u8(b8 + 5);
    Q("vld2q_dup_u8.1", u8(r2.val[1]));
    uint16x8x3_t lane3 = vld3q_lane_u16((const uint16_t *)(b8 + 2), ((uint16x8x3_t){{l4.val[0], l4.val[1], l4.val[2]}}), 5);
    Q("vld3q_lane_u16.2", u16(lane3.val[2]));
    uint8x16x4_t x4 = vld1q_u8_x4(b8);
    Q("vld1q_u8_x4.3", u8(x4.val[3]));
    memset(out, 0, sizeof out);
    vst2q_u8(out, l2);
    P8(vld1q_u8(out + 16));
    vst3q_u8(out, l3);
    P8(vld1q_u8(out + 32));
    vst4q_u16((uint16_t *)out, l4);
    P8(vld1q_u8(out + 48));
    vst3q_lane_u16((uint16_t *)(out + 1), lane3, 6);
    P8(vld1q_u8(out));
    vst1q_u8_x2(out + 3, l2);
    P8(vld1q_u8(out + 16));
    vst1q_lane_u8(out + 60, vld1q_u8(b8), 7);
    pu("vst1q_lane_u8", out[60]);
}

__attribute__((noinline)) static void scalars(void) {
    int8_t i8 = (int8_t)b8[5];
    int16_t i16 = h16[7];
    int32_t i32 = s32[3];
    int64_t i64 = (int64_t)s32[5] << 20;
    pu("vqaddb_s8", (unsigned)(int)vqaddb_s8(i8, 100));
    pu("vqaddh_s16", (unsigned)(int)vqaddh_s16(i16, 30000));
    pu("vqadds_s32", (unsigned)vqadds_s32(i32, 0x7fff0000));
    pu("vqaddd_s64", (unsigned long long)vqaddd_s64(i64, 0x7fffffffffff0000ll));
    pu("vqsubs_u32", vqsubs_u32((uint32_t)i32, 0x12345678u));
    pu("vqdmulhs_s32", (unsigned)vqdmulhs_s32(i32, s32[7]));
    pu("vqrdmulhh_s16", (unsigned)(int)vqrdmulhh_s16(i16, h16[12]));
    pu("vqdmullh_s16", (unsigned)vqdmullh_s16(i16, h16[3]));
    pu("vqdmulls_s32", (unsigned long long)vqdmulls_s32(i32, s32[9]));
    pu("vqshlb_u8", vqshlb_u8((uint8_t)i8, 3));
    pu("vqshls_s32", (unsigned)vqshls_s32(i32, -5));
    pu("vrshld_s64", (unsigned long long)vrshld_s64(i64, -9));
    pu("vshld_u64", (unsigned long long)vshld_u64((uint64_t)i64, 4));
    pu("vqrshld_u64", (unsigned long long)vqrshld_u64((uint64_t)i64, 7));
    pu("vqabss_s32", (unsigned)vqabss_s32(i32));
    pu("vqnegd_s64", (unsigned long long)vqnegd_s64(i64));
    pu("vabsd_s64", (unsigned long long)vabsd_s64(i64));
    pu("vqmovnd_s64", (unsigned)vqmovnd_s64(i64));
    pu("vqmovuns_s32", vqmovuns_s32(i32));
    pu("vqmovnh_u16", vqmovnh_u16((uint16_t)i16));
    pu("vqshrns_n_s32", (unsigned)(int)vqshrns_n_s32(i32, 5));
    pu("vqrshrund_n_s64", vqrshrund_n_s64(i64, 17));
    pu("vqshlud_n_s64", (unsigned long long)vqshlud_n_s64(i64 >> 30, 3));
    pu("vshrd_n_s64", (unsigned long long)vshrd_n_s64(i64, 13));
    pu("vrshrd_n_u64", (unsigned long long)vrshrd_n_u64((uint64_t)i64, 63));
    pu("vslid_n_u64", (unsigned long long)vslid_n_u64((uint64_t)i64, 0x123456789abcdefull, 17));
    pu("vsrid_n_s64", (unsigned long long)vsrid_n_s64(i64, -7, 40));
    pu("vuqaddb_s8", (unsigned)(int)vuqaddb_s8(i8, 200));
    pu("vsqaddd_u64", (unsigned long long)vsqaddd_u64(5, -3));
    pu("vcvts_n_s32_f32", (unsigned)vcvts_n_s32_f32(f32[4], 10));
    pf("vcvtd_n_f64_u64", vcvtd_n_f64_u64((uint64_t)i64, 33));
    pu("vpaddd_u64", vpaddd_u64(vld1q_u64((const uint64_t *)s32)));
    pf("vpadds_f32", vpadds_f32(vld1_f32(f32 + 2)));
    pf("vmaxnmvq_f32", vmaxnmvq_f32(vld1q_f32(f32 + 6)));
    pu("vceqzd_s64", vceqzd_s64(i64));
    pu("vcgtd_s64", vcgtd_s64(i64, 7));
    pu("vtstd_u64", vtstd_u64((uint64_t)i64, 0x100000));
}

int main(void) {
    init();
    arith();
    shifts();
    fp();
    perm();
    structs();
    scalars();
    printf("sum %08x\n", sum);
    return 0;
}
