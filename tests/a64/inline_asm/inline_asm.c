// AArch64 inline assembly (milestone F1): register classes and modifiers
// (r with %w/%x, w with %s/%d/%q and vN.4s, x), fixed registers, tied
// operands, immediates (I, K, L, M, N, Z with %w), memory operands (m, Q),
// clobbers of caller- and callee-saved registers, system registers,
// several outputs, and an exclusive-access loop.
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static uint64_t add_rr(uint64_t a, uint64_t b) {
    uint64_t r;
    __asm__("add %0, %1, %2" : "=r"(r) : "r"(a), "r"(b));
    return r;
}
static uint32_t add_w(uint32_t a, uint32_t b) {
    uint32_t r;
    __asm__("add %w0, %w1, %w2" : "=r"(r) : "r"(a), "r"(b));
    return r;
}
static uint32_t add_imm(uint32_t a) {
    uint32_t r;
    __asm__("add %w0, %w1, %2" : "=r"(r) : "r"(a), "I"(4095));
    return r;
}
static uint64_t logic_imm(uint64_t a) {
    uint64_t r;
    __asm__("and %0, %1, %2" : "=r"(r) : "r"(a), "L"(0xFF00FF00FF00FF00ull));
    return r;
}
static uint64_t movk(void) {
    uint64_t r;
    __asm__("mov %0, %1\n\tmovk %0, %2, lsl #16" : "=r"(r) : "N"(0x1234), "M"(0xBEEF));
    return r;
}
static uint32_t zero_reg(uint32_t a) {
    uint32_t r;
    __asm__("orr %w0, %w1, %w2" : "=r"(r) : "rZ"(0), "r"(a));
    return r;
}
static uint64_t tied(uint64_t a) {
    __asm__("lsl %0, %0, #3" : "+r"(a));
    return a;
}
static double fmadd(double a, double b, double c) {
    double r;
    __asm__("fmadd %d0, %d1, %d2, %d3" : "=w"(r) : "w"(a), "w"(b), "w"(c));
    return r;
}
static float fsqrt(float a) {
    float r;
    __asm__("fsqrt %s0, %s1" : "=w"(r) : "w"(a));
    return r;
}
typedef float v4f __attribute__((vector_size(16)));
typedef int32_t v4i __attribute__((vector_size(16)));
static v4f vadd(v4f a, v4f b) {
    v4f r;
    __asm__("fadd %0.4s, %1.4s, %2.4s" : "=w"(r) : "w"(a), "x"(b));
    return r;
}
static v4i vmul_lane(v4i a, v4i b) {
    v4i r;
    __asm__("mul %0.4s, %1.4s, %2.s[1]" : "=w"(r) : "w"(a), "x"(b));
    return r;
}
static uint64_t fixed_regs(uint64_t a, uint64_t b) {
    register uint64_t x3 __asm__("x3") = a;
    register uint64_t x5 __asm__("x5") = b;
    uint64_t r;
    __asm__("sub %0, x3, x5" : "=r"(r) : "r"(x3), "r"(x5));
    return r;
}
static uint64_t fixed_constraint(uint64_t a) {
    uint64_t r;
    __asm__("eor x9, %1, %1, lsl #1\n\tmov %0, x9" : "=r"(r) : "r"(a) : "x9");
    return r;
}
static void two_out(uint64_t a, uint64_t *q, uint64_t *rem) {
    uint64_t x, y;
    __asm__("mov %0, %2\n\tlsr %0, %0, #4\n\tand %1, %2, #15" : "=&r"(x), "=r"(y) : "r"(a));
    *q = x;
    *rem = y;
}
static uint64_t load_mem(const uint64_t *p) {
    uint64_t r;
    __asm__("ldr %0, %1" : "=r"(r) : "m"(*p));
    return r;
}
static void store_q(uint32_t *p, uint32_t v) {
    __asm__ volatile("str %w1, %0" : "=Q"(*p) : "r"(v) : "memory");
}
static uint64_t clobber_callee(uint64_t a) {
    uint64_t keep = a * 3;
    __asm__ volatile("mov x19, #77\n\tmov x20, #78\n\tmov x27, #79\n\tfmov d8, #1.0\n\tfmov d9, #2.0" :::
                     "x19", "x20", "x27", "v8", "v9");
    return keep + 1;
}
static uint64_t atomic_add(uint64_t *p, uint64_t v) {
    uint64_t old, tmp;
    uint32_t st;
    __asm__ volatile("1: ldaxr %0, [%3]\n\t"
                     "add %1, %0, %4\n\t"
                     "stlxr %w2, %1, [%3]\n\t"
                     "cbnz %w2, 1b"
                     : "=&r"(old), "=&r"(tmp), "=&r"(st)
                     : "r"(p), "r"(v)
                     : "memory");
    return old;
}
static uint64_t fpcr_roundtrip(void) {
    uint64_t c;
    __asm__ volatile("mrs %0, fpcr" : "=r"(c));
    __asm__ volatile("msr fpcr, %0" : : "r"(c));
    return c & 0xC00000;   // the rounding mode
}
static uint64_t sat_flag(void) {
    uint64_t f;
    __asm__ volatile("msr fpsr, xzr\n\t"
                     "movi v0.16b, #127\n\t"
                     "sqadd v0.16b, v0.16b, v0.16b\n\t"
                     "mrs %0, fpsr" : "=r"(f) : : "v0");
    return f >> 27 & 1;
}
static int count_ones(uint64_t a) {
    int r;
    __asm__("fmov d31, %1\n\tcnt v31.8b, v31.8b\n\taddv b31, v31.8b\n\tumov %w0, v31.b[0]" : "=r"(r) : "r"(a) : "v31");
    return r;
}

int main(void) {
    printf("%llu %u %u\n", (unsigned long long)add_rr(1ull << 40, 7), add_w(0xFFFFFFFFu, 2), add_imm(1));
    printf("%llx %llx %u\n", (unsigned long long)logic_imm(0x123456789ABCDEFull), (unsigned long long)movk(),
           zero_reg(0x55));
    printf("%llu %.6f %.6f\n", (unsigned long long)tied(5), fmadd(1.5, 2.0, 0.25), fsqrt(2.0f));
    v4f a = {1, 2, 3, 4}, b = {0.5f, 0.25f, 0.125f, 8};
    v4f c = vadd(a, b);
    v4i ia = {1, 2, 3, 4}, ib = {10, 20, 30, 40};
    v4i ic = vmul_lane(ia, ib);
    printf("%g %g %g %g / %d %d %d %d\n", c[0], c[1], c[2], c[3], ic[0], ic[1], ic[2], ic[3]);
    printf("%llu %llx\n", (unsigned long long)fixed_regs(100, 58), (unsigned long long)fixed_constraint(0x0F0F));
    uint64_t q, rem;
    two_out(0x12345, &q, &rem);
    uint64_t m = 0xDEADBEEF;
    uint32_t w = 0;
    store_q(&w, 0xCAFE);
    printf("%llx %llx %llx %x\n", (unsigned long long)q, (unsigned long long)rem, (unsigned long long)load_mem(&m), w);
    uint64_t ctr = 40;
    uint64_t old = atomic_add(&ctr, 2);
    printf("%llu %llu %llu\n", (unsigned long long)clobber_callee(14), (unsigned long long)old,
           (unsigned long long)ctr);
    printf("%llx %llu %d %d\n", (unsigned long long)fpcr_roundtrip(), (unsigned long long)sat_flag(),
           count_ones(0xF0F0F0F0F0F0F0F0ull), count_ones(7));
    return 0;
}
