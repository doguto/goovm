// Shifts of every width, constant and variable amounts, signed and unsigned.
#include <stdio.h>
#include <stdint.h>

int main(void) {
    volatile int amt = 3;
    int8_t a = -100;
    uint8_t b = 0xF0;
    int16_t c = -30000;
    uint16_t d = 0xF00F;
    int32_t e = -123456789;
    uint32_t f = 0x80000001u;
    int64_t g = -1234567890123456789LL;
    uint64_t h = 0x8000000000000001ull;
    for (int s = 0; s < 8; s++)
        printf("8: %d %d %u %u\n", (int8_t)(a << s), (int8_t)(a >> s), (uint8_t)(b << s), (uint8_t)(b >> s));
    for (int s = 0; s < 16; s += 3)
        printf("16: %d %d %u %u\n", (int16_t)(c << s), (int16_t)(c >> s), (uint16_t)(d << s), (uint16_t)(d >> s));
    for (int s = 0; s < 32; s += 5)
        printf("32: %d %d %u %u\n", (int32_t)((uint32_t)e << s), e >> s, f << s, f >> s);
    for (int s = 0; s < 64; s += 7)
        printf("64: %lld %lld %llu %llu\n", (long long)((uint64_t)g << s), (long long)(g >> s),
               (unsigned long long)(h << s), (unsigned long long)(h >> s));
    printf("const %d %d %u %lld\n", e >> 31, e >> 1, f >> 31, (long long)(g >> 63));
    printf("var %d %u %lld %llu\n", e >> amt, f << amt, (long long)(g >> amt), (unsigned long long)(h >> amt));
    uint32_t x = 0x12345678u;
    for (int r = 0; r < 32; r += 4) printf("rot %08x\n", (x << r) | (x >> ((32 - r) & 31)));
    return 0;
}
