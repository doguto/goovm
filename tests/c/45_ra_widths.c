// Register allocation: values narrower than their register. A truncated value
// keeps the source's upper bits in its register until a use needs them clean
// (zext, uitofp, division, 64-bit arithmetic, call arguments).
#include <stdio.h>
#include <stdint.h>

__attribute__((noinline)) static uint64_t get64(void) { return 0xAFAFAFAFC5C5B8A3ull; }
__attribute__((noinline)) static uint32_t pass32(uint32_t x) { return x; }
__attribute__((noinline)) static unsigned pass16(unsigned short x) { return x; }
__attribute__((noinline)) static int passs8(signed char x) { return x; }

int main(void) {
    uint64_t L = get64();
    uint32_t ui = (uint32_t)L;
    int32_t si = (int32_t)L;
    uint16_t us = (uint16_t)L;
    int16_t ss = (int16_t)L;
    uint8_t uc = (uint8_t)L;
    int8_t sc = (int8_t)L;
    printf("%llu %llu %llu\n", (unsigned long long)(L - ui), (unsigned long long)(L / ui), (unsigned long long)(L % ui));
    printf("%lld %lld\n", (long long)(L - si), (long long)((int64_t)L / si));
    printf("%llu %llu %llu %llu\n", (unsigned long long)(L - us), (unsigned long long)(L / us),
           (unsigned long long)(L - uc), (unsigned long long)(L / uc));
    printf("%lld %lld %lld\n", (long long)(L + ss), (long long)(L + sc), (long long)((int64_t)L / ss));
    printf("%u %u %d\n", pass32(ui), pass16(us), passs8(sc));
    printf("%f %f %f\n", (double)ui, (double)us, (double)uc);
    printf("%f %f %f\n", (double)si, (double)ss, (double)sc);
    uint32_t a = ui * 3u + 7u, b = (ui >> 3) | (ui << 29);
    uint64_t w = (uint64_t)a * b;
    printf("%u %u %llu\n", a, b, (unsigned long long)w);
    uint16_t m = (uint16_t)(us * 31u + uc);
    uint8_t n = (uint8_t)(uc * 7u + 1u);
    printf("%u %u %u %u\n", m, n, (unsigned)(m >> 4), (unsigned)(n >> 2));
    printf("%d %d\n", (int)(ss >> 3), (int)(sc >> 1));
    printf("%d %d %d\n", ui > 3000000000u, us < 50000, sc < -10);
    unsigned long long acc = 0;
    for (uint32_t i = ui; i != ui + 16; i++) acc += (uint64_t)i * 2 + (i & 3);
    printf("%llu\n", acc);
    return 0;
}
