// Bit manipulation: popcount, reverse, masks, parity, gray codes.
#include <stdio.h>
#include <stdint.h>

static int popcount(uint64_t x) { int n = 0; while (x) { x &= x - 1; n++; } return n; }
static uint32_t rev32(uint32_t x) {
    x = ((x >> 1) & 0x55555555u) | ((x & 0x55555555u) << 1);
    x = ((x >> 2) & 0x33333333u) | ((x & 0x33333333u) << 2);
    x = ((x >> 4) & 0x0F0F0F0Fu) | ((x & 0x0F0F0F0Fu) << 4);
    x = ((x >> 8) & 0x00FF00FFu) | ((x & 0x00FF00FFu) << 8);
    return (x >> 16) | (x << 16);
}
static int clz64(uint64_t x) { int n = 0; if (!x) return 64; while (!(x >> 63)) { x <<= 1; n++; } return n; }
static uint16_t bswap16(uint16_t x) { return (uint16_t)((x >> 8) | (x << 8)); }

int main(void) {
    uint64_t v[] = {0, 1, 0xFF, 0x8000000000000000ull, 0xDEADBEEFCAFEBABEull, 0x0123456789ABCDEFull};
    for (int i = 0; i < 6; i++) printf("%d %d ", popcount(v[i]), clz64(v[i]));
    printf("\n%08x %08x %04x\n", rev32(1), rev32(0x12345678u), bswap16(0xABCD));
    uint32_t m = 0;
    for (int i = 0; i < 32; i += 3) m |= 1u << i;
    printf("mask %08x %08x %08x %08x\n", m, m & 0xFFFF, m ^ 0xFFFFFFFFu, ~m >> 4);
    for (unsigned i = 0; i < 8; i++) printf("%u ", i ^ (i >> 1));
    printf("\n");
    int64_t s = -1;
    printf("%llx %llx\n", (unsigned long long)(s & 0x0F0F0F0F0F0F0F0FLL), (unsigned long long)((uint64_t)s >> 60));
    uint8_t flags = 0;
    flags |= 1 << 3;
    flags |= 1 << 7;
    flags &= (uint8_t)~(1 << 3);
    printf("flags %u %d\n", flags, (flags & 0x80) != 0);
    unsigned long long x = 0x0123456789ABCDEFull, y = 0;
    for (int i = 0; i < 8; i++) y = (y << 8) | ((x >> (8 * i)) & 0xFF);
    printf("bswap64 %016llx\n", y);
    printf("lowbit %d %d\n", (int)(48 & -48), (int)(0x7000 & -0x7000));
    return 0;
}
