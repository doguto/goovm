// Hashing and pseudo-random number generators with unsigned wrap-around.
#include <stdio.h>
#include <stdint.h>

static uint32_t crc_table[256];
static void crc_init(void) {
    for (uint32_t i = 0; i < 256; i++) {
        uint32_t c = i;
        for (int k = 0; k < 8; k++) c = c & 1 ? 0xEDB88320u ^ (c >> 1) : c >> 1;
        crc_table[i] = c;
    }
}
static uint32_t crc32(const char *s) {
    uint32_t c = 0xFFFFFFFFu;
    while (*s) c = crc_table[(c ^ (uint8_t)*s++) & 0xFF] ^ (c >> 8);
    return c ^ 0xFFFFFFFFu;
}
static uint64_t xorshift64(uint64_t *s) { uint64_t x = *s; x ^= x << 13; x ^= x >> 7; x ^= x << 17; return *s = x; }
static uint32_t lcg(uint32_t *s) { return *s = *s * 1664525u + 1013904223u; }
static uint64_t splitmix(uint64_t *s) {
    uint64_t z = (*s += 0x9E3779B97F4A7C15ull);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
    return z ^ (z >> 31);
}
static uint32_t murmur_mix(uint32_t h) { h ^= h >> 16; h *= 0x85ebca6bu; h ^= h >> 13; h *= 0xc2b2ae35u; return h ^ (h >> 16); }

int main(void) {
    crc_init();
    printf("crc %08x %08x\n", crc32("The quick brown fox jumps over the lazy dog"), crc32(""));
    uint64_t s = 88172645463325252ull;
    for (int i = 0; i < 4; i++) printf("%llu ", (unsigned long long)xorshift64(&s));
    uint32_t l = 1;
    for (int i = 0; i < 4; i++) printf("%u ", lcg(&l));
    uint64_t sm = 0;
    for (int i = 0; i < 3; i++) printf("%016llx ", (unsigned long long)splitmix(&sm));
    printf("\n%08x %08x\n", murmur_mix(1), murmur_mix(0xDEADBEEFu));
    int buckets[16] = {0};
    for (int i = 0; i < 10000; i++) buckets[xorshift64(&s) % 16]++;
    int mn = 100000, mx = 0;
    for (int i = 0; i < 16; i++) { if (buckets[i] < mn) mn = buckets[i]; if (buckets[i] > mx) mx = buckets[i]; }
    printf("buckets %d %d\n", mn, mx);
    return 0;
}
