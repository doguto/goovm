// Arithmetic in every integer width, signed and unsigned, with wrap-around.
#include <stdio.h>
#include <stdint.h>

static int8_t a8(int8_t x, int8_t y) { return (int8_t)(x + y); }
static uint8_t au8(uint8_t x, uint8_t y) { return (uint8_t)(x + y); }
static int16_t m16(int16_t x, int16_t y) { return (int16_t)(x * y); }
static uint16_t mu16(uint16_t x, uint16_t y) { return (uint16_t)(x * y); }
static int32_t s32(int32_t x, int32_t y) { return (int32_t)((uint32_t)x - (uint32_t)y); }
static uint32_t mu32(uint32_t x, uint32_t y) { return x * y; }
static int64_t m64(int64_t x, int64_t y) { return (int64_t)((uint64_t)x * (uint64_t)y); }
static uint64_t au64(uint64_t x, uint64_t y) { return x + y; }

int main(void) {
    volatile int8_t i8 = 100;
    volatile uint8_t u8 = 200;
    volatile int16_t i16 = 30000;
    volatile uint16_t u16 = 60000;
    volatile int32_t i32 = 2000000000;
    volatile uint32_t u32 = 4000000000u;
    volatile int64_t i64 = 9000000000000000000LL;
    volatile uint64_t u64 = 18000000000000000000ull;

    printf("i8  %d %d %d\n", a8(i8, 100), a8(-128, -1), (int8_t)(i8 * 3));
    printf("u8  %u %u %u\n", au8(u8, 100), au8(0, 255), (uint8_t)(u8 * 3));
    printf("i16 %d %d %d\n", m16(i16, 3), m16(-32768, -1), (int16_t)(i16 + i16));
    printf("u16 %u %u %u\n", mu16(u16, 3), mu16(65535, 65535), (uint16_t)(u16 + u16));
    printf("i32 %d %d %d\n", s32(-i32, i32), s32(i32, -i32), (int32_t)((uint32_t)i32 * 7u));
    printf("u32 %u %u %u\n", mu32(u32, 3), mu32(0xFFFFFFFFu, 0xFFFFFFFFu), u32 + u32);
    printf("i64 %lld %lld\n", (long long)m64(i64, 3), (long long)m64(INT64_MIN, -1));
    printf("u64 %llu %llu\n", (unsigned long long)au64(u64, u64), (unsigned long long)(u64 * 5));

    // Mixed-width promotions.
    int8_t sc = -5;
    uint8_t uc = 250;
    int16_t ss = -300;
    uint16_t us = 65000;
    printf("mix %d %d %u %lld %llu\n", sc + uc, ss * us, (unsigned)(sc + 0u),
           (long long)sc * us, (unsigned long long)(uint32_t)ss);
    printf("neg %d %d %lld %d\n", -sc, -ss, -(long long)i32, ~sc);
    int64_t acc = 0;
    for (int i = 0; i < 100; i++) acc = acc * 31 + (int8_t)(i * 37);
    printf("acc %lld\n", (long long)acc);
    uint32_t h = 2166136261u;
    for (int i = 0; i < 50; i++) { h ^= (uint8_t)i; h *= 16777619u; }
    printf("fnv %u\n", h);
    return 0;
}
