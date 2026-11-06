// Division and remainder with negative operands in every width.
#include <stdio.h>
#include <stdint.h>

static void t32(int32_t a, int32_t b) {
    printf("%d/%d = %d r %d   u: %u r %u\n", a, b, a / b, a % b, (uint32_t)a / (uint32_t)b, (uint32_t)a % (uint32_t)b);
}
static void t64(int64_t a, int64_t b) {
    printf("%lld/%lld = %lld r %lld   u: %llu r %llu\n", (long long)a, (long long)b, (long long)(a / b),
           (long long)(a % b), (unsigned long long)((uint64_t)a / (uint64_t)b),
           (unsigned long long)((uint64_t)a % (uint64_t)b));
}
static void t8(int8_t a, int8_t b) {
    int8_t q = a / b, r = a % b;
    uint8_t uq = (uint8_t)a / (uint8_t)b, ur = (uint8_t)a % (uint8_t)b;
    printf("8: %d %d %u %u\n", q, r, uq, ur);
}
static void t16(int16_t a, int16_t b) {
    int16_t q = a / b, r = a % b;
    uint16_t uq = (uint16_t)a / (uint16_t)b, ur = (uint16_t)a % (uint16_t)b;
    printf("16: %d %d %u %u\n", q, r, uq, ur);
}

int main(void) {
    int32_t v32[] = {7, -7, 100, -100, 2147483647, -2147483647, 1, -1, 13};
    for (int i = 0; i < 9; i++)
        for (int j = 0; j < 9; j += 2) t32(v32[i], v32[j]);
    int64_t v64[] = {7, -7, 1000000000007LL, -1000000000007LL, 3, -3};
    for (int i = 0; i < 6; i++)
        for (int j = 0; j < 6; j++) t64(v64[i], v64[j]);
    int8_t v8[] = {127, -128, 5, -5, 3, -3};
    for (int i = 0; i < 6; i++)
        for (int j = 2; j < 6; j++) t8(v8[i], v8[j]);
    int16_t v16[] = {32767, -32768, 300, -300, 7, -7};
    for (int i = 0; i < 6; i++)
        for (int j = 2; j < 6; j++) t16(v16[i], v16[j]);
    volatile unsigned d = 10;
    unsigned n = 4294967295u;
    printf("digits:");
    while (n) { printf(" %u", n % d); n /= d; }
    printf("\n");
    return 0;
}
