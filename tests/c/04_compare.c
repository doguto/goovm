// Comparisons: signed and unsigned, every width and predicate.
#include <stdio.h>
#include <stdint.h>

#define CMP(T, a, b) printf(#T " %d%d%d%d%d%d\n", (T)(a) < (T)(b), (T)(a) <= (T)(b), (T)(a) > (T)(b), \
                            (T)(a) >= (T)(b), (T)(a) == (T)(b), (T)(a) != (T)(b))

static void all(int64_t a, int64_t b) {
    CMP(int8_t, a, b); CMP(uint8_t, a, b);
    CMP(int16_t, a, b); CMP(uint16_t, a, b);
    CMP(int32_t, a, b); CMP(uint32_t, a, b);
    CMP(int64_t, a, b); CMP(uint64_t, a, b);
}

int main(void) {
    int64_t v[] = {0, 1, -1, 127, -128, 255, 32767, -32768, 65535, 2147483647, -2147483648LL, 4294967295LL,
                   INT64_MAX, INT64_MIN};
    int n = sizeof v / sizeof v[0];
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j += 3) all(v[i], v[j]);
    int x = 5;
    int *p = &x, *q = &x + 1;
    printf("ptr %d %d %d %d\n", p < q, p == q, q > p, p != (int *)0);
    _Bool t = x > 3, f = x < 3;
    printf("bool %d %d %d %d\n", t, f, t == f, t > f);
    return 0;
}
