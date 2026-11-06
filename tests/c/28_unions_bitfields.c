// Unions (type punning on integers) and bitfields.
#include <stdio.h>
#include <stdint.h>

union U { uint32_t u; int32_t i; uint8_t b[4]; uint16_t h[2]; };
struct BF { unsigned a : 3; unsigned b : 5; int c : 4; unsigned d : 12; unsigned e : 8; };
struct Flags { unsigned char on : 1, mode : 2, level : 5; };

int main(void) {
    union U x;
    x.u = 0x80402010u;
    printf("%d %u %u %u %u %u\n", x.i, x.b[0], x.b[3], x.h[0], x.h[1], (unsigned)sizeof x);
    x.b[1] = 0xFF;
    printf("%08x\n", x.u);
    struct BF bf = {0};
    bf.a = 5; bf.b = 17; bf.c = -3; bf.d = 4000; bf.e = 255;
    printf("%u %u %d %u %u %u\n", bf.a, bf.b, bf.c, bf.d, bf.e, (unsigned)sizeof bf);
    bf.a += 4;
    bf.c -= 6;
    bf.d *= 2;
    printf("%u %d %u\n", bf.a, bf.c, bf.d);
    struct Flags f[4];
    for (int i = 0; i < 4; i++) { f[i].on = i & 1; f[i].mode = (unsigned char)i; f[i].level = (unsigned char)(i * 9); }
    for (int i = 0; i < 4; i++) printf("%u%u%u ", f[i].on, f[i].mode, f[i].level);
    printf("\n");
    return 0;
}
