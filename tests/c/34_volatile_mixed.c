// Volatile accesses, compound assignments on narrow lvalues, pointer to
// array, comma operator, conditional lvalue-like patterns.
#include <stdio.h>

static volatile int vcount;
struct R { unsigned char r, g, b, a; };

int main(void) {
    for (int i = 0; i < 10; i++) vcount += i;
    printf("%d\n", vcount);
    struct R px[4] = {{1, 2, 3, 4}, {250, 251, 252, 253}, {0}, {9, 9, 9, 9}};
    for (int i = 0; i < 4; i++) { px[i].r += 10; px[i].g *= 2; px[i].b ^= 0xFF; px[i].a >>= 1; }
    for (int i = 0; i < 4; i++) printf("%u,%u,%u,%u ", px[i].r, px[i].g, px[i].b, px[i].a);
    printf("\n");
    int arr[3][4];
    int (*row)[4] = arr;
    for (int i = 0; i < 12; i++) arr[i / 4][i % 4] = i;
    row++;
    printf("%d %d\n", (*row)[2], row[1][3]);
    int a = 1, b = 2, c;
    c = (a += 2, b *= 3, a + b);
    printf("%d %d %d\n", a, b, c);
    int x = 10, y = 20;
    *(x > y ? &x : &y) += 5;
    printf("%d %d\n", x, y);
    short sh[4] = {1000, 2000, 3000, 4000};
    short *ps = sh;
    *ps++ += 1;
    *ps++ -= 1;
    *ps <<= 2;
    printf("%d %d %d %d\n", sh[0], sh[1], sh[2], sh[3]);
    long l = 5;
    l %= 3;
    l <<= 40;
    l /= -7;
    printf("%ld\n", l);
    return 0;
}
