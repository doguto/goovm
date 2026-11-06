// char/short arithmetic, promotions, narrow parameters and returns.
#include <stdio.h>

static signed char sadd(signed char a, signed char b) { return (signed char)(a + b); }
static unsigned char uadd(unsigned char a, unsigned char b) { return (unsigned char)(a + b); }
static short smul(short a, short b) { return (short)(a * b); }
static unsigned short umul(unsigned short a, unsigned short b) { return (unsigned short)(a * b); }
static _Bool both(_Bool a, _Bool b) { return a && b; }
static char upper(char c) { return c >= 'a' && c <= 'z' ? (char)(c - 32) : c; }

int main(void) {
    for (int i = -130; i < 140; i += 37) printf("%d ", sadd((signed char)i, 100));
    printf("\n");
    for (int i = 0; i < 300; i += 41) printf("%u ", uadd((unsigned char)i, 200));
    printf("\n");
    printf("%d %d %u %u\n", smul(300, 300), smul(-200, 170), umul(300, 300), umul(65535, 2));
    printf("%d %d %d\n", both(1, 1), both(1, 0), both(2, 3));
    char s[] = "Mixed Case 123";
    for (char *p = s; *p; p++) *p = upper(*p);
    printf("%s\n", s);
    signed char sc = -1;
    unsigned char uc = sc;
    short ss = sc;
    unsigned short us = sc;
    printf("%d %u %d %u %d\n", sc, uc, ss, us, (int)(unsigned char)sc);
    signed char arr[8] = {-128, -1, 0, 1, 127, -50, 50, -100};
    int sum = 0;
    unsigned usum = 0;
    for (int i = 0; i < 8; i++) { sum += arr[i]; usum += (unsigned char)arr[i]; }
    printf("%d %u\n", sum, usum);
    short sh = 32767;
    sh++;
    unsigned short ush = 0;
    ush--;
    printf("%d %u\n", sh, ush);
    char c = 'A';
    c += 200;
    printf("%d\n", c);
    unsigned char bits = 0xA5;
    printf("%u %u %u %d\n", (unsigned char)(bits << 1), bits >> 3, (unsigned char)~bits, (signed char)bits >> 2);
    return 0;
}
