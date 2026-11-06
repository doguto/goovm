// switch: dense, sparse, fallthrough, nested, char, 64-bit with big cases.
#include <stdio.h>

static const char *name(int d) {
    switch (d) {
    case 0: return "zero"; case 1: return "one"; case 2: return "two"; case 3: return "three";
    case 4: return "four"; case 5: return "five"; case 6: return "six"; case 7: return "seven";
    case 8: return "eight"; case 9: return "nine"; case 10: return "ten"; case 11: return "eleven";
    case 12: return "twelve"; case 13: return "thirteen"; case 14: return "fourteen";
    default: return "many";
    }
}
static int sparse(int x) {
    switch (x) {
    case -1000: return 1;
    case -1: return 2;
    case 7: return 3;
    case 100: return 4;
    case 12345: return 5;
    case 2147483647: return 6;
    case -2147483647 - 1: return 7;
    default: return 0;
    }
}
static int fall(int x) {
    int r = 0;
    switch (x) {
    case 1: r += 1;
    case 2: r += 10;
    case 3: r += 100; break;
    case 4: r += 1000;
    default: r += 10000;
    }
    return r;
}
static long big(long long v) {
    switch (v) {
    case 0x100000000LL: return 1;
    case -0x100000000LL: return 2;
    case 0x7FFFFFFFFFFFFFFFLL: return 3;
    case 5: return 4;
    default: return -1;
    }
}
static int cls(char c) {
    switch (c) {
    case 'a': case 'e': case 'i': case 'o': case 'u': return 1;
    case '0' ... '9': return 2;
    case ' ': return 3;
    default: return 0;
    }
}
static unsigned char ucase(unsigned char c) {
    switch (c) { case 200: return 1; case 255: return 2; case 0: return 3; default: return 4; }
}
static int nested(int a, int b) {
    switch (a) {
    case 0: switch (b) { case 0: return 0; case 1: return 1; default: return 2; }
    case 1: switch (b) { case 0: return 10; default: return 11; }
    default: return 99;
    }
}

int main(void) {
    for (int i = -1; i < 17; i++) printf("%s ", name(i));
    printf("\n");
    int vs[] = {-1000, -1, 7, 100, 12345, 2147483647, -2147483647 - 1, 3, 0};
    for (int i = 0; i < 9; i++) printf("%d", sparse(vs[i]));
    printf("\n");
    for (int i = 0; i < 6; i++) printf("%d ", fall(i));
    printf("\n%ld %ld %ld %ld %ld\n", big(0x100000000LL), big(-0x100000000LL), big(0x7FFFFFFFFFFFFFFFLL), big(5), big(6));
    const char *s = "hello 2024 world";
    int counts[4] = {0};
    for (const char *p = s; *p; p++) counts[cls(*p)]++;
    printf("%d %d %d %d\n", counts[0], counts[1], counts[2], counts[3]);
    printf("%d %d %d %d\n", ucase(200), ucase(255), ucase(0), ucase(7));
    for (int a = 0; a < 3; a++)
        for (int b = 0; b < 3; b++) printf("%d ", nested(a, b));
    printf("\n");
    int state = 0, out = 0;
    for (int i = 0; i < 20; i++) {
        switch (state) {
        case 0: state = 1; out += 1; break;
        case 1: state = i % 2 ? 2 : 0; out += 2; break;
        case 2: state = 3; out *= 2; break;
        case 3: state = 0; out -= 3; break;
        }
    }
    printf("fsm %d\n", out);
    return 0;
}
