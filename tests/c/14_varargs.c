// printf varargs with mixed argument types, many arguments, stack-passed.
#include <stdio.h>
#include <stdint.h>
#include <stddef.h>

int main(void) {
    char c = 'q';
    signed char sc = -5;
    unsigned char uc = 250;
    short s = -1234;
    unsigned short us = 54321;
    int i = -123456;
    unsigned u = 3000000000u;
    long l = -9000000000L;
    unsigned long ul = 18000000000000000000ul;
    const char *str = "str";
    printf("%c %d %u %d %u\n", c, sc, uc, s, us);
    printf("%d %u %ld %lu %s\n", i, u, l, ul, str);
    printf("%d %d %d %d %d %d %d %d %d %d %d %d\n", 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);
    printf("%s %s %s %s %s %s %s %s\n", "a", "b", "c", "d", "e", "f", "g", "h");
    printf("%x %X %o %#x %08d %-5d| %+d\n", 255, 0xABCDEF, 8, 16, 42, 7, 9);
    printf("%lld %llu %hd %hhu %zu %td\n", (long long)INT64_MIN, (unsigned long long)UINT64_MAX, (short)70000,
           (unsigned char)300, sizeof(long), (ptrdiff_t)-3);
    printf("%c%c%c%c%c%c%c%c%c\n", 'v', 'a', 'r', 'a', 'r', 'g', 's', '!', '!');
    int total = 0;
    for (int k = 0; k < 5; k++) total += printf("[%d:%s]", k, k % 2 ? "odd" : "even");
    printf("\nprinted %d\n", total);
    char buf[100];
    int n = snprintf(buf, sizeof buf, "%d,%ld,%s,%c,%u,%lu,%x", -1, 2L, "three", '4', 5u, 6ul, 7);
    printf("%s (%d)\n", buf, n);
    fprintf(stdout, "to stdout %d\n", 77);
    puts("puts done");
    return 0;
}
