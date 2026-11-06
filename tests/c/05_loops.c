// for/while/do-while, break/continue, nested loops, goto.
#include <stdio.h>

int main(void) {
    int sum = 0;
    for (int i = 0; i < 100; i++) {
        if (i % 3 == 0) continue;
        if (i > 90) break;
        sum += i;
    }
    printf("for %d\n", sum);
    int n = 27, steps = 0;
    while (n != 1) { n = n % 2 ? 3 * n + 1 : n / 2; steps++; }
    printf("collatz %d\n", steps);
    int k = 0;
    do { k += 7; } while (k < 100);
    printf("do %d\n", k);
    long tri = 0;
    for (int i = 0; i < 50; i++)
        for (int j = 0; j <= i; j++)
            for (int m = j; m < i; m += 5) tri += (i ^ j) + m;
    printf("nested %ld\n", tri);
    int g = 0, cnt = 0;
again:
    g += 3;
    cnt++;
    if (g < 50) goto again;
    printf("goto %d %d\n", g, cnt);
    unsigned u = 10;
    int down = 0;
    while (u--) down += u;
    printf("down %d %u\n", down, u);
    int found = -1;
    for (int i = 2; i < 1000 && found < 0; i++) {
        int ok = 1;
        for (int d = 2; d * d <= i; d++)
            if (i % d == 0) { ok = 0; break; }
        if (ok && i > 500) found = i;
    }
    printf("prime %d\n", found);
    return 0;
}
