/* Driver of geps.ll. */
#include <stdio.h>

void fill(int *p, int n) {
    for (int i = 0; i < n; i++) p[i] = i * i - 3;
}
long sum_ints(int *p, int n) {
    long s = 0;
    for (int i = 0; i < n; i++) s += p[i] * (i + 1);
    return s;
}
long g_chain(long);
long g_negative(void);
long g_blocks(int);
long g_overaligned(long);
long g_dynamic(int);

int main(void) {
    printf("chain %ld %ld\n", g_chain(123456789), g_chain(-5));
    printf("negative %ld\n", g_negative());
    printf("blocks %ld %ld\n", g_blocks(1), g_blocks(0));
    printf("overaligned %ld\n", g_overaligned(11));
    printf("dynamic %ld\n", g_dynamic(37));
    return 0;
}
