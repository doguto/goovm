// Pointer arithmetic, differences, pointer-to-pointer, intptr casts.
#include <stdio.h>
#include <stdint.h>
#include <stddef.h>

static void swap(int **a, int **b) { int *t = *a; *a = *b; *b = t; }
static int sum_range(const int *b, const int *e) { int s = 0; while (b != e) s += *b++; return s; }

int main(void) {
    int a[10];
    for (int i = 0; i < 10; i++) a[i] = i * i;
    int *p = a, *q = a + 9;
    printf("diff %td %td\n", q - p, p - q);
    printf("sum %d %d\n", sum_range(a, a + 10), sum_range(a + 3, a + 6));
    swap(&p, &q);
    printf("swapped %d %d\n", *p, *q);
    long l[4] = {10, 20, 30, 40};
    long *lp = &l[3];
    lp -= 2;
    printf("long %ld %ld\n", *lp, lp[1]);
    char buf[32];
    char *c = buf;
    for (int i = 0; i < 26; i++) *c++ = 'A' + i;
    *c = 0;
    printf("buf %s %td\n", buf + 20, c - buf);
    uintptr_t u = (uintptr_t)&a[5];
    int *back = (int *)(u - 2 * sizeof(int));
    printf("intptr %d %d\n", *back, (int)((u - (uintptr_t)a) / sizeof(int)));
    int **pp = &p;
    **pp = 1234;
    printf("pp %d %d\n", a[9], **pp);
    struct S { char c; int i; double d; } s;
    printf("offsets %zu %zu\n", offsetof(struct S, i), offsetof(struct S, d));
    char *cp = (char *)&s.i;
    printf("cp %td\n", cp - (char *)&s);
    void *vp = a;
    printf("vp %d\n", ((int *)vp)[4]);
    int neg = -3;
    printf("negidx %d\n", (a + 5)[neg]);
    short sh[6] = {1, 2, 3, 4, 5, 6};
    unsigned short ui = 4;
    printf("short %d\n", sh[ui] + *(sh + (ui - 3)));
    return 0;
}
