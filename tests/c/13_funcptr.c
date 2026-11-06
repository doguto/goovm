// Function pointers: tables, callbacks (qsort, bsearch), returning pointers.
#include <stdio.h>
#include <stdlib.h>

typedef int (*binop)(int, int);
static int add(int a, int b) { return a + b; }
static int sub(int a, int b) { return a - b; }
static int mul(int a, int b) { return a * b; }
static int maxi(int a, int b) { return a > b ? a : b; }
static binop table[] = {add, sub, mul, maxi};
static binop pick(int i) { return table[i & 3]; }
static int fold(binop f, const int *a, int n, int init) {
    for (int i = 0; i < n; i++) init = f(init, a[i]);
    return init;
}
static int cmp_int(const void *a, const void *b) {
    int x = *(const int *)a, y = *(const int *)b;
    return (x > y) - (x < y);
}
static int cmp_desc(const void *a, const void *b) { return -cmp_int(a, b); }
struct Handler { const char *name; void (*fn)(int *, int); };
static void h_inc(int *s, int v) { *s += v; }
static void h_neg(int *s, int v) { *s = -*s + v; }
static void h_sq(int *s, int v) { *s = *s * *s % 1000 + v; }

int main(void) {
    int a[] = {5, -3, 12, 7, 0, 9, -8, 4};
    for (int i = 0; i < 4; i++) printf("fold%d %d\n", i, fold(table[i], a, 8, 1));
    printf("pick %d %d\n", pick(6)(7, 8), (*pick(1))(7, 8));
    qsort(a, 8, sizeof(int), cmp_int);
    for (int i = 0; i < 8; i++) printf("%d ", a[i]);
    printf("\n");
    int key = 7;
    int *hit = bsearch(&key, a, 8, sizeof(int), cmp_int);
    printf("bsearch %td\n", hit ? hit - a : -1);
    qsort(a, 8, sizeof(int), cmp_desc);
    for (int i = 0; i < 8; i++) printf("%d ", a[i]);
    printf("\n");
    struct Handler hs[] = {{"inc", h_inc}, {"neg", h_neg}, {"sq", h_sq}};
    int state = 3;
    for (int r = 0; r < 10; r++) {
        struct Handler *h = &hs[r % 3];
        h->fn(&state, r);
        printf("%s=%d ", h->name, state);
    }
    printf("\n");
    int (*fp)(const void *, const void *) = cmp_int;
    int x = 1, y = 2;
    printf("cmp %d %d\n", fp(&x, &y), fp(&y, &x));
    return 0;
}
