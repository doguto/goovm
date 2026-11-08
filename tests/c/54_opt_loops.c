/* Shapes for loop rotation, tail recursion elimination and if-conversion
 * (milestone E1): loops that run zero, one or many times, header values used
 * after the loop, nested and sequential loops, early exits, recursion in
 * tail position with and without an accumulator, conditional updates. */
#include <stdio.h>
#include <string.h>

static unsigned fib(unsigned n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); }
static long sum_to(long n, long acc) { return n == 0 ? acc : sum_to(n - 1, acc + n); }
static int gcd(int a, int b) { return b == 0 ? a : gcd(b, a % b); }
static long tri(long n) { if (n <= 0) return 0; return n + tri(n - 1); }
static void count_down(int n, int *out) { if (n <= 0) return; (*out)++; count_down(n - 1, out); }
static int ack(int m, int n) {
    if (m == 0) return n + 1;
    if (n == 0) return ack(m - 1, 1);
    return ack(m - 1, ack(m, n - 1));
}
struct node { int v; struct node *next; };
static int list_sum(struct node *p, int acc) { return p ? list_sum(p->next, acc + p->v) : acc; }
static int list_len(struct node *p) { return p ? 1 + list_len(p->next) : 0; }

/* the header's values after the loop */
__attribute__((noinline)) static int find(const int *a, int n, int x) {
    int i = 0;
    while (i < n && a[i] != x) i++;
    return i;
}
__attribute__((noinline)) static unsigned scan(const char *s, char c) {
    unsigned k = 0;
    for (; s[k] && s[k] != c; k++) {}
    return k * 3 + (s[k] == c);
}
__attribute__((noinline)) static long nested(int n, int m) {
    long t = 0;
    for (int i = 0; i < n; i++)
        for (int j = i; j < m; j++)
            t += (i ^ j) & 7;
    return t;
}
__attribute__((noinline)) static int seq(int n) {
    int i = 0, j = 0;
    while (i < n) i += 3;
    while (j < i) j += 2;
    return i * 100 + j;
}
__attribute__((noinline)) static int count_if(const int *a, int n, int lim) {
    int c = 0, s = 0;
    for (int i = 0; i < n; i++) {
        if (a[i] > lim) c++;
        s = a[i] < s ? a[i] : s;
    }
    return c * 1000 + s;
}
__attribute__((noinline)) static int dowhile(int n) {
    int k = 0;
    do { k += n; n--; } while (n > 0);
    return k;
}
__attribute__((noinline)) static int brk(const int *a, int n) {
    int i;
    for (i = 0; i < n; i++)
        if (a[i] < 0) break;
    return i;
}

int main(void) {
    int a[10] = {4, 8, -1, 7, 9, 2, 6, 3, 5, 1};
    struct node n3 = {3, 0}, n2 = {20, &n3}, n1 = {100, &n2};
    int cnt = 0;
    printf("fib %u %u %u\n", fib(0), fib(1), fib(25));
    printf("sum %ld %ld\n", sum_to(0, 5), sum_to(50000, 0));
    printf("gcd %d %d\n", gcd(1071, 462), gcd(17, 0));
    printf("tri %ld %ld\n", tri(0), tri(30000));
    count_down(1000, &cnt);
    printf("count %d\n", cnt);
    printf("ack %d %d\n", ack(2, 3), ack(3, 3));
    printf("list %d %d %d\n", list_sum(&n1, 0), list_len(&n1), list_len(0));
    printf("find %d %d %d %d\n", find(a, 10, 9), find(a, 10, 42), find(a, 0, 4), find(a, 1, 4));
    printf("scan %u %u %u\n", scan("hello", 'l'), scan("hello", 'z'), scan("", 'a'));
    printf("nested %ld %ld %ld\n", nested(0, 5), nested(5, 0), nested(30, 40));
    printf("seq %d %d %d\n", seq(0), seq(1), seq(10));
    printf("count_if %d %d\n", count_if(a, 10, 4), count_if(a, 0, 4));
    printf("dowhile %d %d\n", dowhile(0), dowhile(5));
    printf("brk %d %d %d\n", brk(a, 10), brk(a, 2), brk(a + 3, 7));
    return 0;
}
