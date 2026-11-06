// Recursion: fib, ackermann, mutual recursion, hanoi, permutations.
#include <stdio.h>

static int fib(int n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); }
static int ack(int m, int n) {
    if (m == 0) return n + 1;
    if (n == 0) return ack(m - 1, 1);
    return ack(m - 1, ack(m, n - 1));
}
static int is_odd(unsigned n);
static int is_even(unsigned n) { return n == 0 ? 1 : is_odd(n - 1); }
static int is_odd(unsigned n) { return n == 0 ? 0 : is_even(n - 1); }
static long moves;
static void hanoi(int n, int from, int to, int via) {
    if (!n) return;
    hanoi(n - 1, from, via, to);
    moves += from * 3 + to;
    hanoi(n - 1, via, to, from);
}
static int perm_count;
static void permute(char *s, int l, int r) {
    if (l == r) { if (perm_count++ < 6) printf("%s\n", s); return; }
    for (int i = l; i <= r; i++) {
        char t = s[l]; s[l] = s[i]; s[i] = t;
        permute(s, l + 1, r);
        t = s[l]; s[l] = s[i]; s[i] = t;
    }
}
static unsigned long long fact(unsigned n) { return n ? n * fact(n - 1) : 1; }
static int gcd(int a, int b) { return b ? gcd(b, a % b) : a; }

int main(void) {
    printf("fib %d %d\n", fib(20), fib(25));
    printf("ack %d %d\n", ack(2, 3), ack(3, 4));
    printf("parity %d %d\n", is_even(1000), is_odd(777));
    hanoi(12, 1, 3, 2);
    printf("hanoi %ld\n", moves);
    char s[] = "abcd";
    permute(s, 0, 3);
    printf("perms %d\n", perm_count);
    printf("fact %llu\n", fact(20));
    printf("gcd %d %d\n", gcd(1071, 462), gcd(-48, 18));
    return 0;
}
