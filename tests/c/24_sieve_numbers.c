// Number theory: sieve, gcd/lcm, modular exponentiation, digit sums.
#include <stdio.h>
#include <stdint.h>

static char composite[10001];
static uint64_t powmod(uint64_t b, uint64_t e, uint64_t m) {
    uint64_t r = 1;
    b %= m;
    while (e) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return r;
}
static long gcd(long a, long b) { while (b) { long t = a % b; a = b; b = t; } return a < 0 ? -a : a; }
static int digitsum(unsigned long long n) { int s = 0; while (n) { s += n % 10; n /= 10; } return s; }
static int isqrt(int n) { int r = 0; while ((r + 1) * (r + 1) <= n) r++; return r; }

int main(void) {
    int count = 0, last = 0;
    for (int i = 2; i <= 10000; i++) {
        if (composite[i]) continue;
        count++;
        last = i;
        for (int j = i * 2; j <= 10000; j += i) composite[j] = 1;
    }
    printf("primes %d last %d\n", count, last);
    printf("powmod %llu %llu\n", (unsigned long long)powmod(2, 1000, 1000000007),
           (unsigned long long)powmod(12345, 6789, 99991));
    long l = 1;
    for (int i = 1; i <= 20; i++) l = l / gcd(l, i) * i;
    printf("lcm %ld gcd %ld\n", l, gcd(-84, 36));
    printf("digits %d %d\n", digitsum(18446744073709551615ull), digitsum(1234567890));
    printf("isqrt %d %d %d\n", isqrt(99), isqrt(100), isqrt(1000000));
    int perfect = 0;
    for (int n = 2; n < 10000; n++) {
        int s = 1;
        for (int d = 2; d * d <= n; d++) if (n % d == 0) { s += d; if (d * d != n) s += n / d; }
        if (s == n) printf("perfect %d\n", n), perfect++;
    }
    return perfect;
}
