// Integer-only kernels for comparing the code quality of -O0 back-ends.
// Everything stays inside goovm's subset (no floating point, no varargs
// definitions, no VLAs). usage: kernels [scale]; prints a checksum per kernel.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint32_t rng_state = 2463534242u;
static uint32_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 17;
    rng_state ^= rng_state << 5;
    return rng_state;
}

static uint64_t sieve(int n) {
    uint8_t *composite = calloc((size_t)n + 1, 1);
    uint64_t sum = 0;
    for (int i = 2; i <= n; i++) {
        if (composite[i]) continue;
        sum += (uint64_t)i;
        for (int64_t j = (int64_t)i * i; j <= n; j += i) composite[j] = 1;
    }
    free(composite);
    return sum;
}

static void quicksort(int32_t *a, int lo, int hi) {
    while (lo < hi) {
        int32_t pivot = a[lo + (hi - lo) / 2];
        int i = lo, j = hi;
        while (i <= j) {
            while (a[i] < pivot) i++;
            while (a[j] > pivot) j--;
            if (i <= j) { int32_t t = a[i]; a[i] = a[j]; a[j] = t; i++; j--; }
        }
        if (j - lo < hi - i) { quicksort(a, lo, j); lo = i; }
        else { quicksort(a, i, hi); hi = j; }
    }
}

static uint64_t sort_kernel(int n) {
    int32_t *a = malloc(sizeof(int32_t) * (size_t)n);
    for (int i = 0; i < n; i++) a[i] = (int32_t)(rnd() % 1000000007u);
    quicksort(a, 0, n - 1);
    uint64_t h = 0;
    for (int i = 0; i < n; i += 97) h = h * 31 + (uint32_t)a[i];
    free(a);
    return h;
}

struct entry { uint64_t key; uint64_t value; };

static uint64_t hash_kernel(int n) {
    int cap = 1;
    while (cap < 2 * n) cap <<= 1;
    struct entry *t = calloc((size_t)cap, sizeof(struct entry));
    uint64_t found = 0;
    for (int i = 0; i < n; i++) {
        uint64_t k = ((uint64_t)rnd() << 32 | rnd()) | 1;
        uint64_t h = (k * 0x9E3779B97F4A7C15ull) >> 20;
        for (;;) {
            struct entry *e = &t[h & (uint64_t)(cap - 1)];
            if (e->key == 0) { e->key = k; e->value = (uint64_t)i; break; }
            if (e->key == k) { e->value += 1; break; }
            h++;
        }
    }
    rng_state = 2463534242u;
    for (int i = 0; i < n; i++) {
        uint64_t k = ((uint64_t)rnd() << 32 | rnd()) | 1;
        uint64_t h = (k * 0x9E3779B97F4A7C15ull) >> 20;
        for (;;) {
            struct entry *e = &t[h & (uint64_t)(cap - 1)];
            if (e->key == k) { found += e->value; break; }
            if (e->key == 0) break;
            h++;
        }
    }
    free(t);
    return found;
}

static uint64_t matmul_kernel(int n) {
    int32_t *a = malloc(sizeof(int32_t) * (size_t)(n * n));
    int32_t *b = malloc(sizeof(int32_t) * (size_t)(n * n));
    int64_t *c = calloc((size_t)(n * n), sizeof(int64_t));
    for (int i = 0; i < n * n; i++) { a[i] = (int32_t)(rnd() % 100); b[i] = (int32_t)(rnd() % 100); }
    for (int i = 0; i < n; i++)
        for (int k = 0; k < n; k++) {
            int64_t aik = a[i * n + k];
            for (int j = 0; j < n; j++) c[i * n + j] += aik * b[k * n + j];
        }
    uint64_t h = 0;
    for (int i = 0; i < n * n; i += 13) h = h * 131 + (uint64_t)c[i];
    free(a); free(b); free(c);
    return h;
}

static uint64_t string_kernel(int n) {
    char *buf = malloc((size_t)n + 1);
    for (int i = 0; i < n; i++) buf[i] = (char)('a' + rnd() % 4);
    buf[n] = 0;
    // count occurrences of a few patterns with a naive search
    const char *pats[4] = {"abca", "dd", "cab", "bbbb"};
    uint64_t total = 0;
    for (int p = 0; p < 4; p++) {
        size_t m = strlen(pats[p]);
        for (int i = 0; i + (int)m <= n; i++) {
            size_t k = 0;
            while (k < m && buf[i + (int)k] == pats[p][k]) k++;
            if (k == m) total += (uint64_t)(p + 1);
        }
    }
    free(buf);
    return total;
}

static uint32_t fib(uint32_t n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); }

int main(int argc, char **argv) {
    int scale = argc > 1 ? atoi(argv[1]) : 1;
    printf("sieve  %llu\n", (unsigned long long)sieve(4000000 * scale));
    printf("sort   %llu\n", (unsigned long long)sort_kernel(1000000 * scale));
    printf("hash   %llu\n", (unsigned long long)hash_kernel(500000 * scale));
    printf("matmul %llu\n", (unsigned long long)matmul_kernel(160 * scale));
    printf("string %llu\n", (unsigned long long)string_kernel(4000000 * scale));
    printf("fib    %u\n", fib(27 + scale));
    return 0;
}
