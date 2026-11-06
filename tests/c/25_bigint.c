// Arbitrary precision arithmetic with 32-bit limbs: factorials and powers.
#include <stdio.h>
#include <stdint.h>
#include <string.h>

#define LIMBS 64
typedef struct { uint32_t d[LIMBS]; int n; } Big;

static void set(Big *a, uint32_t v) { memset(a, 0, sizeof *a); a->d[0] = v; a->n = 1; }
static void mul_small(Big *a, uint32_t m) {
    uint64_t carry = 0;
    for (int i = 0; i < a->n; i++) {
        uint64_t t = (uint64_t)a->d[i] * m + carry;
        a->d[i] = (uint32_t)t;
        carry = t >> 32;
    }
    if (carry) a->d[a->n++] = (uint32_t)carry;
}
static void add(Big *r, const Big *a, const Big *b) {
    uint64_t c = 0;
    int n = a->n > b->n ? a->n : b->n;
    for (int i = 0; i < n; i++) {
        uint64_t t = (uint64_t)(i < a->n ? a->d[i] : 0) + (i < b->n ? b->d[i] : 0) + c;
        r->d[i] = (uint32_t)t;
        c = t >> 32;
    }
    r->n = n;
    if (c) r->d[r->n++] = (uint32_t)c;
}
static uint32_t div_small(Big *a, uint32_t m) {
    uint64_t rem = 0;
    for (int i = a->n - 1; i >= 0; i--) {
        uint64_t cur = (rem << 32) | a->d[i];
        a->d[i] = (uint32_t)(cur / m);
        rem = cur % m;
    }
    while (a->n > 1 && !a->d[a->n - 1]) a->n--;
    return (uint32_t)rem;
}
static void print(const Big *a) {
    Big t = *a;
    char buf[700];
    int k = 0;
    do { buf[k++] = (char)('0' + div_small(&t, 10)); } while (t.n > 1 || t.d[0]);
    while (k) putchar(buf[--k]);
    putchar('\n');
}

int main(void) {
    Big f;
    set(&f, 1);
    for (uint32_t i = 2; i <= 60; i++) mul_small(&f, i);
    print(&f);
    Big a, b, c;
    set(&a, 0);
    set(&b, 1);
    for (int i = 0; i < 200; i++) { add(&c, &a, &b); a = b; b = c; }
    print(&b);
    Big p;
    set(&p, 1);
    for (int i = 0; i < 100; i++) mul_small(&p, 3);
    print(&p);
    return 0;
}
