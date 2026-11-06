/* Frame-slot sharing in large functions (more than 256 GIR instructions).
 *   big():     a recursive function of ~2,000 instructions in one block; with
 *              one 8-byte slot per value its frame would be ~16 KB and 3,000
 *              levels of recursion would overflow an 8 MB stack.
 *   later():   (after mem2reg) a value defined in a block that comes after
 *              its use in layout order: the shared layout must notice and
 *              fall back to one slot per value.
 *   jumper():  setjmp in a large function: no sharing (returns_twice). */
#include <setjmp.h>
#include <stdio.h>

#define S(i) acc = acc * 31u + (v[(i) & 7] ^ (unsigned)(i)); v[((i) + 3) & 7] += acc >> 3;
#define S8(i) S(i) S(i + 1) S(i + 2) S(i + 3) S(i + 4) S(i + 5) S(i + 6) S(i + 7)
#define S64(i) S8(i) S8(i + 8) S8(i + 16) S8(i + 24) S8(i + 32) S8(i + 40) S8(i + 48) S8(i + 56)

static unsigned big(unsigned depth, unsigned seed) {
    unsigned v[8] = {seed, 1, 2, 3, 4, 5, 6, 7};
    unsigned acc = seed;
    S64(0) S64(64)
    if (depth == 0) return acc;
    return big(depth - 1, acc ^ v[depth & 7]) ^ acc;
}

static unsigned later(unsigned a, unsigned n) {
    unsigned v[8] = {a, 2, 3, 4, 5, 6, 7, 8};
    unsigned acc = a;
    unsigned x;
    S64(0)
    goto L2;
L1:
    acc += x * 3u;
    if (n-- > 0) goto L2;
    return acc ^ v[1];
L2:
    x = a + acc + n;
    goto L1;
}

static jmp_buf jb;

static __attribute__((noinline)) void bounce(unsigned x) {
    if (x & 1) longjmp(jb, (int)(x | 2));
}

static unsigned jumper(unsigned a) {
    unsigned v[8] = {a, 9, 8, 7, 6, 5, 4, 3};
    unsigned acc = a;
    S64(0)
    unsigned keep = acc ^ 0x5a5a5a5au;
    int r = setjmp(jb);
    if (r == 0) {
        bounce(acc | 1);
        return 0;
    }
    return keep + (unsigned)r + v[2];
}

int main(void) {
    printf("big %u\n", big(3000, 7));
    printf("later %u %u\n", later(5, 3), later(11, 0));
    printf("jumper %u\n", jumper(123));
    return 0;
}
