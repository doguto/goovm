// memcpy/memset/memmove (as LLVM intrinsics and as libc calls), struct copies,
// array zero-initialization.
#include <stdio.h>
#include <string.h>

struct Blob { int a[20]; char tail[13]; };
static struct Blob gblob = {{1, 2, 3}, "tail"};

static unsigned sum(const unsigned char *p, int n) { unsigned s = 0; for (int i = 0; i < n; i++) s = s * 31 + p[i]; return s; }

int main(void) {
    struct Blob b = gblob;            // llvm.memcpy
    b.a[19] = 99;
    struct Blob c;
    c = b;
    printf("copy %d %d %s %d\n", c.a[1], c.a[19], c.tail, gblob.a[19]);
    int zero[50] = {0};               // llvm.memset
    int part[10] = {1, 2};            // memset + stores
    printf("zero %d %d %d\n", zero[49], part[1], part[9]);
    char buf[64];
    memset(buf, 'x', sizeof buf);
    buf[63] = 0;
    printf("set %s\n", buf + 50);
    char s[32] = "0123456789abcdefghij";
    memmove(s + 2, s, 10);            // overlapping
    printf("move %s\n", s);
    memmove(s, s + 5, 10);
    printf("move %s\n", s);
    unsigned char big[1000];
    for (int i = 0; i < 1000; i++) big[i] = (unsigned char)(i * 7);
    unsigned char big2[1000];
    memcpy(big2, big, sizeof big);
    printf("big %u %d\n", sum(big2, 1000), memcmp(big, big2, 1000));
    volatile int n = 17;
    memset(big2, 0, (size_t)n);
    printf("vol %u\n", sum(big2, 40));
    struct Blob arr[3];
    memset(arr, 0, sizeof arr);
    arr[1] = gblob;
    printf("arr %d %s %d\n", arr[1].a[2], arr[1].tail, arr[2].a[0]);
    return 0;
}
