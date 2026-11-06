// ABI of narrow arguments/returns (signext/zeroext) across libc calls and
// callbacks, and through function pointers.
#include <stdio.h>
#include <ctype.h>
#include <stdlib.h>

static signed char sc_id(signed char c) { return c; }
static unsigned char uc_id(unsigned char c) { return c; }
static short s_neg(short s) { return (short)-s; }
static unsigned short us_inc(unsigned short s) { return (unsigned short)(s + 1); }
static _Bool is_neg(int v) { return v < 0; }
static int cmp_sc(const void *a, const void *b) { return *(const signed char *)a - *(const signed char *)b; }
typedef signed char (*scfn)(signed char);

int main(void) {
    signed char vals[] = {-128, -1, 0, 1, 127};
    scfn f = sc_id;
    for (int i = 0; i < 5; i++) printf("%d %d %u %d\n", sc_id(vals[i]), f(vals[i]), uc_id((unsigned char)vals[i]), s_neg(vals[i]));
    printf("%u %u %d %d\n", us_inc(65535), us_inc(7), is_neg(-4), is_neg(4));
    int t = 0;
    for (int c = 0; c < 128; c++) t += isalpha(c) ? 1 : 0, t += isdigit(c) ? 100 : 0;
    printf("ctype %d %c %c\n", t, toupper('m'), tolower('Q'));
    signed char arr[] = {5, -3, 100, -128, 0, 77, -1};
    qsort(arr, sizeof arr, 1, cmp_sc);
    for (unsigned i = 0; i < sizeof arr; i++) printf("%d ", arr[i]);
    printf("\n%d\n", atoi("-12345"));
    return 0;
}
