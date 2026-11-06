// Global initializers: ints, arrays, structs, strings, pointers to globals and
// functions, pointer arithmetic, const tables, zero-init, static locals.
#include <stdio.h>

int gi = 42;
long gl = -1234567890123LL;
short gsh = -7;
unsigned char guc = 200;
_Bool gb = 1;
int gzero;
int garr[5] = {1, 2, 3};
const int ctab[4] = {100, 200, 300, 400};
char gstr[] = "global string";
const char *gptr = "pointer string";
const char *gptr_off = "offset string" + 7;
int *pint = &garr[2];
int **ppint = &pint;
struct S { int a; char b; long c; const char *d; int *e; } gs = {1, 'x', 3, "four", &gi};
struct S gsa[2] = {{10, 'y', 30, "forty", garr + 4}, {0}};
static int counter(void) { static int n = 100; return n++; }
static int add1(int x) { return x + 1; }
static int dbl(int x) { return x * 2; }
int (*fptr)(int) = add1;
int (*ftab[3])(int) = {add1, dbl, add1};
struct Op { const char *name; int (*f)(int); } ops[] = {{"inc", add1}, {"dbl", dbl}};
const char *const names[] = {"a", "bb", "ccc"};
char *strs[2] = {gstr, gstr + 7};
long long big_init[3] = {0x7FFFFFFFFFFFFFFFLL, -1, 0x100000000LL};
unsigned short us_arr[4] = {65535, 1, 32768, 0};
struct Nested { struct { int x, y; } in[2]; char tag[4]; } nest = {{{1, 2}, {3, 4}}, "abc"};
static int sarr[100];
int *end_ptr = &garr[5];
long addr_diff_check = 5;

int main(void) {
    printf("%d %ld %d %u %d %d\n", gi, gl, gsh, guc, gb, gzero);
    printf("%d %d %d %d %d\n", garr[0], garr[1], garr[2], garr[3], garr[4]);
    printf("%d %s %s %s\n", ctab[3], gstr, gptr, gptr_off);
    printf("%d %d\n", *pint, **ppint);
    printf("%d %c %ld %s %d\n", gs.a, gs.b, gs.c, gs.d, *gs.e);
    printf("%d %s %d %d\n", gsa[0].a, gsa[0].d, gsa[0].e == &garr[4], gsa[1].a);
    printf("%d %d %d\n", counter(), counter(), counter());
    printf("%d %d %d %d\n", fptr(1), ftab[0](10), ftab[1](10), ftab[2](10));
    for (int i = 0; i < 2; i++) printf("%s:%d ", ops[i].name, ops[i].f(21));
    printf("\n%s %s %s %s %s\n", names[0], names[1], names[2], strs[0], strs[1]);
    printf("%lld %lld %lld\n", big_init[0], big_init[1], big_init[2]);
    printf("%u %u %u %u\n", us_arr[0], us_arr[1], us_arr[2], us_arr[3]);
    printf("%d %d %s\n", nest.in[1].x, nest.in[0].y, nest.tag);
    for (int i = 0; i < 100; i++) sarr[i] += i;
    printf("%d %d %td\n", sarr[99], sarr[0], end_ptr - garr);
    gi++; gzero += 5;
    fptr = dbl;
    printf("%d %d %d\n", gi, gzero, fptr(gi));
    return 0;
}
