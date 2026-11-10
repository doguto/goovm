// __builtin_object_size and __builtin_dynamic_object_size: at -O1 and above
// the middle-end folds them after inlining (GIR_OBJSIZE) and the fortified
// calls whose check cannot fail become the plain functions. A size may be
// unknown at -O0 (the reference) and known once optimized, so each check
// accepts the exact size or the unknown answer (-1 for the maximum, 0 for
// the minimum), never anything else; the checked calls must still behave.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define OS(p, t) __builtin_object_size(p, t)
#define DOS(p, t) __builtin_dynamic_object_size(p, t)

static int fails;
static void check(const char *what, size_t got, size_t exact, int min) {
    size_t unk = min ? 0 : (size_t)-1;
    if (got != exact && got != unk) {
        printf("%s: %zu (expected %zu or %zu)\n", what, got, exact, unk);
        fails++;
    }
}

char gbuf[40];
static size_t of_arg(char *p) { return OS(p, 0); }
static size_t dyn_of_arg(char *p) { return DOS(p, 0); }

struct S { char a[10]; char b[10]; };

__attribute__((noinline)) static void locals(int k) {
    char buf[24];
    struct S s;
    check("local", OS(buf, 0), 24, 0);
    check("local+5", OS(buf + 5, 0), 19, 0);
    check("local min", OS(buf + 5, 2), 19, 1);
    check("past end", OS(buf + 30, 0), 0, 0);
    check("inlined arg", of_arg(buf + 4), 20, 0);
    check("global", of_arg(gbuf + 1), 39, 0);
    char *r = k ? &s.a[3] : &s.b[8];
    check("select max", OS(r, 0), 17, 0);
    check("select min", OS(r, 2), 2, 1);
    char *q = buf;
    for (int i = 0; i < 4; i++)
        if (i == k) q = &buf[10];
    check("loop", OS(q, 0), 24, 0);
    check("loop+2", OS(q + 2, 0), 22, 0);
    // a checked copy that fits and one that is checked at run time
    __builtin___memcpy_chk(buf, "0123456789", 11, OS(buf, 0));
    __builtin___strcpy_chk(buf + 11, "abc", OS(buf + 11, 0));
    printf("%s %s\n", buf, buf + 11);
    __builtin___snprintf_chk(s.a, sizeof s.a, 0, OS(s.a, 0), "%d-%s", k, "xy");
    printf("%s\n", s.a);
}

__attribute__((noinline)) static void heap(int n) {
    char *p = malloc(32);
    check("malloc", OS(p, 0), 32, 0);
    check("malloc+8", OS(p + 8, 0), 24, 0);
    int *c = calloc(6, sizeof(int));
    check("calloc", OS(c + 1, 0), 20, 0);
    char *d = malloc(n);
    check("dynamic", DOS(d + 3, 0), (size_t)n - 3, 0);
    check("dynamic inlined", dyn_of_arg(d), (size_t)n, 0);
    check("dynamic index", DOS(p + n, 0), 32 - (size_t)n, 0);
    char *v = __builtin_alloca(n);
    check("alloca", DOS(v, 0), (size_t)n, 0);
    memset(v, 'v', n);
    v[n - 1] = 0;
    printf("%zu\n", strlen(v));
    free(p);
    free(c);
    free(d);
}

int main(int argc, char **argv) {
    (void)argv;
    locals(argc - 1);
    locals(argc);
    heap(argc + 9);
    check("null", OS((char *)0, 0), 0, 0);
    printf("%s\n", fails ? "FAIL" : "ok");
    return 0;
}
