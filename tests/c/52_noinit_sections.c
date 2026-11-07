// __attribute__((noinit)) and named sections on tentative definitions (G1).
// clang-20 for x86-64 does not know noinit (-Wunknown-attributes) and ignores
// it: such a variable is an ordinary zero-initialized object. A variable with
// a named section and no initializer is zeros in that section (goosecc did
// not compile it before G1), also when the section's name is the unit's
// first string literal (it was dropped then). The linker defines
// __start_/__stop_ symbols around a section whose name is an identifier.
int printf(const char *, ...);   // no header: "g1sec" is the first string

int __attribute__((section("g1sec"), noinit)) s1;
int __attribute__((noinit, section("g1sec"))) s2;
int __attribute__((section("g1sec"))) s3 = 7;
long __attribute__((section("g1sec"))) s4[3];
int __attribute__((noinit)) n1;
static int __attribute__((noinit)) n2;
struct P { int a[3]; char c; } __attribute__((noinit)) n3;
int __attribute__((noinit)) func(void);   // on a function: ignored as well
int __attribute__((section("g1text"))) in_text(int x) { return x + 1; }

extern char __start_g1sec[], __stop_g1sec[];
static int in_sec(void *p) { return (char *)p >= __start_g1sec && (char *)p < __stop_g1sec; }

int main(void) {
    static long n4 __attribute__((noinit));
    printf("in g1sec: %d %d %d %d %d\n", in_sec(&s1), in_sec(&s2), in_sec(&s3), in_sec(s4), in_sec(&n1));
    printf("values: %d %d %d %ld %d %ld\n", s1, s2, s3, s4[0] + s4[1] + s4[2], n1 + n2 + n3.a[2] + n3.c, n4);
    n1 = 5;
    n2 = 6;
    n4 = 7;
    s1 = 8;
    s4[2] = 9;
    printf("after: %d %d %ld %d %ld %d\n", n1, n2, n4, s1, s4[2], in_text(41));
    return 0;
}
