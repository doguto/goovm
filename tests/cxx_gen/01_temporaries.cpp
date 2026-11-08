// Temporaries: destruction at the end of the full-expression, lifetime
// extension, conditional temporaries, classes passed and returned by
// invisible reference, copy elision, NRVO, implicit copy/move members.
#include <stdio.h>
#include <string.h>

static int live = 0;

struct S {
    int v;
    S(int x) : v(x) { live++; printf("S(%d)\n", v); }
    S(const S &o) : v(o.v + 100) { live++; printf("S(copy %d)\n", o.v); }
    S(S &&o) : v(o.v + 1000) { live++; printf("S(move %d)\n", o.v); o.v = -1; }
    ~S() { live--; printf("~S(%d)\n", v); }
    S &operator=(const S &o) { printf("S= %d <- %d\n", v, o.v); v = o.v; return *this; }
    int get() const { return v; }
};

struct Wrap {
    S a;
    S b;
    Wrap(int x) : a(x), b(x + 1) {}
};

S make(int x) { return S(x); }
S make_named(int x) {
    S s(x);
    s.v += 5;
    return s;
}
S pick(bool c) {
    S a(1), b(2);
    if (c) return a;
    return b;
}
int take(S s) { return s.get(); }
int take_ref(const S &s) { return s.get(); }

struct Plain { int a, b; ~Plain() { printf("~Plain(%d)\n", a); } };
Plain mkp(int a) { Plain p; p.a = a; p.b = 2 * a; return p; }

int main() {
    printf("-- 1\n");
    { int r = take(S(1)); printf("r=%d\n", r); }
    printf("-- 2\n");
    { int r = take_ref(S(2)) + take_ref(make(3)); printf("r=%d\n", r); }
    printf("-- 3\n");
    { S x = make(4); printf("x=%d\n", x.get()); }
    printf("-- 4\n");
    { S y = make_named(5); printf("y=%d\n", y.get()); }
    printf("-- 5\n");
    { const S &e = make(6); printf("e=%d\n", e.get()); printf("end of scope\n"); }
    printf("-- 6\n");
    { int c = 1; int r = c ? take_ref(S(7)) : take_ref(S(8)); printf("r=%d\n", r); }
    printf("-- 7\n");
    { S z(9); S w = z; printf("w=%d\n", w.get()); S m = static_cast<S &&>(z); printf("m=%d z=%d\n", m.get(), z.get()); }
    printf("-- 8\n");
    { S p = pick(true); S q = pick(false); printf("p=%d q=%d\n", p.get(), q.get()); }
    printf("-- 9\n");
    { Wrap w(20); Wrap w2 = w; printf("w2=%d,%d\n", w2.a.get(), w2.b.get()); }
    printf("-- 10\n");
    { S a(30); a = S(31); a = make(32); printf("a=%d\n", a.get()); }
    printf("-- 11\n");
    { printf("get=%d\n", make(40).get()); }
    printf("-- 12\n");
    { Plain p = mkp(50); printf("p=%d %d\n", p.a, p.b); }
    printf("-- 13\n");
    { make(60); S(61); printf("after\n"); }
    printf("live=%d\n", live);
    return 0;
}
