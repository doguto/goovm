// Member pointers (Itanium 2.3): data members (offsets, null -1),
// member functions ({ptr, adj}, virtual ones by vtable offset + 1),
// conversions base -> derived (implicit) and back (static_cast and
// functional casts), null conversions and comparisons, calls through them
// on objects, pointers and temporaries, arrays of them, class results.
#include <stdio.h>

struct A { int a = 1; int f() { return a * 10; } virtual int v() { return 100 + a; } virtual ~A() {} };
struct B { int b = 2; int g() { return b * 10; } virtual int w() { return 200 + b; } virtual ~B() {} };
struct C : A, B { int c = 3; int arr[3] = {7, 8, 9}; int h() { return c * 10; } int w() override { return 300 + c; } };

struct P { int x, y; };
struct Q { P p; P make(int k) { return P{p.x + k, p.y + k}; } };

typedef int (A::*AF)();
typedef int (B::*BF)();
typedef int (C::*CF)();

int call(C *p, CF f) { return (p->*f)(); }
CF pick(int i) {
    static const CF tab[] = { &C::h, &A::f, &B::g, &B::w, &A::v };
    return tab[i];
}
int B::*bmember() { return &B::b; }

int main() {
    C c;
    int C::*pd = &C::c;
    int B::*pb = &B::b;
    int C::*pd2 = pb;
    printf("data %d %d %d %d\n", c.*pd, c.*pb, c.*pd2, c.*bmember());
    int C::*nd = 0;
    int C::*nd2 = (int B::*)0;
    int C::*nd3 = nullptr;
    printf("null %d %d %d %d %d\n", nd == 0, nd2 == nullptr, pd != 0, nd3 == nd, pd2 == pd);
    int B::*back = static_cast<int B::*>(pd2);
    B *bp = &c;
    printf("back %d %d\n", bp->*back, back == pb);
    int (C::*pa)[3] = &C::arr;
    printf("arr %d\n", (c.*pa)[2]);
    c.*pd = 33;
    C *pc = &c;
    pc->*pd += 1;
    printf("assign %d\n", c.c);

    CF f1 = &C::h;
    CF f2 = &A::f;
    CF f3 = &B::g;
    CF f4 = &B::w;
    CF f5 = &A::v;
    printf("fn %d %d %d %d %d\n", call(&c, f1), call(&c, f2), call(&c, f3), call(&c, f4), call(&c, f5));
    for (int i = 0; i < 5; i++) printf(" %d", (c.*pick(i))());
    printf("\n");
    BF b1 = static_cast<BF>(f3);
    BF b2 = BF(f4);
    printf("down %d %d\n", (bp->*b1)(), (bp->*b2)());
    CF fn = 0;
    printf("cmp %d %d %d %d %d\n", f1 == f1, f1 != f2, fn == 0, f3 == CF(&B::g), f4 != f5);
    if (f4) printf("truthy\n");
    if (!fn) printf("null fn\n");
    printf("tmp %d\n", (C().*f1)());
    P (Q::*mk)(int) = &Q::make;
    Q q;
    q.p = P{1, 2};
    P r = (q.*mk)(10);
    printf("class result %d %d\n", r.x, r.y);
    return 0;
}
