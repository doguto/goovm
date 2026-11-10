// Casts between classes (static_cast and C-style casts up and down,
// through non-virtual and virtual bases, pointers and references, null
// pointers kept) and RTTI: typeid of types, of non-polymorphic and
// polymorphic glvalues (bad_typeid on a null *p), dynamic_cast down, across,
// to void * and to references (bad_cast), with the offset hints.
#include <stdio.h>
#include <typeinfo>

struct M1 { int a = 1; };
struct M2 { int b = 2; };
struct MM : M1, M2 { int c = 3; };

struct V { int v = 9; virtual ~V() {} };
struct W : virtual V { int w = 8; };
struct U : W { int u = 7; };

struct Base { virtual ~Base() {} int x = 1; };
struct Left : Base { int l = 2; };
struct Right { virtual void r() {} int rr = 3; };
struct Both : Left, Right { int b = 4; };
struct Priv : private Base { Base *self() { return this; } };
struct Other : Base { };
struct Twice1 : Base { };
struct Twice2 : Base { };
struct Twice : Twice1, Twice2 { };

struct NP { int n; };

int main() {
    MM m;
    M2 *p = (M2 *)&m;
    M2 *q = static_cast<M2 *>(&m);
    MM *back = static_cast<MM *>(q);
    MM *back2 = (MM *)p;
    M2 *z = 0;
    MM *zb = static_cast<MM *>(z);
    M2 &r = m;
    MM &rb = static_cast<MM &>(r);
    MM &rc = (MM &)r;
    const M2 *cq = (const M2 *)&m;
    printf("casts %d %d %d %d %d %d %d %d\n", p->b, q->b, back->c, back2->c, zb == 0, rb.c, rc.a, cq->b);
    printf("offsets %d %d\n", (int)((char *)q - (char *)&m), (int)((char *)back - (char *)&m));

    U u;
    V *pv = (V *)&u;
    W *pw = &u;
    V *pv2 = pw;
    const V *cpv = static_cast<const V *>(&u);
    V &rv = u;
    W *nw = 0;
    V *nv = nw;
    printf("vbase %d %d %d %d %d %d\n", pv->v, pv2->v, cpv->v, rv.v, (int)((char *)pv - (char *)&u), nv == 0);

    // typeid
    printf("typeid %s %s %s %d\n", typeid(int).name(), typeid(MM).name(), typeid(m).name(), typeid(m) == typeid(MM));
    Both both;
    Base *bp = &both;
    Right *rp = &both;
    printf("dyn type %s %s %d %d\n", typeid(*bp).name(), typeid(*rp).name(), typeid(*bp) == typeid(Both), typeid(bp) == typeid(Base *));
    NP np = {5};
    printf("static %s %s\n", typeid(np).name(), typeid(const NP &).name());
    try {
        Base *nb = 0;
        printf("%s\n", typeid(*nb).name());
    } catch (std::bad_typeid &e) {
        printf("bad_typeid\n");
    }

    // dynamic_cast
    Left *lp = dynamic_cast<Left *>(bp);
    Both *bo = dynamic_cast<Both *>(rp);
    Right *cross = dynamic_cast<Right *>(bp);
    Other *no = dynamic_cast<Other *>(bp);
    void *mostd = dynamic_cast<void *>(rp);
    const void *cmost = dynamic_cast<const void *>(static_cast<const Right *>(rp));
    printf("dyn %d %d %d %d %d %d\n", lp == static_cast<Left *>(&both), bo == &both, cross == rp, no == 0, mostd == (void *)&both, cmost == (void *)&both);
    Base *nullb = 0;
    printf("null %d %d\n", dynamic_cast<Both *>(nullb) == 0, dynamic_cast<void *>(nullb) == 0);
    Right &rr = dynamic_cast<Right &>(*bp);
    printf("ref %d\n", rr.rr);
    try {
        Base b0;
        Other &o = dynamic_cast<Other &>(b0);
        printf("no throw %d\n", o.x);
    } catch (std::bad_cast &e) {
        printf("bad_cast\n");
    }
    Twice tw;
    Base *t1 = static_cast<Twice1 *>(&tw);
    printf("twice %d %d\n", dynamic_cast<Twice *>(t1) == &tw, dynamic_cast<Twice2 *>(t1) == static_cast<Twice2 *>(&tw));
    V *vv = &u;
    printf("vdyn %d %d\n", dynamic_cast<U *>(vv) == &u, dynamic_cast<W *>(vv) == static_cast<W *>(&u));
    Priv pr;
    printf("priv %d\n", dynamic_cast<Priv *>(pr.self()) == 0);
    return 0;
}
