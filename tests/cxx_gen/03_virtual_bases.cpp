// Multiple and virtual inheritance: layouts (primary virtual bases,
// indirect primary bases), vtables with secondary vtables, vcall and vbase
// offsets, this-adjusting and covariant thunks, VTTs and construction
// vtables, virtual base conversions, typeid/dynamic_cast across them.
#include <stdio.h>
#include <typeinfo>

static int depth = 0;
#define LOG(...) printf(__VA_ARGS__)

struct A { int a; A() : a(1) { LOG("A() %s\n", name()); } virtual const char *name() const { return "A"; } virtual ~A() { LOG("~A %s\n", name()); } };
struct B : virtual A { int b; B() : b(2) { LOG("B() %s\n", name()); } const char *name() const override { return "B"; } virtual int fb() { return b; } ~B() { LOG("~B %s\n", name()); } };
struct C : virtual A { int c; C() : c(3) { LOG("C() %s\n", name()); } virtual int fc() { return c + a; } ~C() { LOG("~C %s\n", name()); } };
struct D : B, C { int d; D() : d(4) { LOG("D() %s\n", name()); } const char *name() const override { return "D"; } int fb() override { return 40 + d; } int fc() override { return 50 + d; } ~D() { LOG("~D %s\n", name()); } };

struct E { virtual void e() { LOG("E::e\n"); } };       // nearly empty
struct F : virtual E { int f = 5; void e() override { LOG("F::e %d\n", f); } };
struct G : virtual F, virtual E { int g = 6; };
struct H : G { void e() override { LOG("H::e %d %d\n", f, g); } };

struct X { int x = 7; virtual ~X() {} };
struct Y : virtual X { };
struct Z : Y, virtual X { int z = 8; };

// covariant returns through a non-primary base
struct P1 { int p1 = 11; virtual P1 *self() { return this; } virtual ~P1() {} };
struct P2 { int p2 = 12; virtual P2 *self() { return this; } virtual ~P2() {} };
struct Q : P1, P2 { int q = 13; Q *self() override { return this; } };

// non-virtual multiple inheritance: this-adjusting thunks
struct M1 { int m1 = 21; virtual int get() { return m1; } virtual ~M1() {} };
struct M2 { int m2 = 22; virtual int get() { return m2; } virtual int other() { return -m2; } virtual ~M2() {} };
struct MM : M1, M2 { int mm = 23; int get() override { return mm; } };

int call_fb(B *b) { return b->fb(); }
int call_fc(C *c) { return c->fc(); }
const char *nm(A *a) { return a->name(); }
int get2(M2 *m) { return m->get() * 100 + m->other(); }

int main() {
    {
        D d;
        LOG("fb %d fc %d name %s\n", call_fb(&d), call_fc(&d), nm(&d));
        A *pa = &d;
        B *pb = &d;
        C *pc = &d;
        LOG("a via B %d via C %d via A %d\n", pb->a, pc->a, pa->a);
        LOG("dyn %d %d %d\n", dynamic_cast<D *>(pa) == &d, dynamic_cast<C *>(pb) == pc, dynamic_cast<B *>(pc) == pb);
        LOG("typeid %s %d\n", typeid(*pa).name(), typeid(*pc) == typeid(D));
        B b;
        LOG("b: fb %d name %s dyn %p\n", call_fb(&b), nm(&b), (void *)dynamic_cast<D *>((A *)&b));
    }
    {
        H h;
        E *pe = &h;
        pe->e();
        F *pf = &h;
        pf->e();
        G g;
        ((E *)&g)->e();
        LOG("sizes %d %d %d\n", (int)sizeof(F), (int)sizeof(G), (int)sizeof(H));
    }
    {
        Z z;
        X *px = &z;
        Y *py = &z;
        LOG("z %d %d %d %d\n", px->x, py->x, z.z, (int)sizeof(Z));
        LOG("dyn %d\n", dynamic_cast<Z *>(px) == &z);
    }
    {
        Q q;
        P2 *p2 = &q;
        LOG("cov %d %d\n", p2->self() == p2, ((P1 *)&q)->self() == (P1 *)&q);
        P2 *d2 = q.self();
        LOG("cov2 %d\n", d2->p2);
    }
    {
        MM m;
        LOG("mm %d %d\n", get2(&m), ((M1 *)&m)->get());
        M2 *p = new MM;
        delete p;
        LOG("deleted\n");
    }
    try {
        D d;
        throw d;
    } catch (C &c) {
        LOG("caught C %d %s\n", c.fc(), c.name());
    } catch (...) {
        LOG("caught ...\n");
    }
    return depth;
}
