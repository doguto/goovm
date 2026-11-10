// new and delete expressions: single objects, arrays with and without
// cookies (constant and dynamic counts), list and value initialization,
// placement, nothrow, over-aligned types, class-specific operators,
// the operator delete cleanup when a constructor throws, virtual
// destructors (D0), explicit destructor calls, null pointers.
#include <stdio.h>
#include <stdlib.h>
#include <new>

int live = 0;   // (external: the ABI oracle splits the functions between compilers)
struct T { int v; T() : v(1) { live++; } T(int x) : v(x) { live++; } ~T() { live--; } };
struct Triv { int a, b; };
struct alignas(64) Big { int x = 5; };
struct Own {
    int k = 3;
    static void *operator new(size_t n) { printf("Own new %d\n", (int)n); return malloc(n); }
    static void operator delete(void *p, size_t n) { printf("Own delete %d\n", (int)n); free(p); }
    static void *operator new[](size_t n) { printf("Own new[] %d\n", (int)n); return malloc(n); }
    static void operator delete[](void *p) { printf("Own delete[]\n"); free(p); }
    ~Own() {}
};
struct Thrower { Thrower(int x) { if (x) throw 42; } };
struct VB { virtual ~VB() { printf("~VB\n"); } };
struct VD : VB { ~VD() { printf("~VD\n"); } };
struct VO { virtual ~VO() {} static void operator delete(void *p) { printf("VO delete\n"); ::operator delete(p); } };
struct VOD : VO { int x = 1; };
struct alignas(32) VA { virtual ~VA() {} int a = 2; };

int main() {
    T *a = new T;
    T *b = new T(7);
    T *c = new T[3];
    T *d = new T[2]{T(4), T(5)};
    printf("live %d %d %d %d %d\n", live, a->v, b->v, c[2].v, d[1].v);
    delete a; delete b; delete[] c; delete[] d;
    printf("live %d\n", live);
    int *ip = new int(9);
    int *ia = new int[4]();
    Triv *tr = new Triv{1, 2};
    Triv *ta = new Triv[2];
    printf("%d %d %d\n", *ip, ia[3], tr->b);
    delete ip; delete[] ia; delete tr; delete[] ta;
    char buf[sizeof(T)];
    T *pl = new (buf) T(11);
    printf("placement %d %d\n", pl->v, (void *)pl == (void *)buf);
    pl->~T();
    T *nt = new (std::nothrow) T(12);
    printf("nothrow %d\n", nt->v);
    delete nt;
    Big *bg = new Big;
    printf("aligned %d %d\n", bg->x, (int)((unsigned long)bg % 64));
    delete bg;
    Big *bga = new Big[3];
    printf("aligned[] %d\n", (int)((unsigned long)bga % 64));
    delete[] bga;
    Own *o = new Own;
    delete o;
    Own *oa = new Own[2];
    delete[] oa;
    try { Thrower *t = new Thrower(1); (void)t; } catch (int x) { printf("caught %d\n", x); }
    VB *vb = new VD;
    delete vb;
    VO *vo = new VOD;
    delete vo;
    VA *va = new VA;
    printf("va %d %d\n", va->a, (int)((unsigned long)va % 32));
    delete va;
    VB *vg = new VD;
    ::delete vg;
    T *z = 0;
    delete z;
    delete[] z;
    int n = 3;
    T *dyn = new T[n];
    delete[] dyn;
    printf("live %d\n", live);
    return 0;
}
