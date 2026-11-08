// goosecc D1: constructors, destructors (scope exit, members, bases),
// default member initializers, mem-initializers, delegating constructors.
#include <stdio.h>

static int depth = 0;

struct Tracer {
    const char *name;
    int id;
    Tracer(const char *n, int i) : name(n), id(i) { printf("ctor %s %d\n", name, id); depth++; }
    ~Tracer() { printf("dtor %s %d\n", name, id); depth--; }
    void hello() const { printf("hello %s %d\n", name, id); }
};

struct Pair {
    Tracer a;
    Tracer b;
    int extra = 42;
    Pair(int k) : a("a", k), b("b", k + 1) { printf("pair body %d\n", extra); }
};

struct Base {
    int v;
    Base() : v(1) { printf("Base()\n"); }
    Base(int x) : v(x) { printf("Base(%d)\n", x); }
    ~Base() { printf("~Base %d\n", v); }
};

struct Derived : Base {
    Tracer t;
    int w;
    Derived(int x) : Base(x * 10), t("d", x), w(x) { printf("Derived(%d)\n", x); }
    Derived() : Derived(7) { printf("Derived() delegating\n"); }
    ~Derived() { printf("~Derived %d\n", w); }
    int total() const { return v + w; }
};

struct Defaults {
    int a = 3;
    double d = 2.5;
    int b;
    Defaults() : b(a * 2) {}
};

int early(int n) {
    Tracer t("early", n);
    if (n > 2) return n * 2;
    Tracer u("late", n);
    for (int i = 0; i < 2; i++) {
        Tracer loop("loop", i);
        if (i == n) break;
    }
    return n;
}

int main() {
    {
        Tracer t1("t1", 1);
        Tracer t2("t2", 2);
        t1.hello();
        printf("depth %d\n", depth);
    }
    printf("depth %d\n", depth);
    {
        Pair p(5);
        p.b.hello();
    }
    {
        Derived d(3);
        printf("total %d\n", d.total());
    }
    {
        Derived d;
        printf("total %d\n", d.total());
    }
    Defaults x;
    printf("%d %g %d\n", x.a, x.d, x.b);
    printf("%d\n", early(1));
    printf("%d\n", early(5));
    return 0;
}
