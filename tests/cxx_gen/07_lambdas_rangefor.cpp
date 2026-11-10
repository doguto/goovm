// Lambdas (captures by copy and by reference, explicit and implicit, this,
// init-captures, mutable, nested lambdas, return type deduction, the
// conversion to a function pointer, closures passed to templates, class
// captures with copy constructors and destructors) and range-based for
// (arrays, classes with begin/end members, references, break/continue,
// a temporary range kept alive).
#include <stdio.h>

int live = 0;
struct Tr { int v; Tr(int x) : v(x) { live++; } Tr(const Tr &o) : v(o.v) { live++; } ~Tr() { live--; } };

struct R { int a[4] = {1, 2, 3, 4}; int *begin() { return a; } int *end() { return a + 4; } };
struct Vec {
    int n = 0;
    int data[8];
    struct It { int *p; int &operator*() const { return *p; } It &operator++() { ++p; return *this; } bool operator!=(const It &o) const { return p != o.p; } };
    It begin() { return It{data}; }
    It end() { return It{data + n}; }
    void push(int x) { data[n++] = x; }
};
Vec make(int k) { Vec v; for (int i = 0; i < k; i++) v.push(i * i); return v; }

template <class F> int apply(F f, int x) { return f(x); }
template <class F> void twice(F &f) { f(); f(); }

struct S {
    int m = 5;
    int f(int a) { auto l = [this, a](int x) { return m + a + x; }; return l(1); }
    int g() { auto l = [&]() { m *= 2; return m; }; return l(); }
    int h() { return [=]() { return m + 1; }(); }
};

inline int inl(int k) { auto l = [k](int x) { return x + k; }; return l(1); }

int main() {
    int arr[] = {1, 2, 3};
    int s = 0;
    for (int x : arr) s += x;
    for (auto &x : arr) x *= 2;
    R r;
    for (int v : r) s += v;
    for (const int &v : make(5)) { if (v == 4) continue; if (v > 9) break; s += v; }
    printf("range %d %d\n", s, arr[2]);

    int k = 10;
    auto add = [k](int x) { return x + k; };
    auto inc = [&k]() { k++; };
    inc();
    int counter = 0;
    auto bump = [counter]() mutable { return ++counter; };
    bump();
    printf("lambda %d %d %d %d\n", add(1), k, bump(), counter);
    printf("apply %d\n", apply([=](int x) { return x + k + s; }, 1));
    int (*fp)(int) = [](int x) { return x - 1; };
    printf("fp %d\n", fp(5));
    auto init = [y = k * 2, &z = s](int d) { z += d; return y; };
    printf("init %d %d\n", init(3), s);
    auto outer = [&](int a) { return [&, a](int b) { return a * b + k; }(2); };
    printf("nested %d\n", outer(3));
    auto deduce = [](double d) { if (d > 0) return d * 2; return -d; };
    printf("deduce %.1f %.1f\n", deduce(1.5), deduce(-2.0));
    int calls = 0;
    auto cnt = [&calls]() { calls++; };
    twice(cnt);
    printf("twice %d\n", calls);
    {
        Tr t(7);
        auto cap = [t]() { return t.v; };
        auto cap2 = cap;
        printf("class capture %d %d live %d\n", cap(), cap2(), live);
    }
    printf("live %d\n", live);
    S obj;
    printf("this %d %d %d %d\n", obj.f(2), obj.g(), obj.h(), inl(3));
    return 0;
}
