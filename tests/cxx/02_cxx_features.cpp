// What clang emits for C++17 beyond exceptions: comdat templates and inline
// functions, inline variables and static locals with guards, thread_local
// with dynamic initialization (TLS wrappers), init_priority constructors,
// virtual and multiple inheritance, RTTI, member pointers, lambdas,
// std::function, the standard containers, iostreams (module asm).
#include <algorithm>
#include <functional>
#include <iostream>
#include <map>
#include <memory>
#include <sstream>
#include <string>
#include <typeinfo>
#include <vector>

static int order[8];
static int norder;
struct Early { Early() { order[norder++] = 1; } };
struct Late { Late() { order[norder++] = 2; } };
Late late_obj __attribute__((init_priority(2000)));
Early early_obj __attribute__((init_priority(1000)));

static int make(int x) { return x * 7; }
inline int inline_var = make(6);
template <class T> struct Holder { static T value; };
template <class T> T Holder<T>::value = T(make(3));

thread_local std::string tls_name = std::string("tls-") + std::to_string(make(2));
thread_local int tls_counter = make(1);

inline int &counter() {
    static int c = make(10);
    return ++c;
}

struct Shape {
    virtual ~Shape() = default;
    virtual double area() const = 0;
    virtual std::string name() const { return "shape"; }
};
struct Square : Shape {
    double s;
    explicit Square(double x) : s(x) {}
    double area() const override { return s * s; }
    std::string name() const override { return "square"; }
};
struct Circle : Shape {
    double r;
    explicit Circle(double x) : r(x) {}
    double area() const override { return 3.0 * r * r; }
};

struct A { int a = 1; virtual int fa() { return a; } virtual ~A() {} };
struct B : virtual A { int b = 2; int fa() override { return a + b; } };
struct C : virtual A { int c = 3; };
struct D : B, C { int d = 4; };

struct Pt { int x, y; int sum() const { return x + y; } int diff() const { return x - y; } };

template <class F> int apply_twice(F f, int v) { return f(f(v)); }

int main() {
    std::cout << "init order " << order[0] << order[1] << " inline " << inline_var << " holder "
              << Holder<int>::value << " " << Holder<double>::value << "\n";
    std::cout << tls_name << " " << tls_counter++ << " " << tls_counter << "\n";
    int c1 = counter(), c2 = counter();
    std::cout << "counter " << c1 << " " << c2 << "\n";

    std::vector<std::unique_ptr<Shape>> shapes;
    for (int i = 1; i <= 4; i++) {
        if (i % 2) shapes.push_back(std::make_unique<Square>(i));
        else shapes.push_back(std::make_unique<Circle>(i));
    }
    std::sort(shapes.begin(), shapes.end(), [](const auto &x, const auto &y) { return x->area() > y->area(); });
    for (auto &s : shapes)
        std::cout << s->name() << " " << s->area() << " " << (dynamic_cast<Square *>(s.get()) ? "is-square" : "not")
                  << " " << typeid(*s).name() << "\n";

    D d;
    A *pa = &d;
    std::cout << "virtual base " << pa->fa() << " " << d.c << " " << (dynamic_cast<C *>(pa) != nullptr) << "\n";

    int (Pt::*pm[2])() const = {&Pt::sum, &Pt::diff};
    int Pt::*field = &Pt::y;
    Pt p{10, 3};
    std::cout << "member pointers " << (p.*pm[0])() << " " << (p.*pm[1])() << " " << p.*field << "\n";

    int base = 5;
    auto add = [&base](int v) { return v + base; };
    std::function<int(int)> fn = [base](int v) { return v * base; };
    std::cout << "lambdas " << apply_twice(add, 1) << " " << apply_twice(fn, 2) << "\n";

    std::map<std::string, int> words;
    std::istringstream in("the quick brown fox jumps over the lazy dog the end");
    std::string w;
    while (in >> w) words[w]++;
    for (auto &kv : words) std::cout << kv.first << "=" << kv.second << " ";
    std::cout << "\n";
    return 0;
}
