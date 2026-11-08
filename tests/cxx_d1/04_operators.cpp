// goosecc D1: operator overloading (member and non-member), conversion
// functions, copies of trivially copyable classes, global objects with
// constructors and destructors.
#include <stdio.h>

struct Vec {
    double x, y, z;
    Vec(double a = 0, double b = 0, double c = 0) : x(a), y(b), z(c) {}
    Vec operator+(const Vec &o) const { return Vec(x + o.x, y + o.y, z + o.z); }
    Vec operator-(const Vec &o) const { return Vec(x - o.x, y - o.y, z - o.z); }
    Vec operator*(double k) const { return Vec(x * k, y * k, z * k); }
    Vec operator-() const { return Vec(-x, -y, -z); }
    double dot(const Vec &o) const { return x * o.x + y * o.y + z * o.z; }
    Vec &operator+=(const Vec &o) { x += o.x; y += o.y; z += o.z; return *this; }
    bool operator==(const Vec &o) const { return x == o.x && y == o.y && z == o.z; }
    double &operator[](int i) { return i == 0 ? x : i == 1 ? y : z; }
};

Vec operator*(double k, const Vec &v) { return v * k; }

struct Frac {
    int n, d;
    Frac(int a, int b) : n(a), d(b) {}
    operator double() const { return (double)n / d; }
    Frac &operator++() { n += d; return *this; }
    Frac operator++(int) { Frac old = *this; n += d; return old; }
};

bool operator<(const Frac &a, const Frac &b) { return a.n * b.d < b.n * a.d; }

struct Global {
    int v;
    Global(int x) : v(x) { printf("Global(%d)\n", x); }
    ~Global() { printf("~Global(%d)\n", v); }
};

Global g1(1);
Global g2 = Global(2);
int computed = g1.v + 40;

int main() {
    Vec a(1, 2, 3), b(4, 5, 6);
    Vec c = a + b * 2.0;
    Vec d = 0.5 * c - a;
    Vec e = -d;
    e += a;
    printf("%g %g %g\n", c.x, c.y, c.z);
    printf("%g %g %g\n", d.x, d.y, d.z);
    printf("%g %g %g %g\n", e.x, e.y, e.z, a.dot(b));
    printf("%d %d\n", a == a, a == b);
    e[1] = 100;
    printf("%g\n", e[1]);
    Frac f(1, 2), h(2, 3);
    double fd = f;
    printf("%g %d\n", fd, f < h);
    ++f;
    Frac old = f++;
    printf("%d/%d %d/%d\n", f.n, f.d, old.n, old.d);
    printf("%d %d %d\n", g1.v, g2.v, computed);
    return 0;
}
