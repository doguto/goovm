// goosecc D1: member functions, references, overloading, namespaces,
// static members, default arguments.
#include <stdio.h>

struct Point {
    int x, y;
    int sum() const { return x + y; }
    void move(int dx, int dy = 1) { x += dx; y += dy; }
    Point &scale(int k) { x *= k; y *= k; return *this; }
    static int count;
    static int twice(int v) { return 2 * v; }
};
int Point::count = 3;

static int twice(int v) { return 2 * v; }
int twice(double v) { return (int)(3 * v); }
long twice(long v) { return v * 4; }

void inc(int &r) { r++; }
int &pick(int &a, int &b, bool f) { return f ? a : b; }
const int &cmax(const int &a, const int &b) { return a < b ? b : a; }

namespace ns {
int g = 7;
int get() { return g; }
namespace inner {
int get() { return g * 2; }
}
}

struct Counter {
    int n;
    int next() { return ++n; }
    int peek() const { return n; }
};

int sum_refs(const Point &p, Point *q) { return p.x + q->y; }

int main() {
    Point p;
    p.x = 1;
    p.y = 2;
    p.move(3);
    p.move(1, 1);
    printf("%d %d %d\n", p.x, p.y, p.sum());
    p.scale(2).scale(3);
    printf("%d %d\n", p.x, p.y);
    int a = 5, b = 6;
    inc(a);
    pick(a, b, false) = 40;
    pick(a, b, true) += 2;
    int &ra = a;
    ra += 10;
    printf("%d %d %d\n", a, b, cmax(a, b));
    printf("%d %d %ld\n", twice(4), twice(1.5), twice(5L));
    printf("%d %d %d\n", ns::get(), ns::inner::get(), Point::twice(Point::count));
    Counter c = {10};
    c.next();
    c.next();
    printf("%d\n", c.peek());
    Point q = p;
    q.y = 100;
    printf("%d %d\n", sum_refs(p, &q), q.x);
    return 0;
}
