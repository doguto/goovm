// goosecc D1: pointers to data members and to member functions
// (non-virtual and virtual, through objects and pointers, as conditions).
#include <stdio.h>

struct Point {
    int x, y, z;
};

struct Shape {
    int id;
    Shape(int i) : id(i) {}
    virtual ~Shape() {}
    virtual int area() const { return 0; }
    virtual int sides() const { return 0; }
    int twice(int k) const { return 2 * k + id; }
};

struct Square : Shape {
    int s;
    Square(int v) : Shape(4), s(v) {}
    int area() const { return s * s; }
    int sides() const { return 4; }
};

typedef int (Shape::*Query)() const;

int sum(Point *pts, int n, int Point::*field) {
    int s = 0;
    for (int i = 0; i < n; i++) s += pts[i].*field;
    return s;
}

int ask(const Shape &sh, Query q) { return (sh.*q)(); }

int main() {
    Point pts[3] = {{1, 2, 3}, {4, 5, 6}, {7, 8, 9}};
    printf("%d %d %d\n", sum(pts, 3, &Point::x), sum(pts, 3, &Point::y), sum(pts, 3, &Point::z));
    int Point::*f = &Point::y;
    Point *p = &pts[1];
    p->*f = 50;
    printf("%d\n", pts[1].y);
    Square sq(5);
    Shape plain(1);
    Query qs[2] = {&Shape::area, &Shape::sides};
    for (int i = 0; i < 2; i++) printf("%d %d\n", ask(sq, qs[i]), ask(plain, qs[i]));
    int (Shape::*t)(int) const = &Shape::twice;
    Shape *sp = &sq;
    printf("%d\n", (sp->*t)(10));
    Query none = 0;
    Query some = &Shape::area;
    if (some) printf("some\n");
    if (!none) printf("none\n");
    return 0;
}
