// goosecc D1: virtual functions, vtables, virtual destructors, pure
// virtual functions, calls through base pointers and references, new and
// delete.
#include <stdio.h>

struct Shape {
    const char *name;
    Shape(const char *n) : name(n) {}
    virtual ~Shape() { printf("~Shape %s\n", name); }
    virtual double area() const = 0;
    virtual int sides() const { return 0; }
    void describe() const { printf("%s: area %.2f, %d sides\n", name, area(), sides()); }
};

struct Rect : Shape {
    double w, h;
    Rect(double a, double b) : Shape("rect"), w(a), h(b) {}
    ~Rect() { printf("~Rect\n"); }
    double area() const { return w * h; }
    int sides() const { return 4; }
};

struct Square : Rect {
    Square(double s) : Rect(s, s) { name = "square"; }
    double area() const { return Rect::area() + 0.5; }
};

struct Circle : Shape {
    double r;
    Circle(double x) : Shape("circle"), r(x) {}
    double area() const { return 3.0 * r * r; }
};

struct Animal {
    virtual const char *sound() { return "..."; }
    virtual ~Animal() {}
};
struct Dog : Animal {
    const char *sound() { return "woof"; }
};
struct Puppy : Dog {
    const char *sound() { return "yip"; }
};

void speak(Animal &a) { printf("%s\n", a.sound()); }

int main() {
    Shape *shapes[4];
    shapes[0] = new Rect(2, 3);
    shapes[1] = new Square(2);
    shapes[2] = new Circle(1);
    shapes[3] = new Rect(1, 1);
    double total = 0;
    for (int i = 0; i < 4; i++) {
        shapes[i]->describe();
        total += shapes[i]->area();
    }
    printf("total %.2f\n", total);
    for (int i = 0; i < 4; i++) delete shapes[i];
    Dog d;
    Puppy p;
    Animal a;
    speak(d);
    speak(p);
    speak(a);
    Animal *ap = new Puppy;
    printf("%s\n", ap->sound());
    delete ap;
    int *ip = new int(41);
    (*ip)++;
    printf("%d\n", *ip);
    delete ip;
    int *arr = new int[10];
    for (int i = 0; i < 10; i++) arr[i] = i * i;
    printf("%d\n", arr[9]);
    delete[] arr;
    Rect r(4, 5);
    Shape &sr = r;
    printf("%.1f %d\n", sr.area(), sr.sides());
    return 0;
}
