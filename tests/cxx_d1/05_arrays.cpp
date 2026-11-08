// goosecc D1: arrays of class objects (constructed in order, destroyed in
// reverse), member arrays, braced lists of objects, VLAs (GNU), the GNU ?:
// with lvalues, gotos out of scopes with destructors.
#include <stdio.h>

static int live = 0;

struct Cell {
    int v;
    Cell() : v(live++) { printf("Cell() %d\n", v); }
    Cell(int x) : v(x) { live++; printf("Cell(%d)\n", x); }
    ~Cell() { live--; printf("~Cell %d\n", v); }
};

struct Complex {
    double re, im;
    Complex() : re(0), im(0) {}
    Complex(double r, double i) : re(r), im(i) {}
    Complex operator+(const Complex &o) const { return Complex(re + o.re, im + o.im); }
    Complex operator*(const Complex &o) const { return Complex(re * o.re - im * o.im, re * o.im + im * o.re); }
};

Complex table[4];
Cell globals[2];

struct Row {
    Cell cells[3];
    int tag;
    Row() : tag(9) { printf("Row()\n"); }
};

int &pick(int &a) { return a; }

int sum_vla(int n) {
    int t[n];
    for (int i = 0; i < n; i++) t[i] = i * 3;
    int s = 0;
    for (int i = 0; i < n; i++) s += t[i];
    return s;
}

int jumps(int n) {
    int r = 0;
    {
        Cell c(100 + n);
        if (n > 1) goto out;
        r = 1;
    }
out:
    return r + live;
}

int main() {
    for (int i = 0; i < 4; i++) table[i] = Complex(i, i + 1) * Complex(1, 1);
    Complex acc;
    for (int i = 0; i < 4; i++) acc = acc + table[i];
    printf("%g %g\n", acc.re, acc.im);
    {
        Cell local[3];
        printf("live %d\n", live);
    }
    {
        Cell some[4] = {Cell(7), 8};
        printf("live %d %d %d\n", live, some[0].v, some[1].v);
    }
    {
        Row r;
        printf("row %d %d\n", r.tag, r.cells[2].v);
    }
    printf("vla %d\n", sum_vla(10));
    int a = 0, b = 5;
    (pick(a) ?: b) = 42;
    printf("%d %d\n", a, b);
    printf("jumps %d %d\n", jumps(1), jumps(2));
    return 0;
}
