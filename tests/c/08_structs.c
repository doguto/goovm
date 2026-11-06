// Structs: nested, arrays of structs, copies, small and large struct returns.
#include <stdio.h>
#include <string.h>

struct Point { int x, y; };
struct Rect { struct Point a, b; char tag; };
struct Big { long v[5]; short s; char c; };
struct Mixed { char c; short s; int i; long long l; char *p; unsigned char u; };

static struct Point mkpt(int x, int y) { struct Point p = {x, y}; return p; }
static struct Big mkbig(long base) {
    struct Big b;
    for (int i = 0; i < 5; i++) b.v[i] = base * (i + 1);
    b.s = (short)base;
    b.c = 'z';
    return b;
}
static int area(const struct Rect *r) { return (r->b.x - r->a.x) * (r->b.y - r->a.y); }
static void scale(struct Rect *r, int k) { r->a.x *= k; r->a.y *= k; r->b.x *= k; r->b.y *= k; }

struct Rect grects[3] = {{{0, 0}, {2, 3}, 'a'}, {{1, 1}, {4, 5}, 'b'}, {{-2, -2}, {2, 2}, 'c'}};

int main(void) {
    struct Point p = mkpt(3, 4);
    printf("pt %d %d\n", p.x, p.y);
    struct Big b = mkbig(7);
    printf("big %ld %ld %d %c\n", b.v[0], b.v[4], b.s, b.c);
    struct Big b2 = b;
    b2.v[2] = -1;
    printf("copy %ld %ld\n", b.v[2], b2.v[2]);
    int total = 0;
    for (int i = 0; i < 3; i++) total += area(&grects[i]);
    printf("areas %d\n", total);
    scale(&grects[1], 3);
    printf("scaled %d %c\n", area(&grects[1]), grects[1].tag);
    struct Mixed m;
    memset(&m, 0, sizeof m);
    m.c = -3; m.s = -300; m.i = 70000; m.l = -5000000000LL; m.p = "mixed"; m.u = 250;
    struct Mixed n = m;
    printf("mixed %d %d %d %lld %s %u %zu\n", n.c, n.s, n.i, n.l, n.p, n.u, sizeof(struct Mixed));
    struct Rect r = grects[2];
    r.a = mkpt(-10, -10);
    printf("rect %d %d %d\n", area(&r), r.b.x, r.a.y);
    struct Point arr[4];
    for (int i = 0; i < 4; i++) arr[i] = mkpt(i, i * i);
    int s = 0;
    for (struct Point *q = arr; q < arr + 4; q++) s += q->x * 100 + q->y;
    printf("arr %d\n", s);
    return 0;
}
