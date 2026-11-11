/* always_inline nodebug functions (as the intrinsics headers define them)
 * whose bodies hold statement expressions with locals and compound
 * literals: every expansion, in every function, needs slots of its own
 * (goosecc reused the slot of the first function that expanded them). */
#include <stdio.h>

#define AI static __inline__ __attribute__((__always_inline__, __nodebug__))

typedef struct { int x, y, z; } P3;

#define TWICE(v) __extension__({ int __t = (v); __t + __t; })

AI int twice_plus(int a) { return TWICE(a) + 1; }
AI P3 mk(int a, int b) { return (P3){ a, b, a + b }; }
AI int sum3(int a, int b) { P3 p = mk(a, b); int *q = (int[]){ p.x, p.y, p.z }; return q[0] + q[1] + q[2]; }
AI long nested(int a) { return TWICE(TWICE(a)) + __extension__({ long __u = a; __u * 3; }); }

__attribute__((noinline)) int f1(int a) { return twice_plus(a) + sum3(a, 2) + (int)nested(a); }
__attribute__((noinline)) int f2(int a) {
    int r = 0;
    for (int i = 0; i < 3; i++) r += twice_plus(a + i) * sum3(i, a);
    return r + (int)nested(a - 1);
}
__attribute__((noinline)) int f3(int a) { return sum3(twice_plus(a), twice_plus(a + 1)) + (int)nested(sum3(a, a)); }

int main(void) {
    printf("%d %d %d\n", f1(3), f2(5), f3(7));
    printf("%d %d %d\n", f3(1), f1(-4), f2(0));
    return 0;
}
