#include <stdio.h>
struct S { int v; S(int x) : v(x) { printf("S%d\n", v); } ~S() { printf("~S%d\n", v); } };
inline int g(int a) { static S s(a); static int n = 0; return s.v + ++n; }
int f(int a) { static S s(a + 10); { static int k = a; k++; } { static int k = 3; } return s.v; }
struct A { int m(); A() { static int q = 4; q++; } };
int A::m() { static S t(7); return t.v; }
int main() { printf("%d %d %d %d\n", g(1), g(2), f(1), f(2)); A a; printf("%d\n", a.m()); return 0; }
