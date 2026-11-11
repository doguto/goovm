// Local classes: their local names (Z<function>E<name>[_<n>], the
// discriminator after a member's nested name), internal in non-inline
// functions, linkonce in inline ones (with vtables and typeinfo), and a
// static local of main.
#include <stdio.h>
int foo() { struct T { int v; T() : v(1) {} ~T() { printf("~T1\n"); } int get() { return v; } }; T t; return t.get(); }
int bar() { struct T { int w; T() : w(2) {} ~T() { printf("~T2\n"); } }; T t; { struct T { int q = 3; ~T() {} }; T u; return t.w + u.q; } }
inline int ib() { struct L { virtual int f() { return 7; } virtual ~L() {} }; L l; return l.f(); }
int main() { static int sillyArray[3] = {1, 2, 3}; printf("%d %d %d %d\n", foo(), bar(), ib(), sillyArray[1]); return 0; }
