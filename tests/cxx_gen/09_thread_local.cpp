// thread_local variables: namespace-scope ones with constant and dynamic
// initialization and destructors (__tls_init, _ZTH aliases, _ZTW
// wrappers, __cxa_thread_atexit), internal ones, extern declarations,
// block-scope ones with their own guard.
#include <stdio.h>
int live = 0;
struct C { int v; C(int x) : v(x) { live++; printf("C(%d)\n", x); } ~C() { printf("~C(%d)\n", v); } };
thread_local int counter = 5;
thread_local C obj(7);
static thread_local int hidden = 3;
int next() { return ++counter; }
int get_obj() { return obj.v; }
int f() { thread_local C local(9); static thread_local int calls = 0; return local.v + ++calls; }
extern thread_local int ext;
thread_local int ext = 11;
int main() {
    printf("%d %d %d %d %d\n", next(), next(), get_obj(), hidden, ext);
    printf("%d %d\n", f(), f());
    return 0;
}
