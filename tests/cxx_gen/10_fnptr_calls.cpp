// Calls through pointers to functions of C++ types (references, classes
// by value and by invisible reference, a reference result through a
// lambda's invoker), stream-like manipulators, and the destructor of a
// nested class of a class template instantiation used only by a cleanup.
#include <stdio.h>
struct OS { int n = 0; OS &operator<<(OS &(*pf)(OS &)) { return pf(*this); } };
OS &endl2(OS &o) { o.n += 10; return o; }
struct Big { int a[8]; Big(int x) { for (int i = 0; i < 8; i++) a[i] = x + i; } Big(const Big &o) { for (int i = 0; i < 8; i++) a[i] = o.a[i]; } };
Big make(const Big &b, int k) { return Big(b.a[0] + k); }
int sum(Big b) { int s = 0; for (int i = 0; i < 8; i++) s += b.a[i]; return s; }
template <class T> struct TS { int n = 0;
  struct sentry { TS &s; explicit sentry(TS &x) : s(x) {} ~sentry() { s.n += 10; } };
  int go() { sentry se(*this); return 1; } };

int main() {
    TS<int> ts;
    ts.go();
    printf("nested %d\n", ts.n);
    OS os;
    os << endl2 << endl2;
    Big (*mk)(const Big &, int) = make;
    int (*sm)(Big) = sum;
    Big b(1);
    Big c = mk(b, 5);
    int &(*idf)(int &) = [](int &x) -> int & { return x; };
    int v = 3;
    idf(v) = 9;
    printf("%d %d %d %d\n", os.n, c.a[7], sm(c), v);
    return 0;
}
