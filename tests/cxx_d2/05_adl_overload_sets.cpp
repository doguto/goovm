// goosecc D2: argument-dependent lookup of names ordinary lookup does not
// find (functions, function templates, operator functions), deduction from
// overload sets and the address of overloaded function templates, member
// classes of class templates, __typeof of functions.
#include <cstdio>
#include <locale.h>
namespace N {
  struct S { int v; };
  void put(S& s) { printf("put %d\n", s.v); }
  struct O { int n; };
  O& operator<<(O& o, const char* x) { o.n++; printf("<< %s\n", x); return o; }
  template<class T> void tput(T& t) { printf("tput %d\n", t.v); }
}
template<class C> struct R { C c; };
template<class C> int get1(R<C>& r) { return (int)r.c; }

template<class C> struct OS { int n = 0; };
template<class C> OS<C>& endl2(OS<C>& o) { o.n += 100; return o; }
template<class T> T twice(T x) { return x + x; }
int twice2(int x) { return 2 * x; }
double twice2(double x) { return 2 * x; }
int apply(int (*f)(int), int v) { return f(v); }
template<class F> int apply2(F f, int v) { return f(v); }
template<class A> int apply3(A (*f)(A), A v) { return (int)f(v); }

template<class T> struct TS {
  int k = 7;
  struct sentry {
    TS<T> &s;
    explicit sentry(TS<T> &x) : s(x) {}
    int get() { return s.k; }
  };
  struct sentry2 {
    TS &s;
    explicit sentry2(TS &x) : s(x) {}
  };
  int go() { sentry se(*this); sentry2 s2(*this); return se.get() + s2.s.k; }
};

extern "C" __typeof(uselocale) __uselocale;
int f(int);
__typeof(f) g;
int g(int x) { return x + 1; }

int main() {
  N::S s{3};
  put(s);
  tput(s);
  N::O out{0};
  operator<<(out, "x");
  out << "y" << "z";
  R<char> r{'a'};
  printf("%d %d\n", get1(r), get1<char>(r));
  OS<char> o;
  OS<char>& (*pe)(OS<char>&) = endl2;
  endl2(o);
  printf("%d\n", pe == &endl2<char>);
  printf("%d %d %d %d %d\n", o.n, apply(twice, 4), apply2(twice<int>, 5), apply(twice2, 6), apply3(twice2, 7));
  TS<int> t;
  locale_t l = __uselocale((locale_t)0);
  printf("%d %d %d %d\n", t.go(), g(1), l != 0, out.n);
  return 0;
}
