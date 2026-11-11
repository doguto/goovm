// goosecc D2: a member class of a class template declared in it and defined
// out of it (basic_ostream::sentry), instantiated when needed complete;
// its in-class destructor instantiated for a declared object.
#include <cstdio>
template <class T> struct TS { int n = 0; class sentry; friend class sentry;
  int go() { sentry se(*this); if (se) return 1; return 0; } };
template <class T> class TS<T>::sentry { TS &s; public: explicit sentry(TS &x); ~sentry() { s.n += 10; } explicit operator bool() const { return s.n > 0; } };
template <class T> TS<T>::sentry::sentry(TS &x) : s(x) { s.n++; }
int main() { TS<int> t; int r = t.go(); printf("%d %d\n", r, t.n); return 0; }
