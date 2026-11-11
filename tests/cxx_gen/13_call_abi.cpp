// Classes passed and returned by value: the System V classification of a
// class whose data is in its bases (or in reference members), classes
// trivial for calls but not trivially copyable (a reference member, a
// non-trivial assignment) returned in registers, std::nullptr_t arguments.
#include <cstddef>
#include <cstdio>

struct B { long x; double y; };
struct D : B { };
struct E : B { int z; };
struct F { int a; };
struct G : F { float b; };
__attribute__((noinline)) D mkd(long a, double b) { D d; d.x = a; d.y = b; return d; }
__attribute__((noinline)) E mke(long a) { E e; e.x = a; e.y = 2.5; e.z = 7; return e; }
__attribute__((noinline)) G mkg(int a) { G g; g.a = a; g.b = 1.5f; return g; }
__attribute__((noinline)) double used(D d, G g) { return d.x + d.y + g.a + g.b; }

template<class T> T&& fwd(T& x) { return static_cast<T&&>(x); }
struct H { int &&r; H(int &&x) : r(static_cast<int&&>(x)) {} };
struct T : H { T(int &&x) : H(static_cast<int&&>(x)) {} T(const T&) = default; T(T&&) = default; };
T fw1(int &&a) { return T(fwd<int>(a)); }
template<class... A> T fw2(A&&... a) { return T(fwd<A>(a)...); }
int take(T &&t) { return t.r; }
template<class... A> int count(A&&...) { return sizeof...(A); }

struct R { int &r; R(int &x) : r(x) {} R& operator=(const R& o) { r = o.r; return *this; } };
R mkr(int &x) { return R(x); }
int taker(R&& a) { return a.r; }
int taker2(const R& a) { return a.r + 1; }

int nul(std::nullptr_t) { return 1; }
struct Guard { int *p; Guard& operator=(std::nullptr_t) { p = nullptr; return *this; } };

int main() {
  D d = mkd(3, 4.5);
  E e = mke(9);
  G g = mkg(11);
  printf("%ld %g %ld %g %d %d %g %g\n", d.x, d.y, e.x, e.y, e.z, g.a, (double)g.b, used(d, g));
  int v = 5;
  T t1 = fw1(static_cast<int&&>(v));
  T t2 = fw2(static_cast<int&&>(v));
  printf("%d %d %d %d\n", t1.r, t2.r, take(fw1(static_cast<int&&>(v))), count(fw1(static_cast<int&&>(v)), t1));
  R c = mkr(v);
  printf("%d %d %d\n", taker(mkr(v)), taker2(mkr(v)), c.r);
  std::nullptr_t n = nullptr;
  Guard gu;
  gu.p = &v;
  gu = nullptr;
  printf("%d %d %d\n", nul(nullptr), nul(n), gu.p == nullptr);
  return 0;
}
