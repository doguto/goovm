// goosecc D2: the constant evaluator (constexpr functions, loops, objects,
// arrays, constructors, string literals, constexpr variables, static data
// members of class templates) and explicit specializations of function
// templates and of members of class templates.
#include <cstdio>
constexpr int sq(int x) { return x * x; }
static_assert(sq(3) == 9, "sq");
constexpr int fact(int n) { return n <= 1 ? 1 : n * fact(n - 1); }
static_assert(fact(5) == 120, "fact");
constexpr int sum(int n) { int s = 0; for (int i = 1; i <= n; ++i) s += i; return s; }
static_assert(sum(10) == 55, "sum");
struct P { int x, y; constexpr int area() const { return x * y; } };
constexpr P p{3, 4};
static_assert(p.area() == 12, "area");
constexpr int len(const char* s) { int n = 0; while (*s++) n++; return n; }
static_assert(len("hello") == 5, "len");
struct V { int a[4]; constexpr V() : a{1, 2, 3, 4} {} constexpr int get(int i) const { return a[i]; } };
static_assert(V().get(2) == 3, "v");
template<class T> constexpr T mx(T a, T b) { return a < b ? b : a; }
static_assert(mx(3, 7) == 7, "mx");
template<int N> struct F { static constexpr int v = N * F<N - 1>::v; };
template<> struct F<0> { static constexpr int v = 1; };
static_assert(F<5>::v == 120, "F");
constexpr int arr[] = {5, 6, 7};
static_assert(arr[1] == 6, "arr");
constexpr double half(double d) { return d / 2; }
static_assert(half(3.0) == 1.5, "half");
static_assert(__builtin_is_constant_evaluated(), "ice");
int a2[sq(4)];
static_assert(sizeof(a2) == 64, "a2");

template<class T> constexpr int kind(T) { return 0; }
template<> constexpr int kind<int>(int) { return 1; }
template<> constexpr int kind(double) { return 2; }
static_assert(kind('c') == 0 && kind(1) == 1 && kind(1.0) == 2, "kind");
template<class T> struct W { int f() { return 10; } static int g(); };
template<> int W<char>::f() { return 20; }
template<class T> int W<T>::g() { return 30; }
template<> int W<int>::g() { return 40; }

int main() {
  int r = __builtin_is_constant_evaluated() ? 1 : 0;
  W<int> wi; W<char> wc;
  printf("%d %d %d %d %d %d %d %d\n", sq(5), fact(4), kind('c'), kind(1), kind(1.0), wi.f() + wc.f(), W<long>::g() + W<int>::g(), r);
  return 0;
}
