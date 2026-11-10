// goosecc D2: if constexpr in instantiations: the discarded substatement is
// not instantiated (it would be ill-formed for these arguments).
#include <cstdio>
#include <type_traits>
struct A { int a() const { return 1; } };
struct B { int b() const { return 2; } };
template<class T> int get(const T& t) {
  if constexpr (std::is_same_v<T, A>) {
    return t.a();
  } else if constexpr (std::is_same_v<T, B>)
    return t.b();
  else {
    static_assert(std::is_integral_v<T>, "integral");
    for (int i = 0; i < 2; i++) { switch (i) { case 0: break; default: ; } }
    return (int)t * 10;
  }
}
template<int N> struct F {
  static int fact() {
    if constexpr (N <= 1) return 1;
    else return N * F<N - 1>::fact();
  }
};
int main() {
  printf("%d %d %d %d\n", get(A{}), get(B{}), get(4), F<5>::fact());
  return 0;
}
