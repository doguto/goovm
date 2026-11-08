// goosecc D2: variadic templates: sizeof..., folds, recursive partial
// specializations, function parameter packs, expansions in calls and bases.
extern "C" int printf(const char*, ...);
template<class... Ts> struct Count { static const int value = sizeof...(Ts); };
template<class T, class... Rest> struct First { typedef T type; };
template<class... Ts> int sum(Ts... xs) { return (0 + ... + xs); }
template<class... Ts> int sum2(Ts... xs) { return (xs + ...); }
template<class... Ts> bool all(Ts... xs) { return (xs && ...); }
template<class T> T one(T x) { return x; }
template<class... Ts> int fwdsum(Ts... xs) { return sum(one(xs)...); }
template<class... Ts> struct Tuple;
template<> struct Tuple<> { int size() const { return 0; } };
template<class H, class... T> struct Tuple<H, T...> : Tuple<T...> {
  H head;
  int size() const { return 1 + Tuple<T...>::size(); }
};
template<class... Ts> int count_args(Ts&&... args) { return sizeof...(args); }
struct A { int a() { return 1; } };
struct B { int b() { return 2; } };
template<class... Bases> struct Mix : Bases... {};
template<int... Ns> struct ISeq { static const int total = (Ns + ... + 0); };
int main() {
  Tuple<int, double, char> t;
  Mix<A, B> m;
  First<long, int>::type l = 5;
  printf("%d %d %d %d %d %d\n", Count<int, char, double>::value, sum(1, 2, 3), sum2(4, 5), all(1, 2, 0), fwdsum(1, 2, 3, 4), t.size());
  printf("%d %d %d %d %d\n", count_args(1, 'a', 2.0), m.a() + m.b(), (int)sizeof(l), ISeq<1, 2, 3>::total, Count<>::value);
  return 0;
}
