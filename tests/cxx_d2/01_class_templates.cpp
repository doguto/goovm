// goosecc D2: class templates: implicit instantiation, partial and explicit
// specializations, members defined out of the class, static data members,
// nested classes, non-type parameters.
extern "C" int printf(const char*, ...);
template<class T> struct Box {
  T v;
  static int count;
  T get() const { return v; }
  void set(T x);
  struct Inner { T a, b; T sum() const { return a + b; } };
};
template<class T> void Box<T>::set(T x) { v = x; count++; }
template<class T> int Box<T>::count = 10;
template<class T, int N> struct Arr { T data[N]; int size() const { return N; } T& at(int i) { return data[i]; } };
template<class T> struct Arr<T, 0> { int size() const { return -1; } };
int main() {
  Box<int> b; b.set(3); b.set(4);
  Box<double> d; d.set(2.5);
  Box<int>::Inner in; in.a = 1; in.b = 2;
  Arr<long, 4> a; a.at(2) = 7;
  Arr<char, 0> z;
  printf("%d %g %d %d %d %ld %d\n", b.get(), d.get(), Box<int>::count, in.sum(), a.size(), a.at(2), z.size());
  return 0;
}
