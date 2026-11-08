// goosecc D2: function templates: deduction (values, references, pointers,
// arrays, forwarding references), explicit arguments, partial ordering,
// non-templates preferred, redeclarations, member templates in and out of
// their class.
extern "C" int printf(const char*, ...);
template<class T> T mymax(T a, T b) { return a < b ? b : a; }
template<class T> T twice(const T& x) { return x + x; }
template<class T> T* first(T* p) { return p; }
template<class T, int N> int arrsize(T (&)[N]) { return N; }
template<class T> struct Box { T v; template<class U> U conv() const { return (U)v; } };
template<class T> int which(T) { return 1; }
template<class T> int which(T*) { return 2; }
int which(int) { return 3; }
template<class T> T idf(T x);
template<class T> T idf(T x) { return x; }
struct S { template<class T> T scale(T x) const; int k; };
template<class T> T S::scale(T x) const { return x * k; }
template<class T> T fwd(T&& x) { return x; }
int main() {
  int arr[5] = {1, 2, 3, 4, 5};
  Box<double> b; b.v = 2.75;
  S s; s.k = 3;
  double d = 1.5;
  printf("%d %g %d %d %d\n", mymax(3, 7), mymax(2.5, 1.5), twice(21), *first(arr), arrsize(arr));
  printf("%d %d %d %d\n", b.conv<int>(), which(&d), which(d), which(5));
  printf("%d %ld %d %d\n", idf(9), mymax<long>(3, 4L), s.scale(5), fwd(d) > 1);
  return 0;
}
