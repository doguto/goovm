// Function template specializations: their Itanium names (template
// arguments, the declared return and parameter types with T_ / S_
// substitutions, dependent names, packs, member templates of classes and
// class templates, operators), and a static local of a function template
// shared across translation units (the ABI oracle's split links: the
// copies of both compilers must be one).
#include <stdio.h>

namespace N {
template <class T> T id(T x) { return x; }
template <class T, class U> U conv(T x) { return (U)x; }
template <class T> T *ptr(T *p, const T &r) { return p ? p : (T *)&r; }
template <class T> struct Box { T v; typedef T type; template <class U> U get(U d) const { return v ? (U)v : d; } };
template <class T> typename Box<T>::type unbox(const Box<T> &b) { return b.v; }
template <class T> Box<T> operator+(const Box<T> &a, const Box<T> &b) { return Box<T>{a.v + b.v}; }
template <int N> int times(int x) { return N * x; }
template <class... A> int count(A... a) { return sizeof...(A); }
template <class T> int &counter() { static int c = 0; return c; }
struct S { template <class T> int size(T) const { return (int)sizeof(T); } };
}
template <class T, class U> struct Pair { T a; U b; };
template <class T, class U> Pair<U, T> swap_pair(const Pair<T, U> &p) { return Pair<U, T>{p.b, p.a}; }
template <class T> void fill(T *a, int n, T v) { for (int i = 0; i < n; i++) a[i] = v; }
template <class T, int N> int len(T (&)[N]) { return N; }

int bump() { return ++N::counter<int>(); }

int main() {
    int k = N::id(3);
    double d = N::id(2.5);
    long l = N::conv<int, long>(7);
    int x = 1;
    int *p = N::ptr<int>(nullptr, x);
    N::Box<int> b{4};
    int u = N::unbox(b);
    N::Box<int> c = b + b;
    double g = b.get(1.5);
    int t = N::times<3>(5);
    int n = N::count(1, 2.0, 'c');
    N::S s;
    int z = s.size(1.0);
    Pair<int, char> pr{1, 'a'};
    Pair<char, int> sp = swap_pair(pr);
    int arr[4];
    fill(arr, 4, 9);
    bump();
    bump();
    printf("%d %.1f %ld %d %d %d %.1f %d %d %d %c %d %d %d %d\n", k, d, l, *p, u, c.v, g, t, n, z, sp.a, arr[3], len(arr),
           N::counter<int>(), bump());
    return 0;
}
