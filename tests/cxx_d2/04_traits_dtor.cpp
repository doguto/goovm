// goosecc D2: <type_traits> evaluated at compile time (class property
// builtins, SFINAE-based traits, variable templates) and explicit destructor
// and pseudo-destructor calls.
#include <new>
#include <cstdio>
#include <type_traits>
#include <utility>
struct E {};
struct P { int x; double y; };
struct Cx { Cx(); int x; };
struct D : P { int z; };
struct V { virtual ~V(); };
struct F final { int a; };
struct NC { NC(const NC&) = delete; NC() = default; };
struct M { M(M&&); M& operator=(M&&); };
struct Conv { operator int() const; };
struct Ex { explicit Ex(int); };
struct Im { Im(int); };
struct Priv { private: int a; public: int b; };
enum En { A1, B1 };
enum class Sc : short { X };
#define T(...) static_assert(__VA_ARGS__, #__VA_ARGS__)
T(std::is_trivial<int>::value); T(std::is_trivial<E>::value); T(std::is_trivial<P>::value); T(!std::is_trivial<Cx>::value);
T(std::is_trivially_copyable<Cx>::value); T(!std::is_trivially_copyable<V>::value); T(!std::is_trivially_copyable<M>::value);
T(std::is_standard_layout<P>::value); T(!std::is_standard_layout<D>::value); T(!std::is_standard_layout<Priv>::value);
T(std::is_pod<P>::value); T(!std::is_pod<Cx>::value);
T(std::is_empty<E>::value); T(!std::is_empty<P>::value);
T(std::is_polymorphic<V>::value); T(!std::is_polymorphic<P>::value);
T(std::is_final<F>::value); T(!std::is_final<P>::value);
T(std::is_aggregate<P>::value); T(!std::is_aggregate<Cx>::value); T(std::is_aggregate<D>::value);
T(std::has_virtual_destructor<V>::value);
T(std::is_base_of<P, D>::value); T(!std::is_base_of<D, P>::value); T(std::is_base_of<P, P>::value);
T(std::is_convertible<int, double>::value); T(std::is_convertible<D*, P*>::value); T(!std::is_convertible<P*, D*>::value);
T(std::is_convertible<Conv, int>::value); T(!std::is_convertible<int, Ex>::value); T(std::is_convertible<int, Im>::value);
T(std::is_constructible<Ex, int>::value); T(std::is_constructible<P>::value); T(!std::is_constructible<NC, const NC&>::value);
T(std::is_default_constructible<Cx>::value); T(std::is_copy_constructible<P>::value); T(!std::is_copy_constructible<M>::value);
T(std::is_move_constructible<M>::value); T(std::is_trivially_copy_constructible<P>::value);
T(std::is_assignable<int&, int>::value); T(!std::is_assignable<int, int>::value); T(std::is_copy_assignable<P>::value);
T(!std::is_copy_assignable<M>::value); T(std::is_move_assignable<M>::value);
T(std::is_enum<En>::value); T(std::is_enum<Sc>::value); T(!std::is_enum<int>::value);
T(std::is_same<std::underlying_type<Sc>::type, short>::value);
T(std::is_integral<char>::value); T(std::is_floating_point<float>::value); T(std::is_arithmetic<bool>::value);
T(std::is_signed<int>::value); T(std::is_unsigned<unsigned>::value); T(!std::is_signed<bool>::value);
T(std::is_same<std::decay<int[3]>::type, int*>::value); T(std::is_same<std::remove_cv<const volatile int>::type, int>::value);
T(std::is_same<std::conditional<true, int, char>::type, int>::value); T(std::is_same<std::conditional_t<false, int, char>, char>::value);
T(std::is_same<std::common_type<int, long>::type, long>::value);
T(std::is_same<std::make_signed<unsigned char>::type, signed char>::value);
T(std::is_same<decltype(std::declval<int&>()), int&>::value);
T(std::is_nothrow_move_constructible<P>::value);
T(std::is_same_v<std::remove_reference_t<int&&>, int>); T(std::is_class_v<P>); T(!std::is_class_v<En>);
T(std::is_trivially_destructible<P>::value); T(!std::is_trivially_destructible<V>::value);
T(std::conjunction<std::true_type, std::is_class<P>>::value); T(!std::disjunction<std::false_type, std::is_class<int>>::value);
T(std::negation<std::is_class<int>>::value);
T(std::is_invocable<int(*)(int), int>::value);
T(std::is_same<std::invoke_result_t<int(*)(int), int>, int>::value);
T(std::is_swappable<int>::value); T(std::is_nothrow_swappable<P>::value);
T(std::is_same<std::add_pointer_t<int&>, int*>::value);
T(std::rank<int[2][3]>::value == 2); T(std::extent<int[2][3], 0>::value == 2);
T(std::alignment_of<double>::value == 8);
T(std::is_same<std::aligned_storage<8, 8>::type, std::aligned_storage<8, 8>::type>::value);
struct A { int x; A(int v) : x(v) {} ~A() { printf("~A %d\n", x); } };
struct B { virtual ~B() { printf("~B\n"); } };
struct C : B { ~C() override { printf("~C\n"); } };
struct T0 { int z; };
template <class U> void destroy(U* p) { p->~U(); }
typedef int I;
int main() {
    A* a = new A(7);
    a->~A();
    ::operator delete(a);
    B* bp = new C;
    bp->~B();
    ::operator delete(bp);
    int i = 5; I* ip = &i; ip->~I(); i.~I();
    A* a2 = new A(9);
    destroy(a2);
    ::operator delete(a2);
    int* q = &i; destroy(q);
    T0 t; t.~T0();
    printf("%d\n", i);
    return 0;
}
