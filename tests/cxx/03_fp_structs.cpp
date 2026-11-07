// Small floating-point aggregates returned and passed by value, in the shapes
// clang gives them at -O0: a btVector3-like class of four floats ({<2 x float>,
// <2 x float>}), three floats ({<2 x float>, float}), std::complex<float>
// (<2 x float>) and <double> ({double, double}), pairs, a double with an
// integer ({double, i64}, {i32, double}), a char with a double ({i8, double}),
// results used in loops, across calls, in conditions and discarded.
#include <complex>
#include <cstdio>
#include <utility>

struct Vec3 {
    float m[4];
    Vec3() {}
    Vec3(const float &x, const float &y, const float &z) { m[0] = x; m[1] = y; m[2] = z; m[3] = 0.0f; }
    float x() const { return m[0]; }
    float y() const { return m[1]; }
    float z() const { return m[2]; }
    Vec3 &operator+=(const Vec3 &v) { m[0] += v.m[0]; m[1] += v.m[1]; m[2] += v.m[2]; return *this; }
    float dot(const Vec3 &v) const { return m[0] * v.m[0] + m[1] * v.m[1] + m[2] * v.m[2]; }
    Vec3 cross(const Vec3 &v) const {
        return Vec3(m[1] * v.m[2] - m[2] * v.m[1], m[2] * v.m[0] - m[0] * v.m[2], m[0] * v.m[1] - m[1] * v.m[0]);
    }
};
static Vec3 operator+(const Vec3 &a, const Vec3 &b) { return Vec3(a.m[0] + b.m[0], a.m[1] + b.m[1], a.m[2] + b.m[2]); }
static Vec3 operator-(const Vec3 &a, const Vec3 &b) { return Vec3(a.m[0] - b.m[0], a.m[1] - b.m[1], a.m[2] - b.m[2]); }
static Vec3 operator*(const Vec3 &a, const float &s) { return Vec3(a.m[0] * s, a.m[1] * s, a.m[2] * s); }
static Vec3 operator*(const float &s, const Vec3 &a) { return a * s; }
static Vec3 operator-(const Vec3 &a) { return Vec3(-a.m[0], -a.m[1], -a.m[2]); }

// element-wise product
static Vec3 mulv(const Vec3 &a, const Vec3 &b) { return Vec3(a.x() * b.x(), a.y() * b.y(), a.z() * b.z()); }
struct Body {
    Vec3 lin, ang, inv;
    void applyImpulse(const Vec3 &l, const Vec3 &a, float mag) {
        lin += l * mag;
        ang += mag * mulv(a, inv);
    }
};

struct Three { float a, b, c; };
static Three three(float a, float b, float c) { Three t = {a, b, c}; return t; }
struct DL { double d; long n; };
static DL dl(double d, long n) { DL r = {d, n}; return r; }
struct ID { int i; double d; };
static ID id_(int i, double d) { ID r = {i, d}; return r; }
struct CD { char c; double d; };
static CD cd(int c, double d) { CD r = {(char)c, d}; return r; }

static std::complex<double> cmul(std::complex<double> a, std::complex<double> b) { return a * b; }
static std::complex<float> cmulf(std::complex<float> a, std::complex<float> b) { return a * b; }
static std::pair<double, double> minmax(double a, double b) { return a < b ? std::make_pair(a, b) : std::make_pair(b, a); }

static volatile int sink;
static void clobber() { sink = sink + 1; }

int main() {
    // a little rigid-body loop in the style of Bullet's solver
    Body b;
    b.lin = Vec3(0.0f, 1.0f, 2.0f);
    b.ang = Vec3(0.5f, -0.5f, 0.25f);
    b.inv = Vec3(1.0f, 0.5f, 0.25f);
    Vec3 n(0.0f, 0.0f, 1.0f), r(1.0f, 2.0f, 3.0f);
    float acc = 0.0f;
    for (int i = 0; i < 1000; i++) {
        Vec3 rel = b.lin + b.ang.cross(r);
        float vn = rel.dot(n);
        float imp = vn < 0.0f ? -vn * 0.5f : 0.01f * (float)(i % 7);
        Vec3 torque = r.cross(n);
        b.applyImpulse(n, torque, imp);
        Vec3 d = -(rel - torque) * 0.001f;
        acc += d.x() + 2.0f * d.y() + 3.0f * d.z();
        if (b.lin.dot(b.lin) > 100.0f) b.lin = b.lin * 0.5f;
        (void)(n * 2.0f);   // a discarded result
    }
    std::printf("body %.4f %.4f %.4f | %.4f %.4f %.4f | %.4f\n", b.lin.x(), b.lin.y(), b.lin.z(), b.ang.x(),
                b.ang.y(), b.ang.z(), acc);

    Three t = three(1.5f, -2.5f, 3.25f);
    clobber();
    Three u = three(t.c, t.a, t.b);
    std::printf("three %g %g %g\n", u.a, u.b, u.c);

    long sn = 0;
    double sd = 0;
    for (int i = 0; i < 100; i++) {
        DL x = dl(i * 0.25, i * 3L);
        ID y = id_(-i, i * 0.5);
        CD z = cd(200 + i, -i * 0.125);
        sn += x.n + y.i + (unsigned char)z.c;
        sd += x.d + y.d + z.d;
    }
    std::printf("mixed %ld %.4f\n", sn, sd);

    std::complex<double> c(1.0, 0.5), p(1.0, 0.0);
    std::complex<float> cf(0.5f, -1.0f), pf(1.0f, 0.0f);
    for (int i = 0; i < 20; i++) {
        p = cmul(p, c);
        pf = cmulf(pf, cf);
    }
    std::printf("complex %.6f %.6f | %.4f %.4f | abs %.6f arg %.6f\n", p.real(), p.imag(), pf.real(), pf.imag(),
                std::abs(c), std::arg(c));

    std::pair<double, double> m = minmax(3.5, -1.25);
    std::pair<double, double> m2 = minmax(m.first, 2.0);
    std::printf("pair %g %g %g %g\n", m.first, m.second, m2.first, m2.second);
    return 0;
}
