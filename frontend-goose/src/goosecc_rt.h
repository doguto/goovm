/* goosecc: the few C helpers the Goose sources bind with extern fn.
 * Included into the generated C with `goose --include`. */
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>

double goosecc_bits_to_f64(int64_t v) { double d; memcpy(&d, &v, 8); return d; }
int64_t goosecc_f64_to_bits(double d) { int64_t v; memcpy(&v, &d, 8); return v; }
double goosecc_round_f32(double d) { return (double)(float)d; }
int64_t goosecc_find_byte(sl_u8 s, uint8_t c) {
    const uint8_t *p = (const uint8_t *)memchr(s.data, c, (size_t)s.len);
    return p ? (int64_t)(p - s.data) : -1;
}

/* B2 lowering: exact floating-point constants (float, half, long double). */
uint32_t goosecc_f64_to_f32bits(double d) { float f = (float)d; uint32_t b; memcpy(&b, &f, 4); return b; }
double goosecc_f32bits_to_f64(uint32_t b) { float f; memcpy(&f, &b, 4); return (double)f; }
uint32_t goosecc_f64_to_f16bits(double d) { _Float16 h = (_Float16)d; uint16_t b; memcpy(&b, &h, 2); return b; }
double goosecc_f16bits_to_f64(uint32_t b) { uint16_t x = (uint16_t)b; _Float16 h; memcpy(&h, &x, 2); return (double)h; }
double goosecc_u64_to_f64(uint64_t x) { return (double)x; }
uint32_t goosecc_u64_to_f32bits(uint64_t x) { float f = (float)x; uint32_t b; memcpy(&b, &f, 4); return b; }
uint32_t goosecc_i64_to_f32bits(int64_t x) { float f = (float)x; uint32_t b; memcpy(&b, &f, 4); return b; }
double goosecc_copysign(double x, double y) { return copysign(x, y); }
double goosecc_libm_op(int64_t k, double x, double y) {
    switch (k) {
    case 0: return floor(x);
    case 1: return ceil(x);
    case 2: return trunc(x);
    case 3: return round(x);
    case 4: return nearbyint(x);
    case 5: return fmin(x, y);
    default: return fmax(x, y);
    }
}

static long double gcc_ld_get(gen_F80_g3 x) {
    unsigned char b[16] = {0};
    long double d;
    uint16_t h = (uint16_t)x.hi_g;
    memcpy(b, &x.lo_g, 8);
    memcpy(b + 8, &h, 2);
    memcpy(&d, b, sizeof d < 16 ? sizeof d : 16);
    return d;
}
static gen_F80_g3 gcc_ld_put(long double d) {
    unsigned char b[16] = {0};
    gen_F80_g3 r;
    uint16_t h;
    memcpy(b, &d, 10);
    memcpy(&r.lo_g, b, 8);
    memcpy(&h, b + 8, 2);
    r.hi_g = h;
    return r;
}
gen_F80_g3 goosecc_strtold(sl_u8 s) {
    char buf[256];
    size_t n = (size_t)s.len < 255 ? (size_t)s.len : 255;
    size_t j = 0;
    for (size_t i = 0; i < n; i++) if (s.data[i] != '\'') buf[j++] = (char)s.data[i];
    buf[j] = 0;
    return gcc_ld_put(strtold(buf, 0));
}
/* the bits of the literal text as a float (prec 0), double (1) or half (3) */
uint64_t goosecc_strtod_bits(sl_u8 s, int64_t prec) {
    char buf[256];
    size_t n = (size_t)s.len < 255 ? (size_t)s.len : 255;
    size_t j = 0;
    for (size_t i = 0; i < n; i++) if (s.data[i] != '\'') buf[j++] = (char)s.data[i];
    buf[j] = 0;
    if (prec == 0) { float f = strtof(buf, 0); uint32_t b; memcpy(&b, &f, 4); return b; }
    if (prec == 3) { _Float16 h = (_Float16)strtof(buf, 0); long double ld = strtold(buf, 0); h = (_Float16)ld; uint16_t b; memcpy(&b, &h, 2); return b; }
    double d = strtod(buf, 0);
    uint64_t b;
    memcpy(&b, &d, 8);
    return b;
}
gen_F80_g3 goosecc_f64_to_f80(double d) { return gcc_ld_put((long double)d); }
double goosecc_f80_to_f64(gen_F80_g3 x) { return (double)gcc_ld_get(x); }
double goosecc_f80_to_f32_d(gen_F80_g3 x) { return (double)(float)gcc_ld_get(x); }
uint32_t goosecc_f80_to_f32bits(gen_F80_g3 x) { float f = (float)gcc_ld_get(x); uint32_t b; memcpy(&b, &f, 4); return b; }
gen_F80_g3 goosecc_u64_to_f80(uint64_t x) { return gcc_ld_put((long double)x); }
gen_F80_g3 goosecc_i64_to_f80(int64_t x) { return gcc_ld_put((long double)x); }
int64_t goosecc_f80_to_i64(gen_F80_g3 x) { long double d = gcc_ld_get(x); if (d != d) return 0; if (d >= 9.2233720368547758e18L) return INT64_MAX; if (d <= -9.2233720368547758e18L) return INT64_MIN; return (int64_t)d; }
static long double gcc_round_prec(long double v, int64_t prec) {
    if (prec == 0) return (long double)(float)v;
    if (prec == 1) return (long double)(double)v;
    if (prec == 3) return (long double)(_Float16)v;
    return v;
}
gen_F80_g3 goosecc_f80_round(gen_F80_g3 x, int64_t prec) { return gcc_ld_put(gcc_round_prec(gcc_ld_get(x), prec)); }
gen_F80_g3 goosecc_f80_arith(int64_t op, gen_F80_g3 a, gen_F80_g3 b, int64_t prec) {
    long double x = gcc_ld_get(a), y = gcc_ld_get(b), r;
    if (prec == 0) {
        float fx = (float)x, fy = (float)y, fr;
        switch (op) { case 0: fr = fx + fy; break; case 1: fr = fx - fy; break; case 2: fr = fx * fy; break; default: fr = fx / fy; }
        return gcc_ld_put((long double)fr);
    }
    if (prec == 1) {
        double dx = (double)x, dy = (double)y, dr;
        switch (op) { case 0: dr = dx + dy; break; case 1: dr = dx - dy; break; case 2: dr = dx * dy; break; default: dr = dx / dy; }
        return gcc_ld_put((long double)dr);
    }
    switch (op) { case 0: r = x + y; break; case 1: r = x - y; break; case 2: r = x * y; break; default: r = x / y; }
    return gcc_ld_put(gcc_round_prec(r, prec));
}
gen_F80_g3 goosecc_f80_to_i128(gen_F80_g3 x, int64_t is_signed) {
    long double d = gcc_ld_get(x);
    gen_F80_g3 r;
    if (is_signed) { __int128 v = (__int128)d; r.lo_g = (uint64_t)v; r.hi_g = (uint64_t)(v >> 64); }
    else { unsigned __int128 v = (unsigned __int128)d; r.lo_g = (uint64_t)v; r.hi_g = (uint64_t)(v >> 64); }
    return r;
}
