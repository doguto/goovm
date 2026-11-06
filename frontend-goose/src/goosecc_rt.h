/* goosecc: the few C helpers the Goose sources bind with extern fn.
 * Included into the generated C with `goose --include`. */
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>

double goosecc_bits_to_f64(int64_t v) { double d; memcpy(&d, &v, 8); return d; }
int64_t goosecc_f64_to_bits(double d) { int64_t v; memcpy(&v, &d, 8); return v; }
double goosecc_round_f32(double d) { return (double)(float)d; }

/* B3: file I/O with fewer system calls than os's file_exists + read_file
 * (stat, fopen, fstat, 64 KB freads to EOF, fclose: 7 calls per header) and
 * write_file (fopen "wb" truncates, and ext4 then flushes the old blocks'
 * replacement at close: 0.2 ms per object). */
#include <fcntl.h>
#include <errno.h>
#include <unistd.h>
#include <sys/stat.h>

/* Commits the pages of the `bytes` after the top of a growable array's data
 * stack in one call (MADV_POPULATE_WRITE, Linux 5.14) instead of a page
 * fault per page as it grows: half the cost per page, and a large array
 * (the tokens, the AST, the source text) takes a few hundred. Nothing is
 * written: the pages hold zeros, as they would when first touched. At most
 * 512 KB, less than the guard gap after the region (the runtime's 1 MB),
 * so the range never reaches another region; a range in the gap fails
 * there and does nothing. Older kernels refuse the advice (EINVAL). */
#include <sys/mman.h>
#ifndef MADV_POPULATE_WRITE
#define MADV_POPULATE_WRITE 23
#endif
void goosecc_prefault(gs_rref a, int64_t bytes) {
    if (bytes > (512 << 10)) bytes = 512 << 10;
    uintptr_t top = (uintptr_t)a.stk->top;
    uintptr_t s = (top + 4095) & ~(uintptr_t)4095, e = (top + (uintptr_t)bytes) & ~(uintptr_t)4095;
    if (e > s) madvise((void *)s, e - s, MADV_POPULATE_WRITE);
}

static int goosecc_cpath(sl_u8 path, char *p, size_t cap) {
    if (path.len <= 0 || (size_t)path.len >= cap || memchr(path.data, 0, (size_t)path.len)) return 0;
    memcpy(p, path.data, (size_t)path.len);
    p[path.len] = 0;
    return 1;
}

/* Appends the contents of the file at path (anything but a directory, as
 * file_exists + read_file accept) to out: open, fstat, one read of a
 * regular file's size straight to the top of out's data stack (goose.h:
 * C may append there, moving the top and the count together), close.
 * 1 on success; 0 when there is no such file or it cannot be read, with
 * out unchanged. A read that cannot store (EFAULT: past the data stack's
 * reservation) goes through a buffer, so the overflow is the runtime's. */
int64_t goosecc_read_file(sl_u8 path, gs_rref out) {
    char p[4096];
    if (!goosecc_cpath(path, p, sizeof p)) return 0;
    int fd = open(p, O_RDONLY | O_CLOEXEC);
    if (fd < 0) return 0;
    struct stat st;
    if (fstat(fd, &st) != 0 || S_ISDIR(st.st_mode)) {
        close(fd);
        return 0;
    }
    int64_t len0 = out.hdr->len;
    uint8_t *top0 = out.stk->top;
    int reg = S_ISREG(st.st_mode), ok = 1, direct = 1;
    if (reg && st.st_size > 8192) goosecc_prefault(out, st.st_size + 1);
    size_t size = reg ? (size_t)st.st_size : 0, total = 0;
    for (;;) {
        /* one byte more than a regular file has left, to see its end */
        size_t want = reg && total <= size ? size + 1 - total : 65536;
        ssize_t n;
        if (direct) {
            n = read(fd, out.stk->top, want);
            if (n < 0 && errno == EFAULT) { direct = 0; continue; }
        } else {
            uint8_t buf[65536];
            n = read(fd, buf, sizeof buf);
            if (n > 0) gs_bld_append(out, buf, (int64_t)n);
        }
        if (n < 0) {
            if (errno == EINTR) continue;
            ok = 0;
            break;
        }
        if (n == 0) break;
        if (direct) {
            out.stk->top += n;
            out.hdr->len += n;
        }
        total += (size_t)n;
        if (reg && total == size && (size_t)n < want) break;
    }
    close(fd);
    if (!ok) {
        out.hdr->len = len0;
        out.stk->top = top0;
        return 0;
    }
    return 1;
}

/* Writes data to path. An existing regular file (not a symbolic link or a
 * device such as /dev/null) is removed first, as GNU ld does with its
 * output, and a new one is created: rewriting it in place would truncate
 * it. 1 on success. */
int64_t goosecc_write_file(sl_u8 path, sl_u8 data) {
    char p[4096];
    if (!goosecc_cpath(path, p, sizeof p)) return 0;
    struct stat st;
    if (lstat(p, &st) == 0 && S_ISREG(st.st_mode)) unlink(p);
    int fd = open(p, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, 0666);
    if (fd < 0) return 0;
    const uint8_t *d = data.data;
    int64_t left = data.len;
    int ok = 1;
    while (left > 0) {
        ssize_t w = write(fd, d, left > (1 << 30) ? (size_t)1 << 30 : (size_t)left);
        if (w < 0 && errno == EINTR) continue;
        if (w <= 0) { ok = 0; break; }
        d += w;
        left -= w;
    }
    if (close(fd) != 0) ok = 0;
    return ok;
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
