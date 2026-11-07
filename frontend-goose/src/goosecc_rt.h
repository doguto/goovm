/* goosecc: the few C helpers the Goose sources bind with extern fn.
 * Included into the generated C with `goose --include`. */
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>

double goosecc_bits_to_f64(int64_t v) { double d; memcpy(&d, &v, 8); return d; }
int64_t goosecc_f64_to_bits(double d) { int64_t v; memcpy(&v, &d, 8); return v; }
double goosecc_round_f32(double d) { return (double)(float)d; }

/* B3: the identifier hash and the lexer's scans, 8 and 16 bytes at a time.
 *
 * The hash of s[0..n) (common.goose's hash_bytes, and tools/gen_tables.py's
 * for the static tables): each 8 bytes as a little-endian word w, the last
 * one holding what remains (1 to 8 bytes, zero-extended), h = (h ^ w) * K;
 * then h is mixed so that every byte reaches the low bits the tables index
 * with. It reads only s[0..n). */
static inline uint32_t goosecc_hash_mem(const uint8_t *s, int64_t n) {
    const uint64_t K = 0xff51afd7ed558ccdull;
    uint64_t h = 0x9e3779b97f4a7c15ull, w;
    if (n >= 8) {
        const uint8_t *e = s + n;
        while (e - s > 8) {
            memcpy(&w, s, 8);
            h = (h ^ w) * K;
            s += 8;
        }
        memcpy(&w, e - 8, 8);
        w >>= 8 * (8 - (e - s));
        h = (h ^ w) * K;
    } else if (n >= 4) {
        uint32_t a, b;
        memcpy(&a, s, 4);
        memcpy(&b, s + n - 4, 4);
        w = (uint64_t)a | ((uint64_t)b << (8 * (n - 4)));
        h = (h ^ w) * K;
    } else if (n > 0) {
        w = (uint64_t)s[0] | ((uint64_t)s[n >> 1] << (8 * (n >> 1))) | ((uint64_t)s[n - 1] << (8 * (n - 1)));
        h = (h ^ w) * K;
    }
    h ^= h >> 32;
    h *= K;
    h ^= h >> 29;
    return (uint32_t)h;
}
uint32_t goosecc_hash(sl_u8 s) { return goosecc_hash_mem(s.data, s.len); }

#if defined(__SSE2__)
#include <emmintrin.h>
#endif
/* lex.goose's CC_IDCONT: [0-9A-Za-z_$] and the bytes >= 0x80. */
static inline int goosecc_isid(uint8_t c) {
    return (uint8_t)((c | 0x20) - 'a') < 26 || (uint8_t)(c - '0') < 10 || c == '_' || c == '$' || c >= 0x80;
}
/* The run of identifier characters at s[p..]: its length << 32 | its hash.
 * 16 bytes at a time while they are inside s. */
__attribute__((always_inline)) inline uint64_t goosecc_ident_scan(sl_u8 s, int64_t p) {
    const uint8_t *d = s.data;
    int64_t q = p, len = s.len;
#if defined(__SSE2__)
    while (q + 16 <= len) {
        __m128i v = _mm_loadu_si128((const __m128i *)(d + q));
        __m128i l = _mm_or_si128(v, _mm_set1_epi8(0x20));
        __m128i alpha = _mm_cmplt_epi8(_mm_add_epi8(l, _mm_set1_epi8((char)(128 - 'a'))), _mm_set1_epi8((char)(-128 + 26)));
        __m128i digit = _mm_cmplt_epi8(_mm_add_epi8(v, _mm_set1_epi8((char)(128 - '0'))), _mm_set1_epi8((char)(-128 + 10)));
        __m128i us = _mm_or_si128(_mm_cmpeq_epi8(v, _mm_set1_epi8('_')), _mm_cmpeq_epi8(v, _mm_set1_epi8('$')));
        unsigned m = (unsigned)_mm_movemask_epi8(_mm_or_si128(_mm_or_si128(alpha, digit), us)) | (unsigned)_mm_movemask_epi8(v);
        if (m != 0xFFFF) {
            q += __builtin_ctz(~m);
            return ((uint64_t)(q - p) << 32) | goosecc_hash_mem(d + p, q - p);
        }
        q += 16;
    }
#endif
    while (q < len && goosecc_isid(d[q])) q++;
    return ((uint64_t)(q - p) << 32) | goosecc_hash_mem(d + p, q - p);
}
/* The first i >= p with s[i] one of \n / " ' \ NUL (what skipping a line of
 * a group that is not processed must look at), or s.len. */
int64_t goosecc_skip_text(sl_u8 s, int64_t p) {
    const uint8_t *d = s.data;
    int64_t len = s.len;
#if defined(__SSE2__)
    while (p + 16 <= len) {
        __m128i v = _mm_loadu_si128((const __m128i *)(d + p));
        __m128i x = _mm_or_si128(_mm_or_si128(_mm_cmpeq_epi8(v, _mm_set1_epi8('\n')), _mm_cmpeq_epi8(v, _mm_set1_epi8('/'))),
                                 _mm_or_si128(_mm_cmpeq_epi8(v, _mm_set1_epi8('"')), _mm_cmpeq_epi8(v, _mm_set1_epi8('\''))));
        x = _mm_or_si128(x, _mm_or_si128(_mm_cmpeq_epi8(v, _mm_set1_epi8('\\')), _mm_cmpeq_epi8(v, _mm_setzero_si128())));
        unsigned m = (unsigned)_mm_movemask_epi8(x);
        if (m) return p + __builtin_ctz(m);
        p += 16;
    }
#endif
    while (p < len) {
        uint8_t c = d[p];
        if (c == '\n' || c == '/' || c == '"' || c == '\'' || c == '\\' || c == 0) return p;
        p++;
    }
    return len;
}

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
/* B4: the file's stat is kept for its identity (goosecc_last_stat). */
static struct stat goosecc_st;
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
    goosecc_st = st;
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

/* B4: the persistent header cache (hcache.goose). The cache's files are
 * arrays of 32-bit little-endian words; Goose builds and parses them as
 * u32 arrays, and these helpers move them to and from the file system. */
#include <dirent.h>
#include <time.h>
#include <stdio.h>

/* Field k of the last stat (goosecc_read_file's fstat or goosecc_stat's
 * stat): 0 device, 1 inode, 2 size, 3 mtime and 4 ctime in nanoseconds
 * since the epoch, 5 whether it is a regular file. */
int64_t goosecc_last_stat(int64_t k) {
    switch (k) {
    case 0: return (int64_t)goosecc_st.st_dev;
    case 1: return (int64_t)goosecc_st.st_ino;
    case 2: return (int64_t)goosecc_st.st_size;
    case 3: return (int64_t)goosecc_st.st_mtim.tv_sec * 1000000000 + goosecc_st.st_mtim.tv_nsec;
    case 4: return (int64_t)goosecc_st.st_ctim.tv_sec * 1000000000 + goosecc_st.st_ctim.tv_nsec;
    default: return S_ISREG(goosecc_st.st_mode) ? 1 : 0;
    }
}

/* stat(path), what goosecc_read_file would make of it: 0 when it cannot
 * be opened (no such file, a component that is not a directory, no
 * permission to search: stat fails wherever open would), 1 a regular file,
 * 2 a directory (which goosecc_read_file refuses), 3 another kind, -1 a
 * transient error. The fields go to goosecc_last_stat. */
int64_t goosecc_stat(sl_u8 path) {
    char p[4096];
    if (!goosecc_cpath(path, p, sizeof p)) return 0;
    if (stat(p, &goosecc_st) != 0) return (errno == ENOMEM || errno == EIO || errno == EINTR) ? -1 : 0;
    if (S_ISREG(goosecc_st.st_mode)) return 1;
    if (S_ISDIR(goosecc_st.st_mode)) return 2;
    return 3;
}

/* A 64-bit checksum of the words w: four multiply-xor lanes (each step a
 * bijection of the lane, so any change of one word changes the lane),
 * then mixed. */
uint64_t goosecc_csum(sl_u32 w) {
    const uint64_t K = 0xff51afd7ed558ccdull;
    const uint32_t *p = w.data;
    int64_t n = w.len, i = 0;
    uint64_t a = 0x9e3779b97f4a7c15ull, b = 0xc2b2ae3d27d4eb4full, c = 0x165667b19e3779f9ull, d = 0x27d4eb2f165667c5ull;
    for (; i + 8 <= n; i += 8) {
        uint64_t x0, x1, x2, x3;
        memcpy(&x0, p + i, 8); memcpy(&x1, p + i + 2, 8); memcpy(&x2, p + i + 4, 8); memcpy(&x3, p + i + 6, 8);
        a = (a ^ x0) * K; b = (b ^ x1) * K; c = (c ^ x2) * K; d = (d ^ x3) * K;
    }
    for (; i < n; i++) a = (a ^ p[i] ^ ((uint64_t)i << 32)) * K;
    uint64_t h = a ^ (b * 0x9e3779b97f4a7c15ull) ^ (c * 0xc2b2ae3d27d4eb4full) ^ (d * 0x165667b19e3779f9ull) ^ (uint64_t)n;
    h ^= h >> 33; h *= K; h ^= h >> 29; h *= 0xc4ceb9fe1a85ec53ull; h ^= h >> 32;
    return h;
}
uint64_t goosecc_csum_bytes(sl_u8 s) {
    const uint64_t K = 0xff51afd7ed558ccdull;
    uint64_t h = 0x9e3779b97f4a7c15ull ^ (uint64_t)s.len, x;
    int64_t i = 0;
    for (; i + 8 <= s.len; i += 8) { memcpy(&x, s.data + i, 8); h = (h ^ x) * K; h ^= h >> 29; }
    for (; i < s.len; i++) h = (h ^ s.data[i]) * K;
    h ^= h >> 33; h *= K; h ^= h >> 29;
    return h;
}

/* Appends the bytes s to the word array out, zero-padded to whole words. */
void goosecc_bytes_to_words(gs_rref out, sl_u8 s) {
    int64_t nw = (s.len + 3) / 4;
    if (nw == 0) return;
    uint8_t *top = out.stk->top;
    memset(top + (nw * 4 - 4), 0, 4);
    memcpy(top, s.data, (size_t)s.len);
    out.stk->top += nw * 4;
    out.hdr->len += nw;
}
/* Appends n bytes from the word array w, starting at word i, to out: 1, or
 * 0 if they are not all in w. */
int64_t goosecc_words_to_bytes(gs_rref out, sl_u32 w, int64_t i, int64_t n) {
    if (i < 0 || n < 0 || i > w.len || n > (w.len - i) * 4) return 0;
    if (n > 8192) goosecc_prefault(out, n);
    memcpy(out.stk->top, (const uint8_t *)(w.data + i), (size_t)n);
    out.stk->top += n;
    out.hdr->len += n;
    return 1;
}
/* Whether the n bytes at word i of w are s. */
int64_t goosecc_words_eq(sl_u32 w, int64_t i, sl_u8 s) {
    if (i < 0 || i > w.len || s.len > (w.len - i) * 4) return 0;
    return memcmp((const uint8_t *)(w.data + i), s.data, (size_t)s.len) == 0;
}
/* The hash_bytes (goosecc_hash) of the n bytes at word i of w. */
uint32_t goosecc_words_hash(sl_u32 w, int64_t i, int64_t n) {
    if (i < 0 || n < 0 || i > w.len || n > (w.len - i) * 4) return 0;
    return goosecc_hash_mem((const uint8_t *)(w.data + i), n);
}

/* Appends the file at path to the word array out (its size must be a
 * multiple of 4): the number of words, or -1. */
int64_t goosecc_read_words(sl_u8 path, gs_rref out) {
    char p[4096];
    if (!goosecc_cpath(path, p, sizeof p)) return -1;
    int fd = open(p, O_RDONLY | O_CLOEXEC);
    if (fd < 0) return -1;
    struct stat st;
    if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode) || st.st_size % 4 != 0 || st.st_size > ((int64_t)1 << 30)) {
        close(fd);
        return -1;
    }
    int64_t size = st.st_size, total = 0;
    if (size > 8192) goosecc_prefault(out, size);
    while (total < size) {
        ssize_t n = read(fd, out.stk->top + total, (size_t)(size - total));
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) break;
        total += n;
    }
    close(fd);
    if (total != size) return -1;
    out.stk->top += size;
    out.hdr->len += size / 4;
    return size / 4;
}

/* Creates the missing directories of the path p (its last component is a
 * file); errors are left to the open that follows. */
static void goosecc_mkdirs(char *p) {
    for (char *s = p + 1; *s; s++) {
        if (*s != '/') continue;
        *s = 0;
        mkdir(p, 0777);
        *s = '/';
    }
}
/* Writes the words w to path atomically: a new file beside it (named by
 * the process and the time), renamed over path, so that a reader sees
 * the old file or the whole new one. Missing directories are created.
 * 1 on success. */
int64_t goosecc_write_words(sl_u8 path, sl_u32 w) {
    char p[4096], t[4200];
    static unsigned long seq;
    if (!goosecc_cpath(path, p, sizeof p)) return 0;
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    snprintf(t, sizeof t, "%s.%d.%lx.%lx.tmp", p, (int)getpid(), (unsigned long)ts.tv_nsec, ++seq);
    int fd = open(t, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0666);
    if (fd < 0 && errno == ENOENT) {
        goosecc_mkdirs(t);
        fd = open(t, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0666);
    }
    if (fd < 0) return 0;
    const uint8_t *d = (const uint8_t *)w.data;
    int64_t left = w.len * 4;
    int ok = 1;
    while (left > 0) {
        ssize_t n = write(fd, d, (size_t)left);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) { ok = 0; break; }
        d += n;
        left -= n;
    }
    if (close(fd) != 0) ok = 0;
    if (!ok || rename(t, p) != 0) {
        unlink(t);
        return 0;
    }
    return 1;
}

/* Deletes a file of the cache (a corrupt one). */
void goosecc_unlink(sl_u8 path) {
    char p[4096];
    if (goosecc_cpath(path, p, sizeof p)) unlink(p);
}

/* Eviction: when the files under dir (one level of subdirectories) take
 * more than limit bytes, the oldest (by modification time) are deleted
 * until they take at most 3/4 of it. Temporary files older than an hour
 * (left by a killed compiler) are deleted as well. Returns the bytes that
 * remain. */
struct goosecc_ent { int64_t mtime; int64_t size; char name[64]; char sub[16]; };
static int goosecc_ent_cmp(const void *a, const void *b) {
    const struct goosecc_ent *x = a, *y = b;
    return x->mtime < y->mtime ? -1 : x->mtime > y->mtime;
}
int64_t goosecc_evict(sl_u8 dir, int64_t limit) {
    char p[4096], q[4300];
    if (!goosecc_cpath(dir, p, sizeof p)) return -1;
    DIR *top = opendir(p);
    if (!top) return -1;
    struct goosecc_ent *v = 0;
    size_t n = 0, cap = 0;
    int64_t total = 0;
    struct timespec now;
    clock_gettime(CLOCK_REALTIME, &now);
    struct dirent *de;
    while ((de = readdir(top)) != 0) {
        if (de->d_name[0] == '.' || strlen(de->d_name) >= 16) continue;
        snprintf(q, sizeof q, "%s/%s", p, de->d_name);
        DIR *sub = opendir(q);
        if (!sub) continue;
        struct dirent *fe;
        while ((fe = readdir(sub)) != 0) {
            if (fe->d_name[0] == '.' || strlen(fe->d_name) >= 64) continue;
            char f[4400];
            snprintf(f, sizeof f, "%s/%s", q, fe->d_name);
            struct stat st;
            if (stat(f, &st) != 0 || !S_ISREG(st.st_mode)) continue;
            size_t ln = strlen(fe->d_name);
            if (ln > 4 && strcmp(fe->d_name + ln - 4, ".tmp") == 0) {
                if (now.tv_sec - st.st_mtim.tv_sec > 3600) unlink(f);
                continue;
            }
            if (n == cap) {
                cap = cap ? cap * 2 : 1024;
                struct goosecc_ent *nv = realloc(v, cap * sizeof *v);
                if (!nv) break;
                v = nv;
            }
            v[n].mtime = (int64_t)st.st_mtim.tv_sec * 1000000000 + st.st_mtim.tv_nsec;
            v[n].size = (int64_t)st.st_blocks * 512;
            strcpy(v[n].name, fe->d_name);
            strcpy(v[n].sub, de->d_name);
            total += v[n].size;
            n++;
        }
        closedir(sub);
    }
    closedir(top);
    if (total > limit && n > 0) {
        qsort(v, n, sizeof *v, goosecc_ent_cmp);
        for (size_t i = 0; i < n && total > limit / 4 * 3; i++) {
            char f[4400];
            snprintf(f, sizeof f, "%s/%s/%s", p, v[i].sub, v[i].name);
            if (unlink(f) == 0) total -= v[i].size;
        }
    }
    free(v);
    return total;
}

/* The identity of this build of goosecc (build.sh passes a hash of the
 * generated C), part of the cache's configuration key. */
#ifndef GOOSECC_BUILD_ID
#define GOOSECC_BUILD_ID 0
#endif
uint64_t goosecc_build_id(void) { return (uint64_t)GOOSECC_BUILD_ID; }
int64_t goosecc_pid(void) { return (int64_t)getpid(); }
