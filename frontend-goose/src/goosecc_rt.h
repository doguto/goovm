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
/* G1: with the runtime's lazy regions (runtime-patches/lazy-regions.patch)
 * a data stack's region becomes accessible on its first access, through
 * the runtime's fault handler; a system call that stores there (read,
 * madvise) would get EFAULT instead. Code that hands the top of a data
 * stack to one, to append there, first writes a zero byte at the top,
 * which does that access (and is harmless without the patch: C may store
 * past the top; a read would map the zero page, and the store after it
 * fault again). */
static inline void goosecc_commit(uint8_t *p) { *(volatile uint8_t *)p = 0; }
void goosecc_prefault(gs_rref a, int64_t bytes) {
    if (bytes > (512 << 10)) bytes = 512 << 10;
    goosecc_commit(a.stk->top);
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
/* B4: the file's stat is kept for its identity, and why a file could not
 * be read (goosecc_last_stat). */
static struct stat goosecc_st;
static int goosecc_load_why;   /* 0 read, 1 no such path, 2 a directory, 3 another reason */
int64_t goosecc_read_file(sl_u8 path, gs_rref out) {
    char p[4096];
    goosecc_load_why = 1;
    if (!goosecc_cpath(path, p, sizeof p)) return 0;
    int fd = open(p, O_RDONLY | O_CLOEXEC);
    if (fd < 0) {
        goosecc_load_why = (errno == ENOENT || errno == ENOTDIR || errno == ENAMETOOLONG || errno == ELOOP) ? 1 : 3;
        return 0;
    }
    struct stat st;
    if (fstat(fd, &st) != 0 || S_ISDIR(st.st_mode)) {
        goosecc_load_why = S_ISDIR(st.st_mode) ? 2 : 3;
        close(fd);
        return 0;
    }
    goosecc_load_why = 3;
    goosecc_st = st;
    int64_t len0 = out.hdr->len;
    uint8_t *top0 = out.stk->top;
    int reg = S_ISREG(st.st_mode), ok = 1, direct = 1;
    goosecc_commit(out.stk->top);
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
#include <stddef.h>
#include <time.h>
#include <stdio.h>

/* Field k of the last stat (goosecc_read_file's fstat or goosecc_stat's
 * stat): 0 device, 1 inode, 2 size, 3 mtime and 4 ctime in nanoseconds
 * since the epoch, 5 whether it is a regular file, 6 why goosecc_read_file
 * failed last (1 no such path, 2 a directory, 3 another reason). */
int64_t goosecc_last_stat(int64_t k) {
    switch (k) {
    case 0: return (int64_t)goosecc_st.st_dev;
    case 1: return (int64_t)goosecc_st.st_ino;
    case 2: return (int64_t)goosecc_st.st_size;
    case 3: return (int64_t)goosecc_st.st_mtim.tv_sec * 1000000000 + goosecc_st.st_mtim.tv_nsec;
    case 4: return (int64_t)goosecc_st.st_ctim.tv_sec * 1000000000 + goosecc_st.st_ctim.tv_nsec;
    case 6: return goosecc_load_why;
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

/* A cache file being used (a manifest read, a blob mapped) whose last use
 * (the later of its modification and access times) is more than an hour
 * old gets both set to now: the eviction deletes the least recently used
 * files first, and access times alone are seldom kept (relatime updates
 * one at the first read after a write and then once a day; noatime
 * never). At most one system call per file and hour. */
static void goosecc_touch_used(int fd, const struct stat *st) {
    struct timespec now;
    clock_gettime(CLOCK_REALTIME, &now);
    time_t last = st->st_mtim.tv_sec > st->st_atim.tv_sec ? st->st_mtim.tv_sec : st->st_atim.tv_sec;
    if (now.tv_sec - last > 3600) futimens(fd, 0);
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
    goosecc_touch_used(fd, &st);
    int64_t size = st.st_size, total = 0;
    if (size > 0) goosecc_commit(out.stk->top);
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

/* A blob being replayed is mapped, not read: reading it into a fresh array
 * costs a page fault per 4 KB, a private read-only mapping of the page
 * cache costs one per 64 KB (fault-around). Goose reads its words through
 * goosecc_mw, which the C compiler inlines into the loops; the caller
 * checks the index against goosecc_map's length first. */
static const uint32_t *goosecc_map_p = 0;
static size_t goosecc_map_bytes = 0;
int64_t goosecc_map(sl_u8 path) {
    char p[4096];
    if (goosecc_map_p) {
        munmap((void *)goosecc_map_p, goosecc_map_bytes);
        goosecc_map_p = 0;
        goosecc_map_bytes = 0;
    }
    if (!goosecc_cpath(path, p, sizeof p)) return -1;
    int fd = open(p, O_RDONLY | O_CLOEXEC);
    if (fd < 0) return -1;
    struct stat st;
    if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode) || st.st_size % 4 != 0 || st.st_size < 32 || st.st_size > ((int64_t)1 << 30)) {
        close(fd);
        return -1;
    }
    goosecc_touch_used(fd, &st);
    void *m = mmap(0, (size_t)st.st_size, PROT_READ, MAP_PRIVATE | MAP_POPULATE, fd, 0);
    close(fd);
    if (m == MAP_FAILED) return -1;
    goosecc_map_p = m;
    goosecc_map_bytes = (size_t)st.st_size;
    return st.st_size / 4;
}
__attribute__((always_inline)) inline uint32_t goosecc_mw(int64_t i) { return goosecc_map_p[i]; }
uint64_t goosecc_mcsum(int64_t from, int64_t to) {
    sl_u32 w;
    w.data = (gs_u32 *)(goosecc_map_p + from);
    w.len = to - from;
    return goosecc_csum(w);
}
/* Appends the n bytes at word i of the mapping to out (the caller checked
 * that they are in it). */
void goosecc_mcopy(gs_rref out, int64_t i, int64_t n) {
    if (n <= 0) return;
    if (n > 8192) goosecc_prefault(out, n);
    memcpy(out.stk->top, (const uint8_t *)(goosecc_map_p + i), (size_t)n);
    out.stk->top += n;
    out.hdr->len += n;
}
int64_t goosecc_meq(int64_t i, sl_u8 s) {
    return memcmp((const uint8_t *)(goosecc_map_p + i), s.data, (size_t)s.len) == 0;
}

/* Appends the n tokens at word i of the mapping (4 words each: kind |
 * flags << 8 | aux << 16, spelling, value, expansion location) to out,
 * relocated as hcache.goose's rl and lm do: a source offset below 2^31 is
 * in the unit's text (s0 plus it, at most srclen), others index anchors;
 * the value of an identifier token (kind 2, 8 (a parameter) or >= kwmin)
 * indexes ids. 1, or 0 when a value is out of range (out then has some of
 * them: the caller takes them back). */
_Static_assert(sizeof(Tok_g) == 16 && offsetof(Tok_g, spell_g) == 4 && offsetof(Tok_g, val_g) == 8 &&
               offsetof(Tok_g, xloc_g) == 12, "hcache: the layout of Tok");
int64_t goosecc_reloc_toks(gs_rref out, int64_t i, int64_t n, sl_u32 ids, sl_u32 anchors, int64_t s0, int64_t srclen, int64_t kwmin) {
    if (n <= 0) return 1;
    if (n * 16 > 8192) goosecc_prefault(out, n * 16);
    const uint32_t *w = goosecc_map_p + i;
    Tok_g *o = (Tok_g *)out.stk->top;
    int64_t k;
    for (k = 0; k < n; k++, w += 4) {
        uint32_t a = w[0], kind = a & 255, sp = w[1], v = w[2], xl = w[3];
        if (sp < 0x80000000u) {
            if (sp > srclen) break;
            sp = (uint32_t)(s0 + sp);
        } else {
            if ((int64_t)(sp & 0x7fffffffu) >= anchors.len) break;
            sp = anchors.data[sp & 0x7fffffffu];
        }
        if (xl < 0x80000000u) {
            if (xl > srclen) break;
            xl = (uint32_t)(s0 + xl);
        } else {
            if ((int64_t)(xl & 0x7fffffffu) >= anchors.len) break;
            xl = anchors.data[xl & 0x7fffffffu];
        }
        if (kind == 2 || kind == 8 || (int64_t)kind >= kwmin) {
            if ((int64_t)v >= ids.len) break;
            v = ids.data[v];
        }
        o[k].kind_g = (uint8_t)kind;
        o[k].flags_g = (uint8_t)(a >> 8);
        o[k].aux_g = (uint16_t)(a >> 16);
        o[k].spell_g = sp;
        o[k].val_g = v;
        o[k].xloc_g = xl;
    }
    out.stk->top += k * 16;
    out.hdr->len += k;
    return k == n;
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

static int64_t goosecc_write_all(int fd, const uint8_t *d, int64_t left) {
    while (left > 0) {
        ssize_t n = write(fd, d, (size_t)left);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) return 0;
        d += n;
        left -= n;
    }
    return 1;
}
/* Appends the words w to the file at path in one write (O_APPEND: other
 * appenders cannot interleave with it): 1, 2 when there is no such file,
 * 0 on another error. */
int64_t goosecc_append_words(sl_u8 path, sl_u32 w) {
    char p[4096];
    if (!goosecc_cpath(path, p, sizeof p)) return 0;
    int fd = open(p, O_WRONLY | O_APPEND | O_CLOEXEC);
    if (fd < 0) return errno == ENOENT ? 2 : 0;
    int64_t ok = goosecc_write_all(fd, (const uint8_t *)w.data, w.len * 4);
    if (close(fd) != 0) ok = 0;
    return ok;
}
/* Creates the file at path with the words w (O_EXCL), creating missing
 * directories: 1, 2 when it exists, 0 on another error. */
int64_t goosecc_create_words(sl_u8 path, sl_u32 w) {
    char p[4096];
    if (!goosecc_cpath(path, p, sizeof p)) return 0;
    int fd = open(p, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0666);
    if (fd < 0 && errno == ENOENT) {
        goosecc_mkdirs(p);
        fd = open(p, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0666);
    }
    if (fd < 0) return errno == EEXIST ? 2 : 0;
    int64_t ok = goosecc_write_all(fd, (const uint8_t *)w.data, w.len * 4);
    if (close(fd) != 0) ok = 0;
    return ok;
}

/* A blob is written in three pieces without copying them together: the
 * head's words, the source text (bytes, padded to whole words with
 * zeros) and the rest's words. goosecc_csum3 is goosecc_csum of the words
 * of the three in a row (from the head's word 5), goosecc_write3 writes
 * them as goosecc_write_words does. */
typedef struct { uint64_t a, b, c, d; int64_t i; uint8_t buf[32]; int nb; } goosecc_cs;
static void goosecc_cs_chunk(goosecc_cs *st, const uint8_t *q) {
    const uint64_t K = 0xff51afd7ed558ccdull;
    uint64_t x0, x1, x2, x3;
    memcpy(&x0, q, 8); memcpy(&x1, q + 8, 8); memcpy(&x2, q + 16, 8); memcpy(&x3, q + 24, 8);
    st->a = (st->a ^ x0) * K; st->b = (st->b ^ x1) * K; st->c = (st->c ^ x2) * K; st->d = (st->d ^ x3) * K;
    st->i += 8;
}
/* Feeds n bytes (a whole number of words, except at the very end). */
static void goosecc_cs_feed(goosecc_cs *st, const uint8_t *p, int64_t n) {
    while (n > 0 && st->nb > 0) {
        st->buf[st->nb++] = *p++;
        n--;
        if (st->nb == 32) { goosecc_cs_chunk(st, st->buf); st->nb = 0; }
    }
    while (n >= 32) { goosecc_cs_chunk(st, p); p += 32; n -= 32; }
    while (n > 0) { st->buf[st->nb++] = *p++; n--; }
}
static uint64_t goosecc_cs_end(goosecc_cs *st) {
    const uint64_t K = 0xff51afd7ed558ccdull;
    while (st->nb % 4) st->buf[st->nb++] = 0;
    int64_t n = st->i + st->nb / 4;
    uint64_t a = st->a;
    for (int k = 0; k < st->nb / 4; k++) {
        uint32_t w;
        memcpy(&w, st->buf + 4 * k, 4);
        a = (a ^ w ^ ((uint64_t)(st->i + k) << 32)) * K;
    }
    uint64_t h = a ^ (st->b * 0x9e3779b97f4a7c15ull) ^ (st->c * 0xc2b2ae3d27d4eb4full) ^ (st->d * 0x165667b19e3779f9ull) ^ (uint64_t)n;
    h ^= h >> 33; h *= K; h ^= h >> 29; h *= 0xc4ceb9fe1a85ec53ull; h ^= h >> 32;
    return h;
}
uint64_t goosecc_csum3(sl_u32 a, sl_u8 s, sl_u32 b) {
    goosecc_cs st = { 0x9e3779b97f4a7c15ull, 0xc2b2ae3d27d4eb4full, 0x165667b19e3779f9ull, 0x27d4eb2f165667c5ull, 0, {0}, 0 };
    static const uint8_t zero[4];
    goosecc_cs_feed(&st, (const uint8_t *)a.data, a.len * 4);
    goosecc_cs_feed(&st, s.data, s.len);
    goosecc_cs_feed(&st, zero, (4 - s.len % 4) % 4);
    goosecc_cs_feed(&st, (const uint8_t *)b.data, b.len * 4);
    return goosecc_cs_end(&st);
}
int64_t goosecc_write3(sl_u8 path, sl_u32 a, sl_u8 s, sl_u32 b) {
    char p[4096], t[4200];
    static unsigned long seq3;
    static const uint8_t zero[4];
    if (!goosecc_cpath(path, p, sizeof p)) return 0;
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    snprintf(t, sizeof t, "%s.%d.%lx.%lx.tmp", p, (int)getpid(), (unsigned long)ts.tv_nsec, ++seq3);
    int fd = open(t, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0666);
    if (fd < 0 && errno == ENOENT) {
        goosecc_mkdirs(t);
        fd = open(t, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0666);
    }
    if (fd < 0) return 0;
    int64_t ok = goosecc_write_all(fd, (const uint8_t *)a.data, a.len * 4) && goosecc_write_all(fd, s.data, s.len) &&
                 goosecc_write_all(fd, zero, (4 - s.len % 4) % 4) && goosecc_write_all(fd, (const uint8_t *)b.data, b.len * 4);
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

/* Eviction: when the files in dir take more than limit bytes, the least
 * recently used are deleted until they take at most 3/4 of it. A file's
 * last use is the later of its modification and access times (written,
 * appended to, or touched by goosecc_touch_used when it was used more
 * than an hour after its last use). Temporary files older than an hour
 * (left by a killed compiler) are deleted as well. Returns the bytes that
 * remain. */
struct goosecc_ent { int64_t mtime; int64_t size; char name[64]; };
static int goosecc_ent_cmp(const void *a, const void *b) {
    const struct goosecc_ent *x = a, *y = b;
    return x->mtime < y->mtime ? -1 : x->mtime > y->mtime;
}
int64_t goosecc_evict(sl_u8 dir, int64_t limit) {
    char p[4096];
    if (!goosecc_cpath(dir, p, sizeof p)) return -1;
    DIR *d = opendir(p);
    if (!d) return -1;
    struct goosecc_ent *v = 0;
    size_t n = 0, cap = 0;
    int64_t total = 0;
    struct timespec now;
    clock_gettime(CLOCK_REALTIME, &now);
    struct dirent *fe;
    while ((fe = readdir(d)) != 0) {
        if (fe->d_name[0] == '.' || strlen(fe->d_name) >= 64) continue;
        char f[4200];
        snprintf(f, sizeof f, "%s/%s", p, fe->d_name);
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
        int64_t mt = (int64_t)st.st_mtim.tv_sec * 1000000000 + st.st_mtim.tv_nsec;
        int64_t at = (int64_t)st.st_atim.tv_sec * 1000000000 + st.st_atim.tv_nsec;
        v[n].mtime = at > mt ? at : mt;
        v[n].size = (int64_t)st.st_blocks * 512;
        strcpy(v[n].name, fe->d_name);
        total += v[n].size;
        n++;
    }
    closedir(d);
    if (total > limit && n > 0) {
        qsort(v, n, sizeof *v, goosecc_ent_cmp);
        for (size_t i = 0; i < n && total > limit / 4 * 3; i++) {
            char f[4200];
            snprintf(f, sizeof f, "%s/%s", p, v[i].name);
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
