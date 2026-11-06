/* goosecc: the few C helpers the Goose sources bind with extern fn.
 * Included into the generated C with `goose --include`. */
#include <stdint.h>
#include <string.h>

double goosecc_bits_to_f64(int64_t v) { double d; memcpy(&d, &v, 8); return d; }
int64_t goosecc_f64_to_bits(double d) { int64_t v; memcpy(&v, &d, 8); return v; }
double goosecc_round_f32(double d) { return (double)(float)d; }
int64_t goosecc_find_byte(sl_u8 s, uint8_t c) {
    const uint8_t *p = (const uint8_t *)memchr(s.data, c, (size_t)s.len);
    return p ? (int64_t)(p - s.data) : -1;
}
