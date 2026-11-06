/* goosecc: the few C helpers the Goose sources bind with extern fn.
 * Included into the generated C with `goose --include`. */
#include <stdint.h>
#include <string.h>

double goosecc_bits_to_f64(int64_t v) { double d; memcpy(&d, &v, 8); return d; }
int64_t goosecc_f64_to_bits(double d) { int64_t v; memcpy(&v, &d, 8); return v; }
double goosecc_round_f32(double d) { return (double)(float)d; }
