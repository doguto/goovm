/* Driver of gep.ll: an image record with the tables pred4x4 copies between. */
#include <stdio.h>
#include <string.h>

extern char *img;
void pred4x4(int uv, int bx, int by);

int main(void) {
    static char big[16384 + 4 * 4 * 16 * 16 * 2];
    static char modes[64];
    img = big;
    *(char **)(big + 14224) = modes;
    *(int *)(big + 12) = 3;
    modes[3 * 16 + 2] = 2;   /* the mode pred4x4 reads: row 3, byte 2 */
    short *src = (short *)(big + 2048);
    for (int k = 0; k < 4 * 4 * 16 * 16; k++) src[k] = (short)(k * 7 + 1);
    long sum = 0;
    for (int uv = 0; uv < 2; uv++)
        for (int bx = 0; bx < 15; bx += 3)
            for (int by = 0; by < 16; by += 4) {
                pred4x4(uv, bx, by);
                short *dst = (short *)(big + 1024);
                for (int k = 0; k < 4; k++) sum += dst[bx * 16 + by + k] * (k + 1) + dst[(bx + 1) * 16 + by + k];
            }
    printf("%ld\n", sum);
    return 0;
}
