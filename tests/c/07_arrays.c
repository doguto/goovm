// Local and global arrays, 2-D arrays, sorting, searching.
#include <stdio.h>

int garr[10] = {9, 3, 7, 1, 8, 2, 6, 4, 5, 0};
static short gs[3][4] = {{1, 2, 3, 4}, {5, 6, 7, 8}, {9, 10, 11, 12}};
long big[1000];

static void bubble(int *a, int n) {
    for (int i = 0; i < n; i++)
        for (int j = 0; j + 1 < n - i; j++)
            if (a[j] > a[j + 1]) { int t = a[j]; a[j] = a[j + 1]; a[j + 1] = t; }
}
static int bsearch_i(const int *a, int n, int key) {
    int lo = 0, hi = n - 1;
    while (lo <= hi) {
        int mid = lo + (hi - lo) / 2;
        if (a[mid] == key) return mid;
        if (a[mid] < key) lo = mid + 1; else hi = mid - 1;
    }
    return -1;
}

int main(void) {
    bubble(garr, 10);
    for (int i = 0; i < 10; i++) printf("%d ", garr[i]);
    printf("\nfind %d %d\n", bsearch_i(garr, 10, 7), bsearch_i(garr, 10, 42));
    int m[5][7];
    for (int i = 0; i < 5; i++)
        for (int j = 0; j < 7; j++) m[i][j] = i * 10 + j;
    int tr = 0;
    for (int i = 0; i < 5; i++) tr += m[i][i] * m[4 - i][6 - i];
    printf("m %d %d\n", tr, m[3][5]);
    int s = 0;
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 4; j++) s += gs[i][j] * (i + 1);
    printf("gs %d\n", s);
    for (int i = 0; i < 1000; i++) big[i] = (long)i * i - 500;
    long acc = 0;
    for (int i = 999; i >= 0; i -= 3) acc += big[i];
    printf("big %ld\n", acc);
    char str[16];
    for (int i = 0; i < 15; i++) str[i] = 'a' + (i * 7) % 26;
    str[15] = 0;
    printf("str %s\n", str);
    unsigned char hist[256] = {0};
    for (int i = 0; i < 1000; i++) hist[(i * 131) & 255]++;
    int nz = 0;
    for (int i = 0; i < 256; i++) nz += hist[i] != 0;
    printf("hist %d %d\n", nz, hist[131]);
    long long idx = 7;
    printf("idx %d %d\n", garr[idx], garr[idx - 5]);
    return 0;
}
