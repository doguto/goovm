// Quicksort, merge sort, insertion sort, heap sort on the same data.
#include <stdio.h>

#define N 200
static int src[N], tmp[N];

static void quick(int *a, int lo, int hi) {
    if (lo >= hi) return;
    int p = a[(lo + hi) / 2], i = lo, j = hi;
    while (i <= j) {
        while (a[i] < p) i++;
        while (a[j] > p) j--;
        if (i <= j) { int t = a[i]; a[i] = a[j]; a[j] = t; i++; j--; }
    }
    quick(a, lo, j);
    quick(a, i, hi);
}
static void merge_sort(int *a, int n) {
    if (n < 2) return;
    int h = n / 2;
    merge_sort(a, h);
    merge_sort(a + h, n - h);
    int i = 0, j = h, k = 0;
    while (i < h && j < n) tmp[k++] = a[i] <= a[j] ? a[i++] : a[j++];
    while (i < h) tmp[k++] = a[i++];
    while (j < n) tmp[k++] = a[j++];
    for (k = 0; k < n; k++) a[k] = tmp[k];
}
static void insertion(int *a, int n) {
    for (int i = 1; i < n; i++) {
        int v = a[i], j = i - 1;
        while (j >= 0 && a[j] > v) { a[j + 1] = a[j]; j--; }
        a[j + 1] = v;
    }
}
static void sift(int *a, int i, int n) {
    for (;;) {
        int l = 2 * i + 1, r = l + 1, m = i;
        if (l < n && a[l] > a[m]) m = l;
        if (r < n && a[r] > a[m]) m = r;
        if (m == i) return;
        int t = a[i]; a[i] = a[m]; a[m] = t;
        i = m;
    }
}
static void heap(int *a, int n) {
    for (int i = n / 2 - 1; i >= 0; i--) sift(a, i, n);
    for (int e = n - 1; e > 0; e--) { int t = a[0]; a[0] = a[e]; a[e] = t; sift(a, 0, e); }
}
static unsigned check(const int *a) {
    unsigned h = 0;
    for (int i = 0; i < N; i++) { if (i && a[i - 1] > a[i]) return 0; h = h * 33 + (unsigned)a[i]; }
    return h;
}

int main(void) {
    unsigned s = 12345;
    for (int i = 0; i < N; i++) { s = s * 1103515245u + 12345u; src[i] = (int)(s >> 16) % 1000 - 500; }
    int a[N];
    for (int k = 0; k < 4; k++) {
        for (int i = 0; i < N; i++) a[i] = src[i];
        if (k == 0) quick(a, 0, N - 1);
        if (k == 1) merge_sort(a, N);
        if (k == 2) insertion(a, N);
        if (k == 3) heap(a, N);
        printf("sort%d %u %d %d\n", k, check(a), a[0], a[N - 1]);
    }
    return 0;
}
