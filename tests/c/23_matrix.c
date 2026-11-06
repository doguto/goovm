// Integer matrix multiply, transpose, determinant by cofactors.
#include <stdio.h>

#define N 6
static long A[N][N], B[N][N], C[N][N];

static void mul(long (*a)[N], long (*b)[N], long (*c)[N]) {
    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++) {
            long s = 0;
            for (int k = 0; k < N; k++) s += a[i][k] * b[k][j];
            c[i][j] = s;
        }
}
static long det(long m[][N], int n) {
    if (n == 1) return m[0][0];
    long sub[N][N], d = 0;
    for (int c = 0; c < n; c++) {
        for (int i = 1; i < n; i++)
            for (int j = 0, k = 0; j < n; j++)
                if (j != c) sub[i - 1][k++] = m[i][j];
        long s = det(sub, n - 1);
        d += (c % 2 ? -1 : 1) * m[0][c] * s;
    }
    return d;
}

int main(void) {
    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++) { A[i][j] = (i * 7 + j * 3) % 11 - 5; B[i][j] = (i == j) * 2 + (i + j) % 3; }
    mul(A, B, C);
    long tr = 0;
    for (int i = 0; i < N; i++) tr += C[i][i];
    printf("trace %ld C[2][3] %ld\n", tr, C[2][3]);
    long T[N][N];
    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++) T[j][i] = C[i][j];
    printf("T %ld %ld\n", T[3][2], T[0][5]);
    printf("det A %ld det B %ld det C %ld\n", det(A, N), det(B, N), det(C, 4));
    return 0;
}
