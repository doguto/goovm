// exit() from a nested call and a computed exit status.
#include <stdio.h>
#include <stdlib.h>

static void check(int v) {
    if (v > 40) {
        printf("exiting at %d\n", v);
        fflush(stdout);
        exit(v - 37);
    }
}

int main(void) {
    int s = 0;
    for (int i = 0; i < 100; i++) {
        s += i;
        check(s);
    }
    return 1;
}
