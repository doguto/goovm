// Linkage: static functions and variables, extern declarations, weak
// definitions, tentative definitions, static locals in several functions.
#include <stdio.h>

static int hidden = 5;
int visible = 6;
int tentative;
extern int visible;
__attribute__((weak)) int weak_var = 11;
__attribute__((weak)) int weak_fn(int x) { return x * 3; }
static int helper(int x) { static int calls; calls++; return x + calls; }
int exported(int x) { static int calls = 10; calls++; return x * calls; }
static const char *const msg = "linkage";

int main(void) {
    tentative = helper(1) + helper(1);
    printf("%d %d %d %d\n", hidden, visible, tentative, weak_var);
    printf("%d %d %d\n", weak_fn(4), exported(2), exported(2));
    printf("%s %d\n", msg, helper(0));
    return 0;
}
