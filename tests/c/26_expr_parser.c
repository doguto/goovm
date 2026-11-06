// Recursive-descent expression evaluator over strings.
#include <stdio.h>
#include <ctype.h>

static const char *p;
static long expr(void);
static void skip(void) { while (*p == ' ') p++; }
static long primary(void) {
    skip();
    if (*p == '(') { p++; long v = expr(); skip(); if (*p == ')') p++; return v; }
    if (*p == '-') { p++; return -primary(); }
    long v = 0;
    while (isdigit((unsigned char)*p)) v = v * 10 + (*p++ - '0');
    return v;
}
static long term(void) {
    long v = primary();
    for (;;) {
        skip();
        char op = *p;
        if (op != '*' && op != '/' && op != '%') return v;
        p++;
        long r = primary();
        v = op == '*' ? v * r : op == '/' ? (r ? v / r : 0) : (r ? v % r : 0);
    }
}
static long expr(void) {
    long v = term();
    for (;;) {
        skip();
        if (*p == '+') { p++; v += term(); }
        else if (*p == '-') { p++; v -= term(); }
        else return v;
    }
}
static long eval(const char *s) { p = s; return expr(); }

int main(void) {
    const char *tests[] = {"1+2*3", "(1+2)*3", "100/7", "-100/7", "100%7", "-100%7", "2*(3+4)*(5-6)",
                           "((((1))))", "1-2-3-4", "10*-3", "123456789*1000", "7/(3-3)", " 42 "};
    for (unsigned i = 0; i < sizeof tests / sizeof *tests; i++) printf("%s = %ld\n", tests[i], eval(tests[i]));
    return 0;
}
