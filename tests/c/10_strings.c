// Strings: hand-written and libc string functions.
#include <stdio.h>
#include <string.h>
#include <ctype.h>

static size_t my_strlen(const char *s) { const char *p = s; while (*p) p++; return (size_t)(p - s); }
static void my_strcpy(char *d, const char *s) { while ((*d++ = *s++)) {} }
static void reverse(char *s) {
    size_t n = my_strlen(s);
    for (size_t i = 0; i < n / 2; i++) { char t = s[i]; s[i] = s[n - 1 - i]; s[n - 1 - i] = t; }
}
static int count_words(const char *s) {
    int n = 0, in = 0;
    for (; *s; s++) {
        if (*s == ' ' || *s == '\t') in = 0;
        else if (!in) { in = 1; n++; }
    }
    return n;
}
static const char *greeting = "hello, world";
static char gbuf[64] = "initial";

int main(void) {
    char b[64];
    my_strcpy(b, greeting);
    printf("%s %zu %zu\n", b, my_strlen(b), strlen(greeting));
    reverse(b);
    printf("%s\n", b);
    printf("cmp %d %d %d\n", strcmp("abc", "abd") < 0, strcmp("b", "a") > 0, strcmp(greeting, "hello, world"));
    printf("chr %s\n", strchr(greeting, 'w'));
    printf("words %d\n", count_words("  the quick\tbrown  fox "));
    strcat(gbuf, "+more");
    printf("gbuf %s\n", gbuf);
    for (char *p = b; *p; p++) *p = (char)toupper((unsigned char)*p);
    printf("upper %s\n", b);
    char num[32];
    snprintf(num, sizeof num, "%d-%x-%s", 255, 255, "ff");
    printf("snprintf %s\n", num);
    const char *lines[] = {"alpha", "beta", "gamma", "delta"};
    size_t tot = 0;
    for (int i = 0; i < 4; i++) tot += strlen(lines[i]) * (i + 1);
    printf("tot %zu %c\n", tot, lines[2][3]);
    printf("memcmp %d\n", memcmp("abcd", "abce", 4) < 0);
    return 0;
}
