// goosecc D1: static locals (constant, dynamic, objects with destructors),
// static data members, init_priority, namespaces with the same names,
// anonymous namespaces, extern variables defined later.
#include <stdio.h>
#include <stdlib.h>

static int calls = 0;
int next_id() { return ++calls * 10; }

struct Logger {
    int id;
    Logger(int i) : id(i) { printf("Logger %d\n", id); }
    ~Logger() { printf("~Logger %d\n", id); }
};

int counter() {
    static int n = 0;
    static int first = next_id();
    return ++n + first;
}

Logger &instance() {
    static Logger l(next_id());
    return l;
}

struct Registry {
    static int entries;
    static const int limit = 8;
    static int add(int k) { entries += k; return entries < limit; }
};
int Registry::entries;

namespace a { int value() { return 1; } namespace { int hidden = 5; } int get() { return hidden; } }
namespace b { int value() { return 2; } }

extern int late[];
int read_late(int i) { return late[i]; }
int late[] = {3, 1, 4, 1, 5};

struct Early {
    Early(const char *s) { printf("early %s\n", s); }
};
Early e3 __attribute__((init_priority(300))) ("300");
Early e1 __attribute__((init_priority(200))) ("200");
Early e0("default");

int main() {
    printf("%d %d %d\n", counter(), counter(), counter());
    printf("%d\n", instance().id);
    printf("%d\n", instance().id);
    printf("%d %d %d\n", Registry::add(3), Registry::add(4), Registry::add(5));
    printf("%d %d %d\n", a::value(), b::value(), a::get());
    printf("%d %d\n", read_late(2), read_late(4));
    return 0;
}
