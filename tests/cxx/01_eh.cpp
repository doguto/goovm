// Exception handling: catch by type and base, catch(...), rethrow, nested
// handlers, cleanups, function-try-blocks, exceptions from constructors,
// noexcept (std::terminate), values live across invokes and into handlers.
#include <cstdio>
#include <cstdlib>
#include <exception>
#include <stdexcept>
#include <string>
#include <vector>

static int live;
struct Obj {
    int id;
    explicit Obj(int i) : id(i) { live++; }
    Obj(const Obj &o) : id(o.id) { live++; }
    ~Obj() { live--; }
};

struct Base { virtual ~Base() {} virtual const char *name() const { return "Base"; } };
struct Derived : Base { const char *name() const override { return "Derived"; } };
struct Other {};

static int thrower(int k) {
    Obj o(k);
    switch (k % 6) {
    case 0: throw std::out_of_range("range");
    case 1: throw Derived();
    case 2: throw 42;
    case 3: throw std::string("str");
    case 4: throw Other();
    default: return k;
    }
}

static std::string classify(int k) {
    try {
        return "value " + std::to_string(thrower(k));
    } catch (const std::logic_error &e) {
        return std::string("logic_error ") + e.what();
    } catch (const Base &b) {
        return std::string("base ") + b.name();
    } catch (int i) {
        return "int " + std::to_string(i);
    } catch (const std::string &s) {
        return "string " + s;
    } catch (...) {
        return "something";
    }
}

struct Partial {
    Obj a, b;
    Partial(int k) try : a(k), b(thrower(k)) {
        std::printf("Partial(%d) built\n", k);
    } catch (...) {
        std::printf("Partial(%d) failed, live=%d\n", k, live);
    }
};

static int rethrower(int k) {
    try {
        thrower(k);
    } catch (...) {
        std::printf("  rethrowing at depth 1\n");
        throw;
    }
    return 0;
}

static void on_terminate() {
    std::printf("terminate called, live=%d\n", live);
    std::fflush(stdout);
    std::_Exit(0);
}

static void must_not_throw() noexcept {
    Obj o(99);
    thrower(2);
}

// many values live across invokes and into handlers
static long accumulate(int n) {
    long sum = 0, prod = 1, last = -1;
    std::vector<int> seen;
    for (int i = 0; i < n; i++) {
        try {
            sum += thrower(i);
            prod = prod * 3 % 1000003;
        } catch (int x) {
            last = x + i;
            seen.push_back(i);
        } catch (...) {
            sum -= i;
        }
    }
    return sum * 1000 + prod + last + (long)seen.size();
}

int main() {
    for (int k = 0; k < 12; k++) std::printf("%d: %s\n", k, classify(k).c_str());
    for (int k = 0; k < 3; k++) {
        try {
            Partial p(k + 4);
        } catch (const std::exception &e) {
            std::printf("  outer caught %s\n", e.what());
        } catch (...) {
            std::printf("  outer caught other\n");
        }
    }
    try {
        rethrower(1);
    } catch (Base &b) {
        std::printf("rethrown %s, live=%d\n", b.name(), live);
    }
    try {
        try {
            throw std::runtime_error("inner");
        } catch (std::runtime_error &e) {
            try {
                throw std::logic_error("nested");
            } catch (std::exception &n) {
                std::printf("nested %s inside %s\n", n.what(), e.what());
            }
        }
    } catch (...) {
        std::printf("not reached\n");
    }
    std::printf("accumulate %ld, live=%d\n", accumulate(40), live);
    std::exception_ptr ep;
    try {
        thrower(3);
    } catch (...) {
        ep = std::current_exception();
    }
    try {
        std::rethrow_exception(ep);
    } catch (const std::string &s) {
        std::printf("exception_ptr %s\n", s.c_str());
    }
    std::set_terminate(on_terminate);
    must_not_throw();
    std::printf("not reached\n");
    return 1;
}
