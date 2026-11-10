// <iostream> and <string>: std::cout with manipulators (std::endl through
// a function pointer), std::string construction, +=, + (libstdc++ extern
// templates: their members are the library ones), always_inline members and
// function templates expanded as clang does at -O0.
#include <iostream>
#include <string>
int main() {
    std::cout << "hello world" << std::endl;
    std::string s = "abc";
    s += "def";
    std::string t = s + "!";
    std::cout << s << ' ' << t << ' ' << t.size() << ' ' << 42 << ' ' << 2.5 << std::endl;
    return 0;
}
