// goosecc D1: small "C with classes" programs: a string class with a
// copy constructor and assignment operator, a linked list, a stack with
// an inheritance chain, const member functions, enums in classes.
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

class Str {
    char *buf;
    int len;
public:
    Str(const char *s) : len((int)strlen(s)) {
        buf = new char[len + 1];
        memcpy(buf, s, len + 1);
    }
    Str(const Str &o) : len(o.len) {
        buf = new char[len + 1];
        memcpy(buf, o.buf, len + 1);
        printf("copy %s\n", buf);
    }
    ~Str() { printf("free %s\n", buf); delete[] buf; }
    Str &operator=(const Str &o) {
        if (this != &o) {
            delete[] buf;
            len = o.len;
            buf = new char[len + 1];
            memcpy(buf, o.buf, len + 1);
        }
        return *this;
    }
    Str &append(const char *s) {
        int n = (int)strlen(s);
        char *nb = new char[len + n + 1];
        memcpy(nb, buf, len);
        memcpy(nb + len, s, n + 1);
        delete[] buf;
        buf = nb;
        len += n;
        return *this;
    }
    const char *c_str() const { return buf; }
    int size() const { return len; }
    char operator[](int i) const { return buf[i]; }
};

struct Node {
    int value;
    Node *next;
    Node(int v, Node *n) : value(v), next(n) {}
};

class List {
    Node *head;
    int count;
public:
    List() : head(0), count(0) {}
    ~List() {
        while (head) {
            Node *n = head->next;
            delete head;
            head = n;
        }
    }
    void push(int v) { head = new Node(v, head); count++; }
    int sum() const {
        int s = 0;
        for (Node *n = head; n; n = n->next) s += n->value;
        return s;
    }
    int size() const { return count; }
    void reverse() {
        Node *prev = 0;
        while (head) {
            Node *n = head->next;
            head->next = prev;
            prev = head;
            head = n;
        }
        head = prev;
    }
    int first() const { return head ? head->value : -1; }
};

class Container {
public:
    enum Kind { STACK, QUEUE };
    virtual ~Container() {}
    virtual void put(int v) = 0;
    virtual int take() = 0;
    virtual bool empty() const = 0;
    virtual Kind kind() const = 0;
    int drain() {
        int s = 0, k = 1;
        while (!empty()) s += k++ * take();
        return s;
    }
};

class Stack : public Container {
protected:
    int data[64];
    int top;
public:
    Stack() : top(0) {}
    void put(int v) { data[top++] = v; }
    int take() { return data[--top]; }
    bool empty() const { return top == 0; }
    Kind kind() const { return STACK; }
};

class Queue : public Stack {
    int front;
public:
    Queue() : front(0) {}
    int take() { return data[front++]; }
    bool empty() const { return front == top; }
    Kind kind() const { return QUEUE; }
};

int main() {
    Str a("hello");
    Str b(a);
    b.append(", world");
    Str c("x");
    c = b;
    printf("%s|%s|%s %d %c\n", a.c_str(), b.c_str(), c.c_str(), c.size(), c[4]);
    {
        List l;
        for (int i = 1; i <= 10; i++) l.push(i * i);
        l.reverse();
        printf("%d %d %d\n", l.size(), l.sum(), l.first());
    }
    Container *cs[2];
    cs[0] = new Stack;
    cs[1] = new Queue;
    for (int j = 0; j < 2; j++) {
        for (int i = 1; i <= 5; i++) cs[j]->put(i);
        printf("kind %d drain %d\n", (int)cs[j]->kind(), cs[j]->drain());
        delete cs[j];
    }
    return 0;
}
