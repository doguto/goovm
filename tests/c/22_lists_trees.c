// Heap-allocated linked list and binary search tree (malloc/free).
#include <stdio.h>
#include <stdlib.h>

struct Node { int v; struct Node *next; };
struct Tree { int key, count; struct Tree *l, *r; };

static struct Node *push(struct Node *h, int v) {
    struct Node *n = malloc(sizeof *n);
    n->v = v;
    n->next = h;
    return n;
}
static struct Node *reverse(struct Node *h) {
    struct Node *p = 0;
    while (h) { struct Node *n = h->next; h->next = p; p = h; h = n; }
    return p;
}
static struct Tree *insert(struct Tree *t, int k) {
    if (!t) { t = calloc(1, sizeof *t); t->key = k; t->count = 1; return t; }
    if (k < t->key) t->l = insert(t->l, k);
    else if (k > t->key) t->r = insert(t->r, k);
    else t->count++;
    return t;
}
static int depth(struct Tree *t) { if (!t) return 0; int a = depth(t->l), b = depth(t->r); return 1 + (a > b ? a : b); }
static void inorder(struct Tree *t, int *out, int *n) {
    if (!t) return;
    inorder(t->l, out, n);
    out[(*n)++] = t->key * 10 + t->count;
    inorder(t->r, out, n);
}
static void free_tree(struct Tree *t) { if (t) { free_tree(t->l); free_tree(t->r); free(t); } }

int main(void) {
    struct Node *h = 0;
    for (int i = 0; i < 10; i++) h = push(h, i * i);
    h = reverse(h);
    for (struct Node *p = h; p; p = p->next) printf("%d ", p->v);
    printf("\n");
    while (h) { struct Node *n = h->next; free(h); h = n; }
    struct Tree *t = 0;
    unsigned s = 7;
    for (int i = 0; i < 40; i++) { s = s * 69069u + 1; t = insert(t, (int)(s >> 24) % 20); }
    int out[64], n = 0;
    inorder(t, out, &n);
    for (int i = 0; i < n; i++) printf("%d ", out[i]);
    printf("\nnodes %d depth %d\n", n, depth(t));
    free_tree(t);
    return 0;
}
