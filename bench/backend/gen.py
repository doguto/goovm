#!/usr/bin/env python3
"""Generate a large synthetic C program inside goovm's subset.

  gen.py N [--seed S] [-o out.c]

N functions of the shapes typical for C code compiled at -O0: loops over
arrays, struct field updates through pointers, switch-based dispatch, calls
to earlier functions (direct, through function-pointer tables, printf),
string scanning, bit mixing. Every function is deterministic and free of UB
(unsigned arithmetic for anything that can overflow, masked indices,
divisors forced non-zero), and main() calls a sample of them and prints a
checksum, so the generated program can also be run to check correctness.
No floating point, no variadic definitions, no VLAs.
"""
import argparse
import random

PRELUDE = r"""#include <stdio.h>
#include <string.h>
#include <stdint.h>

struct rec { int32_t id; uint8_t kind; int16_t delta; uint32_t flags; int64_t total; const char *name; struct rec *next; };
struct vec3 { int32_t x, y, z; };
struct buf { uint32_t len; uint8_t data[64]; };

static uint32_t g_u32[256];
static int64_t g_i64[128];
static uint8_t g_bytes[512];
static struct rec g_recs[32];
static struct vec3 g_vecs[16] = {{1, 2, 3}, {-4, 5, -6}, {7, -8, 9}};
static const char *g_names[8] = {"alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta"};
static const int16_t g_tab[16] = {3, -1, 4, -1, 5, -9, 2, -6, 5, 3, -5, 8, -9, 7, -9, 3};
static uint64_t g_seed = 0x9E3779B97F4A7C15ull;
static uint32_t g_fuel;

static uint32_t mix32(uint32_t x) { x ^= x >> 16; x *= 0x7feb352dU; x ^= x >> 15; x *= 0x846ca68bU; return x ^ (x >> 16); }
static uint64_t next_rand(void) { g_seed ^= g_seed << 13; g_seed ^= g_seed >> 7; g_seed ^= g_seed << 17; return g_seed; }
"""


class Gen:
    def __init__(self, n, seed):
        self.n = n
        self.r = random.Random(seed)
        self.out = []
        self.sigs = []  # (name, kind)

    def w(self, s):
        self.out.append(s)

    def callee(self, i):
        """An earlier function and an expression calling it, or None."""
        if i == 0:
            return None
        j = self.r.randrange(max(0, i - 50), i)
        return j

    def call_expr(self, i, a, b):
        j = self.callee(i)
        if j is None:
            return f"mix32({a})"
        kind = self.sigs[j]
        if kind == "u2":
            return f"f{j}({a}, {b})"
        if kind == "p":
            return f"(uint32_t)f{j}(&g_recs[({a}) & 31], (int32_t){b})"
        if kind == "s":
            return f"(uint32_t)f{j}((int)({a}))"
        if kind == "b":
            return f"f{j}((const uint8_t *)g_bytes + (({a}) & 255), ({b}) & 63)"
        if kind == "v":
            return f"(uint32_t)f{j}(g_vecs[({a}) & 15], (int8_t){b}, (uint16_t)({a} >> 3))"
        return f"f{j}((uint64_t)({a}), {b} | 1u, (int16_t)({b}), (uint8_t)({a}), (int32_t)({a} ^ {b}), {b} >> 1, ({a}) + 7u)"

    def expr(self, vs, depth=0):
        r = self.r
        if depth > 1 or r.random() < 0.35:
            c = r.random()
            if c < 0.5:
                return r.choice(vs)
            if c < 0.8:
                return f"{r.randrange(1, 1000)}u"
            return f"g_u32[({r.choice(vs)}) & 255]"
        a = self.expr(vs, depth + 1)
        b = self.expr(vs, depth + 1)
        op = r.choice(["+", "-", "*", "^", "&", "|", ">>", "<<", "/", "%"])
        if op in (">>", "<<"):
            return f"(({a}) {op} (({b}) & 31u))"
        if op in ("/", "%"):
            return f"(({a}) {op} (({b}) | 1u))"
        return f"(({a}) {op} ({b}))"

    def cond(self, vs):
        r = self.r
        a, b = r.choice(vs), self.expr(vs, 2)
        op = r.choice(["<", ">", "<=", ">=", "==", "!="])
        if r.random() < 0.3:
            return f"(int32_t){a} {op} (int32_t)({b})"
        if r.random() < 0.2:
            c = r.choice(vs)
            return f"({a} {op} {b}) {r.choice(['&&', '||'])} ({c} & {r.randrange(1, 16)}u)"
        return f"{a} {op} {b}"

    def stmts(self, i, ws, n, depth=0, rs=()):
        """n statements; ws = assignable variables, rs = extra read-only ones (loop counters)."""
        r = self.r
        ind = "    " * (depth + 1)
        vs = list(ws) + list(rs)
        for _ in range(n):
            c = r.random()
            v = r.choice(ws)
            if c < 0.30:
                self.w(f"{ind}{v} = {self.expr(vs)};")
            elif c < 0.42 and depth < 2:
                self.w(f"{ind}if ({self.cond(vs)}) {{")
                self.stmts(i, ws, r.randrange(1, 4), depth + 1, rs)
                if r.random() < 0.5:
                    self.w(f"{ind}}} else {{")
                    self.stmts(i, ws, r.randrange(1, 3), depth + 1, rs)
                self.w(f"{ind}}}")
            elif c < 0.52 and depth < 2:
                k = f"k{depth}"
                self.w(f"{ind}for (uint32_t {k} = 0; {k} < {r.randrange(2, 9)}u; {k}++) {{")
                self.stmts(i, ws, r.randrange(1, 4), depth + 1, list(rs) + [k])
                self.w(f"{ind}}}")
            elif c < 0.62:
                # Calls are bounded by a global budget so the call tree stays small at run time.
                self.w(f"{ind}if (g_fuel) {{ g_fuel--; {v} += {self.call_expr(i, r.choice(vs), r.choice(vs))}; }}")
            elif c < 0.68:
                self.w(f"{ind}g_u32[({v}) & 255] ^= {self.expr(vs, 1)};")
            elif c < 0.73:
                self.w(f"{ind}{v} = {r.choice(vs)} > {r.choice(vs)} ? {self.expr(vs, 2)} : {self.expr(vs, 2)};")
            elif c < 0.78:
                self.w(f"{ind}g_i64[({v}) & 127] += (int64_t)(int32_t){r.choice(vs)} * {r.randrange(-50, 50)};")
            elif c < 0.83:
                self.w(f"{ind}{v} += (uint32_t)g_tab[({r.choice(vs)}) & 15] + (uint32_t)strlen(g_names[{v} & 7]);")
            elif c < 0.88 and depth < 2:
                self.w(f"{ind}while ({v} > {r.randrange(100, 100000)}u) {v} = ({v} >> 1) + {r.randrange(1, 9)}u;")
            elif c < 0.93:
                self.w(f"{ind}g_bytes[({v}) & 511] = (uint8_t)({self.expr(vs, 1)});")
            else:
                self.w(f"{ind}{v} = mix32({v} + (uint32_t)next_rand());")

    # ---- function shapes -------------------------------------------------
    def f_arith(self, i):
        self.sigs.append("u2")
        self.w(f"uint32_t f{i}(uint32_t a, uint32_t b) {{")
        self.w("    uint32_t x = a ^ b, y = a + 3u, z = b * 7u;")
        self.stmts(i, ["a", "b", "x", "y", "z"], self.r.randrange(3, 10))
        self.w("    return x + y * 3u + z;\n}\n")

    def f_struct(self, i):
        self.sigs.append("p")
        self.w(f"int64_t f{i}(struct rec *r, int32_t v) {{")
        self.w("    uint32_t t = (uint32_t)v, u = r->flags;")
        self.w(f"    r->id += v % {self.r.randrange(3, 99)};")
        self.w("    r->kind = (uint8_t)(r->kind + (uint8_t)t);")
        self.w("    r->delta = (int16_t)(r->delta - (int16_t)(t & 0xFF));")
        self.w("    r->total += (int64_t)r->id * r->delta;")
        self.w("    if (!r->name) r->name = g_names[t & 7];")
        self.w("    if (r->next == 0 && (t & 1)) r->next = &g_recs[(t >> 1) & 31];")
        self.stmts(i, ["t", "u"], self.r.randrange(2, 6))
        self.w("    int guard = 0;")
        self.w("    for (struct rec *p = r->next; p && p != r && guard < 40; p = p->next, guard++) { u += (uint32_t)p->id; if (u & 0x10000) break; }")
        self.w("    r->flags = u ^ t;")
        self.w("    return r->total + (int64_t)u;\n}\n")

    def f_switch(self, i):
        self.sigs.append("s")
        n = self.r.randrange(4, 16)
        self.w(f"int f{i}(int op) {{")
        self.w("    uint32_t acc = (uint32_t)op, s = 1;")
        self.w(f"    for (int step = 0; step < {self.r.randrange(2, 6)}; step++) {{")
        self.w(f"        switch ((acc + (uint32_t)step) % {n}u) {{")
        for c in range(n):
            self.w(f"        case {c}:")
            vs = ["acc", "s"]
            self.stmts(i, vs, self.r.randrange(1, 2), 2, ["step"])
            if self.r.random() < 0.8:
                self.w("            break;")
        self.w("        default: acc ^= 0x55u; break;")
        self.w("        }")
        self.w("    }")
        self.w("    return (int)(acc ^ s);\n}\n")

    def f_bytes(self, i):
        self.sigs.append("b")
        self.w(f"uint32_t f{i}(const uint8_t *p, uint32_t n) {{")
        self.w("    struct buf b;")
        self.w("    uint32_t h = 2166136261u, c = 0;")
        self.w("    memset(&b, 0, sizeof b);")
        self.w("    for (uint32_t k = 0; k < n; k++) {")
        self.w("        h = (h ^ p[k]) * 16777619u;")
        self.w(f"        if (p[k] == {self.r.randrange(0, 255)}u) c++;")
        self.w("        b.data[k & 63] = (uint8_t)(h >> 24);")
        self.w("    }")
        self.w("    b.len = n;")
        self.stmts(i, ["h", "c"], self.r.randrange(2, 8))
        self.w("    struct buf copy = b;")
        self.w("    return h + c + copy.data[n & 63] + copy.len;\n}\n")

    def f_vec(self, i):
        self.sigs.append("v")
        self.w(f"int32_t f{i}(struct vec3 v, int8_t k, uint16_t m) {{")
        self.w("    struct vec3 w[4];")
        self.w("    uint32_t q = (uint32_t)(v.x * k) + m;")
        self.w("    for (int j = 0; j < 4; j++) { w[j].x = v.x + j * k; w[j].y = v.y - (int32_t)m; w[j].z = v.z ^ j; }")
        self.stmts(i, ["q"], self.r.randrange(2, 8))
        self.w("    int32_t best = w[0].x;")
        self.w("    for (int j = 1; j < 4; j++) if (w[j].x + w[j].y > best) best = w[j].x + w[j].y;")
        self.w("    return best + w[q & 3].z + (int32_t)(q & 0xFFFF);\n}\n")

    def f_many(self, i):
        self.sigs.append("m")
        self.w(f"uint32_t f{i}(uint64_t a, uint32_t b, int16_t c, uint8_t d, int32_t e, uint32_t f, uint32_t g) {{")
        self.w("    uint32_t x = (uint32_t)a + b, y = (uint32_t)(int32_t)c + d, z = (uint32_t)e ^ f ^ g;")
        self.w("    uint32_t loc[8];")
        self.w("    for (int j = 0; j < 8; j++) loc[j] = x * (uint32_t)j + y;")
        self.stmts(i, ["x", "y", "z", "b", "f", "g"], self.r.randrange(3, 8))
        self.w(f"    if ((z & 7u) == {self.r.randrange(0, 8)}u) printf(\"f{i}: %u %u\\n\", x, z);")
        self.w("    return x + y + z + loc[(x ^ z) & 7];\n}\n")

    def generate(self):
        self.w(PRELUDE)
        shapes = [self.f_arith, self.f_arith, self.f_struct, self.f_switch, self.f_bytes, self.f_vec, self.f_many]
        for i in range(self.n):
            self.r.choice(shapes)(i)
        # Function-pointer table over the uint32_t(uint32_t, uint32_t) functions.
        u2 = [i for i, k in enumerate(self.sigs) if k == "u2"][:64] or None
        if u2:
            self.w("static uint32_t (*const g_fns[])(uint32_t, uint32_t) = {" + ", ".join(f"f{i}" for i in u2) + "};")
        self.w("int main(void) {")
        self.w("    uint64_t check = 0;")
        self.w("    for (int i = 0; i < 32; i++) { g_recs[i].id = i; g_recs[i].next = &g_recs[(i * 7) & 31]; }")
        self.w("    for (int i = 0; i < 512; i++) g_bytes[i] = (uint8_t)mix32((uint32_t)i);")
        self.w("    g_fuel = 100000;")
        calls = sorted(self.r.sample(range(self.n), min(self.n, 200)))
        for j in calls:
            self.w(f"    check = check * 31 + (uint64_t){self.call_expr(j + 1, f'(uint32_t)check + {j}u', f'{j * 13}u')};")
        if u2:
            self.w(f"    for (uint32_t i = 0; i < {len(u2)}u; i++) check += g_fns[i](i, (uint32_t)check);")
        self.w("    for (int i = 0; i < 256; i++) check = check * 17 + g_u32[i];")
        self.w("    for (int i = 0; i < 128; i++) check ^= (uint64_t)g_i64[i];")
        self.w('    printf("checksum %llu\\n", (unsigned long long)check);')
        self.w("    return 0;\n}")
        return "\n".join(self.out) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("n", type=int)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("-o", default="-")
    a = ap.parse_args()
    src = Gen(a.n, a.seed).generate()
    if a.o == "-":
        print(src, end="")
    else:
        with open(a.o, "w") as f:
            f.write(src)


if __name__ == "__main__":
    main()
