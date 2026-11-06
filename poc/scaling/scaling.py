#!/usr/bin/env python3
"""How does the Goose compiler scale with program size?

Generates synthetic Goose programs of increasing size and times each phase
of the toolchain, with the peak memory of each process:

  check   goose check            parse + resolve + typecheck + analyses
  emit    goose -o x.c           everything above + C generation
  jit     goose run              everything above + TinyCC compile + run
  cc-O0   clang -O0 -c x.c       the C compiler on the generated C
  cc-O2   clang -O2 -c x.c

It also probes two scaling issues reported upstream:
  #226  nested calls f(f(f(...))): checking time vs nesting depth
  #227  a long sum a+a+...+a: generated C nesting vs clang's limit

usage: scaling.py GOOSE_EXE OUT_DIR [--sizes 1000,10000,...] [--cc clang-20]
"""
import argparse, json, os, subprocess, sys, time


def run(cmd, cwd=None, timeout=1800):
    """Run cmd; return (seconds, peak RSS in MB, exit code, stderr tail).

    GNU time reports the peak RSS of this one process on the last stderr line.
    """
    t0 = time.perf_counter()
    p = subprocess.Popen(["/usr/bin/time", "-f", "@@%M", *cmd], cwd=cwd,
                         stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    try:
        _, err = p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        p.kill()
        p.communicate()
        return timeout, 0.0, "timeout", ""
    dt = time.perf_counter() - t0
    text = err.decode(errors="replace")
    rss = 0.0
    head, sep, tail = text.rpartition("@@")
    if sep:
        try:
            rss = int(tail.strip().split()[0]) / 1024
        except (ValueError, IndexError):
            pass
        text = head
    return dt, rss, p.returncode, text[-400:]


FUNC = """
fn fn_{i}(n: i64, acc: i64) -> i64 {{
    var t: i64 = 0;
    {{
        var xs: i64[>..] = [];
        for j in n {{ xs.push(j * {k} + acc); }}
        for x in xs {{ if x % 3 == 0 {{ t += x; }} else {{ t -= 1; }} }}
    }}
    let p = P {{ x: t, y: n }};
    var sh: Shape = Shape.Sq {{ s: n }};
    if t % 2 != 0 {{ sh = Shape.Rc {{ w: n, h: 2 }}; }}
    t += twice(p.x % 100) + area(sh);
    {call}
    return t + p.y;
}}
"""

PRELUDE = """
struct P { x: i64, y: i64 }
enum Shape { Sq { s: i64 }, Rc { w: i64, h: i64 } }
fn area(s: Shape.Sq) -> i64 { s.s * s.s }
fn area(s: Shape.Rc) -> i64 { s.w * s.h }
fn twice(x) { x + x }
"""


def gen_program(n_funcs):
    parts = [PRELUDE]
    for i in range(n_funcs):
        # Chains of ten calls, so the call graph is wide rather than deep.
        call = f"t += fn_{i - 1}(n, t % 7);" if i % 10 != 0 else ""
        parts.append(FUNC.format(i=i, k=i % 7 + 1, call=call))
    main = ["fn main() {", "    var total: i64 = 0;"]
    for i in range(9, n_funcs, 10):
        main.append(f"    total += fn_{i}(5, {i % 13});")
    main.append("    print(total);")
    main.append("}")
    parts.append("\n".join(main))
    return "\n".join(parts)


def gen_nested(depth):
    # f(f(f(...f(1)...))) — upstream issue #226.
    expr = "1"
    for _ in range(depth):
        expr = f"inc({expr})"
    return f"fn inc(x: i64) -> i64 {{ x + 1 }}\nfn main() {{ print({expr}); }}\n"


def gen_long_sum(terms):
    # a + a + ... + a — upstream issue #227.
    expr = " + ".join(["a"] * terms)
    return f"fn main() {{ let a: i64 = 1; print({expr}); }}\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("goose")
    ap.add_argument("out")
    ap.add_argument("--sizes", default="1000,10000,50000,100000,200000")
    ap.add_argument("--cc", default="clang-20")
    ap.add_argument("--skip-cc-above", type=int, default=10**9,
                    help="skip the C compiler phases above this many lines")
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    results = {"sizes": [], "nested": [], "long_sum": []}

    for target in [int(s) for s in a.sizes.split(",")]:
        n_funcs = max(1, target // 14)
        src = gen_program(n_funcs)
        lines = src.count("\n") + 1
        path = os.path.join(a.out, f"prog_{target}.goose")
        cfile = os.path.join(a.out, f"prog_{target}.c")
        with open(path, "w") as f:
            f.write(src)
        row = {"target": target, "lines": lines, "funcs": n_funcs}
        for name, cmd in [
            ("check", [a.goose, "check", path]),
            ("emit", [a.goose, "--standalone", "-o", cfile, path]),
            ("jit", [a.goose, "run", path]),
        ]:
            dt, rss, rc, err = run(cmd)
            row[name] = {"s": dt, "rss_mb": rss, "rc": rc, "err": err if rc else ""}
            print(f"{lines:>7} lines {name:>6}: {dt:8.2f}s  {rss:8.0f} MB  rc={rc}", flush=True)
        if os.path.exists(cfile):
            row["c_bytes"] = os.path.getsize(cfile)
            row["c_lines"] = sum(1 for _ in open(cfile, errors="replace"))
            if lines <= a.skip_cc_above:
                for name, opt in [("cc-O0", "-O0"), ("cc-O2", "-O2")]:
                    dt, rss, rc, err = run([a.cc, opt, "-w", "-c", cfile, "-o", os.devnull])
                    row[name] = {"s": dt, "rss_mb": rss, "rc": rc, "err": err if rc else ""}
                    print(f"{lines:>7} lines {name:>6}: {dt:8.2f}s  {rss:8.0f} MB  rc={rc}", flush=True)
        results["sizes"].append(row)

    for depth in [8, 12, 16, 18, 20, 22]:
        path = os.path.join(a.out, f"nested_{depth}.goose")
        with open(path, "w") as f:
            f.write(gen_nested(depth))
        dt, rss, rc, err = run([a.goose, "check", path], timeout=300)
        results["nested"].append({"depth": depth, "s": dt, "rc": rc})
        print(f"nested depth {depth:>3}: check {dt:8.2f}s rc={rc}", flush=True)

    for terms in [250, 500, 1000, 1500, 3000]:
        path = os.path.join(a.out, f"sum_{terms}.goose")
        cfile = os.path.join(a.out, f"sum_{terms}.c")
        with open(path, "w") as f:
            f.write(gen_long_sum(terms))
        dt, _, rc, err = run([a.goose, "--standalone", "-o", cfile, path], timeout=300)
        row = {"terms": terms, "emit_s": dt, "emit_rc": rc}
        if rc == 0:
            dt2, _, rc2, err2 = run([a.cc, "-O0", "-w", "-c", cfile, "-o", os.devnull], timeout=300)
            row.update({"cc_s": dt2, "cc_rc": rc2, "cc_err": err2.strip().splitlines()[-1] if rc2 else ""})
        results["long_sum"].append(row)
        print(f"sum of {terms:>5} terms: emit rc={rc} cc rc={row.get('cc_rc')} {row.get('cc_err', '')}", flush=True)

    with open(os.path.join(a.out, "results.json"), "w") as f:
        json.dump(results, f, indent=1)


if __name__ == "__main__":
    main()
