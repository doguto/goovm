#!/usr/bin/env python3
"""Build the four IR-core variants and compare them.

  goose      ircore.goose  (slot pools, i32 links, data stacks)
  c++idx     ircore_idx.cpp (same layout; std::vector pools)
  c++idx+res ircore_idx.cpp -DRESERVE (pools pre-sized: growth never moves)
  c++ptr     ircore_ptr.cpp (LLVM style: one heap object per inst and use)

Each binary runs --runs times; per phase the fastest run is kept. Peak RSS
comes from GNU time. All variants must print the same checksum.

usage: run.py GOOSE_EXE WORK_DIR [--n 2000000] [--runs 5] [--cc clang-20]
"""
import argparse, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))


def sh(cmd):
    subprocess.run(cmd, check=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("goose")
    ap.add_argument("work")
    ap.add_argument("--n", type=int, default=2000000)
    ap.add_argument("--runs", type=int, default=5)
    ap.add_argument("--cc", default="clang-20")
    ap.add_argument("--cxx", default="clang++-20")
    a = ap.parse_args()
    os.makedirs(a.work, exist_ok=True)
    w = lambda n: os.path.join(a.work, n)

    sh([a.goose, "--standalone", "-o", w("ircore.c"), os.path.join(HERE, "ircore.goose")])
    sh([a.cc, "-O2", "-w", w("ircore.c"), "-o", w("goose"), "-lm", "-pthread"])
    sh([a.cxx, "-O2", "-std=c++17", os.path.join(HERE, "ircore_idx.cpp"), "-o", w("idx")])
    sh([a.cxx, "-O2", "-std=c++17", "-DRESERVE", os.path.join(HERE, "ircore_idx.cpp"), "-o", w("idxres")])
    sh([a.cxx, "-O2", "-std=c++17", os.path.join(HERE, "ircore_ptr.cpp"), "-o", w("ptr")])

    phases = ["build", "fold", "dce", "walk", "total"]
    rows = []
    for name, exe in [("goose", "goose"), ("c++ idx", "idx"), ("c++ idx + reserve", "idxres"), ("c++ ptr (LLVM style)", "ptr")]:
        best = {p: 1e18 for p in phases}
        rss = 0
        checksum = None
        for _ in range(a.runs):
            r = subprocess.run(["/usr/bin/time", "-f", "@@%M", w(exe), str(a.n)],
                               capture_output=True, text=True, check=True)
            first, second = r.stdout.strip().splitlines()[:2]
            checksum = re.search(r"checksum=(\d+)", first).group(1)
            for p in phases:
                best[p] = min(best[p], int(re.search(rf"{p} (\d+) ms", second).group(1)))
            rss = max(rss, int(r.stderr.rpartition("@@")[2].split()[0]))
        rows.append((name, best, rss // 1024, checksum))

    print(f"n = {a.n:,} instructions, best of {a.runs} runs (ms), peak RSS (MB)\n")
    print("| variant | build | fold | dce | walk | total | peak MB | checksum |")
    print("|---|---:|---:|---:|---:|---:|---:|---|")
    for name, b, rss, cs in rows:
        print(f"| {name} | {b['build']} | {b['fold']} | {b['dce']} | {b['walk']} | {b['total']} | {rss} | {cs} |")
    if len({cs for *_, cs in rows}) != 1:
        print("\nCHECKSUM MISMATCH", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
