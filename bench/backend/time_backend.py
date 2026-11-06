#!/usr/bin/env python3
"""Best-of-N phase times of goovm-llc --time.

usage: bench/backend/time_backend.py --goovm PATH [--goovm PATH2 ...] [--backend goose] [-n 5] in.bc ...

For each input and each goovm-llc binary, runs `goovm-llc --backend=B --time
in.bc -o /tmp/x.o` N times and prints a markdown table with the best (minimum)
backend_us, export_us and total_us. Several --goovm options compare builds
(e.g. a v0 build of commit 8f55b18 against the current one); --backend applies
to all of them (v0 builds need --backend=goose too).
"""
import argparse
import os
import re
import subprocess
import sys
import tempfile


def best(goovm, backend, bc, n):
    out = os.path.join(tempfile.gettempdir(), f"goovm-time-{os.getpid()}.o")
    res = {}
    for _ in range(n):
        r = subprocess.run([goovm, f"--backend={backend}", "--time", bc, "-o", out],
                           stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
        if r.returncode:
            sys.exit(f"{goovm} failed on {bc}: {r.stderr.decode(errors='replace')[:500]}")
        line = [l for l in r.stderr.decode().splitlines() if l.startswith("goovm-time:")][0]
        kv = dict(re.findall(r"(\w+)=(\d+)", line))
        for k in ("parse_us", "export_us", "backend_us", "total_us", "gir_insts"):
            v = int(kv.get(k, 0))
            res[k] = min(res.get(k, v), v)
    os.unlink(out)
    return res


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--goovm", action="append", required=True)
    ap.add_argument("--backend", default="goose")
    ap.add_argument("-n", type=int, default=5)
    ap.add_argument("inputs", nargs="+")
    a = ap.parse_args()
    hdr = "| input | gir insts |" + "".join(f" backend ms ({i}) | export ms ({i}) |" for i in range(len(a.goovm)))
    print(hdr)
    print("|---|---:|" + "---:|---:|" * len(a.goovm))
    for bc in a.inputs:
        rows = [best(g, a.backend, bc, a.n) for g in a.goovm]
        line = f"| {os.path.basename(bc)} | {rows[-1]['gir_insts']} |"
        for r in rows:
            line += f" {r['backend_us'] / 1000:.1f} | {r['export_us'] / 1000:.1f} |"
        print(line, flush=True)
    for i, g in enumerate(a.goovm):
        print(f"\n({i}) {g}")


if __name__ == "__main__":
    main()
