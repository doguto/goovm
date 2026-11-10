#!/usr/bin/env python3
"""Dynamic instruction counts of AArch64 programs under qemu-aarch64 (milestone F1).

Ubuntu's qemu-user has no TCG plugins, so the count comes from qemu's own
log: `-d in_asm,exec,nochain` prints every translation block once with its
code bytes (4 bytes per AArch64 instruction) and, with chaining off, one
`Trace` line per execution of a block. The sum over the executions of the
block sizes is the number of instructions executed. The log streams through
a FIFO, so nothing big is written. Blocks of the executable itself (qemu
names them by the executable's symbols: `IN: main`) are counted apart from
those of the dynamic loader and the C library (no symbols: `IN: `).

usage: bench/a64/icount.py exe [args...]            prints "total program"
       bench/a64/icount.py --suite REPORT.json ...  (see compile_time.py's sibling run_time.py)
"""
import os, re, subprocess, sys, tempfile, threading

IN_RE = re.compile(r"^0x([0-9a-f]+):")
TR_RE = re.compile(r"^Trace \d+: 0x[0-9a-f]+ \[[0-9a-f]+/([0-9a-f]+)/")


def count(exe, args, stdin=None, cwd=None, timeout=3600):
    d = tempfile.mkdtemp(prefix="icount_")
    fifo = os.path.join(d, "log")
    os.mkfifo(fifo)
    env = dict(os.environ, QEMU_LD_PREFIX=os.environ.get("QEMU_LD_PREFIX", "/usr/aarch64-linux-gnu"))
    p = subprocess.Popen(["qemu-aarch64", "-d", "in_asm,exec,nochain", "-D", fifo, exe] + list(args),
                         stdin=stdin or subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                         cwd=cwd, env=env)
    size = {}
    named = set()
    total = prog = 0
    cur = None
    nbytes = 0
    sym = False
    with open(fifo, "r", errors="replace") as f:
        for line in f:
            c = line[0]
            if c == "T":
                m = TR_RE.match(line)
                if m:
                    pc = int(m.group(1), 16)
                    n = size.get(pc, 0)
                    total += n
                    if pc in named:
                        prog += n
            elif c == "0":
                m = IN_RE.match(line)
                if m:
                    if cur is not None:
                        size[cur] = nbytes // 4
                    cur = int(m.group(1), 16)
                    nbytes = 0
                    if sym:
                        named.add(cur)
                    else:
                        named.discard(cur)
            elif c == "I" and line.startswith("IN:"):
                sym = len(line.strip()) > 3
            elif c == "O" and line.startswith("OBJD-T: "):
                nbytes += (len(line.strip()) - 8) // 2
            elif c == "-" and cur is not None:
                size[cur] = nbytes // 4
                cur = None
            elif c == "\n" and cur is not None:
                size[cur] = nbytes // 4
                cur = None
    p.wait(timeout=timeout)
    os.unlink(fifo)
    os.rmdir(d)
    return total, prog, p.returncode


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    t, pr, rc = count(sys.argv[1], sys.argv[2:])
    print(t, pr, rc)


if __name__ == "__main__":
    main()
