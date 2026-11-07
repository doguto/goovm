#!/usr/bin/env python3
"""Chooses the hot regions of runtime-patches/lazy-regions.patch: the data
stack regions that nearly every compile touches, which build.sh places
next to each other and makes accessible at start-up (GS_HOT_REGIONS).

Build a profiling goosecc first (each run then lists the registry indices
of the regions it touched on stderr):

  PROFILE_REGIONS=1 frontend-goose/build.sh /tmp/gprof
  frontend-goose/runtime-patches/hot_regions.py /tmp/gprof compile_commands.json [-o hot-regions.txt]

compile_commands.json is CTMark's (llvm-test-suite with cmake/caches/O0.cmake);
every C file is compiled twice, with an empty header cache and with the
cache the first compile filled, and a region touched by at least
--threshold of the runs (default 0.4) is hot. The list holds the names of
the regions' globals (build.sh maps them to registry indices through the
generated C, <build>/regions.txt), most often touched first.
"""
import argparse, collections, json, os, re, shlex, shutil, subprocess, sys, tempfile


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("build", help="directory of a PROFILE_REGIONS=1 build (goosecc, regions.txt)")
    ap.add_argument("ccjson")
    ap.add_argument("--threshold", type=float, default=0.4)
    ap.add_argument("-o", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "hot-regions.txt"))
    a = ap.parse_args()
    g = os.path.join(a.build, "goosecc")
    names = open(os.path.join(a.build, "regions.txt")).read().split()
    tmp = tempfile.mkdtemp(prefix="hot_regions_")
    count = collections.Counter()
    runs = 0
    for e in json.load(open(a.ccjson)):
        if not e["file"].endswith(".c"):
            continue
        args = shlex.split(e["command"]) if "command" in e else list(e["arguments"])
        for i, x in enumerate(args):
            if os.path.basename(x).startswith(("clang", "gcc", "cc")):
                args = args[i:]
                break
        oi = args.index("-o")
        cmd = [g] + args[1:oi] + args[oi + 2:] + ["-o", os.path.join(tmp, "x.o")]
        cache = os.path.join(tmp, "cache")
        shutil.rmtree(cache, ignore_errors=True)
        for _ in range(2):
            r = subprocess.run(cmd, cwd=e["directory"], env=dict(os.environ, GOOSECC_CACHE=cache),
                               stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
            m = re.search(r"goose regions touched:([ 0-9]*)", r.stderr)
            if not m:
                sys.exit("no region profile from %s (not a PROFILE_REGIONS=1 build?)" % g)
            count.update(int(x) for x in m.group(1).split())
            runs += 1
    shutil.rmtree(tmp, ignore_errors=True)
    hot = [i for i, c in count.most_common() if c >= a.threshold * runs and i < len(names)]
    with open(a.o, "w") as f:
        f.write("# Data stack regions that at least %d%% of %d compiles of CTMark's C files touch\n"
                "# (hot_regions.py; build.sh places them first and makes them accessible at start-up).\n"
                % (round(a.threshold * 100), runs))
        for i in hot:
            f.write("%s %d\n" % (names[i], count[i]))
    print("%d hot regions of %d touched (%d runs) -> %s" % (len(hot), len(count), runs, a.o))


if __name__ == "__main__":
    main()
