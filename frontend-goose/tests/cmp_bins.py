#!/usr/bin/env python3
"""Two goosecc builds produce the same outputs (G1): for every corpus file
(corpus.py, with its flags) and output -- `-E`, `--dump-ast`,
`--layout-check`, the object of `-c` and of `-c -g` -- the exit status,
standard output, standard error and output file of the new build must be
those of the reference build, byte for byte. Both run without the header
cache. The reference's results can be saved as checksums and reused:

  cmp_bins.py --ref old/goosecc --save ref.json        # record
  cmp_bins.py --load ref.json --goosecc new/goosecc    # compare
  cmp_bins.py --ref old/goosecc --goosecc new/goosecc  # both at once

A differing object is reported with the ELF sections whose contents differ
(llvm-readelf), so that an intended change can be told from another.

usage: frontend-goose/tests/cmp_bins.py [--ref A | --load F] [--goosecc B] [--save F]
         [--corpus torture,...] [--modes E,ast,layout,c,g] [-j 2] [--show N] [--list F] [files... -- flags]
"""
import argparse, concurrent.futures as cf, hashlib, json, os, subprocess, sys, tempfile, threading, collections

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import corpus as corpus_mod

MODES = {"E": ["-E"], "ast": ["--dump-ast"], "layout": ["--layout-check"], "c": ["-c"], "g": ["-c", "-g"]}


def run(goosecc, mode, flags, path, out):
    env = dict(os.environ, SOURCE_DATE_EPOCH="1700000000", TZ="UTC")
    cmd = [goosecc] + MODES[mode] + ["-fno-header-cache"] + flags + [path]
    if mode != "E":
        cmd += ["-o", out]
    r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env)
    data = b""
    if mode != "E" and os.path.exists(out):
        data = open(out, "rb").read()
        os.unlink(out)
    return r.returncode, r.stdout, r.stderr, data


def digest(res):
    h = hashlib.sha256()
    for part in res[1:]:
        h.update(len(part).to_bytes(8, "little"))
        h.update(part)
    return "%d:%s" % (res[0], h.hexdigest()[:32])


def sections(obj, tmp):
    """{section name: sha of its contents} of an object."""
    p = os.path.join(tmp, "s.%d.o" % threading.get_ident())
    open(p, "wb").write(obj)
    r = subprocess.run(["llvm-readelf", "-S", "--wide", p], capture_output=True, text=True)
    out = {}
    for line in r.stdout.splitlines():
        f = line.replace("[ ", "[").split()
        if len(f) > 6 and f[0].startswith("[") and f[0].endswith("]") and f[1] != "":
            try:
                off, size = int(f[4], 16), int(f[5], 16)
            except ValueError:
                continue
            out[f[1]] = hashlib.sha256(obj[off:off + size]).hexdigest()[:16] if f[2] != "NOBITS" else "nobits:%d" % size
    os.unlink(p)
    return out


def main():
    argv, cflags = corpus_mod.split_flags(sys.argv[1:])
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--ref", default="")
    ap.add_argument("--load", default="")
    ap.add_argument("--save", default="")
    ap.add_argument("--goosecc", default="")
    ap.add_argument("--corpus", default="torture,unit,regress,bench,ctmark")
    ap.add_argument("--modes", default="E,ast,layout,c,g")
    ap.add_argument("-j", type=int, default=2)
    ap.add_argument("--show", type=int, default=30)
    ap.add_argument("--list", default="", help="write the differing files and modes here (JSON)")
    ap.add_argument("files", nargs="*")
    a = ap.parse_args(argv)
    modes = a.modes.split(",")
    items = [("files", f, cflags) for f in a.files] if a.files else list(corpus_mod.corpus(a.corpus.split(",")))
    ref = json.load(open(a.load)) if a.load else {}
    tmp = tempfile.mkdtemp(prefix="cmp_bins_")

    def one(item):
        c, p, fl = item
        out = os.path.join(tmp, "o.%d" % threading.get_ident())
        res = {}
        for m in modes:
            key = "%s|%s" % (m, p)
            r = {}
            if a.ref:
                ra = run(os.path.abspath(a.ref), m, fl, p, out)
                r["ref"] = digest(ra)
            else:
                ra = None
                r["ref"] = ref.get(key)
            if a.goosecc:
                rb = run(os.path.abspath(a.goosecc), m, fl, p, out)
                r["new"] = digest(rb)
                if r["ref"] != r["new"]:
                    what = []
                    if ra is not None:
                        what = [n for n, x, y in zip(("status", "stdout", "stderr", "output"), ra, rb) if x != y]
                        if m in ("c", "g") and "output" in what and ra[3] and rb[3]:
                            sa, sb = sections(ra[3], tmp), sections(rb[3], tmp)
                            what.append("sections " + ",".join(sorted(k for k in set(sa) | set(sb) if sa.get(k) != sb.get(k))))
                    r["what"] = " ".join(what)
            res[key] = r
        return c, p, res

    by = collections.defaultdict(lambda: collections.Counter())
    saved = dict(ref)
    diffs = []
    with cf.ThreadPoolExecutor(a.j) as ex:
        for k, (c, p, res) in enumerate(ex.map(one, items)):
            for key, r in res.items():
                m = key.split("|", 1)[0]
                if a.save:
                    saved[key] = r["ref"] if a.ref else r.get("new")
                if a.goosecc:
                    by[c][m + " runs"] += 1
                    if r["ref"] != r["new"]:
                        by[c][m + " differ"] += 1
                        diffs.append({"file": p, "mode": m, "what": r.get("what", "")})
                        if len(diffs) <= a.show:
                            print("DIFF %s %s %s" % (m, p, r.get("what", "")), flush=True)
            if (k + 1) % 250 == 0:
                print("... %d/%d" % (k + 1, len(items)), flush=True)
    if a.save:
        json.dump(saved, open(a.save, "w"), indent=0, sort_keys=True)
        print("saved %d results to %s" % (len(saved), a.save))
    if a.goosecc:
        print("| corpus | " + " | ".join(modes) + " |")
        print("|---|" + "---:|" * len(modes))
        for c, b in by.items():
            print("| %s | " % c + " | ".join("%d/%d differ" % (b[m + " differ"], b[m + " runs"]) for m in modes) + " |")
        print("differences: %d" % len(diffs))
        if a.list:
            json.dump(diffs, open(a.list, "w"), indent=1)
    sys.exit(1 if diffs else 0)


if __name__ == "__main__":
    main()
