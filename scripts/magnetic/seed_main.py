#!/usr/bin/env python3
"""Seed main's Lake build with the build artifacts of a landing branch (MAG-SEAL landing).

Usage:
  seed_main.py --src SRC_BUILD --dst DST_BUILD [--tree SRC_TREE] [--list OUT.tsv] [--apply] [--data-dir DIR]

Lists every file under SRC_BUILD/{lib,ir} that DST_BUILD lacks or holds with different bytes,
excluding ir/**/*.setup.json (written by Lake per build, carries the worktree path), `*.nobuild`
markers, and the artifacts of modules with no source in --tree (stale outputs of renamed or moved
modules, e.g. the pre-move KAM/Magnetic/Data/{CsegGraph,CsegSupport,Format}). Without
--apply it only prints counts and sizes (dry run). With --apply it copies them (cp -p semantics,
via a temporary name and an atomic rename).

--data-dir DIR (optional, with --apply): place the artifacts of the generated magnetic data
(lib/lean/KAM/Magnetic/Data and ir/KAM/Magnetic/Data) under DIR/{lib,ir} on another disk and
replace the two destination directories by single directory symlinks to them. The few artifacts
main already has there are carried over first. --link (with --data-dir on the source's filesystem)
hard-links the data artifacts into DIR instead of copying them (no extra space); a later rebuild of
those modules in the source worktree would then share inodes, so retire the source build or rebuild
nothing there afterwards.
"""
import argparse, filecmp, os, re, shutil, sys

DATA = ("lib/lean/KAM/Magnetic/Data", "ir/KAM/Magnetic/Data")

ART = re.compile(r"\.(olean|ilean|ir|c|trace|olean\.private|olean\.server|ir\.sig)(\.hash)?$")

def module_of(rel):
    m = rel[len("lib/lean/"):] if rel.startswith("lib/lean/") else rel[len("ir/"):]
    return ART.sub("", m)

def walk(src, tree):
    for top in ("lib", "ir"):
        for dp, dns, fns in os.walk(os.path.join(src, top)):
            dns.sort()
            for fn in sorted(fns):
                rel = os.path.relpath(os.path.join(dp, fn), src)
                if rel.startswith("ir" + os.sep) and fn.endswith(".setup.json"):
                    continue
                if fn.endswith(".nobuild"):
                    continue
                m = module_of(rel)
                if m == rel or not os.path.exists(os.path.join(tree, m + ".lean")):
                    continue  # not a module artifact, or no source: stale
                yield rel

def needed(src, dst, tree):
    for rel in walk(src, tree):
        s, d = os.path.join(src, rel), os.path.join(dst, rel)
        if os.path.islink(s):
            sys.exit(f"symlink in source tree: {s}")
        if not os.path.exists(d):
            yield rel, "new", os.path.getsize(s)
        elif os.path.getsize(s) != os.path.getsize(d) or not filecmp.cmp(s, d, shallow=False):
            yield rel, "changed", os.path.getsize(s)

def copy(s, d, link=False):
    os.makedirs(os.path.dirname(d), exist_ok=True)
    tmp = d + ".seedtmp"
    if os.path.lexists(tmp):
        os.unlink(tmp)
    if link:
        os.link(s, tmp)
    else:
        shutil.copy2(s, tmp)
    os.replace(tmp, d)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", required=True)
    ap.add_argument("--dst", required=True)
    ap.add_argument("--tree", default=".", help="source tree whose modules count (default .)")
    ap.add_argument("--list")
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("--data-dir")
    ap.add_argument("--link", action="store_true", help="hard-link the data artifacts into --data-dir")
    a = ap.parse_args()
    src, dst = os.path.abspath(a.src), os.path.abspath(a.dst)
    rows = list(needed(src, dst, os.path.abspath(a.tree)))
    tot = {}
    for rel, kind, sz in rows:
        grp = "magnetic-data" if rel.startswith(DATA) else "other"
        k = (grp, rel.split(os.sep)[0], kind)
        n, b = tot.get(k, (0, 0)); tot[k] = (n + 1, b + sz)
    for k in sorted(tot):
        n, b = tot[k]; print(f"{k[0]:14} {k[1]:4} {k[2]:8} {n:7} files {b/2**30:8.2f} GiB")
    print(f"TOTAL {len(rows)} files {sum(r[2] for r in rows)/2**30:.2f} GiB")
    if a.list:
        with open(a.list, "w") as f:
            for rel, kind, sz in rows:
                f.write(f"{rel}\t{kind}\t{sz}\n")
    if not a.apply:
        print("dry run (pass --apply to copy)"); return
    if a.link and not a.data_dir:
        sys.exit("--link needs --data-dir")
    if a.data_dir:
        dd = os.path.abspath(a.data_dir)
        for sub in DATA:
            dlink, target = os.path.join(dst, sub), os.path.join(dd, sub.split(os.sep)[0])
            if os.path.islink(dlink):
                if os.path.realpath(dlink) != os.path.realpath(target):
                    sys.exit(f"{dlink} links elsewhere: {os.readlink(dlink)}")
                continue
            os.makedirs(target, exist_ok=True)
            if os.path.isdir(dlink):  # carry main's existing data artifacts over first
                shutil.copytree(dlink, target, symlinks=True, dirs_exist_ok=True)
                shutil.rmtree(dlink)
            os.makedirs(os.path.dirname(dlink), exist_ok=True)
            os.symlink(target, dlink)
            print(f"symlink {dlink} -> {target}")
        with open(os.path.join(dd, "IN-USE.txt"), "w") as f:
            f.write(f"IN USE: {dst}/{{{DATA[0]},{DATA[1]}}} are symlinks into this directory "
                    "(magnetic data build artifacts, MAG-SEAL landing). Do not delete or move.\n")
    for i, (rel, kind, sz) in enumerate(rows):
        copy(os.path.join(src, rel), os.path.join(dst, rel), link=a.link and rel.startswith(DATA))
        if i % 2000 == 0:
            print(f"{i}/{len(rows)}", flush=True)
    print(f"copied {len(rows)} files")

if __name__ == "__main__":
    main()
