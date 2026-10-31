#!/usr/bin/env python3
"""SO-CSEG: per-family kernel time and peak RSS from the kbuild logs (both lanes), for the handoff."""
import collections
import re

D = "/mnt/HC_Volume_106379410/kam-data/so-cseg/kbuild/"
fam = collections.defaultdict(lambda: [0, 0.0, 0, ""])   # count, wall sum, max rss kB, module of the max
last = {}
for tsv in ("kbuild.tsv", "kbuild_lane2.tsv"):
    for l in open(D + tsv):
        m, kind, rc, wall, rss = l.rstrip("\n").split("\t")
        if rc == "0" and kind == "heavy":
            last[m] = (float(wall), int(rss or 0))
for m, (wall, rss) in last.items():
    T = "lower" if ".Lower." in m else ("upper" if ".Upper." in m else "shared")
    tail = m.split(".Seg.")[-1] if ".Seg." in m else m.split(".")[-1]
    f = re.sub(r"\d+(_\d+)*", "#", tail.split(".")[-1] if "." not in tail else tail)
    f = re.sub(r"\d+", "#", tail)
    key = (T, f)
    e = fam[key]
    e[0] += 1
    e[1] += wall
    if rss > e[2]:
        e[2], e[3] = rss, m
print("| torus | family | theorems | wall total (s) | peak RSS (GB) |")
print("|---|---|---:|---:|---:|")
for (T, f), (n, w, r, mm) in sorted(fam.items()):
    print("| %s | %s | %d | %.0f | %.2f |" % (T, f, n, w, r / 1e6))
tot = sum(e[1] for e in fam.values())
print("\ntotal heavy wall %.2f h over %d theorems; max peak %.2f GB" % (tot / 3600, sum(e[0] for e in fam.values()),
                                                                        max(e[2] for e in fam.values()) / 1e6))
