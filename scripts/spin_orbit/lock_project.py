#!/usr/bin/env python3
"""LOCK-DATA: wall-time projection of the lock chain (untrusted tooling): reads the dry schedule (LOCK_DRY=1 lock_mlane.py) and the measured per-module walls of earlier kernel passes; list-schedules L lanes by longest remaining path."""
# Wall-time projection of the lock chain from the dry schedule and measured per-module wall times.
import re, sys, glob, statistics as st, heapq, os
V = "/mnt/HC_Volume_106379410/kam-data/so-lock"
P = "KAM.SpinOrbit.Data.LockN65."
sched = [l.split() for l in open(V + "/dry-d55.txt") if re.match(r"^\d+ KAM", l)]
mods = [m for _, m in sched]
# deps from sources
ROOT = "/root/code/KAM-inp-lockdata"
IMP = re.compile(r"^(?:public )?import (\S+)", re.M)
deps = {m: [i for i in IMP.findall(open(os.path.join(ROOT, *m.split(".")) + ".lean").read()) if i.startswith(P[:-1])] for m in mods}
meas = {}
for f in glob.glob(V + "/*.out"):
    for l in open(f):
        mm = re.match(r"^(KAM\.\S+) rc=0 cpu=\S* wall=(\S+)", l)
        if mm:
            w = mm.group(2).split(":"); s = sum(float(x) * 60 ** i for i, x in enumerate(reversed(w)))
            meas[mm.group(1)] = s
def cls(m):
    r = m[len(P):]
    r = re.sub(r"\d+", "#", r)
    return r
bycls = {}
for m, s in meas.items():
    bycls.setdefault(cls(m), []).append(s)
def coarse(m):
    r = m[len(P):]
    for k, v in (("ShOpsD", 25), ("ShOps", 120), ("ShG", 60), ("DecP", 60), ("Rem", 15), ("Aux", 30), ("Arg", 15),
                 ("Res", 120), ("Rad.", 60), ("Full.", 45), ("Low.", 45), ("Ledger", 8), ("Memo", 15), ("Plan", 10),
                 ("Stage", 10), ("Gram", 60), ("Tors", 60), ("Checks", 120), ("Pass.", 120), ("Prod.", 30)):
        if k in r:
            return v
    return 10   # base data / support (zdecs literals ~3 s elaboration + import)
cost, src = {}, {"meas": 0, "cls": 0, "coarse": 0}
for m in mods:
    if m in meas: cost[m] = meas[m]; src["meas"] += 1
    elif cls(m) in bycls: cost[m] = st.median(bycls[cls(m)]); src["cls"] += 1
    else: cost[m] = coarse(m); src["coarse"] += 1
tot = sum(cost.values())
# critical path
cp = {}
for m in mods:
    cp[m] = cost[m] + max([cp[d] for d in deps[m]], default=0)
def sim(L, scale=1.0):
    # list scheduling, priority = longest remaining path
    tail = {}
    rdeps = {m: [] for m in mods}
    for m in mods:
        for d in deps[m]: rdeps[d].append(m)
    for m in reversed(mods):
        tail[m] = cost[m] + max([tail[x] for x in rdeps[m]], default=0)
    indeg = {m: len(deps[m]) for m in mods}
    ready = [(-tail[m], m) for m in mods if indeg[m] == 0]; heapq.heapify(ready)
    run, t, free = [], 0.0, L
    while ready or run:
        while ready and free:
            _, m = heapq.heappop(ready); heapq.heappush(run, (t + cost[m] * scale, m)); free -= 1
        t, m = heapq.heappop(run); free += 1
        for x in rdeps[m]:
            indeg[x] -= 1
            if indeg[x] == 0: heapq.heappush(ready, (-tail[x], x))
    return t
print("modules", len(mods), "cost sources", src)
print("total serial wall %.1f h; critical path %.2f h" % (tot / 3600, max(cp.values()) / 3600))
for L in (1, 5, 8, 11, 12):
    print("lanes %2d: projected wall %.2f h (x1.3 margin %.2f h)" % (L, sim(L) / 3600, sim(L, 1.3) / 3600))
