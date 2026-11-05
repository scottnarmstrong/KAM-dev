#!/usr/bin/env python3
"""LOCK-DATA: wall-time projection of the lock chain (untrusted tooling).

    lock_project.py ROOT TARGET LANES[,LANES...] [--variant joined|split] [--est CLASS=SECONDS ...]

ROOT: a tree with KAM/SpinOrbit/Data/LockN65 (sources; the Seg links select the emitted tree). The schedule is the
import closure of TARGET within LockN65 (lock_mlane.closure). Per-module wall seconds, in order of preference:
  1. the module's own measured wall in the D55-form template pass (tpd55*.out),
  2. the median wall of its class in tpd55 (class: digits -> #, heavy/light product modules separated),
  3. the median of its class in the earlier passes (tpass*, kseg*, kpass*: finer split forms),
  4. an explicit estimate (ESTIMATES below, or --est), reported as E.
Variant `joined` (D55 as frozen first): a heavy product's side checks inside its product module (cost: the measured
joined product walls, mean for the unmeasured ones; the Aux modules cost 0). Variant `split`: the side checks in
their own modules (measured fine-form Aux walls). List scheduling over LANES lanes, longest remaining path first.
"""
import glob
import heapq
import os
import re
import statistics as st
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lock_mlane as LM   # noqa: E402

V = "/mnt/HC_Volume_106379410/kam-data/so-lock"
P = "KAM.SpinOrbit.Data.LockN65."
# explicit estimates (seconds of wall per module) for classes with no measurement; E in the report
ESTIMATES = {
    "Seg.Prod.M#ShG#": 90, "Seg.Prod.M#RRShG#": 90, "Seg.Prod.M#RIShG#": 90, "Seg.Prod.M#IIShG#": 90,
    "Seg.Prod.M#IRShG#": 90,                       # light products: 4-shard groups without operand literals
    "Seg.Prod.M#|light": 120,                      # light product module (side checks joined, small operands)
    "Seg.Prod.M#Sh": 10, "Seg.Prod.M#RRSh": 10, "Seg.Prod.M#RISh": 10, "Seg.Prod.M#IISh": 10,
    "Seg.Prod.M#IRSh": 10,                         # shard facades
    "Seg.Tors.S#": 120, "Seg.Gram.E#": 120, "Seg.Gram.BG#": 120, "Seg.Checks.Inv#": 600,
    "Seg.Checks.Energy": 600, "Seg.Checks.FrameN": 600, "Seg.Checks.FrameT": 600, "Seg.Checks.Torsion": 600,
    "Seg.Checks": 60, "Seg.Chain": 60, "Seg.Gram.Check": 120,
    "Pass.Graph#": 600, "Pass.GraphLoC#": 5400, "Pass.GraphHiC#": 5400, "Pass.Embedding#": 300, "Pass.FrameL#V#": 300,
}
DEFAULT = 15


def wall(s):
    return sum(float(x) * 60 ** i for i, x in enumerate(reversed(s.split(":"))))


def measured(pattern):
    out = {}
    for f in sorted(glob.glob(os.path.join(V, pattern))):
        for l in open(f):
            m = re.match(r"^(KAM\.\S+) rc=0 cpu=\S* wall=(\S+)", l)
            if m:
                out[m.group(1)] = wall(m.group(2))
    return out


def cls(m, heavyp):
    r = m[len(P):]
    k = re.sub(r"\d+$", "#", re.sub(r"M\d+", "M#", r))
    k = re.sub(r"^Seg\.(Full|Low)\.S#$", r"Seg.\1.S#", k)
    if k == "Seg.Prod.M#":
        k += "|heavy" if re.search(r"\.M(\d+)$", m).group(1) in heavyp else "|light"
    return k


def main(argv):
    root, target, lanes = argv[0], argv[1], [int(x) for x in argv[2].split(",")]
    variant = argv[argv.index("--variant") + 1] if "--variant" in argv else "split"
    for a in argv:
        if "=" in a and not a.startswith("--"):
            k, v = a.split("=")
            ESTIMATES[k] = float(v)
    order, deps = LM.closure([target], root)
    assert not LM.MISSING, LM.MISSING[:3]
    seg = os.path.join(root, "KAM/SpinOrbit/Data/LockN65/Seg/Prod")
    heavyp = {re.match(r"M(\d+)ShOps\.lean$", f).group(1) for f in os.listdir(seg) if re.match(r"M\d+ShOps\.lean$", f)}
    now = {}
    for pat in ("tpd55*.out", "tp[2-9]*.out", "tp1[0-9]*.out", "m1900*.out"):
        now.update(measured(pat))
    old = {}
    for pat in ("tpass*.out", "kseg*.out", "kpass*.out"):
        old.update(measured(pat))
    bynow, byold = {}, {}
    for d, b in ((now, bynow), (old, byold)):
        for m, s in d.items():
            b.setdefault(cls(m, heavyp), []).append(s)
    joined = [now[P + "Seg.Prod.M%s" % k] for k in ("0", "1", "202", "203") if P + "Seg.Prod.M%s" % k in now]
    cost, src = {}, {"M": 0, "Mc": 0, "Mo": 0, "E": 0}
    estm = {}
    for m in order:
        c = cls(m, heavyp)
        prod_heavy = c == "Seg.Prod.M#|heavy"
        if variant == "joined" and re.search(r"Aux\d+(C\d+)?$", m) and re.search(r"\.M(\d+)Aux", m).group(1) in heavyp:
            cost[m] = 0.0
            continue
        if variant == "joined" and prod_heavy:
            cost[m] = now.get(m, st.mean(joined))
            src["M" if m in now else "Mc"] += 1
            continue
        if variant == "split" and prod_heavy:
            cost[m] = 40.0                       # split-form product assembly (tpass9: 0.6-0.7 GB, ~30-45 s)
            src["Mo"] += 1
            continue
        if m in now and not (variant == "split" and prod_heavy):
            cost[m] = now[m]; src["M"] += 1
        elif c in bynow:
            cost[m] = st.median(bynow[c]); src["Mc"] += 1
        elif c in byold:
            cost[m] = st.median(byold[c]); src["Mo"] += 1
        else:
            e = ESTIMATES.get(c, ESTIMATES.get(re.sub(r"#", "", c), DEFAULT))
            cost[m] = e; src["E"] += 1
            estm[c] = estm.get(c, 0) + 1
    tot = sum(cost.values())
    rdeps = {m: [] for m in order}
    for m in order:
        for d in deps[m]:
            rdeps[d].append(m)
    tail = {}
    for m in reversed(order):
        tail[m] = cost[m] + max([tail[x] for x in rdeps[m]], default=0)

    def sim(L, scale):
        indeg = {m: len(deps[m]) for m in order}
        ready = [(-tail[m], m) for m in order if indeg[m] == 0]
        heapq.heapify(ready)
        run, t, free = [], 0.0, L
        while ready or run:
            while ready and free:
                _, m = heapq.heappop(ready)
                heapq.heappush(run, (t + cost[m] * scale, m))
                free -= 1
            t, m = heapq.heappop(run)
            free += 1
            for x in rdeps[m]:
                indeg[x] -= 1
                if indeg[x] == 0:
                    heapq.heappush(ready, (-tail[x], x))
        return t

    print("variant %s: modules %d; cost sources: own measured %d, class measured (D55) %d, class measured "
          "(earlier forms) %d, estimated %d" % (variant, len(order), src["M"], src["Mc"], src["Mo"], src["E"]))
    print("estimated classes:", ", ".join("%s x%d" % kv for kv in sorted(estm.items(), key=lambda x: -x[1])))
    print("total serial %.1f h; critical path %.2f h" % (tot / 3600, max(tail.values()) / 3600))
    for L in lanes:
        print("lanes %2d: %.2f h (x1.3: %.2f h)" % (L, sim(L, 1.0) / 3600, sim(L, 1.3) / 3600))


if __name__ == "__main__":
    main(sys.argv[1:])
