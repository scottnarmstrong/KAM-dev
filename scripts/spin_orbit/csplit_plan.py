#!/usr/bin/env python3
"""SO-CSEG-GEN: segment plans of the two composition chains (untrusted tooling; the kernel checks the plan).

From a census (`csplit_census.py`), for each chain (cfgFull: wanted `d1 ++ [v0]`; cfgLow: wanted `torsionSlots`):

* the live set: the backward closure of the wanted slots, with every fallible op (`char`, `exp`, `inv`, `sqrt`) a
  root, exactly `SegSpec.liveEff`'s notion (the shadow run computes live and fallible ops, skips the rest);
* forced one-op segments (L1b): every evaluated op carrying a packed product (lunar: slot 10 `[0,10]` in cfgFull,
  the character slot 28 in both chains); their products are memoized (L1c) and cost 0 here;
* the cut points by dynamic programming: every other segment's census cost (backend calls of its live and
  fallible ops) is at most the budget B; among those plans, minimize `THM_BYTES · segments + Σ import bytes`
  (each segment's imports priced at their ledger bytes; the reported ledger is the union, a slot imported by
  several segments is stored once);
* the `SegSpec` rows: `start`, `stop`, `live` (the segment's live slots), `imports` (ledger slots `< start`
  read by its live ops, sorted), `exports` (ledger slots in the segment), and the ledger (wanted ∪ imports).

B: `--budget N`, or `--gate GATE.json` (field `B`, written by the calibration gate CAL-1/2).

Usage: python3 -B -I csplit_plan.py CENSUS.json OUT.json [--budget N | --gate GATE.json]
"""
import json
import sys

FALLIBLE = ("char", "exp", "inv", "sqrt")
THM_BYTES = 20000          # one segment theorem ~ its fixed cost (8-10 s per theorem) in import-byte units


def live_set(recs, wanted):
    live = set(wanted)
    for r in recs:
        if r["op"] in FALLIBLE:
            live.add(r["slot"])
    for r in reversed(recs):
        if r["slot"] in live:
            live.update(r["reads"])
    return live


def plan_chain(recs, wanted, budget):
    n = len(recs)
    assert [r["slot"] for r in recs] == list(range(n))
    live = live_set(recs, wanted)
    ev = [r["slot"] in live or r["op"] in FALLIBLE for r in recs]
    cost = [r["ops"] if ev[i] else 0 for i, r in enumerate(recs)]
    forced = [ev[i] and bool(r["packed"]) for i, r in enumerate(recs)]
    byts = [r.get("bytes", 0) for r in recs]
    over = [(i, recs[i]["op"], cost[i]) for i in range(n) if cost[i] > budget and not forced[i]]
    INF = float("inf")
    best = [INF] * (n + 1)
    back = [0] * (n + 1)
    best[0] = 0
    for j in range(1, n + 1):
        # segment [i, j)
        if forced[j - 1]:
            cands = [j - 1]
        else:
            cands = []
            acc = 0
            for i in range(j - 1, -1, -1):
                if forced[i]:
                    break
                acc += cost[i]
                if acc > budget and i < j - 1:
                    break
                cands.append(i)
        for i in cands:
            if best[i] == INF:
                continue
            imp = set()
            for k in range(i, j):
                if ev[k]:
                    imp.update(a for a in recs[k]["reads"] if a < i)
            c = best[i] + THM_BYTES + sum(byts[a] for a in imp)
            if c < best[j]:
                best[j], back[j] = c, i
    cuts, j = [], n
    while j > 0:
        cuts.append((back[j], j))
        j = back[j]
    cuts.reverse()
    segs, ledger = [], set(wanted)
    for lo, hi in cuts:
        imp = sorted({a for k in range(lo, hi) if ev[k] for a in recs[k]["reads"] if a < lo})
        ledger |= set(imp)
        segs.append(dict(start=lo, stop=hi, live=[k for k in range(lo, hi) if k in live], imports=imp))
    for s in segs:
        s["exports"] = sorted(i for i in ledger if s["start"] <= i < s["stop"])
        s["cost"] = sum(cost[k] for k in range(s["start"], s["stop"]))
        s["forced"] = s["stop"] - s["start"] == 1 and forced[s["start"]]
    return dict(wanted=list(wanted), live=sorted(live), segs=segs, ledger=sorted(ledger),
                ledgerBytes=sum(byts[i] for i in ledger), segments=len(segs),
                maxSegCost=max(s["cost"] for s in segs if not s["forced"]),
                forcedCuts=[s["start"] for s in segs if s["forced"]], overBudgetOps=over,
                maxImports=max(len(s["imports"]) for s in segs))


def main(argv):
    path, out = argv[0], argv[1]
    budget = 75000
    if "--budget" in argv:
        budget = int(argv[argv.index("--budget") + 1])
    if "--gate" in argv:
        budget = int(json.load(open(argv[argv.index("--gate") + 1]))["B"])
    r = json.load(open(path))
    w = r["wanted"]
    full = plan_chain(r["composeFull"], list(w["d1"]) + [w["v0"]], budget)
    low = plan_chain(r["composeLow"], list(w["torsion"]), budget)
    res = dict(which=r["which"], budget=budget, cfgFull=full, cfgLow=low)
    json.dump(res, open(out, "w"), indent=1)
    for nm, p in (("cfgFull", full), ("cfgLow", low)):
        print(nm, "segments", p["segments"], "forced", p["forcedCuts"], "maxSegCost", p["maxSegCost"],
              "ledger", len(p["ledger"]), "models", p["ledgerBytes"], "bytes", "maxImports", p["maxImports"],
              "over", p["overBudgetOps"])


if __name__ == "__main__":
    main(sys.argv[1:])
