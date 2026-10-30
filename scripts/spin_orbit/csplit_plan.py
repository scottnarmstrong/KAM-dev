#!/usr/bin/env python3
"""SO-CSPLIT: segment plans and ledger counts from a census (`csplit_census.py`); untrusted design tooling.

For each composition chain (cfgFull: wanted `v0 :: d1`; cfgLow: wanted `torsionSlots`):

* the live set: the backward closure of the wanted slots, with every fallible op (`char`, `exp`, `inv`, `sqrt`)
  a root (route E's shadow run skips only dead *infallible* ops, see the design §3.3);
* a greedy plan: consecutive segments of the op list whose summed cost stays below the budget (cost = backend
  primitives of the live ops; dead infallible ops cost 0; a packed product adds `SHARD` per shard);
* the ledger: every live slot read across a boundary, plus the wanted slots (terminal exports, audit 1 F3),
  each stored once as `(model, norm)`;
* literal volume: the exact emitted bytes of each ledger model (census field `bytes`, SO-DATA3's `tm` rows);
  stage literals at the census mean (32 B per term).

Usage: python3 -B -I csplit_plan.py CENSUS.json [BUDGET_OPS] [SHARD_OPS] > PLAN.json
(the plan JSON carries the emitted `SegSpec` rows of both chains: the plan itself, not only its counts)
"""
import json
import sys

BYTES_TERM = 58          # fallback only (census without `bytes`): both mantissas 96-bit hex
BYTES_MODEL = 300        # fallback only: def header, degree, radius, norm, list brackets
FALLIBLE = ("char", "exp", "inv", "sqrt")


def live_set(recs, wanted):
    live = set(w for w in wanted)
    for r in recs:
        if r["op"] in FALLIBLE:
            live.add(r["slot"])
    for r in reversed(recs):
        if r["slot"] in live:
            live.update(r["reads"])
    return live


def cost(r, live, shard):
    if r["slot"] not in live and r["op"] not in FALLIBLE:
        return 0
    return r["ops"] + shard * sum(1 for _ in r["packed"]) * 7


def plan(recs, wanted, budget, shard):
    """greedy segments; an op with a packed product is a forced one-op segment (L1b), its products memoized
    (L1c), so its own cost is its census calls only."""
    live = live_set(recs, wanted)
    segs, cur, acc = [], [], 0
    over = []
    for r in recs:
        c = cost(r, live, shard)
        one = bool(r["packed"]) and (r["slot"] in live or r["op"] in FALLIBLE)
        if c > budget and not one:
            over.append((r["slot"], r["op"], c))
        if cur and (one or acc + c > budget):
            segs.append(cur)
            cur, acc = [], 0
        cur.append(r)
        acc += c
        if one:
            segs.append(cur)
            cur, acc = [], 0
    if cur:
        segs.append(cur)
    bounds = [s[0]["slot"] for s in segs[1:]]
    out = {r["slot"]: r["out"] for r in recs}
    ledger, imports = set(wanted), []
    for s in segs:
        lo, hi = s[0]["slot"], s[-1]["slot"] + 1
        imp = set()
        for r in s:
            if r["slot"] in live:
                imp.update(a for a in r["reads"] if a < lo)
        imports.append(len(imp))
        ledger |= imp
    terms = sum(out[i] for i in ledger)
    # the plan literal (SegSpec rows) and the metas, as emitted text
    spec = []
    for s_ in segs:
        lo, hi = s_[0]["slot"], s_[-1]["slot"] + 1
        lv = [r["slot"] for r in s_ if r["slot"] in live]
        imp = sorted({a for r in s_ if r["slot"] in live for a in r["reads"] if a < lo})
        exp = sorted(i for i in ledger if lo <= i < hi)
        spec.append("  ⟨%d, %d, %s, %s, %s⟩,\n" % (lo, hi, lv, imp, exp))
    plan_bytes = sum(len(x) for x in spec) + 400 + (len(segs) + 1) * len("  ⟨000, 0, 0, [cacheRef]⟩,\n")
    memo_bytes = sum(p[3] for s_ in segs for r in s_ for p in r["packed"] if len(p) > 3)
    cuts = [s_[0]["slot"] for s_ in segs if len(s_) == 1 and s_[0]["packed"]]
    byts = {r["slot"]: r.get("bytes", r["out"] * BYTES_TERM + BYTES_MODEL) for r in recs}
    hashes = [r["hash"] for r in recs if r["slot"] in ledger and r.get("hash")]
    return dict(ledgerSlots=sorted(ledger), ledgerHashes=hashes, ledgerBytes=sum(byts[i] for i in ledger),
                live=len(live), liveOps=sum(cost(r, live, 0) for r in recs), segments=len(segs),
                maxSegCost=max(sum(cost(r, live, shard) for r in s) for s in segs),
                ledgerModels=len(ledger), ledgerTerms=terms,
                ledgerMB=round((terms * BYTES_TERM + len(ledger) * BYTES_MODEL) / 1e6, 2),
                maxImports=max(imports), overBudgetOps=over, firstBounds=bounds[:12], oneOpCuts=cuts,
                planBytes=plan_bytes, productMemoBytes=memo_bytes, segSpecs=[x.strip() for x in spec])


def main(path, budget=100000, shard=0):
    r = json.load(open(path))
    w = r["wanted"]
    full = plan(r["composeFull"], w["d1"] + [w["v0"]], budget, shard)
    low = plan(r["composeLow"], sorted(set(w["torsion"])), budget, shard)
    gram_ops = sum(g["ops"] for g in r["gram"])
    tors_ops = sum(s["ops"] for s in r["torsionStages"])
    # Level 2: one theorem per Gram entry / BG entry, one per matrix-product entry, split per product when an
    # entry exceeds the budget; additions and the small tails one each
    def entry_thms(ops, prods):
        return 1 if ops <= budget else prods
    gram_thms = sum(entry_thms(g["ops"] + shard * 7 * len(g["packed"]), len(g["packed"])) for g in r["gram"])
    tors_thms, tors_terms = 0, 0
    for s_ in r["torsionStages"]:
        cells = s_["shape"][0] * s_["shape"][-1]
        per = s_["ops"] / cells
        tors_thms += cells * (1 if per <= budget else s_["shape"][1]) if s_["stage"] == "mul" else 1
        tors_terms += sum(sum(row) for row in s_["out"])
    gram_terms = sum(g["out"] for g in r["gram"])
    gram_bytes = sum(g.get("bytes", 0) for g in r["gram"])
    gram_memo = sum(p[3] for g in r["gram"] for p in g["packed"] if len(p) > 3)
    tors_bytes = sum(s_.get("bytes", 0) for s_ in r["torsionStages"])
    tors_memo = sum(s_.get("packedBytes", 0) for s_ in r["torsionStages"])
    dedup = len(set(full["ledgerHashes"]) | set(low["ledgerHashes"]))
    # complete emitted volume: definitions (model, radius, degree, cached norm; census `bytes`), module headers
    # (one per <= 1,400 lines, 700 B each), plan and metas, stage literals, product memos
    def mods(nbytes):
        return 700 * (1 + nbytes // (1400 * 36))
    vol = dict(cfgFullLedger=full["ledgerBytes"], cfgLowLedger=low["ledgerBytes"],
               plans=full["planBytes"] + low["planBytes"], reflectedWitness=20000,
               composeProductMemos=full["productMemoBytes"] + low["productMemoBytes"],
               gramStages=gram_bytes, gramProductMemos=gram_memo, torsionStages=tors_bytes,
               torsionProductMemos=tors_memo)
    vol["moduleHeaders"] = sum(mods(v) for v in vol.values())
    vol["total"] = sum(vol.values())
    for d in (full, low):
        d.pop("ledgerHashes")
        d["ledgerSlots"] = len(d["ledgerSlots"])
    tails = dict(invRows=len(r.get("invarianceRows", [])), energy=1, frames=len(r.get("frameCornerOps", {})))
    print(json.dumps(dict(budget=budget, shard=shard, cfgFull=full, cfgLow=low, dedupModels=dedup, volume=vol,
                          gramOps=gram_ops, gramPacked=sum(len(g["packed"]) for g in r["gram"]),
                          gramTheorems=gram_thms, gramStageMB=round(gram_terms * 32 / 1e6, 2),
                          torsionStageOps=tors_ops, torsionTheorems=tors_thms,
                          torsionStageMB=round(tors_terms * 32 / 1e6, 2), tails=tails,
                          invRowOps=[x["ops"] for x in r.get("invarianceRows", [])],
                          frameCornerOps=r.get("frameCornerOps")), indent=1))


if __name__ == "__main__":
    main(sys.argv[1], *(int(x) for x in sys.argv[2:]))
