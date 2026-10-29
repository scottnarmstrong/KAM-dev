#!/usr/bin/env python3
"""SO-DATA-PY step 2: build, verify and write the advice book of one torus.

usage: sodata_emit.py REC.json OUT.json [--policy support|minimal] [--budget-full 1e-80] [--budget-low 1e-13]

For every recorded product (sodata_record.py):
  * cls 'model'  -> `ProductAdvice.packed P rr ii ri ir` (sodata_advice.build_complex), each of the four real
                    products VERIFIED by the checker mirror: `checkPackedProduct` (shapeOK, raw lengths, shard
                    count, every `checkShard`: block lengths, window length, shardFits, reconFits, intSlotsBound)
                    and the `checkPackedProduct_sound` conclusion on the exact convolution;
  * cls 'scalar' / 'empty' -> `ProductAdvice.direct`.
Negative tests: every corruption of sodata_test.corruptions on the nonzero part (and on one zero part) of every
cfgLow / graph product must FAIL; for the three full-precision products the cheap subset (shape, scale, window
count and length, raw lengths, one in-box slot) is run, since every full check costs minutes.
Budgets (strip remainder of one packed product, SO-ADVCOUNT): 1e-80 full precision, 1e-13 cfgLow and graph.

The output JSON is deterministic (sorted keys, no timestamps); windows are stored run-length encoded as
[[start, [values...]], ...] of their nonzero runs (each window has 2·blockLen - 1 slots).
Untrusted tooling.
"""
import argparse
import hashlib
import json
import time
from fractions import Fraction as F

import rotlib
import sodata_advice as SA
import sodata_packed as SP
import sodata_test as ST

FULL_CHEAP = ("scale 0", "nonzero advice off the box", "short advice window", "missing advice window",
              "raw factor alias", "raw factor truncated", "in-box slot +2")


def rle(win):
    out = []
    i, n = 0, len(win)
    while i < n:
        if win[i] == 0:
            i += 1
            continue
        j = i
        while j < n and win[j] != 0:
            j += 1
        out.append([i, win[i:j]])
        i = j
    return out


def layout_json(L):
    return [list(L.lo), list(L.dims), list(L.stride), L.width, L.blockRows]


def adv_json(adv):
    return dict(la=layout_json(adv.la), lb=layout_json(adv.lb), target=layout_json(adv.target), scale=adv.scale,
                outLog=adv.outLog, windowLen=2 * SP.block_len(adv) - 1, windows=[rle(r) for r in adv.rounded])


def factor_tuple(f):
    return (list(zip(f["k"], f["l"])), f["v"], f["S"], f["ph"])


def negative_tests(adv, da, db, full):
    box = SP.InBoxTable(adv)
    n = 0
    names = []
    for name, a, xa, xb in ST.corruptions(adv, da, db, box):
        base = name.split(" (")[0]
        if full and base not in FULL_CHEAP:
            continue
        ST.must_fail(name, a, xa, xb)
        n += 1
        names.append(base)
    return n, sorted(set(names))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("rec")
    ap.add_argument("out")
    ap.add_argument("--policy", default="support", choices=("support", "minimal"))
    ap.add_argument("--budget-full", type=float, default=1e-80)
    ap.add_argument("--budget-low", type=float, default=1e-13)
    ap.add_argument("--no-negative", action="store_true")
    args = ap.parse_args()
    t0 = time.time()
    raw = open(args.rec, "rb").read()
    rec = json.loads(raw)
    Wt = rotlib.Weights(F(1, 70))
    books = {}
    stats = []
    nneg = 0
    negnames = set()
    for p in rec["products"]:
        t1 = time.time()
        ent = dict(key=p["key"], family=p["family"], cls=p["cls"])
        st = dict(key=p["key"], family=p["family"], cls=p["cls"], book=p["book"])
        if p["cls"] != "model":
            ent["kind"] = "direct"
        else:
            full = p["precision"] == "full"
            budget = args.budget_full if full else args.budget_low
            P, parts = SA.build_complex(factor_tuple(p["a"]), factor_tuple(p["b"]), Wt, budget, policy=args.policy)
            ent.update(kind="packed", P=P, parts={nm: adv_json(adv) for nm, adv, _, _, _ in parts})
            st.update(P=P, terms=[len(p["a"]["v"]), len(p["b"]["v"])], parts={nm: info for nm, _, _, _, info in parts})
            if not args.no_negative:
                tested_zero = False
                for nm, adv, da, db, info in parts:
                    if info["zero"] and (tested_zero or full):
                        continue
                    tested_zero = tested_zero or info["zero"]
                    n, names = negative_tests(adv, da, db, full)
                    nneg += n
                    negnames.update(names)
                    st.setdefault("negative_tests", {})[nm] = n
            nz = [nm for nm, _, _, _, info in parts if not info["zero"]]
            i0 = st["parts"][nz[0]] if nz else None
            print("  %-14s %-46s P %3d  %s  %s (%.1fs)" % (
                str(p["key"]), p["family"][:46], P, nz,
                "w %d shards %d scale %d outLog %d adv-nz %d rad %.1e+%.1e" % (
                    i0["w"], i0["shards"], i0["scale"], i0["outLog"], i0["advice_nonzero"], i0["rad_in"],
                    i0["rad_out"]) if i0 else "zero", time.time() - t1), flush=True)
        books.setdefault(p["book"], []).append(ent)
        stats.append(st)
    out = dict(which=rec["which"], policy=args.policy, budgets=dict(full=args.budget_full, low=args.budget_low),
               rec_sha256=hashlib.sha256(raw).hexdigest(), books=books)
    txt = json.dumps(out, sort_keys=True, separators=(",", ":"))
    with open(args.out, "w") as fh:
        fh.write(txt)
    summ = dict(which=rec["which"], policy=args.policy, rec_sha256=out["rec_sha256"],
                advice_sha256=hashlib.sha256(txt.encode()).hexdigest(), negative_tests=nneg,
                negative_kinds=sorted(negnames), products=stats)
    with open(args.out.replace(".json", "_stats.json"), "w") as fh:
        fh.write(json.dumps(summ, sort_keys=True, indent=1, default=float))
    print("verified %d products (%d packed); %d negative tests rejected; advice sha256 %s (%.0fs)" % (
        len(rec["products"]), sum(1 for p in rec["products"] if p["cls"] == "model"), nneg, summ["advice_sha256"],
        time.time() - t0))


if __name__ == "__main__":
    main()
