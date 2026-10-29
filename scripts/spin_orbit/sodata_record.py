#!/usr/bin/env python3
"""SO-DATA-PY step 1: enumerate every product the Revision 7 checker performs on one R1 lunar torus, with its
factors and its `ProductKey`, by rerunning SO-ADVCOUNT's recorded pipeline (adv_count.py: SO-GEN2's
rot_build.build(which, 88, 88, 88, 318) and rot_norms.norms with every `SPoly.mul` recorded, plus the
`checkSoGraph` SOS witnesses).

usage: sodata_record.py which OUT.json          (which = lower | upper)

Output (deterministic JSON, sorted, one record per product in call order):
  key     the ProductKey [site, sub, ordinal] (site codes of A-E: compose 0, exp witnesses 1, Gram 3,
          torsion 4, SOS 7; `sub` numbers the call sites of one site code in order of first appearance;
          `ordinal` counts the calls of one call site, so keys are unique);
  book    the ModelConfig advice book: 'full' (cfgFull: energy compose, witness residuals), 'low' (cfgLow:
          Gram, torsion), 'graph' (the SOS products of checkSoGraph);
  cls     'model' (a genuine product: advice `packed`), 'scalar' (a one-term constant factor) or 'empty'
          (an empty factor): the latter two get `ProductAdvice.direct`;
  a, b    the factors: keys, integer mantissas, scale S (value = i^ph * v / 2^S), parity phase ph.
The keys are a PROPOSED convention: SO-MALG / SO-EMB / SO-TORS fix the real call-site keys; only the KEY_SITE
table below then changes.  Untrusted tooling.
"""
import hashlib
import json
import os
import sys
import time

import numpy as np

import adv_count
import rotlib
from rotlib import SPoly

# (call-site prefix of adv_count's site string or family) -> (site code, book)
KEY_SITE = [
    ("energy:", 0, "full"),                  # compose (energy, wanted v0): SLP slot 10 = (A0*A0), the only MM slot
    ("exp witness residual", 1, "full"),
    ("Gram", 3, "low"),
    ("torsion", 4, "low"),
    ("graph SOS", 7, "graph"),
]


def site_of(fam):
    for pre, code, book in KEY_SITE:
        if fam.startswith(pre):
            return code, book
    raise KeyError(fam)


def factor_json(f):
    k, l, v, S, ph = f
    return dict(k=[int(x) for x in k], l=[int(x) for x in l], v=[int(x) for x in v], S=int(S), ph=int(ph))


def main(which, outpath):
    t0 = time.time()
    import rot_build
    import rot_norms
    adv_count.REC.clear()
    SPoly.mul = adv_count._rec_mul
    adv_count.STAGE[0] = "build"
    cand = rot_build.build(which, 88, 88, 88, 318)
    d = json.load(open(os.path.join(rotlib.CERT, "%s_rot.json" % which)))
    assert cand["nv_half"] == d["stats"]["v_terms_half"] and cand["nE"] == d["stats"]["E_terms"], "R1 mismatch"
    adv_count.STAGE[0] = "norms"
    nr = rot_norms.norms(cand, cand["bounds"]["Delta"])
    SPoly.mul = adv_count._orig_mul
    Wt = rotlib.Weights(rotlib.F(1, 70))
    for name, gi, Sg, info in adv_count.sos_witnesses(cand["p"], Wt, which):
        kk = np.array([k for k, _ in gi], dtype=np.int64)
        ll = np.array([l for _, l in gi], dtype=np.int64)
        vv = rotlib._obj(list(gi.values()))
        adv_count.REC.append(dict(site="adv_count.py:sos:" + name, text="SOS " + name, a=(kk, ll, vv, Sg, 0),
                                  b=(kk, ll, vv, Sg, 0), stage="graph"))
    sub_of = {}
    ordinal = {}
    recs = []
    for r in adv_count.REC:
        fam, prec = adv_count.family(r["text"])
        code, book = site_of(fam)
        site = r["site"]
        subs = sub_of.setdefault(code, {})
        if site not in subs:
            subs[site] = len(subs)
        sub = subs[site]
        o = ordinal.get(site, 0)
        ordinal[site] = o + 1
        key = [code, 10] if code == 0 else [code, sub, o]
        recs.append(dict(key=key, book=book, family=fam, precision=prec, site=site, stage=r["stage"],
                         cls=adv_count.classify(r), a=factor_json(r["a"]), b=factor_json(r["b"])))
    keys = [tuple(x["key"]) for x in recs]
    assert len(set(keys)) == len(keys), "ProductKey collision"
    out = dict(which=which, generator="sodata_record.py", n_products=len(recs),
               norms_check=dict(delta=nr["gram"]["delta"], delta_T=nr["torsion"]["delta_T"]), products=recs)
    txt = json.dumps(out, sort_keys=True, separators=(",", ":"))
    with open(outpath, "w") as fh:
        fh.write(txt)
    print("recorded %d products (%s) -> %s  sha256 %s  (%.0fs)" % (
        len(recs), ", ".join("%s %d" % (c, sum(1 for x in recs if x["cls"] == c)) for c in ("model", "scalar", "empty")),
        outpath, hashlib.sha256(txt.encode()).hexdigest(), time.time() - t0))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
