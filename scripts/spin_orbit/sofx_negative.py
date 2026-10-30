#!/usr/bin/env python3
"""SO-DATA-1 negative controls on the emitted lunar data (untrusted tooling).

    python3 sofx_negative.py lower|upper DATADIR

(1) tightened err: err := 99/100 of the largest invariance row  ->  checkInvariance must FAIL;
(2) corrupted advice: one in-box nonzero slot of one window of the energy product [0, 10] (cfgFull) is +2
    -> the packed check fails, CertModel.mul takes the crude enclosure, and checkEnergy must FAIL.
Both run on the emitted books (advice JSON) and the emitted data, through the landed-route mirror.
"""
import json
import os
import sys
sys.set_int_max_str_digits(0)
from fractions import Fraction as F

import sofx_model as M
import sofx_check as C
import sofx_lunar as L
import sofx_packed as PK
import sofx_gen as G


def unrle(t):
    out, i = [], 0
    while i < len(t):
        if t[i] == 0:
            out += [0] * t[i + 1]
            i += 2
        else:
            out.append(t[i])
            i += 1
    return out


def lay(j):
    return PK.Layout(j[0], j[1], j[2], j[3], j[4])


def adv_of(j):
    if j[0] == "direct":
        return ("direct",)
    parts = []
    for a in j[2:]:
        parts.append(PK.Advice(lay(a["la"]), lay(a["lb"]), lay(a["target"]), a["scale"],
                               [unrle(r) for r in a["rounded"]], a["outLog"]))
    return ("packed", j[1], *parts)


def load_books(path):
    a = json.load(open(path))
    return {nm: [(tuple(k), adv_of(v)) for k, v in bk] for nm, bk in a.items()}


def cert(which, d, books, eng):
    cf, cl = G.make_cfgs(eng, books)
    p = d["params"]
    c = L.build(which, F(p["err"]), F(p["disp"]), cf, cl, G.HALV, G.TAYLOR)
    c.torsInv = [[(int(z[0]), int(z[1])) for z in r] for r in d["torsInv"]]
    return c


def main(which, ddir):
    d = json.load(open(os.path.join(ddir, "%s_cert.json" % which)))
    books = load_books(os.path.join(ddir, "%s_advice.json" % which))
    rep = {}
    eng = PK.PackedEngine({})
    # (1) tightened err
    c = cert(which, d, books, eng)
    i0 = {}
    C.checkInvariance(c.B, c, i0)
    worst = max(F(x) for x in i0["rows"])
    c.params["err"] = worst * F(99, 100)
    i1 = {}
    ok = C.checkInvariance(c.B, c, i1)
    rep["tightened_err"] = dict(err=str(c.params["err"]), checkInvariance=ok, expected=False)
    print("tightened err -> checkInvariance", ok, flush=True)
    # (2) corrupted advice window of [0, 10]
    bk = dict(books)
    full = list(bk["cfgFull"])
    for idx, (k, adv) in enumerate(full):
        if k == (0, 10) and adv[0] == "packed":
            parts = list(adv[2:])
            for pi, a in enumerate(parts):
                if a.rounded:
                    for s, r in enumerate(a.rounded):
                        j = next((q for q, x in enumerate(r) if x != 0), None)
                        if j is not None:
                            r2 = list(r)
                            r2[j] += 2
                            rr = list(a.rounded)
                            rr[s] = r2
                            parts[pi] = PK.Advice(a.la, a.lb, a.target, a.scale, rr, a.outLog)
                            break
                    break
            full[idx] = (k, ("packed", adv[1], *parts))
            break
    bk["cfgFull"] = full
    c2 = cert(which, d, bk, PK.PackedEngine({}))
    i2 = {}
    ok2 = C.checkEnergy(c2.B, c2, i2)
    rep["corrupted_advice_0_10"] = dict(checkEnergy=ok2, expected=False, value=str(i2.get("value")))
    print("corrupted [0,10] advice -> checkEnergy", ok2, flush=True)
    rep["all_rejected"] = (ok is False) and (ok2 is False)
    json.dump(rep, open(os.path.join(ddir, "%s_negative.json" % which), "w"), indent=1, default=str)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
