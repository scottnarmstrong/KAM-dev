#!/usr/bin/env python3
"""SO-DATA-1: cross-check the sofx mirror (backend RatB, exact) against the aligned toy ℚ mirror (toy_check.py)
on the four toy certificates (certificates/so-toys/*.json): per sub-check verdicts must coincide, and the exact
quantities compared (invariance row sups, energy value, Gram rows, torsion δ_T) must be EQUAL as rationals.
Then the same certificates are re-run on FixedB(P) (P = 320, 448) with the data rounded outward where needed,
as a smoke test of the fixed-point paths (verdicts recorded, not asserted).

    python3 sofx_toyxcheck.py [OUT.json]
"""
import json
import os
import sys
sys.set_int_max_str_digits(0)
import copy
from fractions import Fraction as F

import sofx_arith as A
import sofx_model as M
import sofx_check as C
import toy_check as TCK
import toy_arith as TA

HERE = os.path.dirname(os.path.abspath(__file__))
TOYS = os.path.join(HERE, "..", "..", "certificates", "so-toys")


def q(x):
    return F(x)


def conv_ops(ops):
    out = []
    for op in ops:
        t = op[0]
        if t == "C":
            out.append(("const", q(op[1]), q(op[2]), int(op[3])))
        elif t == "A":
            out.append(("action", op[1]))
        elif t == "X":
            out.append(("char", tuple(op[1])))
        elif t == "+":
            out.append(("add", op[1], op[2]))
        elif t == "*":
            out.append(("mul", op[1], op[2]))
        elif t == "E":
            out.append(("exp", op[1]))
        elif t == "I":
            out.append(("inv", op[1]))
        else:
            raise ValueError(op)
    return out


def load(name, B, conv):
    """the toy certificate as a sofx Cert on backend B; conv(q) maps an exact rational datum to B."""
    raw = json.load(open(os.path.join(TOYS, name + ".json")))["certificate"]
    jets = json.load(open(os.path.join(TOYS, "jets.json")))["jets"]
    jt = jets["T2" if name == "TR" else name]
    c = C.Cert()
    c.B, c.n = B, raw["n"]
    p = raw["params"]
    c.params = dict(tau=int(p["tau"]), rho=q(p["rho"]), rhoInf=q(p["rhoInf"]), M=q(p["M"]), sK=q(p["sK"]),
                    sB=q(p["sB"]), sT=q(p["sT"]), mu=q(p["mu"]), gbar=q(p["gbar"]), som=q(p["sigma_omega"]),
                    nu=q(p["nuRay"]), gamma=q(p["gamma"]), s=q(p["s"]), err=q(p["err"]), E0=q(p["E0"]),
                    disp=q(p["disp"]))
    c.jet = dict(prog=conv_ops(jt["ops"]), v0=jt["v0"], d1=jt["d1"], d2=jt["d2"], d3=jt["d3"])
    c.jetOps = c.jet["prog"]
    c.jetOps_toy = TA.parse_ops(jt["ops"])
    c.expHalvings, c.expOrder = raw["expHalvings"], raw["expOrder"]
    c.weight = M.Weight(q(raw["weight"]["rho"]), q(raw["weight"]["w"]))
    c.weightH = M.Weight(q(raw["weightH"]["rho"]), q(raw["weightH"]["w"]))
    c.centre = [q(x) for x in raw["centre"]]
    c.radius = [q(x) for x in raw["radius"]]
    c.freqBox = [(q(a), q(b)) for a, b in raw["freqBox"]]

    def cc(z):
        return (conv(q(z[0])), conv(q(z[1])))

    def poly(P):
        return [(tuple(k), cc(z)) for k, z in P]

    def rpoly(R):
        return M.RealPoly(conv(q(R["zero"])), poly(R["half"]))
    e = raw["emb"]
    c.emb = M.Embedding([int(x) for x in e["angleDeg"]], [rpoly(R) for R in e["angle"]],
                        [int(x) for x in e["actionDeg"]], [rpoly(R) for R in e["action"]])
    w = raw["wit"]
    ew = lambda E: (poly(E["poly"]), E["pinHalvings"], E["pinOrder"])
    c.wit = M.Witnesses([ew(E) for E in w["expWit"]], [poly(Q) for Q in w["invWit"]],
                        [(tuple(k), ew(E)) for k, E in w["charWit"]])
    c.gramInv = [[poly(P) for P in r] for r in raw["gramInv"]]
    c.torsInv = [[cc(z) for z in r] for r in raw["torsInv"]]
    pe = raw["piEnc"]
    c.piEnc = A.PiEnclosure(conv(q(pe["centre"])), conv(q(pe["rad"])), pe["machinK"], pe["machinJ"])
    if isinstance(B, A.FixedB):     # widen the π enclosure by 4 ulp (rounding of centre/rad)
        c.piEnc.rad = B.upAdd(B.ofRatUp(q(pe["rad"])), 4)
    for nm in ("cfgFull", "cfgLow"):
        cf = raw[nm]
        book = [(tuple(k), ("direct",)) for k, a in cf["advice"]]
        setattr(c, nm, M.Cfg(nm, cf["cutoff"], cf["taylorN"], cf["halvings"], book))
    c.DKc = C.dkCache(B, c.n, c.emb, c.weight, c.piEnc)
    c.graph = None
    return c, raw


def run_sofx(c):
    out = {}
    for name, f in C.SUBCHECKS:
        info = {}
        try:
            ok = f(c.B, c, info)
        except Exception as ex:          # recorded, never hidden
            ok, info = None, dict(exception=repr(ex))
        out[name] = (ok, info)
    return out


def run_toy(name):
    raw = json.load(open(os.path.join(TOYS, name + ".json")))["certificate"]
    jets = json.load(open(os.path.join(TOYS, "jets.json")))["jets"]
    c = TCK.load_cert(raw, jets["T2" if name == "TR" else name]) if hasattr(TCK, "load_cert") else None
    return c


def main():
    outp = sys.argv[1] if len(sys.argv) > 1 else None
    import toy_gen
    rep = {}
    for name in ("T2", "T2d", "T3", "TR"):
        c, raw = load(name, A.RatB(), lambda x: x)
        r = run_sofx(c)
        verd = {k: v[0] for k, v in r.items()}
        # the toy mirror's verdicts, recorded in the certificate JSON by toy_gen (verification block)
        ver = json.load(open(os.path.join(TOYS, name + ".json")))["verification"]
        rep[name] = dict(sofx_rat=verd, toy=ver.get("subchecks", ver.get("verdicts")),
                         sofx_info={k: {kk: (str(vv) if isinstance(vv, F) else vv) for kk, vv in v[1].items()
                                        if kk in ("margin", "rows", "value", "deltaT", "dRows", "bounds", "C1_ratio")}
                                    for k, v in r.items()})
        print(name, "sofx(ℚ):", verd, flush=True)
        mg = ver["margins"]
        cmp = dict(
            inv=(max(r["checkInvariance"][1]["rows"]) if "rows" in r["checkInvariance"][1] else None,
                 mg["checkInvariance"]["bound"]),
            energy=(r["checkEnergy"][1].get("value"), mg["checkEnergy"]["bound"]),
            gram_delta=(max(r["checkGram"][1]["dRows"]) if "dRows" in r["checkGram"][1] else None,
                        mg["checkGram"]["delta"]),
            gram_beta=(max(r["checkGram"][1]["bRows"]) if "bRows" in r["checkGram"][1] else None,
                       mg["checkGram"]["beta"]),
            torsion_deltaT=(r["checkTorsion"][1].get("deltaT"), mg["checkTorsion"]["deltaT"]),
            torsion_normS=(r["checkTorsion"][1].get("b"), mg["checkTorsion"]["normS"]),
            ham=(r["checkHamBounds"][1].get("bounds"), mg["checkHamBounds"]["bounds"]))
        agree = {}
        for k, (a, b) in cmp.items():
            if k == "ham":
                hb = [b["DH"], b["X_H"], b["DX_H"], b["D2X_H"], b["D2H"]]
                agree[k] = a is not None and all(abs(float(x) - y) <= 1e-12 * max(1, abs(y)) for x, y in zip(a, hb))
            else:
                agree[k] = a is not None and abs(float(a) - b) <= 1e-12 * max(abs(b), 1e-300) + 1e-300
        rep[name]["toy_passes"] = ver["passes"]
        rep[name]["value_agreement"] = agree
        rep[name]["values"] = {k: (str(a)[:60], b) for k, (a, b) in cmp.items() if k != "ham"}
        print(name, "toy passes:", ver["passes"], "agree:", agree, flush=True)
        for P in (320, 448):
            B = A.FixedB(P)
            try:
                cf, _ = load(name, B, lambda x, B=B: B.ofRatDown(x))
                rf = run_sofx(cf)
                rep[name]["sofx_fixed%d" % P] = {k: v[0] for k, v in rf.items()}
                print(name, "sofx(Fixed %d):" % P, rep[name]["sofx_fixed%d" % P], flush=True)
            except Exception as ex:
                rep[name]["sofx_fixed%d" % P] = repr(ex)
                print(name, "Fixed", P, "exception", repr(ex))
    if outp:
        json.dump(rep, open(outp, "w"), indent=1, default=str)


if __name__ == "__main__":
    main()
