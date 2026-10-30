#!/usr/bin/env python3
"""LOCK-DATA: exact sizing and checking of the N = 65 lock certificate in the sofx mirror (untrusted tooling; the
kernel decides).  Every size comes from an EXACT mirror of a landed check (sofx_check sub-checks, toy_arith's
Slp.balls with the sqrt arm, sodata3_v2checks' checkFrameMajorants / hamClaimOk), never from grid suprema.

    python3 lock_gen.py size RHO MU OUTDIR      # GENERATE pass: exact values of every check, the derived literals
    python3 lock_gen.py check OUTDIR            # CHECK pass from scratch with the emitted books and literals

Size pass, in order (each step's literal is the exact value rounded UP, plus mu where the check subtracts mu):
  1. checkEmbedding at provisional sizes: the DK row sums (sK), the angle Im bound (rhoH = rho + mu + iota),
     the action deviations (radius_i = dev_i + mu);
  2. the disc pass (Slp.balls) on that domain: hamBoundsOk's M and hamClaimOk's four sums;
  3. checkInvariance / checkEnergy: err (exact maximum, times 1.001, 3 digits up);
  4. checkGram: (d, b), sB = b / (1 - d) + mu; torsion models, torsInv (sofx_gen.torsion_witness), sT;
  5. frame rows: checkFrameMajorants' exact row maxima;
then the refined threshold (lock_v2.threshold) with these literals.
"""
import json
import math
import os
import sys
import time
from fractions import Fraction as F

sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sofx_model as M           # noqa: E402
import sofx_check as C           # noqa: E402
import sofx_gen as G             # noqa: E402
import sofx_packed as PK         # noqa: E402
import sodata3_v2checks as VC    # noqa: E402
import sodata3_witness as SW     # noqa: E402
import lock_sofx as LS           # noqa: E402

BIG = F(10 ** 6)


def log(*a):
    print("[%s]" % time.strftime("%H:%M:%S"), *a, flush=True)


def toy_ops(prog):
    tag = dict(add="+", mul="*", exp="E", inv="I", sqrt="S")
    out = []
    for op in prog:
        t = op[0]
        if t == "const":
            out.append(("C", F(op[1]), F(op[2]), int(op[3])))
        elif t == "action":
            out.append(("A", op[1]))
        elif t == "char":
            out.append(("X", tuple(op[1])))
        elif t in ("add", "mul"):
            out.append((tag[t], op[1], op[2]))
        else:
            out.append((tag[t], op[1]))
    return out


def up(x, sig=4):
    return SW.up_sig(F(x), sig)


def set_weightH(c, rhoH):
    import sofx_lunar as SL
    c.weightH = M.Weight(rhoH, SL.weight_for(rhoH, c.expHalvings, c.expOrder))


def size(rho, mu, outdir):
    os.makedirs(outdir, exist_ok=True)
    d = LS.load()
    d["params"] = dict(d["params"], rho=str(rho), mu=str(mu), sK=str(BIG), sB=str(BIG), sT=str(BIG), M=str(BIG))
    eng = PK.PackedEngine({"cfgFull": F(1, 10 ** 24), "cfgLow": F(1, 10 ** 8)})
    cf, cl = G.make_cfgs(eng)
    c = LS.build(F(1), F(1), cf, cl, d=d)
    c.jetOps_toy = toy_ops(c.jetOps)
    B, rep = c.B, dict(rho=str(rho), mu=str(mu))
    log("built; gramInv terms", [[len(x) for x in r] for r in c.gramInv])
    # 1. embedding
    info = {}
    C.checkEmbedding(B, c, info)
    iota = max(min(a, b) for a, b in info["iota"])
    sK = up(max(info["dkRows"])) + mu
    rhoH = up(rho + mu + iota, 5)
    radius = [up(s, 4) + mu for s, _ in info["action"]]
    centre = [F(int(x["zero"]), 2 ** c.prec).limit_denominator(10 ** 7) for x in d["emb"]["action"]]
    # the action check is centred at `centre`: recompute the deviation about the rounded centre
    c.centre, c.radius = centre, [BIG] * 2
    info2 = {}
    C.checkEmbedding(B, c, info2)
    radius = [up(s, 4) + mu for s, _ in info2["action"]]
    c.radius = radius
    set_weightH(c, rhoH)
    c.params["sK"] = sK
    rep["embedding"] = dict(dkRows=[str(x) for x in info["dkRows"]], iota=[[str(a), str(b)] for a, b in info["iota"]],
                            action=[str(s) for s, _ in info2["action"]], sK=str(sK), rhoH=str(rhoH),
                            centre=[str(x) for x in centre], radius=[str(x) for x in radius])
    log("embedding", json.dumps(rep["embedding"])[:600])
    # 2. disc pass
    t = time.time()
    hv = VC.ham_values(c)
    if hv is None:
        rep["balls"] = "FAIL"
        log("disc pass fails on the domain")
        json.dump(rep, open(os.path.join(outdir, "size.json"), "w"), indent=1, default=str)
        return rep
    hb = {}
    C.hamBoundsOk(2 * c.n, c.jet, TA_balls(c), BIG, hb)
    Mv = up(max(hb["bounds"]))
    c.params["M"] = Mv
    R = {k: up(hv[k]) for k in ("dh", "dx", "d2x", "d2h")}
    rep["ham"] = dict(values={k: str(v) for k, v in hv.items()}, bounds=[str(x) for x in hb["bounds"]], M=str(Mv),
                      seconds=round(time.time() - t))
    log("ham", {k: float(v) for k, v in hv.items()}, "M", float(Mv))
    # 3. invariance / energy
    v = G.run_all(c, ["checkInvariance", "checkEnergy"], rep)
    rows = rep["checks"]["checkInvariance"]["info"]["rows"]
    en = rep["checks"]["checkEnergy"]["info"]["value"]
    err = G.up3(max(F(max(rows)), F(en)) * F(1001, 1000))
    c.params["err"] = err
    rep["err"] = str(err)
    log("err", float(err))
    # 4. gram, torsion
    G.run_all(c, ["checkGram"], rep)
    gi = rep["checks"]["checkGram"]["info"]
    db = c._gram
    dd, bb = B.val(db[0]), B.val(db[1])
    sB = up(bb / (1 - dd)) + mu
    c.params["sB"] = sB
    T = C.torsionModels(B, 2, c.jet, c.emb, c.wit, c.gramInv, db, c.freqBox, c.params["s"], c.weight, c.cfgLow,
                        c.piEnc, c.DKc)
    S, Cm = G.torsion_witness(B, c, T)
    c.torsInv = S
    tinfo = {}
    C.torsionAvgCheck(B, 2, T, S, BIG, tinfo)
    rep["torsion"] = G.summ(tinfo)
    log("gram d %.3g b %.4g sB %s; torsion %s" % (float(dd), float(bb), sB, json.dumps(G.summ(tinfo))[:400]))
    # 5. frames
    rows_f = VC.frame_rows(B, c)
    fv = VC.frame_values(B, c, rows_f)
    R.update(bL=up(max(fv["L"])), bN=up(max(fv["N"])), bNt=up(max(fv["Nt"])), bT=up(max(fv["T"])))
    rep["frame"] = {k: [str(x) for x in vv] for k, vv in fv.items()}
    rep["claims"] = {k: str(x) for k, x in R.items()}
    log("claims", {k: float(x) for k, x in R.items()})
    rep["books"] = {"cfgFull": len(G.books_of(cf)), "cfgLow": len(G.books_of(cl))}
    json.dump(rep, open(os.path.join(outdir, "size.json"), "w"), indent=1, default=str)
    return rep


def TA_balls(c):
    import toy_arith as TA
    return TA.slp_balls(c.n, c.jetOps_toy, c.weightH.w, c.centre, c.radius, c.expOrder)


if __name__ == "__main__":
    if sys.argv[1] == "size":
        size(F(sys.argv[2]), F(sys.argv[3]), sys.argv[4])
