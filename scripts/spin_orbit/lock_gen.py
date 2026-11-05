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
    rows = rep["checks"]["checkInvariance"]["info"].get("rows")
    en = rep["checks"]["checkEnergy"]["info"].get("value")
    err = G.up3(max(F(max(rows)), F(en)) * F(1001, 1000)) if rows and en is not None else F(1)
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
    # 6. threshold (kp = 4, the sizing decision), with the exact literals
    import lock_v2 as LV
    ti = rep["torsion"]
    sT = up(F(ti["b"]) / (1 - F(ti["deltaT"]))) + mu
    c.params["sT"] = sT
    p = LV.lock_package(rho, c.kappa, sK, sB, sT, Mv, mu=mu)
    rep["sizes"] = dict(sK=str(sK), sB=str(sB), sT=str(sT), M=str(Mv))
    for kp in (3, 4):
        th = LV.threshold(p, R, kp=kp)
        rep["threshold_kp%d" % kp] = th
        log("kp", kp, "log10 thr %.3f" % th["log10_thr"], th["binding"], "err", float(err))
    json.dump(rep, open(os.path.join(outdir, "size.json"), "w"), indent=1, default=str)
    return rep


def TA_balls(c):
    import toy_arith as TA
    return TA.slp_balls(c.n, c.jetOps_toy, c.weightH.w, c.centre, c.radius, c.expOrder)


if __name__ == "__main__":
    if sys.argv[1] == "size":
        size(F(sys.argv[2]), F(sys.argv[3]), sys.argv[4])


# ---------------------------------------------------------------------------------------------- full generation
FINAL = dict(rho=F(1, 100), mu=F(1, 1000), sK=F(371, 200), sB=F(1017, 200), sT=F(103, 50), M=F(93020),
             err=F(27, 25 * 10 ** 21), slackLo=F(1, 10 ** 5), slackHi=F(1, 10 ** 5))


def final_params(d):
    p = dict(d["params"])
    for k in ("rho", "mu", "sK", "sB", "sT", "M"):
        p[k] = str(FINAL[k])
    return p


def witness_v2(c):
    """X*, disp (never rounded down) and the refined witness at kp = 4 with the exact sites (lock_bites)."""
    import lock_v2 as LV
    import lock_bites as LB
    import v2_r2 as D
    import v2_q as V
    p = LV.lock_package(FINAL["rho"], c.kappa, FINAL["sK"], FINAL["sB"], FINAL["sT"], FINAL["M"], mu=FINAL["mu"])
    box = [tuple(x) for x in c.freqBox]
    err = FINAL["err"]
    R = {k: F(v) for k, v in c.claims.items()}
    st = LB.sites(p)
    d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    sc, g2 = p["gamma"] ** 4 * d0 ** 4, p["gamma"] ** 2 * p["rho"] ** 2
    Xs = V.up(float(2 * err / sc), 3)
    ok, why, w = D.okB_at("refined", p, box, LB.KP, F(1, 8), LB.J, Xs, R, st, detail=True)
    Q = V.refined_num(w, 2, p, box)
    C = V.disp_coefs(Q, 2, p, Xs, False)[0]
    disp = V.up(float(C * err / g2) * (1 + 1e-9), 3)
    while C * err > disp * g2:
        disp = V.up(float(disp) * 1.001, 3)
    fin = V.refinedCore(2, dict(p, err=err, disp=disp), box, dict(w), detail=True)
    return dict(Xs=Xs, disp=disp, okB=ok, why=why, refinedCore=fin, sites={"%s%d" % k: str(v) for k, v in st.items()},
                w={k: (str(v) if not isinstance(v, (list, dict)) else str(v)) for k, v in w.items()})


def full(outdir, books=None):
    """GENERATE (books None) or CHECK (books given) pass at the FINAL literals: every sub-check, the torsion witness,
    the graph SOS, the frame and Ham claims, the v2 witness."""
    os.makedirs(outdir, exist_ok=True)
    d = LS.load()
    d["params"] = final_params(d)
    sz = json.load(open(os.path.join(os.environ["SO_LOCK_SIZE"], "size.json")))
    eng = PK.PackedEngine({"cfgFull": F(1, 10 ** 24), "cfgLow": F(1, 10 ** 8)})
    cf, cl = G.make_cfgs(eng, books)
    c = LS.build(FINAL["err"], F(1), cf, cl, d=d)
    c.jetOps_toy = toy_ops(c.jetOps)
    B, rep = c.B, dict(mode="check" if books else "generate")
    # domain: rhoH from sizing; centres rounded to 1e-6, radii recomputed about them (+ mu)
    c.centre = [F(round(float(F(x)) * 10 ** 6), 10 ** 6) for x in sz["embedding"]["centre"]]
    c.radius = [F(10 ** 6)] * 2
    info = {}
    C.checkEmbedding(B, c, info)
    c.radius = [up(s, 4) + FINAL["mu"] for s, _ in info["action"]]
    set_weightH(c, F(sz["embedding"]["rhoH"]))
    rep["domain"] = dict(rhoH=str(c.weightH.rho), wH=str(c.weightH.w), centre=[str(x) for x in c.centre],
                         radius=[str(x) for x in c.radius])
    log("domain", rep["domain"])
    hv = VC.ham_values(c)
    c.claims = {k: up(hv[k]) for k in ("dh", "dx", "d2x", "d2h")}
    # v2 witness needs the frame claims: from the sizing pass (re-checked below by the verdict functions)
    for k in ("bL", "bN", "bNt", "bT"):
        c.claims[k] = F(sz["claims"][k])
    wv = witness_v2(c)
    c.params["disp"] = wv["disp"]
    rep["v2"] = {k: (str(v) if isinstance(v, F) else v) for k, v in wv.items()}
    log("v2 witness: Xs", wv["Xs"], "disp", float(wv["disp"]), "okB", wv["okB"], "refinedCore", wv["refinedCore"])
    # the seven sub-checks of `landedBase` (V2/Engine.lean); v1's checkSmallness is replaced by the engine test
    names = [n for n, _ in C.SUBCHECKS if n not in ("checkTorsion", "checkSmallness")]
    v = G.run_all(c, names, rep)
    db = c._gram
    T = C.torsionModels(B, 2, c.jet, c.emb, c.wit, c.gramInv, db, c.freqBox, c.params["s"], c.weight, c.cfgLow,
                        c.piEnc, c.DKc)
    if books is None:
        c.torsInv, _ = G.torsion_witness(B, c, T)
    else:
        c.torsInv = [[(int(a), int(b)) for a, b in r] for r in books["torsInv"]]
    v.update(G.run_all(c, ["checkTorsion"], rep))
    okH = VC.checkHamClaim(c, c.claims, hv)
    rows_f = VC.frame_rows(B, c)
    bOm = up(VC.freqNormUp(c.freqBox), 8)
    okF, parts = VC.checkFrameMajorants(B, c, dict(c.claims, bOm=bOm), rows_f)
    rep["hamClaim"], rep["frame"], rep["bOm"] = okH, parts, str(bOm)
    log("hamClaim", okH, "frameMajorants", okF, parts)
    # graph
    if books is None:
        gi = {}
        fm, fa = C.soGraphMonoModel(B, c), C.soGraphActionModel(B, c)
        mono0, mono, gM = G.graph_side(B, c, fm, None, "mono", gi)
        pLo0, pLo, gL = G.graph_side(B, c, fa, FINAL["slackLo"], "pLo", gi)
        nhi0, nhi, gH = G.graph_side(B, c, M.negM(B, fa), FINAL["slackHi"], "pHi", gi)
        c.graph = dict(mono=mono, mono0=mono0, sosMono=gM, pLo=pLo, pLo0=pLo0, sosLo=gL, pHi=-nhi, pHi0=-nhi0,
                       sosHi=gH)
        rep["graph_choice"] = G.summ(gi)
    else:
        c.graph = books["graph"]
    gi2 = {}
    vg = C.checkSoGraph(B, c, gi2)
    rep["checkSoGraph"] = dict(ok=vg, info=G.summ(gi2))
    band = (c.graph["pLo"] - c.params["disp"], c.graph["pHi"] + c.params["disp"])
    rep["band"] = [str(x) for x in band]
    bandOk = band[0] >= BAND[0] and band[1] <= BAND[1]
    log("checkSoGraph", vg, "band", [float(x) for x in band], "inside", [float(x) for x in BAND], bandOk)
    rep["passes"] = all(v.values()) and vg and okH and okF and wv["refinedCore"][0] if isinstance(
        wv["refinedCore"], (list, tuple)) else all(v.values()) and vg and okH and okF
    rep["bandOk"] = bandOk
    rep["verdicts"] = v
    if books is None:
        out = {"cfgFull": G.books_of(cf), "cfgLow": G.books_of(cl)}
        import pickle
        pickle.dump(dict(books=out, torsInv=c.torsInv, graph=c.graph, claims=c.claims, domain=rep["domain"],
                         v2=wv, bOm=bOm), open(os.path.join(outdir, "gen.pkl"), "wb"))
    json.dump(rep, open(os.path.join(outdir, "%s.json" % rep["mode"]), "w"), indent=1, default=str)
    log("PASSES" if rep["passes"] and bandOk else "FAILS", rep["mode"])
    return c, rep


if __name__ == "__main__" and sys.argv[1] == "generate":
    full(sys.argv[2])



# ---------------------------------------------------------------------------------------------- graph SOS (lock)
# the barrier window of AssemblyN65 (lockLiteralCheck passes at lo = 13155/1000000, fails at 0.01315)
BAND = (F(13155, 1000000), F(163, 10000))
SOS = dict(K0=112, K1=8, slackLo=F(7, 10 ** 5), slackHi=F(3, 10 ** 5), bits=64, tol=1e-15, grid=(2048, 512))


def lock_sos(B, f, slack, rho):
    """sofx_gen.sos_witness with a WEIGHTED truncation (|c| w^{|k|_1} >= tol: the residual is measured in the
    weighted norm), 64-bit coefficients, a 2048 x 512 grid and a k-heavy degree box (the l-degree does not matter
    for the lock's action, the k-degree does: lock_gen sizing notes, 2026-10-31)."""
    import math
    import numpy as np
    vals = G.grid_values(B, f, *SOS["grid"])
    hm = float(vals.min())
    c0 = hm - float(slack)
    s = np.sqrt(np.maximum(vals - c0, 0.0))
    S = np.fft.fft2(s) / s.size
    N0, N1 = S.shape
    g, sc = [], 2 ** SOS["bits"]
    for k0 in range(-SOS["K0"], SOS["K0"] + 1):
        for k1 in range(-SOS["K1"], SOS["K1"] + 1):
            z = S[k0 % N0, k1 % N1]
            if abs(z) * math.exp(2 * math.pi * rho * (abs(k0) + abs(k1))) < SOS["tol"]:
                continue
            re, im = round(z.real * sc), round(z.imag * sc)
            if re or im:
                g.append(((k0, k1), (B.ofRatDown(F(re, sc)), B.ofRatDown(F(im, sc)))))
    g.sort()
    return g, F(round(c0 * 10 ** 9), 10 ** 9), hm


def regraph(gdir):
    """recompute the graph data with lock_sos (per-side slacks) and store it in GENDIR/gen.pkl."""
    import pickle
    d = LS.load()
    d["params"] = final_params(d)
    eng = PK.PackedEngine({"cfgFull": F(1, 10 ** 24), "cfgLow": F(1, 10 ** 8)})
    cf, cl = G.make_cfgs(eng)
    c = LS.build(FINAL["err"], F(1), cf, cl, d=d, gramInv=[[[], []], [[], []]])
    B, rho = c.B, float(c.weight.rho)
    G.sos_witness = lambda B_, f, slack, **k: lock_sos(B_, f, slack, rho)
    gi = {}
    fm, fa = C.soGraphMonoModel(B, c), C.soGraphActionModel(B, c)
    mono0, mono, gM = G.graph_side(B, c, fm, None, "mono", gi)
    pLo0, pLo, gL = G.graph_side(B, c, fa, SOS["slackLo"], "pLo", gi)
    nhi0, nhi, gH = G.graph_side(B, c, M.negM(B, fa), SOS["slackHi"], "pHi", gi)
    graph = dict(mono=mono, mono0=mono0, sosMono=gM, pLo=pLo, pLo0=pLo0, sosLo=gL, pHi=-nhi, pHi0=-nhi0, sosHi=gH)
    log("regraph", G.summ(gi))
    p = os.path.join(gdir, "gen.pkl")
    st = pickle.load(open(p, "rb"))
    st["graph"], st["graph_choice"] = graph, G.summ(gi)
    pickle.dump(st, open(p + ".tmp", "wb"))
    os.replace(p + ".tmp", p)
    log("band", float(pLo), float(-nhi))


if __name__ == "__main__" and sys.argv[1] == "regraph":
    regraph(sys.argv[2])


# (after BAND and the graph helpers, which `full` reads)
if __name__ == "__main__" and sys.argv[1] == "check":
    import pickle
    g = pickle.load(open(os.path.join(sys.argv[2], "gen.pkl"), "rb"))
    full(sys.argv[3], dict(g["books"], torsInv=g["torsInv"], graph=g["graph"]))
