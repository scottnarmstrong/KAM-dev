#!/usr/bin/env python3
"""SO-DATA-1: generate the complete lunar certificate data of one torus and verify it with the sofx mirror of the
landed checker (untrusted tooling).

    python3 sofx_gen.py lower|upper OUTDIR

GENERATE pass (books empty: every genuine product's advice is built from the exact product, then checked by the
landed route), the choices err / disp / S / graph data, then a CHECK pass from scratch with the emitted books
(a missing key gets Lean's fallback and is reported).  Writes OUTDIR/<which>_cert.json (data), OUTDIR/<which>_
advice.json (books), OUTDIR/<which>_report.json (margins, sizes, product table, key coverage).
"""
import json
import math
import os
import sys
sys.set_int_max_str_digits(0)
import time
import hashlib
from fractions import Fraction as F

import numpy as np

import sofx_arith as A
import sofx_model as M
import sofx_check as C
import sofx_lunar as L
import sofx_packed as PK
import toy_constants as TC

CUT_FULL = 100000
CUT_LOW = 30
TAYLOR, HALV = 30, 12
BUDGET = {"cfgFull": F(1, 10 ** 80), "cfgLow": F(1, 10 ** 8)}
SOS_BITS = 40


def log(*a):
    print("[%s]" % time.strftime("%H:%M:%S"), *a, flush=True)


def fl(x):
    return float(x)


def up3(x):
    """a 3-significant-digit rational >= x > 0."""
    x = F(x)
    e = math.floor(math.log10(float(x))) - 2
    D = F(10) ** e
    m = math.ceil(x / D)
    return m * D


def make_cfgs(engine, books=None):
    bf = None if books is None else books["cfgFull"]
    bl = None if books is None else books["cfgLow"]
    return (M.Cfg("cfgFull", CUT_FULL, TAYLOR, HALV, bf, engine), M.Cfg("cfgLow", CUT_LOW, TAYLOR, HALV, bl, engine))


# ---------------------------------------------------------------------------------------------- torsion witness
def torsion_witness(B, c, T):
    k = 3
    Cm = np.zeros((k, k), dtype=np.complex128)
    for l in range(k):
        for j in range(k):
            z = C.zeroModeBall(B, 2, C.entry(T, l, j, B))[0]
            Cm[l, j] = complex(fl(B.val(z[0])), fl(B.val(z[1])))
    S = np.linalg.inv(Cm)
    sc = 2 ** SOS_BITS
    rows = []
    for i in range(k):
        r = []
        for j in range(k):
            re = F(round(S[i, j].real * sc), sc)
            im = F(round(S[i, j].imag * sc), sc)
            r.append((B.ofRatDown(re), B.ofRatDown(im)))
        rows.append(r)
    return rows, Cm


# ---------------------------------------------------------------------------------------------- SOS witnesses
def grid_values(B, f, N0=1024, N1=256):
    """Re f on the real torus grid (float), f a degree-0 model with 2-d keys."""
    G = np.zeros((N0, N1), dtype=np.complex128)
    for (k0, k1), (re, im) in f.poly:
        G[k0 % N0, k1 % N1] += complex(fl(B.val(re)), fl(B.val(im)))
    return np.real(np.fft.ifft2(G) * (N0 * N1))


def sos_witness(B, f, slack, K0=24, K1=6, tol=1e-9):
    vals = grid_values(B, f)
    hm = float(vals.min())
    c0 = hm - slack
    s = np.sqrt(np.maximum(vals - c0, 0.0))
    S = np.fft.fft2(s) / s.size
    N0, N1 = S.shape
    g = []
    sc = 2 ** SOS_BITS
    for k0 in range(-K0, K0 + 1):
        for k1 in range(-K1, K1 + 1):
            z = S[k0 % N0, k1 % N1]
            if abs(z) < tol:
                continue
            re, im = round(z.real * sc), round(z.imag * sc)
            if re == 0 and im == 0:
                continue
            g.append(((k0, k1), (B.ofRatDown(F(re, sc)), B.ofRatDown(F(im, sc)))))
    g.sort()
    m0 = F(round(c0 * 10 ** 9), 10 ** 9)
    return g, m0, hm


def graph_side(B, c, f, slack, tag, info):
    """(m0, m, g) with checkRealLowerBound passing: Re f >= m on the real torus."""
    g, m0, hm = sos_witness(B, f, slack) if slack is not None else ([], None, None)
    if slack is None:
        vals = grid_values(B, f)
        m0 = F(round(float(np.mean(vals)) * 10 ** 9), 10 ** 9)
    i = {}
    C.checkRealLowerBound(B, c.weight, c.cfgLow, f, m0, m0, g, i, "x")
    sup = i["x"]["sup"]
    m = m0 - sup / 2
    m = F(math.floor(m * 10 ** 7), 10 ** 7) - F(1, 10 ** 7)
    info[tag] = dict(gridmin=hm, m0=fl(m0), m=fl(m), resid_half=fl(sup / 2), g_terms=len(g))
    return m0, m, g


# ---------------------------------------------------------------------------------------------- main
def run_all(c, names, rep):
    B = c.B
    verdicts = {}
    for name, f in C.SUBCHECKS:
        if name not in names:
            continue
        t = time.time()
        info = {}
        ok = f(B, c, info)
        verdicts[name] = ok
        rep.setdefault("checks", {})[name] = dict(ok=ok, seconds=round(time.time() - t, 1),
                                                  info=summ(info))
        log(name, ok, "%.0fs" % (time.time() - t), json.dumps(summ(info), default=str)[:400])
    return verdicts


def summ(info):
    out = {}
    for k, v in info.items():
        if k in ("G", "compose"):
            continue
        if isinstance(v, F):
            out[k] = fl(v)
        elif isinstance(v, (list, tuple)):
            out[k] = [summ({"x": x})["x"] if not isinstance(x, (int, float, str, bool, type(None))) else x
                      for x in v]
        elif isinstance(v, dict):
            out[k] = summ(v)
        else:
            out[k] = v
    return out


def books_of(cfg):
    seen, out = set(), []
    for k, adv in cfg.generated:
        if k not in seen:
            seen.add(k)
            out.append((k, adv))
    return out


def main(which, outdir):
    os.makedirs(outdir, exist_ok=True)
    rep = dict(which=which, budgets={k: str(v) for k, v in BUDGET.items()}, cutoffs=[CUT_FULL, CUT_LOW])
    eng = PK.PackedEngine({"cfgFull": BUDGET["cfgFull"], "cfgLow": BUDGET["cfgLow"]})
    cf, cl = make_cfgs(eng)
    err0 = F(1)
    t0 = time.time()
    c = L.build(which, err0, F(1), cf, cl, HALV, TAYLOR)
    B = c.B
    log("built", which)
    # ---- GENERATE: invariance and energy fix err
    v = run_all(c, ["checkInvariance", "checkEnergy"], rep)
    rows = rep["checks"]["checkInvariance"]["info"]["rows"]
    en = rep["checks"]["checkEnergy"]["info"]["value"]
    inv_exact = max(F(x) for x in rows)
    err = up3(max(F(max(rows)), F(en)) * F(1001, 1000))
    p = c.params
    c2 = TC.isoC2Q(2, p["tau"], p["rho"], p["rhoInf"], p["M"], p["sK"], p["sB"], p["sT"])
    disp = up3(c2 * err / (p["gamma"] ** 2 * p["rho"] ** 2))
    c.params = L.lunarR1(err, disp)
    rep["err"], rep["disp"] = str(err), str(disp)
    log("err", fl(err), "disp", fl(disp))
    # ---- Gram, torsion (S from the centres)
    run_all(c, ["checkGram"], rep)
    db = c._gram
    T = C.torsionModels(B, 2, c.jet, c.emb, c.wit, c.gramInv, db, c.freqBox, c.params["s"], c.weight, c.cfgLow,
                        c.piEnc, c.DKc)
    S, Cm = torsion_witness(B, c, T)
    c.torsInv = S
    rep["torsion_centre"] = [[str(x) for x in r] for r in Cm]
    # ---- graph
    gi = {}
    fm = C.soGraphMonoModel(B, c)
    fa = C.soGraphActionModel(B, c)
    mono0, mono, gM = graph_side(B, c, fm, None, "mono", gi)
    pLo0, pLo, gL = graph_side(B, c, fa, F(3, 10000), "pLo", gi)
    nhi0, nhi, gH = graph_side(B, c, M.negM(B, fa), F(3, 10000), "pHi", gi)
    c.graph = dict(mono=mono, mono0=mono0, sosMono=gM, pLo=pLo, pLo0=pLo0, sosLo=gL, pHi=-nhi, pHi0=-nhi0, sosHi=gH)
    rep["graph_choice"] = gi
    log("graph", json.dumps(gi))
    rep["generate_seconds"] = round(time.time() - t0)
    gen_books = {"cfgFull": books_of(cf), "cfgLow": books_of(cl)}
    # ---- CHECK pass from scratch with exactly the emitted books
    eng2 = PK.PackedEngine({"cfgFull": BUDGET["cfgFull"], "cfgLow": BUDGET["cfgLow"]})
    cf2, cl2 = make_cfgs(eng2, gen_books)
    c2c = L.build(which, err, disp, cf2, cl2, HALV, TAYLOR)
    c2c.torsInv, c2c.graph = S, c.graph
    t1 = time.time()
    chk = {}
    v = run_all(c2c, [n for n, _ in C.SUBCHECKS], chk)
    gi2 = {}
    vg = C.checkSoGraph(B, c2c, gi2)
    chk["checkSoGraph"] = dict(ok=vg, info=summ(gi2))
    log("checkSoGraph", vg, json.dumps(summ(gi2), default=str))
    rep["check"] = chk["checks"]
    rep["check"]["checkSoGraph"] = chk["checkSoGraph"]
    rep["check_seconds"] = round(time.time() - t1)
    rep["passes"] = all(v.values()) and vg
    # ---- key coverage
    cov = {}
    for nm, cfg in (("cfgFull", cf2), ("cfgLow", cl2)):
        emitted = [k for k, _ in gen_books[nm]]
        looked = []
        for k in cfg.lookups:
            if k not in looked:
                looked.append(k)
        cov[nm] = dict(emitted=len(emitted), looked_up=len(looked), equal=sorted(emitted) == sorted(looked),
                       misses=[list(x) if isinstance(x, tuple) else x for x in cfg.misses][:10])
    rep["key_coverage"] = cov
    # ---- product table (sizes SO-DATA-2 feeds to the kernel)
    prods = []
    for fk, infos in eng.stats:
        for part, inf in zip(("rr", "ii", "ri", "ir"), infos):
            if not inf.get("zero"):
                prods.append(dict(key=list(fk), part=part, **inf))
    rep["products"] = prods
    with open(os.path.join(outdir, "%s_report.json" % which), "w") as fh:
        json.dump(rep, fh, indent=1, default=str, sort_keys=True)
    save_data(os.path.join(outdir, "%s_cert.json" % which), os.path.join(outdir, "%s_advice.json" % which),
              c2c, gen_books, rep)
    log("PASSES" if rep["passes"] else "FAILS", which)
    return c2c, gen_books, rep


def pj(B, P):
    return [[list(k), [str(z[0]), str(z[1])]] for k, z in P]


def adv_json(adv):
    if adv[0] == "direct":
        return ["direct"]
    _, P, *parts = adv
    out = ["packed", P]
    for a in parts:
        out.append(dict(la=a.la.json(), lb=a.lb.json(), target=a.target.json(), scale=a.scale, outLog=a.outLog,
                        rounded=[rle(r) for r in a.rounded]))
    return out


def rle(win):
    out, z = [], 0
    for x in win:
        if x == 0:
            z += 1
        else:
            if z:
                out += [0, z]
                z = 0
            out.append(x)
    if z:
        out += [0, z]
    return out


def save_data(cpath, apath, c, books, rep):
    B = c.B
    e = c.emb
    rp = lambda R: dict(zero=str(R.zero), half=pj(B, R.half))
    d = dict(precision=L.PREC, mantissas="integers m denoting m / 2^320 (CertFixed 320)",
             params={k: str(v) for k, v in c.params.items()},
             ham="soRotHamExprScaled lunarR1TimeScale", weightH=[str(c.weightH.rho), str(c.weightH.w)],
             centre=[str(x) for x in c.centre], radius=[str(x) for x in c.radius],
             freqBox=[[str(a), str(b)] for a, b in c.freqBox],
             emb=dict(angleDeg=e.angleDeg, angle=[rp(R) for R in e.angle], actionDeg=e.actionDeg,
                      action=[rp(R) for R in e.action]),
             weight=[str(c.weight.rho), str(c.weight.w)],
             wit=dict(expWit=[], invWit=[], charWit=[[list(k), dict(poly=pj(B, E[0]), pinHalvings=E[1],
                                                                     pinOrder=E[2])] for k, E in c.wit.charWit]),
             gramInv=[[pj(B, P) for P in r] for r in c.gramInv],
             torsInv=[[[str(z[0]), str(z[1])] for z in r] for r in c.torsInv],
             cfgFull=dict(cutoff=CUT_FULL, taylorN=TAYLOR, halvings=HALV),
             cfgLow=dict(cutoff=CUT_LOW, taylorN=TAYLOR, halvings=HALV),
             piEnc=dict(centre=str(c.piEnc.centre), rad=str(c.piEnc.rad), machinK=c.piEnc.machinK,
                        machinJ=c.piEnc.machinJ),
             expHalvings=c.expHalvings, expOrder=c.expOrder,
             graph={k: (str(v) if isinstance(v, F) else pj(B, v)) for k, v in c.graph.items()})
    with open(cpath, "w") as fh:
        json.dump(d, fh, sort_keys=True, separators=(",", ":"))
    a = {nm: [[list(k), adv_json(adv)] for k, adv in bk] for nm, bk in books.items()}
    with open(apath, "w") as fh:
        json.dump(a, fh, sort_keys=True, separators=(",", ":"))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
