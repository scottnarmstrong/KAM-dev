#!/usr/bin/env python3
"""Exact rational mirror of the hybrid test (package SHARP2-C8D; format docs/campaign/design/hybrid/format.md).

Untrusted tooling.  Reads a `kam-hybrid` v1 file and evaluates, in Fractions with no float in any predicate, the checks
H0-H5 of format.md section 5 (the hypotheses of `iso_g1_hybrid_R`, blueprint bp:p2s2hc / bpI:p2s2hc):
  * every polynomial claim (d0, dinf, d0R, d1, d1t, d1R, d1tR) recomputed exactly from the emitted DK^ with the emitted
    weights (each weight w checked >= a rational upper bound of e^{2 pi r}; pi in [333/106, 355/113]);
  * the claims that need the composition (lE, dE0, dE0R, o0, o0R, o1, o1R, lH) are taken as given (kernel-only);
  * the transfer (frames, errors, torsion, bordered torsion), the consistency of `params1`, `witness1` and the outer
    displacement, and the restarted route-A' run `refinedCoreR` without its small-divisor certificates
    (hybrid_numq.py, validated against the kernel facts of the repository).
Margins reported (log10): the plain margin log10(e*/e) of the base run, the hybrid margin log10(e1*/e1) of the restarted
run (e* = X*_max gamma^4 delta0^(4 tau), X*_max the largest X* with okR), and the relative slack of every H0-H4 inequality.

Usage:  python3 -I scripts/apost_sharp/hybrid_mirror.py FILE.json [FILE.json ...]
"""
import json, math, os, sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import hybrid_numq as NQ   # noqa: E402

PI_LO, PI_HI = F(333, 106), F(355, 113)


# ============================================================================================ parsing
def q(s):
    return F(s)


def params_from(d):
    out = {k: q(v) for k, v in d.items() if k != "tau"}
    out["tau"] = int(d["tau"])
    return out


def box_from(d):
    return [(q(c), q(r)) for c, r in d]


def poly_from(d, S):
    """CertRealPoly -> (zero, [(key, re, im)]) with exact rationals."""
    return q(d["zero"]) / 2 ** S, [(tuple(k), F(int(c[0]), 2 ** S), F(int(c[1]), 2 ** S)) for k, c in d["half"]]


def emb_from(d, S):
    return dict(angleDeg=[int(x) for x in d["angleDeg"]], angle=[poly_from(p, S) for p in d["angle"]],
                actionDeg=[int(x) for x in d["actionDeg"]], action=[poly_from(p, S) for p in d["action"]])


def witR_from(d):
    core = d["base"]["core"]
    c = dict(Xs=q(core["Xs"]), kp=int(core["kp"]), th=q(core["th"]), c=[q(x) for x in core["c"]],
             cbar=[q(x) for x in core["cbar"]], ctail=q(core["ctail"]), sB=q(core["sB"]), sT=q(core["sT"]),
             sLt=q(core["sLt"]), sN=q(core["sN"]), sNt=q(core["sNt"]), t=q(core["t"]), J=int(core["J"]))
    return dict(base=dict(core=c, R={k: q(v) for k, v in d["base"]["R"].items()}, kappa=q(d["base"]["kappa"]),
                          sites=d["base"]["sites"]), bF=q(d["bF"]), bT=q(d["bT"]))


# ============================================================================================ exact norms
def exp_up(x, terms=30):
    """a rational upper bound of e^x for x >= 0: (e^{x/m})^m with x/m <= 1, each factor a Taylor sum with a geometric
    tail bound."""
    x = F(x)
    m = max(1, math.ceil(x))
    y = x / m
    s, t = F(0), F(1)
    for k in range(terms):
        s += t
        t = t * y / (k + 1)
    f = s + t / (1 - y / (terms + 1))
    f = F(math.ceil(f * 10 ** 20), 10 ** 20)                # round each factor up (keeps the numbers small)
    return f ** m


def weight_ok(W):
    """w >= e^{2 pi r}: compared with a rational upper bound of e^{2 pi_hi r}."""
    r, w = q(W["rho"]), q(W["w"])
    return r <= 0 or w >= exp_up(2 * PI_HI * r)


def pow2pi(d, up=True):
    """an upper bound of (2 pi)^d (d an integer)."""
    if d >= 0:
        return (2 * PI_HI) ** d
    return (2 * PI_LO) ** d


def comps(emb):
    return [(d, p) for d, p in zip(emb["angleDeg"], emb["angle"])] + \
        [(d, p) for d, p in zip(emb["actionDeg"], emb["action"])]


def mag(re, im):
    return abs(re) + abs(im)


def norm_poly(d, p, w):
    """sup-norm bound on T_r of (2 pi)^d P, P = zero + sum_half (c e_k + conj c e_-k): |zero| + 2 sum |c| w^{|k|_1}."""
    z, half = p
    return pow2pi(d) * (abs(z) + 2 * sum(mag(re, im) * w ** sum(abs(x) for x in k) for k, re, im in half))


def deriv_entry(d, p, l, w):
    """sup-norm bound of d/dtheta_l of (2 pi)^d P: (2 pi)^{d+1} 2 sum |k_l| |c| w^{|k|_1}."""
    _, half = p
    return pow2pi(d + 1) * 2 * sum(abs(k[l]) * mag(re, im) * w ** sum(abs(x) for x in k) for k, re, im in half)


def step_norms(emb, n, w):
    """(vector norm, row-sum norm of D, row-sum norm of D^T) of an embedding increment with weight w."""
    cs = comps(emb)
    v = max([norm_poly(d, p, w) for d, p in cs] + [F(0)])
    ent = [[deriv_entry(d, p, l, w) for l in range(n)] for d, p in cs]
    rows = max([sum(r) for r in ent] + [F(0)])
    cols = max([sum(ent[j][l] for j in range(len(ent))) for l in range(n)] + [F(0)])
    return v, rows, cols


# ============================================================================================ the transfer
def frames(ell, ellt, beta, d1, d1t):
    g = ellt * d1 + d1t * ell + d1t * d1
    if not beta * g < 1:
        return None
    b1 = beta / (1 - beta * g)
    db = beta ** 2 * g / (1 - beta * g)
    return dict(g=g, b1=b1, db=db, nD=b1 * d1 + ell * db, nDt=b1 * d1t + ellt * db)


def transfer(n, base_p, claim, cl, rho1, mu1, iso=True):
    """Definition bp:p2s2hc:data and format.md H0-H3: the transferred numbers (exact) and the slacks."""
    mu, rho, rhoinf = base_p["mu"], base_p["rho"], base_p["rhoInf"]
    ell, beta, m = base_p["sK"] - mu, base_p["sB"] - mu, base_p["sT"] - mu
    ellt, nu, nut, t = claim["bL"], claim["bN"], claim["bNt"], claim["bT"]
    M1, M2, Mh1, Mh2 = claim["dx"], claim["d2x"], claim["dh"], claim["d2h"]
    cTh, cDTh = 2 * M1, 2 * M2
    sl = {}
    sl["mu1>0"] = mu1 > 0
    sl["mu1<mu"] = mu1 < mu
    sl["d0<mu"] = cl["d0"] < mu
    sl["d0+mu1<=mu"] = cl["d0"] + mu1 <= mu
    sl["d1+mu1/2<=mu/2"] = cl["d1"] + mu1 / 2 <= mu / 2
    sl["rhoinf<rho1<=rho"] = rhoinf < rho1 <= rho
    fs = frames(ell, ellt, beta, cl["d1"], cl["d1t"])
    fr = frames(ell, ellt, beta, cl["d1R"], cl["d1tR"])
    sl["beta g<1"] = fs is not None
    sl["beta gR<1"] = fr is not None
    if fs is None or fr is None:
        return None, sl
    e1 = cl["lE"] + M2 / 2 * cl["d0"] ** 2
    if iso:
        e1 = max(e1, cl["lH"] + Mh2 / 2 * cl["d0R"] ** 2)
    dl1 = min(F(1), (rho1 - rhoinf) / 6)
    eps1 = n * e1 / dl1
    wB = lambda l_, lt_, e_: lt_ * (4 * n * M1) * l_ + e_ * (2 * n * l_ + lt_)

    def parts(f, d0, dE0, o0, o1):
        nu1, nut1 = nu + f["nD"], nut + f["nDt"]
        dab = f["nDt"] * cTh * nu1 + nut * cDTh * d0 * nu1 + nut * cTh * f["nD"]
        lam0 = nut * beta * dE0 + beta ** 3 * wB(ell, ellt, dE0) * o0
        lam1 = nut1 * f["b1"] * eps1 + f["b1"] ** 3 * wB(ell + cl["d1"], ellt + cl["d1t"], eps1) * o1
        return nu1, nut1, dab, lam0, lam1
    nu1, nut1, dab, lam0, lam1 = parts(fs, cl["d0"], cl["dE0"], cl["o0"], cl["o1"])
    t1 = min(t + dab + lam0, nut1 * cTh * nu1) + lam1
    _, _, dabR, lam0R, lam1R = parts(fr, cl["d0R"], cl["dE0R"], cl["o0R"], cl["o1R"])
    tA = dabR + lam0R + lam1R
    if iso:
        tA = max(tA + cl["dw"], n * (Mh1 * fr["nDt"] + Mh2 * cl["d0R"] * (nut + fr["nDt"])))
    sl["m tA<1"] = m * tA < 1
    if not m * tA < 1:
        return None, sl
    tr = dict(e1=e1, sK1=ell + cl["d1"] + mu1, sB1=fs["b1"] + mu1, sT1=m / (1 - m * tA) + mu1,
              bL1=ellt + cl["d1t"], bN1=nu1, bNt1=nut1, bT1=t1, tA=tA, dab=dab, lam0=lam0, lam1=lam1,
              nuRay1=base_p["nuRay"] - cl["dw"], delta0p=dl1, g=fs["g"], gR=fr["g"])
    return tr, sl


# ============================================================================================ the hybrid test
def check(data, log=print):
    S, n = int(data["scale_bits"]), int(data["n"])
    base, step, rst = data["base"], data["step"], data["restart"]
    bp, box = params_from(base["params"]), box_from(base["freqBox"])
    claim = {k: q(v) for k, v in base["claim"].items()}
    cl = {k: q(v) for k, v in step["claims"].items()}
    rho1, mu1, s1 = q(step["rho1"]), q(step["mu1"]), q(step["s1"])
    iso = bool(step.get("iso", True))
    res = dict(name=data["name"], ok=True, fails=[], slack={})

    def need(cond, what):
        if not cond:
            res["ok"] = False
            res["fails"].append(what)
    # polynomial claims, exactly
    W = step["weights"]
    for k, Wk in W.items():
        need(weight_ok(Wk), "weight %s" % k)
    dK = emb_from(step["dK"], S)
    w1, wi, wR = q(W["rho1"]["w"]), q(W["rhoinf"]["w"]), F(1)
    v1, D1, D1t = step_norms(dK, n, w1)
    vi, _, _ = step_norms(dK, n, wi)
    vR, DR, DRt = step_norms(dK, n, wR)
    exact = dict(d0=v1, d1=D1, d1t=D1t, dinf=vi, d0R=vR, d1R=DR, d1tR=DRt)
    for k, v in exact.items():
        need(cl[k] >= v, "claim %s = %s < exact %s" % (k, float(cl[k]), float(v)))
    res["exact_poly_claims"] = {k: float(v) for k, v in exact.items()}
    need(cl["dw"] >= abs(s1 - bp["s"]) * NQ.box_norm_up(box), "claim dw")
    # H0-H3
    tr, sl = transfer(n, bp, claim, cl, rho1, mu1, iso)
    for k, v in sl.items():
        need(v, "H0-H3 " + k)
    if tr is None:
        return res
    res["transferred"] = {k: float(v) for k, v in tr.items()}
    # H4
    p1 = params_from(rst["params1"])
    w1R = witR_from(rst["witness1"])
    R1 = w1R["base"]["R"]
    for k in ("tau", "rhoInf", "M", "gamma", "gbar", "sigma_omega", "E0"):
        need(p1[k] == bp[k], "params1.%s" % k)
    need(p1["rho"] == rho1, "params1.rho")
    need(p1["mu"] == mu1, "params1.mu")
    need(p1["sK"] == tr["sK1"], "params1.sK")
    need(p1["sB"] >= tr["sB1"], "params1.sB")
    need(p1["sT"] >= tr["sT1"], "params1.sT")
    need(p1["err"] >= tr["e1"], "params1.err")
    need(p1["nuRay"] <= tr["nuRay1"], "params1.nuRay")
    need(p1["s"] == s1, "params1.s")
    for k in ("dh", "dx", "d2x", "d2h"):
        need(R1[k] == claim[k], "R1.%s" % k)
    for k, tk in (("bL", "bL1"), ("bN", "bN1"), ("bNt", "bNt1"), ("bT", "bT1")):
        need(R1[k] >= tr[tk], "R1.%s" % k)
    need(bp["disp"] >= max(cl["dinf"], cl["dw"]) + p1["disp"], "outer disp")
    need(cl["dinf"] + p1["disp"] <= bp["mu"] / 2, "closeness budget")
    need(rst["sites"] != "reuse-base" or rho1 == bp["rho"], "sites reuse needs rho1 = rho")
    # H5
    ok5, parts = NQ.refined_core_r(n, p1, box, w1R, detail=True)
    need(ok5, "H5 refinedCoreR %s" % parts)
    res["H5"] = {k: bool(v) for k, v in parts.items()}
    # margins
    Xmax1, Q1 = NQ.max_xs(n, p1, box, w1R, lo=w1R["base"]["core"]["Xs"] / 4)
    e1s = Xmax1 * p1["gamma"] ** 4 * Q1.delta0 ** (4 * p1["tau"])
    res["e1"] = float(tr["e1"]); res["e1_star"] = float(e1s)
    res["hybrid_margin"] = math.log10(e1s / tr["e1"]) if e1s > 0 else float("-inf")
    rel = lambda a, b: float(1 - a / b) if b != 0 else float("inf")
    res["slack"] = {"d0+mu1<=mu": rel(cl["d0"] + mu1, bp["mu"]), "d1+mu1/2<=mu/2": rel(cl["d1"] + mu1 / 2, bp["mu"] / 2),
                    "beta g<1": float(1 - (bp["sB"] - bp["mu"]) * tr["g"]),
                    "m tA<1": float(1 - (bp["sT"] - bp["mu"]) * tr["tA"]),
                    "closeness": rel(cl["dinf"] + p1["disp"], bp["mu"] / 2),
                    "outer disp": rel(max(cl["dinf"], cl["dw"]) + p1["disp"], bp["disp"]),
                    "params1.err": float(p1["err"] / tr["e1"] - 1)}
    # the plain run of the base with the base witness (if given)
    if data.get("plain_witness"):
        wP = witR_from(data["plain_witness"])
        XmaxP, QP = NQ.max_xs(n, bp, box, wP, lo=wP["base"]["core"]["Xs"] / 4)
        eP = XmaxP * bp["gamma"] ** 4 * QP.delta0 ** (4 * bp["tau"])
        res["e_base"] = float(bp["err"]); res["e_star_plain"] = float(eP)
        res["plain_margin"] = math.log10(eP / bp["err"]) if eP > 0 else float("-inf")
    return res


def report(res, log=print):
    log("== %s: hybrid test %s" % (res["name"], "PASSES" if res["ok"] else "FAILS"))
    for f in res["fails"]:
        log("   fail: %s" % f)
    if "plain_margin" in res:
        log("   plain run:  e = %.4g, e* = %.4g, margin %+.3f"
            % (res["e_base"], res["e_star_plain"], res["plain_margin"]))
    if "hybrid_margin" in res:
        log("   restarted:  e1 = %.4g, e1* = %.4g, hybrid margin %+.3f"
            % (res["e1"], res["e1_star"], res["hybrid_margin"]))
    if res.get("slack"):
        log("   slacks: " + ", ".join("%s %.3g" % (k, v) for k, v in res["slack"].items()))
    if res.get("exact_poly_claims"):
        log("   exact polynomial claims: " + ", ".join("%s %.3g" % (k, v) for k, v in res["exact_poly_claims"].items()))


if __name__ == "__main__":
    for path in sys.argv[1:]:
        report(check(json.load(open(path))))
