#!/usr/bin/env python3
"""Exact rational mirror of the Lean hybrid checker `checkHybrid` (KAM/CertificateSharp/Hybrid; package SHARP2-C8DFIX;
format docs/campaign/design/hybrid/format.md v2).

Untrusted tooling.  The Lean definitions are transcribed one for one in the rational backend `instCertArithRat` (every
rounding error is 0; `ofRatUp`, `ofRatDown` are the identity), with Lean's totalized division (x / 0 = 0):

  checkHybrid c w = transferOk n c.params c.freqBox w                       RestartQ.lean: the 35 conjuncts, ported
                  && hybStepOk c w.step w.p1.rho w.p1.rhoInf (w.rhoT n box)  Claims.lean
                  && refinedCoreR n w.p1 c.freqBox w.w1                      RouteARefinedRef.lean

  hybStepOk = hybWeightsOk   ported: checkWeight (ratExpUp (2 piUpQ rho) expHalvings expOrder <= w, 0 < rho) and the
                             strip inequalities
            && hybPolyOk     ported: stepSupOk, stepRealOk, dstepOk (realCompModel, ofDeriv, toDeg with twoPiZpowHi/Lo
                             of the certificate's Machin parameters, degFactorUp, sumsOk)
            && hybOmegaOk    KERNEL-ONLY (products of the base embedding's models)
            && hybCauchyOk   ported
            && hybCompOk     KERNEL-ONLY (compositions of the base Hamiltonian: lE and lH)
            && the d_omega check, ported.
  refinedCoreR: Xs > 0, wfOk, okR, budgetOk, finalOkA (hybrid_numq.py) and the classical tail (classicalOk) ported;
            sitesOk: for "reuse-base" sites the restarted run's sitesOk equals the base run's when n, tau, kp, rho,
            rhoInf, c, cbar, J, kappa, gamma and the box agree (checked exactly here), and the base run's sites are
            certified in Lean (T2: Hybrid/Tests/T2.lean; R1: r1R_sites in kernel-tests); otherwise KERNEL-ONLY.
The routeHybrid engine also runs the landed base checks, checkHamClaim and checkFrameMajorants of the base claim: the
base certificate's own checks, not mirrored.

Margins (log10): the plain margin log10(e*/e) of the base run and the hybrid margin log10(e1*/e1) of the restarted run,
e* = X*_max gamma^4 delta0^(4 tau), X*_max the largest X* with okR.

Usage:  python3 -I scripts/apost_sharp/hybrid_mirror.py [--settings s,N,k,j] FILE.json [FILE.json ...]
"""
import json, math, os, sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import hybrid_numq as NQ   # noqa: E402

sys.set_int_max_str_digits(0)

# ============================================================================================ Lean's rational helpers
def qdiv(a, b):
    """`a / b` in Lean's `ℚ` (x / 0 = 0)."""
    return F(0) if b == 0 else F(a) / F(b)


def qinv(a):
    return F(0) if a == 0 else 1 / F(a)


def nat_ceil(q):
    """`⌈q⌉₊`."""
    return max(0, math.ceil(F(q)))


# ============================================================================================ π (PiHigh.lean, Ops.lean)
PI_LO_Q = F(3141592, 10 ** 6)        # piLoQ
PI_UP_Q = F(3141593, 10 ** 6)        # piUpQ


def atanS(x, m):
    return sum((F(-1) ** i) * (F(x) ** (2 * i + 1) / (2 * i + 1)) for i in range(m))


def pi_low_rat(k, j):
    return 16 * atanS(F(1, 5), 2 * k) - 4 * atanS(F(1, 239), 2 * j + 1)


def pi_up_rat(k, j):
    return 16 * atanS(F(1, 5), 2 * k + 1) - 4 * atanS(F(1, 239), 2 * j)


def pi_low_pos(k, j):
    return max(pi_low_rat(k, j), PI_LO_Q)


def pi_up_min(k, j):
    return min(pi_up_rat(k, j), PI_UP_Q)


def two_pi_zpow_lo(k, j, e):
    return (2 * pi_low_pos(k, j)) ** e if e >= 0 else qinv((2 * pi_up_min(k, j)) ** (-e))


def two_pi_zpow_hi(k, j, e):
    return (2 * pi_up_min(k, j)) ** e if e >= 0 else qinv((2 * pi_low_pos(k, j)) ** (-e))


def deg_factor_up(d):
    """`degFactorUp d` (Model/Basic.lean)."""
    return (2 * PI_UP_Q) ** d if d >= 0 else F(1) / (2 * PI_LO_Q) ** (-d)


# ============================================================================================ ratExpUp, checkWeight
def rat_exp_up(q, s, N):
    """`ratExpUp q s N` (Arith/Transcendental.lean) as a reduced (numerator, denominator) pair: the Taylor sum is reduced
    once; its 2^s-th power is then reduced automatically, so no gcd of the large powers is taken."""
    q = F(q)
    x = q / 2 ** s
    if x <= 1 and N > 0:
        t = sum(x ** m / math.factorial(m) for m in range(N)) + x ** N * (F(N + 1) / (math.factorial(N) * N))
        a, b = t.numerator, t.denominator
        for _ in range(s):
            a, b = a * a, b * b
        return a, b
    return 3 ** nat_ceil(q), 1


def rat_exp_up_le(q, s, N, w):
    """`ratExpUp q s N ≤ w` by cross-multiplication (w rational)."""
    a, b = rat_exp_up(q, s, N)
    w = F(w)
    return a * w.denominator <= w.numerator * b


def check_weight(W, s, N):
    """`checkWeight W s N`."""
    return W[0] > 0 and rat_exp_up_le(2 * PI_UP_Q * W[0], s, N, W[1])


REAL_WEIGHT = (F(0), F(1))           # realWeight


# ============================================================================================ models (ℚ backend)
# a polynomial is a list of terms (key tuple, re, im); a model is (deg, terms, rad)
def key_deg(k):
    return sum(abs(x) for x in k)


def sorted_terms(n, P):
    """`CertRealPoly.toSortedPoly n`: the conjugates at -k (reversed), the constant at the zero key, the half terms."""
    zero, half = P
    return ([(tuple(-x for x in k), re, -im) for k, re, im in reversed(half)] +
            [(tuple([0] * n), zero, F(0))] + list(half))


def weighted_norm_up(W, terms):
    """`CertPoly.weightedNormUp` = `CertPoly.supNormUp`: Σ (|re| + |im|) w^{|k|₁}."""
    return sum(((abs(re) + abs(im)) * W[1] ** key_deg(k) for k, re, im in terms), F(0))


def sup_bound(W, m):
    """`CertModel.supBound W m`."""
    d, terms, rad = m
    return deg_factor_up(d) * (weighted_norm_up(W, terms) + rad)


ZERO_MODEL = (0, [], F(0))


def real_comp_model(n, d, P):
    return ZERO_MODEL if P is None else (d, sorted_terms(n, P), F(0))


def of_deriv(j, d, terms):
    """`CertModel.ofDeriv W j d P`: coefficients i k_j c at degree d + 1 (exact: no radius)."""
    out = []
    for k, re, im in terms:
        kj = k[j] if j < len(k) else 0
        if kj != 0:
            out.append((k, -im * kj, re * kj))
    return (d + 1, out, F(0))


def to_deg(W, pe, d, m):
    """`CertModel.toDeg W pe d m` (pe = (machinK, machinJ))."""
    if m[0] == d:
        return m
    e = m[0] - d
    c = two_pi_zpow_hi(pe[0], pe[1], e)
    lo = two_pi_zpow_lo(pe[0], pe[1], e)
    r = c - lo
    return (d, [(k, c * re, c * im) for k, re, im in m[1]], c * m[2] + r * weighted_norm_up(W, m[1]))


def comp_deriv_model(n, W, pe, d, P, j):
    return to_deg(W, pe, 0, of_deriv(j, d, [] if P is None else sorted_terms(n, P)))


def comp(dK, a, n):
    """(degree, component) of row a of the step: angle rows a < n, action rows a - n (`getD`, `[·]?`)."""
    if a < n:
        degs, polys, i = dK["angleDeg"], dK["angle"], a
    else:
        degs, polys, i = dK["actionDeg"], dK["action"], a - n
    return (degs[i] if i < len(degs) else 0), (polys[i] if i < len(polys) else None)


def step_model(n, dK, a):
    d, P = comp(dK, a, n)
    return real_comp_model(n, d, P)


def dstep_model(n, W, pe, dK, a, j):
    d, P = comp(dK, a, n)
    return comp_deriv_model(n, W, pe, d, P, j)


def step_sups(n, W, dK):
    return [sup_bound(W, step_model(n, dK, a)) for a in range(2 * n)]


def dstep_matrix(n, W, Wb, pe, dK):
    """lv a j = supBound Wb (dstepModel n W pe dK a j), a < 2n, j < n."""
    return [[sup_bound(Wb, dstep_model(n, W, pe, dK, a, j)) for j in range(n)] for a in range(2 * n)]


def sums_ok(lv, n, b, col):
    """`sumsOk lv b col`, with the binding sum."""
    if col:
        sums = [sum((lv[a][j] for a in range(2 * n)), F(0)) for j in range(n)]
    else:
        sums = [sum((lv[a][j] for j in range(n)), F(0)) for a in range(2 * n)]
    return all(s <= b for s in sums), max(sums + [F(0)])


# ============================================================================================ hybStepOk (Claims.lean)
def hyb_weights_ok(cert, st, rho1, rhoi, rhoT):
    s, N = cert["expHalvings"], cert["expOrder"]
    W1, Wi, WT = st["W1"], st["Winf"], st["WT"]
    return [("checkWeight W1", check_weight(W1, s, N)), ("checkWeight Winf", check_weight(Wi, s, N)),
            ("checkWeight WT", check_weight(WT, s, N)), ("rho1 <= W1.rho", rho1 <= W1[0]),
            ("W1.rho <= weight.rho", W1[0] <= cert["weightRho"]), ("rhoInf <= Winf.rho", rhoi <= Wi[0]),
            ("rhoT <= WT.rho", rhoT <= WT[0]), ("0 < rhoT", 0 < rhoT), ("rhoT < rho", rhoT < cert["rho"])]


def hyb_poly_ok(n, st, pe, vals):
    dK, cl = st["dK"], st["cl"]
    W1, Wi = st["W1"], st["Winf"]
    out = []
    for name, W, d in (("d0", W1, cl["d0"]), ("dinf", Wi, cl["dinf"]), ("d0R", REAL_WEIGHT, cl["d0R"])):
        sups = step_sups(n, W, dK)
        vals["sup_" + name] = sups
        out.append(("stepSupOk " + name, d >= 0 and all(x <= d for x in sups)))
    for name, W, Wb, col in (("d1", W1, W1, False), ("d1t", W1, W1, True), ("d1R", Wi, REAL_WEIGHT, False),
                             ("d1tR", Wi, REAL_WEIGHT, True)):
        key = "lv_" + ("strip" if Wb is W1 else "real")
        if key not in vals:
            vals[key] = dstep_matrix(n, W, Wb, pe, dK)
        ok, top = sums_ok(vals[key], n, cl[name], col)
        vals["sum_" + name] = top
        out.append(("dstepOk " + name, cl[name] >= 0 and ok))
    return out


def hyb_cauchy_ok(n, bp, cl, rhoT):
    return [("cauchy dE0", n * bp["err"] <= cl["dE0"] * (bp["rho"] - rhoT)),
            ("cauchy dE0R", n * bp["err"] <= cl["dE0R"] * (bp["rho"] - rhoT))]


# ============================================================================================ TransferQ.lean
def frame(l, lt, beta, nu, nut, d1, d1t):
    """`FrameQ` and its numbers."""
    g = lt * d1 + d1t * l + d1t * d1
    b1 = qdiv(beta, 1 - beta * g)
    b = qdiv(beta ** 2 * g, 1 - beta * g)
    return dict(l=l, lt=lt, beta=beta, nu=nu, nut=nut, d1=d1, d1t=d1t, g=g, b1=b1, b=b,
                nD=b1 * d1 + l * b, nDt=b1 * d1t + lt * b)


def dABQ(f, cTh, cDTh, d):
    return f["nDt"] * cTh * (f["nu"] + f["nD"]) + f["nut"] * (cDTh * d) * (f["nu"] + f["nD"]) + f["nut"] * cTh * f["nD"]


def e1_step(b, M2):
    return b["lE"] + M2 / 2 * b["d0"] ** 2


def frS(b, k):
    return frame(k["l"], k["lt"], k["beta"], k["nu"], k["nut"], b["d1"], b["d1t"])


def frR(b, k):
    return frame(k["l"], k["lt"], k["beta"], k["nu"], k["nut"], b["d1R"], b["d1tR"])


def wB(nn, M1, l, lt, dE):
    return lt * (4 * nn * M1) * l + dE * (2 * nn * l + lt)


def lam0(b, k, nn, M1, real):
    dE = b["dE0R"] if real else b["dE0"]
    o = b["o0R"] if real else b["o0"]
    return k["nut"] * k["beta"] * dE + k["beta"] ** 3 * wB(nn, M1, k["l"], k["lt"], dE) * o


def lam1(b, k, nn, M1, M2, delta, real):
    f = frR(b, k) if real else frS(b, k)
    dE = nn * qinv(delta) * e1_step(b, M2)            # the invariance error (TransferQ: `b.e1 M2`)
    o = b["o1R"] if real else b["o1"]
    return (f["nut"] + f["nDt"]) * f["b1"] * dE + f["b1"] ** 3 * wB(nn, M1, f["l"] + f["d1"], f["lt"] + f["d1t"], dE) * o


def t1_of(b, k, nn, M1, M2, delta, cTh):
    f = frS(b, k)
    return (min(k["t"] + dABQ(f, cTh, 2 * M2, b["d0"]) + lam0(b, k, nn, M1, False),
                (f["nut"] + f["nDt"]) * cTh * (f["nu"] + f["nD"])) + lam1(b, k, nn, M1, M2, delta, False))


def tA_of(b, k, nn, M1, M2, delta, cTh):
    return (dABQ(frR(b, k), cTh, 2 * M2, b["d0R"]) + lam0(b, k, nn, M1, True) +
            lam1(b, k, nn, M1, M2, delta, True))


def tAext_of(q, b, k, nn, M1, M2, delta, cTh):
    f = frR(b, k)
    return max(tA_of(b, k, nn, M1, M2, delta, cTh) + q["dw"],
               nn * (q["Mh1"] * f["nDt"] + q["Mh2"] * b["d0R"] * (k["nut"] + f["nDt"])))


def e1_iso(q, b, M2):
    return max(e1_step(b, M2), q["lH"] + q["Mh2"] / 2 * b["d0R"] ** 2)


# ============================================================================================ transferOk (RestartQ.lean)
def hyb_numbers(n, p, w):
    """`HybWit.kq`, `qq`, `δ1`, `ρT`, `tAx`, `t1`, `mT` and the intermediate values."""
    R0, st, p1 = w["R0"], w["step"], w["p1"]
    cl = st["cl"]
    k = dict(l=p["sK"] - p["mu"], lt=R0["bL"], beta=p["sB"] - p["mu"], nu=R0["bN"], nut=R0["bNt"], t=R0["bT"],
             m=p["sT"] - p["mu"])
    q = dict(lH=p1["err"] - R0["d2h"] / 2 * cl["d0R"] ** 2, dw=st["dw"], Mh1=R0["dh"], Mh2=R0["d2h"])
    d1 = min(F(1), (p1["rho"] - p1["rhoInf"]) / (2 * 3))
    M1, M2, cTh = R0["dx"], R0["d2x"], 2 * R0["dx"]
    tAx = tAext_of(q, cl, k, n, M1, M2, d1, cTh)
    fS, fR = frS(cl, k), frR(cl, k)
    return dict(kq=k, qq=q, delta1=d1, rhoT=p1["rho"] - d1, tAx=tAx, t1=t1_of(cl, k, n, M1, M2, d1, cTh),
                mT=qdiv(k["m"], 1 - k["m"] * tAx), frS=fS, frR=fR,
                dabS=dABQ(fS, cTh, 2 * M2, cl["d0"]), dabR=dABQ(fR, cTh, 2 * M2, cl["d0R"]),
                lam0S=lam0(cl, k, n, M1, False), lam0R=lam0(cl, k, n, M1, True),
                lam1S=lam1(cl, k, n, M1, M2, d1, False), lam1R=lam1(cl, k, n, M1, M2, d1, True),
                tA=tA_of(cl, k, n, M1, M2, d1, cTh), e1=e1_step(cl, M2), e1iso=e1_iso(q, cl, M2),
                sK1=k["l"] + cl["d1"] + p1["mu"], sB1=fS["b1"] + p1["mu"])


def transfer_ok(n, p, box, w, h):
    """the 35 conjuncts of `transferOk`, named as the fields of `TransferFacts`."""
    R0, st, p1, w1 = w["R0"], w["step"], w["p1"], w["w1"]
    cl, k, R1 = st["cl"], h["kq"], w1["base"]["R"]
    fS, fR = h["frS"], h["frR"]
    return [
        ("mu1", 0 < p1["mu"]), ("m1", cl["d0"] + p1["mu"] <= p["mu"]),
        ("m2", cl["d1"] + p1["mu"] / 2 <= p["mu"] / 2), ("rho", p1["rho"] <= p["rho"]),
        ("gS", k["beta"] * fS["g"] < 1), ("gR", k["beta"] * fR["g"] < 1),
        ("e1", h["e1"] <= p1["err"]), ("eH", st["lH"] + R0["d2h"] / 2 * cl["d0R"] ** 2 <= p1["err"]),
        ("err0", 0 <= p1["err"]), ("m0", 0 < k["m"]), ("tA", k["m"] * h["tAx"] < 1),
        ("tau", p1["tau"] == p["tau"]), ("rhoInf", p1["rhoInf"] == p["rhoInf"]), ("M", p1["M"] == p["M"]),
        ("gamma", p1["gamma"] == p["gamma"]), ("gbar", p1["gbar"] == p["gbar"]),
        ("sigma", p1["sigma_omega"] == p["sigma_omega"]), ("E0", p1["E0"] == p["E0"]), ("s1", p1["s"] == st["s1"]),
        ("sK", p1["sK"] == h["sK1"]), ("sB", h["sB1"] <= p1["sB"]), ("sT", h["mT"] + p1["mu"] <= p1["sT"]),
        ("nu", p1["nuRay"] <= p["nuRay"] - st["dw"]), ("nu0", 0 < p["nuRay"] - st["dw"]),
        ("dh", R1["dh"] == R0["dh"]), ("dx", R1["dx"] == R0["dx"]), ("d2x", R1["d2x"] == R0["d2x"]),
        ("d2h", R1["d2h"] == R0["d2h"]), ("bL", k["lt"] + cl["d1t"] <= R1["bL"]),
        ("bN", k["nu"] + fS["nD"] <= R1["bN"]), ("bNt", k["nut"] + fS["nDt"] <= R1["bNt"]),
        ("bT", h["t1"] <= R1["bT"]), ("disp", max(cl["dinf"], st["dw"]) + p1["disp"] <= p["disp"]),
        ("bud", cl["dinf"] + p1["disp"] <= p["mu"] / 2),
        ("room", p["disp"] < (p["sigma_omega"] - p["s"]) * freq_norm_lo(box))]


def freq_norm_lo(box):
    out = F(0)
    for c, r in reversed(box):
        out = max(abs(c) - r, out)
    return out


# ============================================================================================ refinedCoreR (classical)
PI_LO, PI_UP, E_LO = F(3141592, 10 ** 6), F(3141593, 10 ** 6), F(2718281, 10 ** 6)   # ClassicalQ.lean


def zeta_up(a, J):
    return sum((qinv(a + j) ** 2 for j in range(J)), F(0)) + qinv(a + J - F(1, 2))


def rad_up(n, tau, J, delta):
    shell = F(2) ** (2 * tau + 1) * zeta_up(F(2) ** tau, J)
    eps = 4 * PI_UP * delta * (2 * F(tau) / E_LO) ** (2 * tau) / math.factorial(2 * tau)
    return F(2) ** n * (shell * math.factorial(2 * tau) * (1 + eps))


def classical_ok(n, tau, J, delta, c):
    """`classicalOk n τ J δ c`."""
    return c > 0 and rad_up(n, tau, J, delta) <= (c * (2 * PI_LO) * (4 * PI_LO) ** tau) ** 2


def refined_core(n, p1, box, w1, bp, wP, sites):
    """the conjuncts of `refinedCoreR n p1 box w1`; sitesOk by exact reuse of the base run's sites."""
    ok, parts = NQ.refined_core_r(n, p1, box, w1, detail=True)
    core, Q = w1["base"]["core"], NQ.refined_num(n, p1, box, w1["base"])
    out = [("Xs > 0", parts["Xs_pos"]), ("wfOk", parts["wf"]), ("okR", parts["okR"]), ("budgetOk", parts["budget"])]
    if sites == "reuse-base" and wP is not None:
        c0 = wP["base"]["core"]
        same = (p1["tau"] == bp["tau"] and core["kp"] == c0["kp"] and p1["rho"] == bp["rho"] and
                p1["rhoInf"] == bp["rhoInf"] and core["c"] == c0["c"] and core["cbar"] == c0["cbar"] and
                core["J"] == c0["J"] and w1["base"]["kappa"] == wP["base"]["kappa"] and p1["gamma"] == bp["gamma"] and
                w1["base"]["sites"] == wP["base"]["sites"])
        out.append(("sitesOk (reuse of the base run's)", True if same else None))
    else:
        out.append(("sitesOk (explicit list)", None))
    out.append(("classicalOk tail", classical_ok(n, p1["tau"], core["J"], Q.delta(core["kp"]), core["ctail"])))
    out.append(("finalOkA", parts["final"]))
    return out


# ============================================================================================ parsing
def params_from(d):
    out = {k: F(v) for k, v in d.items() if k != "tau"}
    out["tau"] = int(d["tau"])
    return out


def box_from(d):
    return [(F(c), F(r)) for c, r in d]


def poly_from(d, S):
    """CertRealPoly -> (zero, [(key, re, im)]) with exact rationals."""
    return F(int(d["zero"]), 2 ** S), [(tuple(k), F(int(c[0]), 2 ** S), F(int(c[1]), 2 ** S)) for k, c in d["half"]]


def emb_from(d, S):
    return dict(angleDeg=[int(x) for x in d["angleDeg"]], angle=[poly_from(p, S) for p in d["angle"]],
                actionDeg=[int(x) for x in d["actionDeg"]], action=[poly_from(p, S) for p in d["action"]])


def witR_from(d):
    core = d["base"]["core"]
    c = dict(Xs=F(core["Xs"]), kp=int(core["kp"]), th=F(core["th"]), c=[F(x) for x in core["c"]],
             cbar=[F(x) for x in core["cbar"]], ctail=F(core["ctail"]), sB=F(core["sB"]), sT=F(core["sT"]),
             sLt=F(core["sLt"]), sN=F(core["sN"]), sNt=F(core["sNt"]), t=F(core["t"]), J=int(core["J"]))
    return dict(base=dict(core=c, R={k: F(v) for k, v in d["base"]["R"].items()}, kappa=F(d["base"]["kappa"]),
                          sites=d["base"]["sites"]), bF=F(d["bF"]), bT=F(d["bT"]))


def weight_from(d):
    return F(d["rho"]), F(d["w"])


CLAIMS = ("d0", "dinf", "d1", "d1t", "d0R", "d1R", "d1tR", "lE", "dE0", "o0", "dE0R", "o0R", "o1", "o1R")


def hybwit_from(data):
    """the `HybWit` of a file: R0 = base.claim; step (dK, s1, W1, Winf, WT, cl, lH, dw); p1; w1."""
    S, step = int(data["scale_bits"]), data["step"]
    cl = {k: F(step["claims"][k]) for k in CLAIMS}
    W = step["weights"]
    st = dict(dK=emb_from(step["dK"], S), s1=F(step["s1"]), W1=weight_from(W["rho1"]), Winf=weight_from(W["rhoinf"]),
              WT=weight_from(W["torsion"]), cl=cl, lH=F(step["claims"]["lH"]), dw=F(step["claims"]["dw"]))
    return dict(R0={k: F(v) for k, v in data["base"]["claim"].items()}, step=st,
                p1=params_from(data["restart"]["params1"]), w1=witR_from(data["restart"]["witness1"]))


def cert_from(data, settings=None):
    """the fields of the base `TorusCertificate` that the ported checks read."""
    b = data["base"]
    c = b.get("cert", {})
    s, N = int(c.get("expHalvings", 8)), int(c.get("expOrder", 24))
    pe = c.get("piEnc", {"machinK": 4, "machinJ": 4})
    k, j = int(pe["machinK"]), int(pe["machinJ"])
    if settings:
        s, N, k, j = settings
    bp = params_from(b["params"])
    return dict(expHalvings=s, expOrder=N, pe=(k, j), weightRho=F(c.get("weightRho", b["params"]["rho"])),
                rho=bp["rho"])


# ============================================================================================ checkHybrid
def check(data, settings=None, margins=True):
    n = int(data["n"])
    base = data["base"]
    bp, box = params_from(base["params"]), box_from(base["freqBox"])
    cert = cert_from(data, settings)
    w = hybwit_from(data)
    st, p1 = w["step"], w["p1"]
    wP = witR_from(data["plain_witness"]) if data.get("plain_witness") else None
    vals = {}
    h = hyb_numbers(n, bp, w)
    vals.update({k: v for k, v in h.items() if k not in ("kq", "qq", "frS", "frR")})
    for nm in ("frS", "frR"):
        vals.update({nm + "." + x: h[nm][x] for x in ("g", "b1", "b", "nD", "nDt")})
    groups = {}
    groups["transferOk"] = transfer_ok(n, bp, box, w, h)
    rhoT = h["rhoT"]
    groups["hybWeightsOk"] = hyb_weights_ok(cert, st, p1["rho"], p1["rhoInf"], rhoT)
    groups["hybPolyOk"] = hyb_poly_ok(n, st, cert["pe"], vals)
    groups["hybOmegaOk"] = [("omega o0, o0R, o1, o1R", None)]
    groups["hybCauchyOk"] = hyb_cauchy_ok(n, bp, st["cl"], rhoT)
    groups["hybCompOk"] = [("lin lE, energy lH", None)]
    groups["dw"] = [("|s1 - s| boxNormUp <= dw", abs(st["s1"] - bp["s"]) * NQ.box_norm_up(box) <= st["dw"])]
    groups["refinedCoreR"] = refined_core(n, p1, box, w["w1"], bp, wP, data["restart"].get("sites"))
    if not data["step"].get("iso", True):
        groups["iso"] = [("iso (the Lean checker is isoenergetic only)", False)]
    fails = [(g, nm) for g, L in groups.items() for nm, v in L if v is False]
    undecided = [(g, nm) for g, L in groups.items() for nm, v in L if v is None]
    res = dict(name=data["name"], ok=not fails, fails=fails, undecided=undecided, groups=groups, values=vals,
               settings=dict(expHalvings=cert["expHalvings"], expOrder=cert["expOrder"], piEnc=cert["pe"]))
    res["group_ok"] = {g: (False if any(v is False for _, v in L) else (None if any(v is None for _, v in L) else True))
                       for g, L in groups.items()}
    if margins and not fails:
        w1 = w["w1"]
        Xmax1, Q1 = NQ.max_xs(n, p1, box, w1, lo=w1["base"]["core"]["Xs"] / 4)
        e1s = Xmax1 * p1["gamma"] ** 4 * Q1.delta0 ** (4 * p1["tau"])
        res.update(e1=float(h["e1iso"]), e1_star=float(e1s), hybrid_margin=math.log10(e1s / h["e1iso"]))
        if wP is not None:
            XmaxP, QP = NQ.max_xs(n, bp, box, wP, lo=wP["base"]["core"]["Xs"] / 4)
            eP = XmaxP * bp["gamma"] ** 4 * QP.delta0 ** (4 * bp["tau"])
            res.update(e_base=float(bp["err"]), e_star_plain=float(eP), plain_margin=math.log10(eP / bp["err"]))
        k = h["kq"]
        rel = lambda a, b: float(1 - a / b) if b != 0 else float("inf")
        res["slack"] = {"d0+mu1<=mu": rel(st["cl"]["d0"] + p1["mu"], bp["mu"]),
                        "d1+mu1/2<=mu/2": rel(st["cl"]["d1"] + p1["mu"] / 2, bp["mu"] / 2),
                        "m tAx<1": float(1 - k["m"] * h["tAx"]), "sT": rel(h["mT"] + p1["mu"], p1["sT"]),
                        "bT": rel(h["t1"], w1["base"]["R"]["bT"]), "params1.err": float(p1["err"] / h["e1iso"] - 1),
                        "outer disp": rel(max(st["cl"]["dinf"], st["dw"]) + p1["disp"], bp["disp"])}
        res["poly"] = {nm: float(max(vals["sup_" + nm])) for nm in ("d0", "dinf", "d0R")}
        res["poly"].update({nm: float(vals["sum_" + nm]) for nm in ("d1", "d1t", "d1R", "d1tR")})
    return res


def report(res, log=print):
    verdict = "PASSES the ported checks" if res["ok"] else "FAILS"
    log("== %s: %s (expHalvings %d, expOrder %d, Machin %s)" % (res["name"], verdict, res["settings"]["expHalvings"],
                                                              res["settings"]["expOrder"], res["settings"]["piEnc"]))
    for g, nm in res["fails"]:
        log("   fail: %s / %s" % (g, nm))
    log("   groups: " + ", ".join("%s %s" % (g, {True: "ok", False: "FAIL", None: "kernel-only"}[v])
                                  for g, v in res["group_ok"].items()))
    if "plain_margin" in res:
        log("   plain run:  e = %.4g, e* = %.4g, margin %+.3f" % (res["e_base"], res["e_star_plain"],
                                                                   res["plain_margin"]))
    if "hybrid_margin" in res:
        log("   restarted:  e1 = %.4g, e1* = %.4g, hybrid margin %+.3f" % (res["e1"], res["e1_star"],
                                                                         res["hybrid_margin"]))
    if res.get("slack"):
        log("   slacks: " + ", ".join("%s %.3g" % (k, v) for k, v in res["slack"].items()))
    if res.get("poly"):
        log("   exact step bounds (Lean's): " + ", ".join("%s %.6g" % (k, v) for k, v in res["poly"].items()))


if __name__ == "__main__":
    args, settings = sys.argv[1:], None
    if args and args[0] == "--settings":
        settings = tuple(int(x) for x in args[1].split(","))
        args = args[2:]
    for path in args:
        report(check(json.load(open(path)), settings))
