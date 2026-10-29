#!/usr/bin/env python3
"""SO-TOYGEN: passing certificate data for the toys T2, T2d, T3 and the checker-only toy TR (design §8).

Untrusted tooling.  Builds each `TorusCertificate n ℚ` (A-E §G) as exact data, runs the Python mirror of
`checkTorusCertificate` (toy_check.py) and writes deterministic JSON:

    python3 toy_gen.py JETS.json OUTDIR [toy ...]

JETS.json is the landed jet programs (toy_lean_extract.py).  OUTDIR receives <toy>.json (certificate and
verification) and summary.json.
"""
import json, math, sys, hashlib
from fractions import Fraction as F
from math import isqrt
import toy_arith as A
import toy_model as Mo
import toy_check as K
import toy_constants as C

GAMMA2 = F(1, 42)    # lunarNuMinus_half_isDiophantine: IsDiophantine (1/42) 1 ![nu_-/2, 1/2] (SO-DIO)
GAMMA3 = F(1, 12)    # cubicFreq_isDiophantine: IsDiophantine (1/12) 2 cubicFreq (SO-DIO3)
NU_COEFFS = [[F(3039, 6236), F(1, 6236)], [F(1, 2)]]           # lunarFreqMinus_eq at sqrt 5
CUBIC_COEFFS = [[F(0), F(1, 2)], [F(0), F(0), F(1, 2)], [F(1, 2)]]  # cubicFreq_eq_algFreq at cbrt 2
MARGIN = F(1, 1000)  # target: isoC1Q e / (gamma^4 rho^(4 tau)) <= MARGIN


def lg(q):
    q = F(q)
    return math.log10(q.numerator) - math.log10(q.denominator) if q > 0 else float("-inf")


def root_encl(d, m, digits):
    """[lo, hi] = [floor(d^(1/m) 10^D), +1] / 10^D, with checkRootEnclosure m d lo hi."""
    s = 10 ** digits
    lo_i = iroot(d * s ** m, m)
    lo, hi = F(lo_i, s), F(lo_i + 1, s)
    assert A.checkRootEnclosure(m, d, lo, hi)
    return lo, hi


def iroot(N, m):
    x = 1 << ((N.bit_length() + m - 1) // m)
    while True:                     # Newton, then fix up
        y = ((m - 1) * x + N // x ** (m - 1)) // m
        if y >= x:
            break
        x = y
    while x ** m > N:
        x -= 1
    while (x + 1) ** m <= N:
        x += 1
    return x


def alg_box(coeffs, lo, hi):
    box = []
    for row in coeffs:
        L, H = A.algRowLo(row, lo, hi), A.algRowHi(row, lo, hi)
        box.append(((L + H) / 2, (H - L) / 2))
    return box


def weight_for(rho, s, N):
    """the least w in 10^-6 Z with w >= ratExpUp(2 piUp rho, s, N) (checkWeight)."""
    v = A.ratExpUp(2 * A.PI_UP * F(rho), s, N)
    return round_up(v, 10 ** 6)


def exp_params(rho):
    q = 2 * A.PI_UP * F(rho)
    s = 0
    while q / 2 ** s > 1:
        s += 1
    return s + 2, 24


def round_up(q, den=100):
    q = F(q)
    return F(-((-q.numerator * den) // q.denominator), den)


def pi_enc(k=4, j=4):
    lo, hi = A.piLowRat(k, j), A.piUpRat(k, j)
    return ((lo + hi) / 2, (hi - lo) / 2, k, j)


def base_cert(toy, n, jets, rho, rhoH, centre, radius, box, action, params, cfg_full, cfg_low, wit=None,
              rhoinf=None):
    s, N = exp_params(max(rho, rhoH))
    c = dict(toy=toy, n=n, _jet=jets[toy if toy != "TR" else "T2"],
             params=params, weightH=(F(rhoH), weight_for(rhoH, s, N)), centre=list(centre), radius=list(radius),
             freqBox=box,
             emb=dict(angleDeg=[0] * n, angle=[(F(0), [])] * n, actionDeg=[0] * n,
                      action=[(F(a), []) for a in action]),
             weight=(F(rho), weight_for(rho, s, N)),
             wit=wit or dict(expWit=[], invWit=[], charWit=[]),
             gramInv=[[Mo.p_const((1, 0), n) if i == j else Mo.p_zero() for j in range(n)] for i in range(n)],
             torsInv=None, cfgFull=cfg_full, cfgLow=cfg_low, piEnc=pi_enc(), expHalvings=s, expOrder=N)
    return c


def torsion_witness(c):
    """S = exact inverse of the averaged centre matrix C (from the mirror's torsion models)."""
    K.prepare(c)
    db, _ = K.gram_check(c)
    T, info = K.torsion_models(c, db)
    n = c["n"]
    Cm = []
    for row in T:
        r = []
        for m in row:
            m0 = Mo.m_toDeg(m, 0, c["weight"][1], c["piEnc"], c["_log"])
            z = Mo.p_coeff0(m0.poly, n)
            assert z[1] == 0
            r.append(z[0])
        Cm.append(r)
    return [[(x, F(0)) for x in row] for row in mat_inv(Cm)], Cm


def mat_inv(Mx):
    k = len(Mx)
    a = [list(map(F, row)) + [F(1 if i == j else 0) for j in range(k)] for i, row in enumerate(Mx)]
    for col in range(k):
        piv = next(r for r in range(col, k) if a[r][col] != 0)
        a[col], a[piv] = a[piv], a[col]
        pv = a[col][col]
        a[col] = [x / pv for x in a[col]]
        for r in range(k):
            if r != col and a[r][col] != 0:
                f = a[r][col]
                a[r] = [x - f * y for x, y in zip(a[r], a[col])]
    return [row[k:] for row in a]


def norm_S(S):
    return max(sum(A.normUp(x) for x in row) for row in S)


def finish_params(c, err, gamma, extra_disp=F(1)):
    """M from the ball pass, sigma_T from the torsion witness, disp from isoC2Q; mutates c."""
    p = c["params"]
    K.prepare(c)
    b, _ = K.ball_bounds(c)
    p["M"] = round_up(max(b.values()) * F(1001, 1000))
    p["sK"] = round_up(1 + p["mu"] + F(1, 1000))
    p["sB"] = round_up(1 + p["mu"] + F(1, 1000))
    S, Cm = torsion_witness(c)
    c["torsInv"] = S
    p["sT"] = round_up(norm_S(S) * F(1001, 1000) + p["mu"])
    p["err"] = err
    p["disp"] = F(0)
    q = dict(p, n=c["n"])
    _, d = C.smallness(q)
    p["disp"] = round_up(d["disp_min"] * extra_disp * F(1001, 1000), 10 ** max(0, int(-lg(d["disp_min"])) + 6)) \
        if d["disp_min"] > 0 else F(0)
    return c


def threshold(c):
    p = dict(c["params"], n=c["n"], err=F(0), disp=F(0))
    _, d = C.smallness(p)
    return d["threshold"]


# ---------------------------------------------------------------- the toys
def params_common(n, tau, rho, rhoinf, mu, nu, gamma, s=F(2), sw=F(3)):
    return dict(tau=tau, rho=F(rho), rhoInf=F(rhoinf), M=F(0), sK=F(0), sB=F(0), sT=F(0), mu=F(mu),
                gbar=F(gamma), sigma_omega=F(sw), nuRay=F(nu), gamma=F(gamma), s=F(s), err=F(0), E0=F(0),
                disp=F(0))


def cfg(cutoff, taylorN=24, halvings=8):
    return dict(cutoff=cutoff, taylorN=taylorN, halvings=halvings)


def toy_T2(jets, digits):
    lo, hi = root_encl(5, 2, digits)
    box = alg_box(NU_COEFFS, lo, hi)
    nu_t = 2 * box[0][0]
    mu, r = F(1, 100), F(1, 50)
    rho, rhoinf = F(9), F(1)
    p = params_common(2, 1, rho, rhoinf, mu, F(49, 100), GAMMA2)
    c = base_cert("T2", 2, jets, rho, rho + 2 * mu, [nu_t, -nu_t ** 2 / 2], [r, r], box, [nu_t, -nu_t ** 2 / 2], p,
                  cfg(0), cfg(0))
    c["root"] = dict(m=2, d=5, lo=lo, hi=hi, coeffs=NU_COEFFS)
    return finish_params(c, 4 * box[0][1], GAMMA2)


def toy_TR(jets):
    box = [(F(1, 4), F(0)), (F(1, 2), F(0))]
    mu, r = F(1, 100), F(1, 50)
    rho, rhoinf = F(9), F(1)
    p = params_common(2, 1, rho, rhoinf, mu, F(49, 100), GAMMA2)
    c = base_cert("TR", 2, jets, rho, rho + 2 * mu, [F(1, 2), F(-1, 8)], [r, r], box, [F(1, 2), F(-1, 8)], p,
                  cfg(0), cfg(0))
    return finish_params(c, F(0), GAMMA2)


def toy_T3(jets, digits):
    lo, hi = root_encl(2, 3, digits)
    box = alg_box(CUBIC_COEFFS, lo, hi)
    a, b = 2 * box[0][0], 2 * box[1][0]
    mu, r = F(1, 100), F(1, 50)
    rho, rhoinf = F(9), F(1)
    L = max(abs(cc) - rr for cc, rr in box)
    nu = F(math.floor(float(L) * 100) - 1, 100)
    p = params_common(3, 2, rho, rhoinf, mu, nu, GAMMA3)
    c = base_cert("T3", 3, jets, rho, rho + 2 * mu, [a, b, -(a * a + b * b) / 2], [r, r, r], box,
                  [a, b, -(a * a + b * b) / 2], p, cfg(0), cfg(0))
    c["root"] = dict(m=3, d=2, lo=lo, hi=hi, coeffs=CUBIC_COEFFS)
    return finish_params(c, 4 * max(box[0][1], box[1][1]), GAMMA3)


def recip_witness(K_, P, aconst=3):
    """Q = Σ_{|k| <= K} c_k χ_k, c_k = (-r)^{|k|}/sqrt(a^2 - 1), r = a - sqrt(a^2 - 1), dyadic at 2^-P."""
    S = 1 << (P + 40)
    s8 = isqrt((aconst * aconst - 1) * S * S)               # sqrt(a^2 - 1) * S
    r = aconst * S - s8                                      # r * S
    terms = []
    pw = S                                                   # r^k * S
    for k in range(K_ + 1):
        ck = F(pw * (-1) ** k, s8)                          # (-r)^k / sqrt(a^2 - 1)
        ck = F(round(ck * 2 ** P), 2 ** P)
        terms.append(((k, 0), (ck, F(0))))
        if k:
            terms.append(((-k, 0), (ck, F(0))))
        pw = pw * r // S
    return Mo.p_reduce(Mo.p_from_terms(terms))


def toy_T2d(jets, digits, rhoH, mu, rr, Kq, Pq, err=None, rhoinf_frac=F(1, 10), cut_low=None, aconst=3):
    lo, hi = root_encl(5, 2, digits)
    box = alg_box(NU_COEFFS, lo, hi)
    nu_t = 2 * box[0][0]
    rho = rhoH - 2 * mu                                   # rho + iota + mu <= rhoH with margin mu (iota = 0)
    rhoinf = rho * rhoinf_frac
    p = params_common(2, 1, rho, rhoinf, mu, F(49, 100), GAMMA2)
    s_pin, N_pin = 0, 400
    Q = recip_witness(Kq, Pq, aconst)
    wit = dict(expWit=[], invWit=[Q], charWit=[((0, 0), (Mo.p_const((1, 0), 2), s_pin, N_pin))])
    c = base_cert("T2d", 2, jets, rho, rhoH, [nu_t, -nu_t ** 2 / 2], [rr, rr], box, [nu_t, -nu_t ** 2 / 2], p,
                  cfg(2 * Kq + 2), cfg(cut_low if cut_low is not None else 2 * Kq + 2), wit=wit)
    c["root"] = dict(m=2, d=5, lo=lo, hi=hi, coeffs=NU_COEFFS)
    c["recip"] = dict(K=Kq, P=Pq, a=aconst)
    return finish_params(c, err if err is not None else 4 * box[0][1], GAMMA2)


# ---------------------------------------------------------------- serialization
def js(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, bool) or x is None or isinstance(x, (int, str)):
        return x
    if isinstance(x, float):
        return x
    if isinstance(x, dict):
        return {str(k): js(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [js(v) for v in x]
    raise TypeError(type(x))


def poly_json(P):
    return [[list(k), [str(re), str(im)]] for k, (re, im) in Mo.p_terms(P)]


def cert_json(c):
    w = c["wit"]
    out = dict(
        toy=c["toy"], n=c["n"],
        params={k: str(v) if isinstance(v, F) else v for k, v in c["params"].items()},
        ham=dict(lean=c.get("_ham_lean"), jetSlots=len(c["_jet"]["ops"])),
        weightH=dict(rho=str(c["weightH"][0]), w=str(c["weightH"][1])),
        centre=js(c["centre"]), radius=js(c["radius"]),
        freqBox=[[str(a), str(b)] for a, b in c["freqBox"]],
        emb=dict(angleDeg=c["emb"]["angleDeg"], angle=[dict(zero=str(z), half=h) for z, h in c["emb"]["angle"]],
                 actionDeg=c["emb"]["actionDeg"],
                 action=[dict(zero=str(z), half=h) for z, h in c["emb"]["action"]]),
        weight=dict(rho=str(c["weight"][0]), w=str(c["weight"][1])),
        wit=dict(expWit=[dict(poly=poly_json(E[0]), pinHalvings=E[1], pinOrder=E[2]) for E in w["expWit"]],
                 invWit=[poly_json(Q) for Q in w["invWit"]],
                 charWit=[[list(k), dict(poly=poly_json(E[0]), pinHalvings=E[1], pinOrder=E[2])]
                          for k, E in w["charWit"]]),
        gramInv=[[poly_json(P) for P in row] for row in c["gramInv"]],
        torsInv=[[[str(z[0]), str(z[1])] for z in row] for row in c["torsInv"]],
        cfgFull=dict(c["cfgFull"], toMant="none (direct route)", advice=c.get("_advFull")),
        cfgLow=dict(c["cfgLow"], toMant="none (direct route)", advice=c.get("_advLow")),
        piEnc=dict(centre=str(c["piEnc"][0]), rad=str(c["piEnc"][1]), machinK=c["piEnc"][2],
                   machinJ=c["piEnc"][3]),
        expHalvings=c["expHalvings"], expOrder=c["expOrder"])
    if "root" in c:
        r = c["root"]
        out["freqProvider"] = dict(checkRootEnclosure=[r["m"], r["d"], str(r["lo"]), str(r["hi"])],
                                   checkAlgBox_coeffs=[[str(x) for x in row] for row in r["coeffs"]])
    return out


# ---------------------------------------------------------------- driver
def run_checks(c):
    ok, rep = K.check(c)
    return ok, rep


def tune_digits(build, err_of_digits_log, d0=40):
    """choose the root-enclosure digits so that isoC1Q e/(gamma^4 rho^4tau) <= MARGIN."""
    c = build(d0)
    thr = threshold(c)
    d = max(5, math.ceil(err_of_digits_log - lg(thr * MARGIN)) + 1)
    return d


def summarize(c, ok, rep):
    p = c["params"]
    q = dict(p, n=c["n"])
    _, sm = C.smallness(q)
    hb = rep["checkHamBounds"][1]
    tor = rep["checkTorsion"][1]
    inv = rep["checkInvariance"][1]
    en = rep["checkEnergy"][1]
    emb = rep["checkEmbedding"][1]
    gr = rep["checkGram"][1]
    st = rep["checkStatic"][1]
    f = lambda x: None if x is None else float(x)
    margins = {
        "checkStatic": dict(failed=[k for k, v in st["conds"].items() if not v], normLower=f(st["normLower"]),
                            nu=f(p["nuRay"]), nuMax=f(min(p["s"] - 1, p["sigma_omega"] - p["s"]) * st["normLower"])),
        "checkHamBounds": dict(M=f(p["M"]), bounds={k: f(v) for k, v in hb.get("bounds", {}).items()}),
        "checkEmbedding": dict(DKnorm=f(emb["DKnorm"]), sK_minus_mu=f(p["sK"] - p["mu"]),
                               iota=[f(x) for x in emb["iota"]], actionDist=[f(x) for x in emb["actionDist"]],
                               rho_mu_vs_rhoH=[f(p["rho"] + p["mu"]), f(c["weightH"][0])]),
        "checkInvariance": dict(bound=f(inv.get("bound")), err=f(p["err"]),
                                log10_bound=lg(inv["bound"]) if inv.get("bound") else None),
        "checkEnergy": dict(bound=f(en.get("bound")), err=f(p["err"])),
        "checkGram": dict(delta=f(gr.get("delta")), beta=f(gr.get("beta")), sB_minus_mu=f(p["sB"] - p["mu"])),
        "checkTorsion": dict(deltaT=f(tor.get("deltaT")), normS=f(tor.get("normS")), normR=f(tor.get("normR")),
                             normInvBound=f(tor.get("normInvBound")), sT_minus_mu=f(p["sT"] - p["mu"])),
        "checkSmallness": dict(ratio_C1=f(sm["ratio1"]), log10_ratio_C1=lg(sm["ratio1"]) if sm["ratio1"] else None,
                               log10_threshold=lg(sm["threshold"]), log10_err=lg(p["err"]) if p["err"] else None,
                               disp=f(p["disp"]), disp_min=f(sm["disp_min"]),
                               mSize=f(max(1, p["M"], p["sK"], p["sB"], p["sT"]))),
    }
    return dict(passes=ok, subchecks={k: bool(v[0]) for k, v in rep.items()}, margins=margins)


def products_of(c):
    out = {}
    for name in ("_cfgFull", "_cfgLow"):
        cf = c[name]
        keys, seen = [], set()
        for key, la, lb, pairs in cf.products:
            if key not in seen:
                seen.add(key)
                keys.append((key, la, lb, pairs))
        out[cf.name] = dict(distinct=len(keys), calls=len(cf.products),
                            pairs_distinct=sum(k[3] for k in keys), pairs_calls=sum(k[3] for k in cf.products),
                            largest=sorted(keys, key=lambda t: -t[3])[:6])
        c["_adv" + cf.name[3:]] = [[list(k[0]), "direct"] for k in keys]
    return out


def emit(c, outdir, extra=None):
    ok, rep = run_checks(c)
    prods = products_of(c)
    summ = summarize(c, ok, rep)
    cj = cert_json(c)
    doc = dict(certificate=cj, verification=dict(summ, products={k: dict(v, largest=[[list(t[0]), t[1], t[2], t[3]]
                                                                                    for t in v["largest"]])
                                                                for k, v in prods.items()},
                                                  toDegCalls=len(c["_log"])))
    if extra:
        doc["verification"].update(extra)
    text = json.dumps(doc, indent=1, sort_keys=True) + "\n"
    path = "%s/%s.json" % (outdir, c["toy"])
    with open(path, "w") as fh:
        fh.write(text)
    return ok, rep, summ, hashlib.sha256(text.encode()).hexdigest(), len(text)


def pow10_floor(q):
    """the largest 10^-k <= q (q > 0)."""
    k = math.ceil(-lg(q))
    while F(1, 10 ** k) > q:
        k += 1
    return F(1, 10 ** k)


def t2d_plan(jets, rhoH=F(1, 100), mu=F(1, 1000), rr=F(3, 2000), rhoinf_frac=F(1, 10), cut_low=30):
    """parameters of T2d: err = 10^-k <= MARGIN * threshold; digits and (K, P) sized against err."""
    c = toy_T2d(jets, 10, rhoH, mu, rr, 4, 60, rhoinf_frac=rhoinf_frac)
    thr = threshold(c)
    err = pow10_floor(thr * MARGIN)
    w = float(c["weight"][1])
    r = 3 - 2 * math.sqrt(2)
    digits = math.ceil(-lg(err)) + 2                               # 4 r0 = 10^-digits/3118 <= err/100
    Kq = math.ceil((-lg(err) + 5) / (-math.log10(r * w)))           # tail <= err * 1e-5
    Pq = math.ceil((-lg(err) + 5 + math.log10(2 * Kq + 1) + Kq * math.log10(w)) / math.log10(2))
    return dict(rhoH=rhoH, mu=mu, rr=rr, rhoinf_frac=rhoinf_frac, cut_low=cut_low, err=err, digits=digits, K=Kq,
                P=Pq, threshold=thr)


def build(name, jets):
    if name == "T2":
        c = toy_T2(jets, 30)
        err = pow10_floor(threshold(c) * MARGIN)
        digits = math.ceil(-lg(err)) - 3                            # 4 r0 = 10^-digits/3118 <= err
        c = toy_T2(jets, digits)
        assert c["params"]["err"] <= err
        return c
    if name == "T3":
        c = toy_T3(jets, 30)
        err = pow10_floor(threshold(c) * MARGIN)
        digits = math.ceil(-lg(err)) + 1                            # 4 r1 ~ 1.26 * 10^-digits * 2 <= err
        c = toy_T3(jets, digits)
        assert c["params"]["err"] <= err
        return c
    if name == "TR":
        return toy_TR(jets)
    if name == "T2d":
        pl = t2d_plan(jets)
        c = toy_T2d(jets, pl["digits"], pl["rhoH"], pl["mu"], pl["rr"], pl["K"], pl["P"], err=pl["err"],
                    rhoinf_frac=pl["rhoinf_frac"], cut_low=pl["cut_low"])
        c["_plan"] = pl
        return c
    raise ValueError(name)


def main():
    import time
    jets_path, outdir = sys.argv[1], sys.argv[2]
    names = sys.argv[3:] or ["T2", "T2d", "T3", "TR"]
    J = json.load(open(jets_path))
    jets = J["jets"]
    import os
    spath = "%s/summary.json" % outdir
    summary = json.load(open(spath)) if os.path.exists(spath) else {}
    for name in names:
        t0 = time.time()
        c = build(name, jets)
        c["_ham_lean"] = J["source"]["T2" if name == "TR" else name]["lean"]
        extra = {}
        if "_plan" in c:
            extra["plan"] = js({k: v for k, v in c["_plan"].items()})
        if name == "TR":
            extra["resonance"] = resonance_TR(c)
        ok, rep, summ, sha, size = emit(c, outdir, extra)
        dt = time.time() - t0
        summary[name] = dict(passes=ok, subchecks=summ["subchecks"], sha256=sha, bytes=size,
                             log10_threshold=summ["margins"]["checkSmallness"]["log10_threshold"],
                             log10_err=summ["margins"]["checkSmallness"]["log10_err"],
                             ratio_C1=summ["margins"]["checkSmallness"]["ratio_C1"])
        print(name, "passes" if ok else "FAILS", summ["subchecks"], "%.1fs" % dt, flush=True)
    with open(spath, "w") as fh:
        json.dump(summary, fh, indent=1, sort_keys=True)
        fh.write("\n")


def resonance_TR(c):
    """TR's reference vector (1/4, 1/2) is the exact box centre (radius 0) and k = (2, -1) gives k.omega = 0,
    so IsDiophantine gamma tau omega fails for every gamma > 0 (gamma / |k|_1^tau > 0 = |k.omega|)."""
    box = c["freqBox"]
    assert all(r == 0 for _, r in box)
    om = [cc for cc, _ in box]
    k = (2, -1)
    dot = sum(a * b for a, b in zip(k, om))
    return dict(omega=[str(x) for x in om], k=list(k), k_dot_omega=str(dot), resonant=dot == 0,
                gamma_over_k_tau=str(c["params"]["gamma"] / F(3) ** c["params"]["tau"]),
                diophantine_fails=dot == 0 and c["params"]["gamma"] > 0)


if __name__ == "__main__":
    main()
