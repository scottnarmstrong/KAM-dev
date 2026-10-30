#!/usr/bin/env python3
"""SO-V2PKG: the v2 thresholds of the lunar packages (R2 at N = 65, and sketches at other N), branch by branch.

    python3 -I v2_r2.py [--N 65] [--kp 3] [--json OUT]

Branches of routeAV2 = sharpV2.orElse (routeAFrozen.orElse routeARefined):
  sharpV2       the landed sharpTest (sharp_q.py, kernel-cross-checked at R2: 10^-31.827);
  routeAFrozen  frozenCore (v2_q.frozenCore): classical constants, default initial values, M1 = M2 = M;
  routeARefined refinedCore (v2_q.refinedCore): the refined claim R (HamFacts by the disc pass, FrameFacts by the C4
                majorants), certified small-divisor constants at the prefix sites (float c_freq x 1.01 here; the
                Lean biteOk / balBound is not mirrored), classical tail.
For each, the largest X* passing okB with tight caps (cap = init + sum, a fixed point, then x (1 + 1e-6)), then the
threshold e* = X* gamma^4 delta0^4 (strict), and the displacement coefficient C/(gamma^2 rho^2) at e*.
Untrusted tooling; exact rationals for every pass/fail decision, floats only to locate X*.
"""
import sys, os, math, json, argparse
from fractions import Fraction as F
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(1, os.path.join(HERE, "..", "apost_sharp"))
import sharp_q as SQ          # noqa: E402
import v2_q as V              # noqa: E402
import smalldiv as SD         # noqa: E402

N_DIM = 2


def package(N=65, rho=F(1, 140), M=F(54, 25), sK=F(1873, 1000), sB=F(2689, 500), sT=F(13, 25), nu=F(1, 10 ** 6),
            s=1 + F(1, 10 ** 6), c=F(2), gden=None, rhoInf=None, mu=F(1, 160)):
    """CertParams in g3_r2.R2's shape; defaults are lunarR2 (KAM/SpinOrbit/LunarParamsR2.lean)."""
    kappa = c / s
    gden = gden or (N + 2)
    rhoInf = rhoInf if rhoInf is not None else rho / 1000
    return dict(tau=1, rho=rho, rhoInf=rhoInf, M=M, sK=sK, sB=sB, sT=sT, mu=mu, gbar=kappa / gden, som=F(2), nu=nu,
                gamma=kappa / gden, s=s, c=c, err=F(0), E0=F(0), disp=F(0), kappa=kappa, N=N)


def nu_minus_one(N, which):
    A = 2 * N - 1
    D = (A * A - 5) / 2
    a = (A - math.sqrt(5)) / D
    return -a if which == "lower" else a


def box_of(p, which):
    """The box of lunarR2Box shape: coordinate 0 about kappa (nu - 1) (radius from the sqrt5 interval), coordinate 1
    exactly (kappa, 0).  Only boxNormUp, freqNormLo (both = kappa) and the clock enter the tests."""
    k = p["kappa"]
    c0 = F(nu_minus_one(p["N"], which)).limit_denominator(10 ** 15) * k
    return [(c0, F(1, 10 ** 9)), (k, F(0))]


# --------------------------------------------------------------------------------------------- caps
def solve_caps(mk, m0, Xs, fixed, iters=60):
    """Tight caps: cap_i = m0_i + sum_i(caps) for the free caps (sB, sT, sLt, sN, sNt, t), by monotone iteration from
    m0; returns the caps x (1 + 1e-6) rounded up, or None if the iteration diverges."""
    free = [2, 3, 4, 5, 6, 7]
    caps = {i: m0[i] * (1 + 1e-9) + 1e-30 if isinstance(m0[i], float) else m0[i] * (1 + F(1, 10 ** 9)) + F(1, 10 ** 30)
            for i in free}
    for _ in range(iters):
        Q = mk(caps)
        sm = Q.sums(Xs)
        new = {i: m0[i] + sm[i] for i in free}
        if any(not (float(new[i]) < 1e6) for i in free):
            return None
        done = all(float(new[i]) <= float(caps[i]) * (1 + 1e-9) for i in free)
        caps = {i: V.up(float(max(new[i], caps[i])) * (1 + 1e-12), 12) for i in free}
        if done:
            break
    return {i: V.up(float(caps[i]) * (1 + 1e-6), 9) for i in free}


def run_witness(branch, p, box, kp, th, J, Xs, R=None, sites=None):
    """The witness (FrozenWit fields, plus R) at X*, with tight caps; None if no caps."""
    n = N_DIM
    d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    dl = lambda s: F(1, 2) ** s * d0
    rr = lambda s: p["rho"] - 6 * d0 * (1 - F(1, 2) ** s)
    bb = lambda s: min(rr(s), F(1))
    if branch == "frozen":
        c = [V.classical_c(n, 1, J, dl(s)) for s in range(kp)]
        cbar = [V.classical_c(n, 1, J, bb(s)) for s in range(kp)]
        m0 = V.defaultInitQ(n, p)
    else:
        c = [sites[("d", s)] for s in range(kp)]
        cbar = [sites[("b", s)] for s in range(kp)]
        m0 = V.initQ(R["bL"], R["bN"], R["bNt"], R["bT"], p["sK"], p["sB"], p["sT"], p["mu"])
    ctail = V.classical_c(n, 1, J, dl(kp))
    base = dict(Xs=Xs, kp=kp, th=th, c=c, cbar=cbar, ctail=ctail, J=J, R=R)

    def mk(caps):
        w = dict(base, sB=caps[2], sT=caps[3], sLt=caps[4], sN=caps[5], sNt=caps[6], t=caps[7])
        return V.frozen_num(w, n, p, box) if branch == "frozen" else V.refined_num(w, n, p, box)
    caps = solve_caps(mk, m0, Xs, None)
    if caps is None:
        return None
    return dict(base, sB=caps[2], sT=caps[3], sLt=caps[4], sN=caps[5], sNt=caps[6], t=caps[7])


def _fl(d):
    return None if d is None else {k: (float(v) if isinstance(v, F) else v) for k, v in d.items()}


def okB_at(branch, p, box, kp, th, J, Xs, R=None, sites=None, detail=False, fl=False):
    """fl: evaluate in floating point (only to locate X*; every reported decision is exact)."""
    if fl:
        p, R, sites, th, Xs = _fl(p), _fl(R), _fl(sites), float(th), float(Xs)
        box = [(float(a), float(b)) for a, b in box]
    w = run_witness(branch, p, box, kp, th, J, Xs, R, sites)
    if w is None:
        return (False, ["caps diverge"], None) if detail else False
    n = N_DIM
    if branch == "frozen":
        Q = V.frozen_num(w, n, p, box)
        m0 = V.defaultInitQ(n, p)
        extra = V.torsionCapOk(Q, p["M"], p["sK"], p["sB"], Xs) and V.classicalListOk(Q, J)
    else:
        Q = V.refined_num(w, n, p, box)
        m0 = V.initQ(R["bL"], R["bN"], R["bNt"], R["bT"], p["sK"], p["sB"], p["sT"], p["mu"])
        extra = V.classicalOk(n, 1, J, Q.delta(kp), Q.ctail)
    ok, why = Q.okB(V.capQ(Q, p["mu"], p["nu"]), m0, Xs, detail=True)
    ok = ok and Q.wfOk() and extra
    if not extra:
        why = why + ["torsion/classical"]
    return (ok, why, w) if detail else ok


def max_Xs(branch, p, box, kp, th, J, R=None, sites=None, lo=-40.0, hi=5.0, steps=34):
    """Largest X* (log10, 3-digit mantissa) with okB; bisection on a monotone test."""
    for _ in range(steps):
        mid = (lo + hi) / 2
        if okB_at(branch, p, box, kp, th, J, V.up(10 ** mid, 3), R, sites, fl=True):
            lo = mid
        else:
            hi = mid
    Xs = F(int(10 ** (lo - math.floor(lo)) * 100), 100) * F(10) ** math.floor(lo)
    while not okB_at(branch, p, box, kp, th, J, Xs, R, sites):
        Xs = Xs * F(99, 100)
    return Xs


def site_constants(p, which, kp, margin=1.01):
    """Certified small-divisor constants at the prefix sites delta_s and b_s (float c_freq x margin)."""
    k = float(p["kappa"])
    om = (k * nu_minus_one(p["N"], which), k)
    gam = float(p["gamma"])
    d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    out = {}
    for s in range(kp):
        d = float(F(1, 2) ** s * d0)
        r = float(min(p["rho"] - 6 * d0 * (1 - F(1, 2) ** s), F(1)))
        out[("d", s)] = V.up(SD.c_freq(om, gam, 1, d)[0] * margin, 4)
        out[("b", s)] = V.up(SD.c_freq(om, gam, 1, r)[0] * margin, 4)
    return out


def lg(x):
    return SQ.lg(F(x)) if x > 0 else float("-inf")


def evaluate(p, which, R, kp_frozen=5, kp_ref=3, th=F(1, 8), J=20, verbose=True):
    box = box_of(p, which)
    n = N_DIM
    out = {}
    # v1 sharp
    r = SQ.sharp(p)
    out["sharp"] = dict(log10_thr=lg(r["threshold"]), log10_disp_coef=lg(r["disp_coef"]), active=r["active"])
    d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    scale = p["gamma"] ** 4 * d0 ** 4
    g2r2 = p["gamma"] ** 2 * p["rho"] ** 2
    for branch, kp in (("frozen", kp_frozen), ("refined", kp_ref)):
        sites = site_constants(p, which, kp) if branch == "refined" else None
        Xs = max_Xs(branch, p, box, kp, th, J, R if branch == "refined" else None, sites)
        ok, why, w = okB_at(branch, p, box, kp, th, J, Xs, R, sites, detail=True)
        _, why_up, _ = okB_at(branch, p, box, kp, th, J, Xs * F(11, 10), R, sites, detail=True)
        Q = V.frozen_num(w, n, p, box) if branch == "frozen" else V.refined_num(w, n, p, box)
        C, c2, c3, C2s, C3s = V.disp_coefs(Q, n, p, Xs, branch == "frozen")
        e = Xs * scale
        out[branch] = dict(kp=kp, Xs=str(Xs), log10_thr=lg(e), log10_disp_coef=lg(C / g2r2),
                           log10_c2Q_coef=lg(c2 / g2r2), log10_c3Q_coef=lg(c3 / g2r2),
                           binding_at_1p1Xs=why_up, caps={k: float(w[k]) for k in ("sB", "sT", "sLt", "sN", "sNt", "t")},
                           c=[float(x) for x in w["c"]], cbar=[float(x) for x in w["cbar"]], ctail=float(w["ctail"]))
        # the exact final test at err just below e*, disp at its minimum (rounded up)
        perr = dict(p, err=V.up(float(e) * 0.999, 6))
        perr["disp"] = V.up(float(C * perr["err"] / g2r2) * 1.001, 3)
        fin = (V.frozenCore if branch == "frozen" else V.refinedCore)(n, perr, box, dict(w), detail=True)
        out[branch]["exact_test_at_0.999e*"] = dict(err=str(perr["err"]), disp=str(perr["disp"]), parts=fin[1],
                                                   passes=fin[0])
        if verbose:
            print(branch, json.dumps(out[branch]["exact_test_at_0.999e*"]["parts"]), flush=True)
    return out


R65 = {  # the refined claim at N = 65 (both tori within 1e-4): Ham sums of the sofx run (checkHamBounds forms) x 1.01,
    # frame sums of v2_frame.py (sampled x 1.01), rounded up
    "lower": dict(dh=F(2099, 1000), dx=F(2020, 1000), d2x=F(1512, 1000), d2h=F(2141, 1000),
                  bL=F(1830, 1000), bN=F(2253, 1000), bNt=F(2291, 1000), bT=F(10393, 1000)),
}
R65["upper"] = dict(R65["lower"])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json")
    ap.add_argument("--kpf", type=int, default=5)
    ap.add_argument("--kpr", type=int, default=3)
    a = ap.parse_args()
    res = {}
    for which in ("lower", "upper"):
        p = package(65)
        res[which] = evaluate(p, which, R65[which], a.kpf, a.kpr)
        o = res[which]
        print("N = 65 %s: sharp %.3f | frozen %.3f (disp coef 10^%.2f) | refined %.3f (disp coef 10^%.2f)" % (
            which, o["sharp"]["log10_thr"], o["frozen"]["log10_thr"], o["frozen"]["log10_disp_coef"],
            o["refined"]["log10_thr"], o["refined"]["log10_disp_coef"]), flush=True)
    if a.json:
        json.dump(res, open(a.json, "w"), indent=1, default=str)


if __name__ == "__main__":
    main()
