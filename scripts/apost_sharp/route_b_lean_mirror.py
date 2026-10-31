#!/usr/bin/env python3
"""SHARP2-B6: exact rational mirror of the Lean route-B predicate `KAM.Sharp2.RouteB.routeBOk`.

Untrusted tooling.  Evaluates, with exact Fractions and no float in the predicate, the declarations of
KAM/Sharp2/RouteB/Data.lean literally:
  * the schedule `bite0R`, `biteSR`, `stripSR` (KAM/Sharp2/EngineRatio.lean), `NumB.bfull`, `NumB.rcf`;
  * the stage inputs `NumB.inp s` (prefix: c(delta_s), c'(split delta_s) rcf, cbar_s (delta_s/bfull_s)^tau, the stage-0
    weights lam0 and ePer0; tail from kp on: ctail, ctail rcf, cbtail (delta_kp/bfull_kp)^tau, the bite delta_kp);
  * every constant of `stepConstsB` through its helper definitions (KAM/Sharp2/ModConstantsB/Data.lean, parsed and
    evaluated by check_modconstb_v2.py; `stepConstsB_eq` is rfl), and the conditions `stepCondB`;
  * `xSeqR`, `NumB.rate`, `NumB.wt`, `NumB.ballSum`, `capB`, `initB`, (J1), (J1t), (J2), (J3) over the seven caps, (J4);
  * `pN`, `c1B`, `c2B`, `NumB.Fits`, `InitB.Wf`, `NumB.Wf`.
The threshold is the largest Xstar with routeBOk, reported as log10 of e* = gamma^4 rho^(4 tau)/c1B (the smallness of
`G1BodyB` is c1B e/(gamma^4 rho^(4 tau)) < 1).  It is compared with `thresholdB` of thresholds_v2.py (the design mirror,
variant B6 of `run_routeB`: L1 data, c_Th, frequency-specific constants, free budgets, anisotropic stage 0).

The numbers N, I come from the design data dict exactly as `thresholdB` builds its stages:
  * N.sK = sigma_K - mu/2 (the frozen conclusion; hypothesis hsK of g1_v2B), the other caps those of `with_caps`;
  * I = the measured initial values (sigma - mu for L^T, N, N^T; `InitB.Wf` needs I < caps strictly, and (J3) needs
    room), so p_bar = max{iNt, iLt/(gbar delta0^tau)} is the design's p_bar divided by 1 + 1/20;
  * lam0, ePer0 are the least values allowed by `NumB.Fits`;
  * ts = the design's torsion slack 1/10; bF (the local torsion budget, a Lean-only free number that no constant uses) is
    max_s B_loc,s X_s at the threshold, which is the design's 2 max_s B_loc,s X_s charged to the Tab sum.
Usage: python3 -I scripts/apost_sharp/route_b_lean_mirror.py
"""
from fractions import Fraction as F
import math, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import thresholds_v2 as T2          # noqa: E402
import check_modconstb_v2 as CM     # noqa: E402  (evaluator of the Lean helper definitions)


def log10(x):
    x = F(x)
    return math.log10(x.numerator) - math.log10(x.denominator)


def ipow(x, e):
    """x ^ e for a real exponent e that is a natural number (tau = 1 here; Real.rpow_natCast)."""
    assert F(e).denominator == 1 and e >= 0, e
    return F(x) ** int(e)


class NumB:
    """The Lean structure `NumB n` (fields of the same names) and its derived definitions."""

    def __init__(self, **kw):
        self.__dict__.update(dict(selfcons=False, lamW0=F(1), iso=False, Θ=F(0), y0=F(0), Mh2=F(0)))
        self.__dict__.update(kw)
        self._k = {}

    # schedule (KAM/Sharp2/EngineRatio.lean)
    def δ0(self):
        return min(F(1), (self.ρ - self.ρinf) * (self.a - 1) / (3 * self.a))

    def δ(self, s):
        return self.δ0() / self.a ** s

    def r(self, s):
        ai = 1 / self.a
        return self.ρ - 3 * self.δ0() * (1 - ai ** s) / (1 - ai)

    def bfull(self, s):
        return min(self.r(s), F(1))

    def split(self):
        return self.τ / (self.τ + 1)

    def rcf(self):
        return ipow(self.τ + 1, self.τ + 1) / ipow(self.τ, self.τ)

    def inp(self, s):
        pre = s < self.kp
        return {"n": self.n, "κ": self.τ, "M1": self.M1, "M2": self.M2, "cTh": self.cTh, "cDTh": self.cDTh,
                "sK": self.sK, "sLt": self.sLt, "sB": self.sB, "sN": self.sN, "sNt": self.sNt, "sT": self.sT,
                "ts": self.ts, "bF": self.bF,
                "c": self.c(s) if pre else self.ctail,
                "c1": (self.c_(s) if pre else self.ctail) * self.rcf(),
                "cavg": (self.cbar(s) * ipow(self.δ(s) / self.bfull(s), self.τ) if pre
                         else self.cbtail * ipow(self.δ(self.kp) / self.bfull(self.kp), self.τ)),
                "θ": self.θ, "θξ": self.θξ, "θΩ": self.θΩ, "q": self.q, "θN": self.θN, "θω": self.θω,
                "a": self.a, "lam": self.lam0 if s == 0 else F(1), "γb": self.γb, "δ": self.δ(min(s, self.kp)),
                "selfcons": self.selfcons, "stage0": s == 0, "ePer": self.ePer0, "iso": self.iso, "Θ": self.Θ,
                "y0": self.y0, "Mh2": self.Mh2, "lamW": self.lamW0 if s == 0 else F(1)}

    def k(self, s):
        """`stepConstsB (N.inp s)` (constants do not depend on bF; s >= kp is the tail record)."""
        s = min(s, self.kp)
        if s not in self._k:
            self._k[s] = CM.consts(self.inp(s))
        return self._k[s]

    def Qs(self, s):
        return self.k(s)["sQ"]

    def xS(self, Xs, upto):
        x = [F(Xs)]
        for s in range(upto):
            x.append(ipow(self.a, self.τ + 1) * self.Qs(s) * x[-1] ** 2)
        return x

    def rate(self, s):
        k = self.k(s)
        return [self.n * k["sCDK"], 2 * self.n * k["sCDK"], k["sCBb"], k["sCNb"], k["sCNbT"], k["sCab"], k["sCnu"]]

    def wt(self, s):
        return [F(1)] * 6 + [self.γb * ipow(self.δ(min(s, self.kp)), self.τ + 1)]

    def ballSum(self, x):
        kp = self.kp
        return (sum(self.k(s)["sCDK"] * self.δ(s) * x[s] for s in range(kp))
                + self.k(kp)["sCDK"] * self.δ(kp) * x[kp] / (1 - self.ybar))

    def cond(self, s, X):
        """`stepCondB (N.inp s) X` as the list of failing clauses (check_modconstb_v2.conds is its transcription)."""
        p = self.inp(s)
        return ["cond%d" % i for i, (co, bd, pw) in enumerate(CM.conds(p, self.k(s))) if co * F(X) ** pw > bd]

    def Bloc(self, s):
        return self.k(s)["sBloc"]


def initB(I, σK, σB, μ):
    return [σK - μ, I["iLt"], σB - μ, I["iN"], I["iNt"], F(0), F(0)]


def capB(N, σT, μ, ν):
    mT = σT - μ
    return [N.sK, N.sLt, N.sB, N.sN, N.sNt, (N.sT - mT) / (N.sT * mT) - 2 * N.bF, ν / 2]


def routeBOk(N, σ, m0, β, Xs):
    """The Lean structure `routeBOk N σ m₀ β Xs`: the list of failing fields (empty iff it holds)."""
    fails = []
    if Xs < 0:
        fails.append("Xs_nonneg")
    kp = N.kp
    x = N.xS(Xs, kp)
    for s in range(kp):                                   # J1
        fails += ["J1 stage%d %s" % (s, c) for c in N.cond(s, x[s])]
    fails += ["J1t %s" % c for c in N.cond(kp, x[kp])]    # J1t: every clause is monotone in X >= 0, so X = X_kp
    if ipow(N.a, N.τ + 1) * N.Qs(kp) * x[kp] > N.ybar:   # J2
        fails.append("J2 tail decay")
    for i in range(7):                                    # J3
        tot = m0[i] + sum(N.rate(s)[i] * N.wt(s)[i] * x[s] for s in range(kp)) \
            + N.rate(kp)[i] * N.wt(kp)[i] * x[kp] / (1 - N.ybar)
        if tot > σ[i]:
            fails.append("J3 cap%d" % i)
    if not N.ballSum(x) < β:                              # J4
        fails.append("J4 ball")
    return fails


def pN(N, I):
    return max(I["iNt"], F(1)) if N.iso else I["iNt"]


def c1B(N, I, Xs):
    return (ipow(N.ρ, 4 * N.τ) * max(I["iLt"] * N.γb ** 2, pN(N, I) * N.γb ** 3 * ipow(N.δ0(), N.τ))
            / (Xs * ipow(N.δ0(), 2 * N.τ + 1)))


def c2B(N, I, Xs):
    return (ipow(N.ρ, 2 * N.τ) * max(I["iLt"], pN(N, I) * N.γb * ipow(N.δ0(), N.τ)) * N.ballSum(N.xS(Xs, N.kp))
            / (Xs * ipow(N.δ0(), 2 * N.τ + 1)))


def pbar(N, I):
    return max(max(I["iNt"], I["iLt"] / (N.γb * ipow(N.δ0(), N.τ))), F(1) if N.iso else F(0))


def wf_fails(N, I, σT, μ):
    """`NumB.Wf`, `InitB.Wf`, `NumB.Fits` (the Boolean parts; the certificate functions are checked on s <= kp)."""
    f = []
    rng = range(N.kp + 1)
    chk = [("two_le", 2 <= N.n), ("τ_ge", 1 <= N.τ), ("ρinf_pos", 0 < N.ρinf), ("ρinf_lt", N.ρinf < N.ρ),
           ("ρ_le", N.ρ <= 1), ("nonneg", min(N.M1, N.M2, N.cTh, N.cDTh, N.Θ, N.y0, N.Mh2, N.ePer0) >= 0),
           ("caps", min(N.sK, N.sLt, N.sB, N.sN, N.sNt, N.sT) > 0), ("budgets", N.ts > 0 and N.bF > 0),
           ("ratios", all(0 < t < 1 for t in (N.θ, N.θξ, N.θΩ, N.q, N.θN, N.θω))), ("a_gt", 1 < N.a),
           ("ybar", 0 < N.ybar < 1), ("kp_pos", 1 <= N.kp),
           ("lam", 0 < N.lam0 <= 1 and 0 < N.lamW0 <= 1), ("γb", 0 < N.γb),
           ("sd", all(N.c(s) > 0 and N.c_(s) > 0 and N.cbar(s) > 0 for s in rng) and N.ctail > 0 and N.cbtail > 0),
           ("I.pos", min(I["iLt"], I["iN"], I["iNt"]) > 0),
           ("I.lt", I["iLt"] < N.sLt and I["iN"] < N.sN and I["iNt"] < N.sNt),
           ("I.torsion", 0 < σT - μ < N.sT),
           ("Fits.lam0", I["iNt"] / pbar(N, I) <= N.lam0),
           ("Fits.lamW0", (not N.iso) or 1 / max(max(I["iNt"], I["iLt"] / (N.γb * ipow(N.δ0(), N.τ))), F(1)) <= N.lamW0),
           ("Fits.ePer0", 1 / pbar(N, I) <= N.ePer0)]
    return [nm for nm, ok in chk if not ok]


def from_design(D, st, ct, k=5, theta=F(1, 16)):
    """`NumB`, `InitB`, the frozen sigma's for the design package D (before `with_caps`), variant B6, fixed frequency."""
    mu = D["mu"]
    Dv = T2.with_caps(D, F(1, 20))
    I = {"iLt": D["sLt"] - mu, "iN": D["sN"] - mu, "iNt": D["sNt"] - mu}
    N = NumB(n=D["n"], τ=F(D["tau"]), ρ=D["rho"], ρinf=D["rhoinf"], γb=D["gbar"], M1=D["M1"], M2=D["M2"],
             cTh=D["cTh"], cDTh=2 * D["M2"], sK=D["sK"] - mu / 2, sLt=Dv["sLt"], sB=Dv["sB"], sN=Dv["sN"],
             sNt=Dv["sNt"], sT=Dv["sT"], ts=F(1, 10), bF=F(1), θ=theta, θξ=F(1, 8), θΩ=F(1, 8), q=F(1, 8),
             θN=F(1, 8), θω=F(1, 8), a=F(2), ybar=F(1, 2), kp=k,
             c=lambda s: st(s)[0], c_=lambda s: st(s)[1], cbar=lambda s: st(s)[2], ctail=ct[0], cbtail=ct[1],
             lam0=F(1), ePer0=F(0))
    assert F(D["tau"]) == 1 and D["gamma"] == D["gbar"]
    pb = pbar(N, I)
    N.lam0 = I["iNt"] / pb                                   # least values allowed by NumB.Fits
    N.ePer0 = 1 / pb
    sig = dict(σK=D["sK"], σB=D["sB"], σT=D["sT"], μ=mu)
    return N, I, sig, Dv


def ok_at(N, I, sig, Xs):
    """routeBOk at Xs, with bF = max_s B_loc,s X_s (the least local budget that J1, J1t allow)."""
    x = N.xS(Xs, N.kp)
    N.bF = max(max(N.Bloc(s) * x[s] for s in range(N.kp + 1)), F(1, 10 ** 30))
    σ = capB(N, sig["σT"], sig["μ"], F(0))
    m0 = initB(I, sig["σK"], sig["σB"], sig["μ"])
    return routeBOk(N, σ, m0, sig["μ"] / 2, F(Xs))


def threshold(N, I, sig, iters=60):
    """Largest Xs with routeBOk (bisection in log scale; every bisection point is an exact rational)."""
    lo, hi = -40.0, 10.0
    for _ in range(iters):
        mid = (lo + hi) / 2
        if ok_at(N, I, sig, F(10 ** mid).limit_denominator(10 ** 40)):   # a failing field
            hi = mid
        else:
            lo = mid
    return lo


def short_rational_below(N, I, sig, lx, digits=4):
    """A short rational Xs <= 10^lx (digits significant digits) at which routeBOk holds exactly."""
    e = math.floor(lx) - digits + 1
    m = int(10 ** (lx - e))
    for _ in range(10):
        Xs = F(m) * F(10) ** e
        fl = ok_at(N, I, sig, Xs)
        if not fl:
            return Xs, fl
        m -= 1
    return Xs, fl


def main():
    print("| package | design thresholdB (B6) | Lean routeBOk: log10 X* | log10 e* = gamma^4 rho^4/c1B | Lean - design |"
          " certificate X* (exact check) | bF | binding just above |")
    print("|---|---:|---:|---:|---:|---|---:|---|")
    worst = 0
    for name, D in (("R1", T2.package("R1")), ("H50", T2.package_H50())):
        Dv = T2.with_caps(D, F(1, 20))
        o = dict(keep_delta=True, avg_full_bite=True, theta=F(1, 16), selfcons=False, L1=True, cTh=D["cTh"],
                 free_budgets=True, aniso=True)
        st, ct = T2.c_stages(Dv, "freq", 5)
        ld, _, _ = T2.thresholdB(Dv, o, False, 5, st, ct)
        N, I, sig, _ = from_design(D, st, ct, 5)
        lx = threshold(N, I, sig)
        Xs, fl = short_rational_below(N, I, sig, lx)
        assert fl == [], fl
        wf = wf_fails(N, I, sig["σT"], sig["μ"])
        assert wf == [], wf
        bF = N.bF
        c1 = c1B(N, I, Xs)
        le = log10(D["gamma"] ** 4 * ipow(N.ρ, 4 * N.τ) / c1)
        above = ok_at(N, I, sig, F(10 ** (lx + 0.01)).limit_denominator(10 ** 40))
        c2 = c2B(N, I, Xs)
        print("| %s fixed | %.3f | %.3f | %.3f | %+.3f | %s | %.3g | %s |" % (
            name, ld, lx, le, le - ld, Xs, float(bF), ", ".join(above)))
        print("|   (c1B = %.6g, c2B = %.6g, delta0 = %s, lam0 = %.6g, ePer0 = %.6g) | | | | | | | |" % (
            float(c1), float(c2), N.δ0(), float(N.lam0), float(N.ePer0)))
        worst = max(worst, abs(le - ld))
    # cross-check of the stage constants against stageB at the same inputs (prefix and tail of R1, variant B6)
    D = T2.package("R1")
    Dv = T2.with_caps(D, F(1, 20))
    st, ct = T2.c_stages(Dv, "freq", 5)
    N, I, sig, _ = from_design(D, st, ct, 5)
    o = dict(keep_delta=True, avg_full_bite=True, theta=F(1, 16), selfcons=False, L1=True, cTh=D["cTh"],
             free_budgets=True, aniso=True)
    gd0 = D["gamma"] * N.δ0()
    pb_design = max(Dv["sNt"], Dv["sLt"] / gd0)
    diffs = 0
    for s in range(N.kp + 1):
        if s < N.kp:
            c, ch, cr = st(s)
            lamL = min(F(1), Dv["sNt"] / pb_design) if s == 0 else F(1)
            so = dict(e_over_mu=1 / pb_design) if s == 0 else None
            py = T2.stageB(Dv, o, N.δ(s), N.r(s), c, ch * 4, cr, False, stage0=so, lamL=lamL)
        else:
            py = T2.stageB(Dv, dict(o, avg_full_bite=True), N.δ(s), N.r(s), ct[0], ct[0] * 4, ct[1], False)
        k = N.k(s)
        pairs = [("sQ", py["Q"]), ("sCDK", py["C_DK"]), ("sBloc", py["B_loc"]), ("sCBb", py["rates"]["B"][0]),
                 ("sCNb", py["rates"]["N"][0]), ("sCNbT", py["rates"]["Nt"][0]), ("sCab", py["rates"]["Tab"][0])]
        rel = [(nm, float(k[nm] / v - 1)) for nm, v in pairs]
        bad = [(nm, r) for nm, r in rel if (s > 0 and r != 0) or abs(r) > F(1, 10)]
        diffs += len(bad)
        print("stage %d: Lean/stageB - 1 = %s%s" % (s, ", ".join("%s %.2e" % t for t in rel),
                                                   "" if not bad else "   UNEXPECTED"))
    print("stage constants: %s (stage 0 differs only through ePer0 = 1.05/p_bar_design and the measured I)"
          % ("equal on stages >= 1" if diffs == 0 else "MISMATCH"))
    print("max |Lean - design| in log10 e*: %.3f" % worst)
    return 0 if diffs == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
