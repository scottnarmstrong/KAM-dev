#!/usr/bin/env python3
"""Mirror of the Lean route A constants (KAM/Sharp2/RouteA/Constants.lean, Data.lean; KAM/Iso/Sharp2/RouteA/Scheme.lean).

Untrusted tooling.  Evaluates `routeAOk` of KAM/Sharp2/RouteA/Data.lean literally: stage inputs `NumA.inp`
(prefix: delta_s, c(delta_s), cbar_s (delta_s/r_s)^tau; tail: delta_kp, ctail, ctail), the five `StepInA.Cond`
fields, J2, and the eight sums of J3 with `sumA` (gamma_bar^2 delta_t^(2a-b), twice the tail term).  The threshold is
the largest Xstar with routeAOk, reported as log10 of e* = Xstar gamma^4 delta0^(4 tau).

Compared with `thresholdA` of thresholds_v2.py (the design mirror): the deviations of the Lean statement are
  * the cap of |DK| is sigma_K - mu/2 (the frozen conclusion), not sigma_K;
  * the tail keeps delta_kp in the constants instead of the absorbed gamma_bar^i.
Both only help.

`route_a_ok_ref` evaluates `routeAOkR` and `Ref.Budget` of KAM/Sharp2/RouteA/Ref (lever L8', the torsion against the
initial torus): the conditions without the Neumann condition of <T_bar>, the local bound B_loc x <= b_F with the constant
c_{s+1} at the bite delta_s/2, and the sum of the rates of T_ab plus 2 b_F below beta_T and below the cap of |T|.

Usage:  python3 -I scripts/apost_sharp/route_a_lean_mirror.py
"""
import math, os, sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import thresholds_v2 as T2   # noqa: E402
import dominance as Dom      # noqa: E402
import smalldiv as sd        # noqa: E402
from smalldiv_sum import cohConstR  # noqa: E402


def stage_consts(p):
    iso = p.get("iso", False)
    Th, HY, Mh2 = p.get("Th", 0.0), p.get("HY", 0.0), p.get("Mh2", 0.0)
    n, kap = p["n"], p["kap"]
    d, gb = p["d"], p["gb"]
    sK, sB, sT, sLt, sN, sNt, t = (p[k] for k in ("sK", "sB", "sT", "sLt", "sN", "sNt", "t"))
    M1, M2, c, ca, th = p["M1"], p["M2"], p["c"], p["ca"], p["th"]
    g = gb * d ** kap
    COm = 2 * (n - 1) * c * sLt
    CSym = max(1.0, sB ** 2) * COm
    CRed = n * max(sNt, sLt + 2 * sN)
    w = 2 * M1 * sLt * sK + (2 * n * sK + n * sLt)
    CS = sT * max(sNt * g + t * ca * sLt, g + ca * HY * sLt) if iso else sT * (sNt * g + t * ca * sLt)
    CXiN = CS + c * sLt
    CG = t * CXiN + Th * CS + sNt * g
    CDXi = max(CG, sLt * g)
    CXi = max(c * CG, g * CXiN)
    CDK = sK * c * CG + sN * g * CXiN
    CLin = CRed * CXi + CSym * CDXi + Th * COm * CS
    P = sK + sN
    CDw = Th * g * CS
    CFr = (M1 * sK + n) * (1 + sB) + sN * ((sLt * M1 + 2 * n) * sK + sLt * (M1 * sK + n)) * sB
    CdK = CFr * CXi + P * g * CDXi
    CE1 = 2 * P * (gb ** 2 * d ** (2 * kap - 1)) * CLin + M2 / 2 * CDK ** 2 + (g * CS * CdK if iso else 0.0)
    CE2 = gb * d ** (kap - 1) * n * (sLt * g + Th * COm) * c * CG + Mh2 / 2 * CDK ** 2
    CE = max(CE1, CE2) if iso else CE1
    CGr = n * sLt + 2 * n * sK
    CB = sB ** 2 * CGr / (1 - th)
    CNd = n * sB + sK * CB
    CNtd = CB * sLt + 2 * n * sB
    CDab = 2 * M1 * (CNtd * sN + sNt * CNd) + 2 * M2 * sNt * sN * d
    CDc = sB ** 3 * w * (2 * n * sK + n * sLt)
    CDT0 = (CDab + CDc) * CDK + 2 * n * sNt * sB * (gb ** 2 * d ** (2 * kap)) + 2 * sB ** 3 * w * COm * g
    CDT = max(CDT0 + CDw * d, n * CDw * d + 2 * n * sNt * (gb ** 2 * d ** (2 * kap))) if iso else CDT0
    rT = sT ** 2 / (1 - th) * CDT
    rates = [CDK, n * CDK, CB * CDK, rT, 2 * n * CDK, CNd * CDK, CNtd * CDK, CDT] + ([CDw] if iso else [])
    cond = [(gb ** 4 * d ** (4 * kap - 1), 1.0), (CSym * gb ** 3 * d ** (3 * kap - 1), 0.5), (CE, 1.0),
            (sT * CDT * gb ** 2 * d ** (2 * kap - 1), th), (sB * CGr * CDK * gb ** 2 * d ** (2 * kap - 1), th)]
    rAb = max(CDab * CDK + CDw * d, n * CDw * d) if iso else CDab * CDK

    def bLoc(ch):
        b0 = (n * sNt * sB * gb ** 4 * d ** (4 * kap - 1) +
              2 ** (kap + 1) * sB ** 3 * w * (2 * (n - 1) * ch * sLt) * gb ** 3 * d ** (3 * kap - 1))
        return max(b0, n * sNt * gb ** 4 * d ** (4 * kap)) if iso else b0
    return dict(CE=CE, rates=rates, cond=cond, rAb=rAb, bLoc=bLoc)


JA = [0, 1, 1, 1, 1, 1, 1, 1, 0]


def route_a_ok(N, Xs):
    kap, kp, gb = N["tau"], N["kp"], N["gb"]
    a = 2 * kap
    x = Xs
    nr = len(N["m0"])
    used = [0.0] * nr
    for s in range(kp):
        st = stage_consts(N["inp"](s))
        if any(co * x > bd for co, bd in st["cond"]):
            return False
        dl = N["delta"](s)
        for i in range(nr):
            used[i] += st["rates"][i] * x * (gb ** 2 * dl ** (a - JA[i]))
        x = 2 ** (2 * a) * st["CE"] * x ** 2
        if x > 1e200:
            return False
    st = stage_consts(N["inp"](kp))
    if any(co * x > bd for co, bd in st["cond"]):
        return False
    if 2 ** (2 * a) * st["CE"] * x > 1:
        return False
    dk = N["delta"](kp)
    for i in range(nr):
        used[i] += 2 * st["rates"][i] * x * (gb ** 2 * dk ** (a - JA[i]))
    return all(N["m0"][i] + used[i] <= N["cap"][i] for i in range(nr))


def route_a_ok_ref(N, Xs):
    """`routeAOkR` / `routeAOkRI` and `Ref.Budget` (lever L8').  The caps of T_ab and |T| are replaced by one sum."""
    kap, kp, gb = N["tau"], N["kp"], N["gb"]
    a = 2 * kap
    x = Xs
    nr = len(N["m0"])
    idx = [i for i in range(nr) if i not in (3, 7)]
    used = [0.0] * nr
    ab = bF = 0.0

    def step(s, weight):
        nonlocal ab, bF
        st = stage_consts(N["inp"](s))
        if any(co * x > bd for i, (co, bd) in enumerate(st["cond"]) if i != 3):
            return None
        dl = N["delta"](s)
        for i in idx:
            used[i] += weight * st["rates"][i] * x * (gb ** 2 * dl ** (a - JA[i]))
        ab += weight * st["rAb"] * x * (gb ** 2 * dl ** (a - 1))
        bF = max(bF, st["bLoc"](N["cnext"](s)) * x)
        return st
    for s in range(kp):
        st = step(s, 1.0)
        if st is None:
            return False
        x = 2 ** (2 * a) * st["CE"] * x ** 2
        if x > 1e200:
            return False
    st = step(kp, 2.0)
    if st is None or 2 ** (2 * a) * st["CE"] * x > 1:
        return False
    sT, t = N["cap"][3], N["cap"][7]
    mT, iH = N["m0"][3], N["m0"][7]
    if ab + 2 * bF > min((sT - mT) / (sT * mT), t - iH):
        return False
    return all(N["m0"][i] + used[i] <= N["cap"][i] for i in idx)


def threshold(N, ok=None):
    ok = ok or route_a_ok
    lo, hi = -60.0, 30.0
    for _ in range(70):
        mid = (lo + hi) / 2
        if ok(N, 10 ** mid):
            lo = mid
        else:
            hi = mid
    gam, d0, tau = N["gamma"], N["delta"](0), N["tau"]
    return lo + math.log10(gam ** 4 * d0 ** (4 * tau))


def num_from(D, st, ct, k=5, iso=False):
    """The Lean `NumA` for the design data dict D (after with_caps), with small-divisor data st(s) = (c, ch, cr)."""
    f = float
    mu = f(D["mu"]); rho = f(D["rho"]); rhoinf = f(D["rhoinf"]); tau = f(D["kappa"]); gam = f(D["gamma"])
    gb = f(D["gbar"])
    delta0 = min(1.0, (rho - rhoinf) / 6)
    delta = lambda s: delta0 / 2 ** s
    r = lambda s: rho - 6 * delta0 * (1 - 2.0 ** (-s))
    sK = f(D["sK"]) - mu / 2
    capT = f(D["Tsup_cap"])

    def inp(s):
        if s < k:
            c, _, cr = st(s)
            c, cr = f(c), f(cr)
            ca = cr * (delta(s) / min(r(s), 1.0)) ** tau     # the bite of Lean's `NumA.bbar`
            dd = delta(s)
        else:
            c = ca = f(ct[0] if isinstance(ct, tuple) else ct)   # c_stages: (tail, full-strip tail)
            dd = delta(k)
        return dict(n=D["n"], kap=tau, d=dd, gb=gb, sK=sK, sB=f(D["sB"]), sT=f(D["sT"]), sLt=f(D["sLt"]), sN=f(D["sN"]),
                    sNt=f(D["sNt"]), t=capT, M1=f(D["M1"]), M2=f(D["M2"]), c=c, ca=ca, th=0.125, iso=iso,
                    Th=f(D["Theta_omega"]) if iso else 0.0, HY=f(D["Mh1"]) * f(D["sN"]) if iso else 0.0,
                    Mh2=f(D["Mh2"]) if iso else 0.0)
    m0 = [0.0, f(D["sK"]) - mu, f(D["sB"]) - f(D["bud_B"]), f(D["sT"]) - f(D["bud_Tinv"]), f(D["sLt"]) - f(D["bud_Lt"]),
          f(D["sN"]) - f(D["bud_N"]), f(D["sNt"]) - f(D["bud_Nt"]), capT - f(D["bud_Tsup"])]
    cap = [mu / 2, sK, f(D["sB"]), f(D["sT"]), f(D["sLt"]), f(D["sN"]), f(D["sNt"]), capT]
    if iso:
        m0 = m0 + [0.0]
        cap = cap + [f(D["nu"]) / 2]
    ctail = ct[0] if isinstance(ct, tuple) else ct
    cnext = lambda s: f(st(s + 1)[0]) if s + 1 < k else f(ctail)  # Lean's N.cS (s + 1): the constant at delta_s / 2
    return dict(tau=tau, kp=k, gb=gb, gamma=gam, delta=delta, inp=inp, m0=m0, cap=cap, cnext=cnext)


def main():
    print("| package | small divisors | design mirror (thresholdA, L8') | Lean routeAOk | Lean routeAOkR (L8') | "
          "L8' - design |")
    print("|---|---|---:|---:|---:|---:|")
    F20 = F(1, 20)
    for name, D0 in (("R1", T2.package("R1")), ("H50", T2.package_H50())):
        Dv = T2.with_caps(D0, F20)
        o = dict(L1=True, torsion_cap=Dv["Tsup_cap"], torsion_real=Dv["Tsup_cap"], omega_eta=True, avg_full_bite=True,
                 keep_delta=True, caps_tilde=True, free_budgets=True)
        st, ct = T2.c_stages(Dv, "freq", k=5)
        for iso in (False, True):
            ld = T2.thresholdA(Dv, o, iso, k=5, c_stage=st, c_tail=ct)[0]
            Nv = num_from(Dv, st, ct, iso=iso)
            lL, lR = threshold(Nv), threshold(Nv, route_a_ok_ref)
            print("| %s %s | freq | %.2f | %.2f | %.2f | %+.2f |" % (name, "iso" if iso else "fixed", ld, lL, lR, lR - ld))
    for tag in ("cA-like", "R1-like"):
        D = Dom.plasmalean_data(tag)
        Dv = T2.with_caps(D, F20)
        delta0 = (D["rho"] - D["rhoinf"]) / 6
        om, gam = D["omega_star"], float(D["gamma"])
        cf = sd.c_freq(om, gam, 1, float(delta0))[0]
        cr = sd.c_freq(om, gam, 1, float(D["rho"]))[0]
        st = lambda s, cf=cf, cr=cr: (cf, cf, cr)
        ct = float(T2.Fr(sd.c_classical(2, 1, float(delta0) / 32)))
        o = dict(L1=True, torsion_cap=Dv["Tsup_cap"], torsion_real=Dv["Tsup_cap"], omega_eta=True, avg_full_bite=True,
                 keep_delta=True, caps_tilde=True, free_budgets=True)
        ld = T2.thresholdA(Dv, o, False, k=5, c_stage=st, c_tail=ct)[0]
        Nv = num_from(Dv, st, ct)
        lL, lR = threshold(Nv), threshold(Nv, route_a_ok_ref)
        tol = Dom.PLASMALEAN["log10_tolerance"]
        print("| PlasmaLean %s | freq | %.2f | %.2f | %.2f | %+.2f | (vs its %.2f: %+.2f) |" %
              (tag, ld, lL, lR, lR - ld, tol, lR - tol))


if __name__ == "__main__":
    main()


def torsion_coef(N, D):
    """`torsionCoef` of `Frozen.lean`, the coefficient of X* in `TorsionOk`."""
    n, tau, M, sK, sB = D["n"], N["tau"], float(D["M"]), float(D["sK"]), float(D["sB"])
    cR = cohConstR(n, tau)
    cT1 = 2 * n ** 2 * sK * sB ** 2
    wT = 4 * n * M * sK ** 2 + 2 * n * (n + 1) * sK
    cT2 = 2 ** (tau + 1) * sB ** 3 * wT * (2 * n * (n + 1) * cR * sK)
    gb, d0 = N["gb"], N["delta"](0)
    return cT1 * gb ** 4 * d0 ** (4 * tau - 1) + cT2 * gb ** 3 * d0 ** (3 * tau - 1)


def default_data():
    """`g1_v2A_default` / `iso_g1_v2A_default` on R1: no refined hypothesis.  M1 = M2 = Mh2 = M, the initial values of
    `defaultInit`, H_T = cT0 + 1 for the torsion, classical constants, caps = initial values + 5%.  The threshold is the
    one of `torsionXs`: min(X*, 1/(1 + torsionCoef)) when the torsion smallness binds."""
    print("| default data, R1 | form | classical constants | Lean routeAOk at default data | with torsionXs | v1 |")
    D0 = T2.package("R1")
    n, M, sK, sB, mu = D0["n"], D0["M"], D0["sK"], D0["sB"], D0["mu"]
    D = dict(D0, M1=M, M2=M, Mh1=M, Mh2=M)
    sK1, sB1 = sK - mu, sB - mu
    D.update(sLt=2 * n * sK1 + mu, sN=sK1 * sB1 + mu, sNt=2 * n * sK1 * sB1 + mu,
             Tsup=4 * n * M * sK ** 2 * sB ** 2 + 1)
    for k_, base in (("B", D["sB"]), ("Tinv", D["sT"]), ("Lt", D["sLt"]), ("N", D["sN"]), ("Nt", D["sNt"]),
                     ("Tsup", D["Tsup"])):
        D["bud_" + k_] = base / 10
    Dv = T2.with_caps(D, F(1, 20))
    st, ct = T2.c_stages(Dv, "classical", k=5)
    for iso in (False, True):
        N = num_from(Dv, st, ct, iso=iso)
        lt = threshold(N)
        scale = math.log10(N["gamma"] ** 4 * N["delta"](0) ** (4 * N["tau"]))
        ltors = -math.log10(1 + torsion_coef(N, D)) + scale
        print("| R1 | %s | c_nat | %.2f | %.2f | %s |" % ("iso" if iso else "fixed", lt, min(lt, ltors),
                                                         "-24.98" if iso else "-24.72"))


if __name__ == "__main__":
    default_data()
