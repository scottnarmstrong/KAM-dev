#!/usr/bin/env python3
"""Fair dominance check of the v2 design against the explicit a-posteriori KAM theorems for flows (APOST-SHARP-V2.md,
section 5 and section 11).

Untrusted tooling (design numbers).  On a grid of generic data compare the threshold (largest admissible invariance
error e) of
  v2       the better of route A (additive, v1 + levers) and route B (modified step) of thresholds_v2.py, using ONLY
           the information the competitors use (one size M = sigma's, sigma_K^T = 2n sigma_K, sigma_N = sigma_K sigma_B,
           sigma_N^T = 2n sigma_K sigma_B, derived torsion, the classical small-divisor constant, no measured objects);
  HL19     Haro-Luque 2019 Theorem 3.1 (benchmark_hl19.py), a1 optimised;
  FH24     Figueras-Haro 2024 Theorem 2.18 (benchmark_fh24.py), delta, nu and the two control constants optimised,
           with erratum E2 corrected (the printed (3.72) is not a valid bound in general); the printed version is
           reported for information.
FAIR DATA (audit AUDIT-SHARP-V2-fixed-1 F7): every competitor receives its best legally available small-divisor data,
the classical constant c^natural(n, tau, b) of blueprint bp:p2s2sd:classical at its OWN bites:
  FH24     c_R = c^nat(delta) at its optimised initial bite delta (FH24 App. B allows c_R(delta) or uniform bounds; its
           later bites are smaller and c^nat is nondecreasing, so c^nat(delta) is a uniform bound for every step),
           c^1_R = (tau+1)^{tau+1}/tau^tau c^nat(tau/(tau+1) delta) (Corollary 2.16 (2.22) at its split bite, uniform over
           the later bites since c^nat is nondecreasing; AUDIT-SHARP2-FIX-fixed-1 F2), and
           c_R(rho) = c^nat(rho) for its full-strip average (3.45) (a small-bite constant does not certify the bite rho);
  HL19     c_R = c^nat(delta_0) at its initial bite delta_0 = rho/a_3(a_1) (Lemma 4.1 allows c_R(delta); HL19 5.3 takes
           the constants at delta_0, which is legal here because c^nat is nondecreasing: the uniformity caveat of HL19
           5.3 concerns non-monotone c(delta) only).
v2 gets c^nat at its stage bites delta_s, delta_s/2, r_s and c^nat(delta_k) for the tail (every later bite).  The
like-for-like margin reading ("normalised": sigma - mu/2, so that the competitor's conclusion implies the frozen one).
A competitor "wins" at a point if its threshold exceeds v2's by more than 0.005 orders.

Usage:  python3 -I scripts/apost_sharp/dominance.py [--quick] [--grid old|ext] [--jobs J] [--json OUT]
        python3 -I scripts/apost_sharp/dominance.py --point n tau gamma rho size     (one point, with diagnosis)
        --ablate: v2 without the levers of the fair comparison (split 1/2, ratio 2, decay 1/2, no L10)
        python3 -I scripts/apost_sharp/dominance.py --plasmalean [--json OUT]   # PlasmaLean, incl. B10 l^1 entry step
"""
from fractions import Fraction as F
import json, math, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import thresholds as v1          # noqa: E402
import thresholds_v2 as T2       # noqa: E402
import benchmark_hl19 as HL      # noqa: E402
import benchmark_fh24 as FH      # noqa: E402
import smalldiv as sd            # noqa: E402

lg = v1.lg


def grid_data(n, tau, gamma, rho, size, mu=F(1, 16)):
    s = F(size)
    return dict(n=n, tau=tau, kappa=tau, rho=F(rho), rhoinf=F(rho) / 1000, gamma=F(gamma), gbar=F(gamma), mu=mu,
                nu=F(1, 10 ** 6), M=s, sK=s, sB=s, sT=s,
                M0=s, M1=s, M2=s, Mh1=s, Mh2=s, sLt=2 * n * s, sN=s * s, sNt=2 * n * s * s,
                Tsup=4 * n * s ** 5 + 1, Theta_omega=2 * n * s * s * (s + 1), omega_star=None)


_CNAT = {}


def c_nat(n, tau, b, exact=True):
    """c^natural(n, tau, b) (rational upper bound if exact)."""
    key = (n, tau, float(b))
    if key not in _CNAT:
        x = sd.c_classical(n, tau, float(b))
        _CNAT[key] = (x, v1.up(x))
    return _CNAT[key][1] if exact else _CNAT[key][0]


RATIOS = ((F(2), 5), (F(3, 2), 9), (F(13, 10), 13), (F(6, 5), 19), (F(23, 20), 25))


def v2_same_data(D, thetas=(F(1, 16), F(1, 8)), kpre=5, ratios=RATIOS, ymaxs=(F(1, 2), F(9, 10)), scs=(False, True)):
    """v2 with the competitors' information only (levers that need no extra data).  Route B is evaluated over the free
    parameters (Neumann ratio theta, schedule ratio a with its prefix length) in floating point (design numbers);
    route A is the v1-schedule scheme (ratio 2) in exact arithmetic."""
    n, tau = D["n"], int(D["tau"])
    c_cl = lambda d: c_nat(n, tau, d)
    lam = 3
    delta0 = min(F(1), (D["rho"] - D["rhoinf"]) / (2 * lam))

    def st(s):
        ds = delta0 / 2 ** s
        r = D["rho"] - 2 * lam * delta0 * (1 - F(1, 2 ** s))
        return c_cl(ds), c_cl(ds / 2), c_cl(min(r, F(1)))
    ct = c_cl(delta0 / 2 ** kpre)                   # tail: a constant valid at every bite <= delta_k (c^nat monotone)
    oA = dict(omega_eta=True, avg_full_bite=True, keep_delta=True, caps_tilde=True)
    lA, _, wA = T2.thresholdA(D, oA, False, k=kpre, c_stage=st, c_tail=ct)
    Df = {k_: (float(v) if isinstance(v, F) else v) for k_, v in D.items()}
    cf = lambda d: c_nat(n, tau, d, exact=False)
    sp = tau / (tau + 1)                            # optimal Russmann-Cauchy split (the second constant is at s delta)
    if ABLATE:                                      # the design before the fair comparison: s = 1/2, a = 2, ybar = 1/2, no L10
        sp, ratios, ymaxs, scs = 0.5, ((F(2), 5),), (F(1, 2),), (False,)
    stf = lambda ds, r: (cf(ds), cf(sp * ds), cf(min(r, 1.0)))
    stf.by_bite = True
    lB, wB, parB = -1e9, None, None
    for a, k in ratios:                             # the schedule ratio a and the prefix length are free parameters
        d0 = min(1.0, (Df["rho"] - Df["rhoinf"]) * float(a - 1) / (3 * float(a)))
        rk = Df["rho"] - 3 * d0 * (1 - float(a) ** -k) / (1 - 1 / float(a))
        ctf = (cf(d0 / float(a) ** k), cf(min(rk, 1.0)))   # tail: bite delta_k; full strips r_j <= r_k (F9)
        for th in thetas:                           # the Neumann ratio is a free parameter of the design
            for ym in ymaxs:                        # the tail decay bound (J2) is a free parameter
                for sc in scs:                      # the self-consistent tangential error is optional (its conditions)
                    oB = dict(L1=False, keep_delta=True, avg_full_bite=True, aniso=True, theta=th, ratio=a, split=sp,
                              ymax=ym, selfcons=sc)
                    r = T2.thresholdB(Df, oB, False, k, stf, ctf)
                    if r[0] > lB:
                        lB, wB, parB = r[0], r[2], dict(ratio=float(a), kpre=k, theta=float(th), ymax=float(ym),
                                                        selfcons=sc)
    return max(lA, lB), ("A" if lA >= lB else "B"), lA, lB, wA, wB, parB


def comp_data_hl(D):
    n = D["n"]; s = D["sK"]; mu = D["mu"]; sh = mu / 2
    return dict(n=n, tau=D["tau"], rho=D["rho"], rhoinf=D["rhoinf"], gamma=D["gamma"], cX0=D["M"], cX1=D["M"],
                cX2=D["M"], cXT1=D["M"], sK=D["sK"] - sh, sKT=2 * n * D["sK"] - sh, sB=D["sB"] - sh,
                sT=D["sT"] - sh, DK=D["sK"] - mu, DKT=2 * n * (D["sK"] - mu), Bact=D["sB"] - mu, Tinv=D["sT"] - mu,
                dist=mu - sh)


def comp_data_fh(D):
    n = D["n"]; mu = D["mu"]; sh = mu / 2
    sK, sB = D["sK"], D["sB"]
    return dict(n=n, tau=D["tau"], rho=D["rho"], rhoinf=D["rhoinf"], gamma=D["gamma"],
                c_Xh=D["M"], c_DXh=D["M"], c_DXhT=D["M"], c_D2Xh=D["M"], c_Th=2 * D["M"], c_DTh=2 * D["M"],
                s_DK=sK - sh, s_DKT=2 * n * sK - sh, s_B=sB - sh, s_N=sK * sB - sh, s_NT=2 * n * sK * sB - sh,
                s_Tinv=D["sT"] - sh, DK=sK - mu, DKT=2 * n * (sK - mu), B=sB - mu, N=(sK - mu) * (sB - mu),
                NT=2 * n * (sK - mu) * (sB - mu), Tinv=D["sT"] - mu, dist=mu - sh)


def best_fh24_fair(d, errata=True):
    """FH24 with c_R = c^nat(delta) at its own bite (the search of benchmark_fh24.best_fh24 with a bite-dependent
    constant): delta = t (rho - rho_inf)/3, kappa on k/40, nu and varkappa on m 10^-j, then local refinement."""
    n, tau = int(d["n"]), int(d["tau"])
    fac = F(tau + 1) ** (tau + 1) / F(tau) ** tau
    Dr = (F(d["rho"]) - F(d["rhoinf"])) / 3
    dd = dict(d, cRrho=c_nat(n, tau, min(F(d["rho"]), F(1))))
    ddf = dict(dd, cRrho=float(dd["cRrho"]))

    spl = F(tau, tau + 1)                           # FH24 Cor. 2.16 (2.22): c^1_R from the split bite tau/(tau+1) delta

    def obj(p):
        c = c_nat(n, tau, p[0] * Dr, exact=False)
        c1 = float(fac) * c_nat(n, tau, spl * p[0] * Dr, exact=False)
        try:
            return FH.fh24(ddf, c, c1, p[0] * Dr, p[1], p[2], p[3], exact=False, errata=errata)["threshold_e"]
        except (AssertionError, ZeroDivisionError, OverflowError):
            return 0.0
    logg = sorted({F(m, 10 ** j) for j in range(1, 25) for m in (1, 2, 5)} | {F(1, 2), F(1, 5)})

    def descend(p, grids, best):
        for _ in range(4):
            moved = False
            for i, gr in enumerate(grids):
                for x in gr:
                    q = list(p); q[i] = x
                    val = obj(q)
                    if val > best:
                        best, p, moved = val, q, True
            if not moved:
                break
        return p, best
    tk = FH._grid_t(F(0), F(1), 40)
    p = [F(1, 2), F(1, 10 ** 6), F(1, 10 ** 6), F(1, 2)]
    p, best = descend(p, [[F(1, 2)], logg, logg, [F(1, 2)]], obj(p))
    for t0 in tk:
        for k0 in tk:
            q = [t0, p[1], p[2], k0]
            val = obj(q)
            if val > best:
                p, best = q, val
    p, best = descend(p, [tk, logg, logg, tk], best)
    for step in (F(1, 200), F(1, 800), F(1, 3200)):
        for _ in range(3):
            p0 = p
            for tj in [p0[0] + j * step for j in range(-8, 9) if 0 < p0[0] + j * step < 1]:
                for kj in [p0[3] + j * step for j in range(-8, 9) if 0 < p0[3] + j * step < 1]:
                    q = [tj, p0[1], p0[2], kj]
                    val = obj(q)
                    if val > best:
                        p, best = q, val
            p, best = descend(p, [[p[0]], logg, logg, [p[3]]], best)
            if p == p0:
                break
    c = c_nat(n, tau, p[0] * Dr)
    c1 = fac * c_nat(n, tau, spl * p[0] * Dr)       # sharper legal c^1_R (AUDIT-SHARP2-FIX-fixed-1, F2)
    r = FH.fh24(dd, c, c1, p[0] * Dr, p[1], p[2], p[3], exact=True, errata=errata)
    r["t"] = p[0]; r["cR"] = c; r["cR1"] = c1
    return r


def hl19_scan(d, grid=None, iso=False):
    """HL19 (Thm 3.1, or Thm 3.6 if iso) with c_R = c^nat(delta_0(a_1)) at its initial bite, for every a_1 of the grid
    (nu_HL self-consistent): the list of admissible results (each a valid instance of the theorem)."""
    n, tau = int(d["n"]), int(d["tau"])
    grid = grid or [F(k, 100) for k in range(105, 401, 5)] + [F(k, 10) for k in range(45, 101, 5)]
    rho, a2 = F(d["rho"]), F(d["rho"]) / F(d["rhoinf"])
    out = []
    for a1 in grid:
        a3 = 3 * a1 / (a1 - 1) * a2 / (a2 - 1)
        c = c_nat(n, tau, min(rho / a3, F(1)))
        nu = F(1, 10 ** 6)
        try:
            for _ in range(3):
                r = HL.hl19(d, c, a1, nu, iso)
                nu = r["threshold"] / r["delta0"] * (1 + F(1, 10 ** 9))
            r = HL.hl19(d, c, a1, nu, iso)
        except (AssertionError, ZeroDivisionError):
            continue
        if r["threshold"] <= 0 or r["threshold"] >= r["delta0"] * nu:
            continue
        r["a1"] = a1; r["cR"] = c
        out.append(r)
    return out


def best_hl19_fair(d, grid=None, iso=False):
    """HL19 with c_R = c^nat(delta_0(a_1)) at its initial bite, a_1 optimised (nu_HL self-consistent)."""
    sc = hl19_scan(d, grid, iso)
    return max(sc, key=lambda r: r["threshold"]) if sc else None


def compare(D):
    n, tau = D["n"], int(D["tau"])
    lv2, route, lA, lB, wA, wB, parB = v2_same_data(D)
    hl = best_hl19_fair(comp_data_hl(D))
    fhc = best_fh24_fair(comp_data_fh(D), errata=True)
    fhp = best_fh24_fair(comp_data_fh(D), errata=False)
    return dict(v2=lv2, route=route, A=lA, B=lB, HL19=lg(hl["threshold"]) if hl else -1e9,
                FH24=lg(fhp["threshold_e"]), FH24_corr=lg(fhc["threshold_e"]),
                FH24_delta=float(fhc["delta"]), FH24_cR=float(fhc["cR"]), FH24_binding=str(fhc.get("active", "")),
                v2_binding=", ".join(wB if route == "B" else wA), v2_B_params=parB)


def _point(args):
    n, tau, g, r, s = args
    D = grid_data(n, tau, g, r, s)
    try:
        res = compare(D)
    except (AssertionError, T2.IllegalData) as ex:
        return dict(n=n, tau=tau, gamma=float(g), rho=float(r), size=s, skipped=str(ex))
    best_comp = max(res["HL19"], res["FH24_corr"])
    return dict(n=n, tau=tau, gamma=float(g), rho=float(r), size=s, **res, margin=res["v2"] - best_comp)


ABLATE = "--ablate" in sys.argv

GRID_OLD = dict(ns=[(2, 1), (2, 2), (3, 2), (4, 3)], gammas=[F(1, 1000), F(1, 100), F(1, 10)],
                rhos=[F(1, 1000), F(1, 100), F(1, 10)], sizes=[1, 3, 10])
GRID_EXT = dict(ns=[(2, 1), (2, 2), (2, 3), (3, 2), (3, 3), (4, 3), (4, 4), (5, 4), (6, 5)],
                gammas=[F(1, 10 ** 6), F(1, 10 ** 4), F(1, 1000), F(1, 100), F(1, 10)],
                rhos=[F(1, 1000), F(1, 100), F(1, 10), F(3, 10)], sizes=[1, 3, 10, 30])


def main():
    quick = "--quick" in sys.argv
    gname = sys.argv[sys.argv.index("--grid") + 1] if "--grid" in sys.argv else "old"
    G = dict(GRID_EXT if gname == "ext" else GRID_OLD)
    if quick:
        G = dict(ns=[(2, 1), (4, 3)], gammas=[F(1, 1000)], rhos=[F(1, 10)], sizes=[1, 10])
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 1
    pts_in = [(n, tau, g, r, s) for (n, tau) in G["ns"] for g in G["gammas"] for r in G["rhos"] for s in G["sizes"]]
    t0 = time.time()
    if jobs > 1:
        import multiprocessing as mpr
        with mpr.Pool(jobs) as pool:
            rows = pool.map(_point, pts_in, chunksize=1)
    else:
        rows = [_point(a) for a in pts_in]
    print("| n | tau | gamma | rho | size | v2 (route) | HL19 | FH24 printed | FH24 corrected | margin | v2 binding |")
    print("|---|---|---|---|---|---:|---:|---:|---:|---:|---|")
    pts, wins, skipped = [], [], []
    for row in rows:
        if "skipped" in row:
            skipped.append(row)
            print("| %d | %d | %g | %g | %d | skipped (%s) |" % (row["n"], row["tau"], row["gamma"], row["rho"],
                                                                  row["size"], row["skipped"]))
            continue
        pts.append(row)
        flag = ""
        if row["HL19"] > row["v2"] + 0.005 or row["FH24_corr"] > row["v2"] + 0.005:
            wins.append(row); flag = " **competitor wins**"
        print("| %d | %d | %g | %g | %d | %.2f (%s) | %.2f | %.2f | %.2f | %+.2f%s | %s |" % (
            row["n"], row["tau"], row["gamma"], row["rho"], row["size"], row["v2"], row["route"], row["HL19"],
            row["FH24"], row["FH24_corr"], row["margin"], flag, row["v2_binding"]))
    print()
    print("grid %s: points %d (skipped %d), corrected-competitor wins: %d, printed-FH24 wins: %d, time %.0f s" % (
        gname, len(pts), len(skipped), len(wins), sum(1 for p in pts if p["FH24"] > p["v2"] + 0.005),
        time.time() - t0))
    if pts:
        mg = sorted(p["margin"] for p in pts)
        print("margin v2 - best fair competitor: min %.3f, median %.3f, max %.3f orders" % (mg[0], mg[len(mg) // 2],
                                                                                           mg[-1]))
        worst = min(pts, key=lambda p: p["margin"])
        print("worst point:", {k: worst[k] for k in ("n", "tau", "gamma", "rho", "size", "v2", "route", "FH24_corr",
                                                     "HL19", "margin")})
    if "--json" in sys.argv:
        json.dump(dict(points=pts, wins=wins, skipped=skipped), open(sys.argv[sys.argv.index("--json") + 1], "w"),
                  indent=1, default=str)


def point_main():
    i = sys.argv.index("--point")
    n, tau = int(sys.argv[i + 1]), int(sys.argv[i + 2])
    g, r, s = F(sys.argv[i + 3]), F(sys.argv[i + 4]), int(sys.argv[i + 5])
    row = _point((n, tau, g, r, s))
    print(json.dumps(row, indent=1, default=str))


if __name__ == "__main__" and "--point" in sys.argv:
    point_main()
elif __name__ == "__main__" and "--plasmalean" not in sys.argv and "--fh25" not in sys.argv and \
        "--closeness" not in sys.argv:
    main()


# ---------------------------------------------------------------------------------------------------------------
# PlasmaLean's example (owner directive 3).  PlasmaLean (github.com/siddhartha-gadgil/PlasmaLean, KamTorusAExact.lean,
# notes/theory/after-kam.md, as summarised in docs/explorations/striking-applications.md section 8 on branch apps-scout):
# field-line flow of a divergence-free field on T^2 (1 1/2 degrees of freedom), Newton in weighted l^1 coefficient norms,
# 2 unknown functions; proved tolerance delta0^4/(32 kappa) = 5.7e-19 at gamma = 0.0687, strip 0.1257 rad (rho = 0.02
# turns), delta0 = r/7.  Not like for like: our theorem is for canonical Hamiltonian flows (n = 2 with the clock
# frequency omega = (iota, 1)), sup norms on a 2n-dimensional phase space; the exact field of PlasmaLean has a
# non-canonical area form and no closed-form canonical chart.  What is compared: our threshold on e (sup norm of the
# invariance error) at PlasmaLean's gamma, strip and frame/torsion bounds (two norm guesses of run_mag.py), against its
# proved tolerance on its own error norm.
# ---------------------------------------------------------------------------------------------------------------

PLASMALEAN = dict(log10_tolerance=math.log10(5.7e-19), gamma=0.0687, rho_rad=0.1257, iota=(75 + math.sqrt(5)) / 562)


def plasmalean_data(tag):
    sK, sB, M, T = {"cA-like": (3.1, 2.0, 3.0, 19.84), "R1-like": (1.37, 1.93, 1.9, 3.3)}[tag]
    mu = F(1, 160)
    sK, sB, M = F(str(sK)), F(str(sB)), F(str(M))
    D = grid_data(2, 1, F(687, 10000), v1.up(0.1257 / (2 * math.pi)), 1)
    D.update(M=M, M0=M, M1=M, M2=M, Mh1=M, Mh2=M, sK=sK, sB=sB, sT=1 / F(22, 100) + mu, mu=mu,
             sLt=2 * 2 * sK, sN=sK * sB, sNt=2 * 2 * sK * sB, Tsup=F(str(T)), cTh=2 * M,
             omega_star=(PLASMALEAN["iota"], 1.0))
    for k_, base in (("B", D["sB"]), ("Tinv", D["sT"]), ("Lt", D["sLt"]), ("N", D["sN"]), ("Nt", D["sNt"]),
                     ("Tsup", D["Tsup"])):
        D["bud_" + k_] = base / 10
    # floating point (as for FH25): exact rationals make the 5-stage bisection very slow here
    return {k: (float(v) if isinstance(v, F) else v) for k, v in D.items()}


def plasmalean():
    print("PlasmaLean's example: its proved tolerance 10^%.2f (l^1 norms, its own theorem)." % PLASMALEAN["log10_tolerance"])
    print("| norms | small divisors | v2 route A | v2 route B | best | vs PlasmaLean |")
    print("|---|---|---:|---:|---:|---:|")
    rows = []
    for tag in ("cA-like", "R1-like"):
        D = plasmalean_data(tag)
        lam = 3
        delta0 = (D["rho"] - D["rhoinf"]) / (2 * lam)
        om = D["omega_star"]; gam = float(D["gamma"])
        for which in ("classical", "freq", "l1-freq (L9)"):
            if which == "classical":
                st, ct = T2.c_stages(D, "classical")
                pen = 0.0
            elif which == "freq":                       # flat in delta (as measured for R1/H50): the value at delta0
                cf = sd.c_freq(om, gam, 1, float(delta0))[0]
                cr_ = sd.c_freq(om, gam, 1, float(D["rho"]))[0]
                st = lambda s, cf=cf, cr_=cr_: (cf, cf, cr_)
                rk = float(D["rho"]) - 6 * float(delta0) * (1 - 2 ** -5)
                ct = (float(T2.Fr(sd.c_classical(2, 1, float(delta0) / 32))),   # tail: every bite <= delta_k, and
                      float(T2.Fr(sd.c_classical(2, 1, min(rk, 1.0)))))          # every full bite r_j <= r_k (F9)
                pen = 0.0
            else:                                       # L9: SHARP-L9's certified c_inf = Gamma_inf gamma delta^tau, flat
                cinf = 0.00123                          # (docs/campaign/handoffs/SHARP-L9.md, PlasmaLean's frequency)
                st = lambda s, cinf=cinf: (cinf, cinf, cinf)
                ct = sd.c_inf_classical(1)
                pen = math.log10(3.6)                  # l^1/sup of E (CERTIFIER-SHARPNESS 1.2, worst R1 value)
            oA = dict(L1=True, torsion_cap=D["Tsup"], torsion_real=D["Tsup"], omega_eta=True, avg_full_bite=True,
                      keep_delta=True, caps_tilde=True, free_budgets=True)
            Dv = T2.with_caps(D, F(1, 20))
            oA["torsion_cap"] = Dv["Tsup_cap"]; oA["torsion_real"] = Dv["Tsup_cap"]
            lA = T2.thresholdA(Dv, oA, False, k=5, c_stage=st, c_tail=ct)[0] - pen
            lB = -1e9
            for th in (F(1, 16), F(1, 8)):
                for sc in (False, True):                # option L10 is a free choice of the theorem
                    oB = dict(L1=True, keep_delta=True, avg_full_bite=True, aniso=True, theta=th, cTh=Dv["cTh"],
                              free_budgets=True, selfcons=sc)
                    lB = max(lB, T2.thresholdB(Dv, oB, False, 5, st, ct)[0] - pen)
            best = max(lA, lB)
            rows.append(dict(norms=tag, small_divisors=which, A=lA, B=lB, best=best,
                             margin=best - PLASMALEAN["log10_tolerance"]))
            print("| %s | %s | %.2f | %.2f | %.2f | %+.2f |" % (tag, which, lA, lB, best,
                                                               best - PLASMALEAN["log10_tolerance"]))
            sys.stdout.flush()
    return rows


def plasmalean_l1():
    """B10 (blueprint/parts/p2s2-l1hybrid.tex): the l^1 entry step on PlasmaLean's example.  Stage 0 uses l^1 data of
    the initial torus with Gamma_inf at the actual bites; stages >= 1 are the sup scheme with c_freq computed AT EACH
    BITE (c_stages(..., 'freq'), not the flat value of the table above) and the classical constant c(delta_5) in the
    tail.  Two readings of the threshold:
      (a) the threshold on |E|_{l1,rho}, against PlasmaLean's tolerance on the l^1 error-norm category (not an
          identified canonical residual)
          (|eta|_{l1} <= (frame cap) |E|_{l1}, sup|E| <= |E|_{l1}: aN = aL = 1, PlasmaLean's frame and torsion
          bounds read as l^1 bounds);
      (b) sup-equivalent: the threshold on sup|E| for an error with |E|_{l1}/sup|E| = 3.6 (aN = aL = 3.6; the R1
          lower-torus ratio of CERTIFIER-SHARPNESS 1.2, measured 4.28 on R1's own residual by l1_entry_r1.py).
    Transposes are the conservative defaults (s_Lt = 2n s_K, ...); the l^1 frame caps of the frame-increment variant are
    the same numbers (nuK = s_K, nuN = s_N); route B gets the torsion cap |T| <= 19.84 x 1.05 as route A does."""
    print()
    print("B10: the l^1 entry step on PlasmaLean's example (its tolerance 10^%.2f)." % PLASMALEAN["log10_tolerance"])
    print("Conditional comparisons of scalar error tolerances at assumed data (declared bounds read as sup and l^1"
          " bounds, nuK = s_K, nuN = s_N, ratio 3.6 assumed); not a dominance certificate for its torus"
          " (AUDIT-B10D-1 F7).")
    print("| norms | reading | variant | log10 threshold | vs PlasmaLean | binding |")
    print("|---|---|---|---:|---:|---|")
    rows = []
    for tag in ("cA-like", "R1-like"):
        D = plasmalean_data(tag)
        for reading, a_ in (("(a) l1 vs l1", 1.0), ("(b) sup-equivalent x3.6", 3.6)):
            out = T2.run_l1(D, tag, a_, a_, None, exact=False, forms=(False,), torsion_cap_B=True,
                            nuK=D["sK"], nuN=D["sN"], log=lambda *x: None)
            for r_ in out:
                m = r_["log10_threshold"] - PLASMALEAN["log10_tolerance"]
                rows.append(dict(norms=tag, reading=reading, variant=r_["variant"], log10=r_["log10_threshold"],
                                 margin=m, binding=r_["binding"]))
                print("| %s | %s | %s | %.2f | %+.2f | %s |" % (tag, reading, r_["variant"], r_["log10_threshold"], m,
                                                               ", ".join(r_["binding"])))
                sys.stdout.flush()
    best = {}
    for r_ in rows:
        k_ = (r_["norms"], r_["reading"])
        best[k_] = max(best.get(k_, -1e9), r_["margin"])
    for k_, v_ in best.items():
        print("best margin over PlasmaLean, %s, %s: %+.2f orders" % (k_[0], k_[1], v_))
    if "--json" in sys.argv:
        json.dump(dict(rows=rows), open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1)
    return rows


if __name__ == "__main__" and "--plasmalean" in sys.argv:
    plasmalean()
    plasmalean_l1()


# ---------------------------------------------------------------------------------------------------------------
# Figueras-Haro 2025 (J. Nonlinear Sci. 35 (2025) 13, arXiv:2403.10152, section 5): planar Sun-Jupiter-Saturn, a 3-torus,
# FH24 with one first integral (d = 3), tau = 2.4, gamma = 1.69e-6, rho = 0.1, delta = rho/6; c_Xh = 0.09, c_DXh = c_(DXh)^T
# = 129, c_D2Xh = 5e10; ||DK|| = 4.7812, ||DK^T|| = 6.8756, ||B|| = 7.3581, ||N|| = 3.5704, ||N^T|| = 2.8621,
# |<T>^-1| = 354.08; sigma = norm (1 + 1e-10).  Their check: the Iterative Lemma iterated numerically for 10 steps, then
# the KAM theorem, closes for ||eta^DK|| = 1e-38, ||eta^N|| = 1e-44 (numerically checked, not interval arithmetic).
# Mapping: v2 is a d = n canonical theorem; we use their norms as the caps of a d = n = 3 problem (the first integral and
# the moment flow are dropped: c_Xp = 0), the same uniform small-divisor constant structure (classical, our c^natural),
# c_Th = 2 c_DXh, c_DTh = 2 c_D2Xh, margins 1e-10 x norm for the internal caps and the frame, and a prefix of 10 exact
# stages (their 10 numerical steps).  Compared: whether (1e-38, 1e-44) is admissible, and the margin in orders.
# ---------------------------------------------------------------------------------------------------------------

FH25 = dict(etaL=1e-38, etaN=1e-44)


def fh25_data(mu_rel=1e-10):
    n = 3
    norms = dict(sK=4.7811815833, sLt=6.8755882886, sB=7.35806411265, sN=3.5704498717, sNt=2.8621242724, sT=354.07743243)
    D = dict(n=n, tau=2.4, kappa=2.4, rho=0.1, rhoinf=0.1 / 1000, gamma=1.69e-6, gbar=1.69e-6,
             M=5e10, M0=0.09, M1=129.0, M2=5e10, Mh1=129.0, Mh2=5e10, cTh=2 * 129.0, Tsup=None,
             Theta_omega=None, omega_star=None, nu=1e-6)
    for k_, v in norms.items():
        D[k_] = v * (1 + mu_rel)
    D["mu"] = 2 * mu_rel * norms["sK"]                     # so that the |DK| budget mu/2 equals their margin
    for k_, nm in (("B", "sB"), ("Tinv", "sT"), ("Lt", "sLt"), ("N", "sN"), ("Nt", "sNt")):
        D["bud_" + k_] = norms[nm] * mu_rel
    return D


def fh25(kpre=10):
    D = fh25_data()
    n, tau = D["n"], D["tau"]
    lam = 3
    delta0 = (D["rho"] - D["rhoinf"]) / (2 * lam)
    ccl = lambda d: sd.c_classical(n, tau, float(d))

    def st(s):
        ds = delta0 / 2 ** s
        r = D["rho"] - 2 * lam * delta0 * (1 - 0.5 ** s)
        return ccl(ds), ccl(ds / 2), ccl(min(r, 1.0))
    ct = ccl(delta0 / 2 ** kpre)
    gd0 = D["gamma"] * delta0 ** tau
    mu0 = max(FH25["etaL"], FH25["etaN"] / gd0)             # their errors, isotropic weight
    X0 = mu0 / (D["gamma"] * delta0 ** (tau + 1))
    out = {}
    stg = lambda ds, r: (ccl(ds), ccl(ds / 2), ccl(min(r, 1.0)))
    for aniso, ratio, cDTh in ((False, 2, None), (True, 2, None), (True, 3, None), (True, 4, None), (True, 3, 2 * 129.0)):
        o = dict(L1=True, keep_delta=True, avg_full_bite=True, theta=F(1, 16), cTh=D["cTh"], free_budgets=True,
                 aniso=aniso, eta_measured=(FH25["etaL"], FH25["etaN"]), no_e=True, ratio=ratio)
        if cDTh:
            o["cDTh"] = cDTh
        st_use = st if ratio == 2 else stg
        le, _, why = T2.thresholdB(D, o, False, kpre, st_use, ct)
        tag = "%s, ratio %s%s" % ("anisotropic" if aniso else "FH24 weight", ratio,
                                   ", c_DTh = 2 c_DXh (hypothetical)" if cDTh else ", c_DTh = 2 c_D2Xh")
        out[tag] = dict(log10_scale=le, binding=why)
        print("FH25 data, v2 route B (k = %d, classical c, %s): admissible scale of (1e-38, 1e-44) = 10^%.2f; binding %s"
              % (kpre, tag, le, ", ".join(why)))
    return out
    for aniso in ():
        o = dict(L1=True, keep_delta=True, avg_full_bite=True, theta=F(1, 16), cTh=D["cTh"], free_budgets=True,
                 aniso=aniso, eta_measured=(FH25["etaL"], FH25["etaN"]), no_e=True)
        # admissible X at stage 0 (bisection inside thresholdB returns log10 e for mu_0 = per_e e; recover log10 X*)
        le, _, why = T2.thresholdB(D, o, False, kpre, st, ct)
        per_e = max(FH25["etaL"], FH25["etaN"] / gd0) / 1.0
        # thresholdB uses per_e = max{etaL, etaN/(gamma delta0^kappa)} with the measured eta's per unit e; e* is the
        # scale factor on (etaL, etaN): admissible iff e* >= 1
        out["aniso" if aniso else "iso-weight"] = dict(log10_scale=le, binding=why)
        print("FH25 data, v2 route B (k = %d, classical c, %s): admissible scale of (1e-38, 1e-44) = 10^%.2f; binding %s"
              % (kpre, "anisotropic stage-0 weight" if aniso else "FH24 weight", le, ", ".join(why)))
    return out


if __name__ == "__main__" and "--fh25" in sys.argv:
    fh25()


# ---------------------------------------------------------------------------------------------------------------
# SHARP2-DOMPLUS: closeness constants (C2 of G1Body; iso C2 and C3 of IG1Body) and wider ranges.
# The closeness bound of a theorem at the error e is the bound it gives for |K_inf - K| (and |omega_inf - omega|) when
# |E| <= e satisfies its smallness; each theorem is a family over its free parameters, and every member admitting e is a
# valid instance, so its bound at e is the minimum over the admissible members.  Compared at
#   e_c = (1/2) min{e*_v2, e*_competitor}  (both theorems apply, with room), and
#   e -> 0                                  (the linear coefficient: e_0 = 1e-9 min of the thresholds).
# v2: route B (all configurations of v2_same_data, floating point) and route A (exact); the ball sum of the engine is
# the closeness bound (bp:p2s2:engine, J4) and the frequency sum the iso frequency closeness (bpI:p2s2:g1).
# FH24: ||K_inf - K|| <= C_DeltaK/(gamma delta^tau) eps, eps <= c_Om max{s_NT, s_LT/(gamma delta^tau)} e ((2.32), p. 19), its
# (delta, kappa) scanned with c_R = c^nat(delta) (fair data), nu, varkappa at the threshold optimum.  HL19: C2 e/(gamma^2
# rho^{2 tau}) ((3.11), <= by E-HL19-1/8); iso frequency C3 e/(gamma rho^tau) ((6.51), E-HL19-12), a_1 scanned.
# ---------------------------------------------------------------------------------------------------------------

def _v2_configs(D, iso=False, kpre=5, thetas=(F(1, 16), F(1, 8)), ratios=RATIOS, ymaxs=(F(1, 2), F(9, 10)),
                scs=(False, True), xlo=1e-60, tslacks=(F(1, 10),), tights=(False,)):
    """The route-B configurations of v2 (floating point) as (options, k, c_stage, c_tail)."""
    n, tau = D["n"], int(D["tau"])
    Df = {k_: (float(v) if isinstance(v, F) else v) for k_, v in D.items()}
    cf = lambda d: c_nat(n, tau, d, exact=False)
    sp = tau / (tau + 1)
    stf = lambda ds, r: (cf(ds), cf(sp * ds), cf(min(r, 1.0)))
    stf.by_bite = True
    out = []
    for a, k in ratios:
        d0 = min(1.0, (Df["rho"] - Df["rhoinf"]) * float(a - 1) / (3 * float(a)))
        rk = Df["rho"] - 3 * d0 * (1 - float(a) ** -k) / (1 - 1 / float(a))
        ctf = (cf(d0 / float(a) ** k), cf(min(rk, 1.0)))
        for th in thetas:
            for ym in ymaxs:
                for sc in scs:
                    for ts in tslacks:
                        for tg in tights:
                            oB = dict(L1=False, keep_delta=True, avg_full_bite=True, aniso=True, theta=th, ratio=a,
                                      split=sp, ymax=ym, selfcons=sc, theta_given=iso, xlo=xlo, tslack=ts,
                                      tight_caps=tg)
                            out.append((oB, k, stf, ctf))
    return Df, out


def _v2_routeA(D, iso=False, kpre=5):
    """Route A of v2 (exact), as in v2_same_data."""
    n, tau = D["n"], int(D["tau"])
    c_cl = lambda d: c_nat(n, tau, d)
    delta0 = min(F(1), (D["rho"] - D["rhoinf"]) / 6)

    def st(s):
        ds = delta0 / 2 ** s
        r = D["rho"] - 6 * delta0 * (1 - F(1, 2 ** s))
        return c_cl(ds), c_cl(ds / 2), c_cl(min(r, F(1)))
    ct = c_cl(delta0 / 2 ** kpre)
    oA = dict(omega_eta=True, avg_full_bite=True, keep_delta=True, caps_tilde=True, theta_given=iso, xlo=1e-200)
    return oA, st, ct


def v2_threshold(D, iso=False, xlo=1e-60):
    """log10 e* of v2 on the competitors' data (best of route B configurations and route A)."""
    Df, cfgs = _v2_configs(D, iso, xlo=xlo)
    best = (-1e9, None)
    for oB, k, stf, ctf in cfgs:
        le = T2.thresholdB(Df, oB, iso, k, stf, ctf)[0]
        if le > best[0]:
            best = (le, dict(route="B", ratio=float(oB["ratio"]), kpre=k, theta=float(oB["theta"]),
                             ymax=float(oB["ymax"]), selfcons=oB["selfcons"]))
    oA, st, ct = _v2_routeA(D, iso)
    try:
        lA = T2.thresholdA(D, oA, iso, k=5, c_stage=st, c_tail=ct)[0]
    except (AssertionError, ZeroDivisionError, OverflowError):
        lA = -1e9
    if lA > best[0]:
        best = (lA, dict(route="A"))
    return best


RATIOS_CLOSE = RATIOS + ((F(3), 4), (F(4), 3), (F(8), 2), (F(32), 1), (F(256), 1), (F(4096), 1))   # large a: delta_0 ->
# (rho - rho_inf)/3, the limit FH24's bite also approaches; FH24's scan gets the same bites (T_NEAR)
T_NEAR = [1 - 1 / float(a) for a, _ in RATIOS_CLOSE if a > 2]


def v2_close(D, e, iso=False):
    """v2's closeness bounds at the error e: the minimum over the admissible members (route B configurations, route A)
    of the ball sum (|K_inf - K|) and, iso, of the frequency sum (|omega_inf - omega|).  The schedule ratio is free; for
    closeness the large ratios matter (the first displacement ~ 1/delta_0^{2 kappa})."""
    Df, cfgs = _v2_configs(D, iso, ratios=RATIOS_CLOSE, thetas=(F(1, 16), F(1, 8), F(1, 128)),
                           tslacks=(F(1, 10), F(1, 1000), F(1, 10 ** 9)), tights=(False, True))
    ball = nu = math.inf
    for oB, k, stf, ctf in cfgs:
        r = T2.thresholdB(Df, oB, iso, k, stf, ctf, at_e=e)
        if r["ok"]:
            ball = min(ball, float(r["ball"]))
            if iso:
                nu = min(nu, float(r["nu"]))
    oA, st, ct = _v2_routeA(D, iso)
    try:
        r = T2.thresholdA(D, oA, iso, k=5, c_stage=st, c_tail=ct, at_e=v1.up(e))
        if r["ok"]:
            ball = min(ball, float(r["ball"]))
            if iso and r["nu"] is not None:
                nu = min(nu, float(r["nu"]))
    except (AssertionError, ZeroDivisionError, OverflowError):
        pass
    return ball, nu


def fh24_scan(d, nu, k1, errata=True, steps=40):
    """FH24 with fair data on the (delta, kappa) grid (nu, varkappa fixed at the threshold optimum): the list of
    (threshold_e, closeness_e, t, kappa) of its members (floating point)."""
    n, tau = int(d["n"]), int(d["tau"])
    fac = float(F(tau + 1) ** (tau + 1) / F(tau) ** tau)
    Dr = (float(d["rho"]) - float(d["rhoinf"])) / 3
    ddf = dict(d, cRrho=float(c_nat(n, tau, min(F(d["rho"]), F(1)))))
    tk = sorted(set([float(x) for x in FH._grid_t(F(0), F(1), steps)] + T_NEAR))
    out = []

    spl = tau / (tau + 1)

    def ev(t, k2):
        c = c_nat(n, tau, t * Dr, exact=False)
        c1 = fac * c_nat(n, tau, spl * t * Dr, exact=False)   # c^1_R from the split bite (FH24 Cor. 2.16)
        try:
            r = FH.fh24(ddf, c, c1, t * Dr, float(nu), float(k1), k2, exact=False, errata=errata)
            return (r["threshold_e"], r["closeness_e"], t, k2)
        except (AssertionError, ZeroDivisionError, OverflowError):
            return None
    for t in tk:
        for k2 in tk:
            r = ev(t, k2)
            if r:
                out.append(r)
    return out, ev


def fh24_close(scan, ev, e):
    """FH24's closeness bound at e: the minimum over admissible members, refined locally."""
    adm = [r for r in scan if r[0] >= e]
    if not adm:
        return math.inf
    best = min(adm, key=lambda r: r[1])
    for step in (1 / 200, 1 / 800):
        t0, k0 = best[2], best[3]
        for i in range(-8, 9):
            for j in range(-8, 9):
                t, k2 = t0 + i * step, k0 + j * step
                if 0 < t < 1 and 0 < k2 < 1:
                    r = ev(t, k2)
                    if r and r[0] >= e and r[1] < best[1]:
                        best = r
    return best[1] * e


def hl19_close(scan, e, gamma, rho, tau, which="C2"):
    """HL19's closeness bound at e (C2 e/(gamma^2 rho^{2tau}); iso C3 e/(gamma rho^tau), (6.51))."""
    g, rr = float(gamma), float(rho)
    best = math.inf
    for r in scan:
        if float(r["threshold"]) >= e:
            if which == "C2":
                best = min(best, float(r["C2"]) * e / (g ** 2 * rr ** (2 * tau)))
            else:
                best = min(best, float(r["C3"]) * e / (g * rr ** tau))
    return best


def _lm(a, b):
    """log10(a/b), with inf handled."""
    if b == 0 or math.isinf(a) and math.isinf(b):
        return float("nan")
    if math.isinf(a):
        return float("inf")
    if math.isinf(b):
        return float("-inf")
    return math.log10(a / b)


def compare_close(D, xlo=1e-60):
    """Thresholds and closeness at fixed frequency: v2 vs FH24 (corrected, fair) and HL19 (fair)."""
    tau = int(D["tau"])
    lv2, par = v2_threshold(D, False, xlo)
    hls = hl19_scan(comp_data_hl(D))
    eH = max((float(r["threshold"]) for r in hls), default=0.0)
    fhc = best_fh24_fair(comp_data_fh(D), errata=True)
    eF = float(fhc["threshold_e"])
    scan, ev = fh24_scan(comp_data_fh(D), fhc["nu"], fhc["kappa1"])
    ev2 = 10 ** lv2
    out = dict(v2=lv2, v2_params=par, FH24_corr=lg(fhc["threshold_e"]), HL19=math.log10(eH) if eH > 0 else -1e9)
    ecF, ecH = 0.5 * min(ev2, eF), 0.5 * min(ev2, eH) if eH > 0 else 0.0
    e0 = 1e-9 * min(x for x in (ev2, eF, eH) if x > 0)
    vF, _ = v2_close(D, ecF)
    vH, _ = v2_close(D, ecH) if ecH > 0 else (math.inf, None)
    v0, _ = v2_close(D, e0)
    cF, c0F = fh24_close(scan, ev, ecF), fh24_close(scan, ev, e0)
    cH = hl19_close(hls, ecH, D["gamma"], D["rho"], tau) if ecH > 0 else math.inf
    c0H = hl19_close(hls, e0, D["gamma"], D["rho"], tau)
    out.update(close_v2_eF=vF, close_FH24_eF=cF, close_v2_eH=vH, close_HL19_eH=cH, lin_v2=v0 / e0, lin_FH24=c0F / e0,
               lin_HL19=c0H / e0, m_FH24_ec=_lm(cF, vF), m_HL19_ec=_lm(cH, vH), m_FH24_lin=_lm(c0F, v0),
               m_HL19_lin=_lm(c0H, v0))
    out["margin_thr"] = lv2 - max(out["FH24_corr"], out["HL19"])
    out["margin_close"] = min(out["m_FH24_ec"], out["m_HL19_ec"], out["m_FH24_lin"], out["m_HL19_lin"])
    return out


def grid_data_iso(n, tau, gamma, rho, size):
    """The grid data with the isoenergetic inputs: |omega*| = 1, sigma_omega = 2 (Theta = sigma_omega |omega*| = 2, given to
    both theorems), frequency margin nu = 1/10, |Dh|, |D^2 h| <= M."""
    D = grid_data(n, tau, gamma, rho, size)
    D.update(Theta_omega=F(2), nu=F(1, 10))
    return D


def comp_data_hl_iso(D):
    d = comp_data_hl(D)
    d.update(cc1=D["M"], cc2=D["M"], omstar=F(1), sigom=F(2), distom=D["nu"])
    return d


def compare_iso(D):
    """Isoenergetic: v2 (route B iso, route A iso) vs HL19 Theorem 3.6 (fair): thresholds, C2 (|K_inf - K|), C3
    (|omega_inf - omega|, (6.51) normalisation, E-HL19-12).  FH24 has no isoenergetic theorem."""
    tau = int(D["tau"])
    lv2, par = v2_threshold(D, True)
    hls = hl19_scan(comp_data_hl_iso(D), iso=True)
    eH = max((float(r["threshold"]) for r in hls), default=0.0)
    ev2 = 10 ** lv2
    out = dict(v2=lv2, v2_params=par, HL19=math.log10(eH) if eH > 0 else -1e9)
    if eH <= 0:
        out.update(margin_thr=float("inf"), margin_close=float("inf"))
        return out
    ec, e0 = 0.5 * min(ev2, eH), 1e-9 * min(ev2, eH)
    vb, vn = v2_close(D, ec, True)
    vb0, vn0 = v2_close(D, e0, True)
    out.update(m_C2_ec=_lm(hl19_close(hls, ec, D["gamma"], D["rho"], tau), vb),
               m_C3_ec=_lm(hl19_close(hls, ec, D["gamma"], D["rho"], tau, "C3"), vn),
               m_C2_lin=_lm(hl19_close(hls, e0, D["gamma"], D["rho"], tau), vb0),
               m_C3_lin=_lm(hl19_close(hls, e0, D["gamma"], D["rho"], tau, "C3"), vn0))
    out["margin_thr"] = lv2 - out["HL19"]
    out["margin_close"] = min(out["m_C2_ec"], out["m_C3_ec"], out["m_C2_lin"], out["m_C3_lin"])
    return out


def _cpoint(args):
    n, tau, g, r, s, iso, xlo = args
    try:
        if iso:
            res = compare_iso(grid_data_iso(n, tau, g, r, s))
        else:
            res = compare_close(grid_data(n, tau, g, r, s), xlo)
    except (AssertionError, ZeroDivisionError, OverflowError, TypeError, ValueError) as ex:
        return dict(n=n, tau=tau, gamma=float(g), rho=float(r), size=s, skipped=repr(ex)[:200])
    return dict(n=n, tau=tau, gamma=float(g), rho=float(r), size=s, **res)


def wide_points():
    """The wider ranges: n in {8, 10} with tau in {n-1, n}, rho up to 1, gamma down to 1e-10; and rho in {0.6, 1},
    gamma = 1e-10 for the earlier (n, tau)."""
    pts = []
    for (n, tau) in [(8, 7), (8, 8), (10, 9), (10, 10)]:
        for g in [F(1, 10 ** 10), F(1, 10 ** 6), F(1, 1000), F(1, 10)]:
            for r in [F(1, 100), F(1, 10), F(3, 10), F(6, 10), F(1)]:
                for s in [1, 10, 30]:
                    pts.append((n, tau, g, r, s))
    for (n, tau) in GRID_EXT["ns"]:
        for g in [F(1, 10 ** 10), F(1, 1000)]:
            for r in [F(6, 10), F(1)]:
                for s in [1, 10]:
                    pts.append((n, tau, g, r, s))
        for r in [F(1, 1000), F(1, 10)]:
            for s in [1, 10]:
                pts.append((n, tau, F(1, 10 ** 10), r, s))
    return pts


def closeness_main():
    gname = sys.argv[sys.argv.index("--grid") + 1] if "--grid" in sys.argv else "ext"
    iso = "--iso" in sys.argv
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 1
    if gname == "wide":
        pts_in = wide_points()
    elif gname == "iso":
        pts_in = [(n, tau, g, r, s) for (n, tau) in [(2, 1), (2, 2), (3, 2), (4, 3)]
                  for g in [F(1, 10 ** 6), F(1, 1000), F(1, 10)] for r in [F(1, 100), F(1, 10), F(3, 10)] for s in [1, 3, 10]]
        iso = True
    elif gname == "quick":
        pts_in = [(2, 1, F(1, 1000), F(1, 10), 1), (4, 3, F(1, 1000), F(1, 10), 10)]
    else:
        G = GRID_EXT
        pts_in = [(n, tau, g, r, s) for (n, tau) in G["ns"] for g in G["gammas"] for r in G["rhos"] for s in G["sizes"]]
    args = [(n, tau, g, r, s, iso, 1e-280) for (n, tau, g, r, s) in pts_in]
    t0 = time.time()
    if jobs > 1:
        import multiprocessing as mpr
        with mpr.Pool(jobs) as pool:
            rows = pool.map(_cpoint, args, chunksize=1)
    else:
        rows = [_cpoint(a) for a in args]
    pts = [r for r in rows if "skipped" not in r]
    skipped = [r for r in rows if "skipped" in r]
    key_thr, key_cl = "margin_thr", "margin_close"
    for r in rows:
        if "skipped" in r:
            print("| %d | %d | %g | %g | %d | skipped %s |" % (r["n"], r["tau"], r["gamma"], r["rho"], r["size"], r["skipped"]))
        elif iso:
            print("| %d | %d | %g | %g | %d | %.2f | %.2f | %+.2f | C2 %+.2f / %+.2f | C3 %+.2f / %+.2f |" % (
                r["n"], r["tau"], r["gamma"], r["rho"], r["size"], r["v2"], r["HL19"], r["margin_thr"],
                r.get("m_C2_ec", float("nan")), r.get("m_C2_lin", float("nan")), r.get("m_C3_ec", float("nan")),
                r.get("m_C3_lin", float("nan"))))
        else:
            print("| %d | %d | %g | %g | %d | %.2f | %.2f | %.2f | %+.2f | FH24 %+.2f / %+.2f | HL19 %+.2f / %+.2f |" % (
                r["n"], r["tau"], r["gamma"], r["rho"], r["size"], r["v2"], r["FH24_corr"], r["HL19"], r["margin_thr"],
                r["m_FH24_ec"], r["m_FH24_lin"], r["m_HL19_ec"], r["m_HL19_lin"]))
    print()
    nthr = sum(1 for p in pts if p[key_thr] < -0.005)
    ncl = sum(1 for p in pts if p[key_cl] < -0.005)
    print("grid %s%s: points %d (skipped %d), threshold losses %d, closeness losses %d, time %.0f s" % (
        gname, " iso" if iso else "", len(pts), len(skipped), nthr, ncl, time.time() - t0))
    for k_ in (key_thr, key_cl) + (("m_FH24_ec", "m_FH24_lin", "m_HL19_ec", "m_HL19_lin") if not iso else
                                    ("m_C2_ec", "m_C2_lin", "m_C3_ec", "m_C3_lin")):
        v = sorted(p[k_] for p in pts if k_ in p and not math.isnan(p[k_]))
        if v:
            print("  %s: min %+.3f, median %+.3f, max %+.3f" % (k_, v[0], v[len(v) // 2], v[-1]))
    if pts:
        w = min(pts, key=lambda p: p[key_cl])
        print("worst closeness point:", {k_: w[k_] for k_ in w if not isinstance(w[k_], dict)})
    if "--json" in sys.argv:
        json.dump(dict(points=pts, skipped=skipped), open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1,
                  default=str)


if __name__ == "__main__" and "--closeness" in sys.argv:
    closeness_main()
