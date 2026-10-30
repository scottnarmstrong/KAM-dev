#!/usr/bin/env python3
"""SJS-PLAN item 1: v2 thresholds on the MEASURED coarse SJS torus, per chart, searching the strip and the scales (c, ell).

Untrusted design tooling.  Mirrors (read-only): scripts/apost_sharp/thresholds_v2.py (thresholdA, thresholdB: the design mirrors)
and route_a_lean_mirror.py (`routeAOkR`, lever L8').  Data measured by sjs_chart.py on sjs_torus.py's torus:
  sK, Lt, B, N, Nt: sampled sups on the distinguished boundary of T_rho (x 1.01 + mu);  <T>^-1, sup|T|, sup|T_h|: real grid;
  M0, M1, M2, Mh1, Mh2: sampled on the polydisc box of the chart (the domain of the landed ball arithmetic) x SAFE.
Delaunay rows also evaluate FH's published (c_Xh, c_DXh, c_D2Xh) to reproduce SJS-FEAS.  SAFE is the assumed ratio enclosure/sample.
tau = 2 (the cubic frequency).  gamma: the certified value of sjs_dioph.py, or the numerical one.  Frequency-specific stage constants
from S(omega, delta), fitted as S = 2.77e12 (delta/0.00265)^-3.2 (period-1 units, SJS-FEAS's three computed bites); the frame's
effect on |k|_1 in S is neglected.  Fixed-frequency form.
Usage: python3 -I scripts/sjs/plan/sjs_plan_thresholds.py TORUS.npz [--json OUT] [--quick]
"""
import itertools, json, math, os, sys, time
from fractions import Fraction as F
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, "scripts", "apost_sharp"))
sys.path.insert(0, os.path.join(ROOT, "scripts", "certifier"))
import sjs_torus as ST                  # noqa: E402
import sjs_chart as CH                  # noqa: E402
import thresholds_v2 as T2              # noqa: E402
import route_a_lean_mirror as RA        # noqa: E402

TP = 2 * math.pi
OM = np.array(ST.OMEGA)
SAFE = 2.0
GAMMAS = dict(num=1.85e-5, cert8=2.77e-7)      # FH units; cert8 = sjs_dioph.py, field x^3 - x - 1, |omega - omega_FH| <= 1e-8


def Sfit(delta):
    return 2.77e12 * (delta / 0.00265) ** -3.2


def q(x):
    return F(float(x)).limit_denominator(10 ** 14)


def crop(P, new):
    C = np.fft.fftn(P, axes=(-3, -2, -1))
    idx = [np.r_[0:n // 2, -n // 2 + 1:0] for n in new]
    out = C[np.ix_(range(P.shape[0]), *idx)]
    full = np.zeros((P.shape[0],) + tuple(new), dtype=complex)
    full[np.ix_(range(P.shape[0]), *[np.r_[0:n // 2, -n // 2 + 1:0] for n in new])] = out
    return np.fft.ifftn(full, axes=(-3, -2, -1)).real * (np.prod(new) / np.prod(P.shape[1:]))


def package(geo, tor, Mx, rho1, mu, c, ell, gam_fh, om_t, tau=2):
    """the design data dict, period-1 strip rho1."""
    gam = c * gam_fh / TP
    nrm = float(np.abs(om_t).max())
    D = dict(n=3, tau=tau, kappa=tau, rho=q(rho1), rhoinf=q(rho1 / 1000), gamma=q(gam), gbar=q(gam), mu=q(mu),
             nu=q(1e-6 * nrm), sK=q(geo["K"] * 1.01 + mu), sB=q(geo["B"] * 1.01 + mu), sT=q(tor["tinv"] * 1.0005 + mu),
             M0=q(Mx["M0"]), M1=q(Mx["M1"]), M2=q(Mx["M2"]), M=q(max(Mx["M0"], Mx["M1"], Mx["M2"])), Mh1=q(Mx["Mh1"] * 3),
             Mh2=q(Mx["Mh2"]), sLt=q(geo["Lt"] * 1.01 + mu), sN=q(geo["N"] * 1.01 + mu), sNt=q(geo["Nt"] * 1.01 + mu),
             Tsup=q(tor["Tsup"] * 1.01), cTh=q(Mx.get("Th", 2 * Mx["M1"])), Theta_omega=q(2 * nrm),
             omega_star=tuple(float(x) for x in om_t))
    for k_, base in (("B", D["sB"]), ("Tinv", D["sT"]), ("Lt", D["sLt"]), ("N", D["sN"]), ("Nt", D["sNt"]), ("Tsup", D["Tsup"])):
        D["bud_" + k_] = base / 10
    return D


def stage_fn(Dv, k=2):
    """frequency-specific constants at the bites, the classical constant beyond"""
    n, tau, kap = Dv["n"], int(Dv["tau"]), int(Dv["kappa"])
    lam = 3
    delta0 = (Dv["rho"] - Dv["rhoinf"]) / (2 * lam)
    gam = float(Dv["gamma"]); wmax = float(np.abs(Dv["omega_star"]).max())
    c_rel = max(abs(x) for x in Dv["omega_star"]) / (abs(OM).max() / TP)  # = c
    ccl = lambda d: T2.Fr(T2.sd.c_classical(n, tau, float(d)))

    def cf(d):
        d = float(d)
        G = TP ** -1 * 2 ** (n / 2) * math.sqrt(Sfit(d)) / c_rel
        return min(T2.Fr(G * gam * d ** kap), ccl(d))

    def st(s):
        ds = delta0 / 2 ** s
        r = Dv["rho"] - 2 * lam * delta0 * (1 - F(1, 2 ** s))
        return cf(ds), cf(ds / 2), ccl(min(r, F(1)))
    return st, ccl(delta0 / 2 ** k)


def route_b(D, freq=True, k=2, iso=False):
    th = F(1, 16)
    o = dict(keep_delta=True, avg_full_bite=True, theta=th, L1=True, cTh=D["cTh"], free_budgets=True)
    Dv = T2.with_caps(D, F(1, 20))
    if freq:
        st, ct = stage_fn(Dv, k)
    else:
        st, ct = T2.c_stages(Dv, "classical")
        k = 5
    le, d0, why = T2.thresholdB(Dv, o, iso, k, st, ct)
    return le, ",".join(why[:2])


def route_a(D, freq=True, k=2):
    Dv = T2.with_caps(D, F(1, 20))
    if freq:
        st, ct = stage_fn(Dv, k)
        ct = (ct, ct)
    else:
        st, ct = T2.c_stages(Dv, "classical")
        k = 5
    Dv = dict(Dv)
    Dv["Tsup_cap"] = Dv.get("Tsup_cap", D["Tsup"] + D["mu"] / 2)
    return RA.threshold(RA.num_from(Dv, st, ct, k=k), RA.route_a_ok_ref)


def evaluate(chart, P, Fm, phi, gr, gr_c, Pc, rho, ell, c, mu, gam, tn_box, tor_cache, geo_cache, tag=None):
    key = (chart, rho, ell)
    if key not in geo_cache:
        geo_cache[key] = CH.frames_on_strip(Pc, Fm, gr_c, rho, ell)
    geo = geo_cache[key]
    if (chart, ell) not in tor_cache:
        tor_cache[(chart, ell)] = CH.torsion_grid(chart, P, Fm, phi, gr, step=2, c=1.0, ell=ell)
    t1 = tor_cache[(chart, ell)]
    tor = dict(tinv=t1["tinv"] / c, Tsup=t1["Tsup"] * c, Th=t1["Th"] * c)
    Mx = {k: v * SAFE for k, v in CH.majorants(tn_box, c, ell).items()}
    Mx["Th"] = tor["Th"] * SAFE
    om_t = c * (Fm @ OM) / TP
    return package(geo, tor, Mx, rho / TP, mu, c, ell, gam, om_t), geo, tor, Mx


def main():
    d = np.load(sys.argv[1])
    u = d["u"]
    quick = "--quick" in sys.argv
    out = []
    rhos = [0.02, 0.05, 0.1] if quick else [0.01, 0.02, 0.03, 0.05, 0.07, 0.1]
    ells = [1.0, 0.1, 0.01, 1e-3] if quick else [1.0, 0.3, 0.1, 0.03, 0.01, 3e-3, 1e-3]
    cs = [1.0, 30.0, 300.0, 3000.0] if quick else [1.0, 10.0, 30.0, 100.0, 300.0, 1000.0, 3000.0, 10000.0]
    mus = [1e-3, 1e-4]
    charts = ("syn", "del")

    def arg(name, default, conv=float):
        if name in sys.argv:
            return [conv(x) for x in sys.argv[sys.argv.index(name) + 1].split(",")]
        return default
    rhos, ells, cs, mus = arg("--rhos", rhos), arg("--ells", ells), arg("--cs", cs), arg("--mus", mus)
    charts = arg("--charts", charts, str)
    print("| chart | gamma | rho | ell | c | mu | route A' | route B | binding B | sK | sB | |T^-1| | M1 | M2 |", flush=True)
    for chart in charts:
        P, Fm, phi, gr = CH.periodic_data(u, chart)
        new = (64, 64, 64)
        Pc = crop(P, new)
        gr_c = ST.Grid(new)
        tor_cache, geo_cache = {}, {}
        for rho in rhos:
            best = {}
            pts, info = CH.box_points(P, Fm, gr, rho, 1e-3, 1e-5, 4000)
            tn = CH.tensors(chart, pts, phi)
            for ell, mu, c in itertools.product(ells, mus, cs):
                for gname, gam in GAMMAS.items():
                    t0 = time.time()
                    D, geo, tor, Mx = evaluate(chart, P, Fm, phi, gr, gr_c, Pc, rho, ell, c, mu, gam, tn, tor_cache, geo_cache)
                    try:
                        a = route_a(D)
                    except Exception as ex:           # noqa: BLE001
                        a = float("nan")
                    try:
                        b, why = route_b(D)
                    except Exception as ex:           # noqa: BLE001
                        b, why = float("nan"), repr(ex)[:60]
                    rec = dict(chart=chart, gamma=gname, rho=rho, ell=ell, c=c, mu=mu, A=a, B=b, why=why, sK=float(D["sK"]),
                               sB=float(D["sB"]), sT=float(D["sT"]), M1=float(D["M1"]), M2=float(D["M2"]), M0=float(D["M0"]),
                               sN=float(D["sN"]), sNt=float(D["sNt"]), sLt=float(D["sLt"]), Tsup=float(D["Tsup"]))
                    out.append(rec)
                    for nm in ("A", "B"):
                        v = rec[nm]
                        if v == v and (gname, nm) not in best or (v == v and v > best[(gname, nm)][nm]):
                            best[(gname, nm)] = rec
            for (gname, nm), r in sorted(best.items()):
                print("| %s | %s | %.3f | %.3g | %.3g | %.0e | %.1f | %.1f | %s | %.2f | %.1f | %.3g | %.3g | %.3g | best %s" % (
                    r["chart"], gname, r["rho"], r["ell"], r["c"], r["mu"], r["A"], r["B"], r["why"][:24], r["sK"], r["sB"],
                    r["sT"], r["M1"], r["M2"], nm), flush=True)
            if "--json" in sys.argv:
                json.dump(out, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=0)


if __name__ == "__main__":
    main()
