#!/usr/bin/env python3
"""SJS-FEAS: thresholds of the a-posteriori theorems on Figueras-Haro's Sun-Jupiter-Saturn torus data.

Untrusted design tooling.  Data: FH25 (arXiv:2403.10152) Section 5: n = 3 (angular momentum reduced), fixed frequency,
tau = 2.4, gamma = 1.69e-6, rho = 0.1 (2 pi-periodic angles), delta = rho/6, c_Xh = 0.09, c_DXh = c_(DXh)^T = 129,
c_D2Xh = 5e10, |DK| = 4.78118, |DK^T| = 6.87559, |B| = 7.35806, |N| = 3.57045, |N^T| = 2.86212, |<T>^-1| = 354.077.
Theorems (mirrors imported read-only):
  v0   the sealed g1_explicit structure (thresholds.current_fixed; one size m)
  v1   the sharp design (thresholds.sharp, Russmann data, one M)
  FH24 Theorem 2.18 of Figueras-Haro 2024 (SHARP-PLUS's benchmark_fh24.py, exact transcription, canonical case),
       evaluated in FH's own variables (2 pi angles) -- FH25's published thresholds include 10 Iterative-Lemma steps
  v2   SHARP-PLUS's route B (FH24's modified step + v2 levers; thresholds_v2.thresholdB) with
       (a) classical small-divisor constants, (b) frequency-specific stage constants from S(omega, delta) (sjs_freq.S3)
Integer tau only in the mirrors (tau = 2 and 3 bracket FH's 2.4; with frequency-specific constants the nominal tau
only enters the tail and the absorptions).  Conventions: the v1/v2 mirrors use period-1 angles; FH's norms are used
unchanged (their 2 pi rescaling of angle and action rows is not undone -- an approximation, the same for every theorem).
The gamma used: FH's certified 1.69e-6 (a Diophantine vector within 1e-80 of the ephemeris frequency) or the
numerical infimum 1.85e-5 at k = (0, 0, 1) (sjs_freq.dioph), which an explicit algebraic frequency could attain.
Usage: python3 -I scripts/sjs/sjs_thresholds.py [--json OUT]       (env KAM_V2_DIR: SHARP-PLUS mirror directory)
"""
import os, sys, math, json
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
V2 = os.environ.get("KAM_V2_DIR", "/home/scott/KAM-dev-worktrees/sharp-plus/scripts/apost_sharp")
sys.path.insert(0, V2)
import thresholds as v1           # noqa: E402
import thresholds_v2 as T2        # noqa: E402
import benchmark_fh24 as B24      # noqa: E402
sys.path.insert(0, HERE)
import sjs_freq as SF             # noqa: E402

TP = 2 * math.pi
Q = lambda x: F(x).limit_denominator(10 ** 15) if not isinstance(x, F) else x
FH = dict(gamma=1.69e-6, gamma_num=1.85007988e-5, rho=0.1, cX=0.09, cDX=129.0, cDXT=129.0, cD2X=5e10,
          DK=4.7811815833, DKT=6.8755882886, B=7.35806411265, N=3.5704498717, NT=2.8621242724, Tinv=354.07743243)


def lg(x):
    return v1.lg(x) if isinstance(x, F) else math.log10(x)


def v0_v1(tau, gam_fh, mu=F(1, 1000)):
    rho = Q(FH["rho"] / TP); g = Q(gam_fh / TP)
    m = Q(FH["cD2X"])
    k0 = v1.current_fixed(n=3, tau=tau, M=m, sK=m, sB=m, sT=m, mu=mu, rho=rho, rhoinf=rho / 1000, gbar=g,
                          cR=max(F(1), v1.cohConst_crude(3, tau)))
    k1 = v1.sharp(n=3, tau=tau, kappa=tau, cR=v1.cohConstR_lean(3, tau), M=m, sK=Q(FH["DK"]) + mu,
                  sB=Q(FH["B"]) + mu, sT=Q(FH["Tinv"]) + mu, mu=mu, rho=rho, rhoinf=rho / 1000, gbar=g, iso=False)
    return lg(v1.threshold(k0, g)), lg(v1.threshold(k1, g))


def fh24_native(tau, gam_fh):
    """Theorem 2.18 in FH's variables (rho = 0.1, gamma as in FH, 2 pi angles), FH24's classical constants."""
    eps = F(1, 10 ** 10)
    d = dict(n=3, tau=tau, rho=Q(FH["rho"]), rhoinf=Q(FH["rho"]) / 1000, gamma=Q(gam_fh),
             c_Xh=Q(FH["cX"]), c_DXh=Q(FH["cDX"]), c_DXhT=Q(FH["cDXT"]), c_D2Xh=Q(FH["cD2X"]),
             c_Th=2 * Q(FH["cDX"]), c_DTh=2 * Q(FH["cD2X"]),
             s_DK=Q(FH["DK"]) * (1 + eps), s_DKT=Q(FH["DKT"]) * (1 + eps), s_B=Q(FH["B"]) * (1 + eps),
             s_N=Q(FH["N"]) * (1 + eps), s_NT=Q(FH["NT"]) * (1 + eps), s_Tinv=Q(FH["Tinv"]) * (1 + eps),
             DK=Q(FH["DK"]), DKT=Q(FH["DKT"]), B=Q(FH["B"]), N=Q(FH["N"]), NT=Q(FH["NT"]), Tinv=Q(FH["Tinv"]),
             dist=F(1, 1000))
    cR = B24.cR_hat_fh24(3, tau)
    cR1 = B24.cR1_fh24(cR, tau)
    r = B24.best_fh24(d, cR, cR1)
    return r


def sjs_package(tau, gam_fh, mu=F(1, 1000)):
    """SHARP-PLUS's data dict for route B (period-1 angles; FH's norms; fixed frequency)."""
    rho = Q(FH["rho"] / TP); g = Q(gam_fh / TP)
    om = [x / TP for x in SF.W]
    D = dict(n=3, tau=tau, kappa=tau, rho=rho, rhoinf=rho / 1000, gamma=g, gbar=g, mu=mu, nu=F(1, 10 ** 8),
             M=Q(FH["cD2X"]), sK=Q(FH["DK"]) + mu, sB=Q(FH["B"]) + mu, sT=Q(FH["Tinv"]) + mu,
             M0=Q(FH["cX"]), M1=Q(FH["cDX"]), M2=Q(FH["cD2X"]), Mh1=Q(FH["cX"]) * 3, Mh2=Q(FH["cDX"]),
             sLt=Q(FH["DKT"]) + mu, sN=Q(FH["N"]) + mu, sNt=Q(FH["NT"]) + mu, Tsup=2 * Q(FH["cDX"]) * Q(FH["NT"]) * Q(FH["N"]),
             cTh=2 * Q(FH["cDX"]), Theta_omega=Q(2 * max(abs(x) for x in om)), omega_star=tuple(om))
    for k_, base in (("B", D["sB"]), ("Tinv", D["sT"]), ("Lt", D["sLt"]), ("N", D["sN"]), ("Nt", D["sNt"]),
                     ("Tsup", D["Tsup"])):
        D["bud_" + k_] = base / 10
    return D


_S_CACHE_FILE = os.path.join(HERE, "results", "S3_cache.json")


def S3_cached(om, d):
    """S(omega, delta) of sjs_freq.S3, cached on disk by delta (the frequency vector is fixed)."""
    try:
        cache = json.load(open(_S_CACHE_FILE))
    except (OSError, ValueError):
        cache = {}
    key = "%.12e" % d
    if key not in cache:
        cache[key] = SF.S3(om, d)[0]
        json.dump(cache, open(_S_CACHE_FILE, "w"), indent=1)
    return cache[key]


def freq_stages(D, k=2, tail="classical"):
    """Frequency-specific constants c(delta) = Gamma_spec(delta) gamma delta^kappa at the stage bites (sjs_freq.S3),
    the classical constant beyond (tail)."""
    lam = 3
    delta0 = (D["rho"] - D["rhoinf"]) / (2 * lam)
    n, tau, kap = D["n"], int(D["tau"]), int(D["kappa"])
    gam = float(D["gamma"]); om = D["omega_star"]
    ccl = lambda d: T2.Fr(T2.sd.c_classical(n, tau, float(d)))
    cache = {}

    dmin = float(delta0) / 4                         # deepest bite with a computed S (cached)

    def cf(d):
        d = float(d)
        if tail == "freq" and d < dmin * (1 - 1e-12):
            return cf_est
        if d not in cache:
            S = S3_cached(om, d)
            G = TP ** -1 * 2 ** (n / 2) * math.sqrt(S)
            cache[d] = min(T2.Fr(G * gam * d ** kap), ccl(d))
        return cache[d]

    cf_est = None
    if tail == "freq":
        cf_est = max(cf(dmin), cf(2 * dmin))

    def st(s):
        ds = delta0 / 2 ** s
        r = D["rho"] - 2 * lam * delta0 * (1 - F(1, 2 ** s))
        return cf(ds), cf(ds / 2), ccl(min(r, F(1)))
    if tail == "freq":
        # ESTIMATE: the frequency-specific constant at the deepest computed bite, taken as uniform for every smaller bite
        # (S(delta) grows like delta^-3.3 on the computed bites, so c = Gamma gamma delta^kappa decreases for kappa >= 2);
        # this emulates a long prefix of sharp stages (FH's 10 Iterative-Lemma steps), it is not a proved bound
        return st, cf_est
    return st, ccl(delta0 / 2 ** k)


def route_b(D, which, k=2, free=True):
    th = F(1, 16)
    tail = "classical"
    if which.startswith("freq_tail"):
        k = int(which.split(":")[1]) if ":" in which else k
        which, tail = "freq", "freq"
    o = dict(keep_delta=True, avg_full_bite=True, theta=th, L1=True, cTh=D["cTh"], free_budgets=free)
    Dv = T2.with_caps(D, F(1, 20)) if free else D
    if which == "freq":
        st, ct = freq_stages(Dv, k, tail)
    else:
        st, ct = T2.c_stages(Dv, which)
    le, d0, why = T2.thresholdB(Dv, o, False, k if which != "v1" else 1, st, ct)
    return le, why


def main():
    out = {}
    print("| tau | gamma (FH units) | v0 | v1 | FH24 Thm 2.18 (--fh24 only) | v2 route B: v1 c_R | classical | frequency-specific (2 stages) | + frequency-specific tail (estimate) |")
    print("|---|---|---:|---:|---:|---:|---:|---:|---:|")
    for tau in (2, 3):
        for gname, gfh in (("1.69e-6 (FH)", FH["gamma"]), ("1.85e-5 (num.)", FH["gamma_num"])):
            a0, a1 = v0_v1(tau, gfh)
            f24 = float("nan")
            if "--fh24" in sys.argv:                      # slow (grid search); see the literature reproduction instead
                try:
                    f24 = lg(fh24_native(tau, gfh)["threshold_e"])
                except Exception as ex:                   # pragma: no cover
                    print("FH24 failed:", ex)
            D = sjs_package(tau, gfh)
            res = {}
            for which in ("v1", "classical", "freq", "freq_tail", "freq_tail:6", "freq_tail:10"):
                try:
                    res[which] = route_b(D, which)
                except Exception as ex:                   # pragma: no cover
                    res[which] = (float("nan"), [repr(ex)])
            print("| %d | %s | %.1f | %.1f | %.1f | %.1f | %.1f | %.1f (%s) | %.1f (%s) |" % (
                tau, gname, a0, a1, f24, res["v1"][0], res["classical"][0], res["freq"][0], ",".join(res["freq"][1][:2]),
                res["freq_tail"][0], ",".join(res["freq_tail"][1][:2])), flush=True)
            print("    k = 6 stages: %.1f (%s); k = 10 stages: %.1f (%s)" % (
                res["freq_tail:6"][0], ",".join(res["freq_tail:6"][1][:2]), res["freq_tail:10"][0],
                ",".join(res["freq_tail:10"][1][:2])), flush=True)
            out["tau%d/%s" % (tau, gname)] = dict(v0=a0, v1=a1, fh24=f24, v2B={k: v[0] for k, v in res.items()},
                                                  binding={k: v[1] for k, v in res.items()})
    if "--json" in sys.argv:
        json.dump(out, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1, default=str)


if __name__ == "__main__" and "--geff" not in sys.argv:
    main()


def gamma_eff_variant(tau, out=None):
    """ESTIMATE of lever L2 pushed through the whole theorem (weights and absorptions included): route B with the
    classical constants and gamma replaced by gamma_eff, the constant for which the classical small-divisor bound
    c_cl gamma^-1 delta0^-tau equals the frequency-specific Gamma_spec(delta0).  Not a theorem: an upper estimate of
    what a v2 whose weighted error uses Gamma_spec (not gamma delta^tau) could reach on this frequency vector."""
    D0 = sjs_package(tau, FH["gamma"])
    lam = 3
    delta0 = float((D0["rho"] - D0["rhoinf"]) / (2 * lam))
    S = S3_cached(D0["omega_star"], delta0)
    Gs = TP ** -1 * 2 ** 1.5 * math.sqrt(S)
    ccl = float(T2.sd.c_classical(3, tau, delta0))
    g_eff_p1 = ccl / (Gs * delta0 ** tau)
    D = sjs_package(tau, g_eff_p1 * TP)
    le, why = route_b(D, "classical", k=2)
    return dict(gamma_eff_p1=g_eff_p1, gamma_eff_FH=g_eff_p1 * TP, log10_threshold=le, binding=why)


if __name__ == "__main__" and "--geff" in sys.argv:
    for tau in (2, 3):
        r = gamma_eff_variant(tau)
        print("tau %d: gamma_eff (FH units) %.3e -> route B log10 threshold %.1f (%s)" % (
            tau, r["gamma_eff_FH"], r["log10_threshold"], ",".join(r["binding"][:2])))
