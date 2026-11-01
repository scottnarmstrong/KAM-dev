#!/usr/bin/env python3
"""V2-ENERGY step 1: the isoenergetic energy-row bound (docs/campaign/studies/V2-ENERGY-ROW.md).

Untrusted tooling, report only.  The energy row of the bordered torsion, Y = DH(K) N, needs a bound y0 of its row sum.
Route B's checker fixes y0 = M s_N with the one-size M; route A refined already has HY = dh s_N, with dh the certified
gradient sum of `checkHamClaim`.  This script measures, with the exact route-B and route-A mirrors, what each candidate
for the gradient bound is worth, changing nothing else:
    M        the one-size bound (route B today);
    dh       the certified sum of `hamClaimOk` (the claim of the landed certificates);
    sampled  the sup over D of the gradient sum, a floor for any pass over D (not a bound);
    omega    y0 = |s omega*|_1, the value of the row on an exact torus (Y = omega^T - (eta^L)^T), a floor for y0 itself.

Packages: the two lunar N = 65 band tori, and LG00 T' on the exact energy (LG00-T2's dry run, copied to
docs/campaign/studies/v2-energy-data/; KAM_LG00_TP overrides it).

Usage: python3 -B -I scripts/apost_sharp/energy_row.py [--json OUT]
"""
import json, math, os, sys
from fractions import Fraction as F

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import structured_b as SB   # noqa: E402

TP_JSON = os.environ.get("KAM_LG00_TP", os.path.join(SB.ROOT, "docs/campaign/studies/v2-energy-data/dry_tp_L20.json"))


def lg00_tp(B):
    """The T' package: parameters and claim of the exact-energy dry run, on the chart and box of the child."""
    rep = json.load(open(TP_JSON))
    q = {k: F(v) for k, v in rep["params"].items()}
    B = dict(B, claim={k: F(v) for k, v in rep["claim"].items()}, params=rep["params"])
    pkg = SB.lg00_pkg(B)
    pkg["p"] = dict(q, tau=1, kappa=F(160000))
    pkg["tag"] = "LG00 T' L=20"
    return B, pkg


def freq_sites(p, om, kp, margin=1.01):
    """Frequency-specific site constants for route A, as v2_r2.site_constants (float c_freq x margin)."""
    import v2_q as VQ
    import smalldiv as SD
    d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    gam = float(p["gamma"])
    out = {}
    for s in range(kp):
        d = float(F(1, 2) ** s * d0)
        r = float(min(p["rho"] - 6 * d0 * (1 - F(1, 2) ** s), F(1)))
        out[("d", s)] = VQ.up(SD.c_freq(om, gam, 1, d)[0] * margin, 4)
        out[("b", s)] = VQ.up(SD.c_freq(om, gam, 1, r)[0] * margin, 4)
    return out


def with_mu(pkg, mu):
    """The package at another mu: the what-if of a free parameter, the claims as they are."""
    return dict(pkg, p=dict(pkg["p"], mu=mu))


def route_a_table(pkg, sites_tab):
    """log10 e* of route A refined for each gradient bound in HY = Mh1 s_N."""
    R, p = pkg["R"], pkg["p"]
    return {name: SB.route_a(dict(pkg, R=dict(R, dh=v)), sites_tab) for name, v in pkg["Mh1s"].items()}


def main():
    RB, T2 = SB.setup_mirror()
    res = {}
    data = [("lower", SB.lunar_bounds("lower")), ("upper", SB.lunar_bounds("upper")), ("tp", SB.lg00_bounds())]
    for tag, B in data:
        if tag == "tp":
            B, pkg = lg00_tp(B)
        else:
            pkg = SB.lunar_pkg(tag, B)
        p, R, S = pkg["p"], pkg["R"], B["sums"]
        omega1 = sum(abs(F(c)) for c, _ in pkg["box"]) * p["s"]
        sN = R["bN"] * F(21, 20)
        grad = F(B["sampled"][3]).limit_denominator(10 ** 9)
        assert grad <= S["dh"] <= R["dh"], "a sampled gradient above the certified sum"
        pkg["Mh1s"] = dict(M=p["M"], dh=R["dh"], sampled=grad, omega=omega1 / sN)
        print("\n== %s: M %.6g, certified dh %.6g (claim %.6g), sampled gradient %.6g; |s omega*|_1 %.6g, s_N cap %.5g; "
              "y0 = M s_N %.5g, dh s_N %.5g" % (tag, float(p["M"]), float(S["dh"]), float(R["dh"]), float(grad),
                                               float(omega1), float(sN), float(p["M"] * sN), float(R["dh"] * sN)),
              flush=True)
        c0, d0 = 2 * R["dx"], 2 * R["d2x"]
        err = float(p["err"]) if p.get("err") else {"lower": 16e-17, "upper": 183e-18}.get(tag)
        lerr = math.log10(err)
        cases = [("y0 = %s s_N" % k, c0, d0, v) for k, v in pkg["Mh1s"].items()]
        cases.append(("y0 = dh s_N, structured cTh", B["sums"]["cTh"], d0, R["dh"]))
        out = dict(M=float(p["M"]), dh=float(R["dh"]), dh_exact=float(S["dh"]), sampled=float(grad), omega1=float(omega1),
                   sN=float(sN), log10_err=lerr, route_b={}, route_a={})
        for sites in ("classical", "freq"):
            rows = SB.evaluate(pkg, sites, cases, RB, T2)
            out["route_b"][sites] = rows
            print("-- route B, %s sites, kp = 5 (log10 err %.2f)" % (sites, lerr))
            for r in rows:
                print("  %-30s t %8.5g  log10 e* %8.3f (%+.3f)  margin %8.3g  disp %.3g  binding %s" % (
                    r["case"], r["t"], r["log10_e"], r["log10_e"] - rows[0]["log10_e"], 10 ** (r["log10_e"] - lerr),
                    r["disp"], ", ".join(r["binding"][:6])), flush=True)
        st = SB.classical_sites(p, 3)
        out["route_a"]["classical"] = route_a_table(pkg, st)
        sf = freq_sites(p, pkg["omega"], 3)
        out["route_a"]["freq"] = route_a_table(pkg, sf)
        for k, v in out["route_a"].items():
            print("-- route A refined, %s sites, kp = 3: " % k + ", ".join(
                "%s %.3f (margin %.3g)" % (a, b, 10 ** (b - lerr)) for a, b in v.items()), flush=True)
        if tag == "tp":
            out["mu"] = {}
            for mu in (F(1, 10 ** 4), F(1, 10 ** 3)):
                q = with_mu(pkg, mu)
                rows = SB.evaluate(q, "classical", cases[:2], RB, T2)
                rf = SB.evaluate(q, "freq", cases[:2], RB, T2)
                out["mu"][str(mu)] = dict(b_classical=rows, b_freq=rf,
                                          a_classical=SB.route_a(dict(q, R=dict(R)), SB.classical_sites(q["p"], 3)))
                print("-- mu = %s: route B M %.3f, dh %.3f (classical); M %.3f, dh %.3f (freq); route A classical %.3f; "
                      "binding %s" % (mu, rows[0]["log10_e"], rows[1]["log10_e"], rf[0]["log10_e"], rf[1]["log10_e"],
                                      out["mu"][str(mu)]["a_classical"], rows[1]["binding"]), flush=True)
        res[tag] = out
    if "--json" in sys.argv:
        json.dump(res, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1, default=str)
    return 0


if __name__ == "__main__":
    sys.exit(main())
