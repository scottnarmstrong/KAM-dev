#!/usr/bin/env python3
"""SJS-FEAS: Fourier support of the SJS torus as a function of the theorem threshold, strip and representation.

Untrusted design tooling.  Decay model from FH25 Fig. 3 (fits of the coefficient decay per angle, 2 pi angles):
|K_k| ~ exp(-sum_i r_i |k_i|) with r = (0.524, 0.417, 0.316) for (l1, l2, g-hat).  On the strip rho (FH units) the
certificate keeps k with sum_i (r_i - rho)|k_i| <= L ln 10 (weighted size >= 10^-L): a cross-polytope with semi-axes
A_i = L ln 10/(r_i - rho), S = (4/3) A1 A2 A3 (lattice-point count ~ volume; it is frame-invariant), against the box
8 A1 A2 A3 (FFT grids; packed layouts) -- box/support = 6.  Truncation digits for a threshold T: the invariance error
of the truncated torus is ~ 10^{-L + c0} (c0 = 4 covers the edge-term count, derivatives and the composition); with
2 orders of headroom L = -log10 T + 2 + c0.  Bits = 3.33 L + 24 (SO-GEN2's rule).
Threshold dependence on the strip: T(rho) = T(0.1) (rho/0.1)^p with p the delta-power of the smallness condition
(delta = rho/6): v1 p = 4 tau (+ the gamma-free part), route B (FH24 structure) p = tau + 1 for the tangential and
2 tau + 1 for the normal component; we use p = 2 tau + 1 = 5.8 (conservative) for route B and 4 tau = 9.6 for v1.
Usage: python3 -I scripts/sjs/sjs_support.py [--json OUT]
"""
import sys, json, math

R = (0.524, 0.417, 0.316)
LN10 = math.log(10)


def support(L, rho, r=R):
    A = [L * LN10 / (ri - rho) for ri in r]
    S = 4.0 / 3.0 * A[0] * A[1] * A[2]
    return S, A, 8 * A[0] * A[1] * A[2]


def digits(logT, c0=4.0, head=2.0):
    return -logT + head + c0


def best_rho(logT01, p, rhos=None):
    """minimize S over the strip: T(rho) = T(0.1) (rho/0.1)^p."""
    rhos = rhos or [0.01 * i for i in range(1, 30)]
    best = None
    for rho in rhos:
        lt = logT01 + p * math.log10(rho / 0.1)
        L = digits(lt)
        S, A, box = support(L, rho)
        if best is None or S < best[1]:
            best = (rho, S, L, A, box, lt)
    return best


def main():
    out = {}
    print("Support of the SJS torus (cross-polytope count) at strip rho = 0.1 (FH units):")
    print("| L (digits) | S | box | max |k| (l1, l2, g) |")
    print("|---:|---:|---:|---|")
    for L in (20, 30, 40, 54, 80, 120, 140):
        S, A, box = support(L, 0.1)
        print("| %d | %.2e | %.2e | %s |" % (L, S, box, [round(a) for a in A]))
        out["L%d" % L] = dict(S=S, box=box, A=A)
    print("\nPer theorem (threshold at rho = 0.1 -> strip-optimized):")
    rows = [("v1 (one M)", -130.0, 9.6), ("FH24-type, as FH25 report (eta^L)", -38.0, 5.8),
            ("route B + L2 (freq.-specific) estimate", None, 5.8)]
    for name, lt, p in rows:
        if lt is None:
            continue
        rho, S, L, A, box, lt2 = best_rho(lt, p)
        S01, _, _ = support(digits(lt), 0.1)
        print("%-40s T(0.1) 1e%.0f: L %.0f S %.2e at rho 0.1; best rho %.2f: log T %.1f L %.0f S %.2e (bits %d)" % (
            name, lt, digits(lt), S01, rho, lt2, L, S, 3.33 * L + 24))
        out[name] = dict(S_rho01=S01, best_rho=rho, S=S, L=L, logT=lt2)
    print("\nS as a function of log10 T (best strip, route-B delta power p = 5.8):")
    for lt in (-60, -50, -44, -38, -30, -25, -20, -15):
        rho, S, L, A, box, lt2 = best_rho(lt, 5.8)
        print("  log T(0.1) %d: best rho %.2f, L %.0f, S %.2e, half-lattice (reversibility) %.2e" % (lt, rho, L, S, S / 2))
    if "--json" in sys.argv:
        json.dump(out, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1)


if __name__ == "__main__":
    main()
