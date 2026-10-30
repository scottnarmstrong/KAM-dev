#!/usr/bin/env python3
"""SJS-FEAS: the Fourier support of the planar Sun-Jupiter-Saturn perturbation in Delaunay angles (reproducible model).

Untrusted design tooling.  The planar three-body Hamiltonian of FH25 (2.1) in Poincare heliocentric variables, with the
Keplerian parametrization of each planet by its Delaunay angles: H1(l1, l2, g^) = |y1|^2/2 + |y2|^2/2 + y1.y2
- m1 m2 / |x1 - x2| (the mu-part), at the zeroth-order actions (a_i from the fast frequencies of FH25 (4.1) by Kepler's
third law, e1 = 0.0489, e2 = 0.0565), g2 = 0 and g1 = g^ (rotation invariance).  This is the source of every harmonic of
the torus at first order in mu (K1 = R_omega(...) has the same support pattern), so its coefficient geometry is a proxy
for the torus's.
Measured on an N^3 FFT grid (double precision, dynamic range ~1e-14):
  * the support count S_true(L, rho) = #{k : |c_k| e^{rho |k|_1} >= 10^-L max|c|} (frame-invariant);
  * FH-style per-axis marginal decay rates r_i (fits of the univariate sums, as FH25 Fig. 3) and the product-model
    count (4/3) prod_i (L ln 10 / (r_i - rho)) built from them (the model of sjs_support.py);
  * bounding boxes of the support in the Delaunay frame and in the d'Alembert-adapted frame
    (k1, k2, m) -> (k1, k2, m - k1) (angles l1 + g1 - ..., i.e. mean-longitude-type), box/support ratios;
  * the reversibility (real cosine/sine) halving.
Usage: python3 -I scripts/sjs/sjs_model_support.py [N] [--json OUT]
"""
import sys, json, math
import numpy as np

W = (8.39549288702546301204e-2, 3.38240117059304358259e-2)
M1, M2 = 0.9546, 0.2856
E1, E2 = 0.0489, 0.0565


def kepler(l, e):
    E = l.copy()
    for _ in range(30):
        E = E - (E - e * np.sin(E) - l) / (1 - e * np.cos(E))
    return E


def planet(l, a, e, m, g):
    """position and momentum (heliocentric Poincare) of a Keplerian orbit with mean anomaly l, argument g; G = 1, Sun
    mass 1, planet 'mass' m in the units of FH25 (2.1): H0 = |y|^2/(2m) - m/|x| -> mean motion a^{-3/2}."""
    E = kepler(l, e)
    q1 = a * (np.cos(E) - e); q2 = a * math.sqrt(1 - e * e) * np.sin(E)
    b = m * a ** -0.5                      # b = m^2 / L with L = m sqrt(a)
    p1 = -b * np.sin(E) / (1 - e * np.cos(E)); p2 = b * math.sqrt(1 - e * e) * np.cos(E) / (1 - e * np.cos(E))
    c, s = np.cos(g), np.sin(g)
    return (c * q1 - s * q2, s * q1 + c * q2), (c * p1 - s * p2, s * p1 + c * p2)


FLOOR = 1e-14


def model(N):
    a1, a2 = W[0] ** (-2 / 3), W[1] ** (-2 / 3)
    t = 2 * np.pi * np.arange(N) / N
    l1 = t[:, None, None]; l2 = t[None, :, None]; gh = t[None, None, :]
    x1, y1 = planet(l1 + 0 * gh, a1, E1, M1, gh)
    x2, y2 = planet(l2 + 0 * gh, a2, E2, M2, 0 * gh)
    dx = x1[0] - x2[0]; dy = x1[1] - x2[1]
    H1 = (y1[0] ** 2 + y1[1] ** 2) / 2 + (y2[0] ** 2 + y2[1] ** 2) / 2 + y1[0] * y2[0] + y1[1] * y2[1] \
        - M1 * M2 / np.sqrt(dx * dx + dy * dy)
    H1 = np.broadcast_to(H1, (N, N, N))
    C = np.fft.fftn(H1) / N ** 3
    return C, (a1, a2)


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 and sys.argv[1].isdigit() else 128
    C, (a1, a2) = model(N)
    k = np.fft.fftfreq(N, 1 / N).astype(int)
    K1, K2, K3 = np.meshgrid(k, k, k, indexing="ij")
    A = np.abs(C)
    A[0, 0, 0] = 0.0
    amax = A.max()
    rel = A / amax
    out = dict(N=N, a=(a1, a2), alpha=a1 / a2)
    print("model: a1 %.4f a2 %.4f alpha %.4f e (%.4f, %.4f); N = %d; max |c| %.3e" % (a1, a2, a1 / a2, E1, E2, N, amax))
    # per-axis marginal decay (FH25 Fig. 3 style): f_i(k_i) = sum over the other indices of |c|
    rates = []
    for ax, name in ((0, "l1"), (1, "l2"), (2, "g^")):
        marg = A.sum(axis=tuple(i for i in range(3) if i != ax))
        kk = np.fft.fftfreq(N, 1 / N).astype(int)
        sel = (np.abs(kk) >= 4) & (np.abs(kk) <= N // 2 - 8) & (marg > 1e-13 * marg.max())
        x = np.abs(kk[sel]); y = np.log(marg[sel])
        r = -np.polyfit(x, y, 1)[0]
        rates.append(r)
        print("marginal decay rate in %s: %.3f per mode (FH25 torus: l1 0.524, l2 0.417, g^ 0.316)" % (name, r))
    out["marginal_rates"] = rates
    n1 = np.abs(K1) + np.abs(K2) + np.abs(K3)
    out["counts"] = {}
    print("| rho | L | S_true | product model from the marginals | ratio | box (Delaunay) | box (adapted) |")
    print("|---:|---:|---:|---:|---:|---:|---:|")
    for rho in (0.0, 0.05, 0.1):
        wt = rel * np.exp(rho * n1)
        for L in (6, 8, 10, 12):
            m = (wt >= 10.0 ** (-L)) & (rel >= FLOOR)
            # trusted only if every coefficient that could matter at L digits is above the noise floor:
            # 10^-L e^{-rho |k|} >= FLOOR on the counted support
            trusted = bool(np.all(10.0 ** (-L) * np.exp(-rho * n1[m]) >= FLOOR)) if m.any() else True
            S = int(m.sum())
            prod = 4 / 3 * np.prod([L * math.log(10) / max(r - rho, 1e-9) for r in rates])
            kk1, kk2, kk3 = K1[m], K2[m], K3[m]
            boxD = (np.ptp(kk1) + 1) * (np.ptp(kk2) + 1) * (np.ptp(kk3) + 1)
            # d'Alembert-adapted frame: (k1, k2, m) -> (k1, k2, m - k1); also the 2:5 resonant shear on (k1, k2)
            boxA = (np.ptp(kk1) + 1) * (np.ptp(kk2) + 1) * (np.ptp(kk3 - kk1) + 1)
            print("| %.2f | %d | %d%s | %.3g | %.1f | %d | %d |" % (rho, L, S, "" if trusted else " (noise-limited)",
                                                               prod, prod / max(S, 1), boxD, boxA))
            out["counts"]["rho%.2f/L%d" % (rho, L)] = dict(S=S, product=prod, boxD=int(boxD), boxA=int(boxA),
                                                           trusted=trusted)
    # growth law S ~ L^p on the trusted rho = 0 counts (frame-invariant count; the strip weight is a separate factor)
    Ls = np.array([6, 8, 10, 12]); Ss = np.array([out["counts"]["rho0.00/L%d" % L]["S"] for L in Ls])
    p = np.polyfit(np.log(Ls), np.log(Ss), 1)
    out["fit_rho0"] = dict(exponent=p[0], prefactor=float(np.exp(p[1])))
    print("S_true(L) at rho = 0 ~ %.3g L^%.2f -> L = 30: %.2e, L = 54: %.2e (cubic extrapolation: %.2e, %.2e)" % (
        np.exp(p[1]), p[0], np.exp(p[1]) * 30 ** p[0], np.exp(p[1]) * 54 ** p[0],
        Ss[-1] * (30 / 12) ** 3, Ss[-1] * (54 / 12) ** 3))
    if "--json" in sys.argv:
        json.dump(out, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1, default=float)


if __name__ == "__main__":
    main()
