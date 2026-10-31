#!/usr/bin/env python3
"""SJS-PLAN: Fourier support of the coarse SJS torus (sjs_torus.py) in FH25's Delaunay chart and in a regular chart.

Untrusted design tooling.  S(L, rho) = #{k in the full lattice : max_components |c_k| e^{rho |k|_1} >= 10^-L max|c|}, 2 pi angles
(FH's rho).  Delaunay chart: K = (theta + u, L1, L2, Ghat).  Regular chart (normal-mode polar coordinates of the reduced
secular problem, the polar coordinates around the secular equilibrium instead of around e = 0):
  Poincare: z_i = sqrt(2 P_i) exp(i p_i), P_i = L_i - G_i, p_i = -g_i, lambda_i = l_i + g_i;
  w = Q^T z, Q a rotation by phi (phi chosen to minimize the variation of |w_6| on the torus; Laplace-Lagrange's modes);
  w_j = sqrt(2 I_j) exp(i psi_j);  a1 = lambda_1 + psi_5, a2 = lambda_2 + psi_5, a3 = psi_6 - psi_5, conjugate to
  (Lambda_1, Lambda_2, I_6), the fourth pair being the total angular momentum.
  With g2 = 0 (the reduced gauge) all of this is a function on the torus; the winding of (a1, a2, a3) in theta is an integer
  matrix.  The spectrum of the periodic parts is what the chart would give.
Also reports the box of the support in frames k -> F^-T k (Kronecker layout, beta = box/S) and the decay rates.
Usage: python3 -I scripts/sjs/plan/sjs_spectrum.py TORUS.npz [--json OUT]
"""
import json, math, os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sjs_torus as ST
sys.path.pop(0)


def fullspec(A):
    """A (m, N1, N2, N3) real periodic -> max over components of |c_k| / global max, on the fftshifted full lattice."""
    C = np.abs(np.fft.fftn(A, axes=(-3, -2, -1))) / np.prod(A.shape[1:])
    return C


def lattice(shape):
    ks = [np.fft.fftfreq(n, 1.0 / n) for n in shape]
    return np.meshgrid(*ks, indexing="ij")


def counts(Cmax, kk, Ls, rhos, cutoff):
    """S(L, rho) with coefficient normalized by the largest nonconstant coefficient; only |k_i| <= cutoff_i trusted."""
    k1 = np.abs(kk[0]) + np.abs(kk[1]) + np.abs(kk[2])
    m = Cmax.copy()
    m[0, 0, 0] = 0
    top = m.max()
    out = {}
    for rho in rhos:
        w = m * np.exp(rho * k1) / top
        out[rho] = [int(np.count_nonzero(w >= 10.0 ** -L)) for L in Ls]
    return out


def boxes(Cmax, kk, L, rho, frames):
    k1 = np.abs(kk[0]) + np.abs(kk[1]) + np.abs(kk[2])
    m = Cmax.copy(); m[0, 0, 0] = 0
    sel = m * np.exp(rho * k1) / m.max() >= 10.0 ** -L
    pts = np.stack([kk[i][sel] for i in range(3)])
    out = {}
    for name, G in frames.items():
        q = np.array(G) @ pts
        ext = q.max(axis=1) - q.min(axis=1) + 1
        out[name] = (int(pts.shape[1]), [int(x) for x in ext], float(np.prod(ext) / pts.shape[1]))
    return out


def robust_frames(Cmax, kk, L, rho, keep=0.995, emax=2):
    """the unimodular frame with entries <= emax minimizing the box of the kept set after dropping the outermost 1 - keep of it
    per axis pair (robust against stragglers near the numerical floor); returns the best few (frame = integer G, k' = G k)."""
    k1 = np.abs(kk[0]) + np.abs(kk[1]) + np.abs(kk[2])
    m = Cmax.copy(); m[0, 0, 0] = 0
    sel = m * np.exp(rho * k1) / m.max() >= 10.0 ** -L
    pts = np.stack([kk[i][sel] for i in range(3)])
    rng = range(-emax, emax + 1)
    rows = [np.array(r) for r in __import__("itertools").product(rng, rng, rng) if any(r)]
    q = (1 - keep) / 2 * 100
    ext = {}
    for r in rows:
        v = r @ pts
        ext[tuple(r)] = float(np.percentile(v, 100 - q) - np.percentile(v, q) + 1)
    best = []
    order = sorted(ext, key=ext.get)[:40]
    for a in order:
        for b in order:
            for c in order:
                G = np.array([a, b, c])
                if abs(round(np.linalg.det(G))) == 1:
                    best.append((ext[a] * ext[b] * ext[c] / pts.shape[1], G.tolist(), ext[a], ext[b], ext[c]))
    best.sort(key=lambda t: t[0])
    return pts.shape[1], best[:2]


def rates(Cmax, kk, shape):
    """per-axis decay rate of the maximal coefficient on |k_i| (FH-style marginal, per mode)."""
    r = []
    for ax in range(3):
        kv = np.abs(np.fft.fftfreq(shape[ax], 1.0 / shape[ax]))
        vals = sorted(set(kv))
        env = []
        for v in vals:
            env.append(np.max(np.take(Cmax, np.where(kv == v)[0], axis=ax)))
        env = np.array(env); vals = np.array(vals)
        ok = (env > 1e-9) & (vals >= 2)
        r.append(float(-np.polyfit(vals[ok], np.log(env[ok]), 1)[0]) if ok.sum() > 3 else float("nan"))
    return r


def regular_chart(u, gr, nphi=361):
    """the torus in normal-mode polar coordinates: periodic parts of (a1, a2, a3), Lambda1, Lambda2, I6."""
    th = gr.theta_chart()
    l1, l2, gh = u[0] + th[0], u[1] + th[1], u[2] + th[2]
    L1, L2, Gh = u[3], u[4], u[5]
    P1, P2 = L1 - Gh, L2 - (ST.GTOT - Gh)
    z1 = np.sqrt(2 * P1) * np.exp(-1j * gh)
    z2 = np.sqrt(2 * P2) + 0j
    best = None
    for phi in np.linspace(-math.pi / 2, math.pi / 2, nphi):
        c, s = math.cos(phi), math.sin(phi)
        w6 = -s * z1 + c * z2
        v = float(np.std(np.abs(w6) ** 2) / np.mean(np.abs(w6) ** 2))
        wmin = float(np.min(np.abs(w6)))
        w5 = c * z1 + s * z2
        if wmin > 0 and np.min(np.abs(w5)) > 0 and (best is None or v < best[0]):
            best = (v, phi)
    phi = best[1]
    c, s = math.cos(phi), math.sin(phi)
    w5, w6 = c * z1 + s * z2, -s * z1 + c * z2
    psi5, psi6 = np.angle(w5), np.angle(w6)
    # unwrap: psi_j = -(integer winding).theta + periodic
    def periodic_angle(w):
        """w = |w| exp(i (n.theta + q)): returns the integer n and the periodic q."""
        n = []
        for ax in range(3):
            d = np.angle(np.roll(w, -1, axis=ax) / w)
            n.append(int(np.rint(d.sum(axis=ax).mean() / (2 * math.pi))))
        phase = np.exp(1j * sum(n[i] * gr.th[i] for i in range(3)))
        r = w / phase
        m = np.mean(r / np.abs(r))
        m = m / abs(m)                            # center the branch, so that the periodic part does not wrap
        q = np.angle(r / m) + np.angle(m)
        return n, q
    n5, q5 = periodic_angle(w5)
    n6, q6 = periodic_angle(w6)
    a1 = u[0] + u[2] + q5                     # l1 + ghat + psi5 = theta1 + theta3 + u0 + u2 + n5.theta + q5
    a2 = u[1] + q5
    a3 = q6 - q5
    Iw6 = np.abs(w6) ** 2 / 2
    Iw5 = np.abs(w5) ** 2 / 2
    Pm = np.stack([a1, a2, a3, L1, L2, Iw6])
    F = np.array([[1 + n5[0], n5[1], 1 + n5[2]], [n5[0], 1 + n5[1], n5[2]],
                  [n6[0] - n5[0], n6[1] - n5[1], n6[2] - n5[2]]])
    return dict(P=Pm, phi=phi, I5=Iw5, I6=Iw6, n5=n5, n6=n6, F=F, q5=q5, q6=q6, rel_var_I6=best[0],
                e_range=[float(np.sqrt(2 * P1.min() / L1.mean())), float(np.sqrt(2 * P1.max() / L1.mean())),
                         float(np.sqrt(2 * P2.min() / L2.mean())), float(np.sqrt(2 * P2.max() / L2.mean()))])


def main():
    d = np.load(sys.argv[1])
    u = d["u"]
    shape = u.shape[1:]
    gr = ST.Grid(shape)
    kk = lattice(shape)
    Ls = [2, 4, 5, 6, 7, 8, 9, 10]
    rhos = [0.0, 0.02, 0.05, 0.1]
    C = fullspec(u)
    # scale the actions as a chart would (ell = 1e-3 of the torus's action variation is about 1): per-component relative
    Cm = np.max(C / np.max(C.reshape(6, -1)[:, 1:], axis=1).reshape(6, 1, 1, 1), axis=0)
    S = counts(Cm, kk, Ls, rhos, None)
    print("Delaunay: S(L) by rho (each component relative to its own largest nonconstant coefficient)")
    for r in rhos:
        print("  rho %.2f" % r, dict(zip(Ls, S[r])))
    print("  per-axis rates", ["%.3f" % x for x in rates(Cm, kk, shape)])
    frames = dict(delaunay=np.eye(3), mlong=[[1, 0, -1], [0, 1, 1], [0, 0, 1]], feas=[[1, 0, 0], [0, 1, 0], [-1, 0, 1]])
    for L in (6, 8):
        print("  boxes L", L, boxes(Cm, kk, L, 0.02, frames))
    R = regular_chart(u, gr)
    print("regular chart: phi %.4f, rel. var of I6 %.4f, winding n5 %s n6 %s, F %s" % (
        R["phi"], R["rel_var_I6"], R["n5"], R["n6"], R["F"].tolist()))
    print("  e1 range %.4f..%.4f, e2 range %.4f..%.4f" % tuple(R["e_range"]))
    print("  I5 range %.4e..%.4e, I6 range %.4e..%.4e" % (R["I5"].min(), R["I5"].max(), R["I6"].min(), R["I6"].max()))
    Cr = fullspec(R["P"])
    Crm = np.max(Cr / np.max(Cr.reshape(6, -1)[:, 1:], axis=1).reshape(6, 1, 1, 1), axis=0)
    S2 = counts(Crm, kk, Ls, rhos, None)
    for r in rhos:
        print("  rho %.2f" % r, dict(zip(Ls, S2[r])))
    print("  per-axis rates", ["%.3f" % x for x in rates(Crm, kk, shape)])
    for L in (6, 8):
        print("  boxes L", L, boxes(Crm, kk, L, 0.02, frames))
    Rs = []
    for lab, cm in (("delaunay", Cm), ("regular", Crm)):
        for L in (6, 8):
            r = robust_frames(cm, kk, L, 0.02)
            print("  robust frame", lab, "L", L, "S", r[0], "beta %.1f" % r[1][0][0], r[1][0][1], ["%.0f" % x for x in r[1][0][2:]])
            Rs.append((lab, L, r[0], r[1][0]))
    if "--json" in sys.argv:
        json.dump(dict(robust=Rs, Ls=Ls, delaunay={str(k): v for k, v in S.items()}, regular={str(k): v for k, v in S2.items()},
                       rates_del=rates(Cm, kk, shape), rates_reg=rates(Crm, kk, shape), phi=R["phi"], e_range=R["e_range"]),
                  open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1)


if __name__ == "__main__":
    main()
