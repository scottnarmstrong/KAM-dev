#!/usr/bin/env python3
"""SJS-LG00: the invariant torus of LG00's secular model (11) with a frequency of the curve Gamma' (eq. 51).

Untrusted design tooling (double precision).  Steps:
1. Normal modes (lg00_model.normal_modes): eta = Q Y, xi = Q^{-T} X, then action-angle variables (LG00's (14))
   X_j = sqrt(2 I_j) cos phi_j, Y_j = sqrt(2 I_j) sin phi_j  (canonical: d phi ^ d I = d eta ^ d xi), so
       h(phi, I) = sum_{(m, k)} c_{m,k} (2 I_1)^{m_1/2} (2 I_2)^{m_2/2} cos(k . phi)
   -- LG00's form (15); the number of (m, k) terms is printed (129).  Terms with m_1, m_2 odd carry sqrt(I_1 I_2).
2. Frequency: omega = omega_2 (r, 1), r = (a + b g)/(c + d g), g = (sqrt 5 - 1)/2, omega_2 the centre of the
   Gamma' range (rad/year).
3. Torus K(theta) = (theta + u(theta), I0 + v(theta)) on an N x N grid of 2 pi-periodic angles, Newton step of the
   parameterization method (Haro-Luque frame P = [L, N], N = J L (L^T L)^{-1}, torsion block T of
   P^{-1}(DX_h P - d_omega P); the small blocks are dropped, so convergence is quasi-quadratic).  Initial guess:
   I0 from the averaged Hamiltonian, then continuation h_eps = <h> + eps (h - <h>), eps = 0.25, 0.5, 0.75, 1.
4. Output: Fourier coefficients of u, v (npz), decay profile max|c_k| per |k|_1, the residual.

Usage: python3 -I lg00_torus.py [N] [--out results/lg00_torus_N.npz]
"""
import os, sys, math, json, itertools
import numpy as np
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lg00_data as D          # noqa: E402
import lg00_model as M         # noqa: E402

KM = 6                          # max trigonometric degree per angle


def poly_subst(terms, Q):
    """H'(X, Y) = H(Q^{-T} X, Q Y) as {(a1, a2, b1, b2): coeff} (float), exponents of X1 X2 Y1 Y2."""
    Qit = np.linalg.inv(Q).T
    lin = [{(1, 0, 0, 0): Qit[i, 0], (0, 1, 0, 0): Qit[i, 1]} for i in range(2)] + \
          [{(0, 0, 1, 0): Q[i, 0], (0, 0, 0, 1): Q[i, 1]} for i in range(2)]

    def mul(p, q):
        r = {}
        for e1, c1 in p.items():
            for e2, c2 in q.items():
                e = tuple(a + b for a, b in zip(e1, e2))
                r[e] = r.get(e, 0.0) + c1 * c2
        return r
    out = {}
    for c, e in terms:
        p = {(0, 0, 0, 0): float(c)}
        for i in range(4):
            for _ in range(e[i]):
                p = mul(p, lin[i])
        for k, v in p.items():
            out[k] = out.get(k, 0.0) + v
    return out


def trig_coeffs(a, b):
    """cos^a x sin^b x = sum_k t[k] e^{i k x}, k = -(a+b)..(a+b) (array index k + KM)."""
    t = np.zeros(2 * KM + 1, complex); t[KM] = 1.0
    cs = np.zeros(2 * KM + 1, complex); cs[KM - 1] = cs[KM + 1] = 0.5
    sn = np.zeros(2 * KM + 1, complex); sn[KM + 1] = 1 / 2j; sn[KM - 1] = -1 / 2j
    for f, n in ((cs, a), (sn, b)):
        for _ in range(n):
            t = np.convolve(t, f)[KM:KM + 2 * KM + 1]
    return t


def action_angle_form(Q):
    """{(m1, m2): C} with C[k1 + KM, k2 + KM] the coefficient of (2I1)^{m1/2} (2I2)^{m2/2} e^{i k.phi}."""
    Hp = poly_subst(D.coeffs(), Q)
    out = {}
    for (a1, a2, b1, b2), c in Hp.items():
        if abs(c) < 1e-300:
            continue
        m = (a1 + b1, a2 + b2)
        t = np.outer(trig_coeffs(a1, b1), trig_coeffs(a2, b2)) * c
        out[m] = out.get(m, 0) + t
    return out


class AAHam:
    """h(phi, I) and derivatives from the action-angle form; phi 2 pi-periodic (any shape (..., 2) arrays)."""

    def __init__(self, form, eps=1.0):
        self.form = {}
        for m, C in form.items():
            C = C.copy()
            if eps != 1.0:
                C0 = C[KM, KM]
                C *= eps; C[KM, KM] = C0
            self.form[m] = C
        ks = np.arange(-KM, KM + 1)
        self.k1, self.k2 = np.meshgrid(ks, ks, indexing="ij")

    def count_terms(self, tol=1e-30):
        """number of real cosine terms (m, k ~ -k) with nonzero coefficient, and the largest sine part."""
        n, smax = 0, 0.0
        for m, C in self.form.items():
            for i in range(2 * KM + 1):
                for j in range(2 * KM + 1):
                    k = (i - KM, j - KM)
                    if k < (0, 0):
                        continue
                    if abs(C[i, j]) > tol * 1e-8:
                        n += 1
                    smax = max(smax, abs(C[i, j].imag))
        return n, smax

    def derivs(self, phi, I, order=2):
        """h, grad (4), Hessian (4x4) [, third derivatives (4x4x4)] at points (phi, I) (..., 2)."""
        sh = phi.shape[:-1]
        E = {}
        ph = np.exp(1j * (np.multiply.outer(phi[..., 0], np.arange(-KM, KM + 1))))      # (..., 13)
        ph2 = np.exp(1j * (np.multiply.outer(phi[..., 1], np.arange(-KM, KM + 1))))
        R2 = 2 * I                                                                       # (..., 2)
        nd = 4
        h = np.zeros(sh, complex)
        g = np.zeros(sh + (nd,), complex)
        Hs = np.zeros(sh + (nd, nd), complex)
        T3 = np.zeros(sh + (nd, nd, nd), complex) if order >= 3 else None
        ks = np.arange(-KM, KM + 1)
        for (m1, m2), C in self.form.items():
            # angular part and its phi-derivatives: F_{ab} = sum C (i k1)^a (i k2)^b e^{ik.phi}
            def Fab(a, b):
                Cw = C * (1j * ks[:, None]) ** a * (1j * ks[None, :]) ** b
                return np.einsum("...i,ij,...j->...", ph, Cw, ph2)
            # radial part P = (2I1)^{m1/2} (2I2)^{m2/2} and its I-derivatives
            def Pd(d1, d2):
                f = np.ones(sh, complex)
                for (mm, dd, j) in ((m1, d1, 0), (m2, d2, 1)):
                    coef = 1.0
                    e = mm / 2
                    for t in range(dd):
                        coef *= 2 * (e - t)
                    f = f * coef * np.asarray(R2[..., j], complex) ** (e - dd)
                return f
            idx = list(itertools.product(range(4), repeat=1))
            # derivative multi-index -> (a1, a2 on phi; d1, d2 on I)
            def term(ix):
                a = [0, 0, 0, 0]
                for i in ix:
                    a[i] += 1
                return Fab(a[0], a[1]) * Pd(a[2], a[3])
            cache = {}
            def T(ix):
                key = tuple(sorted(ix))
                if key not in cache:
                    cache[key] = term(key)
                return cache[key]
            h = h + T(())
            for i in range(4):
                g[..., i] += T((i,))
                for j in range(4):
                    Hs[..., i, j] += T((i, j))
                    if order >= 3:
                        for l in range(4):
                            T3[..., i, j, l] += T((i, j, l))
        return (h, g, Hs, T3) if order >= 3 else (h, g, Hs)


J4 = np.block([[np.zeros((2, 2)), np.eye(2)], [-np.eye(2), np.zeros((2, 2))]])     # X_h = J grad h, (phi, I)


def frequency():
    g = (math.sqrt(5) - 1) / 2
    G = D.GAMMA_P
    r = (G["a"] + G["b"] * g) / (G["c"] + G["d"] * g)
    w2 = float(G["omega2"])
    return np.array([r * w2, w2])


class Grid:
    def __init__(self, N):
        self.N = N
        th = 2 * np.pi * np.arange(N) / N
        self.t1, self.t2 = np.meshgrid(th, th, indexing="ij")
        k = np.fft.fftfreq(N, 1 / N)
        self.k1, self.k2 = np.meshgrid(k, k, indexing="ij")

    def dth(self, f, om):
        """d_omega f (spectral), f real (N, N, ...)."""
        Fh = np.fft.fft2(f, axes=(0, 1))
        mult = 1j * (om[0] * self.k1 + om[1] * self.k2)
        return np.fft.ifft2(Fh * mult[(...,) + (None,) * (f.ndim - 2)], axes=(0, 1)).real

    def d(self, f, j):
        Fh = np.fft.fft2(f, axes=(0, 1))
        mult = 1j * (self.k1 if j == 0 else self.k2)
        return np.fft.ifft2(Fh * mult[(...,) + (None,) * (f.ndim - 2)], axes=(0, 1)).real

    def filt(self, f, frac=1 / 3):
        Fh = np.fft.fft2(f, axes=(0, 1))
        m = (np.abs(self.k1) > frac * self.N) | (np.abs(self.k2) > frac * self.N)
        Fh[m] = 0
        return np.fft.ifft2(Fh, axes=(0, 1)).real

    def solve(self, f, om):
        """d_omega^{-1} of a zero-average f, zero-average solution."""
        Fh = np.fft.fft2(f, axes=(0, 1))
        mult = 1j * (om[0] * self.k1 + om[1] * self.k2)
        mult[0, 0] = 1.0
        S = Fh / mult[(...,) + (None,) * (f.ndim - 2)]
        S[0, 0] = 0
        return np.fft.ifft2(S, axes=(0, 1)).real


def residual(Hm, G, om, u, v, I0):
    phi = np.stack([G.t1 + u[..., 0], G.t2 + u[..., 1]], -1)
    I = I0 + v
    h, g, Hs = Hm.derivs(phi, I)
    g, Hs = g.real, Hs.real
    XH = np.einsum("ab,...b->...a", J4, g)
    Kt = np.concatenate([u, v], -1)
    dK = G.dth(Kt, om)
    dK[..., 0] += om[0]; dK[..., 1] += om[1]
    return XH - dK, g, Hs, h.real


def newton_step(Hm, G, om, u, v, I0):
    E, g, Hs, h = residual(Hm, G, om, u, v, I0)
    Kt = np.concatenate([u, v], -1)
    L = np.zeros(Kt.shape[:2] + (4, 2))
    for j in range(2):
        L[..., :, j] = G.d(Kt, j)
        L[..., j, j] += 1.0
    B = np.linalg.inv(np.einsum("...ki,...kj->...ij", L, L))
    N = np.einsum("ab,...bk,...kj->...aj", J4, L, B)
    P = np.concatenate([L, N], -1)
    Pi = np.linalg.inv(P)
    DX = np.einsum("ab,...bc->...ac", J4, Hs)
    dN = G.dth(N.reshape(N.shape[:2] + (8,)), om).reshape(N.shape)
    Tm = np.einsum("...ab,...bc->...ac", Pi, np.einsum("...ab,...bc->...ac", DX, N) - dN)[..., :2, :]
    eta = np.einsum("...ab,...b->...a", Pi, E)           # dK = P xi: d_om xi = [[0, T], [0, 0]] xi + P^{-1} E
    etaL, etaN = eta[..., :2], eta[..., 2:]
    xiN = G.solve(etaN - etaN.mean(axis=(0, 1)), om)
    rhs = etaL + np.einsum("...ab,...b->...a", Tm, xiN)
    Tavg = Tm.mean(axis=(0, 1))
    xiN0 = np.linalg.solve(Tavg, -rhs.mean(axis=(0, 1)))
    xiN = xiN + xiN0
    rhs = etaL + np.einsum("...ab,...b->...a", Tm, xiN)
    xiL = G.solve(rhs - rhs.mean(axis=(0, 1)), om)
    xi = np.concatenate([xiL, xiN], -1)
    dK = np.einsum("...ab,...b->...a", P, xi)
    u2 = u + dK[..., :2]
    v2 = v + dK[..., 2:]
    # renormalise: zero-average angle displacement (phase), the action average goes into I0
    u2, v2 = G.filt(u2), G.filt(v2)                       # 1/3 cut against aliasing
    u2 = u2 - u2.mean(axis=(0, 1))
    I0n = I0 + v2.mean(axis=(0, 1))
    v2 = v2 - v2.mean(axis=(0, 1))
    return u2, v2, I0n, np.abs(E).max(), Tavg


def averaged_I0(form, om, I_start):
    Hm = AAHam(form)
    I = np.array(I_start, float)
    phis = np.zeros((1, 2))
    for _ in range(50):
        # averaged gradient: k = 0 coefficients only
        h0 = {m: C[KM:KM + 1, KM:KM + 1] for m, C in form.items()}
        A0 = AAHam({m: np.pad(c, KM) for m, c in h0.items()})
        _, g, Hs = A0.derivs(phis, I[None, :])
        F_ = g[0, 2:].real - om
        J_ = Hs[0, 2:, 2:].real
        dI = np.linalg.solve(J_, -F_)
        I = I + dI
        if np.abs(dI).max() < 1e-18:
            break
    return I


def solve_torus(N=64, log=print, eps_list=(0.25, 0.5, 0.75, 1.0), iters=12):
    Q, lam = M.normal_modes()
    form = action_angle_form(Q)
    om = frequency()
    I0 = averaged_I0(form, om, [6.5e-4, 3.2e-4])
    log("frequency omega = %s rad/yr; averaged I0 = %s" % (om, I0))
    G = Grid(N)
    u = np.zeros((N, N, 2)); v = np.zeros((N, N, 2))
    for eps in eps_list:
        Hm = AAHam(form, eps)
        best = None
        for it in range(iters):
            u2, v2, I02, err, Tavg = newton_step(Hm, G, om, u, v, I0)
            log("  eps %.2f it %2d  |E(before step)| = %.3e  I0 = %s" % (eps, it, err, I02))
            if best is not None and err >= 0.5 * best:
                break                                       # stagnation: keep the previous iterate
            best = err
            u, v, I0 = u2, v2, I02
    E, g, Hs, h = residual(AAHam(form), G, om, u, v, I0)
    return dict(Q=Q, lam=lam, form=form, om=om, I0=I0, u=u, v=v, N=N, err=float(np.abs(E).max()),
                energy=float(h.mean()), Tavg=Tavg)


def decay_profile(f):
    """max |c_k| per |k|_1 of a real grid function (N, N)."""
    N = f.shape[0]
    C = np.fft.fft2(f) / N ** 2
    k = np.fft.fftfreq(N, 1 / N).astype(int)
    k1, k2 = np.meshgrid(k, k, indexing="ij")
    n1 = np.abs(k1) + np.abs(k2)
    out = []
    for s in range(0, N // 2):
        msk = n1 == s
        out.append(float(np.abs(C[msk]).max()) if msk.any() else 0.0)
    return np.array(out)


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 and sys.argv[1].isdigit() else 64
    Q, lam = M.normal_modes()
    form = action_angle_form(Q)
    nterm, smax = AAHam(form).count_terms()
    print("action-angle form (15): %d cosine terms (m, k); largest sine part %.1e" % (nterm, smax))
    T = solve_torus(N)
    print("final |E|_grid = %.3e, energy <h(K)> = %.17e" % (T["err"], T["energy"]))
    print("Tavg (torsion, rad/yr / action) =\n%s" % T["Tavg"])
    prof = {}
    for name, f in (("u1", T["u"][..., 0]), ("u2", T["u"][..., 1]), ("v1", T["v"][..., 0]), ("v2", T["v"][..., 1])):
        p = decay_profile(f)
        prof[name] = p.tolist()
    mx = np.max([prof[k] for k in prof], axis=0)
    print("max |c_k| over u, v (v relative to I0) per |k|_1:")
    vrel = np.max([np.array(prof["v1"]) / T["I0"][0], np.array(prof["v2"]) / T["I0"][1]], axis=0)
    for s in range(0, len(mx), 2):
        print("  |k|_1 = %3d   u %.2e   v/I0 %.2e" % (s, max(prof["u1"][s], prof["u2"][s]), vrel[s]))
    out = sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else os.path.join(
        HERE, "results", "lg00_torus_N%d.npz" % N)
    np.savez(out, u=T["u"], v=T["v"], I0=T["I0"], om=T["om"], Q=T["Q"], lam=T["lam"], err=T["err"],
             energy=T["energy"], Tavg=T["Tavg"])
    print("saved", out)


if __name__ == "__main__":
    main()
