#!/usr/bin/env python3
"""SJS-LG00: the secular Hamiltonian (11) of LG00 -- evaluation, normal modes, and checks against the paper.

Untrusted design tooling (double precision).  Conventions:
- z = (xi1, xi2, eta1, eta2).  The canonical pairs are (eta_j, xi_j) with eta the coordinate: LG00's (2) has
  xi = sqrt(2P) cos p, eta = sqrt(2P) sin p with p = -varpi, P = Lambda (1 - sqrt(1 - e^2)), and
  d eta ^ d xi = dp ^ dP.  Hamilton:  eta' = dH/dxi,  xi' = -dH/deta.  With (14) xi' = sqrt(2I) cos phi,
  eta' = sqrt(2I) sin phi this gives phi' = dH/dI, negative here (the quadratic part is negative definite), as the
  paper's frequencies.
- Normal modes: eta = Q Y, xi = Q^{-T} X (canonical), H2 = sum_j lam_j (X_j^2 + Y_j^2)/2, lam_j < 0, mode 0 the
  Jupiter-like one (|lam_0| < |lam_1|).

Checks (python3 -I lg00_model.py):
  E      H(Table 3) against eq. (52);
  freq   integrate (11) from Table 3 (RK4), frequency analysis (Hann window, refined peak) of the normal-mode signals,
         against eq. (12);
  omega' the two orbits of sect. 4.3 (xi1, eta1 scaled by 1 +- 0.02, (xi2, eta2) scaled to keep the energy), against
         omega' and omega'';
  table4 the linear actions of Table 3 against Table 4's I (which also includes the Birkhoff step: O(e^2) relative).
"""
import os, sys, math, json
import numpy as np
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lg00_data as D   # noqa: E402

ARC = math.pi / 648000


class Poly:
    """sum c_m z^{E_m} in 4 variables (numpy; complex arguments allowed)."""

    def __init__(self, terms):
        self.c = np.array([float(c) for c, _ in terms])
        self.E = np.array([e for _, e in terms], dtype=np.int64)
        self.terms = terms

    def eval(self, z):
        """z: (..., 4) -> (...), vectorized over the monomials."""
        z = np.asarray(z)
        P = [np.ones_like(z)]
        for _ in range(int(self.E.max()) if len(self.E) else 0):
            P.append(P[-1] * z)
        P = np.stack(P)                                       # (d+1, ..., 4)
        mon = np.ones((len(self.c),) + z.shape[:-1], dtype=np.result_type(z, float))
        for i in range(4):
            mon = mon * P[self.E[:, i], ..., i]
        return np.tensordot(self.c, mon, axes=(0, 0))

    def deriv(self, idx):
        """partial derivative along the multi-index idx (tuple of variable indices)."""
        terms = []
        for c, e in self.terms:
            e = list(e); c = F(c)
            ok = True
            for i in idx:
                if e[i] == 0:
                    ok = False; break
                c *= e[i]; e[i] -= 1
            if ok:
                terms.append((c, tuple(e)))
        return Poly(terms) if terms else Poly([(F(0), (0, 0, 0, 0))])

    def grad_fns(self):
        return [self.deriv((i,)) for i in range(4)]


H = Poly(D.coeffs())
G = H.grad_fns()


def rhs(z):
    g = [Gi.eval(z) for Gi in G]
    return np.array([-g[2], -g[3], g[0], g[1]])      # xi' = -dH/deta, eta' = dH/dxi


def quad_blocks():
    A = np.zeros((2, 2)); B = np.zeros((2, 2))
    for c, e in D.coeffs():
        if sum(e) != 2:
            continue
        c = float(c)
        xi, et = e[:2], e[2:]
        if sum(xi) == 2:
            i, j = [k for k in range(2) for _ in range(xi[k])]
            A[i, j] += c if i != j else 2 * c
            if i != j:
                A[j, i] += c
        else:
            i, j = [k for k in range(2) for _ in range(et[k])]
            B[i, j] += c if i != j else 2 * c
            if i != j:
                B[j, i] += c
    return A, B                       # H2 = xi^T A xi / 2 + eta^T B eta / 2


def normal_modes():
    """Q, lam with eta = Q Y, xi = Q^{-T} X, H2 = sum lam_j (X_j^2 + Y_j^2)/2."""
    A, B = quad_blocks()
    Ah, Bh = -A, -B                                   # positive definite
    C = np.linalg.cholesky(Bh).T                      # Bh = C^T C
    S = C @ Ah @ C.T
    d, R = np.linalg.eigh(S)
    order = np.argsort(d)                             # |lam| increasing: Jupiter-like mode first
    d, R = d[order], R[:, order]
    for j in range(2):                                # sign convention: positive diagonal of R
        if R[j, j] < 0:
            R[:, j] = -R[:, j]
    Q = np.linalg.inv(C) @ R @ np.diag(d ** 0.25)
    lam = -np.sqrt(d)
    return Q, lam


def to_modes(z, Q):
    xi, eta = z[:2], z[2:]
    X = Q.T @ xi                                      # xi = Q^{-T} X  ->  X = Q^T xi
    Y = np.linalg.solve(Q, eta)
    return X, Y


def rk4(z0, h, nsteps, every):
    z = np.array(z0, float)
    out = [z.copy()]
    for n in range(nsteps):
        k1 = rhs(z); k2 = rhs(z + h / 2 * k1); k3 = rhs(z + h / 2 * k2); k4 = rhs(z + h * k3)
        z = z + h / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
        if (n + 1) % every == 0:
            out.append(z.copy())
    return np.array(out)


def naff_peak(sig, dt, guess=None):
    """frequency (rad/time) of the dominant line of a complex signal: Hann window, FFT peak, golden refinement."""
    N = len(sig)
    t = np.arange(N) * dt
    w = 1 - np.cos(2 * np.pi * np.arange(N) / N)
    if guess is None:
        Fk = np.fft.fft(sig * w)
        k = int(np.argmax(np.abs(Fk)))
        nu0 = 2 * np.pi * np.fft.fftfreq(N, dt)[k]
    else:
        nu0 = guess
    amp = lambda nu: -abs(np.sum(sig * w * np.exp(-1j * nu * t)))
    a, b = nu0 - 2 * np.pi / (N * dt), nu0 + 2 * np.pi / (N * dt)
    g = (math.sqrt(5) - 1) / 2
    c, d = b - g * (b - a), a + g * (b - a)
    fc, fd = amp(c), amp(d)
    for _ in range(80):
        if fc < fd:
            b, d, fd = d, c, fc; c = b - g * (b - a); fc = amp(c)
        else:
            a, c, fc = c, d, fd; d = a + g * (b - a); fd = amp(d)
    return (a + b) / 2


def frequencies(z0, Q, h=100.0, nsteps=2 ** 17, every=4):
    traj = rk4(z0, h, nsteps, every)
    X = traj[:, :2] @ Q                               # X = Q^T xi, row-wise
    Y = np.linalg.solve(Q, traj[:, 2:].T).T
    dt = h * every
    return [naff_peak(X[:, j] + 1j * Y[:, j], dt) for j in range(2)], traj


def scaled_point(z3, f):
    """sect. 4.3: xi1, eta1 times f; (xi2, eta2) times s (ratio kept) with H equal to H(z3) (bisection on s)."""
    E0 = H.eval(z3)
    def g(s):
        return H.eval(np.array([z3[0] * f, z3[1] * s, z3[2] * f, z3[3] * s])) - E0
    lo, hi = 0.5, 1.5
    for _ in range(200):
        mid = (lo + hi) / 2
        if (g(lo) > 0) == (g(mid) > 0):
            lo = mid
        else:
            hi = mid
    s = (lo + hi) / 2
    return np.array([z3[0] * f, z3[1] * s, z3[2] * f, z3[3] * s]), s


def main():
    out = {}
    t3 = D.TABLE3
    z3 = np.array([float(t3["xi1"]), float(t3["xi2"]), float(t3["eta1"]), float(t3["eta2"])])
    # exact energy at Table 3
    zf = [F(t3["xi1"]), F(t3["xi2"]), F(t3["eta1"]), F(t3["eta2"])]
    Ex = sum(c * zf[0] ** e[0] * zf[1] ** e[1] * zf[2] ** e[2] * zf[3] ** e[3] for c, e in D.coeffs())
    lo, hi = (F(x) for x in D.E52)
    print("E  H11(Table 3) = %.17e   eq. (52): [%s, %s]   inside: %s   rel. offset from centre %.2e" % (
        float(Ex), D.E52[0], D.E52[1], lo <= Ex <= hi, float((Ex - (lo + hi) / 2) / ((lo + hi) / 2))))
    out["E_table3"] = float(Ex)
    Q, lam = normal_modes()
    print("linear frequencies (rad/yr): %s  = %s arcsec/yr" % (lam, lam / ARC))
    out["lam"] = lam.tolist(); out["Q"] = Q.tolist()
    X, Y = to_modes(z3, Q)
    I = (X ** 2 + Y ** 2) / 2
    phi = np.arctan2(Y, X)
    print("table4  linear actions %s (Table 4: %s, %s), angles %s (Table 4: %s, %s)" % (
        I, D.TABLE4["I1"], D.TABLE4["I2"], phi % (2 * np.pi), D.TABLE4["phi1"], D.TABLE4["phi2"]))
    out["I_linear"] = I.tolist()
    nu, traj = frequencies(z3, Q)
    e12 = [float(D.EQ12["g1"]) * ARC, float(D.EQ12["g2"]) * ARC]
    print("freq  frequency analysis (rad/yr): %.15e %.15e" % tuple(nu))
    print("      eq. (12)               : %.15e %.15e   rel. diff %.2e %.2e" % (
        e12[0], e12[1], nu[0] / e12[0] - 1, nu[1] / e12[1] - 1))
    print("      energy drift along the RK4 orbit: %.2e (relative)" % (
        max(abs(H.eval(z) / H.eval(z3) - 1) for z in traj[::512])))
    out["freq_table3"] = nu
    for tag, f, ref in (("omega' (1+0.02)", 1.02, D.OMEGA_P), ("omega' (1-0.02)", 0.98, D.OMEGA_P),
                        ("omega'' (1+0.02)", 1.02, D.OMEGA_PP), ("omega'' (1-0.02)", 0.98, D.OMEGA_PP)):
        pass
    res = {}
    for f in (1.02, 0.98):
        zs, s = scaled_point(z3, f)
        nus, _ = frequencies(zs, Q)
        res[f] = nus
        print("omega  f = %.2f (s = %.6f): %.16e %.16e" % (f, s, nus[0], nus[1]))
    for name, ref in (("omega'", D.OMEGA_P), ("omega''", D.OMEGA_PP)):
        r = np.array([float(x) for x in ref])
        best = min(res, key=lambda f: np.abs(np.array(res[f]) / r - 1).max())
        print("       %s = %s: closest f = %.2f, rel. diff %s" % (name, ref, best, np.array(res[best]) / r - 1))
    out["omega_scaled"] = {str(k): v for k, v in res.items()}
    if "--json" in sys.argv:
        json.dump(out, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1)


if __name__ == "__main__":
    main()
