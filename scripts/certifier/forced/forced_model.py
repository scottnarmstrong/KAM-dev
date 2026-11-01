#!/usr/bin/env python3
"""V2-TOOLS #6: the periodically forced toy (model, frequency, candidate torus).  Untrusted producer tooling.

The toy is a forced pendulum with interacting Fourier modes, in the extended phase space
z = ((theta0, theta1), (p, J)), theta1 the time (period 1), J its conjugate action:

    H = c * ( J + beta p^2 / 2 + sum_j eps_j cos 2 pi (k_j . theta) )               (all k_j with k_j0 != 0)

`c` is the time scale, `beta` the twist.  The reference frequency is the rotated lunar family of
KAM/SpinOrbit/RotFreqN.lean:  omega* = kappa (nu_-(N) - 1, 1), kappa = c / s, with the exact Q(sqrt 5) description
    nu_-(N) - 1 = (-(2N - 1) + sqrt 5) / D,  D = 2 (N^2 - N - 1),
and the proved Diophantine constant gamma = kappa / (N + 2), tau = 1 (`lunarRotFreqMinusN_isDiophantine`, N >= 8).
N controls the frequency separation |nu - 1| ~ 1/N from the resonance of the mode (1, 0).

The invariant torus K(theta) = (theta0 + u/(2 pi), theta1, p(theta), J(theta)) of frequency omega = (w0, 1),
w0 = nu - 1, is pi-free in these unknowns: with e_m = exp(2 pi i m.theta) and the Fourier coefficients ^,
    -(m.omega)^2 u^_m = beta [ sum_j eps_j k_j0 sin(2 pi k_j.theta + k_j0 u) ]^_m       (m != 0, u odd),
    p = (w0 + sum_m i (m.omega) u^_m e_m) / beta,
    J^_m = -i [ sum_j eps_j k_j1 sin(2 pi k_j.theta + k_j0 u) ]^_m / (m.omega),  J^_0 = J0 (energy E0 = 0),
solved here by a Picard iteration in exact rationals rounded to 2^-R (the residual is whatever the checker
computes from the emitted data; nothing here is trusted).
"""
import math
from fractions import Fraction as F

SQRT5_DIGITS = 40


# ---------------------------------------------------------------------------------------------- the model
class Toy:
    """A toy instance.  modes: list of ((k0, k1), eps) with k0 != 0; every number exact."""

    def __init__(self, N=8, c=F(1), beta=F(1), modes=None, s=1 + F(1, 10 ** 6), name="toy"):
        self.N, self.c, self.beta, self.s, self.name = N, F(c), F(beta), F(s), name
        self.modes = [((int(k[0]), int(k[1])), F(e)) for k, e in (modes or DEFAULT_MODES)]
        for (k0, _), _e in self.modes:
            assert k0 != 0, "a mode with k0 = 0 needs a character witness at the zero key"
        assert N >= 8, "lunarRotFreqMinusN_isDiophantine needs N >= 8"

    @property
    def kappa(self):
        return self.c / self.s

    @property
    def gamma(self):
        """lunarRotFreqMinusN_isDiophantine: IsDiophantine (kappa / (N + 2)) 1 omega*."""
        return self.kappa / (self.N + 2)

    def m_D(self):
        return 2 * self.N - 1, 2 * (self.N * self.N - self.N - 1)

    def alg_coeffs(self):
        """lunarRotFreqMinusN_eq: omega* = algFreq 2 [[-(2N-1) kappa / D, kappa / D], [kappa]] (sqrt 5)."""
        m, D = self.m_D()
        k = self.kappa
        return [[-m * k / D, k / D], [k]]

    def ham(self):
        """The HamExpr as a tuple tree (adv_jet format):  c * (J + (beta/2) p^2 + sum_j eps_j cos 2 pi k_j.theta)."""
        modes = ("const", F(0))
        for k, e in reversed(self.modes):
            modes = ("add", ("mul", ("const", e), ("cosMode", k)), modes)
        H0 = ("add", ("action", 1), ("add", ("mul", ("const", self.beta / 2), ("pow", ("action", 0), 2)), modes))
        return ("mul", ("const", self.c), H0)

    def describe(self):
        return dict(name=self.name, N=self.N, c=str(self.c), beta=str(self.beta), s=str(self.s),
                    kappa=str(self.kappa), gamma=str(self.gamma),
                    modes=[[list(k), str(e)] for k, e in self.modes])


DEFAULT_MODES = [((1, 0), F(1, 10 ** 4)), ((1, 1), F(2, 10 ** 4)), ((2, -1), F(1, 10 ** 4))]


def lean_q(q):
    q = F(q)
    if q.denominator == 1:
        return "(%d)" % q.numerator
    return "(%d / %d)" % (q.numerator, q.denominator)


def ham_lean(e):
    """The tuple tree as a Lean `HamExpr 2` term."""
    t = e[0]
    if t == "const":
        return "(.const %s)" % lean_q(e[1])
    if t == "action":
        return "(.action %d)" % e[1]
    if t == "cosMode":
        return "(.cosMode [%s])" % ", ".join(str(x) for x in e[1])
    if t == "pow":
        return "(.pow %s %d)" % (ham_lean(e[1]), e[2])
    if t in ("add", "mul"):
        return "(.%s %s %s)" % (t, ham_lean(e[1]), ham_lean(e[2]))
    raise ValueError(t)


# ---------------------------------------------------------------------------------------------- frequency
def sqrt5_enclosure(d=SQRT5_DIGITS):
    D = 10 ** d
    a = math.isqrt(5 * D * D)
    return F(a, D), F(a + 1, D)


def alg_row_lo(row, lo, hi):
    acc = F(0)
    for i, a in enumerate(row):
        acc += min(a * lo ** i, a * hi ** i)
    return acc


def alg_row_hi(row, lo, hi):
    acc = F(0)
    for i, a in enumerate(row):
        acc += max(a * lo ** i, a * hi ** i)
    return acc


def freq_box(toy, d=SQRT5_DIGITS):
    """((centre, radius) per coordinate), the box of `checkAlgBox 2 coeffs lo hi box` (toy_gen.alg_box)."""
    lo, hi = sqrt5_enclosure(d)
    box = []
    for row in toy.alg_coeffs():
        L, H = alg_row_lo(row, lo, hi), alg_row_hi(row, lo, hi)
        box.append(((L + H) / 2, (H - L) / 2))
    return box, (lo, hi)


# ---------------------------------------------------------------------------------------------- Fourier series
# a series is a dict {(m0, m1): (re, im)} of exact rationals


def rnd(q, R):
    """round to the nearest multiple of 2^-R."""
    q = F(q)
    if q == 0:
        return q
    D = 1 << R
    return F(round(q * D), D)


def cmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def sadd(A, Bs, sc=F(1)):
    out = dict(A)
    for k, v in Bs.items():
        o = out.get(k, (F(0), F(0)))
        out[k] = (o[0] + sc * v[0], o[1] + sc * v[1])
    return {k: v for k, v in out.items() if v[0] != 0 or v[1] != 0}


def smul(A, Bs, keep, R):
    out = {}
    for ka, va in A.items():
        for kb, vb in Bs.items():
            k = (ka[0] + kb[0], ka[1] + kb[1])
            if not keep(k):
                continue
            o = out.get(k, (F(0), F(0)))
            p = cmul(va, vb)
            out[k] = (o[0] + p[0], o[1] + p[1])
    return {k: (rnd(v[0], R), rnd(v[1], R)) for k, v in out.items() if v[0] != 0 or v[1] != 0}


def sscale(A, z):
    return {k: cmul(z, v) for k, v in A.items()}


def sexp_i(u, k0, keep, R, tol, prune=None):
    """exp(i k0 u) for a real series u, by the Taylor series (u small); `prune(m, |c|)` drops terms of each
    power (the dropped mass is what the checker's witness radius and pin then see)."""
    E = {(0, 0): (F(1), F(0))}
    term = dict(E)
    j = 0
    while True:
        j += 1
        term = sscale(smul(term, u, keep, R), (F(0), F(k0, j)))
        if prune is not None:
            term = {m: v for m, v in term.items() if not prune(m, abs(v[0]) + abs(v[1]))}
        if not term:
            break
        E = sadd(E, term)
        if max(abs(v[0]) + abs(v[1]) for v in term.values()) < tol:
            break
        if j > 200:
            raise RuntimeError("exp series does not converge")
    return E


def sin_shift(E, k):
    """sin(2 pi k.theta + phi) as a series, from E = exp(i phi):  (e_k E - conj(e_k E)) / (2 i)."""
    f = {(m[0] + k[0], m[1] + k[1]): v for m, v in E.items()}
    g = {(-m[0], -m[1]): (v[0], -v[1]) for m, v in f.items()}          # conj of the real-variable function
    d = sadd(f, g, F(-1))
    return sscale(d, (F(0), F(-1, 2)))                                  # / (2 i) = * (-i/2)


def real_part_check(A, tol):
    for k, v in A.items():
        w = A.get((-k[0], -k[1]), (F(0), F(0)))
        if abs(v[0] - w[0]) > tol or abs(v[1] + w[1]) > tol:
            return False
    return True


# ---------------------------------------------------------------------------------------------- the torus
class Torus:
    """u (angle 0 times 2 pi), p, J as series, the frequency w0, J0, and the solve log."""

    def __init__(self, u, p, J, w0, info):
        self.u, self.p, self.J, self.w0, self.info = u, p, J, w0, info


def solve_torus(toy, w0, L0=6, L1=6, R=160, tol=F(1, 10 ** 45), iters=200, prune=None):
    """Picard iteration for u on the support |m0| <= L0, |m1| <= L1; then p, J.  `prune(m, |c|)` drops terms."""
    keep = lambda m: abs(m[0]) <= L0 and abs(m[1]) <= L1
    om = lambda m: m[0] * w0 + m[1]
    prune_e = (lambda m, a: prune(m, a * F(1, 10 ** 4))) if prune is not None else None
    beta = toy.beta
    k0s = sorted({k[0] for k, _ in toy.modes})
    u = {}
    hist = []
    for it in range(iters):
        Es = {k0: sexp_i(u, k0, keep, R, tol, prune_e) for k0 in k0s}
        Fu, FJ = {}, {}
        for k, e in toy.modes:
            S = sin_shift(Es[k[0]], k)
            S = {m: v for m, v in S.items() if keep(m)}
            Fu = sadd(Fu, S, beta * e * k[0])
            FJ = sadd(FJ, S, e * k[1])
        new = {}
        for m, v in Fu.items():
            if m == (0, 0):
                continue
            d = om(m) ** 2
            new[m] = (rnd(-v[0] / d, R), rnd(-v[1] / d, R))
        if prune is not None:
            new = {m: v for m, v in new.items() if not prune(m, abs(v[0]) + abs(v[1]))}
        diff = max([abs(new.get(m, (0, 0))[0] - u.get(m, (0, 0))[0]) + abs(new.get(m, (0, 0))[1] -
                    u.get(m, (0, 0))[1]) for m in set(new) | set(u)] or [F(0)])
        hist.append(float(diff))
        u = new
        if diff < tol:
            break
    mean_F = Fu.get((0, 0), (F(0), F(0)))
    # p = (w0 + sum i (m.omega) u_m e_m) / beta
    p = {(0, 0): (w0 / beta, F(0))}
    for m, v in u.items():
        p[m] = (rnd(-om(m) * v[1] / beta, R), rnd(om(m) * v[0] / beta, R))
    # J_m = -i FJ_m / (m.omega)
    J = {}
    for m, v in FJ.items():
        if m == (0, 0):
            continue
        J[m] = (rnd(v[1] / om(m), R), rnd(-v[0] / om(m), R))
    if prune is not None:
        p = {m: v for m, v in p.items() if m == (0, 0) or not prune(m, abs(v[0]) + abs(v[1]))}
        J = {m: v for m, v in J.items() if not prune(m, abs(v[0]) + abs(v[1]))}
    # J0: the energy average (H0 o K) is 0
    pp = smul(p, p, lambda m: m == (0, 0), R)
    Vm = F(0)
    Es = {k0: sexp_i(u, k0, keep, R, tol, prune_e) for k0 in k0s}
    for k, e in toy.modes:
        z = Es[k[0]].get((-k[0], -k[1]), (F(0), F(0)))
        Vm += e * z[0]
    J0 = -(beta / 2 * pp.get((0, 0), (F(0), F(0)))[0] + Vm)
    J[(0, 0)] = (rnd(J0, R), F(0))
    info = dict(iterations=len(hist), last_diff=hist[-1] if hist else 0.0, mean_forcing=float(abs(mean_F[0]) +
                abs(mean_F[1])), terms=dict(u=len(u), p=len(p), J=len(J)), L0=L0, L1=L1)
    return Torus(u, p, J, w0, info)


def half_poly(S):
    """(zero, half): the CertRealPoly form of a real series (half keys (k, l) > (0, 0), ascending)."""
    z = S.get((0, 0), (F(0), F(0)))
    half = sorted((k, v) for k, v in S.items() if k > (0, 0))
    return z[0], half


if __name__ == "__main__":
    toy = Toy()
    box, _ = freq_box(toy)
    w0 = box[0][0] / toy.kappa
    T = solve_torus(toy, w0, 5, 5, R=120, tol=F(1, 10 ** 30))
    print(toy.describe())
    print("w0", float(w0), T.info)
    big = sorted(T.u.items(), key=lambda kv: -abs(kv[1][1]))[:8]
    print([(k, float(v[1])) for k, v in big])
