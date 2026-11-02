"""Exact rational single-planet Kepler series in Poincare variables.

A single-planet series is a dict {(p, q): Fraction} standing for
    sum c_{p,q} u^p ubar^q w^(q - p + shift),
where u = (xi - i eta)/sqrt(Lambda) = sqrt(2 Gamma/Lambda) e^{i varpi}, w = e^{i lambda}
and `shift` is a fixed harmonic offset carried by the caller.  Every Kepler quantity
used here obeys the d'Alembert rule, so the w exponent is determined by (p, q).

Z = (r/a) e^{i(f - M)} = rho e^{i(phi - lambda)} is built from the Bessel expansions
    E - M = sum_s (2/s) J_s(s e) sin(sM),
    cos E = -e/2 + sum_s (1/s)(J_{s-1}(se) - J_{s+1}(se)) cos(sM),
and e e^{i varpi} = u sqrt(1 - u ubar/4) (exact: e^2 = 2Gamma/Lambda - (Gamma/Lambda)^2).
All arithmetic is exact (fractions.Fraction); truncation is by total degree p + q <= D.
"""
from __future__ import annotations

from fractions import Fraction as Fr
from math import comb, factorial

D_DEFAULT = 18


# ---------------------------------------------------------- univariate in e
def _pmul(a, b, n):
    out = [Fr(0)] * (n + 1)
    for i, x in enumerate(a):
        if x == 0 or i > n:
            continue
        for j, y in enumerate(b):
            if i + j > n:
                break
            if y:
                out[i + j] += x * y
    return out


def _bessel_J(order: int, mult: int, n: int):
    """J_order(mult * e) as a list of coefficients in e, degree <= n (order >= 0)."""
    out = [Fr(0)] * (n + 1)
    l = 0
    while order + 2 * l <= n:
        out[order + 2 * l] = (Fr((-1) ** l) * Fr(mult, 2) ** (order + 2 * l)
                              / (factorial(l) * factorial(order + l)))
        l += 1
    return out


def _sqrt1m(n):
    """sqrt(1 - e^2) coefficients in e, degree <= n."""
    out = [Fr(0)] * (n + 1)
    half = Fr(1, 2)
    j = 0
    while 2 * j <= n:
        c = Fr(1)
        for i in range(j):
            c *= (half - i)
        c /= factorial(j)
        out[2 * j] = c * (-1) ** j
        j += 1
    return out


def hansen_position(n: int):
    """{s: coeffs in e} with (r/a) e^{i f} = sum_s X_s(e) e^{i s M}, e-degree <= n."""
    sq = _sqrt1m(n + 1)
    X = {}
    zero = [Fr(0)] * (n + 1)
    X[0] = list(zero)
    if n >= 1:
        X[0][1] = Fr(-3, 2)
    for s in range(1, n + 2):
        jm = _bessel_J(s - 1, s, n + 1)
        jp = _bessel_J(s + 1, s, n + 1)
        js = _bessel_J(s, s, n + 1)
        cosE = [Fr(1, 2 * s) * (jm[i] - jp[i]) for i in range(n + 1)]
        # sqrt(1-e^2) J_s(se)/(s e): divide by e (J_s(se) has no constant term for s >= 1)
        js_over_e = [js[i + 1] / s for i in range(n + 1)]
        sinE = _pmul(sq, js_over_e, n)
        X[s] = [cosE[i] + sinE[i] for i in range(n + 1)]
        X[-s] = [cosE[i] - sinE[i] for i in range(n + 1)]
    return X


# ---------------------------------------------------- bivariate (p, q) series
def smul(a, b, D):
    out = {}
    for (p, q), x in a.items():
        for (r, s), y in b.items():
            if p + q + r + s <= D:
                k = (p + r, q + s)
                out[k] = out.get(k, 0) + x * y
    return {k: v for k, v in out.items() if v != 0}


def sadd(a, b, cb=1):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + cb * v
    return {k: v for k, v in out.items() if v != 0}


def sscale(a, c):
    return {k: c * v for k, v in a.items()} if c != 0 else {}


def stranspose(a):
    """Complex conjugate of a series with real coefficients: swaps u and ubar."""
    return {(q, p): v for (p, q), v in a.items()}


def kepler_Z(D: int = D_DEFAULT):
    """Z = (r/a) e^{i(f - M)} as an exact (p, q) series (harmonic shift 0)."""
    X = hansen_position(D + 1)
    # x = u ubar polynomial pieces: S^k = (1 - x/4)^{k/2}, e^2 = x (1 - x/4)
    def S_pow(k, nmax):
        out = []
        for j in range(nmax + 1):
            c = Fr(1)
            for i in range(j):
                c *= (Fr(k, 2) - i)
            c /= factorial(j)
            out.append(c * Fr(-1, 4) ** j)
        return out

    nx = D // 2 + 1
    e2 = [Fr(0)] * (nx + 1)
    e2[1] = Fr(1)
    if nx >= 2:
        e2[2] = Fr(-1, 4)
    Z = {}
    for s, coeffs in X.items():
        t = s - 1  # Z picks e^{i(s-1)M}
        at = abs(t)
        if at > D:
            continue
        # coeffs = e^{|t|} P(e^2); extract P
        P = []
        for l in range(0, (D - at) // 2 + 1):
            idx = at + 2 * l
            P.append(coeffs[idx] if idx < len(coeffs) else Fr(0))
        # check lower coefficients vanish (d'Alembert)
        for idx in range(0, min(at, len(coeffs))):
            assert coeffs[idx] == 0, (s, idx)
        # P(e^2) with e^2 = x(1 - x/4)  -> polynomial in x
        nmax = (D - at) // 2
        Px = [Fr(0)] * (nmax + 1)
        e2pow = [Fr(1)] + [Fr(0)] * nmax
        for l, c in enumerate(P):
            if l > 0:
                e2pow = _pmul(e2pow, e2, nmax)
            if c:
                for i in range(nmax + 1):
                    Px[i] += c * e2pow[i]
        Px = _pmul(Px, S_pow(at, nmax), nmax)
        for l, c in enumerate(Px):
            if c == 0:
                continue
            if t >= 0:
                key = (l, l + at)
            else:
                key = (l + at, l)
            if sum(key) <= D:
                Z[key] = Z.get(key, 0) + c
    return {k: v for k, v in Z.items() if v != 0}


def slog1p(Y, D):
    """log(1 + Y) for Y without constant term."""
    out = {}
    power = dict(Y)
    for n in range(1, D + 1):
        if not power:
            break
        out = sadd(out, power, Fr((-1) ** (n + 1), n))
        power = smul(power, Y, D)
    return out


def sexp(X, D):
    """exp(X) for X without constant term."""
    out = {(0, 0): Fr(1)}
    power = {(0, 0): Fr(1)}
    for n in range(1, D + 1):
        power = smul(power, X, D)
        if not power:
            break
        out = sadd(out, power, Fr(1, factorial(n)))
    return out


def universal_series(D: int = D_DEFAULT, KL: int = 17, NM: int | None = None):
    """Exact universal single-planet series used by the pair expansion.

    Returns dict with
      'Z'           Z = rho e^{i(phi - lambda)}                    (shift 0)
      'V'           V = -i d/dlambda (Z w) / w = (w d/dw)(Z w)/w   (shift +1; times i gives d/dlambda)
      'A'[(m, k)]   sigma^m e^{ik(phi - lambda)}                   (shift 0)  [inner planet]
      'B'[(m, k)]   sigma^m e^{-ik(phi - lambda)} / rho            (shift 0)  [outer planet]
    with sigma = 2 log rho, m <= NM (default D), |k| <= KL.
    """
    if NM is None:
        NM = D
    Z = kepler_Z(D)
    Y = sadd(Z, {(0, 0): Fr(1)}, -1)
    g = slog1p(Y, D)
    gb = stranspose(g)
    sigma = sadd(g, gb)          # 2 log rho
    delta = sadd(g, gb, -1)      # 2 i (phi - lambda)
    E1 = sexp(sscale(delta, Fr(1, 2)), D)
    E = {0: {(0, 0): Fr(1)}, 1: E1, -1: stranspose(E1)}
    for k in range(2, KL + 1):
        E[k] = smul(E[k - 1], E1, D)
        E[-k] = stranspose(E[k])
    rinv = sexp(sscale(sigma, Fr(-1, 2)), D)
    spow = [{(0, 0): Fr(1)}]
    for m in range(1, NM + 1):
        spow.append(smul(spow[-1], sigma, D))
    A = {}
    B = {}
    for m in range(NM + 1):
        Bm = smul(spow[m], rinv, D)
        for k in range(-KL, KL + 1):
            A[(m, k)] = smul(spow[m], E[k], D)
            B[(m, k)] = smul(Bm, E[-k], D)
    # V: (w d/dw) applied to Z w: term u^p ub^q w^{q-p+1} -> factor (q - p + 1)
    V = {(p, q): v * (q - p + 1) for (p, q), v in Z.items() if (q - p + 1) != 0}
    return {'D': D, 'KL': KL, 'Z': Z, 'V': V, 'A': A, 'B': B, 'sigma': sigma}


if __name__ == '__main__':
    import cmath
    import math
    import time
    t0 = time.time()
    Z = kepler_Z(18)
    print('Z terms', len(Z), 'time', round(time.time() - t0, 2))
    # numerical check against a direct Kepler solve
    e, varpi, M = 0.05, 0.3, 1.0
    E = M
    for _ in range(60):
        E = E - (E - e * math.sin(E) - M) / (1 - e * math.cos(E))
    x = math.cos(E) - e
    y = math.sqrt(1 - e * e) * math.sin(E)
    Zdir = complex(x, y) * cmath.exp(-1j * M)
    G_over_L = 1 - math.sqrt(1 - e * e)
    u = math.sqrt(2 * G_over_L) * cmath.exp(1j * varpi)
    lam = M + varpi
    w = cmath.exp(1j * lam)
    Zs = sum(float(c) * u ** p * u.conjugate() ** q * w ** (q - p) for (p, q), c in Z.items())
    print('series', Zs, 'direct', Zdir, 'diff', abs(Zs - Zdir))
