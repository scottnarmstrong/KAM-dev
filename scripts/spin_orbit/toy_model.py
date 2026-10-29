#!/usr/bin/env python3
"""Exact ℚ Fourier models for the SO toy certificates (the `direct` product route of A-E §C).

Untrusted tooling (SO-TOYGEN).  Mirrors the LANDED `CertPoly`, `CertRealPoly.toPoly`, `CertWeight`,
`CertPoly.weightedNormUp`, `degFactorUp`, `CertModel.supBound` and the DESIGN semantics (bodies still `sorry`
in the signatures) of `CertModel.{add, mul, trim, toDeg, ofDeriv}`, `CertPoly.shift`, `expWitnessRadius`,
`invWitnessRadius`, over the exact backend (no rounding terms).

Representation: a polynomial is (den, {key: (re, im)}) with integer re, im over the common positive integer
denominator `den` (exact; avoids per-term gcds in the large T2d products).  A model is (deg, poly, rad) with
`rad` a Fraction and the denotation `(2π)^deg (P + T)`, `sup_{T_ρ} |T| ≤ rad`.
"""
from fractions import Fraction as F
from math import gcd
import toy_arith as A

ZERO_KEY_CACHE = {}


def zkey(n):
    return (0,) * n


def kabs(k):
    return sum(abs(x) for x in k)


# ---------------------------------------------------------------- polynomials
def p_zero():
    return (1, {})


def p_const(c, n):
    re, im = F(c[0]), F(c[1])
    den = re.denominator * im.denominator // gcd(re.denominator, im.denominator)
    return (den, {zkey(n): (re.numerator * (den // re.denominator), im.numerator * (den // im.denominator))})


def p_from_terms(terms):
    """terms: list of (key tuple, (re Fraction, im Fraction)); repeated keys add."""
    den = 1
    for _, (re, im) in terms:
        for x in (F(re), F(im)):
            den = den * x.denominator // gcd(den, x.denominator)
    d = {}
    for k, (re, im) in terms:
        re, im = F(re), F(im)
        a, b = d.get(k, (0, 0))
        d[k] = (a + re.numerator * (den // re.denominator), b + im.numerator * (den // im.denominator))
    return (den, d)


def p_terms(P):
    den, d = P
    return [(k, (F(a, den), F(b, den))) for k, (a, b) in sorted(d.items())]


def p_rescale(P, den):
    pd, d = P
    assert den % pd == 0
    f = den // pd
    return (den, {k: (a * f, b * f) for k, (a, b) in d.items()})


def p_add(P, Q, sign=1):
    den = P[0] * Q[0] // gcd(P[0], Q[0])
    P2, Q2 = p_rescale(P, den), p_rescale(Q, den)
    d = dict(P2[1])
    for k, (a, b) in Q2[1].items():
        x, y = d.get(k, (0, 0))
        d[k] = (x + sign * a, y + sign * b)
    return (den, d)


def p_scale(P, c):
    """multiply by the exact complex constant c = (re, im)."""
    re, im = F(c[0]), F(c[1])
    cd = re.denominator * im.denominator // gcd(re.denominator, im.denominator)
    cr, ci = re.numerator * (cd // re.denominator), im.numerator * (cd // im.denominator)
    return (P[0] * cd, {k: (a * cr - b * ci, a * ci + b * cr) for k, (a, b) in P[1].items()})


def p_mul(P, Q, stats=None):
    """Exact product; stats counts the coefficient pairs (the kernel cost driver of the direct route)."""
    d = {}
    for k1, (a, b) in P[1].items():
        for k2, (c, e) in Q[1].items():
            k = tuple(x + y for x, y in zip(k1, k2))
            x, y = d.get(k, (0, 0))
            d[k] = (x + a * c - b * e, y + a * e + b * c)
    if stats is not None:
        stats["pairs"] = stats.get("pairs", 0) + len(P[1]) * len(Q[1])
    return (P[0] * Q[0], d)


def p_shift(P, m):
    return (P[0], {tuple(x + y for x, y in zip(k, m)): v for k, v in P[1].items()})


def p_wnorm(P, w):
    """weightedNormUp over ℚ: Σ (|re| + |im|) w^{|k|₁}."""
    den, d = P
    by = {}
    for k, (a, b) in d.items():
        m = kabs(k)
        by[m] = by.get(m, 0) + abs(a) + abs(b)
    w = F(w)
    return sum((F(v, den) * w ** m for m, v in by.items()), F(0))


def p_coeff0(P, n):
    a, b = P[1].get(zkey(n), (0, 0))
    return (F(a, P[0]), F(b, P[0]))


def p_value0(P):
    """value at θ = 0: the sum of all coefficients."""
    return (F(sum(a for a, _ in P[1].values()), P[0]), F(sum(b for _, b in P[1].values()), P[0]))


def p_deriv(P, j):
    """∂_j at (2π)-degree +1: coefficient i k_j c (exact)."""
    return (P[0], {k: (-k[j] * b, k[j] * a) for k, (a, b) in P[1].items() if k[j] != 0})


def p_truncate(P, cutoff, w):
    """keep |k|₁ <= cutoff; return (kept, weighted norm of the dropped part)."""
    if cutoff is None:
        return P, F(0)
    keep = {k: v for k, v in P[1].items() if kabs(k) <= cutoff}
    drop = (P[0], {k: v for k, v in P[1].items() if kabs(k) > cutoff})
    return (P[0], keep), p_wnorm(drop, w)


def p_is_zero(P):
    return all(a == 0 and b == 0 for a, b in P[1].values())


def p_reduce(P):
    """drop exact zero coefficients and reduce the common denominator (exactness preserved)."""
    den, d = P
    d = {k: v for k, v in d.items() if v != (0, 0)}
    g = den
    for a, b in d.values():
        g = gcd(g, gcd(abs(a), abs(b)))
        if g == 1:
            break
    if g > 1:
        den //= g
        d = {k: (a // g, b // g) for k, (a, b) in d.items()}
    return (den, d)


def realpoly_to_poly(zero, half, n):
    """CertRealPoly.toPoly: zero term, each half term and its conjugate at -k."""
    terms = [(zkey(n), (F(zero), F(0)))]
    for k, (re, im) in half:
        k = tuple(k) + (0,) * (n - len(k))
        terms.append((k, (F(re), F(im))))
        terms.append((tuple(-x for x in k), (F(re), -F(im))))
    return p_reduce(p_from_terms(terms))


# ---------------------------------------------------------------- models
class Model:
    __slots__ = ("deg", "poly", "rad")

    def __init__(self, deg, poly, rad=F(0)):
        self.deg, self.poly, self.rad = int(deg), p_reduce(poly), F(rad)

    def is_zero(self):
        return self.rad == 0 and p_is_zero(self.poly)


def m_const(c, n, deg=0, rad=F(0)):
    return Model(deg, p_const(c, n), rad)


def m_zero(n):
    return Model(0, p_zero(), F(0))


def supBound(m, w):
    return A.degFactorUp(m.deg) * (p_wnorm(m.poly, w) + m.rad)


def pi_pow_ball(d, pe):
    """ball (centre, radius) of (2π)^d from the validated π enclosure pe = (centre, rad), d integer."""
    c, r = F(pe[0]), F(pe[1])
    lo, hi = 2 * (c - r), 2 * (c + r)
    assert lo > 0
    vals = [lo ** d, hi ** d]
    a, b = min(vals), max(vals)
    return (a + b) / 2, (b - a) / 2


def m_toDeg(m, d, w, pe, log):
    """Re-express at degree d: (2π)^deg P = (2π)^d ((2π)^(deg-d) P)."""
    if m.deg == d:
        return m
    if m.is_zero():
        return Model(d, p_zero(), F(0))
    log.append(("toDeg", m.deg, d))
    c, r = pi_pow_ball(m.deg - d, pe)
    return Model(d, p_scale(m.poly, (c, 0)), r * p_wnorm(m.poly, w) + (c + r) * m.rad)


def m_add(a, b, w, pe, log, sign=1):
    if a.is_zero():
        return b if sign == 1 else m_neg(b)
    if b.is_zero():
        return a
    if a.deg != b.deg:
        b = m_toDeg(b, a.deg, w, pe, log)
    return Model(a.deg, p_add(a.poly, b.poly, sign), a.rad + b.rad)


def m_neg(a):
    return Model(a.deg, p_scale(a.poly, (-1, 0)), a.rad)


def m_scale_ball(a, c, r, w):
    """multiply by a scalar ball (c complex exact, radius r): the model of a constant times a."""
    return Model(a.deg, p_scale(a.poly, c), (abs(c[0]) + abs(c[1]) + r) * a.rad + r * p_wnorm(a.poly, w))


class Cfg:
    def __init__(self, name, cutoff, taylorN, halvings):
        self.name, self.cutoff, self.taylorN, self.halvings = name, cutoff, taylorN, halvings
        self.products = []          # (key, |a|, |b|, pairs)

    def advice(self):
        return [[list(k), "direct"] for k, *_ in self.products]


def m_mul(a, b, w, cfg, key):
    """CertModel.mul, `direct` advice: exact product, cutoff truncation into the radius, cross terms."""
    st = {}
    if a.is_zero() or b.is_zero():
        cfg.products.append((tuple(key), len(a.poly[1]), len(b.poly[1]), 0))
        return Model(a.deg + b.deg, p_zero(), F(0))
    P = p_mul(a.poly, b.poly, st)
    P, drop = p_truncate(P, cfg.cutoff, w)
    na, nb = p_wnorm(a.poly, w), p_wnorm(b.poly, w)
    cfg.products.append((tuple(key), len(a.poly[1]), len(b.poly[1]), st["pairs"]))
    return Model(a.deg + b.deg, P, drop + na * b.rad + nb * a.rad + a.rad * b.rad)


def m_ofDeriv(j, d, P):
    return Model(d + 1, p_deriv(P, j), F(0))


# ---------------------------------------------------------------- witnesses
def expPinBall(g):
    """g₀(0) = sum of the coefficients of the polynomial part (exact over ℚ, radius 0)."""
    return p_value0(g.poly), F(0)


def expWitnessRadius(n, w, rho, cfg, g, E, key):
    """E = (poly, pinHalvings, pinOrder).  Returns the radius or None (design §1.7, A-E §C)."""
    Epoly, s, N = E
    if g.deg != 0:
        return None
    B = p_wnorm(g.poly, w)
    pin, prad = expPinBall(g)
    out = A.certCExpReduced(pin, prad, s, N)
    if out is None:
        return None
    E0 = p_value0(Epoly)
    eps0 = A.normUp((E0[0] - out[0][0], E0[1] - out[0][1])) + out[1]
    res = F(0)
    Em = Model(0, Epoly)
    for j in range(n):
        dE = m_ofDeriv(j, 0, Epoly)
        dg = m_ofDeriv(j, 0, g.poly)
        prod = m_mul(dg, Em, w, cfg, list(key) + [j])
        diff = Model(1, p_add(dE.poly, prod.poly, -1), prod.rad)
        res += (F(1, 2) + F(rho)) * supBound(diff, w)
    eta = g.rad
    up = lambda q: A.ratExpUp(q, cfg.halvings, cfg.taylorN)
    return up(2 * B) * (eps0 + res) + up(B) * (up(eta) - 1)


def invWitnessRadius(n, w, cfg, b, Q, key):
    """δ >= sup|1 - Q (P + T)|, δ < 1; radius sup|Q| δ/(1 - δ) (design §1.7, ruling O2)."""
    prod = m_mul(Model(0, Q), Model(0, b.poly, b.rad), w, cfg, key)
    one_minus = p_add(p_const((1, 0), n), prod.poly, -1)
    delta = p_wnorm(one_minus, w) + prod.rad
    if not delta < 1:
        return None, delta
    return p_wnorm(Q, w) * delta / (1 - delta), delta
