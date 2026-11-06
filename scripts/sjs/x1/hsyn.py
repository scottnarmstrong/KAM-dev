#!/usr/bin/env python3
"""SJS-X1: FH25's reduced planar Sun-Jupiter-Saturn Hamiltonian in the synodic regular chart, with jets.

Untrusted design tooling.  The chart is SJS-PLAN's (sjs_chart.H_syn): angles (b1, b2, b3) = (a1 - a2, a2, a2 + a3), actions
(Lambda1, I5, I6), Lambda2 = C + I5 + I6 - Lambda1, gauge psi5 = 0, normal modes w5 = sqrt(2 I5), w6 = sqrt(2 I6) e^{i a3},
Poincare variables z = Q w (Q the rotation by phi).  Unlike sjs_chart (which goes through Delaunay's l, g, e and an arctangent),
this module uses regular Kepler variables, as the plan's operation count does (sjs_ops.py):
  k + i h = eps conj(z), eps = sqrt((2 Lambda - P) / (2 Lambda^2)), P = |z|^2 / 2, so e^2 = k^2 + h^2 and sqrt(1 - e^2) = 1 - P/Lambda;
  eccentric longitude F:  lambda = F - k sin F + h cos F;  beta = 1 / (1 + sqrt(1 - e^2)) = Lambda / (2 Lambda - P);
  X = a ((1 - beta h^2) cos F + beta h k sin F - k),  Y = a ((1 - beta k^2) sin F + beta h k cos F - h),
  (VX, VY) = (b / rho) (beta h k cos F - (1 - beta h^2) sin F, (1 - beta k^2) cos F - beta h k sin F),
  rho = 1 - k cos F - h sin F,  a = Lambda^2 / m^2,  b = m^2 / Lambda   (FH25's scaling, as sjs_torus.delaunay_jet).
  H = -m1^3 / (2 Lambda1^2) - m2^3 / (2 Lambda2^2) + mu (|V1 + V2|^2 / 2 - m1 m2 / |X1 - X2|)        (FH25 (2.1)-(2.2)).
No e = 0 singularity and no branch cut on the torus.  The base number type is a float64 array, a DD array (dd.py) or an mpmath
number; Jet carries sparse first and second derivatives.
"""
import math
import os
import sys
import numpy as np
import mpmath

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dd import DD
sys.path.pop(0)

# FH25's data as printed (decimal strings); the float values below are their roundings
M_STR = ("0.9546", "0.2856")
MU_STR = "1e-3"
GTOT_STR = "3.05839852910896096675"
OMEGA_STR = ("8.39549288702546301204e-2", "3.38240117059304358259e-2", "-1.85007988077595e-5")
M = tuple(float(x) for x in M_STR)
MU0 = float(MU_STR)
GTOT = float(GTOT_STR)
OMEGA = np.array([float(x) for x in OMEGA_STR])


def _is_mp(x):
    return isinstance(x, (mpmath.mpf, mpmath.mpc))


def b_inv(x):
    if isinstance(x, DD):
        return x.inv()
    return 1 / x


def b_sqrt(x):
    if isinstance(x, DD):
        return x.sqrt()
    if _is_mp(x):
        return mpmath.sqrt(x)
    return np.sqrt(x)


def b_sincos(x):
    if isinstance(x, DD):
        return x.sincos()
    if _is_mp(x):
        return mpmath.sin(x), mpmath.cos(x)
    return np.sin(x), np.cos(x)


def b_one(x):
    if isinstance(x, DD):
        return DD(np.ones_like(x.hi))
    if _is_mp(x):
        return mpmath.mpf(1)
    return np.ones_like(x)


def consts(kind):
    """the model's constants, exactly rounded in the base type: 'f' float, 'dd' DD scalars, 'mp' mpmath"""
    m = [mpmath.mpf(x) for x in M_STR]
    vals = dict(m2=[x ** 2 for x in m], im2=[1 / x ** 2 for x in m], m3h=[-x ** 3 / 2 for x in m], mm=m[0] * m[1],
                mu=mpmath.mpf(MU_STR), C=mpmath.mpf(GTOT_STR))
    if kind == "mp":
        return vals
    conv = (lambda x: float(x)) if kind == "f" else (lambda x: DD(np.float64(float(x)), np.float64(float(x - float(x)))))
    return {k: ([conv(x) for x in v] if isinstance(v, list) else conv(v)) for k, v in vals.items()}


def omega_dd():
    return [DD(np.float64(float(mpmath.mpf(x))), np.float64(float(mpmath.mpf(x) - float(mpmath.mpf(x))))) for x in OMEGA_STR]


class Jet:
    """value v, gradient g {i: d}, Hessian h {(i, j): d, i <= j}; order 1 or 2 (h unused for order 1)"""
    __slots__ = ("v", "g", "h", "o")

    def __init__(self, v, g, h, o):
        self.v, self.g, self.h, self.o = v, g, h, o

    @staticmethod
    def var(v, i, o):
        return Jet(v, {i: b_one(v)}, {}, o)

    @staticmethod
    def const(v, o):
        return Jet(v, {}, {}, o)

    def __add__(self, b):
        if not isinstance(b, Jet):
            return Jet(self.v + b, self.g, self.h, self.o)
        g = dict(self.g)
        for k, x in b.g.items():
            g[k] = g[k] + x if k in g else x
        h = dict(self.h)
        for k, x in b.h.items():
            h[k] = h[k] + x if k in h else x
        return Jet(self.v + b.v, g, h, self.o)
    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.v, {k: -x for k, x in self.g.items()}, {k: -x for k, x in self.h.items()}, self.o)

    def __sub__(self, b):
        return self + (-b)

    def __rsub__(self, b):
        return (-self) + b

    def __mul__(self, b):
        if not isinstance(b, Jet):
            return Jet(self.v * b, {k: x * b for k, x in self.g.items()}, {k: x * b for k, x in self.h.items()}, self.o)
        a = self
        g = {}
        for k, x in a.g.items():
            g[k] = x * b.v
        for k, x in b.g.items():
            g[k] = g[k] + x * a.v if k in g else x * a.v
        h = {}
        if self.o >= 2:
            for k, x in a.h.items():
                h[k] = x * b.v
            for k, x in b.h.items():
                h[k] = h[k] + x * a.v if k in h else x * a.v
            for i, x in a.g.items():
                for j, y in b.g.items():
                    key = (i, j) if i <= j else (j, i)
                    t = x * y
                    if i == j:
                        t = t + t
                    h[key] = h[key] + t if key in h else t
            # cross terms counted once per ordered pair; for i != j both (i, j) and (j, i) orderings appear across a and b
        return Jet(a.v * b.v, g, h, self.o)
    __rmul__ = __mul__

    def fn(self, f0, f1, f2=None):
        g = {k: x * f1 for k, x in self.g.items()}
        h = {}
        if self.o >= 2:
            for k, x in self.h.items():
                h[k] = x * f1
            items = sorted(self.g.items())
            for p, (i, x) in enumerate(items):
                for j, y in items[p:]:
                    t = (x * y) * f2
                    h[(i, j)] = h[(i, j)] + t if (i, j) in h else t
        return Jet(f0, g, h, self.o)

    def inv(self):
        r = b_inv(self.v)
        r2 = r * r
        return self.fn(r, -r2, (r2 * r) * 2.0 if self.o >= 2 else None)

    def sqrt(self):
        s = b_sqrt(self.v)
        i = b_inv(s)
        return self.fn(s, i * 0.5, (i * b_inv(self.v)) * (-0.25) if self.o >= 2 else None)

    def sincos(self):
        s, c = b_sincos(self.v)
        return self.fn(s, c, -s if self.o >= 2 else None), self.fn(c, -s, -c if self.o >= 2 else None)


# plain base numbers get the same interface
def j_inv(x):
    return x.inv() if isinstance(x, Jet) else b_inv(x)


def j_sqrt(x):
    return x.sqrt() if isinstance(x, Jet) else b_sqrt(x)


def j_sincos(x):
    return x.sincos() if isinstance(x, Jet) else b_sincos(x)


def _val(x):
    return x.v if isinstance(x, Jet) else x


def kepler_base(lam, k, h):
    """solve lam = F - k sin F + h cos F in the base type"""
    if _is_mp(lam):
        F = lam
        for _ in range(200):
            s, c = mpmath.sin(F), mpmath.cos(F)
            d = (F - k * s + h * c - lam) / (1 - k * c - h * s)
            F = F - d
            if abs(d) < mpmath.mpf(2) ** (-mpmath.mp.prec + 8):
                break
        return F
    if isinstance(lam, DD):
        F = kepler_base(lam.hi, k.hi, h.hi)
        F = DD(F)
        for _ in range(2):
            s, c = F.sincos()
            f = F - k * s + h * c - lam
            fp = 1 - k.hi * c.hi - h.hi * s.hi
            F = F - f * (1 / fp)
        return F
    F = lam.copy()
    for _ in range(30):
        s, c = np.sin(F), np.cos(F)
        d = (F - k * s + h * c - lam) / (1 - k * c - h * s)
        F = F - d
        if np.max(np.abs(d)) < 1e-16:
            break
    return F


def kepler(lam, k, h):
    if not isinstance(lam, Jet):
        return kepler_base(lam, k, h)
    F = Jet.const(kepler_base(lam.v, _val(k), _val(h)), lam.o)
    for _ in range(lam.o):
        s, c = F.sincos()
        F = F - (F - k * s + h * c - lam) * (1 - k * c - h * s).inv()
    return F


def planet(lam, La, zr, zi, m2, im2):
    """position and FH momentum of one planet from (lambda, Lambda, Re z, Im z)"""
    P = (zr * zr + zi * zi) * 0.5
    iLa = j_inv(La)
    twoLP = La * 2.0 - P
    eps = j_sqrt(twoLP * (iLa * iLa) * 0.5)
    k = zr * eps
    h = zi * eps * (-1.0)
    F = kepler(lam, k, h)
    s, c = j_sincos(F)
    beta = La * j_inv(twoLP)
    bh, bk = beta * h, beta * k
    hk = bh * k
    a = La * La * im2
    ux = (1.0 - bh * h)
    uy = (1.0 - bk * k)
    X = a * (ux * c + hk * s - k)
    Y = a * (uy * s + hk * c - h)
    rho = 1.0 - k * c - h * s
    w = iLa * m2 * j_inv(rho)
    VX = w * (hk * c - ux * s)
    VY = w * (uy * c - hk * s)
    return X, Y, VX, VY


def H_chain(z, cs, K):
    """z = (b1, b2, b3, Lambda1, I5, I6) as Jets or base numbers; cs = (cos phi, sin phi) and K = consts(...) in the base type"""
    b1, b2, b3, La1, I5, I6 = z
    c, s = cs
    La2 = (I5 + I6 - La1) + K["C"]
    lam1 = b1 + b2
    lam2 = b2
    a3 = b3 - b2
    r5 = j_sqrt(I5 * 2.0)
    r6 = j_sqrt(I6 * 2.0)
    s3, c3 = j_sincos(a3)
    w6r, w6i = r6 * c3, r6 * s3
    z1r, z1i = r5 * c - w6r * s, w6i * (-1.0) * s
    z2r, z2i = r5 * s + w6r * c, w6i * c
    X1, Y1, U1, V1 = planet(lam1, La1, z1r, z1i, K["m2"][0], K["im2"][0])
    X2, Y2, U2, V2 = planet(lam2, La2, z2r, z2i, K["m2"][1], K["im2"][1])
    dx, dy = X1 - X2, Y1 - Y2
    ir = j_inv(j_sqrt(dx * dx + dy * dy))
    su, sv = U1 + U2, V1 + V2
    H1 = (su * su + sv * sv) * 0.5 - ir * K["mm"]
    i1, i2 = j_inv(La1), j_inv(La2)
    return i1 * i1 * K["m3h"][0] + i2 * i2 * K["m3h"][1] + H1 * K["mu"]


def cs_of(phi, kind):
    """(cos phi, sin phi) for a float phi, exactly rounded in the base type"""
    c, s = mpmath.cos(mpmath.mpf(phi)), mpmath.sin(mpmath.mpf(phi))
    if kind == "dd":
        return DD(np.float64(float(c)), np.float64(float(c - float(c)))), DD(np.float64(float(s)), np.float64(float(s - float(s))))
    if kind == "mp":
        return c, s
    return float(c), float(s)


def grad_dd(z, phi, chunk=32768):
    """z: list of 6 DD arrays (flat) -> list of 6 DD gradient arrays"""
    n = z[0].hi.size
    out = [DD(np.zeros(n), np.zeros(n)) for _ in range(6)]
    cs = cs_of(phi, "dd")
    K = consts("dd")
    for a in range(0, n, chunk):
        sl = slice(a, min(n, a + chunk))
        v = [Jet.var(DD(zi.hi[sl], zi.lo[sl]), i, 1) for i, zi in enumerate(z)]
        H = H_chain(v, cs, K)
        for i in range(6):
            out[i].hi[sl] = H.g[i].hi
            out[i].lo[sl] = H.g[i].lo
    return out


def grad_hess(z, phi, chunk=32768, want_hess=True):
    """z: (6, n) float -> grad (6, n), hess (6, 6, n)"""
    n = z.shape[1]
    grad = np.zeros((6, n))
    hess = np.zeros((6, 6, n)) if want_hess else None
    cs = cs_of(phi, "f")
    K = consts("f")
    o = 2 if want_hess else 1
    for a in range(0, n, chunk):
        sl = slice(a, min(n, a + chunk))
        v = [Jet.var(z[i, sl].copy(), i, o) for i in range(6)]
        H = H_chain(v, cs, K)
        for i in range(6):
            grad[i, sl] = H.g[i]
        if want_hess:
            for (i, j), x in H.h.items():
                hess[i, j, sl] = x
                hess[j, i, sl] = x
    return grad, hess


def _H_delaunay_mp(z, phi, K):
    """H through SJS-PLAN's Delaunay route (sjs_chart.H_reg: polar Poincare angles, e = sqrt(1 - (G/L)^2), Kepler in E), mpmath"""
    mp = mpmath.mpf
    b1, b2, b3, La1, I5, I6 = z
    a1, a2, a3 = b1 + b2, b2, b3 - b2
    La2 = K["C"] + I5 + I6 - La1
    c, s = mpmath.cos(phi), mpmath.sin(phi)
    w5 = mpmath.sqrt(2 * I5); w6 = mpmath.sqrt(2 * I6) * mpmath.expj(a3)
    z1 = c * w5 - s * w6; z2 = s * w5 + c * w6
    out = []
    for a, La, zz, m in ((a1, La1, z1, mp(M_STR[0])), (a2, La2, z2, mp(M_STR[1]))):
        P = abs(zz) ** 2 / 2; g = -mpmath.arg(zz); l = a - g; G = La - P
        ratio = G / La; e = mpmath.sqrt(1 - ratio ** 2); A = La ** 2 / m ** 2; B = m ** 2 / La
        E = l
        for _ in range(200):
            E = E - (E - e * mpmath.sin(E) - l) / (1 - e * mpmath.cos(E))
        q1 = A * (mpmath.cos(E) - e); q2 = A * ratio * mpmath.sin(E)
        w = B / (1 - e * mpmath.cos(E)); p1 = -w * mpmath.sin(E); p2 = w * ratio * mpmath.cos(E)
        cg, sg = mpmath.cos(g), mpmath.sin(g)
        out.append((cg * q1 - sg * q2, sg * q1 + cg * q2, cg * p1 - sg * p2, sg * p1 + cg * p2))
    (x1, y1, u1, v1), (x2, y2, u2, v2) = out
    H1 = ((u1 + u2) ** 2 + (v1 + v2) ** 2) / 2 - K["mm"] / mpmath.sqrt((x1 - x2) ** 2 + (y1 - y2) ** 2)
    return K["m3h"][0] / La1 ** 2 + K["m3h"][1] / La2 ** 2 + K["mu"] * H1


def _selftest():
    """against sjs_chart.H_syn (Delaunay route, Taylor algebra, double), the same Delaunay route in mpmath, and an mpmath
    finite difference of H_chain"""
    here = os.path.dirname(os.path.abspath(__file__))
    sys.path.insert(0, os.path.join(here, "..", "plan"))
    import sjs_chart as SC
    sys.path.pop(0)
    rng = np.random.default_rng(5)
    phi = -1.0908
    n = 40
    z = np.stack([rng.uniform(0, 6.28, n), rng.uniform(0, 6.28, n), rng.uniform(0, 6.28, n),
                  2.18 + 1e-4 * rng.standard_normal(n), 1.5e-3 * (1 + 0.2 * rng.standard_normal(n)),
                  6e-4 * (1 + 0.1 * rng.standard_normal(n))])
    # Lambda1 for FH's torus: m1 / n1^(1/3); I5, I6 of the order of the torus's
    z[3] = M[0] / OMEGA[0] ** (1 / 3.0) + 1e-4 * rng.standard_normal(n)
    g, h = grad_hess(z, phi)
    T = SC.tensors("syn", z.astype(complex), phi, deg=2)
    eg = np.abs(T["D1"].real - g).max() / np.abs(g).max()
    eh = np.abs(T["D2"].real - h).max() / np.abs(h).max()
    zd = [DD(z[i].copy()) for i in range(6)]
    gd = grad_dd(zd, phi)
    egd = max(float(np.abs(gd[i].to_float() - g[i]).max()) for i in range(6)) / np.abs(g).max()
    # mpmath: central differences at 3 points, step 1e-30, 200 bits
    cs = cs_of(phi, "mp")
    Kmp = consts("mp")
    emp = 0.0
    for p in range(3):
        zp = [mpmath.mpf(float(z[i, p])) for i in range(6)]
        for i in range(6):
            hstep = mpmath.mpf(10) ** -30
            zp1 = list(zp); zp1[i] += hstep
            zp2 = list(zp); zp2[i] -= hstep
            d = (H_chain(zp1, cs, Kmp) - H_chain(zp2, cs, Kmp)) / (2 * hstep)
            got = mpmath.mpf(float(gd[i].hi[p])) + mpmath.mpf(float(gd[i].lo[p]))
            emp = max(emp, float(abs(got - d)))
    eroute = 0.0
    for p in range(4):
        zp = [mpmath.mpf(float(z[i, p])) for i in range(6)]
        eroute = max(eroute, float(abs(H_chain(zp, cs, Kmp) - _H_delaunay_mp(zp, mpmath.mpf(phi), Kmp))))
    print("H_syn self-test: grad vs sjs_chart %.1e, hess vs sjs_chart %.1e (relative to max; since the two formulas agree at 200 bits, "
          "this gap is rounding in sjs_chart's double evaluation), DD vs float grad %.1e, DD grad vs mpmath %.1e (absolute; |grad| max %.2e), "
          "H regular-Kepler vs Delaunay route at 200 bits %.1e" % (eg, eh, egd, emp, float(np.abs(g).max()), eroute))
    return eg, eh, egd, emp, eroute


if __name__ == "__main__":
    _selftest()
