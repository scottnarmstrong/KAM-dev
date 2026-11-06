"""Rigorous Fourier models on the 2-torus for the SJSU gate-2 ball mirror (SR-4, SR-5, SR-7).

Needs python-flint (arb ball arithmetic; `pip install python-flint`, 0.9.0 used).

A model is a real function f(phi), phi in T^2, written f = p + e:
  * p is a trigonometric polynomial with exact parity, stored by one real coefficient array:
      even:  p = sum_k a_k e^{i k.phi},   a_k real, a_{-k} = a_k   (a cosine series);
      odd:   p = sum_k i b_k e^{i k.phi}, b_k real, b_{-k} = -b_k  (a sine series);
    coefficients are arb balls, so arithmetic on them is rigorous;
  * e is an unknown remainder with ||e||_W <= eps, where ||f||_W = sum_k |f_k| (1 + h(k)) and
    h(k) = |k1| + |k2| + |k1 + k2| is the hexagonal norm.  (1 + h) is submultiplicative, so ||.||_W is a
    Banach algebra norm; ||f||_sup <= ||f||_1 <= ||f||_W and ||d_phi_a f||_1 <= ||f||_W (|k_a| <= h(k)).
Products are Kronecker-packed into one arb_poly: operand index (k1 + CP) + S (k2 + CP), product index
(k1 + 2CP) + S (k2 + 2CP), stride S = 4 CP + 1, so that products of two models with |k_i| <= CP never wrap.
After a product the support is truncated to the hexagon h(k) <= KH (KH <= 2 CP) and the dropped modes are
added to eps in the W-norm.

Fixed-point emulation (for SR-5): `fx` is the coefficient of 2^-p in the W-norm error that a checker with p
fractional bits per model (scaled to the model's largest coefficient) would add; it is propagated with the
same first-order rules as eps.  It is an estimate for sizing, not part of the rigorous bound.
"""
from __future__ import annotations

from fractions import Fraction

from flint import arb, arb_poly, ctx, fmpq

ZERO = arb(0)


def hexn(k1, k2):
    return abs(k1) + abs(k2) + abs(k1 + k2)


def to_arb(x):
    if isinstance(x, Fraction):
        return arb(fmpq(x.numerator, x.denominator))
    return arb(x)


class Layout:
    def __init__(self, CP, KH, prec=160):
        assert KH <= 2 * CP
        ctx.prec = prec
        self.CP, self.KH, self.S = CP, KH, 4 * CP + 1
        S = self.S
        self.op_len = S * 2 * CP + 2 * CP + 1
        self.shift = CP * (S + 1)  # operand -> product layout
        # operand box |k_i| <= CP
        self.op_modes = [(k1, k2, (k1 + CP) + S * (k2 + CP), hexn(k1, k2))
                         for k2 in range(-CP, CP + 1) for k1 in range(-CP, CP + 1)]
        # product box |k_i| <= 2 CP: (prod index, operand index or -1 if outside KH, h, k1, k2)
        self.prod_modes = []
        for k2 in range(-2 * CP, 2 * CP + 1):
            for k1 in range(-2 * CP, 2 * CP + 1):
                h = hexn(k1, k2)
                oi = (k1 + CP) + S * (k2 + CP) if h <= KH else -1
                self.prod_modes.append(((k1 + 2 * CP) + S * (k2 + 2 * CP), oi, h, k1, k2))
        self.log = []          # straight-line program: (stage, kind, cA, cB) per product
        self.stage = ''
        self.n_unpack = 0


class FM:
    """A model in operand layout."""
    __slots__ = ('L', 'poly', 'par', 'eps', 'fx', 'nW', 'n1', 'c', 'maxabs')

    def __init__(self, L, poly, par, eps=ZERO, fx=0.0, c=None, norms=None):
        self.L, self.poly, self.par, self.eps, self.fx = L, poly, par, eps, fx
        self.c = L.CP if c is None else c
        if norms is None:
            norms = op_norms(L, poly)
        self.nW, self.n1, self.maxabs = norms

    @staticmethod
    def from_coeffs(L, coeffs, par, eps=ZERO, fx=0.0):
        """coeffs: dict (k1, k2) -> number (exact parity is the caller's job; checked here)."""
        lst = [ZERO] * L.op_len
        c = 0
        for (k1, k2), v in coeffs.items():
            if hexn(k1, k2) > L.KH:
                raise ValueError('mode outside KH')
            lst[(k1 + L.CP) + L.S * (k2 + L.CP)] = to_arb(v)
            c = max(c, abs(k1), abs(k2))
        for (k1, k2), v in coeffs.items():
            w = coeffs.get((-k1, -k2), 0)
            if (par == 0 and w != v) or (par == 1 and w != -v):
                raise ValueError('parity violated at %s' % ((k1, k2),))
        return FM(L, arb_poly(lst), par, eps, fx, c)

    def coeffs(self):
        cs = self.poly.coeffs()
        out = {}
        for k1, k2, oi, h in self.L.op_modes:
            if oi < len(cs) and not cs[oi].is_zero():
                out[(k1, k2)] = cs[oi]
        return out

    def scale(self, s):
        a = to_arb(s)
        return FM(self.L, self.poly * a, self.par, self.eps * abs(a), self.fx * abs(float(s)), self.c,
                  (self.nW * abs(a), self.n1 * abs(a), self.maxabs * abs(float(s))))

    def dphi(self, a):
        """d/dphi_a (a = 0, 1); the result's eps is an l1 bound (not W)."""
        cs = self.poly.coeffs()
        lst = [ZERO] * self.L.op_len
        for k1, k2, oi, h in self.L.op_modes:
            if oi < len(cs):
                ka = k1 if a == 0 else k2
                if ka:
                    lst[oi] = cs[oi] * (ka if self.par == 0 else -ka)
        return FM(self.L, arb_poly(lst), 1 - self.par, self.eps, self.fx, self.c)

    def eval(self, phi1, phi2):
        """Value at a point (arb inputs allowed); remainder not included."""
        cs = self.poly.coeffs()
        s = arb(0)
        for k1, k2, oi, h in self.L.op_modes:
            if oi < len(cs) and not cs[oi].is_zero():
                t = k1 * phi1 + k2 * phi2
                s += cs[oi] * (t.cos() if self.par == 0 else -t.sin())
        return s


def op_norms(L, poly):
    cs = poly.coeffs()
    lev = {}
    mx = 0.0
    for k1, k2, oi, h in L.op_modes:
        if oi < len(cs):
            c = cs[oi]
            if not c.is_zero():
                u = c.abs_upper()
                lev[h] = lev.get(h, ZERO) + u
                f = float(u)
                if f > mx:
                    mx = f
    nW = ZERO
    n1 = ZERO
    for h, v in lev.items():
        nW += v * (1 + h)
        n1 += v
    return nW, n1, mx


def lincomb(L, terms):
    """sum s_i f_i for models of equal parity (operand layout, no products)."""
    par = terms[0][1].par
    poly = arb_poly([])
    eps, fx = ZERO, 0.0
    c = 0
    for s, f in terms:
        assert f.par == par
        a = to_arb(s)
        poly = poly + f.poly * a
        eps += f.eps * abs(a)
        fx += f.fx * abs(float(s))
        c = max(c, f.c)
    return FM(L, poly, par, eps, fx, c)


class Acc:
    """A sum of products, in product layout (no truncation yet)."""
    __slots__ = ('L', 'poly', 'par', 'eps', 'fx', 'c', 'n')

    def __init__(self, L, par):
        self.L, self.poly, self.par, self.eps, self.fx, self.c, self.n = L, arb_poly([]), par, ZERO, 0.0, 0, 0

    def addmul(self, s, A, B, kind=''):
        par = (A.par + B.par) % 2
        assert par == self.par, 'parity mismatch'
        sgn = -1 if (A.par == 1 and B.par == 1) else 1  # (i b)(i b') = -b b'
        a = to_arb(s) * sgn
        if A.c <= B.c:
            self.poly = self.poly + (A.poly * a) * B.poly
        else:
            self.poly = self.poly + A.poly * (B.poly * a)
        aa = abs(a)
        self.eps += aa * (A.eps * B.nW + A.nW * B.eps + A.eps * B.eps)
        self.fx += abs(float(s)) * (A.fx * float(B.nW) + float(A.nW) * B.fx)
        self.c = max(self.c, A.c + B.c)
        self.n += 1
        self.L.log.append((self.L.stage, kind, A.c, B.c))

    def addfm(self, s, A):
        assert A.par == self.par
        a = to_arb(s)
        self.poly = self.poly + (A.poly * a).left_shift(self.L.shift)
        self.eps += abs(a) * A.eps
        self.fx += abs(float(s)) * A.fx
        self.c = max(self.c, A.c)

    def norms(self):
        """(||p||_1, ||p||_W) of the polynomial part over the whole product box (no truncation)."""
        cs = self.poly.coeffs()
        lev = {}
        for pi, oi, h, k1, k2 in self.L.prod_modes:
            if pi < len(cs):
                c = cs[pi]
                if not c.is_zero():
                    lev[h] = lev.get(h, ZERO) + c.abs_upper()
        n1, nW = ZERO, ZERO
        for h, v in lev.items():
            n1 += v
            nW += v * (1 + h)
        return n1, nW

    def norms_by_level(self):
        cs = self.poly.coeffs()
        lev = {}
        for pi, oi, h, k1, k2 in self.L.prod_modes:
            if pi < len(cs):
                c = cs[pi]
                if not c.is_zero():
                    lev[h] = lev.get(h, ZERO) + c.abs_upper()
        return lev

    def unpack(self, emulate_round=True):
        """Truncate to h <= KH: a model in operand layout, dropped modes added to eps (W-norm)."""
        L = self.L
        L.n_unpack += 1
        cs = self.poly.coeffs()
        lst = [ZERO] * L.op_len
        drop = {}
        keep = {}
        mx = 0.0
        c = 0
        wsum = 0
        for pi, oi, h, k1, k2 in L.prod_modes:
            if pi >= len(cs):
                continue
            v = cs[pi]
            if v.is_zero():
                continue
            u = v.abs_upper()
            if oi < 0:
                drop[h] = drop.get(h, ZERO) + u
            else:
                lst[oi] = v
                keep[h] = keep.get(h, ZERO) + u
                wsum += 1 + h
                f = float(u)
                if f > mx:
                    mx = f
                c = max(c, abs(k1), abs(k2))
        eps = self.eps
        for h, v in drop.items():
            eps += v * (1 + h)
        nW, n1 = ZERO, ZERO
        for h, v in keep.items():
            nW += v * (1 + h)
            n1 += v
        fx = self.fx
        if emulate_round and mx > 0:
            # rounding every kept coefficient to an absolute grid 2^-p * max|coef| (W-norm of the error)
            fx += mx * wsum
        return FM(L, arb_poly(lst), self.par, eps, fx, c, (nW, n1, mx))


def binom_q(alpha: Fraction, m: int) -> Fraction:
    out = Fraction(1)
    for i in range(m):
        out = out * (alpha - i) / (i + 1)
    return out
