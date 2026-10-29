"""Rotated-frame (owner ruling O5) certificate tooling: exact sparse Fourier models on the strip.  Untrusted tooling.

Conventions (as model.py): angles (psi, phi), characters e_kappa = exp(2 pi i (k psi + l phi)), kappa = (k, l).
The strip is T_rho = {|Im psi|, |Im phi| < rho} (KAM `complexStrip 2 rho`), on which |e_kappa| <= w^|kappa|_1 with
w = exp(2 pi rho).  A model (SPoly) is a finite Fourier polynomial with EXACT dyadic coefficients plus a radius r:
it denotes every function f with sup_{T_rho} |f - P| <= r (the checker's CertModel semantics, design decision 5).
All norms are the checker's: ||f||_w = sum |c_kappa| W(|kappa|_1) + r with a rigorous integer table W(n) >= w^n, so
||f||_w >= sup_{T_rho} |f|.  Every rounding is outward: dropped / rounded coefficient mass goes into the radius,
radii are floats rounded up after every operation (`up`).

Parity: every function here is real on reals with a definite parity, so its coefficients are either real and even
(phase 0) or i * (real, odd) (phase 1).  An SPoly stores the real integers `vals` at scale 2^S plus the phase.
"""
import json, math, os
import numpy as np
from fractions import Fraction as F
import mpmath
from mpmath import iv

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
CERT = os.path.join(ROOT, "certificates", "lunar-spin-orbit")

INF = float("inf")


def up(x):
    """float >= x for a float/int/Fraction x (correctly rounded conversion, then one ulp up)."""
    if isinstance(x, F):
        x = x.numerator / x.denominator          # correctly rounded int/int division
    else:
        x = float(x)
    return math.nextafter(x, INF) if x != 0 else 0.0


def addu(*xs):
    s = 0.0
    for x in xs:
        s = up(s + x)
    return s


def mulu(a, b):
    return up(a * b)


# ---------------------------------------------------------------------------------------------- weights
WB = 64   # weight table scale bits


class Weights:
    """W[n] = integer >= exp(2 pi rho n) 2^WB (interval arithmetic upper endpoint, ceiling)."""

    def __init__(self, rho, nmax=1200):
        self.rho = F(rho)
        iv.prec = 160
        r = iv.mpf(self.rho.numerator) / self.rho.denominator
        tw = 2 * iv.pi * r
        self.W = np.empty(nmax + 1, dtype=object)
        for n in range(nmax + 1):
            ub = (iv.exp(tw * n)).b
            self.W[n] = int(mpmath.ceil(ub * 2**WB)) + 1
        self.nmax = nmax

    def w_up(self):
        """float upper bound of w = exp(2 pi rho)."""
        return up(F(self.W[1], 1 << WB))


# ---------------------------------------------------------------------------------------------- pi
def two_pi_interval(S):
    """(c, e): c a dyadic Fraction at scale 2^S, |2 pi - c| <= e (float)."""
    mpmath.mp.prec = S + 64
    c = F(int(mpmath.nint(2 * mpmath.pi * 2**S)), 1 << S)
    return c, up(F(1, 1 << S))


# ---------------------------------------------------------------------------------------------- sparse polys
def _obj(a):
    o = np.empty(len(a), dtype=object)
    o[:] = list(a)
    return o


def _rshift_round(vals, sh):
    """round-to-nearest right shift of an object array of ints; returns (new, max |error| numerator at old scale)."""
    if sh <= 0:
        return vals * (1 << (-sh)), 0
    half = 1 << (sh - 1)
    return _obj([(int(x) + half) >> sh for x in vals]), half


class SPoly:
    __slots__ = ("k", "l", "v", "S", "ph", "r")

    def __init__(self, k, l, v, S, ph=0, r=0.0):
        self.k = np.asarray(k, dtype=np.int64)
        self.l = np.asarray(l, dtype=np.int64)
        self.v = v if isinstance(v, np.ndarray) and v.dtype == object else _obj(v)
        self.S, self.ph, self.r = S, ph, float(r)

    # -- constructors
    @staticmethod
    def zero(S=0, ph=0):
        return SPoly([], [], [], S, ph, 0.0)

    @staticmethod
    def const(c, S):
        """exact constant c (dyadic Fraction or int) at scale S (must be exact)."""
        c = F(c)
        n = c * (1 << S)
        assert n.denominator == 1, "constant not dyadic at this scale"
        return SPoly([0], [0], [int(n)], S, 0, 0.0)

    @staticmethod
    def from_dict(d, S, ph=0, r=0.0):
        ks = list(d.keys())
        return SPoly([a for a, _ in ks], [b for _, b in ks], [d[x] for x in ks], S, ph, r)

    def to_dict(self):
        return {(int(a), int(b)): int(x) for a, b, x in zip(self.k, self.l, self.v)}

    def copy(self):
        return SPoly(self.k.copy(), self.l.copy(), self.v.copy(), self.S, self.ph, self.r)

    def __len__(self):
        return len(self.v)

    # -- norms
    def l1w(self, Wt):
        """sum |c| W(|kappa|) upper bound (float), without the radius."""
        if len(self.v) == 0:
            return 0.0
        n = np.abs(self.k) + np.abs(self.l)
        assert n.max() <= Wt.nmax
        tot = int((np.abs(self.v) * Wt.W[n]).sum())
        return up(F(tot, 1 << (self.S + WB)))

    def norm(self, Wt):
        return addu(self.l1w(Wt), self.r)

    def maxdeg(self):
        return int((np.abs(self.k) + np.abs(self.l)).max()) if len(self.v) else 0

    def coeff0(self):
        """exact zero-mode coefficient (Fraction, real part if phase 0; phase-1 functions have 0 mean)."""
        if self.ph == 1:
            return F(0)
        m = (self.k == 0) & (self.l == 0)
        return F(int(self.v[m].sum()) if m.any() else 0, 1 << self.S)

    # -- structural ops
    def rescale(self, S):
        """exact re-scaling to a larger S."""
        assert S >= self.S
        return SPoly(self.k, self.l, self.v * (1 << (S - self.S)), S, self.ph, self.r)

    def neg(self):
        return SPoly(self.k, self.l, -self.v, self.S, self.ph, self.r)

    def round_to(self, S, Wt, thr=0):
        """round coefficients to scale S (nearest), drop |c| < thr (Fraction or 0); error mass into the radius."""
        k, l, v, r = self.k, self.l, self.v, self.r
        if thr:
            ti = int(math.ceil(F(thr) * (1 << self.S)))
            keep = np.abs(v) >= ti
            if (~keep).any():
                drop = SPoly(k[~keep], l[~keep], v[~keep], self.S, self.ph)
                r = addu(r, drop.l1w(Wt))
                k, l, v = k[keep], l[keep], v[keep]
        sh = self.S - S
        if sh > 0:
            nv, half = _rshift_round(v, sh)
            if len(v):
                n = np.abs(k) + np.abs(l)
                tot = int(Wt.W[n].sum()) * half
                r = addu(r, up(F(tot, 1 << (self.S + WB))))
            v = nv
        elif sh < 0:
            v = v * (1 << (-sh))
        nz = v != 0
        return SPoly(k[nz], l[nz], v[nz], S, self.ph, r)

    def add(self, o, sign=1):
        if len(o.v) == 0 and o.r == 0:
            return self.copy()
        if len(self.v) == 0 and self.r == 0:
            return o.copy() if sign == 1 else o.neg()
        assert self.ph == o.ph, "parity/phase mismatch in add"
        S = max(self.S, o.S)
        a = self.rescale(S); b = o.rescale(S)
        d = {}
        for x, y, z in zip(a.k.tolist(), a.l.tolist(), a.v):
            d[(x, y)] = z
        for x, y, z in zip(b.k.tolist(), b.l.tolist(), b.v):
            d[(x, y)] = d.get((x, y), 0) + sign * z
        d = {kk: vv for kk, vv in d.items() if vv != 0}
        return SPoly.from_dict(d, S, self.ph, addu(self.r, o.r))

    def sub(self, o):
        return self.add(o, -1)

    def mul_int(self, m):
        return SPoly(self.k, self.l, self.v * m, self.S, self.ph, mulu(abs(m), self.r))

    def mul_frac(self, q, Wt, S=None):
        """multiply by an exact rational q, round the result to scale S (default self.S)."""
        q = F(q)
        S = self.S if S is None else S
        num = self.v * q.numerator
        # exact value num / (den 2^self.S); write at scale S with rounding: n = round(num 2^S / (den 2^self.S))
        den = q.denominator << self.S
        out = []
        err = False
        for x in num:
            y = int(x) << S
            qq, rr = divmod(y, den)
            if 2 * rr >= den:
                qq += 1
            if rr:
                err = True
            out.append(qq)
        r = mulu(abs(float(q)) * (1 + 1e-15), self.r) if self.r else 0.0
        if err and len(out):
            n = np.abs(self.k) + np.abs(self.l)
            r = addu(r, up(F(int(Wt.W[n].sum()), 1 << (S + 1 + WB))))
        res = SPoly(self.k, self.l, _obj(out), S, self.ph, r)
        nz = res.v != 0
        return SPoly(res.k[nz], res.l[nz], res.v[nz], S, self.ph, r)

    def mul_iv(self, c, e, Wt, S=None):
        """multiply by an uncertain scalar in [c - e, c + e] (c exact Fraction, e float)."""
        res = self.mul_frac(c, Wt, S)
        res.r = addu(res.r, mulu(e, self.norm(Wt)))
        return res

    def times_i(self):
        """multiply by i: phase 0 -> 1 keeps vals; phase 1 -> 0 negates (i * i = -1)."""
        if self.ph == 0:
            return SPoly(self.k, self.l, self.v, self.S, 1, self.r)
        return SPoly(self.k, self.l, -self.v, self.S, 0, self.r)

    def dpsi(self):
        """index-unit derivative d/dpsi / (2 pi): multiply coefficient by i k.  Exact polynomial only."""
        assert self.r == 0, "derivative of a model with radius"
        return SPoly(self.k, self.l, self.v * self.k.astype(object), self.S, self.ph, 0.0).times_i()

    def dphi(self):
        assert self.r == 0, "derivative of a model with radius"
        return SPoly(self.k, self.l, self.v * self.l.astype(object), self.S, self.ph, 0.0).times_i()

    def dir_deriv(self, a, b):
        """index-unit derivative along (a, b) with integer a, b."""
        assert self.r == 0
        m = self.k.astype(object) * a + self.l.astype(object) * b
        return SPoly(self.k, self.l, self.v * m, self.S, self.ph, 0.0).times_i()

    def shift(self, s):
        """multiply by e_s (only for building models; phase handled by the caller)."""
        return SPoly(self.k + s[0], self.l + s[1], self.v, self.S, self.ph, self.r)

    def mul(self, o, Wt, S=None, thr=0):
        """product model; exact convolution (scale Sa + Sb), then optionally round to scale S and drop |c| < thr."""
        if S is None:
            S = self.S + o.S
        k, l, v = conv(self.k, self.l, self.v, o.k, o.l, o.v)
        ph = self.ph + o.ph
        if ph >= 2:
            v = -v; ph -= 2
        r = 0.0
        if self.r or o.r:
            na, nb = self.l1w(Wt), o.l1w(Wt)
            r = addu(mulu(na, o.r), mulu(self.r, nb), mulu(self.r, o.r))
        res = SPoly(k, l, v, self.S + o.S, ph, r)
        return res.round_to(S, Wt, thr)

    def eval_grid(self, N1, N2, ypsi=0.0, yphi=0.0):
        """complex128 values on the N1 x N2 grid at Im = (ypsi, yphi) (head only; double precision)."""
        C = np.zeros((N1, N2), complex)
        if len(self.v):
            c = np.array([float(F(int(x), 1 << self.S)) for x in self.v])
            if self.ph == 1:
                c = 1j * c
            c = c * np.exp(-2 * math.pi * (self.k * ypsi + self.l * yphi))
            np.add.at(C, (self.k % N1, self.l % N2), c)
        return np.fft.ifft2(C) * N1 * N2


def conv(ak, al, av, bk, bl, bv):
    """exact 2-D convolution of sparse integer polys (object arrays); returns (k, l, v) without zeros."""
    if len(av) == 0 or len(bv) == 0:
        return np.zeros(0, np.int64), np.zeros(0, np.int64), _obj([])
    if len(av) > len(bv):
        ak, al, av, bk, bl, bv = bk, bl, bv, ak, al, av
    akmin, almin, bkmin, blmin = ak.min(), al.min(), bk.min(), bl.min()
    nl = int(al.max() - almin + bl.max() - blmin + 1)
    nk = int(ak.max() - akmin + bk.max() - bkmin + 1)
    out = np.empty(nk * nl, dtype=object)
    out.fill(0)
    bidx = (bk - bkmin) * nl + (bl - blmin)
    aidx = (ak - akmin) * nl + (al - almin)
    for i in range(len(av)):
        idx = bidx + aidx[i]
        out[idx] += av[i] * bv
    nz = np.nonzero(out != 0)[0]
    kk = nz // nl + akmin + bkmin
    ll = nz % nl + almin + blmin
    return kk.astype(np.int64), ll.astype(np.int64), out[nz]


# ---------------------------------------------------------------------------------------------- data
def load_candidate(which):
    """SO-GEN 1e-130 data: b (half lattice H, sin coefficients of v) and Ehat (full lattice), both at 2^-P."""
    d = json.load(open(os.path.join(CERT, "%s.json" % which)))
    P = d["scale_bits"]
    b = {(k, l): int(n) for k, l, n in d["v_sin"]}
    E = {(k, l): int(n) for k, l, n in d["E_re"]}
    return b, E, P


def sin_series(b, S, ph_check=True):
    """v = sum_{H} b sin(2 pi kappa.theta) as a phase-1 SPoly at scale S+1 (b ints at scale S)."""
    ks, ls, vs = [], [], []
    for (k, l), n in b.items():
        ks += [k, -k]; ls += [l, -l]; vs += [-n, n]          # b sin = i(-b/2) e_kappa + i(b/2) e_-kappa
    return SPoly(ks, ls, vs, S + 1, 1)


def cos_series(c, c0, S):
    """c0 + sum_{H} c cos(2 pi kappa.theta) as a phase-0 SPoly at scale S+1 (ints at scale S)."""
    ks, ls, vs = [0], [0], [2 * c0]
    for (k, l), n in c.items():
        ks += [k, -k]; ls += [l, -l]; vs += [n, n]
    return SPoly(ks, ls, vs, S + 1, 0)


def full_dict(E):
    return SPoly.from_dict(E, 0)
