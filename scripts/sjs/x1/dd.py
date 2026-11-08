#!/usr/bin/env python3
"""SJS-X1: double-double arithmetic on numpy arrays, and a double-double FFT.

Untrusted design tooling.  A DD is an unevaluated sum hi + lo of two float64 arrays with |lo| <= ulp(hi)/2, giving about
32 significant digits (unit roundoff 2^-104 ~ 4.9e-32).  Error-free transforms: Knuth's two_sum and Dekker's two_prod (numpy
has no fused multiply-add; Dekker's splitting is exact in IEEE double).  Algorithms as in Hida, Li and Bailey's QD library
(the accurate addition), with sin and cos by a 1024-entry table and a Taylor series of the remainder (|t| <= pi/1024).
CDD is a complex DD; fft_axis is a mixed-radix (2, 3) Cooley-Tukey transform along one axis with twiddles exact to DD.
"""
import math
import numpy as np
import mpmath

mpmath.mp.prec = 200
SPLIT = 134217729.0  # 2^27 + 1


def two_sum(a, b):
    s = a + b
    bb = s - a
    return s, (a - (s - bb)) + (b - bb)


def quick_two_sum(a, b):
    s = a + b
    return s, b - (s - a)


def two_prod(a, b):
    p = a * b
    t = SPLIT * a
    ah = t - (t - a)
    al = a - ah
    t = SPLIT * b
    bh = t - (t - b)
    bl = b - bh
    return p, ((ah * bh - p) + ah * bl + al * bh) + al * bl


def _const(x):
    """an mpmath number -> (hi, lo) python floats"""
    hi = float(x)
    return hi, float(x - hi)


class DD:
    __slots__ = ("hi", "lo")

    def __init__(self, hi, lo=None):
        self.hi = np.asarray(hi, dtype=float)
        self.lo = np.zeros_like(self.hi) if lo is None else lo

    @staticmethod
    def mp(x, like=None):
        h, l = _const(mpmath.mpf(x))
        if like is None:
            return DD(np.float64(h), np.float64(l))
        return DD(np.full(np.shape(like.hi if isinstance(like, DD) else like), h),
                  np.full(np.shape(like.hi if isinstance(like, DD) else like), l))

    def copy(self):
        return DD(self.hi.copy(), self.lo.copy())

    def __getitem__(self, idx):
        return DD(self.hi[idx], self.lo[idx])

    def __setitem__(self, idx, v):
        v = _dd(v)
        self.hi[idx] = v.hi
        self.lo[idx] = v.lo

    @property
    def shape(self):
        return self.hi.shape

    def __neg__(self):
        return DD(-self.hi, -self.lo)

    def __add__(self, o):
        if isinstance(o, DD):
            s, e = two_sum(self.hi, o.hi)
            t, f = two_sum(self.lo, o.lo)
            s, e = quick_two_sum(s, e + t)
            return DD(*quick_two_sum(s, e + f))
        s, e = two_sum(self.hi, o)
        return DD(*quick_two_sum(s, e + self.lo))
    __radd__ = __add__

    def __sub__(self, o):
        return self + (-o)

    def __rsub__(self, o):
        return (-self) + o

    def __mul__(self, o):
        if isinstance(o, DD):
            p, e = two_prod(self.hi, o.hi)
            return DD(*quick_two_sum(p, e + (self.hi * o.lo + self.lo * o.hi)))
        p, e = two_prod(self.hi, o)
        return DD(*quick_two_sum(p, e + self.lo * o))
    __rmul__ = __mul__

    def __truediv__(self, o):
        o = _dd(o)
        q1 = self.hi / o.hi
        r = self - o * q1
        q2 = r.hi / o.hi
        r = r - o * q2
        q3 = r.hi / o.hi
        s, e = quick_two_sum(q1, q2)
        return DD(s, e) + q3

    def __rtruediv__(self, o):
        return _dd(o, self) / self

    def inv(self):
        return _dd(1.0, self) / self

    def sqrt(self):
        x = np.sqrt(self.hi)
        p, e = two_prod(x, x)
        r = (self - DD(p, e)).hi
        return DD(*quick_two_sum(x, r / (2 * x)))

    def sincos(self):
        return dd_sincos(self)

    def to_float(self):
        return self.hi + self.lo


def _dd(x, like=None):
    if isinstance(x, DD):
        return x
    if like is not None and np.ndim(x) == 0:
        return DD(np.full(like.shape, float(x)))
    return DD(np.asarray(x, dtype=float))


# ---- sin and cos -------------------------------------------------------------------------------------------------------
NT = 1024
TWO_PI = DD(*_const(2 * mpmath.pi))
STEP = DD(*_const(2 * mpmath.pi / NT))
_TS = np.array([_const(mpmath.sin(2 * mpmath.pi * j / NT)) for j in range(NT)])
_TC = np.array([_const(mpmath.cos(2 * mpmath.pi * j / NT)) for j in range(NT)])
_FAC = [_const(1 / mpmath.factorial(n)) for n in range(16)]


def dd_sincos(a):
    n = np.rint(a.hi / TWO_PI.hi)
    r = a - TWO_PI * n
    m = np.rint(r.hi / STEP.hi)
    t = r - STEP * m
    j = np.mod(m.astype(np.int64), NT)
    t2 = t * t
    # sin t = t (1 - t2/3! + t2^2/5! - ...), cos t = 1 - t2/2! + ..., through t^13 and t^14 (|t| <= pi/1024)
    s = DD(np.full(t.shape, _FAC[13][0]), np.full(t.shape, _FAC[13][1]))
    for k in (11, 9, 7, 5, 3, 1):
        s = _horner_step(s, t2, k)
    s = s * t
    c = DD(np.full(t.shape, _FAC[14][0]), np.full(t.shape, _FAC[14][1]))
    for k in (12, 10, 8, 6, 4, 2, 0):
        c = _horner_step(c, t2, k)
    S = DD(_TS[j, 0], _TS[j, 1])
    C = DD(_TC[j, 0], _TC[j, 1])
    return S * c + C * s, C * c - S * s


def _horner_step(p, t2, k):
    """p <- 1/k! - t2 p (alternating series in t2)"""
    q = p * t2
    return DD(np.full(q.shape, _FAC[k][0]), np.full(q.shape, _FAC[k][1])) - q


# ---- complex DD and the FFT -------------------------------------------------------------------------------------------
class CDD:
    __slots__ = ("re", "im")

    def __init__(self, re, im=None):
        self.re = re
        self.im = DD(np.zeros_like(re.hi)) if im is None else im

    def __add__(self, o):
        return CDD(self.re + o.re, self.im + o.im)

    def __sub__(self, o):
        return CDD(self.re - o.re, self.im - o.im)

    def __mul__(self, o):
        return CDD(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)

    def scale(self, x):
        return CDD(self.re * x, self.im * x)

    def __getitem__(self, idx):
        return CDD(self.re[idx], self.im[idx])

    @property
    def shape(self):
        return self.re.shape

    def conj(self):
        return CDD(self.re, -self.im)

    def to_complex(self):
        return self.re.to_float() + 1j * self.im.to_float()


def _stack(parts, axis):
    return CDD(DD(np.concatenate([p.re.hi for p in parts], axis), np.concatenate([p.re.lo for p in parts], axis)),
               DD(np.concatenate([p.im.hi for p in parts], axis), np.concatenate([p.im.lo for p in parts], axis)))


_TW = {}


def _twiddle(n, r, sign):
    """W[j, k] = exp(sign 2 pi i j k / n), j < r, k < n / r, as CDD of shape (r, n/r)"""
    key = (n, r, sign)
    if key not in _TW:
        m = n // r
        re = np.zeros((r, m, 2)); im = np.zeros((r, m, 2))
        for j in range(r):
            for k in range(m):
                x = sign * 2 * mpmath.pi * j * k / n
                re[j, k] = _const(mpmath.cos(x)); im[j, k] = _const(mpmath.sin(x))
        _TW[key] = CDD(DD(re[..., 0], re[..., 1]), DD(im[..., 0], im[..., 1]))
    return _TW[key]


_W3 = {s: CDD(DD(*_const(mpmath.cos(s * 2 * mpmath.pi / 3))), DD(*_const(mpmath.sin(s * 2 * mpmath.pi / 3))))
       for s in (-1, 1)}


def _fft_last(x, sign):
    """unnormalized DFT along the last axis, X_k = sum_j x_j exp(sign 2 pi i j k / n); n = 2^a 3^b"""
    n = x.shape[-1]
    if n == 1:
        return x
    r = 2 if n % 2 == 0 else (3 if n % 3 == 0 else None)
    if r is None:
        raise ValueError("length %d is not 2^a 3^b" % n)
    m = n // r
    subs = [_fft_last(x[..., j::r], sign) for j in range(r)]
    W = _twiddle(n, r, sign)
    t = [subs[0]] + [subs[j] * W[j] for j in range(1, r)]
    if r == 2:
        return _stack([t[0] + t[1], t[0] - t[1]], -1)
    w, w2 = _W3[sign], _W3[-sign]          # exp(sign 2 pi i / 3) and its square exp(-sign 2 pi i / 3)
    a = t[1] * w; b = t[2] * w2
    c = t[1] * w2; d = t[2] * w
    return _stack([t[0] + t[1] + t[2], t[0] + a + b, t[0] + c + d], -1)


def fft_axis(x, axis, sign=-1):
    if axis in (-1, x.re.hi.ndim - 1):
        return _fft_last(x, sign)
    mv = lambda d: DD(np.moveaxis(d.hi, axis, -1), np.moveaxis(d.lo, axis, -1))
    y = _fft_last(CDD(mv(x.re), mv(x.im)), sign)
    back = lambda d: DD(np.ascontiguousarray(np.moveaxis(d.hi, -1, axis)), np.ascontiguousarray(np.moveaxis(d.lo, -1, axis)))
    return CDD(back(y.re), back(y.im))


def fftn(x, axes=(-3, -2, -1), sign=-1):
    for ax in axes:
        x = fft_axis(x, ax, sign)
    return x


def _selftest():
    rng = np.random.default_rng(3)
    a = DD(rng.standard_normal(50), rng.standard_normal(50) * 1e-17)
    b = DD(rng.uniform(0.5, 2, 50), rng.standard_normal(50) * 1e-17)
    mp = lambda d, i: mpmath.mpf(float(d.hi[i])) + mpmath.mpf(float(d.lo[i]))
    err = 0.0
    for op, f in (("add", lambda x, y: x + y), ("mul", lambda x, y: x * y), ("div", lambda x, y: x / y)):
        c = f(a, b)
        for i in range(50):
            ref = f(mp(a, i), mp(b, i))
            err = max(err, float(abs(mp(c, i) - ref) / abs(ref)))
    s = b.sqrt()
    for i in range(50):
        err = max(err, float(abs(mp(s, i) - mpmath.sqrt(mp(b, i))) / mpmath.sqrt(mp(b, i))))
    x = DD(rng.uniform(-40, 40, 200), rng.standard_normal(200) * 1e-16)
    sn, cs = dd_sincos(x)
    e2 = 0.0
    for i in range(200):
        xi = mp(x, i)
        e2 = max(e2, float(abs(mp(sn, i) - mpmath.sin(xi))), float(abs(mp(cs, i) - mpmath.cos(xi))))
    n = 24
    re = rng.standard_normal((2, n)); im = rng.standard_normal((2, n))
    X = _fft_last(CDD(DD(re), DD(im)), -1)
    e3 = 0.0
    for row in range(2):
        for k in range(n):
            ref = mpmath.fsum([mpmath.mpc(re[row, j], im[row, j]) * mpmath.expjpi(-2 * mpmath.mpf(j * k) / n) for j in range(n)])
            got = mpmath.mpc(mp(X.re[row], k), mp(X.im[row], k))
            e3 = max(e3, float(abs(got - ref)))
    print("DD self-test: rel err add/mul/div/sqrt %.2e, sincos abs err %.2e, fft(24) abs err %.2e" % (err, e2, e3))
    return max(err, e2, e3 / 10)


if __name__ == "__main__":
    assert _selftest() < 1e-29
