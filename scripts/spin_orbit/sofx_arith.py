#!/usr/bin/env python3
"""SO-DATA-1: backend-generic mirror of the LANDED certified arithmetic (untrusted tooling).

Every function transcribes the Lean definition of the same name for an arbitrary `CertArith` backend:

  Arith/Interface.lean   CertArith (the backend object `B`)
  Arith/Rat.lean         instCertArithRat          -> RatB
  Arith/Fixed.lean       instCertArithFixed P      -> FixedB(P)   (m ↦ m / 2^P; mul floors, upMul ceils)
  Arith/PiHigh.lean      piLoQ, piUpQ, atanS, piLowRat, piUpRat, eRem
  Arith/PiEnclosure.lean checkPiEnclosure
  Arith/Roots.lean       CC.normUp, CertBall.{ofRat, oneBall, plus, mulReErr, mulImErr, times, expAux}, certCExp,
                         certCExpSmall
  Arith/ComplexExp.lean  certBallSquareIter, certCExpReduced
  Arith/Mantissa.lean    mantCheck, ofDyadic, CertFixed.toMant

A backend value is opaque to the engine: an `int` mantissa for FixedB, a Fraction for RatB.  A complex number
`CC α` is a pair (re, im); a ball `CertBall α` is ((re, im), r).
"""
from fractions import Fraction as F


def _cdiv(x, d):
    """CertFixed.cdiv: ceiling division -((-x) / d) with Int.ediv (d > 0: floor)."""
    return -((-x) // d)


class FixedB:
    """instCertArithFixed P: a value is the integer mantissa m (denoting m / 2^P)."""

    def __init__(self, P):
        self.P = P
        self.D = 1 << P
        self.zero = 0
        self.name = "CertFixed %d" % P

    def ofInt(self, z):
        return z * self.D

    def ofRatUp(self, q):
        q = F(q)
        return _cdiv(q.numerator * self.D, q.denominator)

    def ofRatDown(self, q):
        q = F(q)
        return (q.numerator * self.D) // q.denominator

    def add(self, a, b):
        return a + b

    def neg(self, a):
        return -a

    def mul(self, a, b):
        return (a * b) >> self.P          # Int.ediv by 2^P = floor

    def abs(self, a):
        return a if a >= 0 else -a

    def addErr(self, a, b):
        return 0

    def mulErr(self, a, b):
        return 1

    def upAdd(self, a, b):
        return a + b

    def upMul(self, a, b):
        return -((-(a * b)) >> self.P)    # cdiv (a*b) 2^P

    def ble(self, a, b):
        return a <= b

    def blt(self, a, b):
        return a < b

    def beq(self, a, b):
        return a == b

    def val(self, a):
        return F(a, self.D)

    # CertFixed.toMant P : ℕ → CertFixed P → Option ℤ
    def toMant(self, P2, a):
        return a if P2 == self.P else None


class RatB:
    """instCertArithRat: exact; addErr = mulErr = 0, upAdd = +, upMul = *."""

    zero = F(0)
    name = "Rat"

    def ofInt(self, z):
        return F(z)

    def ofRatUp(self, q):
        return F(q)

    ofRatDown = ofRatUp

    def add(self, a, b):
        return a + b

    def neg(self, a):
        return -a

    def mul(self, a, b):
        return a * b

    def abs(self, a):
        return abs(a)

    def addErr(self, a, b):
        return F(0)

    mulErr = addErr

    def upAdd(self, a, b):
        return a + b

    def upMul(self, a, b):
        return a * b

    def ble(self, a, b):
        return a <= b

    def blt(self, a, b):
        return a < b

    def beq(self, a, b):
        return a == b

    def val(self, a):
        return a

    def toMant(self, P2, a):
        return None


# ---------------------------------------------------------------------------------------------- Arith/PiHigh
PI_LO = F(3141592, 1000000)       # piLoQ
PI_UP = F(3141593, 1000000)       # piUpQ


def atanS(x, m):
    x = F(x)
    s, p, x2 = F(0), x, x * x
    for i in range(m):
        s += (p / (2 * i + 1)) if i % 2 == 0 else -(p / (2 * i + 1))
        p *= x2
    return s


_PI_CACHE = {}


def piLowRat(k, j):
    key = ("lo", k, j)
    if key not in _PI_CACHE:
        _PI_CACHE[key] = 16 * atanS(F(1, 5), 2 * k) - 4 * atanS(F(1, 239), 2 * j + 1)
    return _PI_CACHE[key]


def piUpRat(k, j):
    key = ("up", k, j)
    if key not in _PI_CACHE:
        _PI_CACHE[key] = 16 * atanS(F(1, 5), 2 * k + 1) - 4 * atanS(F(1, 239), 2 * j)
    return _PI_CACHE[key]


def factorial(n):
    r = 1
    for i in range(2, n + 1):
        r *= i
    return r


def eRem(n):
    return F(n + 1) / (factorial(n) * n)


# ---------------------------------------------------------------------------------------------- PiEnclosure
class PiEnclosure:
    __slots__ = ("centre", "rad", "machinK", "machinJ")

    def __init__(self, centre, rad, k, j):
        self.centre, self.rad, self.machinK, self.machinJ = centre, rad, k, j


def checkPiEnclosure(B, pe):
    return (B.ble(B.upAdd(B.add(pe.centre, B.neg(pe.rad)), B.addErr(pe.centre, B.neg(pe.rad))),
                  B.ofRatDown(piLowRat(pe.machinK, pe.machinJ)))
            and B.ble(B.upAdd(B.ofRatUp(piUpRat(pe.machinK, pe.machinJ)), B.addErr(pe.centre, pe.rad)),
                      B.add(pe.centre, pe.rad)))


# ---------------------------------------------------------------------------------------------- Roots: balls
def normUp(B, c):
    """CC.normUp: upAdd (abs re) (abs im)."""
    return B.upAdd(B.abs(c[0]), B.abs(c[1]))


def ball_ofRat(B, q):
    u, d = B.ofRatUp(q), B.ofRatDown(q)
    return ((u, B.ofInt(0)), B.upAdd(B.add(u, B.neg(d)), B.addErr(u, B.neg(d))))


def oneBall(B):
    return ((B.ofInt(1), B.ofInt(0)), B.ofInt(0))


def ball_plus(B, b1, b2):
    (a, b), r1 = b1
    (c, d), r2 = b2
    return ((B.add(a, c), B.add(b, d)), B.upAdd(B.upAdd(r1, r2), B.upAdd(B.addErr(a, c), B.addErr(b, d))))


def mulReErr(B, a, b, c, d):
    return B.upAdd(B.upAdd(B.addErr(B.mul(a, c), B.neg(B.mul(b, d))), B.mulErr(a, c)), B.mulErr(b, d))


def mulImErr(B, a, b, c, d):
    return B.upAdd(B.upAdd(B.addErr(B.mul(a, d), B.mul(b, c)), B.mulErr(a, d)), B.mulErr(b, c))


def ball_times(B, b1, b2):
    (a, b), r1 = b1
    (c, d), r2 = b2
    centre = (B.add(B.mul(a, c), B.neg(B.mul(b, d))), B.add(B.mul(a, d), B.mul(b, c)))
    rad = B.upAdd(B.upAdd(B.upMul(r1, B.upAdd(normUp(B, (c, d)), r2)), B.upMul(normUp(B, (a, b)), r2)),
                  B.upAdd(mulReErr(B, a, b, c, d), mulImErr(B, a, b, c, d)))
    return (centre, rad)


def expAux(B, zb, m):
    """CertBall.expAux zb m (the recursion unrolled; (t, s) after m steps)."""
    t, s = oneBall(B), oneBall(B)
    for i in range(m):
        t = ball_times(B, ball_times(B, t, zb), ball_ofRat(B, F(1, i + 1)))
        s = ball_plus(B, s, t)
    return t, s


def certCExp(B, z, zRad, N):
    b = expAux(B, (z, zRad), N)[1]
    return b[0], B.upAdd(b[1], B.ofRatUp(eRem(N + 1)))


def certCExpSmall(B, z, zRad):
    return B.ble(B.upAdd(normUp(B, z), zRad), B.ofInt(1))


def certBallSquareIter(B, b, s):
    for _ in range(s):
        b = ball_times(B, b, b)
    return b


def certCExpReduced(B, z, zRad, s, N):
    red = ball_times(B, (z, zRad), ball_ofRat(B, F(1, 2 ** s)))
    if certCExpSmall(B, red[0], red[1]):
        e = certCExp(B, red[0], red[1], N)
        out = certBallSquareIter(B, (e[0], e[1]), s)
        return (out[0], out[1])
    return None


# ---------------------------------------------------------------------------------------------- Mantissa
def mantCheck(B, P, a, z):
    q = F(z, 2 ** P)
    return B.beq(a, B.ofRatUp(q)) and B.beq(a, B.ofRatDown(q))


def ofDyadic(B, P, z):
    a = B.ofRatDown(F(z, 2 ** P))
    return a if mantCheck(B, P, a, z) else None
