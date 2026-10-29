#!/usr/bin/env python3
"""Exact (Fraction) mirror of the LANDED certified arithmetic used by the SO toy certificates.

Untrusted tooling (SO-TOYGEN).  Each function transcribes the Lean definition of the same name over the exact
backend `ℚ` (`instCertArithRat`: addErr = mulErr = 0, upAdd = +, upMul = *, ofRatUp = ofRatDown = id):

  Arith/Transcendental.lean  ratExpUp
  Arith/PiHigh.lean          piLoQ, piUpQ, atanS, piLowRat, piUpRat, eRem
  Arith/PiEnclosure.lean     checkPiEnclosure
  Arith/Roots.lean           checkRootEnclosure, CC.normUp, CertBall.{ofRat, plus, times, expAux}, certCExp,
                             certCExpSmall
  Arith/ComplexExp.lean      certBallSquareIter, certCExpReduced
  Model/Basic.lean           checkWeight, degFactorUp
  Expr/Ball.lean             cexpHalvings, ballPiLo, ballPiHi, constBall, ballStep, Slp.balls
  Freq.lean                  checkAlgBox (algTermLo/Hi, algRowLo/Hi)

A complex number is a pair (re, im) of Fractions; a ball is ((re, im), r).
"""
from fractions import Fraction as F
from math import factorial, ceil

PI_LO = F(3141592, 1000000)
PI_UP = F(3141593, 1000000)


# ---------------------------------------------------------------- real transcendental bounds
def ratExpUp(q, s, N):
    q = F(q)
    if q / F(2) ** s <= 1 and 0 < N:
        x = q / F(2) ** s
        r = sum((x ** m / factorial(m) for m in range(N)), F(0)) + x ** N * (F(N + 1) / (factorial(N) * N))
        for _ in range(s):
            r = r * r
        return r
    return F(3) ** ceil(q)


def checkWeight(rho, w, s, N):
    return F(rho) > 0 and ratExpUp(2 * PI_UP * F(rho), s, N) <= F(w)


def degFactorUp(d):
    return (2 * PI_UP) ** d if d >= 0 else (2 * PI_LO) ** d


def atanS(x, m):
    x = F(x)
    return sum(((-1) ** i * (x ** (2 * i + 1) / (2 * i + 1)) for i in range(m)), F(0))


def piLowRat(k, j):
    return 16 * atanS(F(1, 5), 2 * k) - 4 * atanS(F(1, 239), 2 * j + 1)


def piUpRat(k, j):
    return 16 * atanS(F(1, 5), 2 * k + 1) - 4 * atanS(F(1, 239), 2 * j)


def eRem(n):
    return F(n + 1) / (factorial(n) * n)


def checkPiEnclosure(centre, rad, k, j):
    """ℚ backend: centre - rad <= piLowRat k j and piUpRat k j <= centre + rad."""
    return F(centre) - F(rad) <= piLowRat(k, j) and piUpRat(k, j) <= F(centre) + F(rad)


def checkRootEnclosure(m, d, lo, hi):
    lo, hi = F(lo), F(hi)
    return 0 <= lo and lo ** m <= d and d <= hi ** m and 0 <= hi


def algRowLo(a_s, lo, hi):
    return sum(((a * lo ** j) if a >= 0 else (a * hi ** j) for j, a in enumerate(a_s)), F(0))


def algRowHi(a_s, lo, hi):
    return sum(((a * hi ** j) if a >= 0 else (a * lo ** j) for j, a in enumerate(a_s)), F(0))


def checkAlgBox(n, coeffs, lo, hi, box):
    lo, hi = F(lo), F(hi)
    if len(box) != n or not 0 <= lo:
        return False
    for i in range(n):
        c, r = box[i] if i < len(box) else (F(0), F(0))
        row = [F(a) for a in (coeffs[i] if i < len(coeffs) else [])]
        if not (c - r <= algRowLo(row, lo, hi) and algRowHi(row, lo, hi) <= c + r):
            return False
    return True


# ---------------------------------------------------------------- complex balls over ℚ
def normUp(c):
    return abs(c[0]) + abs(c[1])


def b_ofRat(q):
    return ((F(q), F(0)), F(0))


def b_one():
    return ((F(1), F(0)), F(0))


def b_plus(b1, b2):
    return ((b1[0][0] + b2[0][0], b1[0][1] + b2[0][1]), b1[1] + b2[1])


def b_times(b1, b2):
    (a, b), r1 = b1
    (c, d), r2 = b2
    return ((a * c - b * d, a * d + b * c), r1 * (normUp((c, d)) + r2) + normUp((a, b)) * r2)


def expAux(zb, m):
    t, s = b_one(), b_one()
    for i in range(m):
        t = b_times(b_times(t, zb), b_ofRat(F(1, i + 1)))
        s = b_plus(s, t)
    return t, s


def certCExp(z, zRad, N):
    b = expAux((z, zRad), N)[1]
    return b[0], b[1] + eRem(N + 1)


def certCExpSmall(z, zRad):
    return normUp(z) + zRad <= 1


def certCExpReduced(z, zRad, s, N):
    red = b_times((z, F(zRad)), b_ofRat(F(1, 2 ** s)))
    if not certCExpSmall(red[0], red[1]):
        return None
    e = certCExp(red[0], red[1], N)
    out = (e[0], e[1])
    for _ in range(s):
        out = b_times(out, out)
    return out


def ceil_nat(q):
    q = F(q)
    return max(0, -((-q.numerator) // q.denominator))


def cexpHalvings(z, r):
    return ceil_nat(2 * (abs(z[0]) + abs(z[1]) + F(r))).bit_length() - 1 + 1 if ceil_nat(
        2 * (abs(z[0]) + abs(z[1]) + F(r))) > 0 else 1   # Nat.log2 0 = 0


# ---------------------------------------------------------------- Slp.balls (Expr/Ball.lean)
def ballPiLo(d):
    return (2 * PI_LO) ** d if d >= 0 else (2 * PI_UP) ** d


def ballPiHi(d):
    return (2 * PI_UP) ** d if d >= 0 else (2 * PI_LO) ** d


def constBall(re, im, deg):
    return b_times(((F(re), F(im)), F(0)), (((ballPiLo(deg) + ballPiHi(deg)) / 2, F(0)),
                                           (ballPiHi(deg) - ballPiLo(deg)) / 2))


BALL_ZERO = ((F(0), F(0)), F(0))


def ballStep(n, wH, centre, radius, taylorN, acc, op):
    g = lambda a: acc[a] if a < len(acc) else BALL_ZERO
    tag = op[0]
    if tag == "C":
        return constBall(F(op[1]), F(op[2]), int(op[3]))
    if tag == "A":
        j = op[1]
        if j < n:
            return ((F(centre[j]) if j < len(centre) else F(0), F(0)), F(radius[j]) if j < len(radius) else F(0))
        return BALL_ZERO
    if tag == "X":
        return ((F(0), F(0)), F(wH) ** sum(abs(x) for x in op[1]))
    if tag == "+":
        return b_plus(g(op[1]), g(op[2]))
    if tag == "*":
        return b_times(g(op[1]), g(op[2]))
    if tag == "E":
        c, r = g(op[1])
        return certCExpReduced(c, r, cexpHalvings(c, r), taylorN)
    if tag == "I":
        (re, im), r = g(op[1])
        m = max(abs(re), abs(im))
        if r < m:
            den = re ** 2 + im ** 2
            return ((re / den, -im / den), r / ((m - r) * m))
        return None
    raise ValueError(op)


def slp_balls(n, ops, wH, centre, radius, taylorN):
    acc = []
    for op in ops:
        b = ballStep(n, wH, centre, radius, taylorN, acc, op)
        if b is None:
            return None
        acc.append(b)
    return acc


def parse_ops(ops):
    """Normalize the JSON ops of toy_lean_extract.py (rationals as strings)."""
    out = []
    for op in ops:
        if op[0] == "C":
            out.append(("C", F(op[1]), F(op[2]), int(op[3])))
        elif op[0] == "X":
            out.append(("X", tuple(int(x) for x in op[1])))
        else:
            out.append(tuple([op[0]] + [int(x) for x in op[1:]]))
    return out
