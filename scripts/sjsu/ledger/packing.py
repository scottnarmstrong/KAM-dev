"""Packed integer arithmetic mirroring the N7 kernel checker (KAM/EffectiveStability/Tube/Engine).

Every function here reproduces a Lean definition bit-exactly:
  layout          Layout.key C S i = (i % S - C, i / S - C), Layout.len C S = 2CS + 2C + 1
  compact         a literal: (2C+1)^2 offset digits of b bits, row-major over the box (digit = m + 2^(b-1))
  litZ            the packed value: slot c + S r holds digit(c + K r) - 2^(b-1)
  whitening       unwhiten s 288 n L = L xor (natRamp 288 n * wmul s)
  l1P / l1Ok      the packed l1 norm and its guard (loadOk, l + 2 <= w, N 2^l < 2^w)
"""
from __future__ import annotations

from fractions import Fraction

CH = 288  # literal chunk bits


def K_of(C):
    return 2 * C + 1


def lay_len(C, S):
    return 2 * C * S + 2 * C + 1


def clog2(n):
    """least L with n <= 2^L"""
    L = 0
    while (1 << L) < n:
        L += 1
    return L


def wmul(s):
    return ((s * 11400714819323198485 + 15119558931263122691) % 2 ** 64) | 1


def wkey(s, n):
    ramp = 0
    for i in range(n):
        ramp |= (i + 1) << (CH * i)
    return ramp * wmul(s)


def nchunks(x):
    n = 0
    while x >> (CH * n):
        n += 1
    return max(n, 1)


class Lit:
    """A compact literal model: half-width C, parity par (False = even), scale q (Fraction),
    mantissas m[(c, r)] for the box (c, r in [0, 2C]), i.e. mode (c - C, r - C)."""

    def __init__(self, C, par, q, mant, b, salt):
        self.C, self.par, self.q, self.b, self.salt = C, par, Fraction(q), b, salt
        K = K_of(C)
        self.mant = mant  # dict (c, r) -> int, missing = 0
        X = 0
        off = 1 << (b - 1)
        for r in range(K):
            for c in range(K):
                m = mant.get((c, r), 0)
                assert -off <= m < off, ('mantissa out of range', m, b)
                X |= (m + off) << (b * (c + K * r))
        self.X = X
        self.nch = nchunks(X)
        self.lit = X ^ wkey(salt, self.nch)
        self.L1 = clog2(K * K)
        self.L2 = clog2(K)

    def Z(self, S, w):
        """litZ: the packed value at stride S, slot width w."""
        K = K_of(self.C)
        z = 0
        for (c, r), m in self.mant.items():
            if m:
                z += m << (w * (c + S * r))
        return z

    def slots(self, S):
        """dict slot index -> value on the layout (C, S)"""
        return {c + S * r: m for (c, r), m in self.mant.items() if m}

    def l1(self):
        return sum(abs(m) for m in self.mant.values())

    def c0(self):
        return self.mant.get((self.C, self.C), 0)

    def sym_ok(self):
        """symDigOk: reversal of the box is k -> -k; even: m(-k) = m(k), odd: m(-k) = -m(k)."""
        K = K_of(self.C)
        sg = -1 if self.par else 1
        for (c, r), m in self.mant.items():
            if self.mant.get((K - 1 - c, K - 1 - r), 0) != sg * m:
                return False
        if self.par and self.mant.get((self.C, self.C), 0) != 0:
            return False
        return True


def slots_of_packed(Z, w, N):
    """the N signed slots of a packed integer (balanced digits), for producer-side checks"""
    out = []
    half = 1 << (w - 1)
    mask = (1 << w) - 1
    y = Z + sum(half << (w * i) for i in range(N))  # offset form
    assert y >= 0
    for i in range(N):
        out.append(((y >> (w * i)) & mask) - half)
    assert y >> (w * N) == 0
    return out


def l1_guard(slots, w):
    """(l, l1) for the packed l1 at the least load level l with all slots in [-2^l, 2^l)"""
    mx = 0
    tot = 0
    for v in slots:
        tot += abs(v)
        mx = max(mx, v if v >= 0 else -v - 1)
    l = mx.bit_length()  # v < 2^l and -v <= 2^l
    while not all(-(1 << l) <= v < (1 << l) for v in (max(slots, default=0), min(slots, default=0))):
        l += 1
    N = len(slots)
    assert l + 2 <= w and N * (1 << l) < (1 << w), ('l1 guard fails', l, w, N)
    return l, tot


def psgn(p):
    return -1 if p else 1


def up(x: Fraction, bits=64):
    """a dyadic upper bound of a nonnegative rational with about `bits` significant bits"""
    x = Fraction(x)
    if x <= 0:
        return Fraction(0)
    e = x.numerator.bit_length() - x.denominator.bit_length() - bits
    if e >= 0:
        n = -(-x.numerator // (x.denominator << e))
        return Fraction(n << e)
    n = -(-(x.numerator << -e) // x.denominator)
    return Fraction(n, 1 << -e)
