#!/usr/bin/env python3
"""V2-SITES-SIGN: exact mirror of `biteOk` (KAM/CertificateSharp/V2/SmallDivQ.lean) and certified site data.

Untrusted tooling.  Transcribes the balanced fibered checker of KAM/Sharp2/Examples/PlasmaLean/Balanced.lean at n = 2,
tau = 1: `expLow`, `cLo`, `tailBound`, `fiberP`, `fiberLb`, `fiberTerm`, `fiberOk`, `balCheck`, `balBound`, and the test
of `biteOk`.  Two evaluations of `balBound`:

* `bal_exact`: exact Fractions by the same bisection as `balSum` (small l only: the rationals grow as in the kernel);
* `bal_up`: an upper bound in integer fixed point, every operation rounded up, usable at every l.  The kernel checks
  `balBound <= B`, so an upper bound is what a witness needs.

`sizes` reports the bit lengths the exact sum reaches, the quantity that drives the kernel's memory.
"""
import math
from fractions import Fraction as F

C0 = 4 + F(99225, 30000)


def floor(x):
    return x.numerator // x.denominator


class Data:
    """`SdsData` with box [(c, r)], at N = 2^l (`biteData box κ γ b w`)."""

    def __init__(self, c, r, gamma, delta, l, J, E1):
        self.c, self.r, self.gamma, self.delta, self.l, self.J, self.E1 = F(c), F(r), F(gamma), F(delta), l, J, F(E1)
        self.N = 2 ** l

    def expLow(self):
        x = F(628, 100) * self.delta
        return sum(x ** i / math.factorial(i) for i in range(self.J + 1))

    def cLo(self):
        return F(628, 100) * self.delta - F(2, self.N + 1)

    def tailBound(self):
        return (2 * (1 + 2) / self.gamma ** 2 * (F(63, 10) * self.delta) * (F(self.N + 1) ** 2 * self.E1 ** (self.N + 1))
                * (1 + 1 / self.cLo()))

    def mode(self, k):
        """(p, L, ok) at the mode k: `fiberP`, `fiberLb`, `fiberOk`."""
        x = k * self.c
        p = floor(-x + F(1, 2))
        rad = abs(k) * self.r
        d = abs(x + p)
        return p, d - rad, d - rad > 0 and d + rad <= F(1, 2)

    def term(self, k):
        p, L, _ = self.mode(k)
        bg = F(0) if p == 0 else 1 / (F(abs(p)) - F(1, 2)) ** 2
        return self.E1 ** (abs(k) + abs(p)) / L ** 2 + self.E1 ** abs(k) * (bg + self.E1 * C0)

    def check(self):
        """`balCheck`."""
        if not (self.gamma > 0 and self.delta > 0 and self.cLo() > 0 and 1 <= self.E1 * self.expLow()):
            return False
        return all(self.mode(j + 1)[2] and self.mode(-(j + 1))[2] for j in range(self.N))

    def bal_exact(self):
        def bal(l, a):
            if l == 0:
                return self.term(a + 1) + self.term(-(a + 1))
            return bal(l - 1, a) + bal(l - 1, a + 2 ** (l - 1))
        return self.E1 * F(99225, 30000) + bal(self.l, 0) + self.tailBound()

    def bal_up(self, prec=200):
        """An upper bound of `balBound`: integers at 2^-prec, every operation rounded up."""
        one = 1 << prec
        up = lambda x: -((-x.numerator << prec) // x.denominator)      # ceil(x 2^prec), x a Fraction
        mul = lambda a, b: -((-a * b) >> prec)
        E = up(self.E1)
        top = 2 * self.N + 3 + int(abs(self.c)) * self.N * 2
        pw = [one]
        for _ in range(top):
            pw.append(mul(pw[-1], E))
        c0 = up(C0)
        tot = 0
        for j in range(self.N):
            for k in (j + 1, -(j + 1)):
                p, L, _ = self.mode(k)
                inv = -((-one * L.denominator ** 2) // L.numerator ** 2)         # ceil(2^prec / L^2)
                bg = 0 if p == 0 else up(1 / (F(abs(p)) - F(1, 2)) ** 2)
                a = abs(k)
                tot += mul(pw[a + abs(p)], inv) + mul(pw[a], bg + mul(E, c0))
        return F(tot + mul(E, up(F(99225, 30000))), 1 << prec) + self.tailBound(), None

    def block_up(self, a, b, prec=200):
        """An upper bound of the fibres a <= j < b of `balSum`, integers at 2^-prec, rounded up."""
        one = 1 << prec
        up = lambda x: -((-x.numerator << prec) // x.denominator)
        mul = lambda u, v: -((-u * v) >> prec)
        E = up(self.E1)
        pw = {0: one}
        cur, top = one, 2 * b + 3 + int(abs(self.c)) * b * 2
        table = [one]
        for _ in range(top):
            cur = mul(cur, E)
            table.append(cur)
        c0 = up(C0)
        tot = 0
        for j in range(a, b):
            for k in (j + 1, -(j + 1)):
                p, L, _ = self.mode(k)
                inv = -((-one * L.denominator ** 2) // L.numerator ** 2)
                bg = 0 if p == 0 else up(1 / (F(abs(p)) - F(1, 2)) ** 2)
                m = abs(k)
                tot += mul(table[m + abs(p)], inv) + mul(table[m], bg + mul(E, c0))
        return F(tot, 1 << prec)

    def sizes(self):
        """Bit lengths of the denominator of the exact finite sum: lcm of the L^2 numerators and of the E1 powers."""
        g = 1
        for j in range(self.N):
            for k in (j + 1, -(j + 1)):
                _, L, _ = self.mode(k)
                n = L.numerator ** 2
                g = g * n // math.gcd(g, n)
        return g.bit_length()


def c_of(B, kappa, gamma, b, sig=4):
    """The shortest c (sig significant digits, rounded up) with `B κ⁻² (γ b)² <= (3.1415 c)²`."""
    x = F(B) / F(kappa) ** 2 * (F(gamma) * F(b)) ** 2
    v = math.sqrt(float(x)) / 3.1415
    e = math.floor(math.log10(v)) - sig + 1
    c = F(math.ceil(v / 10.0 ** e)) * F(10) ** e
    while x > (F(31415, 10000) * c) ** 2:
        c += F(10) ** e
    return c


def bite_ok(data, kappa, gamma, b, c, B, value=None):
    """The test of `biteOk` (data = `biteData box κ γ b w`); value: balBound or an upper bound of it."""
    v = data.bal_up()[0] if value is None else value
    return (c > 0 and b > 0 and data.check() and v <= B and
            F(B) / F(kappa) ** 2 * (F(gamma) * F(b)) ** 2 <= (F(31415, 10000) * c) ** 2)


def up_digits(x, sig):
    """x rounded up to sig significant digits."""
    x = F(x)
    e = math.floor(math.log10(float(x))) - sig + 1
    d = F(10) ** e
    return math.ceil(x / d) * d


def E1_of(delta, J, digits=6):
    """The short E1 with 1 <= E1 expLow: 1/expLow rounded up to `digits` decimals."""
    d = Data(0, 0, 1, delta, 1, J, 1)
    x = 1 / d.expLow()
    D = 10 ** digits
    return F(math.ceil(x * D), D)
