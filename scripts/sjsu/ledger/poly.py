"""Exact trigonometric polynomials on square boxes (Python side of the N7 ledger).

A Poly has half-width C, parity par (False = cosine/even, True = minus-sine/odd) and integer slots
s[(c, r)] (box coordinates c, r in [0, 2C], mode (c - C, r - C)); its value is
q * sum_k s_k trig_par(k . phi) for a rational scale q kept outside.  Products are exact (Kronecker
packing into Python big integers, unpacked through bytes), with the kernel's sign convention:
evalK a * evalK b = psgn(pa and pb) evalK(conv a b), parity pa xor pb.
"""
from __future__ import annotations

WPY = 512  # Python-side slot width (bits, multiple of 8): large enough for every exact product here


class Poly:
    __slots__ = ('C', 'par', 's')

    def __init__(self, C, par, s):
        self.C, self.par, self.s = C, par, {k: v for k, v in s.items() if v}

    def l1(self):
        return sum(abs(v) for v in self.s.values())

    def maxabs(self):
        return max((abs(v) for v in self.s.values()), default=0)

    def embed(self, C2):
        d = C2 - self.C
        return Poly(C2, self.par, {(c + d, r + d): v for (c, r), v in self.s.items()})

    def scale_int(self, m):
        return Poly(self.C, self.par, {k: m * v for k, v in self.s.items()})

    def add(self, other):
        assert self.C == other.C and self.par == other.par
        s = dict(self.s)
        for k, v in other.s.items():
            s[k] = s.get(k, 0) + v
        return Poly(self.C, self.par, s)

    def trunc_round(self, C2, keep, a):
        """the output literal mantissas: modes in the box C2 kept by keep(k1, k2), slot / 2^a rounded
        to nearest, ties away from zero (symmetric)."""
        d = self.C - C2
        out = {}
        half = 1 << (a - 1) if a > 0 else 0
        for (c, r), v in self.s.items():
            cc, rr = c - d, r - d
            if 0 <= cc <= 2 * C2 and 0 <= rr <= 2 * C2 and keep(cc - C2, rr - C2):
                if a == 0:
                    m = v
                elif v >= 0:
                    m = (v + half) >> a
                else:
                    m = -((-v + half) >> a)
                if m:
                    out[(cc, rr)] = m
        return Poly(C2, self.par, out)


def _pack(p: Poly, S):
    """sum_i v_i 2^(WPY i) through a byte array (offset digits, then the offset removed)"""
    if not p.s:
        return 0
    nb = WPY // 8
    n = max(c + S * r for (c, r) in p.s) + 1
    off = 1 << (WPY - 2)
    by = bytearray(n * nb)
    for (c, r), v in p.s.items():
        i = c + S * r
        by[i * nb:(i + 1) * nb] = (v + off).to_bytes(nb, 'little')
    z = int.from_bytes(by, 'little')
    # subtract the offset on the written slots only
    ob = bytearray(n * nb)
    ofs = off.to_bytes(nb, 'little')
    for (c, r) in p.s:
        i = c + S * r
        ob[i * nb:(i + 1) * nb] = ofs
    return z - int.from_bytes(ob, 'little')


def _unpack(z, n, C, S):
    """slots of a packed product of n positions (box half-width C, stride S)"""
    off = 1 << (WPY - 1)
    nb = WPY // 8
    offs = int.from_bytes(off.to_bytes(nb, 'little') * n, 'little')
    zz = z + offs
    by = zz.to_bytes(n * nb, 'little')
    out = {}
    K = 2 * C + 1
    for i in range(n):
        v = int.from_bytes(by[i * nb:(i + 1) * nb], 'little') - off
        if v:
            c, r = i % S, i // S
            assert c < K and r < K, 'wrap'
            out[(c, r)] = v
    return out


def _flat(p: Poly, S):
    n = max((c + S * r for (c, r) in p.s), default=-1) + 1
    v = [0] * n
    for (c, r), x in p.s.items():
        v[c + S * r] = x
    return v


def mul(a: Poly, b: Poly) -> Poly:
    """exact product with the kernel sign: psgn(pa and pb) * conv (flint fmpz_poly, FFT)"""
    from flint import fmpz_poly
    C = a.C + b.C
    S = 2 * C + 1
    if not a.s or not b.s:
        return Poly(C, a.par != b.par, {})
    pr = fmpz_poly(_flat(a, S)) * fmpz_poly(_flat(b, S))
    sg = -1 if (a.par and b.par) else 1
    out = {}
    K = 2 * C + 1
    for i, x in enumerate(pr.coeffs()):
        if x:
            c, r = i % S, i // S
            assert c < K and r < K, 'wrap'
            out[(c, r)] = sg * int(x)
    return Poly(C, a.par != b.par, out)


def conv_raw(a: Poly, b: Poly) -> Poly:
    """the raw convolution (no sign), as the kernel's listConv"""
    C = a.C + b.C
    S = 2 * C + 1
    n = 2 * C * S + 2 * C + 1
    return Poly(C, a.par != b.par, _unpack(_pack(a, S) * _pack(b, S), n, C, S))


def hexn(k1, k2):
    return abs(k1) + abs(k2) + abs(k1 + k2)
