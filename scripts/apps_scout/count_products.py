#!/usr/bin/env python3
"""Full-precision model x model products of the invariance and energy checks, by tracing each H of models.py.

Rules mirror SO-ADVCOUNT (scripts/spin_orbit/adv_jet.py), at the level of the first-order jet of H composed with K:
  scalar x model            free
  action / linear combos    free
  mode cos, sin of an angle combination k.q:   a shift of the character witness of the normalized direction of k; the witness costs 2 products (its two defects) once per direction;
                            an angle with q_i = theta_i exactly (no u_i) is exact and costs nothing
  cos, sin of a nonlinear model phase: an exp witness, 2 products once per phase; the chain rule adds one product per nonzero derivative
  model x model             1 product, memoized (an SLP reuses slots)
  1/b, model b              1 product (reciprocal witness), memoized
  sqrt b                    1 product (witness s^2 = b)
Each complex product counts once: parity leaves one nonzero real product (SO-ADVCOUNT lever 2).
Check: the lunar client must give 3.
"""
import math
from fractions import Fraction

import models as md
from kamlib import Jet


class Ctx:
    def __init__(self, trivial=()):
        self.n, self.memo, self.trivial = 0, {}, set(trivial)
        self.ids = 0
        self.log = {}

    def count(self, key, weight=1, tag="mul"):
        if key not in self.memo:
            self.memo[key] = True
            self.n += weight
            self.log[tag] = self.log.get(tag, 0) + weight


class T(Jet):
    """value with first-order derivatives; kind 'C' constant or 'M' model."""

    def __init__(self, ctx, kind, d=None, phase=None, name=None):
        self.ctx, self.kind, self.d, self.phase = ctx, kind, d, phase
        ctx.ids += 1
        self.id = name if name is not None else ctx.ids

    # ---- helpers
    def _c(self, x):
        return x if isinstance(x, T) else T(self.ctx, "C")

    def __add__(self, o):
        o_t = self._c(o)
        ph = None
        if self.phase is not None and o_t.phase is not None:
            ph = {k: self.phase.get(k, 0) + o_t.phase.get(k, 0) for k in set(self.phase) | set(o_t.phase)}
        elif self.phase is not None and o_t.kind == "C":
            ph = dict(self.phase)
        elif o_t.phase is not None and self.kind == "C":
            ph = dict(o_t.phase)
        d = None
        if self.d is not None or o_t.d is not None:
            a = self.d or [None] * 4
            b = o_t.d or [None] * 4
            d = [(x if y is None else (y if x is None else _lin(x, y))) for x, y in zip(a, b)]
        r = T(self.ctx, "M" if "M" in (self.kind, o_t.kind) else "C", d, ph)
        return r
    __radd__ = __add__

    def __neg__(self):
        return self * (-1.0)

    def __sub__(self, o):
        return self + (self._c(o) * (-1.0) if isinstance(o, T) else o)

    def __rsub__(self, o):
        return (self * (-1.0)) + o

    def __mul__(self, o):
        if not isinstance(o, T):
            return self._scale(o)
        if self.kind == "C":
            return o._scale(1.0)
        if o.kind == "C":
            return self._scale(1.0)
        self.ctx.count(("mul", min(str(self.id), str(o.id)), max(str(self.id), str(o.id))))
        d = None
        if self.d is not None or o.d is not None:
            a = self.d or [None] * 4
            b = o.d or [None] * 4
            d = []
            for x, y in zip(a, b):
                t1 = None if x is None else _m(x, o)
                t2 = None if y is None else _m(self, y)
                d.append(t1 if t2 is None else (t2 if t1 is None else _lin(t1, t2)))
        return T(self.ctx, "M", d)
    __rmul__ = __mul__

    def _scale(self, c):
        ph = None if self.phase is None else {k: v * c for k, v in self.phase.items()}
        d = None if self.d is None else [None if x is None else x._scale(c) for x in self.d]
        r = T(self.ctx, self.kind, d, ph, name=self.id if self.d is None and self.phase is None else None)
        return r

    def inv(self):
        if self.kind == "C":
            return self
        self.ctx.count(("inv", self.id), tag="inv")
        R = T(self.ctx, "M", None, name=("inv", self.id))
        d = None
        if self.d is not None:
            R2 = _m(R, R)
            d = [None if x is None else _m(R2, x) for x in self.d]
        return T(self.ctx, "M", d, name=("invd", self.id))

    def __truediv__(self, o):
        return self * o.inv() if isinstance(o, T) else self._scale(1.0 / o)

    def __rtruediv__(self, o):
        return self.inv()

    def __pow__(self, m):
        r = self
        for _ in range(m - 1):
            r = r * self
        return r

    def sqrt(self):
        if self.kind == "C":
            return self
        self.ctx.count(("sqrt", self.id), tag="sqrt")
        s = T(self.ctx, "M", None, name=("sqrt", self.id))
        d = None
        if self.d is not None:
            self.ctx.count(("inv", s.id), tag="inv")
            R = T(self.ctx, "M", None, name=("inv", s.id))
            d = [None if x is None else _m(R, x) for x in self.d]
        return T(self.ctx, "M", d, name=("sqrtd", self.id))

    def _trig(self, tag):
        if self.kind == "C":
            return self
        if self.phase is not None:
            k = {i: Fraction(v / (2 * math.pi)).limit_denominator(1000) for i, v in self.phase.items() if i not in self.ctx.trivial and abs(v) > 1e-12}
            if k:
                g = 0
                den = 1
                for v in k.values():
                    den = den * v.denominator // math.gcd(den, v.denominator)
                ints = {i: int(v * den) for i, v in k.items()}
                for v in ints.values():
                    g = math.gcd(g, abs(v))
                key = tuple(sorted((i, v // g) for i, v in ints.items()))
                if key[0][1] < 0:
                    key = tuple((i, -v) for i, v in key)
                self.ctx.count(("char", key), 2, tag="witness")
            nm = ("char", tuple(sorted((i, round(v, 6)) for i, v in self.phase.items())))
            c = T(self.ctx, "M", None, name=nm)
            d = [None] * 4
            for i, v in self.phase.items():
                if abs(v) > 1e-12:
                    d[i] = c
            return T(self.ctx, "M", d)
        self.ctx.count(("exp", self.id), 2, tag="witness")
        e = T(self.ctx, "M", None, name=("exp", self.id))
        d = None
        if self.d is not None:
            d = [None if x is None else _m(e, x) for x in self.d]
        return T(self.ctx, "M", d, name=("expd", self.id, tag))

    def sin(self):
        return self._trig("sin")

    def cos(self):
        return self._trig("cos")


def _m(a, b):
    if a.kind == "C":
        return b
    if b.kind == "C":
        return a
    a.ctx.count(("mul", min(str(a.id), str(b.id)), max(str(a.id), str(b.id))))
    return T(a.ctx, "M", None)


def _lin(a, b):
    return T(a.ctx, "M" if "M" in (a.kind, b.kind) else "C", None)


def trace(H, trivial=()):
    """H of the four coordinates (q1, q2, p1, p2); the q are angles (phase 1), the p are data components."""
    ctx = Ctx(trivial)
    def coord(i):
        d = [None] * 4
        d[i] = T(ctx, "C")
        return T(ctx, "M", d, {i: 1.0} if i < 2 else None, name=("x", i))
    z = [coord(i) for i in range(4)]
    v = H(z)
    return ctx.n, ctx.log


def main():
    import pipeline as pl
    rows = {}
    e = 0.0549
    A = md.moon_A(e)
    rows["Moon rotational (check: 3)"] = trace(md.spin_rot(3.45e-4, A), trivial=(1,))
    rows["Moon librational polar"] = trace(md.spin_librational(3.45e-4, A, 1.0, a=2.47), trivial=(1,))
    Am = {m: v for m, v in md.hansen_A(0.2056, 16).items() if abs(v) > 1e-14}
    rows["Mercury rotational"] = trace(md.spin_rot(1.5e-4, Am, 1.5), trivial=(1,))
    rows["Moon exact Kepler (w chart)"] = trace(md.spin_kepler(3.45e-4, 0.0549), trivial=(1,))
    rows["CC07 Victoria (Delaunay)"] = trace(md.cc07(1e-3))
    rows["PCR3BP exact polar"] = trace(md.pcr3bp_polar(9.5e-4, 0.45, 0.55))
    rows["Trojan shear chart"] = trace(md.trojan_shear(9.5e-4, 1.0, 6.0))
    rows["Hill polar"] = trace(md.hill_polar(0.0748, 1.0, 1.0))
    rows["Henon-Heiles polar"] = trace(md.henon_heiles_polar(0.4, 0.7))
    for k, v in rows.items():
        print("%-32s %3d  %s" % (k, v[0], v[1]))
    pl.save("products.json", rows)


if __name__ == "__main__":
    main()
