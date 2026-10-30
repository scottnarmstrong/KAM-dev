#!/usr/bin/env python3
"""SJS-PLAN: operation counts of the checker's straight-line program for planar SJS (replaces SJS-FEAS's hand estimate).

Untrusted design tooling.  The reduced Hamiltonian in the synodic regular chart (sjs_chart.H_syn), written with regular Kepler
variables (eccentric longitude F, k + i h = eps conj(z); no polar coordinates), or in Delaunay's chart, is evaluated on a symbolic
ring with hash-consing, so common subexpressions count once.  Derivatives are nested dual numbers (forward mode, as the landed jet
compiler; sparse: a zero partial costs nothing).
Counted over the real-coefficient ring (reversible case: every model is purely even or odd, so a model product is one real product):
  mul   genuine model x model products,
  scal  scalar x model, add   model +/- model,
  wit   witnesses: inv and sqrt (one checking product each), char exp(i f) (3 derivative residuals of 2 real products, n = 3),
        Kepler (2 products for the residual).  Witness series are certificate data.
Usage: python3 -I scripts/sjs/plan/sjs_ops.py [--json OUT]
"""
import json, sys


class Ring:
    def __init__(self):
        self.c = dict(mul=0, scal=0, add=0, inv=0, sqrt=0, char=0, kep=0)
        self.cache = {}
        self.n = 0

    def new(self):
        self.n += 1
        return Node(self, self.n)

    def op(self, kind, a, b=None):
        key = (kind, a.id, None if b is None else b.id) if kind in ("add", "sub", "sqrt", "inv", "neg") else (kind, min(a.id, b.id), max(a.id, b.id))
        if key not in self.cache:
            self.cache[key] = self.new()
            k = {"sub": "add", "neg": None}.get(kind, kind)
            if k:
                self.c[k] += 1
            if kind in ("inv", "sqrt"):
                self.c["mul"] += 1            # the witness check w x = 1, s^2 = x
        return self.cache[key]


class Node:
    __slots__ = ("r", "id", "const")

    def __init__(self, r, i, const=None):
        self.r, self.id, self.const = r, i, const

    def lift(self, o):
        return o if isinstance(o, Node) else Node(self.r, -abs(hash(float(o))) - 1, float(o))

    def __add__(self, o):
        o = self.lift(o)
        if self.const is not None and o.const is not None:
            return self.lift(self.const + o.const)
        if self.const == 0.0:
            return o
        if o.const == 0.0:
            return self
        if self.const is not None or o.const is not None:   # constant shift: no model op worth counting (one coefficient)
            return self.r.op("add", *(sorted((self, o), key=lambda x: x.id)))
        return self.r.op("add", *(sorted((self, o), key=lambda x: x.id)))
    __radd__ = __add__

    def __neg__(self):
        return self if self.const == 0.0 else (self.lift(-self.const) if self.const is not None else self.r.op("neg", self))

    def __sub__(self, o):
        return self + (-self.lift(o))

    def __rsub__(self, o):
        return (-self) + o

    def __mul__(self, o):
        o = self.lift(o)
        if self.const is not None and o.const is not None:
            return self.lift(self.const * o.const)
        if self.const == 0.0 or o.const == 0.0:
            return self.lift(0.0)
        if self.const == 1.0:
            return o
        if o.const == 1.0:
            return self
        if self.const == -1.0:
            return -o
        if o.const == -1.0:
            return -self
        if self.const is not None or o.const is not None:
            return self.r.op("scal", self, o)
        return self.r.op("mul", self, o)
    __rmul__ = __mul__

    def inv(self):
        return self.lift(1.0 / self.const) if self.const is not None else self.r.op("inv", self)

    def sqrt(self):
        return self.lift(self.const ** 0.5) if self.const is not None else self.r.op("sqrt", self)


class Dual:
    """v + sum d[i] e_i, e_i e_j = 0; v and d[i] in any ring (nesting gives order 2)."""
    __slots__ = ("v", "d")

    def __init__(self, v, d=None):
        self.v, self.d = v, d or {}

    def lift(self, o):
        return o if isinstance(o, Dual) else Dual(o)

    def __add__(self, o):
        o = self.lift(o)
        d = dict(self.d)
        for k, x in o.d.items():
            d[k] = d[k] + x if k in d else x
        return Dual(self.v + o.v, d)
    __radd__ = __add__

    def __neg__(self):
        return Dual(-self.v, {k: -x for k, x in self.d.items()})

    def __sub__(self, o):
        return self + (-self.lift(o))

    def __rsub__(self, o):
        return (-self) + o

    def __mul__(self, o):
        o = self.lift(o)
        d = {}
        for k, x in self.d.items():
            d[k] = x * o.v
        for k, x in o.d.items():
            t = self.v * x
            d[k] = d[k] + t if k in d else t
        return Dual(self.v * o.v, d)
    __rmul__ = __mul__

    def inv(self):
        w = self.v.inv()
        m = -(w * w)
        return Dual(w, {k: m * x for k, x in self.d.items()})

    def sqrt(self):
        s = self.v.sqrt()
        h = (s * 2.0).inv()
        return Dual(s, {k: h * x for k, x in self.d.items()})

    def char(self):
        """(cos f, sin f)"""
        c, s = char(self.v)
        return Dual(c, {k: -(s * x) for k, x in self.d.items()}), Dual(s, {k: c * x for k, x in self.d.items()})


def char(a):
    if isinstance(a, Dual):
        return a.char()
    key = ("char", a.id)
    if key not in a.r.cache:
        a.r.cache[key] = (a.r.new(), a.r.new())
        a.r.c["char"] += 1
        a.r.c["mul"] += 6                     # 3 derivative residuals, each c' = -f' s, s' = f' c
    return a.r.cache[key]


def kepler(lam, k, h):
    """returns (cF, sF, w = 1/(1 - k cF - h sF)) as duals of any nesting; order = nesting depth."""
    if isinstance(lam, Dual):
        cF0, sF0, w0 = kepler(lam.v, k.v, h.v)
        d = {}
        keys = set(lam.d) | set(k.d) | set(h.d)
        for q in keys:
            dl, dk, dh = lam.d.get(q), k.d.get(q), h.d.get(q)
            t = None
            for x in (dl, None if dk is None else dk * sF0, None if dh is None else -(dh * cF0)):
                if x is not None:
                    t = x if t is None else t + x
            d[q] = w0 * t
        cF = Dual(cF0, {q: -(sF0 * x) for q, x in d.items()})
        sF = Dual(sF0, {q: cF0 * x for q, x in d.items()})
        den = (1.0 - (k * cF + h * sF))
        w = Dual(w0, {q: -(w0 * w0) * x for q, x in den.d.items()})
        return cF, sF, w
    r = lam.r
    key = ("kep", lam.id, k.id, h.id)
    if key not in r.cache:
        F = r.new()
        cF, sF = char(F)
        r.c["kep"] += 1
        r.c["mul"] += 2                       # residual F - k s + h c - lam
        den = 1.0 - (k * cF + h * sF)
        r.cache[key] = (cF, sF, den.inv())
    return r.cache[key]


def H_syn(z, m=(0.9546, 0.2856), C=3.058, mu=1e-3, phi=-1.09):
    b1, b2, b3, La1, I5, I6 = z
    a1, a2, a3 = b1 + b2, b2, b3 - b2
    La2 = C + I5 + I6 - La1
    r5, r6 = (I5 * 2.0).sqrt(), (I6 * 2.0).sqrt()
    c3, s3 = char(a3)
    w6r, w6i = r6 * c3, r6 * s3
    co, si = 0.46, -0.89
    z1r, z1i = r5 * co - w6r * si, -(w6i * si)
    z2r, z2i = r5 * si + w6r * co, w6i * co
    out = []
    for lam, La, zr, zi, mm in ((a1, La1, z1r, z1i, m[0]), (a2, La2, z2r, z2i, m[1])):
        P = (zr * zr + zi * zi) * 0.5
        iLa = La.inv()
        rP = P * iLa                          # P / Lambda
        eps = ((1.0 - rP * 0.5) * iLa).sqrt()
        k, h = eps * zr, -(eps * zi)
        cF, sF, w = kepler(lam, k, h)
        beta = (2.0 - rP).inv()
        hk = beta * (h * k)
        a = La * La * (1.0 / mm ** 2)
        X = a * ((1.0 - beta * (h * h)) * cF + hk * sF - k)
        Y = a * ((1.0 - beta * (k * k)) * sF + hk * cF - h)
        b = iLa * (mm ** 2)
        eta = 1.0 - rP                        # sqrt(1 - e^2)
        ww = b * w
        Px = ww * (hk * cF - (1.0 - beta * (h * h)) * sF)
        Py = ww * ((1.0 - beta * (k * k)) * cF - hk * sF)
        out.append((X, Y, Px, Py, iLa))
    (x1, y1, p1, q1, il1), (x2, y2, p2, q2, il2) = out
    d0, d1 = x1 - x2, y1 - y2
    r2 = d0 * d0 + d1 * d1
    ir = r2.sqrt().inv()
    s0, s1 = p1 + p2, q1 + q2
    H1 = (s0 * s0 + s1 * s1) * 0.5 - ir * (m[0] * m[1])
    return il1 * il1 * (-0.5 * m[0] ** 3) + il2 * il2 * (-0.5 * m[1] ** 3) + H1 * mu


def run(order):
    r = Ring()
    leaves = [r.new() for _ in range(6)]
    if order == 0:
        z = leaves
    elif order == 1:
        z = [Dual(leaves[i], {i: Node(r, 0, 1.0)}) for i in range(6)]
    else:
        # nested duals: outer derivative d/dz_i of the inner gradient, the Hessian in sparse form
        z = []
        for i in range(6):
            inner = Dual(leaves[i], {i: Node(r, 0, 1.0)})
            z.append(Dual(inner, {i: Dual(Node(r, 0, 1.0))}))
    H = H_syn(z)
    if order == 1:
        return dict(r.c, partials=len(H.d))
    return dict(r.c)


def main():
    out = {}
    print("| derivatives of H (chart: synodic regular) | model x model products | scalar x model | adds | inv | sqrt | char | Kepler |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|")
    for o, name in ((0, "H only"), (1, "gradient, X_h(K): invariance + energy"), (2, "Hessian, DX_h(K): torsion stage")):
        c = run(o)
        out[name] = c
        print("| %s | %d | %d | %d | %d | %d | %d | %d |" % (name, c["mul"], c["scal"], c["add"], c["inv"], c["sqrt"], c["char"], c["kep"]))
    c = out["H only"]
    gen = c["mul"] - c["inv"] - c["sqrt"] - 6 * c["char"] - 2 * c["kep"]          # value products without the witness checks
    rev = c["mul"] + 2 * gen + 2 * c["inv"] + 2 * c["sqrt"] + 2 * c["char"] + 4 * c["kep"]
    print("\nreverse mode (adjoint sweep over the same program; a generated program, needing its own soundness theorem): %d products "
          "for the gradient\n  = value %d (of which %d witness checks) + adjoints: 2 per value product, 2 per inv/sqrt/char, 4 per Kepler." % (
              rev, c["mul"], c["mul"] - gen))
    out["reverse_gradient_products"] = rev
    if "--json" in sys.argv:
        json.dump(out, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1)


if __name__ == "__main__":
    main()
