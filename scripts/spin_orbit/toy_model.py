#!/usr/bin/env python3
"""Exact ℚ transcription of the LANDED Fourier-model engine of the SO checker (SO-PYALIGN).

Untrusted tooling.  Every function transcribes the Lean declaration named in its docstring over the exact
backend `ℚ` (`instCertArithRat`: add/mul exact, addErr = mulErr = 0, upAdd = +, upMul = *, ofRatUp =
ofRatDown = id, ble = <=, blt = <), so every rounding error is 0 and only the STRUCTURE of the Lean
computation remains: term lists in Lean order (no dict merging: `mergeErrTerms` merges equal keys only where
the Lean merge meets them), literal key lists (`packAddZ`, no padding), balanced `sumUp` / `modelSum` /
`CertBall.listSum` trees, `toDeg` with the Machin bounds of the `π` enclosure (`twoPiZpowHi/Lo`), `crossUp`,
the scalar product route for constant factors, and the advice lookup with its crude fallback.

Files: Model/{Basic,Ops,Terms,Exp,ExpBounds,Inv}.lean, Expr/{Compose,ComposeModels}.lean, Gram.lean,
Torsion/{Frame,Models,Average}.lean, Poly/{Basic,Ops}.lean.

Representation: a polynomial is a list of terms (key tuple, (re, im)) with Fraction coefficients, in Lean list
order; a model is (deg, poly, rad).
"""
from fractions import Fraction as F
import toy_arith as A

PI_LO, PI_UP = A.PI_LO, A.PI_UP
ZERO = F(0)


# ---------------------------------------------------------------- keys (Poly/Basic, Model/Terms, Poly/Advice)
def keyDeg(k):
    """keyDeg: |k|₁ of the stored key."""
    return sum(abs(x) for x in k)


def packAddZ(k, l):
    """packAddZ: zero-extended coordinatewise sum (length max)."""
    if len(k) < len(l):
        k, l = l, k
    return tuple(k[i] + (l[i] if i < len(l) else 0) for i in range(len(k)))


def getD(k, j):
    return k[j] if j < len(k) else 0


def zeros(n):
    return (0,) * n


def padKey(n, k):
    """padKey: length-n key with the same index."""
    return tuple(getD(k, j) for j in range(n))


def isZeroKey(k):
    """Model/Inv isZeroKey: every entry zero (any length)."""
    return all(z == 0 for z in k)


def isZeroKeyN(n, k):
    """Torsion/Average isZeroKeyN: the first n entries (getD 0) are zero."""
    return all(getD(k, i) == 0 for i in range(n))


# ---------------------------------------------------------------- complex numbers and balls (exact)
def normUp(c):
    return abs(c[0]) + abs(c[1])


def cmul(c, d):
    return (c[0] * d[0] - c[1] * d[1], c[0] * d[1] + c[1] * d[0])


def conj(c):
    return (c[0], -c[1])


def neg(c):
    return (-c[0], -c[1])


# ---------------------------------------------------------------- balanced sums
def sumUp(vals):
    """Model/Terms sumUp: 64 rounds of pairwise sums, then foldr (exact: order is structural only)."""
    L = list(vals)
    for _ in range(64):
        if len(L) <= 1:
            break
        L = [L[i] + L[i + 1] if i + 1 < len(L) else L[i] for i in range(0, len(L), 2)]
    return sum(reversed(L), ZERO) if L else ZERO


def listSumBall(balls):
    """ExpBounds CertBall.listSum over exact balls ((re, im), r)."""
    L = list(balls)
    for _ in range(64):
        if len(L) <= 1:
            break
        L = [A.b_plus(L[i], L[i + 1]) if i + 1 < len(L) else L[i] for i in range(0, len(L), 2)]
    if not L:
        return ((ZERO, ZERO), ZERO)
    out = L[-1]
    for b in reversed(L[:-1]):
        out = A.b_plus(b, out)
    return out


def coeffSumBall(P):
    """CertPoly.coeffSumBall: balanced ball sum of the coefficients (radius 0 over ℚ)."""
    return listSumBall([((t[1][0], t[1][1]), ZERO) for t in P])


# ---------------------------------------------------------------- polynomials
def weightTermUp(w, k, e):
    return abs(e) * F(w) ** keyDeg(k)


def supNormUp(P, w):
    """CertPoly.supNormUp (= weightedNormUp over ℚ): Σ |c| w^{|k|₁} over the stored terms."""
    return sumUp(weightTermUp(w, k, normUp(c)) for k, c in P)


def isConst(P):
    """CertPoly.isConst: every key all zero (the empty polynomial included)."""
    return all(isZeroKey(k) for k, _ in P)


def negP(P):
    return [(k, neg(c)) for k, c in P]


def _strict_sorted(P):
    return all(P[i][0] < P[i + 1][0] for i in range(len(P) - 1))


def merge(xs, ys):
    """mergeErrTerms (exact): the literal lexicographic merge, equal keys added (keyCmp = tuple order)."""
    out, i, j = [], 0, 0
    while i < len(xs) and j < len(ys):
        x, y = xs[i], ys[j]
        if x[0] < y[0]:
            out.append(x); i += 1
        elif y[0] < x[0]:
            out.append(y); j += 1
        else:
            out.append((x[0], (x[1][0] + y[1][0], x[1][1] + y[1][1]))); i += 1; j += 1
    out.extend(xs[i:]); out.extend(ys[j:])
    return out


def rowItems(s, bs):
    return [(packAddZ(s[0], t[0]), cmul(s[1], t[1])) for t in bs]


def directItems(As, Bs, stats=None):
    """directItems: foldl of merges of the rows.  Fast path (identical result): both term lists strictly
    ascending with keys of one common length, so every row is ascending and every merge is a sorted union."""
    if stats is not None:
        stats["pairs"] = stats.get("pairs", 0) + len(As) * len(Bs)
    lens = {len(k) for k, _ in As} | {len(k) for k, _ in Bs}
    if len(lens) <= 1 and _strict_sorted(As) and _strict_sorted(Bs):
        d = {}
        for ka, (a, b) in As:
            for kb, (c, e) in Bs:
                k = tuple(x + y for x, y in zip(ka, kb))
                x, y = d.get(k, (ZERO, ZERO))
                d[k] = (x + a * c - b * e, y + a * e + b * c)
        return sorted(d.items())
    acc = []
    for s in As:
        acc = merge(acc, rowItems(s, Bs))
    return acc


def shift(m, P):
    """CertPoly.shift."""
    return [(packAddZ(m, k), c) for k, c in P]


def conjReflect(P):
    return [(tuple(-x for x in k), conj(c)) for k, c in P]


def reflectSorted(P):
    return list(reversed(conjReflect(P)))


def toSortedPoly(n, Pr):
    """CertRealPoly.toSortedPoly: conjugates of the half terms (reversed), the zero term, the half terms."""
    zero, half = Pr
    half = [(tuple(k), (F(c[0]), F(c[1]))) for k, c in half]
    return ([(tuple(-x for x in k), conj(c)) for k, c in reversed(half)] + [(zeros(n), (F(zero), ZERO))]
            + half)


def isZeroData(Pr):
    return len(Pr[1]) == 0 and F(Pr[0]) == 0


# ---------------------------------------------------------------- models
class Model:
    __slots__ = ("deg", "poly", "rad")

    def __init__(self, deg, poly, rad=ZERO):
        self.deg, self.poly, self.rad = int(deg), poly, F(rad)


def zeroModel():
    return Model(0, [], ZERO)


def constModel(n, re, im, deg=0):
    return Model(deg, [(zeros(n), (F(re), F(im)))], ZERO)


def realCompModel(n, d, Pr):
    return zeroModel() if Pr is None else Model(d, toSortedPoly(n, Pr), ZERO)


def realCompPoly(n, Pr):
    return [] if Pr is None else toSortedPoly(n, Pr)


def negM(a):
    return Model(a.deg, negP(a.poly), a.rad)


def degFactorUp(d):
    return (2 * PI_UP) ** d if d >= 0 else (2 * PI_LO) ** d


def supBound(m, w):
    """CertModel.supBound."""
    return degFactorUp(m.deg) * (supNormUp(m.poly, w) + m.rad)


def piLowPos(k, j):
    return max(A.piLowRat(k, j), PI_LO)


def piUpMin(k, j):
    return min(A.piUpRat(k, j), PI_UP)


def twoPiZpowLo(k, j, e):
    return (2 * piLowPos(k, j)) ** e if e >= 0 else 1 / (2 * piUpMin(k, j)) ** (-e)


def twoPiZpowHi(k, j, e):
    return (2 * piUpMin(k, j)) ** e if e >= 0 else 1 / (2 * piLowPos(k, j)) ** (-e)


def toDeg(w, pe, d, a, log=None):
    """CertModel.toDeg: centre the UPPER bound c of (2π)^e, radius (c - lo)|P|_w + c rad."""
    if a.deg == d:
        return a
    if log is not None:
        log.append(("toDeg", a.deg, d))
    e = a.deg - d
    c = twoPiZpowHi(pe[2], pe[3], e)
    lo = twoPiZpowLo(pe[2], pe[3], e)
    return Model(d, [(k, (c * x[0], c * x[1])) for k, x in a.poly], c * a.rad + (c - lo) * supNormUp(a.poly, w))


def add(a, b):
    """CertModel.add (degree of a; no re-expression)."""
    return Model(a.deg, merge(a.poly, b.poly), a.rad + b.rad)


def addMixed(w, pe, a, b, log=None):
    """CertModel.addMixed (Gram.lean)."""
    b2 = toDeg(w, pe, a.deg, b, log)
    if not b2.poly:
        return Model(a.deg, a.poly, a.rad + b2.rad)
    if not a.poly:
        return Model(a.deg, b2.poly, a.rad + b2.rad)
    return add(a, b2)


def modelSum(w, pe, L, log=None):
    """modelSum: 64 rounds of pairwise addMixed, then a left fold; zeroModel for []."""
    L = list(L)
    for _ in range(64):
        if len(L) <= 1:
            break
        L = [addMixed(w, pe, L[i], L[i + 1], log) if i + 1 < len(L) else L[i] for i in range(0, len(L), 2)]
    if not L:
        return zeroModel()
    acc = L[0]
    for m in L[1:]:
        acc = addMixed(w, pe, acc, m, log)
    return acc


def derivItems(j, P):
    """filterMap derivItem j: i k_j c, terms with k_j = 0 dropped."""
    out = []
    for k, (a, b) in P:
        kj = getD(k, j)
        if kj != 0:
            out.append((k, (-b * kj, a * kj)))
    return out


def ofDeriv(j, d, P):
    return Model(d + 1, derivItems(j, P), ZERO)


def ofDeriv2(j, l, d, P):
    """CertModel.ofDeriv2 (Torsion/Frame): -k_j k_l c, factor 0 dropped, degree d + 2."""
    out = []
    for k, (a, b) in P:
        m = -(getD(k, j) * getD(k, l))
        if m != 0:
            out.append((k, (a * m, b * m)))
    return Model(d + 2, out, ZERO)


# ---------------------------------------------------------------- advice books
class Cfg:
    """ModelConfig over ℚ on the direct route.  `book` is None in GENERATE mode (every advice lookup answers
    `direct` and is recorded) or a set of key tuples in CHECK mode (a missing key gives Lean's fallback:
    the crude enclosure in `CertModel.mul`, the direct product in `expResidualProduct`)."""

    def __init__(self, name, cutoff, taylorN, halvings, book=None):
        assert isinstance(cutoff, int) and not isinstance(cutoff, bool) and cutoff >= 0, cutoff
        self.name, self.cutoff, self.taylorN, self.halvings = name, cutoff, taylorN, halvings
        self.book = None if book is None else set(tuple(k) for k in book)
        self.products = []          # every CertModel.mul / residual product: (full key, |a|, |b|, pairs, route)
        self.lookups = []           # full keys looked up, in call order
        self.misses = []            # looked up but absent (CHECK mode)
        self.maxK = 0               # largest |k|₁ of any CertModel.mul product before truncation
        self.prefix = None          # forWitness (s, i)

    def forWitness(self, s, i):
        """ModelConfig.forWitness: the sub-book of keys s :: i :: rest, re-keyed s :: rest."""
        assert self.prefix is None, "nested forWitness does not occur in the checker"
        c = Cfg.__new__(Cfg)
        c.name, c.cutoff, c.taylorN, c.halvings = self.name, self.cutoff, self.taylorN, self.halvings
        c.parent, c.prefix = self, (s, i)
        return c

    def root(self):
        return self.parent.root() if self.prefix is not None else self

    def full_key(self, key):
        key = tuple(key)
        if self.prefix is None:
            return key
        s, i = self.prefix
        return (s, i) + key[1:] if key and key[0] == s else None     # never found in the sub-book

    def lookup(self, key):
        """adviceLookup through the (sub-)book: True iff `direct` advice is found."""
        fk = self.full_key(key)
        r = self.root()
        if fk is None:
            r.misses.append(("unmappable", self.prefix, tuple(key)))
            return False
        r.lookups.append(fk)
        if r.book is None or fk in r.book:
            return True
        r.misses.append(fk)
        return False


def polyProduct(w, cfg, key, a, b):
    """CertModel.polyProduct: (items, err) or None.  Scalar route for a constant factor (no lookup)."""
    st = {}
    root = cfg.root()
    if isConst(a):
        out = directItems(a, b, st); route = "scalar"
    elif isConst(b):
        out = directItems(b, a, st); route = "scalar"
    elif cfg.lookup(key):
        out = directItems(a, b, st); route = "direct"
    else:
        out = None; route = "missing"
    fk = cfg.full_key(key)
    root.products.append((fk if fk is not None else tuple(key), len(a), len(b), st.get("pairs", 0), route))
    return None if out is None else (out, ZERO)


def crossUp(nv, r):
    return ZERO if r == 0 else nv * r


def mulN(w, cfg, key, a, na, b, nb):
    """CertModel.mulN / CertModel.mul (na, nb the factors' supNormUp)."""
    out = polyProduct(w, cfg, key, a.poly, b.poly)
    if out is None:
        return Model(a.deg + b.deg, [], (na + a.rad) * (nb + b.rad))
    items, err = out
    root = cfg.root()
    if items:
        root.maxK = max(root.maxK, max(keyDeg(k) for k, _ in items))
    keep = [t for t in items if keyDeg(t[0]) <= cfg.cutoff]
    drop = sumUp(weightTermUp(w, k, normUp(c)) for k, c in items if keyDeg(k) > cfg.cutoff)
    return Model(a.deg + b.deg, keep,
                 (err + drop) + ((crossUp(na, b.rad) + crossUp(nb, a.rad)) + a.rad * b.rad))


def mul(w, cfg, key, a, b):
    return mulN(w, cfg, key, a, supNormUp(a.poly, w), b, supNormUp(b.poly, w))


# ---------------------------------------------------------------- real exponential bounds (Model/ExpBounds)
def expRemFactor(M):
    return F(M + 1) / (A.factorial(M) * M)


def expSeriesUp(y, k, m, p, S):
    while k > 0:
        S = S + p * y * (F(1) / A.factorial(m + 1))
        p, m, k = p * y, m + 1, k - 1
    return S + p * y * expRemFactor(m + 1)


def expm1Up(s, N, x):
    """expm1Up: an upper bound of exp x - 1 (None unless x/2^s <= 1 and N >= 1)."""
    y = F(x) * (F(1) / 2 ** s)
    if not (y <= 1 and N >= 1):
        return None
    z = expSeriesUp(y, N - 1, 0, F(1), ZERO)
    for _ in range(s):
        z = z * (2 + z)
    return z


# ---------------------------------------------------------------- witnesses (Model/Exp, Model/Inv)
def expPinBall(g):
    b = coeffSumBall(g.poly)
    return b[0], b[1]


def expPinErr(E, out):
    d = A.b_plus(coeffSumBall(E), (neg(out[0]), out[1]))
    return normUp(d[0]) + d[1]


def expResidualProduct(w, cfg, g0, E, j):
    dg = derivItems(j, g0)
    out = polyProduct(w, cfg, (1, j), dg, negP(E))
    return out if out is not None else (directItems(dg, negP(E)), ZERO)


def expResidualUp(w, cfg, g0, E, eN, j):
    items, err = expResidualProduct(w, cfg, g0, E, j)
    merged = merge(derivItems(j, E), items)
    return 2 * PI_UP * ((sumUp(weightTermUp(w, k, normUp(c)) for k, c in merged) + err) + crossUp(eN, ZERO))


def expWitnessRadiusOf(n, w, rho, cfg, g, E, out):
    mB = expm1Up(cfg.halvings, cfg.taylorN, supNormUp(g.poly, w))
    mEta = expm1Up(cfg.halvings, cfg.taylorN, g.rad)
    if mB is None or mEta is None:
        return None
    eB = 1 + mB
    eN = supNormUp(E, w)
    res = sumUp(expResidualUp(w, cfg, g.poly, E, eN, j) for j in range(n))
    return eB * eB * (expPinErr(E, out) + (F(1, 2) + F(rho)) * res) + eB * mEta


def expWitnessRadius(n, w, rho, cfg, g, Ew):
    """expWitnessRadius: Ew = (poly, pinHalvings, pinOrder)."""
    E, s, N = Ew
    z, zr = expPinBall(g)
    out = A.certCExpReduced(z, zr, s, N)
    if out is None:
        return None
    return expWitnessRadiusOf(n, w, rho, cfg, g, E, out)


def oneSubSupUp(w, u):
    z = coeffSumBall([t for t in u.poly if isZeroKey(t[0])])
    d = A.b_plus(A.b_one(), (neg(z[0]), z[1]))
    return ((normUp(d[0]) + d[1]) + supNormUp([t for t in u.poly if not isZeroKey(t[0])], w)) + u.rad


def recipOneSubUp(d):
    """recipBoundAux 64 δ 1: Π (1 + δ^{2^i}) closed by (1 + 2x) once 2x <= 1 (None after 64 squarings)."""
    x, acc = F(d), F(1)
    for _ in range(64):
        if x + x <= 1:
            return acc * (1 + (x + x))
        x, acc = x * x, acc * (1 + x)
    return None


def invWitnessRadius(n, w, cfg, b, Q):
    """invWitnessRadius: (radius or None, δ)."""
    d = oneSubSupUp(w, mul(w, cfg, (2,), Model(0, Q, ZERO), Model(0, b.poly, b.rad)))
    if d < 1:
        t = recipOneSubUp(d)
        return (None if t is None else supNormUp(Q, w) * d * t), d
    return None, d
