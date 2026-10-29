#!/usr/bin/env python3
"""SO-DATA-1: backend-generic mirror of the LANDED Fourier-model engine (untrusted tooling).

Transcribes, for any backend `B` of sofx_arith (FixedB(P) or RatB):
  Model/Basic.lean     checkWeight, CertPoly.weightedNormUp, degFactorUp, CertModel.supBound
  Model/Terms.lean     keyDeg, CC.{addC,addErrC,mulC,mulErrC,scaleC,scaleErrC}, sumUp, weightTermUp, errRadius,
                       supNormUp, mergeErrPair/mergeErrTerms, rowItems, directItems, truncKeep/truncErr/truncPoly
  Model/Ops.lean       itemsPoly, isConst, CertModel.add, polyProduct, crossUp, CertModel.mul, piLowPos, piUpMin,
                       twoPiZpowLo/Hi, scaleItems, CertModel.toDeg, derivItem, CertModel.ofDeriv, adviceLookup
  Model/ExpBounds.lean CertBall.listSum, coeffSumBall, negP, expRemFactor, expSeriesUp, expm1SqIter, expm1Up
  Model/Exp.lean       expPinBall, expPinErr, expResidualProduct, expResidualUp, expWitnessRadiusOf/Radius
  Model/Inv.lean       isZeroKey, oneSubSupUp, recipBoundAux/recipOneSubUp, invWitnessRadius
  Expr/ComposeModels   zeroModel, ratErrUp, padKey, constModel, toSortedPoly, realCompModel, imulItems,
                       phaseTermModel, charPhaseModel, isZeroData, angleIsZero, normKey, reflectSorted, shiftModel,
                       findKeyIdx, subAdvice, forWitness
  Expr/Compose.lean    mulN, ComposeState, charResolve, charEntry, charSlot, composeStep, composeOps, Slp.compose
  Poly/{Basic,Ops}     packAddZ, CertPoly.shift, conjReflect

Representation: key = tuple of ints; a polynomial = list of (key, (re, im)); an ErrTerm = (key, (re, im), err);
a model = Model(deg, poly, rad).  Lists are kept in Lean order.

Products: `polyProduct` consults `cfg.engine` for the packed route (sofx_packed); in GENERATE mode the engine
builds the advice from the exact product and then runs the LANDED check on it (the mirror never trusts the
generator).  Every lookup is recorded (key coverage).
"""
from fractions import Fraction as F
import sofx_arith as A


# ---------------------------------------------------------------------------------------------- keys
def keyDeg(k):
    return sum(x if x >= 0 else -x for x in k)


def packAddZ(k, l):
    if len(k) < len(l):
        return tuple(l[i] + (k[i] if i < len(k) else 0) for i in range(len(l)))
    return tuple(k[i] + (l[i] if i < len(l) else 0) for i in range(len(k)))


def getD(k, j):
    return k[j] if j < len(k) else 0


def padKey(n, k):
    return tuple(getD(k, j) for j in range(n))


def isZeroKey(k):
    return all(z == 0 for z in k)


def keyCmpLt(a, b):
    """keyCmp a b = .lt (lexicographic, shorter prefix first) — Python tuple order is the same."""
    return a < b


# ---------------------------------------------------------------------------------------------- CC
def addC(B, c, d):
    return (B.add(c[0], d[0]), B.add(c[1], d[1]))


def addErrC(B, c, d):
    return B.upAdd(B.addErr(c[0], d[0]), B.addErr(c[1], d[1]))


def mulC(B, c, d):
    return (B.add(B.mul(c[0], d[0]), B.neg(B.mul(c[1], d[1]))), B.add(B.mul(c[0], d[1]), B.mul(c[1], d[0])))


def mulErrC(B, c, d):
    return B.upAdd(A.mulReErr(B, c[0], c[1], d[0], d[1]), A.mulImErr(B, c[0], c[1], d[0], d[1]))


def scaleC(B, s, c):
    return (B.mul(s, c[0]), B.mul(s, c[1]))


def scaleErrC(B, s, c):
    return B.upAdd(B.mulErr(s, c[0]), B.mulErr(s, c[1]))


def negC(B, c):
    return (B.neg(c[0]), B.neg(c[1]))


def conjC(B, c):
    return (c[0], B.neg(c[1]))


# ---------------------------------------------------------------------------------------------- sums
def sumUp(B, vals):
    """sumUp: pairRounds 64 (pairwise upAdd) then foldr upAdd (ofInt 0)."""
    L = list(vals)
    for _ in range(64):
        if len(L) <= 1:
            break
        L = [B.upAdd(L[i], L[i + 1]) if i + 1 < len(L) else L[i] for i in range(0, len(L), 2)]
    acc = B.ofInt(0)
    for v in reversed(L):
        acc = B.upAdd(v, acc)
    return acc


class Weight:
    """CertWeight (rho, w) with a cache of ofRatUp (w ^ d)."""

    def __init__(self, rho, w):
        self.rho, self.w = F(rho), F(w)
        self._c = {}

    def powUp(self, B, d):
        key = (id(B), d)
        if key not in self._c:
            self._c[key] = B.ofRatUp(self.w ** d)
        return self._c[key]


def weightTermUp(B, W, k, e):
    return B.upMul(B.abs(e), W.powUp(B, keyDeg(k)))


def errRadius(B, W, L):
    return sumUp(B, (weightTermUp(B, W, t[0], t[2]) for t in L))


def supNormUp(B, W, P):
    return sumUp(B, (weightTermUp(B, W, k, A.normUp(B, c)) for k, c in P))


def weightedNormUp(B, W, P):
    acc = B.ofInt(0)
    for k, c in reversed(P):
        acc = B.upAdd(B.upMul(A.normUp(B, c), W.powUp(B, keyDeg(k))), acc)
    return acc


def degFactorUp(d):
    return (2 * A.PI_UP) ** d if d >= 0 else (2 * A.PI_LO) ** d


def ratExpUp(q, s, N):
    q = F(q)
    if q / F(2) ** s <= 1 and 0 < N:
        x = q / F(2) ** s
        r = sum((x ** m / A.factorial(m) for m in range(N)), F(0)) + x ** N * (F(N + 1) / (A.factorial(N) * N))
        for _ in range(s):
            r = r * r
        return r
    c = q.numerator // q.denominator + (1 if q.numerator % q.denominator else 0)
    return F(3) ** max(c, 0)


def checkWeight(W, s, N):
    return W.rho > 0 and ratExpUp(2 * A.PI_UP * W.rho, s, N) <= W.w


# ---------------------------------------------------------------------------------------------- terms
def toErrTerms(B, P):
    z = B.ofInt(0)
    return [(k, c, z) for k, c in P]


def itemsPoly(L):
    return [(t[0], t[1]) for t in L]


def mergeErrTerms(B, xs, ys):
    """mergeErrTerms: literally the two-pointer merge (x from xs, y from ys; equal keys -> mergeErrPair)."""
    out, i, j, nx, ny = [], 0, 0, len(xs), len(ys)
    while i < nx and j < ny:
        x, y = xs[i], ys[j]
        if x[0] < y[0]:
            out.append(x); i += 1
        elif y[0] < x[0]:
            out.append(y); j += 1
        else:
            out.append((x[0], addC(B, x[1], y[1]), B.upAdd(B.upAdd(x[2], y[2]), addErrC(B, x[1], y[1]))))
            i += 1; j += 1
    if i < nx:
        out.extend(xs[i:])
    if j < ny:
        out.extend(ys[j:])
    return out


def rowItems(B, s, bs):
    return [(packAddZ(s[0], t[0]), mulC(B, s[1], t[1]), mulErrC(B, s[1], t[1])) for t in bs]


def directItems(B, As, Bs):
    acc = []
    for s in As:
        acc = mergeErrTerms(B, acc, rowItems(B, s, Bs))
    return acc


def truncKeep(cutoff, t):
    return keyDeg(t[0]) <= cutoff


def truncErr(B, cutoff, t):
    return t if truncKeep(cutoff, t) else (t[0], t[1], B.upAdd(t[2], A.normUp(B, t[1])))


def truncPoly(cutoff, L):
    return [(t[0], t[1]) for t in L if truncKeep(cutoff, t)]


def isConst(P):
    return all(isZeroKey(k) for k, _ in P)


def negP(B, P):
    return [(k, negC(B, c)) for k, c in P]


def shift(m, P):
    return [(packAddZ(m, k), c) for k, c in P]


def conjReflect(B, P):
    return [(tuple(-x for x in k), conjC(B, c)) for k, c in P]


def reflectSorted(B, P):
    return list(reversed(conjReflect(B, P)))


# ---------------------------------------------------------------------------------------------- models
class Model:
    __slots__ = ("deg", "poly", "rad")

    def __init__(self, deg, poly, rad):
        self.deg, self.poly, self.rad = int(deg), poly, rad


def zeroModel(B):
    return Model(0, [], B.ofInt(0))


def negM(B, a):
    return Model(a.deg, negP(B, a.poly), a.rad)


def supBound(B, W, m):
    return B.upMul(B.ofRatUp(degFactorUp(m.deg)), B.upAdd(weightedNormUp(B, W, m.poly), m.rad))


def model_add(B, W, a, b):
    """CertModel.add (degree of a)."""
    L = mergeErrTerms(B, toErrTerms(B, a.poly), toErrTerms(B, b.poly))
    return Model(a.deg, itemsPoly(L), B.upAdd(B.upAdd(a.rad, b.rad), errRadius(B, W, L)))


def piLowPos(k, j):
    return max(A.piLowRat(k, j), A.PI_LO)


def piUpMin(k, j):
    return min(A.piUpRat(k, j), A.PI_UP)


def twoPiZpowLo(k, j, e):
    return (2 * piLowPos(k, j)) ** e if e >= 0 else 1 / (2 * piUpMin(k, j)) ** (-e)


def twoPiZpowHi(k, j, e):
    return (2 * piUpMin(k, j)) ** e if e >= 0 else 1 / (2 * piLowPos(k, j)) ** (-e)


def scaleItems(B, s, P):
    return [(k, scaleC(B, s, c), scaleErrC(B, s, c)) for k, c in P]


def toDeg(B, W, pe, d, a):
    if a.deg == d:
        return a
    c = B.ofRatUp(twoPiZpowHi(pe.machinK, pe.machinJ, a.deg - d))
    lo = B.ofRatDown(twoPiZpowLo(pe.machinK, pe.machinJ, a.deg - d))
    r = B.upAdd(B.add(c, B.neg(lo)), B.addErr(c, B.neg(lo)))
    S = scaleItems(B, c, a.poly)
    return Model(d, itemsPoly(S), B.upAdd(B.upMul(c, a.rad),
                                          B.upAdd(B.upMul(r, supNormUp(B, W, a.poly)), errRadius(B, W, S))))


def derivItem(B, j, t):
    kj = getD(t[0], j)
    if kj == 0:
        return None
    m = B.ofInt(kj)
    re, im = t[1]
    return (t[0], (B.neg(B.mul(im, m)), B.mul(re, m)), B.upAdd(B.mulErr(im, m), B.mulErr(re, m)))


def derivItems(B, j, P):
    out = []
    for t in P:
        x = derivItem(B, j, t)
        if x is not None:
            out.append(x)
    return out


def ofDeriv(B, W, j, d, P):
    L = derivItems(B, j, P)
    return Model(d + 1, itemsPoly(L), errRadius(B, W, L))


def deriv2Item(B, j, l, t):
    m = -(getD(t[0], j) * getD(t[0], l))
    if m == 0:
        return None
    mm = B.ofInt(m)
    re, im = t[1]
    return (t[0], (B.mul(re, mm), B.mul(im, mm)), B.upAdd(B.mulErr(re, mm), B.mulErr(im, mm)))


def ofDeriv2(B, W, j, l, d, P):
    L = [x for x in (deriv2Item(B, j, l, t) for t in P) if x is not None]
    return Model(d + 2, itemsPoly(L), errRadius(B, W, L))


def addMixed(B, W, pe, a, b):
    b2 = toDeg(B, W, pe, a.deg, b)
    if not b2.poly:
        return Model(a.deg, a.poly, B.upAdd(a.rad, b2.rad))
    if not a.poly:
        return Model(a.deg, b2.poly, B.upAdd(a.rad, b2.rad))
    return model_add(B, W, a, b2)


def modelSum(B, W, pe, L):
    L = list(L)
    for _ in range(64):
        if len(L) <= 1:
            break
        L = [addMixed(B, W, pe, L[i], L[i + 1]) if i + 1 < len(L) else L[i] for i in range(0, len(L), 2)]
    if not L:
        return zeroModel(B)
    acc = L[0]
    for m in L[1:]:
        acc = addMixed(B, W, pe, acc, m)
    return acc


# ---------------------------------------------------------------------------------------------- config / advice
class Cfg:
    """ModelConfig: cutoff, taylorN, halvings, the advice book (list of (key tuple, advice)) and the product
    engine.  `advice` entries: ("direct",) or ("packed", P, rr, ii, ri, ir).  GENERATE mode (book=None): every
    genuine lookup is answered by the engine's generator and recorded; CHECK mode: the book is consulted exactly
    as `adviceLookup` (first match)."""

    def __init__(self, name, cutoff, taylorN, halvings, book=None, engine=None, budget=None):
        self.name, self.cutoff, self.taylorN, self.halvings = name, cutoff, taylorN, halvings
        self.book = book
        self.engine = engine
        self.budget = budget
        self.prefix = None
        self.parent = None
        self.generated = []        # (full key, advice) in lookup order (GENERATE mode)
        self.lookups = []          # full keys looked up
        self.misses = []
        self.products = []         # (full key, route, |a|, |b|, info)
        self.extra = []            # appended (key, advice) entries (realLowerModel's cfg')

    def root(self):
        return self.parent.root() if self.parent is not None else self

    def forWitness(self, s, i):
        c = Cfg.__new__(Cfg)
        c.__dict__.update(self.__dict__)
        c.parent, c.prefix = self, (s, i)
        return c

    def withExtra(self, key, adv):
        c = Cfg.__new__(Cfg)
        c.__dict__.update(self.__dict__)
        c.parent = self
        c.prefix = None
        c.extra = list(self.extra) + [(tuple(key), adv)]
        return c

    def full_key(self, key):
        key = tuple(key)
        if self.prefix is None:
            return self.parent.full_key(key) if self.parent is not None else key
        s, i = self.prefix
        if not key or key[0] != s:
            return None
        return self.parent.full_key((s, i) + key[1:])

    def lookup(self, key):
        """adviceLookup through sub-books and appended entries: the advice found, or None."""
        key = tuple(key)
        r = self.root()
        fk = self.full_key(key)
        # an appended entry (cfg.advice ++ [...]) is found only after the whole book
        if fk is not None:
            r.lookups.append(fk)
            if r.book is not None:
                for k2, adv in r.book:
                    if k2 == fk:
                        return adv
        for k2, adv in self.extra:
            if k2 == key:
                return adv
        if fk is None:
            r.misses.append(("unmappable", key))
            return None
        if r.book is None:
            return ("generate",)
        r.misses.append(fk)
        return None


def polyProduct(B, W, cfg, key, a, b):
    root = cfg.root()
    fk = cfg.full_key(key)
    if isConst(a):
        root.products.append((fk, "scalar", len(a), len(b), None))
        return (directItems(B, a, b), B.ofInt(0))
    if isConst(b):
        root.products.append((fk, "scalar", len(a), len(b), None))
        return (directItems(B, b, a), B.ofInt(0))
    adv = cfg.lookup(key)
    if adv is None:
        root.products.append((fk, "missing", len(a), len(b), None))
        return None
    if adv[0] == "direct":
        root.products.append((fk, "direct", len(a), len(b), None))
        return (directItems(B, a, b), B.ofInt(0))
    if adv[0] == "generate":
        adv = root.engine.generate(B, W, root, fk, a, b)
        root.generated.append((fk, adv))
        if adv[0] == "direct":
            root.products.append((fk, "direct", len(a), len(b), None))
            return (directItems(B, a, b), B.ofInt(0))
    out = root.engine.mulPacked(B, W, adv, a, b)
    root.products.append((fk, "packed" if out is not None else "packed-FAIL", len(a), len(b),
                          root.engine.last_info))
    if out is None:
        return None
    return (toErrTerms(B, out[0]), out[1])


def crossUp(B, n, r):
    return B.ofInt(0) if B.beq(r, B.ofInt(0)) else B.upMul(n, r)


def mulN(B, W, cfg, key, a, na, b, nb):
    out = polyProduct(B, W, cfg, key, a.poly, b.poly)
    if out is not None:
        items, err = out
        return Model(a.deg + b.deg, truncPoly(cfg.cutoff, items),
                     B.upAdd(B.upAdd(err, errRadius(B, W, [truncErr(B, cfg.cutoff, t) for t in items])),
                             B.upAdd(B.upAdd(crossUp(B, na, b.rad), crossUp(B, nb, a.rad)), B.upMul(a.rad, b.rad))))
    return Model(a.deg + b.deg, [], B.upMul(B.upAdd(na, a.rad), B.upAdd(nb, b.rad)))


def model_mul(B, W, cfg, key, a, b):
    return mulN(B, W, cfg, key, a, supNormUp(B, W, a.poly), b, supNormUp(B, W, b.poly))


# ---------------------------------------------------------------------------------------------- ExpBounds
def listSumBall(B, L):
    L = list(L)
    for _ in range(64):
        if len(L) <= 1:
            break
        L = [A.ball_plus(B, L[i], L[i + 1]) if i + 1 < len(L) else L[i] for i in range(0, len(L), 2)]
    if not L:
        return ((B.ofInt(0), B.ofInt(0)), B.ofInt(0))
    out = L[-1]
    for b in reversed(L[:-1]):
        out = A.ball_plus(B, b, out)
    return out


def coeffSumBall(B, P):
    z = B.ofInt(0)
    return listSumBall(B, [(c, z) for _, c in P])


def expRemFactor(M):
    return F(M + 1) / (A.factorial(M) * M)


def expSeriesUp(B, y, k, m, p, S):
    while k > 0:
        S = B.upAdd(S, B.upMul(B.upMul(p, y), B.ofRatUp(F(1, A.factorial(m + 1)))))
        p, m, k = B.upMul(p, y), m + 1, k - 1
    return B.upAdd(S, B.upMul(B.upMul(p, y), B.ofRatUp(expRemFactor(m + 1))))


def expm1Up(B, s, N, x):
    y = B.upMul(x, B.ofRatUp(F(1, 2 ** s)))
    if B.ble(y, B.ofInt(1)) and 1 <= N:
        z = expSeriesUp(B, y, N - 1, 0, B.ofInt(1), B.ofInt(0))
        for _ in range(s):
            z = B.upMul(z, B.upAdd(B.ofInt(2), z))
        return z
    return None


# ---------------------------------------------------------------------------------------------- Exp witnesses
def expPinBall(B, g):
    b = coeffSumBall(B, g.poly)
    return b[0], b[1]


def expPinErr(B, E, out):
    d = A.ball_plus(B, coeffSumBall(B, E), (negC(B, out[0]), out[1]))
    return B.upAdd(A.normUp(B, d[0]), d[1])


def expResidualProduct(B, W, cfg, g0, E, j):
    dg = itemsPoly(derivItems(B, j, g0))
    out = polyProduct(B, W, cfg, (1, j), dg, negP(B, E))
    if out is not None:
        return out
    return (directItems(B, dg, negP(B, E)), B.ofInt(0))


def expResidualUp(B, W, cfg, g0, E, eN, j):
    pr = expResidualProduct(B, W, cfg, g0, E, j)
    merged = mergeErrTerms(B, derivItems(B, j, E), pr[0])
    s = sumUp(B, (weightTermUp(B, W, t[0], B.upAdd(A.normUp(B, t[1]), t[2])) for t in merged))
    return B.upMul(B.ofRatUp(2 * A.PI_UP),
                   B.upAdd(B.upAdd(s, pr[1]), crossUp(B, eN, errRadius(B, W, derivItems(B, j, g0)))))


def expWitnessRadiusOf(B, n, W, cfg, g, E, out, info=None):
    mB = expm1Up(B, cfg.halvings, cfg.taylorN, supNormUp(B, W, g.poly))
    mEta = expm1Up(B, cfg.halvings, cfg.taylorN, g.rad)
    if mB is None or mEta is None:
        return None
    eB = B.upAdd(B.ofInt(1), mB)
    eN = supNormUp(B, W, E)
    res_j = [expResidualUp(B, W, cfg, g.poly, E, eN, j) for j in range(n)]
    res = sumUp(B, res_j)
    pin = expPinErr(B, E, out)
    if info is not None:
        info.update(mB=mB, mEta=mEta, res=res_j, pin=pin)
    return B.upAdd(B.upMul(B.upMul(eB, eB), B.upAdd(pin, B.upMul(B.ofRatUp(F(1, 2) + W.rho), res))),
                   B.upMul(eB, mEta))


def expWitnessRadius(B, n, W, cfg, g, Ew, info=None):
    """Ew = (poly, pinHalvings, pinOrder)."""
    z, zr = expPinBall(B, g)
    out = A.certCExpReduced(B, z, zr, Ew[1], Ew[2])
    if out is None:
        return None
    return expWitnessRadiusOf(B, n, W, cfg, g, Ew[0], out, info)


# ---------------------------------------------------------------------------------------------- Inv witnesses
def oneSubSupUp(B, W, u):
    z = coeffSumBall(B, [t for t in u.poly if isZeroKey(t[0])])
    d = A.ball_plus(B, A.oneBall(B), (negC(B, z[0]), z[1]))
    return B.upAdd(B.upAdd(B.upAdd(A.normUp(B, d[0]), d[1]),
                           supNormUp(B, W, [t for t in u.poly if not isZeroKey(t[0])])), u.rad)


def recipOneSubUp(B, x):
    acc = B.ofInt(1)
    for _ in range(64):
        if B.ble(B.upAdd(x, x), B.ofInt(1)):
            return B.upMul(acc, B.upAdd(B.ofInt(1), B.upAdd(x, x)))
        x, acc = B.upMul(x, x), B.upMul(acc, B.upAdd(B.ofInt(1), x))
    return None


def invWitnessRadius(B, n, W, cfg, b, Q):
    d = oneSubSupUp(B, W, model_mul(B, W, cfg, (2,), Model(0, Q, B.ofInt(0)), Model(0, b.poly, b.rad)))
    if B.blt(d, B.ofInt(1)):
        t = recipOneSubUp(B, d)
        return None if t is None else B.upMul(B.upMul(supNormUp(B, W, Q), d), t)
    return None


# ---------------------------------------------------------------------------------------------- ComposeModels
def ratErrUp(B, q):
    u, d = B.ofRatUp(q), B.ofRatDown(q)
    return B.upAdd(B.add(u, B.neg(d)), B.addErr(u, B.neg(d)))


def constModel(B, n, re, im, deg):
    return Model(deg, [(padKey(n, ()), (B.ofRatUp(re), B.ofRatUp(im)))], B.upAdd(ratErrUp(B, re), ratErrUp(B, im)))


class RealPoly:
    """CertRealPoly: zero (backend value) and half (list of (key, CC))."""
    __slots__ = ("zero", "half")

    def __init__(self, zero, half):
        self.zero, self.half = zero, half


def toSortedPoly(B, n, P):
    return ([(tuple(-x for x in k), conjC(B, c)) for k, c in reversed(P.half)]
            + [(padKey(n, ()), (P.zero, B.ofInt(0)))] + list(P.half))


def realCompModel(B, n, d, P):
    return zeroModel(B) if P is None else Model(d, toSortedPoly(B, n, P), B.ofInt(0))


def realCompPoly(B, n, P):
    return [] if P is None else toSortedPoly(B, n, P)


def imulItems(B, m, P):
    mm = B.ofInt(m)
    return [(k, (B.neg(B.mul(c[1], mm)), B.mul(c[0], mm)), B.upAdd(B.mulErr(c[1], mm), B.mulErr(c[0], mm)))
            for k, c in P]


def phaseTermModel(B, n, W, d, m, P):
    if P is None:
        return zeroModel(B)
    L = imulItems(B, m, toSortedPoly(B, n, P))
    return Model(d + 1, itemsPoly(L), errRadius(B, W, L))


class Embedding:
    """CertEmbedding: angleDeg, angle (list of RealPoly), actionDeg, action."""

    def __init__(self, angleDeg, angle, actionDeg, action):
        self.angleDeg, self.angle, self.actionDeg, self.action = angleDeg, angle, actionDeg, action

    def angleAt(self, i):
        return self.angle[i] if i < len(self.angle) else None

    def actionAt(self, i):
        return self.action[i] if i < len(self.action) else None


def charPhaseModel(B, n, K, W, pe, k):
    acc = zeroModel(B)
    for j in range(n):
        if getD(k, j) == 0:
            continue
        acc = model_add(B, W, acc, toDeg(B, W, pe, 0, phaseTermModel(B, n, W, getD(K.angleDeg, j), getD(k, j),
                                                                    K.angleAt(j))))
    return acc


def isZeroData(B, P):
    return len(P.half) == 0 and B.beq(P.zero, B.ofInt(0))


def angleIsZero(B, K, j):
    P = K.angleAt(j)
    return True if P is None else isZeroData(B, P)


def normKey(B, n, K, k):
    return tuple(0 if angleIsZero(B, K, j) else getD(k, j) for j in range(n))


def shiftModel(B, W, k, P, r):
    return Model(0, shift(k, P), weightTermUp(B, W, k, r))


def findKeyIdx(k, L):
    for i, e in enumerate(L):
        if tuple(e[0]) == tuple(k):
            return i, e[1]
    return None


# ---------------------------------------------------------------------------------------------- Compose
class Witnesses:
    """expWit: list of (poly, pinHalvings, pinOrder); invWit: list of polys; charWit: list of (key, expWit)."""

    def __init__(self, expWit, invWit, charWit):
        self.expWit, self.invWit, self.charWit = expWit, invWit, charWit


class ComposeState:
    def __init__(self):
        self.slots = []       # (model, supNormUp) in slot order (rev reversed)
        self.nExp = 0
        self.nInv = 0
        self.cache = []       # (key, poly, radius), newest first
        self.info = {}

    def slot(self, B, W, i):
        if i < len(self.slots):
            return self.slots[i]
        z = zeroModel(B)
        return (z, supNormUp(B, W, z.poly))

    def push(self, B, W, m):
        self.slots.append((m, supNormUp(B, W, m.poly)))


def charResolve(B, n, K, wit, W, cfg, pe, cache, k2, info):
    e = findKeyIdx(k2, cache)
    if e is not None:
        return e[1], cache
    f = findKeyIdx(k2, wit.charWit)
    if f is None:
        return None
    c, E = f
    winfo = {}
    r = expWitnessRadius(B, n, W, cfg.forWitness(1, len(wit.expWit) + c), charPhaseModel(B, n, K, W, pe, k2), E,
                         winfo)
    if info is not None:
        info.setdefault("charWit", []).append((tuple(k2), r, winfo))
    if r is None:
        return None
    return (E[0], r), [(tuple(k2), (E[0], r))] + cache


def charEntry(B, n, K, wit, W, cfg, pe, cache, kk, info):
    e = charResolve(B, n, K, wit, W, cfg, pe, cache, kk, info)
    if e is not None:
        return e
    e = charResolve(B, n, K, wit, W, cfg, pe, cache, tuple(-x for x in kk), info)
    if e is None:
        return None
    (poly, r), c = e
    rp = reflectSorted(B, poly)
    return (rp, r), [(tuple(kk), (rp, r))] + c


def composeStep(B, n, K, wit, W, cfg, pe, st, op):
    t = op[0]
    if t == "const":
        st.push(B, W, constModel(B, n, F(op[1]), F(op[2]), int(op[3])))
    elif t == "action":
        j = op[1]
        st.push(B, W, realCompModel(B, n, getD(K.actionDeg, j), K.actionAt(j)) if j < n else zeroModel(B))
    elif t == "char":
        e = charEntry(B, n, K, wit, W, cfg, pe, st.cache, normKey(B, n, K, op[1]), st.info)
        if e is None:
            return None
        (poly, r), c = e
        st.push(B, W, shiftModel(B, W, padKey(n, op[1]), poly, r))
        st.cache = c
    elif t == "add":
        a = st.slot(B, W, op[1])[0]
        b = st.slot(B, W, op[2])[0]
        st.push(B, W, model_add(B, W, a, toDeg(B, W, pe, a.deg, b)))
    elif t == "mul":
        a, na = st.slot(B, W, op[1])
        b, nb = st.slot(B, W, op[2])
        st.push(B, W, mulN(B, W, cfg, (0, len(st.slots)), a, na, b, nb))
    elif t == "exp":
        if st.nExp >= len(wit.expWit):
            return None
        E = wit.expWit[st.nExp]
        r = expWitnessRadius(B, n, W, cfg.forWitness(1, st.nExp), toDeg(B, W, pe, 0, st.slot(B, W, op[1])[0]), E)
        if r is None:
            return None
        st.push(B, W, Model(0, E[0], r))
        st.nExp += 1
    elif t == "inv":
        if st.nInv >= len(wit.invWit):
            return None
        Q = wit.invWit[st.nInv]
        a = st.slot(B, W, op[1])[0]
        r = invWitnessRadius(B, n, W, cfg.forWitness(2, st.nInv), a, Q)
        if r is None:
            return None
        st.push(B, W, Model(-a.deg, Q, r))
        st.nInv += 1
    else:
        raise ValueError(op)
    return st


def compose(B, n, prog, K, wit, W, cfg, pe, wanted, info=None):
    st = ComposeState()
    for op in prog:
        if composeStep(B, n, K, wit, W, cfg, pe, st, op) is None:
            if info is not None:
                info.update(st.info)
            return None
    if info is not None:
        info.update(st.info)
    return [st.slot(B, W, i)[0] for i in wanted]
