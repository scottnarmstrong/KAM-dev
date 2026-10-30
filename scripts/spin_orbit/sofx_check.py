#!/usr/bin/env python3
"""SO-DATA-1: backend-generic mirror of the LANDED sub-checks (untrusted tooling).

  Gram.lean               addMixed/modelSum (sofx_model), compDerivModel, dkAngleModel, dkActionModel,
                          gramEntryModel, gramModels, modelMatrixEntry, gramInvPoly, gramBGModel, gramDefectUp,
                          maxCandidate, gramDefectRows, gramInvRows, gramInvShapeOk, gramBoundsOk, gramCheck
  Torsion/Models.lean     buildMat, modelMatMul, modelMatAdd, modelMatNeg, modelMatTranspose, modelMatOmega,
                          ballModel, freqModel, dkModels, d2kModel, dkwModels, gramInvRadius, gramInvModels,
                          torsionSlots, swapNat, dxhModels, d1Models, torsionModels
  Torsion/Average.lean    listShapeOk, isZeroKeyN, zeroModeBall, ccEntry, avgCentre, avgRadius, avgDefectUp,
                          avgDefectRows, avgInvRows, avgRadRows, avgDegOk, avgBoundsOk, torsionAvgCheck
  Positivity.lean         conjSorted, starModel, ofConst, keyLen, realLowerModel, checkRealLowerBound
  Defs.lean               freqNormLo, hamBoundsOk, angleModel, actionShiftModel, angleImOk, dkRowUp, d1Slots,
                          dkFreqModel, invarianceModel, energyOk, the eight sub-checks
  SpinOrbit/Graph/Cert    soGraphMonoModel, soGraphActionModel, checkSoGraph

Every sub-check returns (verdict, margins) where margins records the compared quantities (exact rationals).
"""
from fractions import Fraction as F
import sofx_arith as A
import sofx_model as M
import toy_arith as TA
import toy_constants as TC


def val(B, x):
    return B.val(x)


# ---------------------------------------------------------------------------------------------- Gram
def compDerivModel(B, n, W, pe, d, P, j):
    return M.toDeg(B, W, pe, 0, M.ofDeriv(B, W, j, d, M.realCompPoly(B, n, P)))


def dkAngleModel(B, n, K, W, pe, i, j):
    m = compDerivModel(B, n, W, pe, M.getD(K.angleDeg, i), K.angleAt(i), j)
    if i == j:
        return M.model_add(B, W, M.constModel(B, n, 1, 0, 0), m)
    return m


def dkActionModel(B, n, K, W, pe, i, j):
    return compDerivModel(B, n, W, pe, M.getD(K.actionDeg, i), K.actionAt(i), j)


def gramEntryModel(B, n, K, W, cfg, pe, a, b, DKc):
    L = [M.model_mul(B, W, cfg, (3, 0, a, b, k), DKc[("a", k, a)], DKc[("a", k, b)]) for k in range(n)]
    L += [M.model_mul(B, W, cfg, (3, 0, a, b, n + k), DKc[("p", k, a)], DKc[("p", k, b)]) for k in range(n)]
    return M.modelSum(B, W, pe, L)


def dkCache(B, n, K, W, pe):
    c = {}
    for i in range(n):
        for j in range(n):
            c[("a", i, j)] = dkAngleModel(B, n, K, W, pe, i, j)
            c[("p", i, j)] = dkActionModel(B, n, K, W, pe, i, j)
    return c


def gramModels(B, n, K, W, cfg, pe, DKc):
    G = [[None] * n for _ in range(n)]
    up = {}
    for a in range(n):
        for b in range(a, n):
            up[(a, b)] = gramEntryModel(B, n, K, W, cfg, pe, a, b, DKc)
    # the Lean matrix recomputes (b, a) for a > b with the same keys [3,0,b,a,_]: identical value
    for a in range(n):
        for b in range(n):
            G[a][b] = up[(a, b)] if a <= b else up[(b, a)]
    return G


def entry(Mx, i, j, B):
    if i < len(Mx) and j < len(Mx[i]):
        return Mx[i][j]
    return M.zeroModel(B)


def gramInvPoly(Binv, i, k):
    if i < len(Binv) and k < len(Binv[i]):
        return Binv[i][k]
    return []


def gramBGModel(B, n, Binv, G, W, cfg, pe, i, j):
    L = [M.model_mul(B, W, cfg, (3, 1, i, j, k), M.Model(0, gramInvPoly(Binv, i, k), B.ofInt(0)), entry(G, k, j, B))
         for k in range(n)]
    return M.toDeg(B, W, pe, 0, M.modelSum(B, W, pe, L))


def gramDefectUp(B, W, i, j, u):
    if i == j:
        return M.oneSubSupUp(B, W, u)
    return B.upAdd(M.supNormUp(B, W, u.poly), u.rad)


def maxCandidate(B, L):
    acc = B.ofInt(0)
    for a in reversed(L):
        acc = acc if B.ble(a, acc) else a
    return acc


def gramBoundsOk(B, dRows, bRows, d, b, s):
    return (all(B.ble(r, d) for r in dRows) and all(B.ble(r, b) for r in bRows) and B.blt(d, B.ofInt(1))
            and B.ble(B.ofInt(0), d) and 0 <= s and B.ble(B.upAdd(b, B.upMul(B.ofRatUp(s), d)), B.ofRatDown(s)))


def gramCheck(B, n, K, Binv, W, cfg, pe, s, DKc, info=None):
    if not (len(Binv) == n and all(len(r) == n for r in Binv)):
        return None
    G = gramModels(B, n, K, W, cfg, pe, DKc)
    dRows = [M.sumUp(B, [gramDefectUp(B, W, i, j, gramBGModel(B, n, Binv, G, W, cfg, pe, i, j)) for j in range(n)])
             for i in range(n)]
    bRows = [M.sumUp(B, [M.supNormUp(B, W, gramInvPoly(Binv, i, j)) for j in range(n)]) for i in range(n)]
    d, b = maxCandidate(B, dRows), maxCandidate(B, bRows)
    if info is not None:
        info.update(dRows=[val(B, x) for x in dRows], bRows=[val(B, x) for x in bRows], G=G,
                    margin=F(s) - (val(B, b) + F(s) * val(B, d)))
    return (d, b) if gramBoundsOk(B, dRows, bRows, d, b, s) else None


# ---------------------------------------------------------------------------------------------- Torsion
def buildMat(r, c, f):
    return [[f(i, j) for j in range(c)] for i in range(r)]


def modelMatMul(B, W, cfg, pe, key, r, m, c, X, Y):
    return buildMat(r, c, lambda i, j: M.toDeg(B, W, pe, 0, M.modelSum(B, W, pe, [
        M.model_mul(B, W, cfg, tuple(key) + (i, j, k), entry(X, i, k, B), entry(Y, k, j, B)) for k in range(m)])))


def modelMatAdd(B, W, pe, r, c, X, Y):
    return buildMat(r, c, lambda i, j: M.addMixed(B, W, pe, entry(X, i, j, B), entry(Y, i, j, B)))


def modelMatNeg(B, r, c, X):
    return buildMat(r, c, lambda i, j: M.negM(B, entry(X, i, j, B)))


def modelMatTranspose(B, r, c, X):
    return buildMat(c, r, lambda i, j: entry(X, j, i, B))


def modelMatOmega(B, n, c, X):
    return buildMat(n + n, c, lambda i, j: M.negM(B, entry(X, n + i, j, B)) if i < n else entry(X, i - n, j, B))


def ballModel(B, n, c, r):
    cm = M.constModel(B, n, c, 0, 0)
    return M.Model(0, cm.poly, B.upAdd(cm.rad, B.ofRatUp(r)))


def boxGet(box, l):
    return box[l] if l < len(box) else (F(0), F(0))


def freqModel(B, n, box, s, l):
    c, r = boxGet(box, l)
    return ballModel(B, n, F(s) * F(c), abs(F(s)) * F(r))


def dkModels(B, n, DKc):
    return buildMat(n + n, n, lambda i, j: DKc[("a", i, j)] if i < n else DKc[("p", i - n, j)])


def d2kModel(B, n, K, W, pe, i, j, l):
    if i < n:
        return M.toDeg(B, W, pe, 0, M.ofDeriv2(B, W, j, l, M.getD(K.angleDeg, i), M.realCompPoly(B, n, K.angleAt(i))))
    return M.toDeg(B, W, pe, 0, M.ofDeriv2(B, W, j, l, M.getD(K.actionDeg, i - n),
                                           M.realCompPoly(B, n, K.actionAt(i - n))))


def dkwModels(B, n, K, box, s, W, cfg, pe):
    return buildMat(n + n, n, lambda i, j: M.toDeg(B, W, pe, 0, M.modelSum(B, W, pe, [
        M.model_mul(B, W, cfg, (4, 10, i, j, l), freqModel(B, n, box, s, l), d2kModel(B, n, K, W, pe, i, j, l))
        for l in range(n)])))


def gramInvRadius(B, db):
    d, b = db
    if B.ble(B.ofInt(0), d) and B.ble(B.ofInt(0), b) and B.blt(d, B.ofInt(1)):
        t = M.recipOneSubUp(B, d)
        return None if t is None else B.upMul(B.upMul(d, b), t)
    return None


def torsionSlots(n, J):
    m = n + n
    d1 = [M.getD(J["d1"], a) for a in range(m)]
    d2 = []
    for q in range(m * m):
        row = J["d2"][q // m] if q // m < len(J["d2"]) else []
        d2.append(row[q % m] if q % m < len(row) else 0)
    return d1 + d2


def swapNat(n, a):
    return a + n if a < n else a - n


def msGet(ms, i, B):
    return ms[i] if i < len(ms) else M.zeroModel(B)


def dxhModels(B, n, ms):
    m = n + n
    return buildMat(m, m, lambda a, b: msGet(ms, m + m * swapNat(n, a) + b, B) if a < n
                    else M.negM(B, msGet(ms, m + m * swapNat(n, a) + b, B)))


def torsionModels(B, n, J, K, wit, Binv, db, box, s, W, cfg, pe, DKc, info=None):
    eps = gramInvRadius(B, db)
    ms = M.compose(B, n, J["prog"], K, wit, W, cfg, pe, torsionSlots(n, J))
    if eps is None or ms is None:
        return None
    m = n + n
    L = dkModels(B, n, DKc)
    Gi = buildMat(n, n, lambda k, j: M.Model(0, gramInvPoly(Binv, k, j), eps))
    DL = dkwModels(B, n, K, box, s, W, cfg, pe)
    N = modelMatOmega(B, n, n, modelMatMul(B, W, cfg, pe, (4, 0), m, n, n, L, Gi))
    DG = modelMatAdd(B, W, pe, n, n,
                     modelMatMul(B, W, cfg, pe, (4, 1), n, m, n, modelMatTranspose(B, m, n, DL), L),
                     modelMatMul(B, W, cfg, pe, (4, 2), n, m, n, modelMatTranspose(B, m, n, L), DL))
    DGi = modelMatNeg(B, n, n, modelMatMul(B, W, cfg, pe, (4, 4), n, n, n,
                                           modelMatMul(B, W, cfg, pe, (4, 3), n, n, n, Gi, DG), Gi))
    DN = modelMatOmega(B, n, n, modelMatAdd(B, W, pe, m, n, modelMatMul(B, W, cfg, pe, (4, 5), m, n, n, DL, Gi),
                                            modelMatMul(B, W, cfg, pe, (4, 6), m, n, n, L, DGi)))
    XN = modelMatAdd(B, W, pe, m, n, modelMatMul(B, W, cfg, pe, (4, 7), m, m, n, dxhModels(B, n, ms), N),
                     modelMatNeg(B, m, n, DN))
    Tb = modelMatMul(B, W, cfg, pe, (4, 8), n, m, n, modelMatTranspose(B, m, n, N), modelMatOmega(B, n, n, XN))
    Y = modelMatMul(B, W, cfg, pe, (4, 9), 1, m, n, [[msGet(ms, a, B) for a in range(m)]], N)

    def T(i, j):
        if i < n:
            return entry(Tb, i, j, B) if j < n else freqModel(B, n, box, s, i)
        return entry(Y, 0, j, B) if j < n else M.zeroModel(B)
    return buildMat(n + 1, n + 1, T)


def isZeroKeyN(n, k):
    return all(M.getD(k, i) == 0 for i in range(n))


def zeroModeBall(B, n, m):
    return M.coeffSumBall(B, [t for t in m.poly if isZeroKeyN(n, t[0])])


def ccEntry(B, S, i, j):
    if i < len(S) and j < len(S[i]):
        return S[i][j]
    return (B.ofInt(0), B.ofInt(0))


def torsionAvgCheck(B, n, T, S, s, info=None):
    k = n + 1
    if not (len(T) == k and all(len(r) == k for r in T) and len(S) == k and all(len(r) == k for r in S)):
        return False
    if not all(entry(T, i, j, B).deg == 0 for i in range(k) for j in range(k)):
        return False
    zb = {(l, j): zeroModeBall(B, n, entry(T, l, j, B)) for l in range(k) for j in range(k)}
    z0 = B.ofInt(0)

    def defect(i, j):
        p = M.listSumBall(B, [A.ball_times(B, (ccEntry(B, S, i, l), z0), (zb[(l, j)][0], z0)) for l in range(k)])
        base = A.oneBall(B) if i == j else ((B.ofInt(0), B.ofInt(0)), B.ofInt(0))
        d = A.ball_plus(B, base, (M.negC(B, p[0]), p[1]))
        return B.upAdd(A.normUp(B, d[0]), d[1])
    dRows = [M.sumUp(B, [defect(i, j) for j in range(k)]) for i in range(k)]
    bRows = [M.sumUp(B, [A.normUp(B, ccEntry(B, S, i, j)) for j in range(k)]) for i in range(k)]
    rRows = [M.sumUp(B, [B.upAdd(zb[(i, j)][1], entry(T, i, j, B).rad) for j in range(k)]) for i in range(k)]
    a, b, r = maxCandidate(B, dRows), maxCandidate(B, bRows), maxCandidate(B, rRows)
    d = B.upAdd(a, B.upMul(b, r))
    if info is not None:
        info.update(a=val(B, a), b=val(B, b), r=val(B, r), deltaT=val(B, d),
                    margin=F(s) - (val(B, b) + F(s) * val(B, d)),
                    centre=[[(val(B, zb[(l, j)][0][0]), val(B, zb[(l, j)][0][1])) for j in range(k)] for l in range(k)])
    return (all(B.ble(x, a) for x in dRows) and all(B.ble(x, r) for x in rRows) and B.ble(B.ofInt(0), r)
            and gramBoundsOk(B, [d], bRows, d, b, s))


# ---------------------------------------------------------------------------------------------- Positivity
def conjSorted(B, P):
    return list(reversed(M.conjReflect(B, P)))


def ofConst(B, length, u, r):
    return M.Model(0, [((0,) * length, (u, B.ofInt(0)))], r)


def keyLen(P):
    return len(P[0][0]) if P else 0


def realLowerModel(B, W, cfg, f, m0, g):
    cfg2 = cfg.withExtra((7,), ("direct",))
    gg = M.model_mul(B, W, cfg2, (7,), M.Model(0, g, B.ofInt(0)), M.Model(0, conjSorted(B, g), B.ofInt(0)))
    G = M.model_mul(B, W, cfg2, (7,), gg, ofConst(B, keyLen(g), B.ofInt(-2), B.ofInt(0)))
    c = B.ofRatUp(-2 * F(m0))
    ln = keyLen(g) if not f.poly else keyLen(f.poly)
    star = M.Model(f.deg, conjSorted(B, f.poly), f.rad)
    return M.model_add(B, W, M.model_add(B, W, M.model_add(B, W, f, star), G),
                       ofConst(B, ln, c, B.upAdd(c, B.neg(B.ofRatDown(-2 * F(m0))))))


def checkRealLowerBound(B, W, cfg, f, m0, m, g, info=None, tag=None):
    if f.deg != 0:
        return False
    sb = M.supBound(B, W, realLowerModel(B, W, cfg, f, m0, g))
    rhs = B.ofRatDown(2 * (F(m0) - F(m)))
    if info is not None:
        info[tag] = dict(sup=val(B, sb), bound=val(B, rhs), margin=val(B, rhs) - val(B, sb))
    return B.ble(sb, rhs)


# ---------------------------------------------------------------------------------------------- Defs
def freqNormLo(box):
    acc = F(0)
    for c, r in reversed(box):
        acc = max(abs(F(c)) - F(r), acc)
    return acc


def slotMagQ(bs, i):
    if i < len(bs):
        (re, im), r = bs[i]
        return abs(re) + abs(im) + r
    return F(0)


def hamBoundsOk(m, J, bs, Mb, info=None):
    g = lambda L, a, d: L[a] if a < len(L) else d
    d1 = lambda a: slotMagQ(bs, g(J["d1"], a, 0))
    d2 = lambda a, b: slotMagQ(bs, g(g(J["d2"], a, []), b, 0))
    d3 = lambda a, b, e: slotMagQ(bs, g(g(g(J["d3"], a, []), b, []), e, 0))
    q = [sum(d1(a) for a in range(m)), max(d1(a) for a in range(m)),
         max(sum(d2(a, b) for b in range(m)) for a in range(m)),
         max(sum(d3(a, b, e) for b in range(m) for e in range(m)) for a in range(m)),
         sum(d2(a, b) for a in range(m) for b in range(m))]
    if info is not None:
        info.update(bounds=q, M=Mb, margin=Mb - max(q))
    return all(x <= Mb for x in q)


class Cert:
    """TorusCertificate n α (+ the SoGraphCert fields)."""
    pass


def checkStatic(B, c, info):
    p, n = c.params, c.n
    ok = (len(c.freqBox) == n and len(c.centre) == n and len(c.radius) == n and 2 <= n and n <= p["tau"] + 1
          and 0 < p["rhoInf"] < p["rho"] and 0 < p["M"] and 0 < p["sK"] and 0 < p["sB"] and 0 < p["sT"]
          and 0 < p["mu"] and 0 < p["gbar"] and 1 < p["som"] and 0 < p["nu"] and 1 < p["s"] < p["som"]
          and 0 < p["gamma"] <= p["gbar"] and 0 <= p["err"] and c.weight.rho == p["rho"])
    wt = M.checkWeight(c.weight, c.expHalvings, c.expOrder)
    wH = M.checkWeight(c.weightH, c.expHalvings, c.expOrder)
    pi = A.checkPiEnclosure(B, c.piEnc)
    L = freqNormLo(c.freqBox)
    rays = 0 < L and p["nu"] <= (p["s"] - 1) * L and p["nu"] <= (p["som"] - p["s"]) * L
    info.update(params=ok, weight=wt, weightH=wH, pi=pi, L=L, rays=rays,
                ray_margin=min((p["s"] - 1) * L, (p["som"] - p["s"]) * L) - p["nu"],
                weight_margin=c.weight.w - M.ratExpUp(2 * A.PI_UP * c.weight.rho, c.expHalvings, c.expOrder),
                weightH_margin=c.weightH.w - M.ratExpUp(2 * A.PI_UP * c.weightH.rho, c.expHalvings, c.expOrder))
    return ok and wt and wH and pi and rays


def checkHamBounds(B, c, info):
    bs = TA.slp_balls(c.n, c.jetOps_toy, c.weightH.w, c.centre, c.radius, c.expOrder)
    if bs is None:
        info.update(balls=None)
        return False
    return hamBoundsOk(2 * c.n, c.jet, bs, c.params["M"], info)


def checkEmbedding(B, c, info):
    n, p, W, pe, K = c.n, c.params, c.weight, c.piEnc, c.emb
    room = c.weightH.rho - p["rho"] - p["mu"]
    ok1, iota = True, []
    for i in range(n):
        s1 = M.supBound(B, W, M.realCompModel(B, n, M.getD(K.angleDeg, i), K.angleAt(i)))
        a1 = B.ble(s1, B.ofRatDown(room))
        s2 = B.upMul(B.ofRatUp(p["rho"]), M.sumUp(B, [M.supBound(B, W, compDerivModel(
            B, n, W, pe, M.getD(K.angleDeg, i), K.angleAt(i), j)) for j in range(n)]))
        a2 = B.ble(s2, B.ofRatDown(room))
        iota.append((val(B, s1), val(B, s2)))
        ok1 = ok1 and (a1 or a2)
    ok2, act = True, []
    for i in range(n):
        m = M.addMixed(B, W, pe, M.realCompModel(B, n, M.getD(K.actionDeg, i), K.actionAt(i)),
                       M.constModel(B, n, -F(c.centre[i] if i < len(c.centre) else 0), 0, 0))
        sb = M.supBound(B, W, m)
        rr = F(c.radius[i] if i < len(c.radius) else 0) - p["mu"]
        act.append((val(B, sb), rr))
        ok2 = ok2 and B.ble(sb, B.ofRatDown(rr))
    DKm = dkModels(B, n, c.DKc)
    rows = [M.sumUp(B, [M.supBound(B, W, entry(DKm, r, j, B)) for j in range(n)]) for r in range(n + n)]
    ok3 = all(B.ble(x, B.ofRatDown(p["sK"] - p["mu"])) for x in rows)
    info.update(room=room, iota=iota, action=act, dkRows=[val(B, x) for x in rows],
                dk_margin=p["sK"] - p["mu"] - max(val(B, x) for x in rows),
                iota_margin=room - max(min(a, b) for a, b in iota),
                action_margin=min(r - s for s, r in act))
    return ok1 and ok2 and ok3


def dkFreqModel(B, n, DKm, box, s, W, cfg, pe, a):
    return M.toDeg(B, W, pe, 0, M.modelSum(B, W, pe, [
        M.model_mul(B, W, cfg, (5, a, l), freqModel(B, n, box, s, l), entry(DKm, a, l, B)) for l in range(n)]))


def checkInvariance(B, c, info):
    n, W, pe = c.n, c.weight, c.piEnc
    cinfo = {}
    ms = M.compose(B, n, c.jetOps, c.emb, c.wit, W, c.cfgFull, pe, [M.getD(c.jet["d1"], a) for a in range(n + n)],
                   cinfo)
    info["compose"] = cinfo
    if ms is None:
        return False
    DKm = dkModels(B, n, c.DKc)
    sups = []
    for a in range(n + n):
        x = msGet(ms, swapNat(n, a), B)
        lhs = x if a < n else M.negM(B, x)
        m = M.addMixed(B, W, pe, lhs, M.negM(B, dkFreqModel(B, n, DKm, c.freqBox, c.params["s"], W, c.cfgFull, pe, a)))
        sups.append(M.supBound(B, W, m))
    e = B.ofRatDown(c.params["err"])
    info.update(rows=[val(B, x) for x in sups], err=c.params["err"],
                margin=c.params["err"] - max(val(B, x) for x in sups))
    return all(B.ble(x, e) for x in sups)


def checkEnergy(B, c, info):
    n, W, pe = c.n, c.weight, c.piEnc
    ms = M.compose(B, n, c.jetOps, c.emb, c.wit, W, c.cfgFull, pe, [c.jet["v0"]])
    if ms is None or len(ms) != 1:
        return False
    d = M.addMixed(B, W, pe, M.toDeg(B, W, pe, 0, ms[0]), M.constModel(B, n, -F(c.params["E0"]), 0, 0))
    if d.deg != 0:
        return False
    z = zeroModeBall(B, n, d)
    lhs = B.upAdd(B.upAdd(A.normUp(B, z[0]), z[1]), d.rad)
    info.update(value=val(B, lhs), err=c.params["err"], margin=c.params["err"] - val(B, lhs))
    return B.ble(lhs, B.ofRatDown(c.params["err"]))


def checkGram(B, c, info):
    p = c.params
    r = gramCheck(B, c.n, c.emb, c.gramInv, c.weight, c.cfgLow, c.piEnc, p["sB"] - p["mu"], c.DKc, info)
    c._gram = r
    return r is not None


def checkTorsion(B, c, info):
    p = c.params
    db = c._gram if hasattr(c, "_gram") else gramCheck(B, c.n, c.emb, c.gramInv, c.weight, c.cfgLow, c.piEnc,
                                                       p["sB"] - p["mu"], c.DKc)
    if db is None:
        return False
    T = torsionModels(B, c.n, c.jet, c.emb, c.wit, c.gramInv, db, c.freqBox, p["s"], c.weight, c.cfgLow, c.piEnc,
                      c.DKc)
    if T is None:
        info.update(models=None)
        return False
    c._T = T
    return torsionAvgCheck(B, c.n, T, c.torsInv, p["sT"] - p["mu"], info)


def checkSmallness(B, c, info):
    p, n = c.params, c.n
    c1 = TC.isoC1Q(n, p["tau"], p["rho"], p["rhoInf"], p["M"], p["sK"], p["sB"], p["sT"], p["mu"], p["nu"], p["gbar"])
    c2 = TC.isoC2Q(n, p["tau"], p["rho"], p["rhoInf"], p["M"], p["sK"], p["sB"], p["sT"])
    lhs1, rhs1 = c1 * p["err"], p["gamma"] ** 4 * p["rho"] ** (4 * p["tau"])
    lhs2, rhs2 = c2 * p["err"], p["disp"] * (p["gamma"] ** 2 * p["rho"] ** (2 * p["tau"]))
    info.update(C1_ratio=lhs1 / rhs1, C2_ratio=lhs2 / rhs2 if rhs2 else None)
    return lhs1 < rhs1 and lhs2 <= rhs2


SUBCHECKS = [("checkStatic", checkStatic), ("checkHamBounds", checkHamBounds), ("checkEmbedding", checkEmbedding),
             ("checkInvariance", checkInvariance), ("checkEnergy", checkEnergy), ("checkGram", checkGram),
             ("checkTorsion", checkTorsion), ("checkSmallness", checkSmallness)]


# ---------------------------------------------------------------------------------------------- graph
def soGraphMonoModel(B, c):
    return M.toDeg(B, c.weight, c.piEnc, 0, entry(dkModels(B, c.n, c.DKc), 0, 0, B))


def soGraphActionModel(B, c):
    return M.toDeg(B, c.weight, c.piEnc, 0,
                   M.realCompModel(B, c.n, M.getD(c.emb.actionDeg, 0), c.emb.actionAt(0)))


def checkSoGraph(B, c, info):
    g = c.graph
    p = c.params
    ok0 = p["disp"] < g["mono"] * p["rhoInf"]
    info["strict"] = dict(disp=p["disp"], mono_rhoInf=g["mono"] * p["rhoInf"])
    fm = soGraphMonoModel(B, c)
    fa = soGraphActionModel(B, c)
    ok1 = checkRealLowerBound(B, c.weight, c.cfgLow, fm, g["mono0"], g["mono"], g["sosMono"], info, "mono")
    ok2 = checkRealLowerBound(B, c.weight, c.cfgLow, fa, g["pLo0"], g["pLo"], g["sosLo"], info, "pLo")
    ok3 = checkRealLowerBound(B, c.weight, c.cfgLow, M.negM(B, fa), -g["pHi0"], -g["pHi"], g["sosHi"], info, "pHi")
    return ok0 and ok1 and ok2 and ok3
