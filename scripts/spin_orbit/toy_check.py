#!/usr/bin/env python3
"""Python mirror of `checkTorusCertificate` (KAM/Certificate/Defs.lean) for ℚ certificates, direct route.

Untrusted tooling (SO-TOYGEN, aligned with the landed Lean by SO-PYALIGN).  Every function transcribes the Lean
declaration of the same (snake-cased where needed) name over the exact backend ℚ, using the model engine of
toy_model.py: `Slp.compose` over the WHOLE program in slot order with the Lean witness numbering and advice
keys, `gramCheck`, `torsionModels`, `torsionAvgCheck`, and the eight sub-checks of Defs.lean.  The alignment
table is docs/tracks/SO/studies/SO-PYALIGN.md.  Two shape tests of `checkStatic` are DELIBERATELY STRICTER than
Lean (box radii >= 0, embedding list lengths = n); they are reported separately (`mirrorOnly`).

A certificate is a dict (see toy_gen.py); every number is a Fraction, every polynomial a Lean-ordered term
list.  `check(cert)` returns (ok, report) where report[sub] = (ok, details) in checker order.
"""
from fractions import Fraction as F
import toy_arith as A
import toy_model as Mo
from toy_model import Model, getD
import toy_constants as C

SUBS = ["checkStatic", "checkHamBounds", "checkEmbedding", "checkInvariance", "checkEnergy", "checkGram",
        "checkTorsion", "checkSmallness"]


def swapNat(n, a):
    return a + n if a < n else a - n


def opt(L, i):
    """`L[i]?`"""
    return L[i] if i < len(L) else None


# ---------------------------------------------------------------- embedding (Gram.lean, Torsion/Models.lean)
def compDerivModel(c, d, Pr, j):
    n, w, pe = c["n"], c["weight"][1], c["piEnc"]
    return Mo.toDeg(w, pe, 0, Mo.ofDeriv(j, d, Mo.realCompPoly(n, Pr)), c["_log"])


def dkAngleModel(c, i, j):
    e = c["emb"]
    m = compDerivModel(c, getD(e["angleDeg"], i), opt(e["angle"], i), j)
    return Mo.add(Mo.constModel(c["n"], 1, 0, 0), m) if i == j else m


def dkActionModel(c, i, j):
    e = c["emb"]
    return compDerivModel(c, getD(e["actionDeg"], i), opt(e["action"], i), j)


def dkModels(c):
    if "_dk" not in c:
        n = c["n"]
        c["_dk"] = [[dkAngleModel(c, i, j) if i < n else dkActionModel(c, i - n, j) for j in range(n)]
                    for i in range(2 * n)]
    return c["_dk"]


def entry(M, i, j):
    """modelMatrixEntry (zeroModel off the list)."""
    if i < len(M) and j < len(M[i]):
        return M[i][j]
    return Mo.zeroModel()


def d2kModel(c, i, j, l):
    n, w, pe, e = c["n"], c["weight"][1], c["piEnc"], c["emb"]
    if i < n:
        m = Mo.ofDeriv2(j, l, getD(e["angleDeg"], i), Mo.realCompPoly(n, opt(e["angle"], i)))
    else:
        m = Mo.ofDeriv2(j, l, getD(e["actionDeg"], i - n), Mo.realCompPoly(n, opt(e["action"], i - n)))
    return Mo.toDeg(w, pe, 0, m, c["_log"])


def ballModel(n, cc, r):
    return Model(0, Mo.constModel(n, cc, 0, 0).poly, F(r))


def freqModel(c, l):
    s, box = c["params"]["s"], c["freqBox"]
    cc, r = box[l] if l < len(box) else (F(0), F(0))
    return ballModel(c["n"], s * cc, abs(s) * r)


# ---------------------------------------------------------------- composition (Expr/Compose.lean)
def angleIsZero(c, j):
    P = opt(c["emb"]["angle"], j)
    return P is None or Mo.isZeroData(P)


def normKey(c, k):
    return tuple(0 if angleIsZero(c, j) else getD(k, j) for j in range(c["n"]))


def charPhaseModel(c, k):
    n, w, pe, e = c["n"], c["weight"][1], c["piEnc"], c["emb"]
    acc = Mo.zeroModel()
    for j in range(n):
        m = getD(k, j)
        if m == 0:
            continue
        P = opt(e["angle"], j)
        if P is None:
            ph = Mo.zeroModel()
        else:
            ph = Model(getD(e["angleDeg"], j) + 1,
                       [(kk, (-x[1] * m, x[0] * m)) for kk, x in Mo.toSortedPoly(n, P)], F(0))
        acc = Mo.add(acc, Mo.toDeg(w, pe, 0, ph, c["_log"]))
    return acc


def findKeyIdx(k, L):
    for i, (kk, v) in enumerate(L):
        if tuple(kk) == tuple(k):
            return i, v
    return None


def charResolve(c, cfg, cache, kk, info):
    hit = findKeyIdx(kk, cache)
    if hit is not None:
        return hit[1], cache
    hit = findKeyIdx(kk, c["wit"]["charWit"])
    if hit is None:
        return None
    ci, Ew = hit
    r = Mo.expWitnessRadius(c["n"], c["weight"][1], c["weight"][0],
                            cfg.forWitness(1, len(c["wit"]["expWit"]) + ci), charPhaseModel(c, kk), Ew)
    info["char"].append((kk, ci, r))
    if r is None:
        return None
    return (Ew[0], r), [(kk, (Ew[0], r))] + cache


def charEntry(c, cfg, cache, kk, info):
    e = charResolve(c, cfg, cache, kk, info)
    if e is not None:
        return e
    nk = tuple(-x for x in kk)
    e = charResolve(c, cfg, cache, nk, info)
    if e is None:
        return None
    (P, r), cache2 = e
    R = Mo.reflectSorted(P)
    return (R, r), [(kk, (R, r))] + cache2


def compose(c, cfg, wanted):
    """Slp.compose: every op of the program in order (fail closed), then the wanted slots (zeroModel off the
    program).  Returns (models or None, info)."""
    n, w, rho, pe = c["n"], c["weight"][1], c["weight"][0], c["piEnc"]
    e, wit, log = c["emb"], c["wit"], c["_log"]
    slots, norms, nExp, nInv, cache = [], [], 0, 0, []
    info = {"inv": [], "char": [], "exp": []}

    def slot(i):
        if i < len(slots):
            return slots[i], norms[i]
        return Mo.zeroModel(), F(0)

    def push(m):
        slots.append(m)
        norms.append(Mo.supNormUp(m.poly, w))

    for op in c["_ops"]:
        t = op[0]
        if t == "C":
            push(Mo.constModel(n, op[1], op[2], op[3]))
        elif t == "A":
            j = op[1]
            push(Mo.realCompModel(n, getD(e["actionDeg"], j), opt(e["action"], j)) if j < n else Mo.zeroModel())
        elif t == "X":
            k = tuple(op[1])
            ent = charEntry(c, cfg, cache, normKey(c, k), info)
            if ent is None:
                return None, dict(info, fail="character slot %d: no witness or check failed (key %s)"
                                  % (len(slots), normKey(c, k)))
            (P, r), cache = ent
            pk = Mo.padKey(n, k)
            push(Model(0, Mo.shift(pk, P), Mo.weightTermUp(w, pk, r)))
        elif t == "+":
            a = slot(op[1])[0]
            push(Mo.add(a, Mo.toDeg(w, pe, a.deg, slot(op[2])[0], log)))
        elif t == "*":
            (a, na), (b, nb) = slot(op[1]), slot(op[2])
            push(Mo.mulN(w, cfg, (0, len(slots)), a, na, b, nb))
        elif t == "E":
            if nExp >= len(wit["expWit"]):
                return None, dict(info, fail="missing exp witness %d" % nExp)
            Ew = wit["expWit"][nExp]
            r = Mo.expWitnessRadius(n, w, rho, cfg.forWitness(1, nExp), Mo.toDeg(w, pe, 0, slot(op[1])[0], log), Ew)
            info["exp"].append((len(slots), nExp, r))
            if r is None:
                return None, dict(info, fail="exp witness %d rejected" % nExp)
            push(Model(0, Ew[0], r))
            nExp += 1
        elif t == "I":
            if nInv >= len(wit["invWit"]):
                return None, dict(info, fail="missing reciprocal witness %d" % nInv)
            Q = wit["invWit"][nInv]
            b = slot(op[1])[0]
            r, delta = Mo.invWitnessRadius(n, w, cfg.forWitness(2, nInv), b, Q)
            info["inv"].append((len(slots), delta, r))
            if r is None:
                return None, dict(info, fail="reciprocal witness %d: delta = %s" % (nInv, float(delta)))
            push(Model(-b.deg, Q, r))
            nInv += 1
        else:
            raise ValueError(op)
    return [slot(i)[0] for i in wanted], info


# ---------------------------------------------------------------- sub-checks (Defs.lean)
def freqNormLo(box):
    acc = F(0)
    for cc, r in reversed(box):
        acc = max(abs(cc) - r, acc)
    return acc


def check_static(c):
    p, n, box = c["params"], c["n"], c["freqBox"]
    L = freqNormLo(box)
    conds = {
        "box.length=n": len(box) == n, "centre.length=n": len(c["centre"]) == n,
        "radius.length=n": len(c["radius"]) == n, "2<=n": 2 <= n, "n<=tau+1": n <= p["tau"] + 1,
        "0<rhoInf": 0 < p["rhoInf"], "rhoInf<rho": p["rhoInf"] < p["rho"], "0<M": 0 < p["M"],
        "0<sK": 0 < p["sK"], "0<sB": 0 < p["sB"], "0<sT": 0 < p["sT"], "0<mu": 0 < p["mu"],
        "0<gbar": 0 < p["gbar"], "1<sigma_omega": 1 < p["sigma_omega"], "0<nuRay": 0 < p["nuRay"],
        "1<s": 1 < p["s"], "s<sigma_omega": p["s"] < p["sigma_omega"], "0<gamma": 0 < p["gamma"],
        "gamma<=gbar": p["gamma"] <= p["gbar"], "0<=err": 0 <= p["err"],
        "weight.rho=rho": c["weight"][0] == p["rho"],
        "checkWeight(weight)": A.checkWeight(c["weight"][0], c["weight"][1], c["expHalvings"], c["expOrder"]),
        "checkWeight(weightH)": A.checkWeight(c["weightH"][0], c["weightH"][1], c["expHalvings"], c["expOrder"]),
        "checkPiEnclosure": A.checkPiEnclosure(*c["piEnc"]),
        "0<freqNormLo": 0 < L,
        "nu<=(s-1)L": p["nuRay"] <= (p["s"] - 1) * L,
        "nu<=(sigma_omega-s)L": p["nuRay"] <= (p["sigma_omega"] - p["s"]) * L,
    }
    mirror_only = {     # deliberately stricter than Lean (not in checkStatic)
        "box radii>=0": all(r >= 0 for _, r in box),
        "emb lengths n": all(len(c["emb"][k]) == n for k in ("angle", "angleDeg", "action", "actionDeg")),
    }
    ok = all(conds.values()) and all(mirror_only.values())
    return ok, dict(conds=conds, mirrorOnly=mirror_only, lean=all(conds.values()), normLower=L)


def ball_bounds(c):
    """Slp.balls at the certificate's expOrder, then the five hamBoundsOk quantities (getD defaults)."""
    n, jet = c["n"], c["_jet"]
    bs = A.slp_balls(n, c["_ops"], c["weightH"][1], c["centre"], c["radius"], c["expOrder"])
    if bs is None:
        return None, None
    BZ = A.BALL_ZERO
    mag = lambda i: (lambda b: abs(b[0][0]) + abs(b[0][1]) + b[1])(bs[i] if i < len(bs) else BZ)
    d1, d2, d3 = jet["d1"], jet["d2"], jet["d3"]
    m = 2 * n
    s1 = lambda a: getD(d1, a)
    s2 = lambda a, b: getD(d2[a] if a < len(d2) else [], b)
    s3 = lambda a, b, e: getD((d3[a][b] if b < len(d3[a]) else []) if a < len(d3) else [], e)
    sm = lambda f: Mo.sumUp(f(a) for a in range(m))
    b = {"DH": sm(lambda a: mag(s1(a))),
         "X_H": max(mag(s1(a)) for a in range(m)),
         "DX_H": max(sm(lambda bb: mag(s2(a, bb))) for a in range(m)),
         "D2X_H": max(sm(lambda bb: sm(lambda e: mag(s3(a, bb, e)))) for a in range(m)),
         "D2H": sm(lambda a: sm(lambda bb: mag(s2(a, bb))))}
    return b, bs


def check_ham_bounds(c):
    b, bs = ball_bounds(c)
    if b is None:
        return False, dict(balls=None, fail="Slp.balls = none (a denominator ball contains 0)")
    M = c["params"]["M"]
    return all(v <= M for v in b.values()), dict(bounds=b, M=M, maxBound=max(b.values()), nslots=len(bs))


def check_embedding(c):
    n, p, w, pe, e = c["n"], c["params"], c["weight"][1], c["piEnc"], c["emb"]
    room = c["weightH"][0] - p["rho"] - p["mu"]
    angle_ok, iotas = True, []
    for i in range(n):
        d, P = getD(e["angleDeg"], i), opt(e["angle"], i)
        supU = Mo.supBound(Mo.realCompModel(n, d, P), w)
        supDU = p["rho"] * Mo.sumUp(Mo.supBound(compDerivModel(c, d, P, j), w) for j in range(n))
        iotas.append(min(supU, supDU))
        angle_ok = angle_ok and (supU <= room or supDU <= room)
    act_ok, dists = True, []
    for i in range(n):
        m = Mo.addMixed(w, pe, Mo.realCompModel(n, getD(e["actionDeg"], i), opt(e["action"], i)),
                        Mo.constModel(n, -getD(c["centre"], i), 0, 0), c["_log"])
        dist = Mo.supBound(m, w)
        dists.append(dist)
        act_ok = act_ok and dist <= getD(c["radius"], i) - p["mu"]
    DK = dkModels(c)
    rowsums = [Mo.sumUp(Mo.supBound(entry(DK, r, j), w) for j in range(n)) for r in range(2 * n)]
    dk_ok = all(r <= p["sK"] - p["mu"] for r in rowsums)
    return angle_ok and act_ok and dk_ok, dict(iota=iotas, actionDist=dists, DKnorm=max(rowsums),
                                                angle_ok=angle_ok, action_ok=act_ok, DK_ok=dk_ok)


def dkFreqModel(c, cfg, a):
    n, w, pe = c["n"], c["weight"][1], c["piEnc"]
    DK = dkModels(c)
    return Mo.toDeg(w, pe, 0, Mo.modelSum(w, pe, [Mo.mul(w, cfg, (5, a, l), freqModel(c, l), entry(DK, a, l))
                                                  for l in range(n)], c["_log"]), c["_log"])


def check_invariance(c):
    n, p, w, pe = c["n"], c["params"], c["weight"][1], c["piEnc"]
    cfg = c["_cfgFull"]
    jet = c["_jet"]
    ms, info = compose(c, cfg, [getD(jet["d1"], a) for a in range(2 * n)])
    if ms is None:
        return False, dict(fail=info.get("fail"))
    comps = []
    for a in range(2 * n):
        x = getD(ms, swapNat(n, a)) if swapNat(n, a) < len(ms) else Mo.zeroModel()
        xa = x if a < n else Mo.negM(x)
        comps.append(Mo.supBound(Mo.addMixed(w, pe, xa, Mo.negM(dkFreqModel(c, cfg, a)), c["_log"]), w))
    e = max(comps)
    return all(x <= p["err"] for x in comps), dict(components=comps, bound=e, err=p["err"], info=info)


def zeroModeBall(n, m):
    return Mo.coeffSumBall([t for t in m.poly if Mo.isZeroKeyN(n, t[0])])


def check_energy(c):
    n, p, w, pe = c["n"], c["params"], c["weight"][1], c["piEnc"]
    ms, info = compose(c, c["_cfgFull"], [c["_jet"]["v0"]])
    if ms is None or len(ms) != 1:
        return False, dict(fail=info.get("fail"))
    d = Mo.addMixed(w, pe, Mo.toDeg(w, pe, 0, ms[0], c["_log"]), Mo.constModel(n, -p["E0"], 0, 0), c["_log"])
    z = zeroModeBall(n, d)
    bound = (Mo.normUp(z[0]) + z[1]) + d.rad
    return d.deg == 0 and bound <= p["err"], dict(average=z[0], radius=d.rad, bound=bound, err=p["err"])


# ---------------------------------------------------------------- Gram (Gram.lean)
def gramModels(c, cfg):
    n, w, pe = c["n"], c["weight"][1], c["piEnc"]

    def ent(a, b):
        L = [Mo.mul(w, cfg, (3, 0, a, b, k), dkAngleModel(c, k, a), dkAngleModel(c, k, b)) for k in range(n)]
        L += [Mo.mul(w, cfg, (3, 0, a, b, n + k), dkActionModel(c, k, a), dkActionModel(c, k, b))
              for k in range(n)]
        return Mo.modelSum(w, pe, L, c["_log"])
    return [[ent(a, b) if a <= b else ent(b, a) for b in range(n)] for a in range(n)]


def gramInvPoly(B, i, k):
    return B[i][k] if i < len(B) and k < len(B[i]) else []


def maxCandidate(L):
    acc = F(0)
    for a in reversed(L):
        acc = acc if a <= acc else a
    return acc


def gram_check(c):
    """gramCheck: ((δ, β) or None, details)."""
    n, p, w, pe = c["n"], c["params"], c["weight"][1], c["piEnc"]
    cfg = c["_cfgLow"]
    B = c["gramInv"]
    sBmu = p["sB"] - p["mu"]
    if not (len(B) == n and all(len(r) == n for r in B)):
        return None, dict(fail="gramInv shape")
    G = gramModels(c, cfg)

    def bg(i, j):
        return Mo.toDeg(w, pe, 0, Mo.modelSum(w, pe, [Mo.mul(w, cfg, (3, 1, i, j, k), Model(0, gramInvPoly(B, i, k)),
                                                            entry(G, k, j)) for k in range(n)], c["_log"]), c["_log"])

    def defect(i, j, u):
        return Mo.oneSubSupUp(w, u) if i == j else Mo.supNormUp(u.poly, w) + u.rad
    dRows = [Mo.sumUp(defect(i, j, bg(i, j)) for j in range(n)) for i in range(n)]
    bRows = [Mo.sumUp(Mo.supNormUp(gramInvPoly(B, i, j), w) for j in range(n)) for i in range(n)]
    delta, beta = maxCandidate(dRows), maxCandidate(bRows)
    det = dict(delta=delta, beta=beta, G=G)
    if not gramBoundsOk(dRows, bRows, delta, beta, sBmu):
        return None, dict(det, fail="gramBoundsOk")
    return (delta, beta), det


def gramBoundsOk(dRows, bRows, d, b, sig):
    return (all(r <= d for r in dRows) and all(r <= b for r in bRows) and d < 1 and 0 <= d and 0 <= sig
            and b + sig * d <= sig)


def check_gram(c):
    db, det = gram_check(c)
    return db is not None, {k: v for k, v in det.items() if k != "G"}


# ---------------------------------------------------------------- torsion (Torsion/Models.lean, Average.lean)
def matMul(c, cfg, key, r, m, cc, X, Y):
    w, pe, log = c["weight"][1], c["piEnc"], c["_log"]
    return [[Mo.toDeg(w, pe, 0, Mo.modelSum(w, pe, [Mo.mul(w, cfg, tuple(key) + (i, j, k), entry(X, i, k), entry(Y, k, j))
                                                    for k in range(m)], log), log)
             for j in range(cc)] for i in range(r)]


def matAdd(c, r, cc, X, Y):
    return [[Mo.addMixed(c["weight"][1], c["piEnc"], entry(X, i, j), entry(Y, i, j), c["_log"]) for j in range(cc)]
            for i in range(r)]


def matNeg(r, cc, X):
    return [[Mo.negM(entry(X, i, j)) for j in range(cc)] for i in range(r)]


def matT(r, cc, X):
    return [[entry(X, j, i) for j in range(r)] for i in range(cc)]


def matOmega(n, cc, X):
    return [[Mo.negM(entry(X, n + i, j)) if i < n else entry(X, i - n, j) for j in range(cc)]
            for i in range(2 * n)]


def gramInvRadius(db):
    d, b = db
    if 0 <= d and 0 <= b and d < 1:
        t = Mo.recipOneSubUp(d)
        return None if t is None else d * b * t
    return None


def torsionSlots(n, jet):
    m = 2 * n
    d2 = jet["d2"]
    return [getD(jet["d1"], a) for a in range(m)] + \
        [getD(d2[q // m] if q // m < len(d2) else [], q % m) for q in range(m * m)]


def torsion_models(c, db):
    n, w, pe, log = c["n"], c["weight"][1], c["piEnc"], c["_log"]
    cfg = c["_cfgLow"]
    jet = c["_jet"]
    eps = gramInvRadius(db)
    ms, info = compose(c, cfg, torsionSlots(n, jet))
    if eps is None:
        return None, dict(info, fail="gramInvRadius")
    if ms is None:
        return None, info
    m2 = 2 * n
    L = dkModels(c)
    Gi = [[Model(0, gramInvPoly(c["gramInv"], k, j), eps) for j in range(n)] for k in range(n)]
    DL = [[Mo.toDeg(w, pe, 0, Mo.modelSum(w, pe, [Mo.mul(w, cfg, (4, 10, i, j, l), freqModel(c, l), d2kModel(c, i, j, l))
                                                  for l in range(n)], log), log) for j in range(n)] for i in range(m2)]
    N = matOmega(n, n, matMul(c, cfg, (4, 0), m2, n, n, L, Gi))
    DG = matAdd(c, n, n, matMul(c, cfg, (4, 1), n, m2, n, matT(m2, n, DL), L),
                matMul(c, cfg, (4, 2), n, m2, n, matT(m2, n, L), DL))
    DGi = matNeg(n, n, matMul(c, cfg, (4, 4), n, n, n, matMul(c, cfg, (4, 3), n, n, n, Gi, DG), Gi))
    DN = matOmega(n, n, matAdd(c, m2, n, matMul(c, cfg, (4, 5), m2, n, n, DL, Gi),
                               matMul(c, cfg, (4, 6), m2, n, n, L, DGi)))
    msg = lambda i: ms[i] if i < len(ms) else Mo.zeroModel()
    DXH = [[(msg(m2 + m2 * swapNat(n, a) + b) if a < n else Mo.negM(msg(m2 + m2 * swapNat(n, a) + b)))
            for b in range(m2)] for a in range(m2)]
    XN = matAdd(c, m2, n, matMul(c, cfg, (4, 7), m2, m2, n, DXH, N), matNeg(m2, n, DN))
    Tb = matMul(c, cfg, (4, 8), n, m2, n, matT(m2, n, N), matOmega(n, n, XN))
    Y = matMul(c, cfg, (4, 9), 1, m2, n, [[msg(a) for a in range(m2)]], N)
    rows = [[(entry(Tb, i, j) if j < n else freqModel(c, i)) if i < n else
             (entry(Y, 0, j) if j < n else Mo.zeroModel()) for j in range(n + 1)] for i in range(n + 1)]
    return rows, info


def ccEntry(S, i, j):
    return S[i][j] if i < len(S) and j < len(S[i]) else (F(0), F(0))


def torsion_avg_check(c, T, S, sig):
    n = c["n"]
    k = n + 1
    shape = lambda M: len(M) == k and all(len(r) == k for r in M)
    if not (shape(T) and shape(S)):
        return False, dict(fail="shape (F7)")
    if not all(entry(T, i, j).deg == 0 for i in range(k) for j in range(k)):
        return False, dict(fail="avgDegOk: an entry of nonzero degree")
    Cm = [[zeroModeBall(n, entry(T, l, j))[0] for j in range(k)] for l in range(k)]
    Rm = [[zeroModeBall(n, entry(T, l, j))[1] + entry(T, l, j).rad for j in range(k)] for l in range(k)]

    def defect(i, j):
        p = Mo.listSumBall([A.b_times((ccEntry(S, i, l), F(0)), (Cm[l][j], F(0))) for l in range(k)])
        d = A.b_plus(A.b_one() if i == j else ((F(0), F(0)), F(0)), (Mo.neg(p[0]), p[1]))
        return Mo.normUp(d[0]) + d[1]
    dRows = [Mo.sumUp(defect(i, j) for j in range(k)) for i in range(k)]
    bRows = [Mo.sumUp(Mo.normUp(ccEntry(S, i, j)) for j in range(k)) for i in range(k)]
    rRows = [Mo.sumUp(Rm[i][j] for j in range(k)) for i in range(k)]
    a, b, r = maxCandidate(dRows), maxCandidate(bRows), maxCandidate(rRows)
    dT = a + b * r
    ok = (all(x <= a for x in dRows) and all(x <= r for x in rRows) and 0 <= r
          and gramBoundsOk([dT], bRows, dT, b, sig))
    return ok, dict(deltaT=dT, normISC=a, normS=b, normR=r, normInvBound=(b / (1 - dT) if dT < 1 else None),
                    bound=sig, centre=Cm, radius=Rm)


def check_torsion(c):
    db, det = gram_check(c)
    if db is None:
        return False, dict(fail="gram")
    T, info = torsion_models(c, db)
    if T is None:
        return False, dict(fail=info.get("fail"))
    p = c["params"]
    return torsion_avg_check(c, T, c["torsInv"], p["sT"] - p["mu"])


def check_smallness(c):
    p = dict(c["params"])
    p["n"] = c["n"]
    return C.smallness(p)


def prepare(c, books=None):
    """books: None (GENERATE: record every lookup) or {"cfgFull": keys, "cfgLow": keys} (CHECK)."""
    c["_ops"] = A.parse_ops(c["_jet"]["ops"])
    c["_log"] = []
    c.pop("_dk", None)
    for nm in ("cfgFull", "cfgLow"):
        cf = c[nm]
        c["_" + nm] = Mo.Cfg(nm, cf["cutoff"], cf["taylorN"], cf["halvings"],
                             None if books is None else books[nm])
    return c


def check(c, only=None, books=None):
    prepare(c, books)
    fns = dict(checkStatic=check_static, checkHamBounds=check_ham_bounds, checkEmbedding=check_embedding,
               checkInvariance=check_invariance, checkEnergy=check_energy, checkGram=check_gram,
               checkTorsion=check_torsion, checkSmallness=check_smallness)
    rep = {}
    for s in SUBS:
        if only and s not in only:
            continue
        rep[s] = fns[s](c)
    return all(r[0] for r in rep.values()), rep
