#!/usr/bin/env python3
"""Python mirror of `checkTorusCertificate` (A-E §G) for ℚ certificates on the `direct` product route.

Untrusted tooling (SO-TOYGEN).  The eight sub-check bodies are still `sorry` in the signatures; this module
implements them from their docstrings, design §1 decisions 2, 3, 7, 8, 9, 10 and the contracts of A-E §G,
over the exact backend ℚ.  Where a reading had to be chosen it is marked READING; every one is listed in
docs/tracks/SO/studies/SO-TOYGEN.md §4.  The landed parts (`Slp.balls`, `checkWeight`, `checkPiEnclosure`,
`HamExpr.jet` via the extracted program) are mirrored literally (toy_arith.py).

A certificate is a dict (see toy_gen.py); every number is a Fraction.  `check(cert)` returns
(ok, report) where report[sub] = (ok, details) for the eight sub-checks in checker order.
"""
from fractions import Fraction as F
import toy_arith as A
import toy_model as Mo
from toy_model import Model, m_add, m_mul, m_neg, m_const, m_zero, supBound, p_wnorm
import toy_constants as C

SUBS = ["checkStatic", "checkHamBounds", "checkEmbedding", "checkInvariance", "checkEnergy", "checkGram",
        "checkTorsion", "checkSmallness"]


def swap(a, n):
    return a + n if a < n else a - n


def hamSign(a, n):
    return 1 if a < n else -1


# ---------------------------------------------------------------- embedding data
def emb_polys(c):
    """(U_i, dU_i, A_i, dA_i) as exact polynomials; a missing component denotes 0 (F2)."""
    n, e = c["n"], c["emb"]
    U, A_ = [], []
    for i in range(n):
        if i < len(e["angle"]):
            z, h = e["angle"][i]
            U.append((Mo.realpoly_to_poly(z, h, n), e["angleDeg"][i] if i < len(e["angleDeg"]) else 0,
                      F(z) == 0 and len(h) == 0))
        else:
            U.append((Mo.p_zero(), 0, True))
        if i < len(e["action"]):
            z, h = e["action"][i]
            A_.append((Mo.realpoly_to_poly(z, h, n), e["actionDeg"][i] if i < len(e["actionDeg"]) else 0))
        else:
            A_.append((Mo.p_zero(), 0))
    return U, A_


def dk_models(c):
    """DK as a 2n x n model matrix (rows in sumVec order)."""
    n, w = c["n"], c["weight"][1]
    U, A_ = emb_polys(c)
    rows = []
    for i in range(n):
        P, d, _ = U[i]
        rows.append([m_add(m_const((1 if i == j else 0, 0), n), Mo.m_ofDeriv(j, d, P), w, c["piEnc"], c["_log"])
                     for j in range(n)])
    for i in range(n):
        P, d = A_[i]
        rows.append([Mo.m_ofDeriv(j, d, P) for j in range(n)])
    return rows


def d2k_models(c):
    """∂_m DK_{l i} as models: list over m of 2n x n matrices."""
    n = c["n"]
    U, A_ = emb_polys(c)
    out = []
    for m in range(n):
        rows = []
        for i in range(n):
            P, d, _ = U[i]
            rows.append([Model(d + 2, Mo.p_deriv(Mo.p_deriv(P, j), m)) for j in range(n)])
        for i in range(n):
            P, d = A_[i]
            rows.append([Model(d + 2, Mo.p_deriv(Mo.p_deriv(P, j), m)) for j in range(n)])
        out.append(rows)
    return out


# ---------------------------------------------------------------- composition (Slp.compose, READING)
def deps(ops, wanted):
    need, stack = set(), list(wanted)
    while stack:
        s = stack.pop()
        if s in need or s >= len(ops):
            continue
        need.add(s)
        op = ops[s]
        if op[0] in "+*":
            stack += [op[1], op[2]]
        elif op[0] in "EI":
            stack.append(op[1])
    return need


def compose(c, cfg, wanted, tag):
    """Models of the wanted slots of the jet program composed with K, or None (fail closed).

    READING: slots are computed in program order over the dependency closure of `wanted`; witnesses are
    consumed in slot order (one per `exp` / `inv` slot of the whole program); products are keyed
    [0, slot] (compose), [1, 1, char, j] (character-witness residuals), [2, inv] (reciprocal check)."""
    n, w, rho, pe = c["n"], c["weight"][1], c["weight"][0], c["piEnc"]
    ops = c["_ops"]
    U, A_ = emb_polys(c)
    need = deps(ops, wanted)
    exp_idx = {s: i for i, s in enumerate([s for s, op in enumerate(ops) if op[0] == "E"])}
    inv_idx = {s: i for i, s in enumerate([s for s, op in enumerate(ops) if op[0] == "I"])}
    vals, info = {}, {"inv": [], "char": []}
    for s in sorted(need):
        op = ops[s]
        g = lambda a: vals.get(a, m_zero(n))
        if op[0] == "C":
            vals[s] = m_const((op[1], op[2]), n, op[3])
        elif op[0] == "A":
            j = op[1]
            vals[s] = Model(A_[j][1], A_[j][0]) if j < n else m_zero(n)
        elif op[0] == "X":
            k = tuple(op[1]) + (0,) * (n - len(op[1]))
            nk = tuple(0 if U[j][2] else k[j] for j in range(n))      # normalized index
            gm = m_zero(n)
            for j in range(n):
                if nk[j] != 0:
                    P, d, _ = U[j]
                    gm = m_add(gm, Model(1 + d, Mo.p_scale(P, (0, k[j]))), w, pe, c["_log"])
            gm = Mo.m_toDeg(gm, 0, w, pe, c["_log"])
            wit = dict((tuple(kk) + (0,) * (n - len(kk)), E) for kk, E in c["wit"]["charWit"]).get(nk)
            if wit is None:
                return None, dict(info, fail="no character witness for %s" % (nk,))
            r = Mo.expWitnessRadius(n, w, rho, cfg, gm, wit, [1, 1, s])
            if r is None:
                return None, dict(info, fail="character witness %s rejected (pin or degree)" % (nk,))
            info["char"].append((s, nk, r))
            vals[s] = Model(0, Mo.p_shift(wit[0], k), r * F(w) ** Mo.kabs(k))
        elif op[0] == "+":
            vals[s] = m_add(g(op[1]), g(op[2]), w, pe, c["_log"])
        elif op[0] == "*":
            vals[s] = m_mul(g(op[1]), g(op[2]), w, cfg, [0, s])
        elif op[0] == "E":
            i = exp_idx[s]
            if i >= len(c["wit"]["expWit"]):
                return None, dict(info, fail="missing exp witness")
            gm = Mo.m_toDeg(g(op[1]), 0, w, pe, c["_log"])
            r = Mo.expWitnessRadius(n, w, rho, cfg, gm, c["wit"]["expWit"][i], [1, 0, i])
            if r is None:
                return None, dict(info, fail="exp witness %d rejected" % i)
            vals[s] = Model(0, c["wit"]["expWit"][i][0], r)
        elif op[0] == "I":
            i = inv_idx[s]
            if i >= len(c["wit"]["invWit"]):
                return None, dict(info, fail="missing reciprocal witness")
            b = g(op[1])
            r, delta = Mo.invWitnessRadius(n, w, cfg, b, c["wit"]["invWit"][i], [2, i])
            info["inv"].append((s, delta, r))
            if r is None:
                return None, dict(info, fail="reciprocal witness %d: delta = %s >= 1" % (i, float(delta)))
            vals[s] = Model(-b.deg, c["wit"]["invWit"][i], r)
    return [vals[s] for s in wanted], info


# ---------------------------------------------------------------- sub-checks
def check_static(c):
    p, n = c["params"], c["n"]
    box = c["freqBox"]
    L = max((abs(cc) - rr for cc, rr in box), default=F(-1))
    conds = {
        "n>=2": n >= 2, "n-1<=tau": n - 1 <= p["tau"], "0<rhoInf": 0 < p["rhoInf"],
        "rhoInf<rho": p["rhoInf"] < p["rho"], "0<M": 0 < p["M"], "0<sK": 0 < p["sK"], "0<sB": 0 < p["sB"],
        "0<sT": 0 < p["sT"], "0<mu": 0 < p["mu"], "0<gbar": 0 < p["gbar"], "1<sigma_omega": 1 < p["sigma_omega"],
        "0<nuRay": 0 < p["nuRay"], "1<s": 1 < p["s"], "s<sigma_omega": p["s"] < p["sigma_omega"],
        "0<gamma": 0 < p["gamma"], "gamma<=gbar": p["gamma"] <= p["gbar"], "0<=err": 0 <= p["err"],
        "weight.rho=rho": c["weight"][0] == p["rho"],
        "checkWeight(weight)": A.checkWeight(c["weight"][0], c["weight"][1], c["expHalvings"], c["expOrder"]),
        "checkWeight(weightH)": A.checkWeight(c["weightH"][0], c["weightH"][1], c["expHalvings"], c["expOrder"]),
        "checkPiEnclosure": A.checkPiEnclosure(*c["piEnc"]),
        "box.length=n": len(box) == n, "box radii>=0": all(r >= 0 for _, r in box),
        "centre/radius length n": len(c["centre"]) == n and len(c["radius"]) == n,
        "emb lengths n": all(len(c["emb"][k]) == n for k in ("angle", "angleDeg", "action", "actionDeg")),
        "box excludes 0": L > 0,
        "nu<=(s-1)L": p["nuRay"] <= (p["s"] - 1) * L,
        "nu<=(sigma_omega-s)L": p["nuRay"] <= (p["sigma_omega"] - p["s"]) * L,
    }
    return all(conds.values()), dict(conds=conds, normLower=L)


def ball_bounds(c):
    n = c["n"]
    jet = c["_jet"]
    bs = A.slp_balls(n, c["_ops"], c["weightH"][1], c["centre"], c["radius"], c["cfgFull"]["taylorN"])
    if bs is None:
        return None, None
    U = lambda s: A.normUp(bs[s][0]) + bs[s][1]
    d1, d2, d3 = jet["d1"], jet["d2"], jet["d3"]
    N2 = 2 * n
    b = {"DH": sum(U(d1[a]) for a in range(N2)),
         "X_H": max(U(d1[swap(a, n)]) for a in range(N2)),
         "DX_H": max(sum(U(d2[swap(a, n)][bb]) for bb in range(N2)) for a in range(N2)),
         "D2X_H": max(sum(U(d3[swap(a, n)][bb][cc]) for bb in range(N2) for cc in range(N2)) for a in range(N2)),
         "D2H": sum(U(d2[a][bb]) for a in range(N2) for bb in range(N2))}
    return b, bs


def check_ham_bounds(c):
    b, bs = ball_bounds(c)
    if b is None:
        return False, dict(balls=None, fail="Slp.balls = none (a denominator ball contains 0)")
    M = c["params"]["M"]
    return all(v <= M for v in b.values()), dict(bounds=b, M=M, maxBound=max(b.values()), nslots=len(bs))


def check_embedding(c):
    n, p, w = c["n"], c["params"], c["weight"][1]
    U, A_ = emb_polys(c)
    rho, mu, rhoH = p["rho"], p["mu"], c["weightH"][0]
    angle_ok, iotas = True, []
    for i in range(n):
        P, d, _ = U[i]
        supU = supBound(Model(d, P), w)
        supDU = sum((supBound(Mo.m_ofDeriv(j, d, P), w) for j in range(n)), F(0))
        iota = min(supU, rho * supDU)
        iotas.append(iota)
        angle_ok = angle_ok and rho + iota + mu <= rhoH
    act_ok, dists = True, []
    for i in range(n):
        P, d = A_[i]
        if d != 0 and not Mo.p_is_zero(P):
            mdl = Mo.m_toDeg(Model(d, P), 0, w, c["piEnc"], c["_log"])
        else:
            mdl = Model(0, P)
        diff = m_add(mdl, m_const((c["centre"][i], 0), n), w, c["piEnc"], c["_log"], sign=-1)
        dist = supBound(diff, w)
        dists.append(dist)
        act_ok = act_ok and dist + mu <= c["radius"][i]
    DK = dk_models(c)
    rowsums = [sum((supBound(m, w) for m in row), F(0)) for row in DK]
    dk_ok = max(rowsums) <= p["sK"] - mu
    return angle_ok and act_ok and dk_ok, dict(iota=iotas, actionDist=dists, DKnorm=max(rowsums),
                                                angle_ok=angle_ok, action_ok=act_ok, DK_ok=dk_ok)


def freq_balls(c):
    s = c["params"]["s"]
    return [(s * cc, s * rr) for cc, rr in c["freqBox"]]


def check_invariance(c):
    n, p, w, pe = c["n"], c["params"], c["weight"][1], c["piEnc"]
    cfg = c["_cfgFull"]
    jet = c["_jet"]
    ms, info = compose(c, cfg, list(jet["d1"]), "invariance")
    if ms is None:
        return False, dict(fail=info.get("fail"))
    DK = dk_models(c)
    v = freq_balls(c)
    comps = []
    for a in range(2 * n):
        xa = ms[swap(a, n)] if a < n else m_neg(ms[swap(a, n)])
        dkv = m_zero(n)
        for j in range(n):
            dkv = m_add(dkv, Mo.m_scale_ball(DK[a][j], (v[j][0], 0), v[j][1], w), w, pe, c["_log"])
        comps.append(supBound(m_add(xa, dkv, w, pe, c["_log"], sign=-1), w))
    e = max(comps)
    return e <= p["err"], dict(components=comps, bound=e, err=p["err"], info=info)


def check_energy(c):
    n, p, w, pe = c["n"], c["params"], c["weight"][1], c["piEnc"]
    ms, info = compose(c, c["_cfgFull"], [c["_jet"]["v0"]], "energy")
    if ms is None:
        return False, dict(fail=info.get("fail"))
    m = Mo.m_toDeg(ms[0], 0, w, pe, c["_log"])
    c0 = Mo.p_coeff0(m.poly, n)
    bound = A.normUp((c0[0] - p["E0"], c0[1])) + m.rad
    return bound <= p["err"], dict(average=c0, radius=m.rad, bound=bound, err=p["err"])


def mat_mul(X, Y, w, cfg, key, pe, log):
    n_r, n_k, n_c = len(X), len(Y), len(Y[0])
    out = []
    for i in range(n_r):
        row = []
        for j in range(n_c):
            acc = None
            for k in range(n_k):
                t = m_mul(X[i][k], Y[k][j], w, cfg, list(key) + [i, j, k])
                acc = t if acc is None else m_add(acc, t, w, pe, log)
            row.append(acc)
        out.append(row)
    return out


def omega0(X, n):
    """Ω₀ applied to the rows of a 2n-row matrix: (a, b) ↦ (-b, a)."""
    return [[m_neg(m) for m in X[n + i]] for i in range(n)] + [list(X[i]) for i in range(n)]


def gram_check(c):
    n, p, w, pe = c["n"], c["params"], c["weight"][1], c["piEnc"]
    cfg = c["_cfgLow"]
    B = c["gramInv"]
    if len(B) != n or any(len(r) != n for r in B):
        return None, dict(fail="gramInv shape")
    DK = dk_models(c)
    DKt = [[DK[l][i] for l in range(2 * n)] for i in range(n)]
    G = mat_mul(DKt, DK, w, cfg, [3, 0], pe, c["_log"])
    Bm = [[Model(0, P) for P in row] for row in B]
    BG = mat_mul(Bm, G, w, cfg, [3, 1], pe, c["_log"])
    E = [[m_add(m_const((1 if i == j else 0, 0), n), BG[i][j], w, pe, c["_log"], sign=-1) for j in range(n)]
         for i in range(n)]
    delta = max(sum((supBound(m, w) for m in row), F(0)) for row in E)
    beta = max(sum((p_wnorm(P, w) for P in row), F(0)) for row in B)
    det = dict(delta=delta, beta=beta, G=G)
    if not delta < 1:
        return None, dict(det, fail="delta >= 1")
    if not beta / (1 - delta) <= p["sB"] - p["mu"]:
        return None, dict(det, fail="beta/(1-delta) > sB - mu")
    return (delta, beta), det


def check_gram(c):
    db, det = gram_check(c)
    return db is not None, {k: v for k, v in det.items() if k != "G"}


def torsion_models(c, db):
    n, p, w, pe, log = c["n"], c["params"], c["weight"][1], c["piEnc"], c["_log"]
    cfg = c["_cfgLow"]
    jet = c["_jet"]
    delta, beta = db
    eps = delta * beta / (1 - delta)
    Ginv = [[Model(0, P, eps) for P in row] for row in c["gramInv"]]
    DK = dk_models(c)
    N = omega0(mat_mul(DK, Ginv, w, cfg, [4, 0], pe, log), n)
    v = freq_balls(c)
    D2K = d2k_models(c)
    D2Kv = [[m_zero(n) for _ in range(n)] for _ in range(2 * n)]
    for m in range(n):
        for l in range(2 * n):
            for i in range(n):
                D2Kv[l][i] = m_add(D2Kv[l][i], Mo.m_scale_ball(D2K[m][l][i], (v[m][0], 0), v[m][1], w), w, pe, log)
    DKt = [[DK[l][i] for l in range(2 * n)] for i in range(n)]
    D2Kvt = [[D2Kv[l][i] for l in range(2 * n)] for i in range(n)]
    DG1 = mat_mul(D2Kvt, DK, w, cfg, [4, 1], pe, log)
    DG2 = mat_mul(DKt, D2Kv, w, cfg, [4, 2], pe, log)
    DG = [[m_add(DG1[i][j], DG2[i][j], w, pe, log) for j in range(n)] for i in range(n)]
    DGinv = [[m_neg(m) for m in row] for row in
             mat_mul(mat_mul(Ginv, DG, w, cfg, [4, 3], pe, log), Ginv, w, cfg, [4, 4], pe, log)]
    T1 = mat_mul(D2Kv, Ginv, w, cfg, [4, 5], pe, log)
    T2 = mat_mul(DK, DGinv, w, cfg, [4, 6], pe, log)
    DN = omega0([[m_add(T1[l][j], T2[l][j], w, pe, log) for j in range(n)] for l in range(2 * n)], n)
    d1, d2 = jet["d1"], jet["d2"]
    flat = list(d1) + [d2[a][b] for a in range(2 * n) for b in range(2 * n)]
    ms, info = compose(c, cfg, flat, "torsion")
    if ms is None:
        return None, info
    D1 = ms[:2 * n]
    D2 = [ms[2 * n + 2 * n * a: 2 * n + 2 * n * (a + 1)] for a in range(2 * n)]
    DXH = [[(D2[swap(a, n)][b] if a < n else m_neg(D2[swap(a, n)][b])) for b in range(2 * n)]
           for a in range(2 * n)]
    XN0 = mat_mul(DXH, N, w, cfg, [4, 7], pe, log)
    XN = [[m_add(XN0[l][j], DN[l][j], w, pe, log, sign=-1) for j in range(n)] for l in range(2 * n)]
    Nt = [[N[l][i] for l in range(2 * n)] for i in range(n)]
    T = mat_mul(Nt, omega0(XN, n), w, cfg, [4, 8], pe, log)
    last = mat_mul([D1], N, w, cfg, [4, 9], pe, log)[0]
    rows = [T[a] + [m_const((v[a][0], 0), n, 0, v[a][1])] for a in range(n)]
    rows.append(last + [m_zero(n)])
    return rows, info


def torsion_avg_check(c, T, S, bound):
    n, w, pe = c["n"], c["weight"][1], c["piEnc"]
    k = n + 1
    if len(T) != k or any(len(r) != k for r in T) or len(S) != k or any(len(r) != k for r in S):
        return False, dict(fail="shape (F7)")
    Cm, R = [], []
    for row in T:
        cr, rr = [], []
        for m in row:
            m0 = Mo.m_toDeg(m, 0, w, pe, c["_log"])
            cr.append(Mo.p_coeff0(m0.poly, n))
            rr.append(m0.rad)
        Cm.append(cr)
        R.append(rr)
    cm = lambda a, b: (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])
    ISC = []
    for i in range(k):
        row = []
        for j in range(k):
            acc = (F(1 if i == j else 0), F(0))
            for l in range(k):
                t = cm(S[i][l], Cm[l][j])
                acc = (acc[0] - t[0], acc[1] - t[1])
            row.append(acc)
        ISC.append(row)
    nISC = max(sum(A.normUp(x) for x in row) for row in ISC)
    nS = max(sum(A.normUp(x) for x in row) for row in S)
    nR = max(sum(row) for row in R)
    dT = nISC + nS * nR
    ok = dT < 1 and nS / (1 - dT) <= bound
    return ok, dict(deltaT=dT, normISC=nISC, normS=nS, normR=nR, normInvBound=(nS / (1 - dT) if dT < 1 else None),
                    bound=bound, centre=Cm, radius=R)


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
    ok, d = C.smallness(p)
    return ok, d


def prepare(c):
    import toy_model as Mo2
    c["_ops"] = A.parse_ops(c["_jet"]["ops"])
    c["_log"] = []
    c["_cfgFull"] = Mo2.Cfg("cfgFull", c["cfgFull"]["cutoff"], c["cfgFull"]["taylorN"], c["cfgFull"]["halvings"])
    c["_cfgLow"] = Mo2.Cfg("cfgLow", c["cfgLow"]["cutoff"], c["cfgLow"]["taylorN"], c["cfgLow"]["halvings"])
    return c


def check(c, only=None):
    prepare(c)
    fns = dict(checkStatic=check_static, checkHamBounds=check_ham_bounds, checkEmbedding=check_embedding,
               checkInvariance=check_invariance, checkEnergy=check_energy, checkGram=check_gram,
               checkTorsion=check_torsion, checkSmallness=check_smallness)
    rep = {}
    for s in SUBS:
        if only and s not in only:
            continue
        rep[s] = fns[s](c)
    return all(r[0] for r in rep.values()), rep
