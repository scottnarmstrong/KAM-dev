#!/usr/bin/env python3
"""SO-GEN2: build the rotated-frame candidate K' and bound its invariance error exactly (owner ruling O5).

Untrusted tooling.  Rotated frame: Q1 = q - phi, Q2 = phi, P1 = p, P2 = p + J,
    H' = P1^2/2 - P1 + P2 + V(Q1 + Q2, Q2),   V(q, phi) = - sum_m eps A_m cos(2 pi (2 q - m phi)),
so the modes of V are the keys s_m = (2, 2 - m) in (Q1, Q2).  Candidate (angles theta = (psi, phi)):
    K'(theta) = (psi + v/2pi, phi, p~, p~ + J~),  frequency omega' = (nu - 1, 1), time scale c: H -> c H',
all data dyadic at scale 2^-S:
    v  = sum_H b sin(2 pi kappa.theta)        (SO-GEN solution, truncated at 10^-Lv, rounded),
    p~ = round(nu + Dt v)                     (Dt = (nu-1) d_psi + d_phi in index units: p = nu + sum b lambda cos),
    E~ = SO-GEN witness of exp(2 i v)         (truncated at 10^-LE, rounded), character witness of every key (2, .),
    J~ = round(-p~^2/2 + sum_m eps A_m Re(e_{s_m} E~)) truncated at 10^-LJ.
Invariance error rows (theta units, before the factor c):
    Q1: p~ - (nu + Dt v)                       (rounding only),   Q2: 0,
    P1: -2 pi [Dt p~ + 2 eps sum A_m Im(e_m E)],  P2: -2 pi [eps sum A_m (2-m) Im(e_m E) + Dt (p~ + J~)],
where E = exp(2 i v) is replaced by E~ plus the witness error Delta >= sup_{T_rho}|exp(2iv) - E~| from the
design's exp-witness theorem: Delta <= e^{2B} (eps0 + (1/2 + rho) (r_psi + r_phi)), B >= sup|2 v|,
eps0 = |E~(0) - 1|, r_j >= sup|d_j E~ - 2 i (d_j v) E~| (theta units).  The polynomial parts are computed
EXACTLY (integers, Q(sqrt5) as pairs) and summed with rigorous integer weights W(n) >= exp(2 pi rho n).
"""
import sys, time, math, json, pickle
import numpy as np
import mpmath
from fractions import Fraction as F
from rotlib import (SPoly, Weights, load_candidate, sin_series, cos_series, up, addu, mulu, WB, _obj)
import model

RHO = F(1, 70)
SQ5_T = 600                                     # sqrt5 enclosure bits
SQ5_LO = math.isqrt(5 << (2 * SQ5_T))           # floor(sqrt5 2^T)
SQ5_HI = SQ5_LO + 1
DEN_NU = 3118
EPSA = {m: model.EPS * model.A_EXACT[m] for m in model.M_MODES}
DA = 1
for q in EPSA.values():
    DA = DA * q.denominator // math.gcd(DA, q.denominator)
AINT = {m: int(EPSA[m] * DA) for m in EPSA}     # eps A_m = AINT_m / DA exactly
SH = model.SHIFT                                # m -> (2, 2 - m)


def lam_pair(which, k, l):
    """3118 lambda = a + b sqrt5 for lambda = (nu - 1) k + l (object arrays)."""
    if which == "lower":     # nu - 1 = -(79 - sqrt5)/3118
        return 3118 * l - 79 * k, k
    return 3118 * l + 79 * k, -k


def nu_minus_one_mp(which):
    a = (79 - mpmath.sqrt(5)) / 3118
    return -a if which == "lower" else a


def absq5_up(X, Y):
    """integer U (object array) with |X + Y sqrt5| <= U / 2^SQ5_T."""
    X = X * (1 << SQ5_T)
    a = np.abs(X + Y * SQ5_LO)
    b = np.abs(X + Y * SQ5_HI)
    return np.where(a > b, a, b) + 1


def l1w_q5(k, l, X, Y, den, Wt, mult=None):
    """upper bound of sum |X + Y sqrt5| / den * W(|kappa|) [* mult] (float)."""
    if len(X) == 0:
        return 0.0
    U = absq5_up(_obj(X), _obj(Y))
    n = np.abs(k) + np.abs(l)
    w = Wt.W[n]
    if mult is not None:
        w = w * mult
    tot = int((U * w).sum())
    return up(F(tot, den << (SQ5_T + WB)))


def exp_up(x):
    """float >= exp(x) (libm exp is accurate to < 1 ulp; one relative 1e-14 guard plus an ulp)."""
    return up(math.exp(x) * (1 + 1e-14))


TWOPI_UP = up(2 * math.pi * (1 + 1e-15))


def build(which, Lv, LE, LJ, S, log=print):
    """Candidate data (dyadic, scale S) and the exact residual bounds.  Returns dict."""
    t0 = time.time()
    Wt = Weights(RHO)
    b0, E0, P = load_candidate(which)
    mpmath.mp.prec = 1400
    # --- v: truncate at 10^-Lv (on the 440-bit data), round to S bits
    tv = int(mpmath.ceil(mpmath.mpf(10) ** (-Lv) * 2**P))
    sh = P - S
    bS = {}
    for kk, n in b0.items():
        if abs(n) >= tv:
            r = (n + (1 << (sh - 1))) >> sh
            if r:
                bS[kk] = r
    # --- E~: SO-GEN witness, truncate at 10^-LE, round
    tE = int(mpmath.ceil(mpmath.mpf(10) ** (-LE) * 2**P))
    ES = {}
    for kk, n in E0.items():
        if abs(n) >= tE:
            r = (n + (1 << (sh - 1))) >> sh
            if r:
                ES[kk] = r
    # --- p~ = round(nu + sum b lambda cos), coefficients at scale S
    nu = 1 + nu_minus_one_mp(which)
    s1 = nu_minus_one_mp(which)
    pS = {}
    for (k, l), n in bS.items():
        c = int(mpmath.nint(n * (s1 * k + l)))
        if c:
            pS[(k, l)] = c
    p0 = int(mpmath.nint(nu * 2**S))
    v = sin_series(bS, S)                        # phase 1, scale S+1
    p = cos_series(pS, p0, S)                    # phase 0, scale S+1
    E = SPoly.from_dict(ES, S, 0)                # phase 0, scale S
    log("%s: v half %d, E %d, p half %d  (%.1fs)" % (which, len(bS), len(ES), len(pS), time.time() - t0))

    # --- J_E = -p^2/2 + sum eps A_m Re_an(e_m E)  exactly, at denominator DA 2^(2S+3)
    t1 = time.time()
    p2 = p.mul(p, Wt)                            # scale 2S+2, exact
    Jd = {}
    for kk, x in zip(zip(p2.k.tolist(), p2.l.tolist()), p2.v):
        Jd[kk] = -int(x) * DA                    # -p^2/2 at scale DA 2^(2S+3)
    sc = 1 << (S + 3)                            # E at 2^S -> 2^(2S+3) needs 2^(S+3); Re_an halves -> 2^(S+2)
    for m, (a, d) in SH.items():
        for (k, l), n in ES.items():
            for kk in ((k + a, l + d), (-k - a, -l - d)):
                Jd[kk] = Jd.get(kk, 0) + AINT[m] * n * (sc >> 1)
    DenJ = DA << (2 * S + 3)
    log("  p~^2 and J_E: %d terms (%.1fs)" % (len(Jd), time.time() - t1))
    # J~ : round J_E to scale S+1 (full-lattice, symmetric), drop |J| < 10^-LJ (zero mode kept)
    tJ = F(1, 10**LJ)
    Jt = {}
    for kk, x in Jd.items():
        if kk != (0, 0) and abs(F(x, DenJ)) < tJ:
            continue
        q = F(x * (1 << (S + 1)), DenJ)
        r = math.floor(q + F(1, 2))
        if r:
            Jt[kk] = r
    # symmetric by construction (J_E is even); half-lattice J coefficients j = 2 Jt (cos form) at scale S+1 -> S:
    J = SPoly.from_dict(Jt, S + 1, 0)
    # exact difference J~ - J_E at denominator DenJ
    dJ = {}
    fac = DenJ >> (S + 1)
    for kk in set(Jd) | set(Jt):
        x = Jt.get(kk, 0) * fac - Jd.get(kk, 0)
        if x:
            dJ[kk] = x

    res = dict(which=which, Lv=Lv, LE=LE, LJ=LJ, S=S, v=v, p=p, E=E, J=J, bS=bS, pS=pS, p0=p0, ES=ES,
               nv_half=len(bS), nE=len(ES), np_half=len(pS), nJ_full=len(Jt))
    res["bounds"] = bounds(which, v, p, E, J, dJ, DenJ, S, Wt, log)
    log("  total %.1fs" % (time.time() - t0))
    return res


def bounds(which, v, p, E, J, dJ, DenJ, S, Wt, log=print):
    t0 = time.time()
    out = {}
    w_up = Wt.w_up()
    twopi_up = TWOPI_UP
    s1 = nu_minus_one_mp(which)
    # ---------------- witness error Delta
    B = mulu(2.0, v.norm(Wt))
    E00 = sum(int(x) for x in E.v)                       # E~(0) = sum of coefficients (scale S)
    eps0 = up(F(abs(E00 - (1 << E.S)), 1 << E.S))
    t1 = time.time()
    dv_psi = v.dpsi()                                     # phase 0
    dv_phi = v.dphi()
    defs = {}
    for name, dv, dE in (("psi", dv_psi, E.dpsi()), ("phi", dv_phi, E.dphi())):
        prod = dv.mul(E, Wt).times_i()                    # i (d v) E, phase 1, scale (S+1)+S
        prod = prod.mul_int(2)
        dEs = dE.rescale(prod.S)
        defs[name] = dEs.sub(prod)                        # d E - 2 i (d v) E  (index units, exact)
    log("  defect products (%.1fs)" % (time.time() - t1))
    r_psi = mulu(twopi_up, defs["psi"].norm(Wt))
    r_phi = mulu(twopi_up, defs["phi"].norm(Wt))
    rho_f = float(RHO) * (1 + 1e-15)
    e2B = exp_up(mulu(2.0, B))
    Delta = mulu(e2B, addu(eps0, mulu(addu(0.5, rho_f), addu(r_psi, r_phi))))
    out.update(B=B, eps0=eps0, r_psi=r_psi, r_phi=r_phi, Delta=Delta)

    # ---------------- row Q1: p~ - (nu + Dt v): rounding of p (bounded per coefficient in mp interval arithmetic)
    # p = nu + sum b lambda cos with b = B/2^S exactly; p~ coefficient C/2^S; |C - B lambda| <= 1/2 (+ tiny)
    mpmath.mp.prec = 1400
    sq5 = mpmath.sqrt(5)
    errsum = mpmath.mpf(0)
    pd = {}
    for (k, l), x in zip(zip(p.k.tolist(), p.l.tolist()), p.v):
        pd[(k, l)] = int(x)
    vd = {}
    for (k, l), x in zip(zip(v.k.tolist(), v.l.tolist()), v.v):
        vd[(k, l)] = int(x)
    nu = 1 + s1
    tot = mpmath.mpf(0)
    qkeys = set(pd) | set(vd) | {(0, 0)}
    for (k, l) in qkeys:
        x = pd.get((k, l), 0)
        if (k, l) == (0, 0):
            ex = nu * 2**(S + 1)
        else:
            # v (phase 1, scale S+1) has value -b at kappa in H and +b at -kappa; p = nu + sum b lambda cos has
            # full-lattice value b lambda (scale S+1) at both +-kappa, with lambda(-kappa) = -lambda(kappa)
            ex = -vd.get((k, l), 0) * (s1 * k + l)
        d = abs(x - ex)
        tot += d * Wt.W[abs(k) + abs(l)]
    eta1 = up(F(str(mpmath.mpf(tot) * (1 + mpmath.mpf(2)**-1000))) / (1 << (S + 1 + WB)))
    out["eta1_unscaled"] = eta1

    # ---------------- rows P1, P2 (index units, phase 1 values at full-lattice mu), exact Q(sqrt5)
    Ed = {}
    for (k, l), x in zip(zip(E.k.tolist(), E.l.tolist()), E.v):
        Ed[(k, l)] = int(x)
    Jd = {}
    for (k, l), x in zip(zip(J.k.tolist(), J.l.tolist()), J.v):
        Jd[(k, l)] = int(x)
    keys = set(pd) | set(Jd)
    for m, (a, d) in SH.items():
        for (k, l) in Ed:
            keys.add((k + a, l + d)); keys.add((-k - a, -l - d))
    keys.discard((0, 0))
    keys = sorted(keys)
    kk = np.array([x for x, _ in keys], dtype=np.int64); ll = np.array([y for _, y in keys], dtype=np.int64)
    ko = _obj(kk.tolist()); lo = _obj(ll.tolist())
    la, lb = lam_pair(which, ko, lo)
    Pv = _obj([pd.get(x, 0) for x in keys])               # scale S+1
    Jv = _obj([Jd.get(x, 0) for x in keys])               # scale S+1
    # sum_m eps A_m (E_{-mu-s} - E_{mu-s}) and the (2-m)-weighted one, numerators at AINT (scale DA 2^S)
    G3 = _obj([0] * len(keys)); G4 = _obj([0] * len(keys))
    for m, (a, d) in SH.items():
        diff = _obj([Ed.get((-x - a, -y - d), 0) - Ed.get((x - a, y - d), 0) for (x, y) in keys])
        G3 = G3 + AINT[m] * diff
        G4 = G4 + AINT[m] * (2 - m) * diff
    # Den3 = 3118 DA 2^(S+1):  R3 = lambda P + G3/(DA 2^S),  R4 = lambda (P + J) + G4/(2 DA 2^S)
    X3 = DA * la * Pv + 2 * DEN_NU * G3
    Y3 = DA * lb * Pv
    X4 = DA * la * (Pv + Jv) + DEN_NU * G4
    Y4 = DA * lb * (Pv + Jv)
    Den3 = DEN_NU * DA << (S + 1)
    R3 = l1w_q5(kk, ll, X3, Y3, Den3, Wt)
    R4 = l1w_q5(kk, ll, X4, Y4, Den3, Wt)
    sumA_w = 0.0; sumA2m_w = 0.0; sumA = 0.0
    for m, (a, d) in SH.items():
        wa = up(F(Wt.W[abs(a) + abs(d)], 1 << WB))
        ea = up(abs(EPSA[m]))
        sumA_w = addu(sumA_w, mulu(ea, wa)); sumA = addu(sumA, ea)
        sumA2m_w = addu(sumA2m_w, mulu(mulu(ea, abs(2 - m)), wa))
    eta3 = mulu(twopi_up, addu(R3, mulu(mulu(2.0, sumA_w), Delta)))
    eta4 = mulu(twopi_up, addu(R4, mulu(sumA2m_w, Delta)))
    out.update(R3_l1w=R3, R4_l1w=R4, eta3_unscaled=eta3, eta4_unscaled=eta4,
               eta_unscaled=max(eta1, eta3, eta4))
    # ---------------- energy: avg(p^2/2 + V_E + J) + witness
    # zero mode of p^2: sum_kappa P_k P_-k (scale 2S+2); V_E zero mode: - sum eps A_m E_{-s_m}
    p2_0 = sum(pd[x] * pd.get((-x[0], -x[1]), 0) for x in pd)
    en = F(p2_0, 1 << (2 * S + 3)) + F(Jd.get((0, 0), 0), 1 << (S + 1))
    for m, (a, d) in SH.items():
        en -= EPSA[m] * F(Ed.get((-a, -d), 0), 1 << S)
    energy = addu(up(abs(en)), mulu(sumA, Delta))
    out["energy_unscaled"] = energy
    # ---------------- gate G-J budgets
    # dJ = J~ - J_E exact at DenJ (dict), DeltaJ = dJ + (W_E - W)
    dk = np.array([x for x, _ in dJ], dtype=np.int64); dl = np.array([y for _, y in dJ], dtype=np.int64)
    dvv = _obj(list(dJ.values()))
    def l1(mult):
        n = np.abs(dk) + np.abs(dl)
        if len(dvv) == 0:
            return 0.0
        tot = int((np.abs(dvv) * Wt.W[n] * mult).sum())
        return up(F(tot, DenJ << WB))
    one = _obj([1] * len(dvv))
    dko = _obj(np.abs(dk).tolist()); dlo = _obj(np.abs(dl).tolist())
    B0 = addu(l1(one), mulu(sumA_w, Delta))
    # Dt dJ: |lambda| dJ   (Q(sqrt5) via l1w_q5)
    la_d, lb_d = lam_pair(which, _obj(dk.tolist()), _obj(dl.tolist()))
    DtdJ = l1w_q5(dk, dl, DEN_NU * 0 + la_d * dvv, lb_d * dvv, DenJ * DEN_NU, Wt) if len(dvv) else 0.0
    # sup |Dt v| (index units): Dt v = sum b lambda cos
    Dtv = 0.0
    if True:
        vk = v.k; vl = v.l
        lav, lbv = lam_pair(which, _obj(vk.tolist()), _obj(vl.tolist()))
        Dtv = l1w_q5(vk, vl, lav * v.v, lbv * v.v, DEN_NU << v.S, Wt)
    # delta_D = (nu-1) defect_psi + defect_phi (index units)
    dD = None
    s1f = up(abs(float(s1)))
    nd_psi = defs["psi"].norm(Wt); nd_phi = defs["phi"].norm(Wt)
    nd_D = addu(mulu(s1f, nd_psi), nd_phi)
    Bt1 = 0.0
    for m, (a, d) in SH.items():
        lam_s = up(abs(float(2 * s1 + (2 - m))) * (1 + 1e-12))
        wa = up(F(Wt.W[abs(a) + abs(d)], 1 << WB))
        term = mulu(wa, addu(mulu(lam_s, Delta), nd_D, mulu(mulu(2.0, Dtv), Delta)))
        Bt1 = addu(Bt1, mulu(up(abs(EPSA[m])), term))
    B1_unscaled = mulu(twopi_up, addu(DtdJ, Bt1))         # sup |D_{omega'} DeltaJ| (theta units), times c later
    # B2: first and second partials (theta units)
    nv_d = {"psi": dv_psi.norm(Wt), "phi": dv_phi.norm(Wt)}
    dkk = {"psi": dko, "phi": dlo}
    nd = {"psi": nd_psi, "phi": nd_phi}
    dj = {j: addu(nd[j], mulu(mulu(2.0, nv_d[j]), Delta)) for j in nd}       # sup|d~_j DeltaE|
    first = {}
    for j in ("psi", "phi"):
        tt = l1(dkk[j])
        for m, (a, d) in SH.items():
            sj = abs(a) if j == "psi" else abs(d)
            wa = up(F(Wt.W[abs(a) + abs(d)], 1 << WB))
            tt = addu(tt, mulu(up(abs(EPSA[m])), mulu(wa, addu(mulu(sj, Delta), dj[j]))))
        first[j] = mulu(twopi_up, tt)
    second = {}
    vv = {"psi": dv_psi, "phi": dv_phi}
    for j in ("psi", "phi"):
        for k2 in ("psi", "phi"):
            dd = (defs[j].dpsi() if k2 == "psi" else defs[j].dphi()).norm(Wt)          # ||d~_k defect_j||
            d2v = (vv[j].dpsi() if k2 == "psi" else vv[j].dphi()).norm(Wt)            # ||d~_k d~_j v||
            tt = l1(dkk[j] * dkk[k2])
            for m, (a, d) in SH.items():
                sj = abs(a) if j == "psi" else abs(d)
                sk = abs(a) if k2 == "psi" else abs(d)
                wa = up(F(Wt.W[abs(a) + abs(d)], 1 << WB))
                inner = addu(mulu(sk * sj, Delta), mulu(sk, dj[j]), mulu(sj, dj[k2]), dd,
                             mulu(mulu(2.0, d2v), Delta), mulu(mulu(2.0, nv_d[j]), dj[k2]))
                tt = addu(tt, mulu(up(abs(EPSA[m])), mulu(wa, inner)))
            second[j + k2] = mulu(mulu(twopi_up, twopi_up), tt)
    B2 = max(list(first.values()) + list(second.values()))
    # sup |p - 1| and sup |V_q(K)| (for B_r = sup|p-1| eta3 + sup|V_q| eta1)
    pm1 = p.sub(SPoly.const(1, p.S)).norm(Wt)
    # |V_q(K)| <= 4 pi sum eps|A_m| |sin X_m(K)|,  |sin X_m(K)| <= w^|s| (||E~||_w + Delta)
    nE = E.norm(Wt)
    Vq = mulu(mulu(2.0, twopi_up), addu(mulu(sumA_w, nE), mulu(sumA_w, Delta)))
    out.update(B0=B0, B1_unscaled=B1_unscaled, B2=B2, B2_parts=dict(first=first, second=second),
               sup_p_minus_1=pm1, sup_Vq=Vq, Br_unscaled=addu(mulu(pm1, eta3), mulu(Vq, eta1)),
               Dt_dJ=DtdJ, defect_psi_l1w=nd_psi, defect_phi_l1w=nd_phi, sup_Dtv=Dtv, normE=nE,
               normv=v.norm(Wt))
    log("  bounds (%.1fs): Delta %.3e  eta1 %.3e  eta3 %.3e  eta4 %.3e  energy %.3e  B0 %.3e B1 %.3e B2 %.3e" % (
        time.time() - t0, Delta, eta1, eta3, eta4, energy, B0, B1_unscaled, B2))
    return out


if __name__ == "__main__":
    which, Lv, LE, LJ, S = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    r = build(which, Lv, LE, LJ, S)
    if len(sys.argv) > 6:
        pickle.dump(r, open(sys.argv[6], "wb"))
