#!/usr/bin/env python3
"""SO-GEN2: rigorous norm enclosures of the rotated-frame candidate (owner ruling O5).  Untrusted tooling.

Every bound is a CHECKER-STYLE enclosure on the open strip T_rho (rho = 1/70): sup|f| <= ||P||_w + r for a model
(P, r) (rotlib.SPoly), products by exact convolution with outward radius propagation, truncation / rounding mass
moved into the radius, 2 pi and nu - 1 as rational centres with explicit error.  No sampled maxima are used
for any bound (grid evaluation only PRODUCES the approximate Gram inverse B and the torsion witness S, whose
quality is then CHECKED).  All quantities at time scale c = 1; the caller scales M by c and the torsion
inverse by 1/c.

  sigma_K - mu >= max_i sum_j ||DK_ij||                         (DK of K' = (psi + v/2pi, phi, p, p + J))
  domain D = T_{rho_H} x discs: rho_H >= rho + iota + mu, r_i >= sup|A_i - c_i| + mu
  M_1 >= the five H'-quantities on D (|sin|,|cos| <= cosh on the Q-strip)
  Gram: B ~ G^-1 (Fourier polynomial), delta = ||I - B G|| < 1, beta = ||B||, ||G^-1|| <= beta/(1 - delta)
  torsion: entries of the bordered extended torsion (frozen `extendedTorsion`) as models, average = zero mode +- r,
           S ~ avg^-1, delta_T = ||I - S C|| + ||S|| ||R|| < 1, ||avg^-1|| <= ||S||/(1 - delta_T)
"""
import sys, math, time, pickle, json
import numpy as np
from fractions import Fraction as F
import mpmath
from rotlib import SPoly, Weights, up, addu, mulu, WB, two_pi_interval
import model
from rot_build import RHO, EPSA, SH, nu_minus_one_mp

MU = F(1, 160)
SN = 72                     # model scale bits
THR = F(1, 2**56)           # coefficient truncation into the radius (~1.4e-17)


def rowsum(rows, Wt):
    return max(addu(*[e.norm(Wt) for e in r]) for r in rows)


class Ctx:
    def __init__(self, which):
        self.Wt = Weights(RHO)
        self.which = which
        self.tp, self.tpe = two_pi_interval(SN)                  # 2 pi in [tp - tpe, tp + tpe]
        mpmath.mp.prec = SN + 64
        s1 = nu_minus_one_mp(which)
        self.s1 = F(int(mpmath.nint(s1 * 2**SN)), 1 << SN)
        self.s1e = up(F(1, 1 << SN))
        self.tp2 = self.tp * self.tp
        self.tp2e = up(addu(mulu(2 * float(self.tp) * (1 + 1e-15), self.tpe), mulu(self.tpe, self.tpe)))

    def red(self, f):
        return f.round_to(SN, self.Wt, THR)

    def mul(self, a, b):
        return a.mul(b, self.Wt, SN, THR)

    def sc(self, f, c, e=0.0):
        return f.mul_iv(F(c), e, self.Wt, SN).round_to(SN, self.Wt, THR)

    def twopi(self, f):
        return self.sc(f, self.tp, self.tpe)

    def Dt(self, f):
        """index-unit derivative along omega' = (nu - 1, 1) of an EXACT polynomial; result model."""
        a = f.dpsi(); b = f.dphi()
        return self.red(self.sc(a, self.s1, self.s1e).add(b.round_to(SN, self.Wt, THR)))


def madd(*fs):
    out = fs[0]
    for f in fs[1:]:
        out = out.add(f)
    return out


def grid_rowsum_sup(Bm, Wt, N1=4096, N2=1024):
    """ALTERNATIVE (not in the designed checker) rigorous bound of sup_{T_rho} max_i sum_j |B_ij|: the row sums are
    plurisubharmonic and continuous on the closed polystrip, so the sup is attained on the distinguished boundary
    |Im psi| = |Im phi| = rho (two tori up to conjugation, B real on reals).  On each torus: max over an N1 x N2 grid
    (double FFT, + 1e-9 evaluation guard) + (h1/2) sum_j sup|d_psi B_ij| + (h2/2) sum_j sup|d_phi B_ij|, the
    derivative sups bounded by weighted l1 norms (theta units, 2 pi rounded up)."""
    rho = float(RHO)
    tp = up(2 * math.pi * (1 + 1e-15))
    best = 0.0
    lips = []
    for i in range(2):
        a = addu(*[mulu(tp, Bm[i][j].dpsi().norm(Wt)) for j in range(2)])
        b = addu(*[mulu(tp, Bm[i][j].dphi().norm(Wt)) for j in range(2)])
        lips.append(addu(mulu(a, 0.5 / N1), mulu(b, 0.5 / N2)))
    for (yp, yf) in [(rho, rho), (rho, -rho)]:
        vals = [[Bm[i][j].eval_grid(N1, N2, yp, yf) for j in range(2)] for i in range(2)]
        for i in range(2):
            m = float((np.abs(vals[i][0]) + np.abs(vals[i][1])).max())
            best = max(best, addu(m, 1e-9, lips[i]))
    return best


def norms(cand, Delta, log=print):
    """cand: dict from rot_build.build (exact v, p, E, J SPolys).  Delta: witness error bound sup|exp(2iv) - E~|."""
    t0 = time.time()
    X = Ctx(cand["which"])
    Wt = X.Wt
    v, p, E, J = cand["v"], cand["p"], cand["E"], cand["J"]
    P2 = p.add(J)                                   # P2 = p + J (exact)
    one = SPoly.const(1, SN)
    out = {}
    # ---------------- DK (theta units)
    dv = [v.dpsi(), v.dphi()]                       # exact, phase 0
    dp = [p.dpsi(), p.dphi()]                       # exact, phase 1
    dP2 = [P2.dpsi(), P2.dphi()]
    DK = [[X.red(dv[0]).add(one), X.red(dv[1])],
          [SPoly.zero(SN, 0), one],
          [X.twopi(X.red(dp[0])), X.twopi(X.red(dp[1]))],
          [X.twopi(X.red(dP2[0])), X.twopi(X.red(dP2[1]))]]
    rows = [addu(*[e.norm(Wt) for e in r]) for r in DK]
    out["DK_rowsums"] = rows
    out["sigmaK_minus_mu_need"] = max(rows)
    log("  DK row sums", ["%.6f" % x for x in rows])
    # ---------------- domain D
    tp_lo = float(X.tp) - X.tpe
    supU = up(v.norm(Wt) / tp_lo * (1 + 1e-15))
    iotaD = mulu(float(RHO) * (1 + 1e-15), addu(dv[0].norm(Wt), dv[1].norm(Wt)))
    iota1 = min(supU, iotaD)
    c1 = p.coeff0(); c2 = P2.coeff0()
    rA1 = p.sub(SPoly.const(c1, p.S)).norm(Wt)
    rA2 = P2.sub(SPoly.const(c2, P2.S)).norm(Wt)
    muf = float(MU)
    rhoH_need = addu(float(RHO) * (1 + 1e-15), iota1, muf * (1 + 1e-15))
    rhoH = F(math.ceil(rhoH_need * 10**5) + 1, 10**5)
    r1 = F(math.ceil(addu(rA1, muf * (1 + 1e-15)) * 10**5) + 1, 10**5)
    r2 = F(math.ceil(addu(rA2, muf * (1 + 1e-15)) * 10**5) + 1, 10**5)
    c1q = F(round(c1 * 10**5), 10**5); c2q = F(round(c2 * 10**5), 10**5)
    # the discs must contain ball(A_i, mu): |A_i - c_iq| <= |A_i - c_i| + |c_i - c_iq|
    r1 = r1 + F(math.ceil(abs(c1 - c1q) * 10**5) + 1, 10**5)
    r2 = r2 + F(math.ceil(abs(c2 - c2q) * 10**5) + 1, 10**5)
    out["domain"] = dict(sup_U1=supU, iota1_meanvalue=iotaD, iota1=iota1, iota2=0.0, rho_H=str(rhoH),
                         c1=str(c1q), r1=str(r1), c2=str(c2q), r2=str(r2), sup_A1_dev=rA1, sup_A2_dev=rA2)
    log("  domain: iota1 %.5f (supU %.5f, MVT %.5f) rho_H %s  P1 in %s +- %s  P2 in %s +- %s" % (
        iota1, supU, iotaD, rhoH, c1q, r1, c2q, r2))
    # ---------------- H' majorant on D (c = 1)
    tpu = up(float(X.tp) + X.tpe)
    gQ = [0.0, 0.0]; gQQ = np.zeros((2, 2)); gQQQ = [0.0, 0.0]
    for m, (a, d) in SH.items():
        y = mulu(mulu(tpu, float(abs(a) + abs(d))), float(rhoH) * (1 + 1e-15))
        ch = up(math.cosh(y) * (1 + 1e-14))
        ea = mulu(up(abs(EPSA[m])), ch)
        dd = (abs(a), abs(d))
        for i in range(2):
            gQ[i] = addu(gQ[i], mulu(ea, mulu(tpu, dd[i])))
            for j in range(2):
                gQQ[i, j] = addu(gQQ[i, j], mulu(ea, mulu(mulu(tpu, tpu), dd[i] * dd[j])))
            gQQQ[i] = addu(gQQQ[i], mulu(ea, mulu(up(tpu ** 3 * (1 + 1e-15)), dd[i] * (dd[0] + dd[1]) ** 2)))
    P1m1 = up(float(abs(c1q - 1) + r1) * (1 + 1e-15))
    dH = addu(gQ[0], gQ[1], P1m1, 1.0)
    XH = max(P1m1, 1.0, gQ[0], gQ[1])
    DXH = max(1.0, addu(gQQ[0, 0], gQQ[0, 1]), addu(gQQ[1, 0], gQQ[1, 1]))
    D2XH = max(gQQQ)
    D2H = addu(1.0, gQQ.sum() * (1 + 1e-14))
    M1 = max(dH, XH, DXH, D2XH, D2H)
    out["H"] = dict(dH=dH, XH=XH, DXH=DXH, D2XH=D2XH, D2H=D2H, M1=M1, P1m1=P1m1, VQ=gQ, VQQ=gQQ.tolist(), VQQQ=gQQQ)
    log("  H' majorant (c=1): M1 %.6f  [dH %.6f XH %.6f DXH %.6f D2XH %.6f D2H %.6f]" % (M1, dH, XH, DXH, D2XH, D2H))
    # ---------------- Gram
    t1 = time.time()
    def dot(i, j):
        terms = [X.mul(DK[r][i], DK[r][j]) for r in (0, 2, 3)]
        s = madd(*terms)
        if i == 1 and j == 1:
            s = s.add(one)
        return X.red(s)
    G = [[dot(0, 0), dot(0, 1)], [None, dot(1, 1)]]
    G[1][0] = G[0][1]
    log("  Gram models: sizes %d %d %d, radii %.2e %.2e %.2e (%.1fs)" % (
        len(G[0][0]), len(G[0][1]), len(G[1][1]), G[0][0].r, G[0][1].r, G[1][1].r, time.time() - t1))
    # approximate inverse on a real grid
    N1, N2 = 512, 128
    g = [[G[i][j].eval_grid(N1, N2) for j in range(2)] for i in range(2)]
    det = g[0][0] * g[1][1] - g[0][1] * g[1][0]
    inv = [[g[1][1] / det, -g[0][1] / det], [-g[1][0] / det, g[0][0] / det]]
    Bm = [[None, None], [None, None]]
    for i in range(2):
        for j in range(2):
            if j < i:
                continue
            C = np.fft.fft2(inv[i][j]) / (N1 * N2)
            kk = np.fft.fftfreq(N1, 1 / N1).astype(int); ll = np.fft.fftfreq(N2, 1 / N2).astype(int)
            d = {}
            for a in range(N1):
                for c in range(N2):
                    x = C[a, c].real
                    if abs(x) > 1e-16:
                        d[(int(kk[a]), int(ll[c]))] = int(round(x * 2**48))
            Bm[i][j] = SPoly.from_dict(d, 48, 0)
    Bm[1][0] = Bm[0][1]
    beta = max(addu(Bm[0][0].norm(Wt), Bm[0][1].norm(Wt)), addu(Bm[1][0].norm(Wt), Bm[1][1].norm(Wt)))
    IBG = [[None, None], [None, None]]
    for i in range(2):
        for j in range(2):
            s = X.mul(Bm[i][0], G[0][j]).add(X.mul(Bm[i][1], G[1][j]))
            if i == j:
                s = SPoly.const(1, SN).sub(s)
            else:
                s = s.neg()
            IBG[i][j] = X.red(s)
    delta = max(addu(IBG[0][0].norm(Wt), IBG[0][1].norm(Wt)), addu(IBG[1][0].norm(Wt), IBG[1][1].norm(Wt)))
    assert delta < 1
    ginv = up(beta / (1 - delta) * (1 + 1e-15))
    epsB = up(delta * beta / (1 - delta) * (1 + 1e-15))
    # sampled sup (diagnostic only): corners of the polystrip
    samp = 0.0
    for (yp, yf) in [(0.999 * float(RHO), 0.999 * float(RHO)), (0.999 * float(RHO), -0.999 * float(RHO))]:
        gg = [[G[i][j].eval_grid(N1, N2, yp, yf) for j in range(2)] for i in range(2)]
        dt = gg[0][0] * gg[1][1] - gg[0][1] * gg[1][0]
        samp = max(samp, float((np.abs(gg[1][1] / dt) + np.abs(gg[0][1] / dt)).max()),
                   float((np.abs(gg[1][0] / dt) + np.abs(gg[0][0] / dt)).max()))
    beta_grid = grid_rowsum_sup(Bm, Wt)
    ginv_grid = up(beta_grid / (1 - delta) * (1 + 1e-15))
    log("  Gram inverse ALTERNATIVE (grid + Lipschitz on the distinguished boundary): sup||B|| <= %.6f -> %.6f" % (
        beta_grid, ginv_grid))
    out["gram"] = dict(beta=beta, delta=delta, Ginv_rowsum_bound=ginv, Ginv_minus_B=epsB, sampled_sup=samp,
                       beta_grid_alternative=beta_grid, Ginv_rowsum_bound_grid_alternative=ginv_grid,
                       B_terms=[len(Bm[0][0]), len(Bm[0][1]), len(Bm[1][1])])
    out["B"] = {"B11": Bm[0][0].to_dict(), "B12": Bm[0][1].to_dict(), "B22": Bm[1][1].to_dict(), "scale_bits": 48}
    log("  Gram inverse: beta %.6f delta %.3e -> ||G^-1|| <= %.6f  (sampled sup %.6f; B terms %s) (%.1fs)" % (
        beta, delta, ginv, samp, out["gram"]["B_terms"], time.time() - t1))
    # ---------------- torsion (c = 1, omega' = (nu - 1, 1))
    t1 = time.time()
    Gi = [[Bm[i][j].round_to(SN, Wt) for j in range(2)] for i in range(2)]
    for i in range(2):
        for j in range(2):
            Gi[i][j] = Gi[i][j].copy(); Gi[i][j].r = addu(Gi[i][j].r, epsB)
    # Omega0 DK: rows (-DK[2], -DK[3], DK[0], DK[1])
    ODK = [[DK[2][j].neg() for j in range(2)], [DK[3][j].neg() for j in range(2)], DK[0], DK[1]]
    def matmul(Am, Bmat, nr, nk, nc):
        return [[X.red(madd(*[X.mul(Am[i][k], Bmat[k][j]) for k in range(nk)])) for j in range(nc)] for i in range(nr)]
    N = matmul(ODK, Gi, 4, 2, 2)
    # D_omega DK (theta units): 2 pi Dt of the theta-unit entries
    DKw = [[X.twopi(X.Dt(dv[j])) for j in range(2)],
           [SPoly.zero(SN, 1), SPoly.zero(SN, 1)],
           [X.twopi(X.twopi(X.Dt(dp[j]))) for j in range(2)],
           [X.twopi(X.twopi(X.Dt(dP2[j]))) for j in range(2)]]
    DKwT = [[DKw[r][i] for r in range(4)] for i in range(2)]
    DKT = [[DK[r][i] for r in range(4)] for i in range(2)]
    A1 = matmul(DKwT, DK, 2, 4, 2); A2 = matmul(DKT, DKw, 2, 4, 2)
    DG = [[X.red(A1[i][j].add(A2[i][j])) for j in range(2)] for i in range(2)]
    T1 = matmul(Gi, DG, 2, 2, 2)
    DGi = [[r.neg() for r in row] for row in matmul(T1, Gi, 2, 2, 2)]
    M1m = matmul(DKw, Gi, 4, 2, 2); M2m = matmul(DK, DGi, 4, 2, 2)
    S_ = [[X.red(M1m[i][j].add(M2m[i][j])) for j in range(2)] for i in range(4)]
    DN = [[S_[2][j].neg() for j in range(2)], [S_[3][j].neg() for j in range(2)], S_[0], S_[1]]
    # composed V-derivatives: cos X_m(K) ~ Re_an(e_s E~), sin X_m(K) ~ Im_an(e_s E~), radius w^|s| Delta
    Eh = E.round_to(SN, Wt, THR)
    def ReIm(s, im):
        a = Eh.shift(s)
        b = SPoly(-Eh.k - s[0], -Eh.l - s[1], Eh.v, Eh.S, 0, Eh.r)
        if im:
            f = a.sub(b)                                     # (A - B)/(2i) = i (B - A)/2
            f = SPoly(f.k, f.l, -f.v, f.S + 1, 1, f.r)
        else:
            f = a.add(b); f = SPoly(f.k, f.l, f.v, f.S + 1, 0, f.r)
        ws = up(F(Wt.W[abs(s[0]) + abs(s[1])], 1 << WB))      # |e_{+-s}| <= w^|s| on the strip
        f.r = addu(mulu(f.r, ws), mulu(ws, Delta))
        return X.red(f)
    VQQ = [[SPoly.zero(SN, 0) for _ in range(2)] for _ in range(2)]
    VQ = [SPoly.zero(SN, 1), SPoly.zero(SN, 1)]
    for m, (a, d) in SH.items():
        Cm = ReIm((a, d), False); Sm = ReIm((a, d), True)
        dd = (a, d)
        for i in range(2):
            if dd[i]:
                VQ[i] = VQ[i].add(X.twopi(X.sc(Sm, EPSA[m] * dd[i])))
            for j in range(2):
                if dd[i] * dd[j]:
                    VQQ[i][j] = VQQ[i][j].add(X.sc(Cm, EPSA[m] * dd[i] * dd[j]))
    VQQ = [[X.sc(VQQ[i][j], X.tp2, X.tp2e) for j in range(2)] for i in range(2)]
    # W_b = DX N_b - DN_b ;  DX rows: Q1 -> N_P1 ; Q2 -> 0 ; P_i -> -sum_j VQQ_ij N_Qj
    T = [[None, None], [None, None]]
    Y = [None, None]
    pm1 = X.red(p.sub(SPoly.const(1, p.S)))
    for b in range(2):
        W = [N[2][b].sub(DN[0][b]), DN[1][b].neg(),
             madd(*[X.mul(VQQ[0][j], N[j][b]) for j in range(2)]).neg().sub(DN[2][b]),
             madd(*[X.mul(VQQ[1][j], N[j][b]) for j in range(2)]).neg().sub(DN[3][b])]
        OW = [W[2].neg(), W[3].neg(), W[0], W[1]]
        for a in range(2):
            T[a][b] = X.red(madd(*[X.mul(N[i][a], OW[i]) for i in range(4)]))
        Y[b] = X.red(madd(X.mul(VQ[0], N[0][b]), X.mul(VQ[1], N[1][b]), X.mul(pm1, N[2][b]), N[3][b]))
    s1c = X.s1
    Cc = [[T[0][0].coeff0(), T[0][1].coeff0(), s1c], [T[1][0].coeff0(), T[1][1].coeff0(), F(1)],
          [Y[0].coeff0(), Y[1].coeff0(), F(0)]]
    Rr = [[T[0][0].r, T[0][1].r, X.s1e], [T[1][0].r, T[1][1].r, 0.0], [Y[0].r, Y[1].r, 0.0]]
    # the zero mode is the average of the polynomial part; the remainder's average is bounded by its sup r
    Cf = np.array([[float(x) for x in r] for r in Cc])
    Si = np.linalg.inv(Cf)
    Sq = [[F(int(round(x * 2**40)), 1 << 40) for x in r] for r in Si]
    ISC = [[(1 if i == j else 0) - sum(Sq[i][k] * Cc[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
    nISC = max(up(sum(abs(x) for x in r)) for r in ISC)
    nS = max(up(sum(abs(x) for x in r)) for r in Sq)
    nR = max(addu(*r) for r in Rr)
    dT = addu(nISC, mulu(nS, nR))
    assert dT < 1
    tinv = up(nS / (1 - dT) * (1 + 1e-15))
    out["torsion"] = dict(avg_center=[[str(x) for x in r] for r in Cc], avg_center_float=Cf.tolist(), avg_radius=Rr,
                          S=[[str(x) for x in r] for r in Sq], norm_S=nS, I_minus_SC=nISC, delta_T=dT,
                          inverse_rowsum_bound_c1=tinv, inverse_float=np.abs(Si).sum(axis=1).max())
    log("  torsion avg (c=1):\n%s\n   radii %s\n   ||S|| %.6f  delta_T %.3e -> ||avg^-1|| <= %.6f (float %.6f) (%.1fs)" % (
        np.array2string(Cf, precision=6), ["%.1e" % max(r) for r in Rr], nS, dT, tinv,
        np.abs(Si).sum(axis=1).max(), time.time() - t1))
    out["seconds"] = time.time() - t0
    return out


if __name__ == "__main__":
    from rot_build import build
    which = sys.argv[1]
    L = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    cand = build(which, L, L, L, 3 * L + 40)
    o = norms(cand, cand["bounds"]["Delta"])
    if len(sys.argv) > 3:
        pickle.dump(o, open(sys.argv[3], "wb"))
