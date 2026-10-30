"""Evaluate the constants of Figueras-Haro 2024 (arXiv 2304.10205v1), Appendix B Tables 1-4, on FH25 SJS data.
Canonical symplectic case, no extra first integrals (d = n = 3): c_Omega=c_G=c_J=c_Jt=1, c_DOmega=c_DG=c_DJ=c_DJt=0,
c_Xp=c_Xpt=c_DXp=c_DXpt=0, c_DPhi=1 (FH24 Remarks 2.20, 2.21).
GUESSES (not in FH25): c_Th = 2 c_DXh, c_DTh = 2 c_D2Xh, nu, kappa, varkappa, dist(K, dU0), Russmann constants.
"""
import math, numpy as np

tau, gam, d, n = 2.4, 1.69e-6, 3, 3
cXh, cDXh, cDXht, cD2Xh = 0.09, 129.0, 129.0, 5e10
cOm, cDOm, cG, cDG, cJ, cDJ, cJt, cDJt = 1, 0, 1, 0, 1, 0, 1, 0
cXp = cXpt = cDXp = cDXpt = 0.0
cDPhi = 1.0
norms0 = dict(DK=4.7811815833, DKt=6.8755882886, B=7.35806411265, N=3.5704498717, Nt=2.8621242724, Tinv=354.07743243)
SIGF = 1 + 1e-10


def zeta2(a):
    return sum(1.0 / (a + j) ** 2 for j in range(400000)) + 1.0 / (a + 400000)


# uniform Russmann constant, FH24 Lemma 2.14 (1-periodic) transported to 2pi-periodic angles by (2pi)^(tau+1)
cRhat_1per = math.sqrt(2 ** (d + 1 - 2 * tau) * zeta2(2**tau) * math.pi ** (-2 * tau - 2) * math.gamma(2 * tau + 1))
cRhat_2pi = (2 * math.pi) ** (tau + 1) * cRhat_1per
c1fac = (tau + 1) ** (tau + 1) / tau**tau


def consts(rho, dl, cR_d, c1R_d, cR_rho, sig, nu, kap, vk, cTh, cDTh):
    s = sig
    sL, sLt, sB, sN, sNt, sT = s['DK'], s['DKt'], s['B'], s['N'], s['Nt'], s['Tinv']
    gd = gam * dl**tau
    c = {}
    # Table 1
    CONL = (d + n - 2) * c1R_d
    CONN = sB**2 * CONL
    Csym = max(CONL, CONN)
    CEL = (sL + sN * nu) / (1 - nu**2); CEN = (sN + sL * nu) / (1 - nu**2); CE = CEL + gd * CEN
    CEtL = n * (sLt + nu * sNt) / (1 - nu**2); CEtN = n * (sNt + nu * sLt) / (1 - nu**2); CEt = CEtL + gd * CEtN
    f = d * (1 + cOm * (sNt * CEL + sLt * CEN))
    CDEL, CDEN = f * CEL, f * CEN; CDE = CDEL + gd * CDEN
    ft = n * (1 + cOm * (sN * CEtL + sL * CEtN))
    CDEtL, CDEtN = ft * CEtL, ft * CEtN; CDEt = CDEtL + gd * CDEtN
    CLK = CE * dl * nu + cXh
    CLL = CDE * nu + cDXp * CE * dl * nu + cDXh * sL
    CLLt = max(CDEt * nu, cDXpt * CE * dl * nu) + sLt * cDXht
    CLGL = CLLt * cG * sL + sLt * cDG * CLK * sL + sLt * cG * CLL
    CLB = sB**2 * CLGL
    CLN = cDJ * CLK * sL * sB + cJ * CLL * sB + cJ * sL * CLB
    CT = sNt * cTh * sN
    ENNL = dl * sLt * cDOm * CEL * sN + max(n + d * CEL * cOm * sNt, dl * cDXpt * CEL * cOm * sN)
    ENNN = dl * sLt * cDOm * CEN * sN + max(d * CEN * cOm * sNt, dl * cDXpt * CEN * cOm * sN)
    ENN = ENNL + gd * ENNN
    ENLL = (d + dl * cDXp) * sLt * cOm * CEL
    ENLN = d + (d + dl * cDXp) * sLt * cOm * CEN
    ELNL = dl * sB**2 * sLt * cG * cDJ * sL * CEL + sB**2 * ENLL
    ELNN = gd * dl * sB**2 * sLt * cG * cDJ * sL * CEN + gd * sB**2 * ENLN + sB * CONL * CLB
    ELN = ELNL + ELNN
    # Table 2
    Cx0L = sT; Cx0N = (dl / rho) ** tau * sT * CT * cR_rho
    CxNL = Cx0L; CxNN = Cx0N + cR_d; CxN = CxNL + CxNN
    CdKbL, CdKbN = sN * CxNL, sN * CxNN; CdKb = CdKbL + CdKbN
    CdDKbL, CdDKbN = d * sN * Cx0L, d * sN * (Cx0N + c1R_d); CdDKb = CdDKbL + CdDKbN
    CdDKtbL, CdDKtbN = n * sNt * Cx0L, n * sNt * (Cx0N + c1R_d); CdDKtb = CdDKtbL + CdDKtbN
    CdLbL, CdLbN = CdDKbL + dl * cDXp * CdKbL, CdDKbN + dl * cDXp * CdKbN; CdLb = CdLbL + CdLbN
    CdLtbL, CdLtbN = max(CdDKtbL, dl * cDXpt * CdKbL), max(CdDKtbN, dl * cDXpt * CdKbN); CdLtb = CdLtbL + CdLtbN
    CEbL = CEL + cDXh * CdKbL + CLN * CxNL
    CEbN = gd * (CEN + sN) + cDXh * CdKbN + CLN * CxNN
    CEb = CEbL + CEbN
    QbN_parts = dict(geom=(CdLtb * cOm + dl * sLt * cDOm * CdKb) * CEb, red=ENN * CxN,
                     D2X=dl * sLt * cOm * 0.5 * cD2Xh * CdKb**2)
    QbN = sum(QbN_parts.values())
    # Table 3
    CxLL = cR_d * (1 + CT * CxNL); CxLN = cR_d * CT * CxNN; CxL = CxLL + CxLN
    CdKbbL = cDPhi * sL * CxLL + gd * CdKbL; CdKbbN = cDPhi * sL * CxLN + gd * CdKbN; CdKbb = CdKbbL + CdKbbN
    CdDKbbL = d * cDPhi * sL * CxLL + gd * CdDKbL; CdDKbbN = d * cDPhi * sL * CxLN + gd * CdDKbN
    CdDKbb = CdDKbbL + CdDKbbN
    CdDKtbbL = 2 * n * cDPhi * sL * CxLL + gd * CdDKtbL; CdDKtbbN = 2 * n * cDPhi * sL * CxLN + gd * CdDKtbN
    CdDKtbb = CdDKtbbL + CdDKtbbN
    CdLbbL = CdDKbbL + dl * cDXp * CdKbbL; CdLbbN = CdDKbbN + dl * cDXp * CdKbbN; CdLbb = CdLbbL + CdLbbN
    CdLtbbL = max(CdDKtbbL, dl * cDXpt * CdKbbL); CdLtbbN = max(CdDKtbbN, dl * cDXpt * CdKbbN)
    CdLtbb = CdLtbbL + CdLtbbN
    CdGL = CdLtbbL * cG * sL + dl * sLt * cDG * CdKbbL * sL + sLt * cG * CdLbbL
    CdGN = CdLtbbN * cG * sL + dl * sLt * cDG * CdKbbN * sL + sLt * cG * CdLbbN
    CdBL, CdBN = sB**2 * CdGL, sB**2 * CdGN; CdB = CdBL + CdBN
    CdNL = dl * cDJ * CdKbbL * sL * sB + cJ * CdLbbL * sB + cJ * sL * CdBL
    CdNN = dl * cDJ * CdKbbN * sL * sB + cJ * CdLbbN * sB + cJ * sL * CdBN
    CdN = CdNL + CdNN
    CdNtL = dl * sB * sL * cDJt * CdKbbL + sB * CdLbbL * cJt + CdBL * sL * cJt
    CdNtN = dl * sB * sL * cDJt * CdKbbN + sB * CdLbbN * cJt + CdBN * sL * cJt
    CdNt = CdNtL + CdNtN
    CdTL_parts = dict(Nt=CdNtL * cTh * sN, DTh=dl * sNt * cDTh * CdKbbL * sN, N=sNt * cTh * CdNL)
    CdTN_parts = dict(Nt=CdNtN * cTh * sN, DTh=dl * sNt * cDTh * CdKbbN * sN, N=sNt * cTh * CdNN)
    CdTL, CdTN = sum(CdTL_parts.values()), sum(CdTN_parts.values()); CdT = CdTL + CdTN
    CdTiL, CdTiN = sT**2 * CdTL, sT**2 * CdTN; CdTi = CdTiL + CdTiN
    CLxL = 1 + CT * CxNL; CLxN = CT * CxNN; CLx = CLxL + CLxN
    CEbbL = cDPhi * (CEbL + sL * CLxL); CEbbN = cDPhi * (CEbN + sL * CLxN); CEbb = CEbbL + CEbbN
    QbbN = (1 + n) * (1 + CONL * CLx * vk) * QbN
    QL1 = ELN * CxN + dl * sNt * cOm * 0.5 * cD2Xh * CdKb**2 + gd * CONN
    QL2 = sNt * cOm * d * CEb * CxL
    QL3 = sNt * cOm * (d * sL * CxL + gd * CdLb) * CLx
    QL4 = sNt * cOm * cDXp * cDPhi * CxL * (CEb + sL * CLx)
    QL5 = (CdNt * cOm + dl * sNt * cDOm * CdKbb) * CEbb
    QbbL_parts = dict(L1=gd * QL1, L2=QL2, L3=QL3, L4=dl * QL4, L5=QL5)
    QbbL = sum(QbbL_parts.values())
    loc = dict(locals())
    return {k: v for k, v in loc.items() if k not in ('s', 'sig', 'c')}


def chat_terms(c, norms, sig, dist, nu, vk, gd):
    """terms of (3.27) Hat C_Delta (Iterative Lemma)"""
    return dict(sym=gd * max(1, c['Csym']) / nu, xiL=c['CxL'], dist=c['dl'] * c['CdKbb'] / dist,
                DK=c['CdDKbb'] / (sig['DK'] - norms['DK']), DKt=c['CdDKtbb'] / (sig['DKt'] - norms['DKt']),
                B=c['CdB'] / (sig['B'] - norms['B']), N=c['CdN'] / (sig['N'] - norms['N']),
                Nt=c['CdNt'] / (sig['Nt'] - norms['Nt']), Tinv=c['CdTi'] / (sig['Tinv'] - norms['Tinv']),
                vk=1 / vk)


def C_terms(c, norms, sig, dist, nu, kap, vk, gd, a):
    """terms of (3.99) C (KAM theorem)"""
    t = chat_terms(c, norms, sig, dist, nu, vk, gd)
    t['dist'] *= a / (a - kap)
    for k in ('DK', 'DKt', 'B', 'N', 'Nt', 'Tinv'):
        t[k] /= (1 - kap)
    Qb = max(c['QbbL'], a**tau * c['QbbN'])
    t['Q'] = a ** (tau + 1) * Qb / kap
    return t
