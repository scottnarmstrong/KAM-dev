"""Threshold / digits / support for hypothetical sharper theorems (same norm reconstruction as optimize.py)."""
import numpy as np, math, pickle
from cfast import hatc
from norms import H_majorant
import optimize as O
G = O.G
def mfor(frame, rho, mu, c, lam, cal):
    sK, sB, imX, pmax = G['sup'][(frame, lam, rho)]
    tors = G['tors'][(frame, lam)] / c
    Mh, _ = H_majorant(frame, imX, pmax, mu, lam, c)
    return max(1.0, cal['M']*Mh, cal['sK']*sK + mu, cal['sB']*sB + mu, cal['sT']*tors + mu), pmax

def hat_variant(m, mu, nu, two_a, shrink=0.0):
    _, _, cd, terms = hatc(m, mu, nu)
    E = terms['E'] / 2**16 * 2**two_a          # 2^{2a} C_E with the variant's a
    return math.log10(max(E, terms['step'], terms['sum'], terms['nu'])) - shrink

def T_variant(V, frame, rho, mu, c, lam, cal):
    m, pmax = mfor(frame, rho, mu, c, lam, cal)
    gam = O.GAM[frame] * c / (1 + 1e-6)
    nu = 1e-6 * c
    if V['kind'] == 'apost':
        d0 = (rho * (1 - 1e-3)) / 8
        lc = hat_variant(m, mu, nu, V['two_a'], V.get('shrink', 0.0))
        T = 4*math.log10(gam) + V['two_a']*math.log10(d0) - lc
    else:   # HL19/FHL17-style: e < gam^4 d0^{4 tau} / (a1^{4tau} C5), d0 = rho/a3
        d0 = rho / V['a3']
        T = 4*math.log10(gam) + 4*math.log10(d0) - 4*math.log10(V['a1']) - V['logC5']
    pf = pmax if frame == 'theta' else 1.0
    return T, T - math.log10(c*lam*pf), m

def best(V, frame, cal, h=2.0):
    out = None
    for rho in G['rhos'][frame]:
        for mu in [0.002, 0.0061, 0.01, 0.03]:
            for c in np.geomspace(0.7, 2.5, 15):
                for lam in [1.0]:
                    T, Teff, m = T_variant(V, frame, rho, mu, c, lam, cal)
                    r = O.needed_L(frame, rho, Teff - h)
                    if r is None: continue
                    if out is None or r[0] < out['L']:
                        out = dict(rho=rho, mu=mu, c=c, m=m, T=T, L=r[0], NV=r[1], NE=r[2])
    return out

VARS = [
 ('V0 existing theorem (2a=16)', dict(kind='apost', two_a=16)),
 ('V1 kappa=tau+n/2 (Parseval), 2a=12', dict(kind='apost', two_a=12)),
 ('V2 kappa=tau (Russmann), 2a=8', dict(kind='apost', two_a=8)),
 ('V3 kappa=tau and a=2kappa, 2a=4', dict(kind='apost', two_a=4)),
 ('V1+c-iv (polynomial constants /1e6)', dict(kind='apost', two_a=12, shrink=6)),
 ('V2+c-iv (polynomial constants /1e6)', dict(kind='apost', two_a=8, shrink=6)),
 ('V5 HL19/FHL17-style, C5=1e8', dict(kind='hl', a1=2.0, a3=5.0, logC5=8)),
 ('V5 HL19/FHL17-style, C5=1e4', dict(kind='hl', a1=2.0, a3=5.0, logC5=4)),
]
if __name__ == '__main__':
    for calname, cal in [('reconstructed x1.05', dict(M=1.05, sK=1.05, sB=1.05, sT=1.05)), ('pilot-calibrated', O.CAL_PILOT)]:
        print('==', calname)
        for name, V in VARS:
            for frame in ['theta', 'rot']:
                b = best(V, frame, cal)
                if b is None: print(name, frame, 'none'); continue
                print("%-40s %-5s rho=%.4f mu=%.4f c=%.2f m=%.3f log10T=%7.2f  L=%5.1f  v_half=%5.0f  E=%5.0f" % (
                    name, frame, b['rho'], b['mu'], b['c'], b['m'], b['T'], b['L'], b['NV'], b['NE']))
