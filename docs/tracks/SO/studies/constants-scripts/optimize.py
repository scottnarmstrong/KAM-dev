import numpy as np, pickle, math, sys
from norms import H_majorant
from cfast import log10_threshold
from resid import load, eta
G = pickle.load(open('normgrid.pkl', 'rb'))
TR = {w: load(w) for w in ['lower', 'upper']}
LS = sorted(TR['lower'].keys())
NV = np.array([max(TR[w][L]['nv'] for w in TR) for L in LS]); NE = np.array([max(TR[w][L]['nE'] for w in TR) for L in LS])
ETA = {}
for frame in ['theta', 'rot']:
    for rho in G['rhos'][frame]:
        ETA[(frame, rho)] = np.array([max(eta(TR[w], L, frame, rho) for w in TR) for L in LS])
GAM = {'theta': 1/21, 'rot': 1/42}
# calibration to the pilot's norm table (theta frame, rho = 0.005): pilot / reconstructed
CAL_PILOT = dict(M=2.685769/2.221996, sK=1.679616/1.599046, sB=3.544134/2.298790, sT=1.0)
def needed_L(frame, rho, target):
    e = ETA[(frame, rho)]
    ok = np.where(e <= target)[0]
    if len(ok) == 0 or LS[ok[0]] >= 125: return None
    i = ok[0]
    if i == 0: return LS[0], NV[0], NE[0]
    # linear interpolation between LS[i-1] (fails) and LS[i] (ok)
    t = (e[i-1] - target) / (e[i-1] - e[i])
    L = LS[i-1] + t * (LS[i] - LS[i-1])
    return L, NV[i-1] + t * (NV[i] - NV[i-1]), NE[i-1] + t * (NE[i] - NE[i-1])

SGRID = [1 + 1e-6]
def best_s(m, mu, rho, rhoinf, gam_c, omnorm_c):
    best = None
    for s in SGRID:
        nu = (s - 1) * omnorm_c / s            # ray margin: nu <= (s-1)|omega*|, sigma_omega = 2s-1
        T, br = log10_threshold(m, mu, rho, rhoinf, gam_c / s, nu)
        if best is None or T > best[0]: best = (T, br, s)
    return best
def evaluate(frame, rho, lam, mu, c, cal, h=2.0, rhoinf_frac=1e-3, fixed=None):
    sK, sB, imX, pmax = G['sup'][(frame, lam, rho)]
    tors = G['tors'][(frame, lam)] / c
    Mh, _ = H_majorant(frame, imX, pmax, mu, lam, c)
    m = max(1.0, cal['M'] * Mh, cal['sK'] * sK + mu, cal['sB'] * sB + mu, cal['sT'] * tors + mu)
    T, br, s = best_s(m, mu, rho, rho * rhoinf_frac, GAM[frame] * c, c * 1.0)
    pf = (pmax + 0.0) if frame == 'theta' else 1.0
    Teff = T - math.log10(c * lam * pf)          # threshold on the weighted scalar residual r
    r = needed_L(frame, rho, Teff - h)
    return dict(frame=frame, rho=rho, lam=lam, mu=mu, c=c, m=m, T=T, Teff=Teff, branch=br, s=s,
                L=None if r is None else r[0], NV=None if r is None else r[1], NE=None if r is None else r[2],
                M=cal['M'] * Mh, sK=cal['sK'] * sK, sB=cal['sB'] * sB, sT=cal['sT'] * tors)

def search(frame, cal, lams=None, rhos=None, cs=None):
    best = None
    for lam in (lams or G['lams']):
        for rho in (rhos or G['rhos'][frame]):
            for mu in np.geomspace(1e-4, 0.3, 40):
                for c in (cs or np.geomspace(0.5, 3.0, 40)):
                    r = evaluate(frame, rho, lam, mu, c, cal)
                    if r['L'] is None: continue
                    if best is None or r['L'] < best['L']: best = r
    return best

def fmt(r):
    return ("%s s-1=%.1e rho=%.4f lam=%.2f c=%.3f mu=%.4f | M=%.3f sK=%.3f sB=%.3f sT=%.3f -> m=%.3f | log10 T=%.2f (%s) Teff=%.2f | L=%.1f digits, v half-lattice %.0f, E %.0f"
            % (r['frame'], r['s']-1, r['rho'], r['lam'], r['c'], r['mu'], r['M'], r['sK'], r['sB'], r['sT'], r['m'], r['T'], r['branch'], r['Teff'], r['L'], r['NV'], r['NE']))

if __name__ == '__main__':
    ONE = dict(M=1.0, sK=1.0, sB=1.0, sT=1.0)
    C105 = dict(M=1.05, sK=1.05, sB=1.05, sT=1.05)
    # Baseline: pilot package evaluated the same way
    rho0 = min(G['rhos']['theta'], key=lambda x: abs(x - 0.005))
    print("rho grid point near 0.005:", rho0)
    T0 = -99.874
    pfac = G['sup'][('theta', 1.0, rho0)][3]
    r0 = needed_L('theta', rho0, T0 - math.log10(pfac) - 2.0)
    print("PILOT package (T=1.34e-100), theta, h=2: L=%.1f NV=%.0f NE=%.0f" % r0)
    for name, cal in [('pilot-calibrated', CAL_PILOT), ('reconstructed x1.05', C105), ('reconstructed x1.00', ONE)]:
        print("==", name)
        # in-theorem, theta frame, no scalings
        b = search('theta', cal, lams=[1.0], cs=[1.0]); print(" theta, lam=c=1      :", fmt(b))
        b = search('theta', cal, lams=[1.0]); print(" theta, time scaling :", fmt(b))
        b = search('theta', cal); print(" theta, +action scal :", fmt(b))
        b = search('rot', cal, lams=[1.0], cs=[1.0]); print(" rot,   lam=c=1      :", fmt(b))
        b = search('rot', cal, lams=[1.0]); print(" rot,   time scaling :", fmt(b))
        b = search('rot', cal); print(" rot,   +action scal :", fmt(b))
