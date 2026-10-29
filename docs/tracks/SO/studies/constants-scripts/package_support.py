import numpy as np, math
from resid import load, eta
TR = {w: load(w) for w in ['lower', 'upper']}
LS = sorted(TR['lower'].keys())
NV = np.array([max(TR[w][L]['nv'] for w in TR) for L in LS]); NE = np.array([max(TR[w][L]['nE'] for w in TR) for L in LS])
BOX = [max(TR[w][L]['vbox'][0] for w in TR) for L in LS]
def support(frame, rho, Teff, h=2.0):
    e = np.array([max(eta(TR[w], L, frame, rho) for w in TR) for L in LS])
    tgt = Teff - h
    ok = np.where(e <= tgt)[0]; i = ok[0]
    t = (e[i-1] - tgt) / (e[i-1] - e[i]); L = LS[i-1] + t*5
    nv = NV[i-1] + t*(NV[i]-NV[i-1]); ne = NE[i-1] + t*(NE[i]-NE[i-1])
    return L, nv, ne
rows = [
 ("P0 pilot (theta, rho=1/200)", 'theta', 1/200, -99.874 - math.log10(1.0321)),
 ("P1 +rhoinf=rho/1000", 'theta', 1/200, -95.064 - math.log10(1.0321)),
 ("P2 +s=1+1e-6 (gamma=1/21)", 'theta', 1/200, -93.860 - math.log10(1.0321)),
 ("P3 +mu=1/160, m=3.56", 'theta', 1/200, -91.205 - math.log10(1.0321)),
 ("P3' +rho=1/160, m=3.57", 'theta', 1/160, -89.700 - math.log10(1.0321)),
 ("P4 +time scale c=5/4", 'theta', 1/160, -89.409 - math.log10(1.0321)),
 ("R2 rotated, rho=1/70, m=2.84, c=2", 'rot', 1/70, -80.587),
 ("R1 rotated, rho=1/70, m=1.95, c=7/4", 'rot', 1/70, -74.752),
]
base = None
for name, fr, rho, Teff in rows:
    L, nv, ne = support(fr, rho, Teff)
    pairs = (2*nv)*ne
    if base is None: base = (L, pairs)
    print("%-40s Teff=%8.2f  L=%6.1f  bits~%3.0f  v_half=%6.0f v_full=%6.0f E=%6.0f  pairs/pilot=%.3f  L^3/pilot=%.3f" % (
        name, Teff, L, L*3.3219+10, nv, 2*nv, ne, pairs/base[1], (L/base[0])**3))
print("emitted 1e-130 data: v_full 19024, E 18766 (upper), pairs vs pilot-h2:", 19024*18766/base[1])
