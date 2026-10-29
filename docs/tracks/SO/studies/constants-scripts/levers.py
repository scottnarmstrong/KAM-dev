import math, numpy as np
from cfast import log10_threshold, log10_disp, hatc
rho = 0.005
base = log10_threshold(4, 1e-3, rho, rho/2, 1/42, 0.25)[0]
print("P0 pilot %.3f"%base)
r1 = log10_threshold(4, 1e-3, rho, rho*1e-3, 1/42, 0.25)[0]; print("P1 rhoinf=rho/1000 %.3f gain %.3f"%(r1, r1-base))
r2 = log10_threshold(4, 1e-3, rho, rho*1e-3, 1/21, 1e-9)[0]; print("P2 + s->1 (gamma=1/21) %.3f gain %.3f"%(r2, r2-r1))
def bestmu(floor, gamma=1/21, rho=0.005, rhoinf=None, extra=1e-4):
    rhoinf = rho*1e-3 if rhoinf is None else rhoinf
    best=None
    for mu in np.logspace(-4, 0, 800):
        m = max(1.0, floor + mu + extra)
        t,k = log10_threshold(m, mu, rho, rhoinf, gamma, 1e-9)
        if best is None or t > best[0]: best=(t,mu,m,k)
    return best
SB = 3.544134
b = bestmu(SB)
print("P3 best mu: thr %.3f mu %.4f m %.4f branch %s gain %.3f"%(b[0],b[1],b[2],b[3], b[0]-r2))
b4=None
for mu in np.logspace(-4, math.log10(0.45), 400):
    t,k = log10_threshold(4, mu, rho, rho*1e-3, 1/21, 1e-9)
    if b4 is None or t > b4[0]: b4=(t,mu,k)
print("   (m=4 kept, best mu): thr %.3f mu %.4f %s gain over P2 %.3f"%(b4[0], b4[1], b4[2], b4[0]-r2))
MM=2.685769
t,mu,m,k = b
c = m/(MM+0.01)
t4,k4 = log10_threshold(m, mu, rho, rho*1e-3, c/21, 1e-9)
print("P4 time scaling c=%.4f: thr %.3f; eta->c eta, effective thr/c %.3f, gain %.3f"%(c,t4,t4-math.log10(c), t4-math.log10(c)-t))
for mm in [4,3.55,3,2.5,2,1.5,1.2,1.0]:
    hs,k,cd,terms = hatc(mm, 0.05)
    print("m=%.2f log10 hatc*=%.2f (%s)   log10 hatCDelta %.2f"%(mm, math.log10(hs), k, math.log10(cd)))
