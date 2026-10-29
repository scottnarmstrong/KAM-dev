from fractions import Fraction as F
import math
from exact_constants import constants
def lg(x): x = F(x); return math.log10(x.numerator) - math.log10(x.denominator)
def run(name, rho, rhoinf, m, mu, nu, gamma, c=F(1)):
    p = dict(n=2, tau=1, rho=rho, rhoinf=rhoinf, M=m, sK=m, sB=m, sT=m, mu=mu, nu=nu, gbar=gamma)
    k = constants(**p)
    thr = gamma**4 * rho**4 / k['isoC1']
    disp = k['isoC2'] / (gamma**2 * rho**2)
    print("%-48s log10 thr = %8.3f  (thr/c on unscaled residual: %8.3f)  active=%s  disp coef = %.3e  a=%s d0=%s" % (
        name, lg(thr), lg(thr / c), k['active'], float(disp), k['a'], k['delta0']))
    return thr
s = 1 + F(1, 10**6)
run("P0 pilot", F(1,200), F(1,400), F(4), F(1,1000), F(1,4), F(1,42))
run("P1 +rhoinf=rho/1000", F(1,200), F(1,200000), F(4), F(1,1000), F(1,4), F(1,42))
run("P2 +s=1+1e-6 (gamma=1/(21 s)), nu=1e-6", F(1,200), F(1,200000), F(4), F(1,1000), F(1,10**6), F(1,21)/s)
run("P3 +mu=1/160, m=3.56 (pilot table)", F(1,200), F(1,200000), F(356,100), F(1,160), F(1,10**6), F(1,21)/s)
run("P3' theta rho=1/160, m=3.57 (pilot-cal.)", F(1,160), F(1,160000), F(357,100), F(1,160), F(1,10**6), F(1,21)/s)
c = F(5,4)
run("P4 theta +time scaling c=5/4 (pilot-cal.)", F(1,160), F(1,160000), F(357,100), F(1,160), F(1,10**6), c/21/s, c)
c = F(7,4)
run("R1 rot rho=1/70, m=1.95, c=7/4 (recon x1.05)", F(1,70), F(1,70000), F(39,20), F(1,160), F(1,10**6), c/42/s, c)
c = F(2)
run("R2 rot rho=1/70, m=2.84, c=2 (pilot-cal.)", F(1,70), F(1,70000), F(284,100), F(1,160), F(1,10**6), c/42/s, c)
