from fractions import Fraction as F
import math
from exact_constants import constants
def L(x): return math.log10(float(x)) if float(x)>0 else -math.inf
def L2(x):  # log10 of a big Fraction robustly
    x=F(x); return (math.log10(x.numerator) if x.numerator>0 else 0) - math.log10(x.denominator)
p = dict(n=2, tau=1, rho=F(1,200), rhoinf=F(1,400), M=F(4), sK=F(4), sB=F(4), sT=F(4), mu=F(1,1000), nu=F(1,4), gbar=F(1,42))
c = constants(**p)
g = F(1,42)
thr = g**4*p['rho']**4/c['isoC1']
print("threshold log10", L2(thr))
d0 = c['delta0']; a = c['a']
print("a", a, "delta0", d0)
print("gamma^4:", L2(g**4))
print("delta0^(2a):", L2(d0**int(2*a)))
print("hatcStar:", L2(c['hatcStar']), c['active'])
for k,v in c['terms'].items(): print("  term",k, "%.4e"%float(v), L2(v))
m = 4; n=2
Theta = 4*n*m**3
print("m^37:", 37*math.log10(m))
# decompose step term: hatcStep*2/mu = 2 Theta^3 * m * CDTbord * hatCDelta * 2/mu
print("hatCDelta", float(c['hatCDelta']), L2(c['hatCDelta']))
print("hatcStep", float(c['hatcStep']), L2(c['hatcStep']))
print("2/mu", L2(2/p['mu']))
print("2Theta^3", L2(2*Theta**3), "m", L2(m))
CDT = c['hatcStep']/(2*Theta**3*m*c['hatCDelta'])
print("CDTbord", float(CDT), L2(CDT))
print("hatCE", float(c['hatCE']), L2(c['hatCE']), " 2^(2a)=", L2(F(2)**16))
# rho^4 cancels:
print("rho^4 in C1 and in hypothesis cancel; check: thr == g^4 d0^16 / hatcStar:", thr == g**4*d0**16/c['hatcStar'])
# delta0 decomposition: (rho-rhoinf)/8
print("delta0^16 = (rho-rhoinf)^16 * 8^-16:", L2((p['rho']-p['rhoinf'])**16), L2(F(1,8)**16))
print("  rho^16:", L2(p['rho']**16), " (1-rhoinf/rho)^16:", L2((1-p['rhoinf']/p['rho'])**16))
# displacement coefficient
coef = c['isoC2']/(g**2*p['rho']**2)
print("disp coef", float(coef), "= 2 hatCDelta / (g^2 d0^8):", float(2*c['hatCDelta']/(g**2*d0**8)))
