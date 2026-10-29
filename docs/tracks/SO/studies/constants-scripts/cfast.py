"""Float mirror of exact_constants.constants (n=2,tau=1,cR=1); returns log10 threshold etc."""
import math
from fractions import Fraction as F
from exact_constants import constants as exact_constants

def hatc(m, mu, nu=1e300, n=2):
    Theta = 4*n*m**3; C_X = 5*n**2*m**5; C_T = 2*n*m**2*C_X; C_Omega = 2*n*(n+1)*m
    C_sym = m**2*C_Omega; C_red = 2*n*(n+1)*m**2; C_xi0 = 2*n*m**2*(m*Theta + C_T)
    C_G = 6*n**2*m; C_B = 2*m**2*C_G; C_DN = 2*n*m + m*C_B; C_DX = 2*m**3 + (m + n*Theta)*C_DN
    C_DT = 4*n*m**2*C_DX + 2*n*C_DN*C_X
    hatCS = max(C_xi0, m*Theta + 2*n*m**5); hatCxiN = hatCS + 2*n*m
    hatCg = C_T*hatCxiN + Theta*hatCS + 2*n*m**2*Theta
    hatCxi = max(hatCg, Theta*hatCxiN); hatCDK = 2*m**2*hatCxi
    hatCDelta = max(hatCDK, Theta**2*hatCS)
    CP = m**2 + n + m**3 + C_X
    hatCpartial = CP*hatCxi + 2*m**2*Theta*hatCg
    hatClin = C_red*hatCxi + C_sym*hatCg + Theta*C_Omega*hatCS
    hatCE1 = 4*m**2*Theta**2*hatClin + m*hatCDK**2 + Theta*hatCS*hatCpartial
    hatCE2 = n*Theta**2*(2*n*m + C_Omega)*hatCg + m*hatCDK**2
    hatCE = max(hatCE1, hatCE2)
    CY = n*m*(2*m**2 + C_DN); CDTbord = C_DT + 8*n**2*m**4 + 1 + CY
    hatcStep = 2*Theta**3*max(C_sym, m*CDTbord*hatCDelta)
    hatcSum = 4*Theta**2*hatCDelta*max(n, C_B, m**2*CDTbord)
    terms = dict(E=2**16*hatCE, step=hatcStep*max(1, 2/mu), sum=2*hatcSum/mu, nu=4*Theta**2*hatCDelta/nu)
    k = max(terms, key=terms.get)
    return terms[k], k, hatCDelta, terms

def log10_threshold(m, mu, rho, rhoinf, gamma, nu=1e300):
    hs, k, cd, _ = hatc(m, mu, nu)
    d0 = min(1.0, (rho - rhoinf)/8)
    return 4*math.log10(gamma) + 16*math.log10(d0) - math.log10(hs), k

def log10_disp(m, rho, rhoinf, gamma):
    _, _, cd, _ = hatc(m, 1.0)
    d0 = min(1.0, (rho - rhoinf)/8)
    return math.log10(2*cd) - 2*math.log10(gamma) - 8*math.log10(d0)

if __name__ == "__main__":
    print(log10_threshold(4, 1e-3, 0.005, 0.0025, 1/42, 0.25), math.log10(1.3366048938742373e-100))
    # exact check at another point
    p = dict(n=2, tau=1, rho=F(1,100), rhoinf=F(1,10**6), M=F(3), sK=F(3), sB=F(7,2), sT=F(3), mu=F(1,50), nu=F(1,4), gbar=F(1,21))
    c = exact_constants(**p)
    thr = F(1,21)**4*p['rho']**4/c['isoC1']
    print(math.log10(thr.numerator)-math.log10(thr.denominator), log10_threshold(3.5, 0.02, 0.01, 1e-6, 1/21, 0.25))
