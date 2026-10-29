# symbolic degree analysis of the constants in m (n=2, tau=1, cR=1) using sympy if available
import sympy as sp
m, mu, nu = sp.symbols('m mu nu', positive=True)
n = sp.Integer(2); cR = sp.Integer(1); a = 8
Theta = 4*n*m**3
C_X = 5*n**2*m**5
C_T = 2*n*m**2*C_X
C_Omega = 2*n*(n+1)*cR*m
C_sym = m**2*C_Omega
C_red = 2*n*(n+1)*m**2
C_xi0 = 2*n*m**2*(m*Theta + cR*C_T)
C_G = 6*n**2*m
C_B = 2*m**2*C_G
C_DN = 2*n*m + m*C_B
C_DX = 2*m**3 + (m + n*Theta)*C_DN
C_DT = 4*n*m**2*C_DX + 2*n*C_DN*C_X
# assume branches: hatCS = C_xi0 (check), etc.
hatCS_a = C_xi0; hatCS_b = m*Theta + 2*n*cR*m**5
print("hatCS branches", sp.expand(hatCS_a), "|", sp.expand(hatCS_b))
hatCS = C_xi0
hatCxiN = hatCS + 2*n*cR*m
hatCg = C_T*hatCxiN + Theta*hatCS + 2*n*m**2*Theta
xa = cR*hatCg; xb = Theta*hatCxiN
print("hatCxi branches", sp.expand(xa), "|", sp.expand(xb))
hatCxi = xa
hatCDK = 2*m**2*hatCxi
da = hatCDK; db = Theta**2*hatCS
print("hatCDelta branches", sp.Poly(sp.expand(da),m).LM(), sp.LC(sp.expand(da)), "|", sp.Poly(sp.expand(db),m).LM(), sp.LC(sp.expand(db)))
hatCDelta = hatCDK
CP = m**2 + n + m**3 + C_X
hatCpartial = CP*hatCxi + 2*m**2*Theta*hatCg
hatClin = C_red*hatCxi + C_sym*hatCg + Theta*C_Omega*hatCS
hatCE1 = 4*m**2*Theta**2*hatClin + m*hatCDK**2 + Theta*hatCS*hatCpartial
hatCE2 = n*Theta**2*(2*n*m + C_Omega)*cR*hatCg + m*hatCDK**2
CY = n*m*(2*m**2 + C_DN)
CDTbord = C_DT + 8*n**2*m**4 + 1 + CY
hatcStep = 2*Theta**3*m*CDTbord*hatCDelta
hatcSum = 4*Theta**2*hatCDelta*m**2*CDTbord
for name, e in [("Theta",Theta),("C_X",C_X),("C_T",C_T),("C_xi0",C_xi0),("hatCg",hatCg),("hatCxi",hatCxi),("hatCDelta",hatCDelta),("hatCE1",hatCE1),("hatCE2",hatCE2),("C_DT",C_DT),("CDTbord",CDTbord),("hatcStep",hatcStep),("hatcSum",hatcSum)]:
    p = sp.Poly(sp.expand(e), m)
    print(f"{name:10s} deg {p.degree():3d} LC {p.LC()}  value@4 {float(e.subs(m,4)):.4e} LCterm@4 {float(p.LC()*4**p.degree()):.4e}")
