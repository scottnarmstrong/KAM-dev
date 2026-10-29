import numpy as np, math
import variants as Vv, optimize as O
G = O.G
def best_hl(V, frame, cal, h=2.0):
    out=None
    for rho in G['rhos'][frame]:
        T, Teff, m = Vv.T_variant(V, frame, rho, 0.002, 1.0, 1.0, cal)
        # tie C5 to the size: C5 ~ C5_0 * (m/2)^8
        adj = 8*math.log10(m/2.0)
        T -= adj; Teff -= adj
        r = O.needed_L(frame, rho, Teff - h)
        if r is None: continue
        if out is None or r[0] < out['L']: out = dict(rho=rho, m=m, T=T, L=r[0], NV=r[1], NE=r[2])
    return out
cal = dict(M=1.05, sK=1.05, sB=1.05, sT=1.05)
for logC5 in [4, 8, 12]:
    for frame in ['theta','rot']:
        b = best_hl(dict(kind='hl', a1=2.0, a3=5.0, logC5=logC5), frame, cal)
        print("HL-style C5=1e%d*(m/2)^8 %-5s rho=%.4f m=%.3f log10T=%7.2f L=%5.1f v_half=%5.0f E=%5.0f" % (logC5, frame, b['rho'], b['m'], b['T'], b['L'], b['NV'], b['NE']))
# support vs digits table
print("L  v_half  E  (max over tori)")
for L, nv, ne in zip(O.LS, O.NV, O.NE): print(L, nv, ne)
