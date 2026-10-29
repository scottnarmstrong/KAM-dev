"""Reconstruction of the norm package (sigma_K, sigma_B, sigma_T, M) of the lunar candidates, double precision.
Frames: 'theta' (KAM-dev's original angles theta1=psi+phi, theta2=phi; H = p^2/2 + V(q,phi) + J)
        'rot'   (angles (psi,phi); Q1=q-phi, Q2=phi, P1=p, P2=p+J; H' = P1^2/2 - P1 + P2 + V(Q1+Q2,Q2)).
Scalings: actions P -> lam*P with H -> lam*H(Q,P/lam) (conformal), time H -> c*H (omega -> c*omega).
Sup over the open strip is sampled on the distinguished boundary (corners of the polystrip; max principle for the
plurisubharmonic row sums), on a 256x64 grid of real parts.  Heuristic (not enclosed)."""
import json, math, numpy as np
from fractions import Fraction as F
import model
EPS = float(model.EPS); A = {m: float(a) for m, a in model.A_EXACT.items()}
ALPHA = (79 - math.sqrt(5)) / 3118

def load(which, cut=1e-24):
    d = json.load(open('/root/code/KAM/certificates/lunar-spin-orbit/%s.json' % which)); P = d['scale_bits']
    co = [(k, l, int(n) / 2**P) for k, l, n in d['v_sin'] if abs(int(n)) / 2**P > cut]
    return co

class Cand:
    def __init__(self, which, N1=256, N2=64):
        self.which = which; self.nu = 1 - ALPHA if which == 'lower' else 1 + ALPHA
        self.co = load(which); self.N1, self.N2 = N1, N2
        self.psi = np.arange(N1)[:, None] / N1 + 0 * np.arange(N2)[None, :]
        self.phi = np.arange(N2)[None, :] / N2 + 0 * np.arange(N1)[:, None]
        self.kk = np.fft.fftfreq(N1, 1 / N1)[:, None] * np.ones((1, N2))
        self.ll = np.fft.fftfreq(N2, 1 / N2)[None, :] * np.ones((N1, 1))

    def fields(self, ypsi, yphi):
        """u and derivatives at (psi + i ypsi, phi + i yphi) on the grid."""
        N1, N2 = self.N1, self.N2
        C = np.zeros((N1, N2), complex)
        for k, l, b in self.co:
            w = math.exp(-2 * math.pi * (k * ypsi + l * yphi))
            C[k % N1, l % N2] += b / 2j * w            # v = sum b sin = sum b/(2i)(e^{+} - e^{-})
            C[(-k) % N1, (-l) % N2] += -b / 2j / w
        def ev(Ck): return np.fft.ifft2(Ck) * N1 * N2
        tk, tl = 2j * math.pi * self.kk, 2j * math.pi * self.ll
        f = {}
        f['u'] = ev(C) / (2 * math.pi)
        f['u_s'] = ev(C * tk) / (2 * math.pi); f['u_f'] = ev(C * tl) / (2 * math.pi)
        f['u_ss'] = ev(C * tk * tk) / (2 * math.pi); f['u_sf'] = ev(C * tk * tl) / (2 * math.pi)
        f['u_ff'] = ev(C * tl * tl) / (2 * math.pi)
        f['psi'] = self.psi + 1j * ypsi; f['phi'] = self.phi + 1j * yphi
        return f

    def geometry(self, ypsi, yphi):
        f = self.fields(ypsi, yphi); nu = self.nu
        s = nu - 1
        u, us, uf = f['u'], f['u_s'], f['u_f']
        p = nu + s * us + uf
        ps = s * f['u_ss'] + f['u_sf']; pf = s * f['u_sf'] + f['u_ff']
        q = f['psi'] + f['phi'] + u; ph = f['phi']
        V = Vq = Vf = Vqq = Vqf = Vff = 0
        for m in range(1, 8):
            X = 2 * math.pi * (2 * q - m * ph); a = EPS * A[m]
            cX, sX = np.cos(X), np.sin(X)
            V = V - a * cX
            Vq = Vq + a * 2 * math.pi * 2 * sX; Vf = Vf + a * 2 * math.pi * (-m) * sX
            Vqq = Vqq + a * (2 * math.pi)**2 * 4 * cX; Vqf = Vqf + a * (2 * math.pi)**2 * (-2 * m) * cX
            Vff = Vff + a * (2 * math.pi)**2 * m * m * cX
        J = -p * p / 2 - V
        Js = -p * ps - Vq * (1 + us); Jf = -p * pf - Vq * (1 + uf) - Vf
        g = dict(u=u, us=us, uf=uf, p=p, ps=ps, pf=pf, q=q, ph=ph, J=J, Js=Js, Jf=Jf,
                 Vq=Vq, Vf=Vf, Vqq=Vqq, Vqf=Vqf, Vff=Vff)
        return g

def frame_objects(g, frame, lam=1.0, c=1.0):
    """L (..,4,2), DH (..,4), Hess (..,4,4) in the frame's coordinates (scaled)."""
    sh = g['u'].shape
    L = np.zeros(sh + (4, 2), complex); DH = np.zeros(sh + (4,), complex); Hs = np.zeros(sh + (4, 4), complex)
    if frame == 'theta':
        # theta1 = psi+phi, theta2 = phi : d/dtheta1 = d_psi, d/dtheta2 = d_phi - d_psi
        L[..., 0, 0] = 1 + g['us'];          L[..., 0, 1] = g['uf'] - g['us']
        L[..., 1, 0] = 0;                    L[..., 1, 1] = 1
        L[..., 2, 0] = lam * g['ps'];        L[..., 2, 1] = lam * (g['pf'] - g['ps'])
        L[..., 3, 0] = lam * g['Js'];        L[..., 3, 1] = lam * (g['Jf'] - g['Js'])
        DH[..., 0] = c * lam * g['Vq']; DH[..., 1] = c * lam * g['Vf']; DH[..., 2] = c * g['p']; DH[..., 3] = c
        Hs[..., 0, 0] = c * lam * g['Vqq']; Hs[..., 0, 1] = Hs[..., 1, 0] = c * lam * g['Vqf']
        Hs[..., 1, 1] = c * lam * g['Vff']; Hs[..., 2, 2] = c / lam
    else:
        Ps = g['ps'] + g['Js']; Pf = g['pf'] + g['Jf']
        L[..., 0, 0] = 1 + g['us'];  L[..., 0, 1] = g['uf']
        L[..., 1, 0] = 0;            L[..., 1, 1] = 1
        L[..., 2, 0] = lam * g['ps']; L[..., 2, 1] = lam * g['pf']
        L[..., 3, 0] = lam * Ps;      L[..., 3, 1] = lam * Pf
        DH[..., 0] = c * lam * g['Vq']; DH[..., 1] = c * lam * (g['Vq'] + g['Vf'])
        DH[..., 2] = c * (g['p'] - 1); DH[..., 3] = c
        # Hess_QQ = A^{-T} Hth A^{-1}, A^{-1} = [[1,1],[0,1]]
        a, b, d = g['Vqq'], g['Vqf'], g['Vff']
        Hs[..., 0, 0] = c * lam * a; Hs[..., 0, 1] = Hs[..., 1, 0] = c * lam * (a + b)
        Hs[..., 1, 1] = c * lam * (a + 2 * b + d); Hs[..., 2, 2] = c / lam
    return L, DH, Hs

def rowsum(Mx): return np.abs(Mx).sum(axis=-1).max(axis=-1)

OM = np.block([[np.zeros((2, 2)), -np.eye(2)], [np.eye(2), np.zeros((2, 2))]])   # Omega0 (a,b) -> (-b,a)
JX = np.block([[np.zeros((2, 2)), np.eye(2)], [-np.eye(2), np.zeros((2, 2))]])   # X_H = JX grad H

def corners(frame, rho):
    if frame == 'theta':   # (Im th1, Im th2) in {(rho,rho),(rho,-rho)} -> (Im psi, Im phi) = (y1-y2, y2)
        return [(0.0, rho), (2 * rho, -rho)]
    return [(rho, rho), (rho, -rho)]

def sup_package(cand, frame, rho, lam=1.0, c=1.0):
    """sup over the strip of |DK|, |G^-1|, and sup |Im X_m|, sup |p| (for the H-majorant)."""
    sK = sB = 0.0; imX = np.zeros(8); pmax = 0.0
    for (yp, yf) in corners(frame, rho):
        g = cand.geometry(yp, yf)
        L, DH, Hs = frame_objects(g, frame, lam, c)
        G = np.einsum('...ki,...kj->...ij', L, L)
        B = np.linalg.inv(G)
        sK = max(sK, rowsum(L).max()); sB = max(sB, rowsum(B).max())
        pmax = max(pmax, np.abs(g['p'] - (1 if frame == 'rot' else 0)).max())
        for m in range(1, 8):
            imX[m] = max(imX[m], np.abs((2 * g['q'] - m * g['ph']).imag).max())
    return sK, sB, imX, pmax

def torsion_inverse(cand, frame, lam=1.0, c=1.0):
    g = cand.geometry(0.0, 0.0)
    L, DH, Hs = frame_objects(g, frame, lam, c)
    G = np.einsum('...ki,...kj->...ij', L, L); B = np.linalg.inv(G)
    N = np.einsum('ab,...bk,...kj->...aj', OM, L, B)                     # N = Omega0 L B
    DX = np.einsum('ab,...bc->...ac', JX, Hs)
    nu = cand.nu
    om = c * (np.array([nu, 1.0]) if frame == 'theta' else np.array([nu - 1, 1.0]))
    # d_omega N = c * D N with D = (nu-1) d_psi + d_phi (same operator in both frames)
    Nh = np.fft.fft2(N, axes=(0, 1))
    mult = 2j * math.pi * c * ((nu - 1) * cand.kk + cand.ll)
    DN = np.fft.ifft2(Nh * mult[:, :, None, None], axes=(0, 1))
    XN = np.einsum('...ab,...bj->...aj', DX, N) - DN
    T = np.einsum('...ai,ab,...bj->...ij', N, OM, XN)
    Y = np.einsum('...a,...aj->...j', DH, N)
    ext = np.zeros(T.shape[:2] + (3, 3), complex)
    ext[..., :2, :2] = T; ext[..., :2, 2] = om; ext[..., 2, :2] = Y
    avg = ext.mean(axis=(0, 1))
    inv = np.linalg.inv(avg)
    return np.abs(inv).sum(axis=1).max(), avg

def H_majorant(frame, imX, pmax, mu, lam=1.0, c=1.0):
    """sup over D (mu-neighbourhood) of the five H quantities, via cosh majorants."""
    tp = 2 * math.pi
    dX = {m: ((2, -m) if frame == 'theta' else (2, 2 - m)) for m in range(1, 8)}
    def ch(m): return math.cosh(tp * (imX[m] + (abs(dX[m][0]) + abs(dX[m][1])) * mu))
    # V derivatives in the frame's Q coordinates: d^j V = eps A (2pi)^j prod dX ... trig
    g1 = [0.0, 0.0]; g2 = np.zeros((2, 2)); g3row = [0.0, 0.0]
    for m in range(1, 8):
        a = EPS * abs(A[m]) * ch(m); d = dX[m]
        for i in range(2):
            g1[i] += a * tp * abs(d[i])
            for j in range(2):
                g2[i, j] += a * tp**2 * abs(d[i] * d[j])
            g3row[i] += a * tp**3 * abs(d[i]) * (abs(d[0]) + abs(d[1]))**2
    pm = pmax + mu / lam
    dH = c * lam * (g1[0] + g1[1]) + c * (pm + 1)
    XH = c * max(pm, 1, lam * g1[0], lam * g1[1])
    DXH = c * max(1 / lam, lam * g2.sum(axis=1).max())
    D2X = c * lam * max(g3row)
    D2H = c / lam + c * lam * g2.sum()
    return max(dH, XH, DXH, D2X, D2H), dict(dH=dH, XH=XH, DXH=DXH, D2X=D2X, D2H=D2H)

if __name__ == '__main__':
    for which in ['lower', 'upper']:
        cd = Cand(which)
        for frame in ['theta', 'rot']:
            sK, sB, imX, pmax = sup_package(cd, frame, 0.005 if frame == 'theta' else 0.01)
            tinv, avg = torsion_inverse(cd, frame)
            Mh, parts = H_majorant(frame, imX, pmax, 0.001)
            print(which, frame, "sK %.6f sB %.6f Tinv %.6f M %.6f" % (sK, sB, tinv, Mh),
                  {k: round(v, 4) for k, v in parts.items()}, "imX2 %.4f pmax %.4f" % (imX[2], pmax))
            if frame == 'theta': print(np.round(avg, 5))
