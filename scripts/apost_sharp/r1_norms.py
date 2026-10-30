#!/usr/bin/env python3
"""Sampled sup norms of the lunar candidate in the rotated frame (package R1 and the harder package H50).

Untrusted tooling, double precision, heuristic (sampled sups, not enclosures).  It measures the objects that the
v2 design (docs/campaign/design/APOST-SHARP-V2.md) lets a certificate bound separately:
    M0 = |X_h|, M1 = |DX_h|, M2 = |D^2 X_h|, |Dh|, |D^2 h|    (sup over the mu-ball around K(T_rho)),
    |DK| = |L|, |L^T|, |B| = |G^{-1}|, |N| = |Omega0 L B|, |N^T| = |B L^T|, sup |T| on T_{rho - delta0}, |<T>^{-1}|.
Norm convention: max norm on vectors, maximum absolute row sum on matrices (the frozen statement's convention).
Sups over the polystrip are sampled on its distinguished boundary (corners (+-y, +-y)), where the plurisubharmonic
row sums attain their maximum; a 256 x 64 grid of real parts.

The geometry (embedding, frame, Hamiltonian majorants by cosh bounds on the mu-neighbourhood) is that of
docs/tracks/SO/studies/constants-scripts/norms.py (CONSTANTS-STUDY), read from this worktree's certificate data.
Usage:  python3 -I scripts/apost_sharp/r1_norms.py [--json OUT]
"""
import json, math, os, sys
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "scripts", "spin_orbit"))
import model  # noqa: E402  (scripts/spin_orbit/model.py: exact model data)

EPS = float(model.EPS)
A = {m: float(a) for m, a in model.A_EXACT.items()}
ALPHA = (79 - math.sqrt(5)) / 3118
OM = np.block([[np.zeros((2, 2)), -np.eye(2)], [np.eye(2), np.zeros((2, 2))]])   # Omega0
JX = np.block([[np.zeros((2, 2)), np.eye(2)], [-np.eye(2), np.zeros((2, 2))]])   # X_H = JX grad H


def load(which, cut=1e-24):
    d = json.load(open(os.path.join(ROOT, "certificates", "lunar-spin-orbit", "%s.json" % which)))
    P = d["scale_bits"]
    return [(k, l, int(n) / 2 ** P) for k, l, n in d["v_sin"] if abs(int(n)) / 2 ** P > cut]


class Cand:
    def __init__(self, which, N1=256, N2=64):
        self.nu = 1 - ALPHA if which == "lower" else 1 + ALPHA
        self.co = load(which)
        self.N1, self.N2 = N1, N2
        self.psi = np.arange(N1)[:, None] / N1 + 0 * np.arange(N2)[None, :]
        self.phi = np.arange(N2)[None, :] / N2 + 0 * np.arange(N1)[:, None]
        self.kk = np.fft.fftfreq(N1, 1 / N1)[:, None] * np.ones((1, N2))
        self.ll = np.fft.fftfreq(N2, 1 / N2)[None, :] * np.ones((N1, 1))

    def fields(self, ypsi, yphi):
        N1, N2 = self.N1, self.N2
        C = np.zeros((N1, N2), complex)
        for k, l, b in self.co:
            w = math.exp(-2 * math.pi * (k * ypsi + l * yphi))
            C[k % N1, l % N2] += b / 2j * w
            C[(-k) % N1, (-l) % N2] += -b / 2j / w
        ev = lambda Ck: np.fft.ifft2(Ck) * N1 * N2
        tk, tl = 2j * math.pi * self.kk, 2j * math.pi * self.ll
        f = {"u": ev(C) / (2 * math.pi), "u_s": ev(C * tk) / (2 * math.pi), "u_f": ev(C * tl) / (2 * math.pi),
             "u_ss": ev(C * tk * tk) / (2 * math.pi), "u_sf": ev(C * tk * tl) / (2 * math.pi),
             "u_ff": ev(C * tl * tl) / (2 * math.pi), "psi": self.psi + 1j * ypsi, "phi": self.phi + 1j * yphi}
        return f

    def geometry(self, ypsi, yphi):
        f = self.fields(ypsi, yphi)
        s = self.nu - 1
        us, uf = f["u_s"], f["u_f"]
        p = self.nu + s * us + uf
        ps = s * f["u_ss"] + f["u_sf"]
        pf = s * f["u_sf"] + f["u_ff"]
        q = f["psi"] + f["phi"] + f["u"]
        ph = f["phi"]
        V = Vq = Vf = Vqq = Vqf = Vff = 0
        for m in range(1, 8):
            X = 2 * math.pi * (2 * q - m * ph)
            a = EPS * A[m]
            cX, sX = np.cos(X), np.sin(X)
            V = V - a * cX
            Vq = Vq + a * 2 * math.pi * 2 * sX
            Vf = Vf + a * 2 * math.pi * (-m) * sX
            Vqq = Vqq + a * (2 * math.pi) ** 2 * 4 * cX
            Vqf = Vqf + a * (2 * math.pi) ** 2 * (-2 * m) * cX
            Vff = Vff + a * (2 * math.pi) ** 2 * m * m * cX
        J = -p * p / 2 - V
        Js = -p * ps - Vq * (1 + us)
        Jf = -p * pf - Vq * (1 + uf) - Vf
        return dict(u=f["u"], us=us, uf=uf, p=p, ps=ps, pf=pf, q=q, ph=ph, J=J, Js=Js, Jf=Jf,
                    Vq=Vq, Vf=Vf, Vqq=Vqq, Vqf=Vqf, Vff=Vff)


def frame_objects(g, c=1.0):
    """Rotated frame: L (..,4,2), DH (..,4), Hessian (..,4,4) of H' = c (P1^2/2 - P1 + P2 + V(Q1+Q2, Q2))."""
    sh = g["u"].shape
    L = np.zeros(sh + (4, 2), complex)
    DH = np.zeros(sh + (4,), complex)
    Hs = np.zeros(sh + (4, 4), complex)
    Ps, Pf = g["ps"] + g["Js"], g["pf"] + g["Jf"]
    L[..., 0, 0] = 1 + g["us"]; L[..., 0, 1] = g["uf"]
    L[..., 1, 1] = 1
    L[..., 2, 0] = g["ps"]; L[..., 2, 1] = g["pf"]
    L[..., 3, 0] = Ps; L[..., 3, 1] = Pf
    DH[..., 0] = c * g["Vq"]; DH[..., 1] = c * (g["Vq"] + g["Vf"]); DH[..., 2] = c * (g["p"] - 1); DH[..., 3] = c
    a, b, d = g["Vqq"], g["Vqf"], g["Vff"]
    Hs[..., 0, 0] = c * a; Hs[..., 0, 1] = Hs[..., 1, 0] = c * (a + b); Hs[..., 1, 1] = c * (a + 2 * b + d)
    Hs[..., 2, 2] = c
    return L, DH, Hs


def rowsum(Mx):
    return float(np.abs(Mx).sum(axis=-1).max())


def objects(cand, ypsi, yphi, c):
    g = cand.geometry(ypsi, yphi)
    L, DH, Hs = frame_objects(g, c)
    G = np.einsum("...ki,...kj->...ij", L, L)
    B = np.linalg.inv(G)
    N = np.einsum("ab,...bk,...kj->...aj", OM, L, B)
    NT = np.swapaxes(N, -1, -2)
    DX = np.einsum("ab,...bc->...ac", JX, Hs)
    Nh = np.fft.fft2(N, axes=(0, 1))
    mult = 2j * math.pi * c * ((cand.nu - 1) * cand.kk + cand.ll)
    DN = np.fft.ifft2(Nh * mult[:, :, None, None], axes=(0, 1))
    XN = np.einsum("...ab,...bj->...aj", DX, N) - DN
    T = np.einsum("...ia,ab,...bj->...ij", NT, OM, XN)
    Y = np.einsum("...a,...aj->...j", DH, N)
    return dict(g=g, L=L, LT=np.swapaxes(L, -1, -2), B=B, N=N, NT=NT, T=T, Y=Y, DH=DH)


def H_parts(imX, pmax, mu, c):
    """Sup over the mu-neighbourhood of the five Hamiltonian quantities, cosh majorants (as norms.py)."""
    tp = 2 * math.pi
    dX = {m: (2, 2 - m) for m in range(1, 8)}
    ch = lambda m: math.cosh(tp * (imX[m] + (abs(dX[m][0]) + abs(dX[m][1])) * mu))
    g1 = [0.0, 0.0]; g2 = np.zeros((2, 2)); g3row = [0.0, 0.0]
    for m in range(1, 8):
        a = EPS * abs(A[m]) * ch(m)
        d = dX[m]
        for i in range(2):
            g1[i] += a * tp * abs(d[i])
            for j in range(2):
                g2[i, j] += a * tp ** 2 * abs(d[i] * d[j])
            g3row[i] += a * tp ** 3 * abs(d[i]) * (abs(d[0]) + abs(d[1])) ** 2
    pm = pmax + mu
    return dict(dH=c * (g1[0] + g1[1]) + c * (pm + 1), XH=c * max(pm, 1, g1[0], g1[1]),
                DXH=c * max(1.0, g2.sum(axis=1).max()), D2XH=c * max(g3row), D2H=c + c * g2.sum())


def measure(which="lower", rho=1 / 70, rhoinf=None, mu=1 / 160, c=7 / 4, lam=3):
    rhoinf = rho / 1000 if rhoinf is None else rhoinf
    delta0 = min(1.0, (rho - rhoinf) / (2 * lam))
    cand = Cand(which)
    out = {}
    for tag, y in (("strip", rho), ("strip_minus_delta0", rho - delta0)):
        acc = dict(L=0.0, LT=0.0, B=0.0, N=0.0, NT=0.0, T=0.0, Y=0.0)
        imX = np.zeros(8); pmax = 0.0
        for (yp, yf) in ((y, y), (y, -y)):
            o = objects(cand, yp, yf, c)
            for k in acc:
                acc[k] = max(acc[k], rowsum(o[k]) if k != "Y" else float(np.abs(o["Y"]).max()))
            gg = o["g"]
            pmax = max(pmax, float(np.abs(gg["p"] - 1).max()))
            for m in range(1, 8):
                imX[m] = max(imX[m], float(np.abs((2 * gg["q"] - m * gg["ph"]).imag).max()))
        out[tag] = acc
        if tag == "strip":
            out["H"] = H_parts(imX, pmax, mu, c)
    o = objects(cand, 0.0, 0.0, c)
    Tavg = o["T"].mean(axis=(0, 1))
    om = c * np.array([cand.nu - 1, 1.0])
    ext = np.zeros((3, 3), complex)
    ext[:2, :2] = Tavg; ext[:2, 2] = om; ext[2, :2] = o["Y"].mean(axis=(0, 1))
    out["real"] = dict(T_sup=rowsum(o["T"]), Tavg=np.real(Tavg).tolist(),
                       Tavg_inv=rowsum(np.linalg.inv(Tavg)), ext_inv=rowsum(np.linalg.inv(ext)),
                       omega_norm=float(np.abs(om).max()))
    out["params"] = dict(which=which, rho=rho, rhoinf=rhoinf, mu=mu, c=c, delta0=delta0)
    return out


def main():
    res = {}
    for name, kw in (("R1", dict(which="lower")),):
        r = measure(**kw)
        res[name] = r
        print("package", name, r["params"])
        print("  Hamiltonian (scaled by c):", {k: round(v, 4) for k, v in r["H"].items()})
        for tag in ("strip", "strip_minus_delta0"):
            print("  sup on %s:" % tag, {k: round(v, 4) for k, v in r[tag].items()})
        print("  real points: sup|T| %.4f  |<T>^-1| %.4g  |<T_ext>^-1| %.4f  |omega| %.4f" % (
            r["real"]["T_sup"], r["real"]["Tavg_inv"], r["real"]["ext_inv"], r["real"]["omega_norm"]))
        print("  <T> =", np.round(r["real"]["Tavg"], 6).tolist())
    if len(sys.argv) > 2 and sys.argv[1] == "--json":
        json.dump(res, open(sys.argv[2], "w"), indent=1)


if __name__ == "__main__":
    main()
