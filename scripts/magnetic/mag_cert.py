#!/usr/bin/env python3
"""MAG-2b: certificate data of the eps = 3/2500 magnetic torus in the SO-GEN2 `<which>_rot.json` schema (untrusted
tooling; the sofx mirror and the kernel check whatever this denotes).

    python3 -B mag_cert.py HP_NPZ OUT.json [--cut 1e-24] [--bits 126]

Embedding K(theta) = (theta1 + u, theta2, p, J) of H = J + h(p) + V(q, phi) (frequency (alpha, 1) = s omega*):
  angle 0 = u (odd: u = sum b sin(2 pi k.theta) over half keys, angleDeg 0), angle 1 = 0,
  action 0 = p = p0 + sum c cos, action 1 = J = J0 + sum j cos, J = -(h(p) + V(theta1 + u, theta2)) (energy 0),
  character witnesses E_m = exp(2 pi i m u) under the normalized keys (m, 0), m = 2, 3 (the q-coefficients of the
  two cosine modes of `magHamExpr`; real Fourier coefficients since u is odd), pinHalvings 0;
  approximate Gram inverse B = (DK^T DK)^-1 (even, 48-bit mantissas).
All series are taken from the 256-bit solution of mag_producer.py (`hp-NxN.npz`) and truncated to the keys whose
weighted modulus |c_k| e^{2 pi rho |k|_1} (rho = 3/1000) exceeds --cut; mantissas are at 2^-bits.
"""
import os, sys, json, math, argparse, time
from fractions import Fraction as F
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
os.environ.setdefault("SO_HP_BITS", "256")
import numpy as np
import mag_producer as MP

P = MP.P


def load(npz):
    d = np.load(npz)
    nx, nt = (int(x) for x in d["shape"])
    uim = np.array([int(s) for s in d["uim"]], dtype=object).reshape(nx, nt)
    pre = np.array([int(s) for s in d["pre"]], dtype=object).reshape(nx, nt)
    return nx, nt, uim, pre


def series(H, gr):
    """fixed-point grid -> (re, im) fixed-point Fourier coefficients."""
    return H.fft_n(gr)


def hp_fields(nx, nt, uim):
    H = MP.HPGrid(nx, nt)
    ure = MP.zeros_obj((nx, nt))
    g = MP.Grid(nx, nt)
    _, ut, pd = g.state(1j * MP.to_float(uim))
    u = H.ifft_re(ure, uim)
    Du = H.ifft_re(-H.mul(H.dim, uim), H.mul(H.dim, ure))
    p = H.ginv(H.alpha + Du, MP.fx_float(pd))
    # V(theta + u, phi)
    Er, Ei = H.expi(H.mul(H.twopi, u))
    E2r, E2i = (Er * Er - Ei * Ei) >> P, (2 * Er * Ei) >> P
    E3r, E3i = (E2r * Er - E2i * Ei) >> P, (E2r * Ei + E2i * Er) >> P
    Ca = (E2r * H.pa[0] - E2i * H.pa[1]) >> P
    Cb = (E3r * H.pb[0] - E3i * H.pb[1]) >> P
    c1, c2, ka, ep = H.c["c1"], H.c["c2"], H.c["ka"], H.eps
    A = (c1 * Ca - c2 * Cb) >> P
    V = ((ep * (Ca + Cb)) >> P) + ((((ka * ep >> P) * ep >> P) * ((A * A) >> P)) >> P)
    p2 = H.mul(p, p); p3 = H.mul(p2, p); p4 = H.mul(p3, p)
    h = p - ((3 * p2) >> 2) + (p3 // 3) - (p4 >> 4)
    J = -(h + V)
    out = dict(p=series(H, p), J=series(H, J))
    # E_m as complex grid functions: FFT of (re, im)
    from hpfft import fft2
    for m, (r, i) in ((2, (E2r, E2i)), (3, (E3r, E3i))):
        Fr, Fi = fft2(r, i, -1)
        out["E%d" % m] = (Fr >> H.logN, Fi >> H.logN)
    return out, g, ut, pd


def keys_of(g):
    return g.K.astype(int), g.L.astype(int)


def half(k, l):
    return (k, l) > (0, 0)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("npz"); ap.add_argument("out")
    ap.add_argument("--cut", type=float, default=1e-24)
    ap.add_argument("--bits", type=int, default=126)
    ap.add_argument("--gram-cut", type=float, default=2.0 ** -46)
    a = ap.parse_args()
    t0 = time.time()
    nx, nt, uim, pre = load(a.npz)
    f, g, ut, pd = hp_fields(nx, nt, uim)
    K, L = keys_of(g)
    w = g.w
    sh = P - a.bits                       # fixed point 2^-P -> mantissa 2^-bits
    def rnd(x):
        return (int(x) + (1 << (sh - 1))) >> sh if sh > 0 else int(x) << -sh
    def fl(x):
        return float(x) / 2.0 ** P
    keep = lambda c, i, j: abs(c) * w[i, j] > a.cut
    v_sin, p_cos, J_cos, E = [], [], [], {2: [], 3: []}
    p0 = J0 = None
    pr, Jr = f["p"][0], f["J"][0]
    for i in range(nx):
        for j in range(nt):
            k, l = int(K[i, j]), int(L[i, j])
            if (k, l) == (0, 0):
                p0, J0 = rnd(pr[i, j]), rnd(Jr[i, j])
                continue
            if not half(k, l) or i == nx // 2 or j == nt // 2:
                continue
            ub = -2 * int(uim[i, j])                       # u = sum b sin: u_k = -i b/2
            if keep(fl(ub) / 2, i, j):
                v_sin.append([k, l, str(rnd(ub))])
            pc = 2 * int(pr[i, j])
            if keep(fl(pc) / 2, i, j):
                p_cos.append([k, l, str(rnd(pc))])
            jc = 2 * int(Jr[i, j])
            if keep(fl(jc) / 2, i, j):
                J_cos.append([k, l, str(rnd(jc))])
    for m in (2, 3):
        Er, Ei = f["E%d" % m]
        for i in range(nx):
            for j in range(nt):
                if i == nx // 2 or j == nt // 2:
                    continue
                if keep(fl(Er[i, j]), i, j):
                    E[m].append([int(K[i, j]), int(L[i, j]), str(rnd(Er[i, j]))])
        E[m].sort()
        im_max = max(abs(fl(x)) for x in Ei.ravel())
        print("E%d terms %d, max |Im coef| %.2e" % (m, len(E[m]), im_max), flush=True)
    # Gram inverse (double): L = DK columns d_theta, d_phi of (theta + u, phi, p, J)
    def dgrid(fh, ax):
        k = g.K if ax == 0 else g.L
        return g.inv(2j * np.pi * k * fh * g.mask)
    uh = 1j * MP.to_float(uim)
    ph = MP.to_float(f["p"][0]) + 1j * MP.to_float(f["p"][1])
    Jh = MP.to_float(f["J"][0]) + 1j * MP.to_float(f["J"][1])
    Lm = [[1 + dgrid(uh, 0), dgrid(uh, 1)], [0 * ut, 1 + 0 * ut], [dgrid(ph, 0), dgrid(ph, 1)],
          [dgrid(Jh, 0), dgrid(Jh, 1)]]
    G = [[sum(Lm[r][i] * Lm[r][j] for r in range(4)) for j in range(2)] for i in range(2)]
    det = G[0][0] * G[1][1] - G[0][1] * G[1][0]
    Binv = {"B11": G[1][1] / det, "B12": -G[0][1] / det, "B22": G[0][0] / det}
    gram = dict(scale_bits=48)
    for nm, arr in Binv.items():
        c = g.fwd(arr)
        rows = []
        for i in range(nx):
            for j in range(nt):
                x = round(float(np.real(c[i, j])) * 2 ** 48)
                if x and abs(c[i, j]) * w[i, j] > a.gram_cut:
                    rows.append([int(K[i, j]), int(L[i, j]), str(x)])
        rows.sort()
        gram[nm] = rows
    # domain: strip room and action balls (sampled on the four strip corners, x 1.25 + mu)
    rho, mu = 0.003, 0.002
    def corner_sup(fh, centre):
        s = 0.0
        for sg in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
            wt = np.exp(-2 * np.pi * rho * (sg[0] * g.K + sg[1] * g.L)) * g.mask
            v = np.fft.ifft2(fh * wt) * g.N - centre
            s = max(s, float(np.max(np.abs(v))))
        return s
    supU = corner_sup(uh, 0)
    l1w = lambda fh: float(np.sum(np.abs(fh * g.mask) * w) - abs(fh[0, 0]))     # weighted l1 of the non-constant part
    dsum = rho * (l1w(2j * np.pi * g.K * uh) + l1w(2j * np.pi * g.L * uh))     # rho sum_j sup|d_j u| (checker's a2)
    c1 = round(float(np.real(ph[0, 0])), 4); c2 = round(float(np.real(Jh[0, 0])), 4)
    r1 = (l1w(ph) + abs(float(np.real(ph[0, 0])) - c1)) * 1.03 + mu
    r2 = (l1w(Jh) + abs(float(np.real(Jh[0, 0])) - c2)) * 1.03 + mu
    rhoH = rho + mu + dsum * 1.1
    up = lambda x, d=10 ** 5: str(F(math.ceil(x * d), d))
    dom = dict(sup_U1=supU, rho_dsum=dsum, rho_H=up(rhoH), c1=str(F(c1).limit_denominator(10 ** 5)), r1=up(r1),
               c2=str(F(c2).limit_denominator(10 ** 5)), r2=up(r2))
    out = dict(schema_version=2, frame="magnetic", which="mag", scale_bits=a.bits, J0_scale_bits=a.bits,
               metadata=dict(generator="scripts/magnetic/mag_cert.py", source=os.path.basename(a.npz), cut=a.cut,
                             eps="3/2500", alpha="(7913-sqrt5)/13618", date=time.strftime("%Y-%m-%d")),
               embedding="K(theta) = (theta1 + u, theta2, p, J); u = sum b sin, p = p0 + sum c cos, J = J0 + sum j cos",
               domain=dom, v_sin=sorted(v_sin), p0=str(p0), p_cos=sorted(p_cos), J0=str(J0), J_cos=sorted(J_cos),
               E2_re=E[2], E3_re=E[3], character_witness=dict(keys="(2,0), (3,0)", pinHalvings=0),
               gram_inverse=gram,
               stats=dict(v=len(v_sin), p=len(p_cos), J=len(J_cos), E2=len(E[2]), E3=len(E[3]),
                          B=[len(gram[x]) for x in ("B11", "B12", "B22")], seconds=round(time.time() - t0)))
    json.dump(out, open(a.out, "w"))
    print(json.dumps(dict(domain=dom, stats=out["stats"])), flush=True)


if __name__ == "__main__":
    main()
