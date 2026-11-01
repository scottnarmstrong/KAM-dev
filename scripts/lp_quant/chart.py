#!/usr/bin/env python3
"""LP-QUANT: the complex chart of LP:MAIN Lemmas 7 and 17 and the exact disturbing function (1).

Untrusted design tooling.  Everything is vectorized and holomorphic in the sense that the formulas (18), (19), (46) are
evaluated with bilinear (not Hermitian) squares and principal square roots, on a domain where the code CHECKS that
  - Newton converged and D_F stays away from 0 (Kepler branch point),
  - every (q_i-q_j).(q_i-q_j) and q_i.q_i avoids the cut of the root (|arg| < pi - 0.05) and 0.
A sampled supremum is a LOWER estimate of the true supremum: every sup below is labelled `estimated`.

 chart_planar(nu, I, lam, x, y)          -> q (...,n,2), p (...,n,2), Dmin
 chart_spatial(nu, I, lam, x, y, u, v)   -> q (...,n,3), p (...,n,3), Dmin
 disturbing(nu, q, p)                    -> f, min |w.w|, max |arg w.w|     MAIN (1): f = |sum p|^2/2 - sum nu_i nu_j/|q_i-q_j|
 sup_oracle(...)                         -> estimated sup of |f| on the complex domain
 tube_radius(...)                        -> the literal Lemma 8 tube radius, and the true holomorphy radius
"""
import math
import numpy as np

TP = 2 * math.pi


def _kepler(k, l, lam, iters=40):
    """Solve F - k sin F + l cos F = lam, starting from the first-order inverse; returns F, D_F, residual."""
    F = lam + k * np.sin(lam) - l * np.cos(lam)
    for _ in range(iters):
        sn, cs = np.sin(F), np.cos(F)
        g = F - k * sn + l * cs - lam
        Dg = 1 - k * cs - l * sn
        step = g / Dg
        F = F - step
        if np.all(np.abs(step) < 1e-13):
            break
    sn, cs = np.sin(F), np.cos(F)
    return F, 1 - k * cs - l * sn, np.abs(F - k * sn + l * cs - lam)


def chart_planar(nu, I, lam, x, y):
    """Formulas (18)-(19) for the product chart.  Inputs broadcast; last axis = planet."""
    a = (I / nu) ** 2
    Gam = (x * x + y * y) / 2
    s = 1 - Gam / I
    be = np.sqrt((1 - Gam / (2 * I)) / I)
    k, l = be * x, -be * y
    F, DF, res = _kepler(k, l, lam)
    c, sn = np.cos(F), np.sin(F)
    A11 = 1 - l * l / (1 + s)
    A12 = k * l / (1 + s)
    A22 = 1 - k * k / (1 + s)
    q = np.stack([a * (A11 * c + A12 * sn - k), a * (A12 * c + A22 * sn - l)], axis=-1)
    fac = nu / np.sqrt(a) / DF
    p = np.stack([fac * (-A11 * sn + A12 * c), fac * (-A12 * sn + A22 * c)], axis=-1)
    return q, p, np.abs(DF), res


def chart_spatial(nu, I, lam, x, y, u, v):
    """Formula (46): rotate the planar vectors by R(t), t = (u,-v,0)/(2 sqrt G), G = I - Gamma."""
    q2, p2, DF, res = chart_planar(nu, I, lam, x, y)
    Gam = (x * x + y * y) / 2
    G = I - Gam
    t1, t2 = u / (2 * np.sqrt(G)), -v / (2 * np.sqrt(G))
    tt = t1 * t1 + t2 * t2
    c = np.sqrt(1 - tt)

    def rot(w):
        w1, w2 = w[..., 0], w[..., 1]
        # R w = (1-2|t|^2) w + 2 t (t.w) + 2 c t x w, with w3 = 0, t3 = 0
        td = t1 * w1 + t2 * w2
        return np.stack([(1 - 2 * tt) * w1 + 2 * t1 * td,
                         (1 - 2 * tt) * w2 + 2 * t2 * td,
                         2 * c * (t1 * w2 - t2 * w1)], axis=-1)

    return rot(q2), rot(p2), DF, res


def disturbing(nu, q, p):
    """Exact f of (1) on (...,n,d) arrays; bilinear squares, principal root; also the worst denominator data."""
    n = q.shape[-2]
    P = np.sum(p, axis=-2)
    f = 0.5 * np.sum(P * P, axis=-1)
    wmin = np.full(f.shape, np.inf)
    amax = np.zeros(f.shape)
    for i in range(n):
        ww = np.sum(q[..., i, :] ** 2, axis=-1)
        wmin = np.minimum(wmin, np.abs(ww))
        amax = np.maximum(amax, np.abs(np.angle(ww)))
        for j in range(i + 1, n):
            w = q[..., i, :] - q[..., j, :]
            ww = np.sum(w * w, axis=-1)
            f = f - nu[i] * nu[j] / np.sqrt(ww)
            wmin = np.minimum(wmin, np.abs(ww))
            amax = np.maximum(amax, np.abs(np.angle(ww)))
    return f, wmin, amax


def _real_slow(rng, N, n, m, I0, Cball):
    """Real slow points of the ball |z|^2/2 <= Cball, m slow pairs per planet in {1,2}: half uniform on the sphere and
    half concentrated on one adjacent pair, split so that both AMD shares are large (the near-contact configurations)."""
    d = 2 * n * m
    z = rng.normal(size=(N, d))
    if n >= 2:
        conc = rng.random(N) < 0.7
        idx = np.nonzero(conc)[0]
        pair = rng.integers(0, n - 1, size=len(idx))
        share = rng.beta(2, 2, size=len(idx))
        z[idx] *= 0.02
        ang0 = rng.uniform(0, TP, size=len(idx))
        spread = rng.normal(scale=0.3, size=len(idx))
        for t, (i, sh, a0, sp) in enumerate(zip(pair, share, ang0, spread)):
            r1, r2 = math.sqrt(2 * sh), math.sqrt(2 * (1 - sh))
            z[idx[t], 2 * m * i] = r1 * math.cos(a0)
            z[idx[t], 2 * m * i + 1] = r1 * math.sin(a0)
            z[idx[t], 2 * m * (i + 1)] = -r2 * math.cos(a0 + sp)
            z[idx[t], 2 * m * (i + 1) + 1] = -r2 * math.sin(a0 + sp)
    z /= np.sqrt(np.sum(z * z, axis=1, keepdims=True))
    rad = np.sqrt(2 * Cball) * rng.random(N) ** (1.0 / 8)  # weight towards the sphere
    return z * rad[:, None]


class Domain:
    """The complex domain (22): |I - I0| < rc, |Im lam| < rho, dist_inf(z, ball) < b, for one centre."""

    def __init__(self, nu, I0, Cball, rho, b, rc, spatial=False):
        self.nu, self.I0, self.Cball, self.rho, self.b, self.rc, self.spatial = nu, I0, Cball, rho, b, rc, spatial
        self.n = len(I0)
        self.m = 2 if spatial else 1

    def draw(self, rng, N):
        n, m = self.n, self.m
        lamr = rng.uniform(0, TP, size=(N, n))
        lami = self.rho * rng.choice([-1.0, 1.0], size=(N, n))
        zr = _real_slow(rng, N, n, m, self.I0, self.Cball)
        phz = rng.uniform(0, TP, size=zr.shape)
        Iph = rng.uniform(0, TP, size=(N, n))
        return dict(lamr=lamr, lami=lami, zr=zr, phz=phz, Iph=Iph)

    def perturb(self, rng, st, scale):
        out = {}
        out["lamr"] = st["lamr"] + scale * rng.normal(size=st["lamr"].shape)
        flip = rng.random(st["lami"].shape) < 0.05 * min(1, scale * 4)
        out["lami"] = np.where(flip, -st["lami"], st["lami"])
        z = st["zr"] + scale * math.sqrt(2 * self.Cball) * 0.3 * rng.normal(size=st["zr"].shape)
        nz = np.sqrt(np.sum(z * z, axis=1, keepdims=True))
        rmax = math.sqrt(2 * self.Cball)
        out["zr"] = z * np.minimum(1.0, rmax / np.maximum(nz, 1e-300))
        out["phz"] = st["phz"] + scale * rng.normal(size=st["phz"].shape)
        out["Iph"] = st["Iph"] + scale * rng.normal(size=st["Iph"].shape)
        return out

    def evaluate(self, st):
        n, m = self.n, self.m
        lam = st["lamr"] + 1j * st["lami"]
        z = st["zr"] + self.b * np.exp(1j * st["phz"])
        I = self.I0 + self.rc * np.exp(1j * st["Iph"])
        if self.spatial:
            x, y, u, v = z[:, 0::4], z[:, 1::4], z[:, 2::4], z[:, 3::4]
            q, p, DF, res = chart_spatial(self.nu, I, lam, x, y, u, v)
        else:
            x, y = z[:, 0::2], z[:, 1::2]
            q, p, DF, res = chart_planar(self.nu, I, lam, x, y)
        f, wmin, amax = disturbing(self.nu, q, p)
        return f, np.min(DF, axis=1), wmin, amax, np.max(res, axis=1)


def sup_oracle(dom, seed=1, N=20000, rounds=10, keep=400):
    """Estimated sup |f| on the domain: random start then a shrinking random ascent.
    `ok` is False when a sample meets a singularity (domain not inside the holomorphy region)."""
    rng = np.random.default_rng(seed)
    st = dom.draw(rng, N)
    best, dmin, wmin_all, amax_all = 0.0, np.inf, np.inf, 0.0
    ok = True
    scale = 0.3
    for it in range(rounds + 1):
        f, DF, wmin, amax, res = dom.evaluate(st)
        good = (res < 1e-9) & (DF > 1e-3) & (amax < math.pi - 0.05) & (wmin > 0) & np.isfinite(np.abs(f))
        if not np.all(good):
            ok = False
        vals = np.where(good, np.abs(f), 0.0)
        # both objectives: the largest |f| and the nearest singularity
        dmin = min(dmin, float(np.min(DF)))
        wmin_all = min(wmin_all, float(np.min(wmin)))
        amax_all = max(amax_all, float(np.max(amax)))
        best = max(best, float(np.max(vals)))
        if it == rounds:
            break
        o1 = np.argsort(-vals)[:keep // 2]
        o2 = np.argsort(wmin)[:keep // 2]
        o = np.concatenate([o1, o2])
        rep = N // len(o)
        seeds = {k: np.repeat(v[o], rep, axis=0) for k, v in st.items()}
        st = dom.perturb(rng, seeds, scale)
        scale *= 0.75
    return dict(M=best, ok=ok, DFmin=dmin, wmin=wmin_all, argmax=amax_all)


def holo_rho(nu, I0, Cball, b, rc, spatial=False, hi=1.5, tol=0.01, seed=3, N=8000):
    """Largest strip rho for which the sampled domain stays inside the holomorphy region (estimated; an upper estimate of
    the true width, because a sample can miss the singularity)."""
    lo = 0.0
    while hi - lo > tol:
        mid = 0.5 * (lo + hi)
        r = sup_oracle(Domain(nu, I0, Cball, mid, b, rc, spatial), seed=seed, N=N, rounds=6, keep=200)
        if r["ok"]:
            lo = mid
        else:
            hi = mid
    return lo


def real_gaps(nu, I0, Cball, N=40000, seed=5):
    """Real sampled (d, Q): min and max over the real ball of |q_i|, |q_i-q_j|: the d and Q of Lemma 8's denominator
    estimate.  Exact values at contact are in geometry.py; this one is for a sanity comparison."""
    dom = Domain(nu, I0, Cball, 0.0, 0.0, 0.0)
    rng = np.random.default_rng(seed)
    st = dom.draw(rng, N)
    x, y = st["zr"][:, 0::2], st["zr"][:, 1::2]
    q, p, DF, res = chart_planar(nu, I0 + 0j, st["lamr"] + 0j, x + 0j, y + 0j)
    n = len(I0)
    dist = []
    for i in range(n):
        dist.append(np.sqrt(np.sum(np.abs(q[:, i]) ** 2, axis=-1)))
        for j in range(i + 1, n):
            dist.append(np.sqrt(np.sum(np.abs(q[:, i] - q[:, j]) ** 2, axis=-1)))
    D = np.stack(dist)
    return float(D.min()), float(D.max())


def lemma8_radius(nu, I0, Cball, d, Q, seed=7, N=8000, hi=2.0):
    """The literal tube of Lemma 8's force-denominator step: largest uniform sup-norm radius R (all chart coordinates) such
    that the sampled complex tube has |w.w - |w_0|^2| <= d^2/2 for every denominator (MAIN line 269-271: the criterion with
    Q, d).  Sampled, so `estimated`; the same quantity by hand is smaller still."""
    lo = 0.0
    n = len(I0)

    def test(R):
        rng = np.random.default_rng(seed)
        dom = Domain(nu, I0, Cball, R, R, min(R, 0.45 * float(np.min(I0))))
        st = dom.draw(rng, N)
        f, DF, wmin, amax, res = dom.evaluate(st)
        lam0 = st["lamr"] + 0j
        z0 = st["zr"] + 0j
        x0, y0 = z0[:, 0::2], z0[:, 1::2]
        q0, p0, _, _ = chart_planar(nu, I0 + 0j, lam0, x0, y0)
        lam = st["lamr"] + 1j * st["lami"]
        z = st["zr"] + dom.b * np.exp(1j * st["phz"])
        I = I0 + dom.rc * np.exp(1j * st["Iph"])
        q, p, DF, res = chart_planar(nu, I, lam, z[:, 0::2], z[:, 1::2])
        worst = 0.0
        for i in range(n):
            for j in range(i, n):
                w = q[:, i] - (q[:, j] if j > i else 0)
                w0 = q0[:, i] - (q0[:, j] if j > i else 0)
                worst = max(worst, float(np.max(np.abs(np.sum(w * w, axis=-1) - np.sum(np.abs(w0) ** 2, axis=-1)))))
        return bool(np.all(res < 1e-9)) and worst <= d * d / 2

    for _ in range(14):
        mid = 0.5 * (lo + hi)
        if test(mid):
            lo = mid
        else:
            hi = mid
    return lo


def single_planet_arrays(nu_i, I_i, zi, N, spatial=False):
    """q(lam), p(lam) of one planet on the uniform grid of N angles (real lam), for FFT work.  zi = (x,y) or (x,y,u,v)."""
    lam = TP * np.arange(N) / N
    nu_a = np.array([nu_i])
    if len(zi) == 4:
        q, p, DF, res = chart_spatial(nu_a, I_i + 0j, lam[:, None] + 0j, zi[0] + 0j, zi[1] + 0j, zi[2] + 0j, zi[3] + 0j)
    else:
        q, p, DF, res = chart_planar(nu_a, I_i + 0j, lam[:, None] + 0j, zi[0] + 0j, zi[1] + 0j)
    return q[:, 0, :], p[:, 0, :]


def pair_grid(nu_i, nu_j, qi, pi, qj, pj):
    """f_ij(lam_i, lam_j) = p_i.p_j - nu_i nu_j/|q_i-q_j| on the N x N grid (index [i_lam, j_lam])."""
    dq = qi[:, None, :] - qj[None, :, :]
    r = np.sqrt(np.sum(dq * dq, axis=-1))
    return np.real(np.sum(pi[:, None, :] * pj[None, :, :], axis=-1) - nu_i * nu_j / r)


def self_grid(pi):
    """f_i(lam_i) = |p_i|^2/2."""
    return np.real(0.5 * np.sum(pi * pi, axis=-1))


def fundamental_check():
    """Self-test: energy, angular momentum and eccentricity of the chart, and symplecticity of the map by finite differences."""
    nu = np.array([1.0, 0.3])
    I = np.array([2.2, 0.9])
    lam = np.array([0.7, 2.1])
    x, y = np.array([0.1, -0.05]), np.array([0.03, 0.08])
    q, p, DF, res = chart_planar(nu, I + 0j, lam + 0j, x + 0j, y + 0j)
    q, p = q.real, p.real
    E = np.sum(p * p, axis=-1) / (2 * nu) - nu / np.sqrt(np.sum(q * q, axis=-1))
    err_E = np.max(np.abs(E + nu ** 3 / (2 * I ** 2)))
    G = q[:, 0] * p[:, 1] - q[:, 1] * p[:, 0]
    err_G = np.max(np.abs(G - (I - (x * x + y * y) / 2)))

    def full(v):
        q, p, _, _ = chart_planar(nu, v[2:4] + 0j, v[0:2] + 0j, v[4:6] + 0j, v[6:8] + 0j)
        return np.concatenate([q.real.ravel(), p.real.ravel()])

    v0 = np.concatenate([lam, I, x, y])
    h = 1e-5
    J = np.zeros((8, 8))
    for i in range(8):
        e = np.zeros(8)
        e[i] = h
        J[:, i] = (full(v0 + e) - full(v0 - e)) / (2 * h)
    Om0 = np.zeros((8, 8))  # dp ^ dq in (q,p)
    for i in range(4):
        Om0[i, 4 + i], Om0[4 + i, i] = 1, -1
    Om1 = J.T @ Om0 @ J
    # dI ^ dlam + dx ^ dy in the order (lam1,lam2,I1,I2,x1,x2,y1,y2)
    Ex = np.zeros((8, 8))
    for i in range(2):
        Ex[i, 2 + i], Ex[2 + i, i] = 1, -1
        Ex[4 + i, 6 + i], Ex[6 + i, 4 + i] = -1, 1
    err_S = min(np.max(np.abs(Om1 - Ex)), np.max(np.abs(Om1 + Ex)))
    # spatial chart: coplanar limit and the angular momentum (45)
    u, v = np.array([0.04, -0.02]), np.array([-0.01, 0.05])
    q3, p3, _, _ = chart_spatial(nu, I + 0j, lam + 0j, x + 0j, y + 0j, u + 0j, v + 0j)
    q3, p3 = q3.real, p3.real
    L = np.cross(q3, p3)
    Gam = (x * x + y * y) / 2
    Z = (u * u + v * v) / 2
    err_3 = np.max(np.abs(L[:, 2] - (I - Gam - Z))) + np.max(np.abs(np.sqrt(np.sum(L * L, axis=-1)) - (I - Gam)))
    return dict(err_energy=float(err_E), err_ang=float(err_G), err_symplectic=float(err_S), err_spatial_L=float(err_3))


if __name__ == "__main__":
    print(fundamental_check())
