#!/usr/bin/env python3
"""HD11964-PILOT self-checks of the gate's conventions.  Untrusted design tooling (Apache-2.0).

1. chart: the Lean chart formula reproduces the action, the AMD and the prograde sign (mpmath, 40 digits);
2. symplecticity of the chart with pairs (lam, Lam), (xi, eta) (finite differences of the Jacobian, mpmath);
3. Hamiltonian identity H o Psi = h(Lam) + mu f o Psi (by construction of f; checked on the Cartesian side);
4. rotation invariance of the gate's residual (numpy);
5. along a direct integration of the Newtonian equations (RK4 in Cartesian coordinates, mpmath-free), the approximate
   integrals F^(N) built at the starting point move far less than Lam: max |F(t) - F(0)| against max |Lam(t) - Lam(0)|.
Writes validation/checks.json.
"""
import json
import math
import os
import sys

import mpmath as mp
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hd11964_model as HM  # noqa: E402
from normal_form import NormalForm  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def symplectic_check(m):
    mp.mp.dps = 40
    nu = [HM.R(x) for x in m.nu]
    ch = m.chart_nominal()
    w0 = [c for planet in ch for c in planet]  # lam0, xi0, Lam0, eta0, lam1, xi1, Lam1, eta1

    def cart(w):
        Q, P = [], []
        for i in range(2):
            q, p = HM.chart_planet(nu[i], *w[4 * i: 4 * i + 4])
            Q += q
            P += p
        return Q + P  # q0x q0y q1x q1y p0x p0y p1x p1y

    h = mp.mpf(10) ** -15
    J = []
    for k in range(8):
        wp = list(w0)
        wm = list(w0)
        wp[k] += h
        wm[k] -= h
        J.append([(a - b) / (2 * h) for a, b in zip(cart(wp), cart(wm))])
    # column k of the Jacobian = d(cart)/dw_k; canonical positions of w: lam_i (4i), xi_i (4i+1); momenta Lam_i, eta_i
    pos = [0, 1, 4, 5]
    mom = [2, 3, 6, 7]

    def omega(a, b):  # standard form on (q, p) = cart[:4], cart[4:]
        return sum(a[k] * b[4 + k] - a[4 + k] * b[k] for k in range(4))

    err = mp.mpf(0)
    for x in range(8):
        for y in range(8):
            target = 0
            if x in pos and y == mom[pos.index(x)]:
                target = 1
            if y in pos and x == mom[pos.index(y)]:
                target = -1
            err = max(err, abs(omega(J[x], J[y]) - target))
    return float(err)


def residual_rotation(m, N=2, theta=0.7):
    nu = [float(HM.R(x)) for x in m.nu]
    mu = float(HM.R(m.mu))
    Lam = [float(m.Lam(i)) for i in range(2)]
    G = [0.004, 0.006]
    out = []
    for rot in (0.0, theta):
        w = [0.4 + rot, 1.9 + rot]
        xi = [math.sqrt(2 * G[i]) * math.cos(w[i]) for i in range(2)]
        eta = [math.sqrt(2 * G[i]) * math.sin(w[i]) for i in range(2)]
        nf = NormalForm(nu, mu, N1=128, N2=64, N=N)
        nf.setup(Lam, xi, eta)
        nf.run()
        out.append([float(np.max(np.abs(a))) for a, _ in nf.residual(N)])
    return out


# ---- direct integration -------------------------------------------------------------------------------------
def field(q, p, nu, mu):
    P = p.sum(axis=0)
    dq = p / nu[:, None] + mu * P
    r3 = np.sum(q * q, axis=1) ** 1.5
    dp = -(nu / r3)[:, None] * q
    d = q[0] - q[1]
    f = mu * nu[0] * nu[1] * d / (d @ d) ** 1.5
    dp[0] -= f
    dp[1] += f
    return dq, dp


def to_chart(q, p, nu):
    """Inverse chart: (lam, xi, Lam, eta) per planet from Cartesian (q, p)."""
    out = []
    for i in range(2):
        qi, pi = q[i], p[i]
        r = math.sqrt(qi @ qi)
        E = (pi @ pi) / (2 * nu[i]) - nu[i] / r
        a = -nu[i] / (2 * E)
        Lam = nu[i] * math.sqrt(a)
        ps2 = pi @ pi
        ev = (ps2 / nu[i] ** 2 - 1 / r) * qi - (qi @ pi) / nu[i] ** 2 * pi
        e = math.sqrt(ev @ ev)
        Gam = Lam * (1 - math.sqrt(1 - e * e))
        vp = math.atan2(ev[1], ev[0])
        xi, eta = math.sqrt(2 * Gam) * math.cos(vp), math.sqrt(2 * Gam) * math.sin(vp)
        ecE = 1 - r / a
        esE = (qi @ pi) / (nu[i] * math.sqrt(a))
        Ean = math.atan2(esE, ecE)
        lam = (Ean - esE) + vp
        out.append((lam, xi, Lam, eta))
    return out


def jet_coeffs(nf, J):
    """Fourier coefficients of every Taylor coefficient of a jet (computed once)."""
    S = nf.S6
    return [(mon, np.fft.fft2(J.c[i]) / (nf.N1 * nf.N2)) for i, mon in enumerate(S.mons[: S.M(J.deg)])]


def jet_eval(nf, JC, lam, u):
    """Evaluate a jet (given by jet_coeffs) at fast angles lam (off grid, by its Fourier series) and local u."""
    k1 = np.fft.fftfreq(nf.N1, 1.0 / nf.N1)
    k2 = np.fft.fftfreq(nf.N2, 1.0 / nf.N2)
    e1 = np.exp(1j * k1 * lam[0])
    e2 = np.exp(1j * k2 * lam[1])
    val = 0.0
    for mon, c in JC:
        val += float(np.real(e1 @ c @ e2)) * float(np.prod([u[v] ** k for v, k in enumerate(mon)]))
    return val


def flow_check(m, N=2, years=20.0, steps_per_inner=300):
    nu = np.array([float(HM.R(x)) for x in m.nu])
    mu = float(HM.R(m.mu))
    ch = m.chart_nominal()
    Q, P = [], []
    for i in range(2):
        q, p = HM.chart_planet(HM.R(m.nu[i]), *ch[i])
        Q.append([float(x) for x in q])
        P.append([float(x) for x in p])
    q, p = np.array(Q), np.array(P)
    c0 = to_chart(q, p, nu)
    Lam0 = [c0[i][2] for i in range(2)]
    xi0 = [c0[i][1] for i in range(2)]
    eta0 = [c0[i][3] for i in range(2)]
    nf = NormalForm(nu, mu, N1=128, N2=64, N=N)
    nf.setup(Lam0, xi0, eta0)
    nf.run()
    JCs = {(Np, i): jet_coeffs(nf, nf.G[Np][i]) for Np in range(1, N + 1) for i in range(2)}
    yu = float(m.years_per_unit())
    T = years / yu
    Pin = 2 * math.pi * (Lam0[0] / nu[0]) ** 3
    dt = Pin / steps_per_inner
    n = int(T / dt)
    rec = []
    every = max(1, steps_per_inner // 4)
    for s in range(n + 1):
        if s % every == 0:
            c = to_chart(q, p, nu)
            lam = [c[0][0], c[1][0]]
            u = [c[0][2] - Lam0[0], c[1][2] - Lam0[1], c[0][1] - xi0[0], c[0][3] - eta0[0], c[1][1] - xi0[1],
                 c[1][3] - eta0[1]]
            row = [s * dt, c[0][2], c[1][2]]
            for Np in range(1, N + 1):
                for i in range(2):
                    row.append(c[i][2] + jet_eval(nf, JCs[(Np, i)], lam, u))
            rec.append(row)
        if s == n:
            break
        k1q, k1p = field(q, p, nu, mu)
        k2q, k2p = field(q + dt / 2 * k1q, p + dt / 2 * k1p, nu, mu)
        k3q, k3p = field(q + dt / 2 * k2q, p + dt / 2 * k2p, nu, mu)
        k4q, k4p = field(q + dt * k3q, p + dt * k3p, nu, mu)
        q = q + dt / 6 * (k1q + 2 * k2q + 2 * k3q + k4q)
        p = p + dt / 6 * (k1p + 2 * k2p + 2 * k3p + k4p)
    R = np.array(rec)
    out = dict(years=years, dt=dt, samples=len(rec),
               Lam_excursion=[float(np.ptp(R[:, 1])), float(np.ptp(R[:, 2]))])
    col = 3
    for Np in range(1, N + 1):
        out[f"F{Np}_excursion"] = [float(np.ptp(R[:, col])), float(np.ptp(R[:, col + 1]))]
        col += 2
    return out


def main():
    m = HM.Model()
    res = {}
    _, _, _, chk = HM.nominal_state(m)
    res["chart_dictionary"] = chk
    res["symplectic_max_error"] = symplectic_check(m)
    res["rotation_invariance_rates"] = residual_rotation(m)
    res["flow_check"] = flow_check(m)
    print(json.dumps(res, indent=1))
    with open(os.path.join(ROOT, "validation", "checks.json"), "w") as fh:
        json.dump(res, fh, indent=1)


if __name__ == "__main__":
    main()
