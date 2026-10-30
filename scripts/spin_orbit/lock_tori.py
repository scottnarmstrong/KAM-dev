#!/usr/bin/env python3
"""SO-LOCK-SCOPE: synchronous periodic orbit and librational invariant tori of the seven-term lunar model.

Untrusted double-precision exploration tooling (no certificate is produced).

Rotated frame, period-one units (model.py): psi = q - phi (turns), t in orbital periods, v = 2*pi*psi.
A librational torus is v = V(theta1, theta2) with theta1 the libration angle (frequency omega) and theta2 = phi;
there is NO linear part in theta1 (degree zero).  The pi-free invariance equation (model.py with the linear part
dropped) is

    R(V) = Dt^2 V + 2 eps sum_m A_m sin(2 pi (2 - m) theta2 + 2 V) = 0,   Dt e_{k,l} = i (omega k + l) e_{k,l}.

Reversibility (psi, phi) -> (-psi, -phi) lets us take V odd in (theta1, theta2) jointly (fixes the theta1 gauge).
The periodic orbit is the theta1-independent solution V*(theta2).  A torus is parametrised by its amplitude
a = Im Vhat(1, 0) * (-2) (so V ~ V* + a sin(2 pi theta1)), the frequency omega being an unknown (bordered Newton).

Elliptic polar coordinates around the periodic orbit (route (a) of the study):
    X = psi - psi*(phi),  Y = (p - 1) - Dpsi*(phi),  Omega = 2 pi omega0,
    I = pi (Omega X^2 + Y^2 / Omega)   (exact action of the linearised libration; dX ^ dY = dI ^ dtheta),
    alpha = atan2(sqrt(Omega) X, Y / sqrt(Omega)) / (2 pi)   (turns),   U = alpha - theta1.
The torus is primary in (alpha, phi; I, J) iff alpha winds once in theta1; we report the Fourier decay of U and I.

    python3 lock_tori.py OUT.json [nx nt]
"""
import sys, json, math
import numpy as np
from model import A_EXACT, EPS

A = {m: float(a) for m, a in A_EXACT.items()}
eps = float(EPS)


class Grid:
    def __init__(self, nx, nt):
        self.nx, self.nt = nx, nt
        self.k = np.fft.fftfreq(nx, 1.0 / nx)
        self.l = np.fft.fftfreq(nt, 1.0 / nt)
        self.t1 = np.arange(nx)[:, None] / nx
        self.t2 = np.arange(nt)[None, :] / nt
        self.ph = {m: 2 * np.pi * (2 - m) * self.t2 for m in A}
        mask = np.ones((nx, nt)); mask[nx // 2, :] = 0; mask[:, nt // 2] = 0
        self.mask = mask

    def sym(self, om):
        return 1j * (om * self.k[:, None] + self.l[None, :])

    def odd(self, f):
        return 0.5 * (f - np.roll(np.flip(f), 1, axis=(0, 1)))

    def proj(self, f):
        return np.real(np.fft.ifft2(np.fft.fft2(f) * self.mask))

    def Dt(self, f, om, power=1):
        return np.real(np.fft.ifft2(np.fft.fft2(f) * self.sym(om) ** power * self.mask))

    def resid(self, V, om):
        s = sum(2 * eps * A[m] * np.sin(self.ph[m] + 2 * V) for m in A)
        return self.proj(self.Dt(V, om, 2) + s)

    def dpot(self, V):
        return sum(4 * eps * A[m] * np.cos(self.ph[m] + 2 * V) for m in A)

    def amp(self, V):
        return -2 * np.imag(np.fft.fft2(V)[1, 0]) / (self.nx * self.nt)


def solve_lin(G, om, c, rhs):
    """Solve Dt^2 h + c h = rhs on the odd masked subspace: dense least squares on the operator columns
    (robust near the resonant symbol omega^2 ~ 4 eps A_2 that stalls a diagonal preconditioner)."""
    nx, nt = G.nx, G.nt
    key = (om, c.tobytes())
    if getattr(G, "_key", None) != key:
        n = nx * nt
        cols = np.empty((n, n))
        for j in range(n):
            e = np.zeros(n); e[j] = 1.0
            h = G.odd(e.reshape(nx, nt))
            cols[:, j] = G.odd(G.proj(G.Dt(h, om, 2) + c * h)).ravel()
        G._key, G._J = key, np.linalg.pinv(cols, rcond=1e-12)
    return G.odd((G._J @ G.odd(rhs).ravel()).reshape(nx, nt))


def newton(G, V, om, a=None, tol=1e-15, it=30):
    """Bordered Newton: unknowns (V odd, omega) with amplitude a fixed (a None: periodic orbit, theta1-free)."""
    for _ in range(it):
        R = G.resid(V, om)
        c = G.dpot(V)
        if a is None:
            h = solve_lin(G, om, c, -R)
            V = V + h
        else:
            # d/d omega of Dt^2 V = 2 (i k)(i (om k + l)) Vhat
            Vh = np.fft.fft2(V)
            dR = np.real(np.fft.ifft2(2 * (1j * G.k[:, None]) * G.sym(om) * Vh * G.mask))
            h1 = solve_lin(G, om, c, -R)
            h2 = solve_lin(G, om, c, -dR)
            r = a - G.amp(V + h1)
            d2 = G.amp(V + h2) - G.amp(V)
            dom = r / d2
            V = V + h1 + dom * h2
            om = om + dom
        if np.max(np.abs(R)) < tol:
            break
    return V, om, float(np.max(np.abs(G.resid(V, om))))


def periodic_orbit(nt=64):
    G = Grid(2, nt)  # theta1-free
    V = np.zeros((2, nt))
    V, _, res = newton(G, V, 0.0)
    return V[0], res


def floquet(Vs):
    """Libration frequency omega0 (cycles/period) of the periodic orbit: monodromy of h'' = -c(t) h (in V units,
    time t in periods: d^2/dt^2 = 4 pi^2 Dt^2)."""
    from scipy.integrate import solve_ivp
    nt = len(Vs)
    Vh = np.fft.fft(Vs) / nt
    l = np.fft.fftfreq(nt, 1.0 / nt)

    def Vat(t):
        return np.real(np.sum(Vh * np.exp(2j * np.pi * l * t)))

    def f(t, y):
        c = sum(4 * eps * A[m] * math.cos(2 * math.pi * (2 - m) * t + 2 * Vat(t)) for m in A)
        return [y[1], -4 * math.pi ** 2 * c * y[0]]
    cols = []
    for y0 in ([1.0, 0.0], [0.0, 1.0]):
        s = solve_ivp(f, (0, 1), y0, method="DOP853", rtol=1e-13, atol=1e-16)
        cols.append(s.y[:, -1])
    tr = cols[0][0] + cols[1][1]
    return math.acos(tr / 2) / (2 * math.pi), tr


def polar(G, V, om, Vs, om0):
    """Polar data (U, I) of a torus on the grid, with winding check."""
    psi = V / (2 * np.pi)
    pm1 = G.Dt(V, om, 1)                      # Dt V = (p - 1) in turns/period divided by... (see below)
    # Dt V = (1/2pi) d/dt (2 pi psi) = dpsi/dt = p - 1  (turns per period)
    ps = np.broadcast_to(Vs[None, :] / (2 * np.pi), V.shape)
    Gs = Grid(2, G.nt)
    pms = np.broadcast_to(Gs.Dt(np.vstack([Vs, Vs]), 0.0, 1)[0][None, :], V.shape)
    Om = 2 * np.pi * om0
    X = psi - ps
    Y = pm1 - pms
    I = np.pi * (Om * X ** 2 + Y ** 2 / Om)
    al = np.arctan2(np.sqrt(Om) * X, Y / np.sqrt(Om)) / (2 * np.pi)
    U = al - G.t1
    U = (U + 0.5) % 1.0 - 0.5
    # winding: U must be continuous (jumps < 1/2) along theta1
    jumps = np.max(np.abs(np.diff(np.vstack([U, U[:1]]), axis=0)))
    return U, I, X, Y, jumps


def decay(f):
    """log10 of max_l |coefficient (k, l)| for each |k| (theta1 decay, sup over the orbital index)."""
    nx, nt = f.shape
    c = np.abs(np.fft.fft2(f)) / (nx * nt)
    k = np.abs(np.fft.fftfreq(nx, 1.0 / nx))[:, None]; l = np.abs(np.fft.fftfreq(nt, 1.0 / nt))[None, :]
    out = {}
    kk = np.broadcast_to(k, c.shape)
    for s in range(0, nx // 2):
        out[s] = float(np.log10(max(np.max(c[kk == s]), 1e-300)))
    return out, c


def width(dec, lo=2):
    """Fit log10|c_k| ~ b - rho * 2 pi k / ln 10 over k >= lo, keeping only coefficients 2 orders above the
    round-off floor (median of the upper half of the k range): analyticity width rho in theta1."""
    ks_all = sorted(dec)
    floor = float(np.median([dec[k] for k in ks_all[len(ks_all) // 2:]]))
    ks = [k for k, v in dec.items() if k >= lo and v > floor + 2]
    if len(ks) < 3:
        return None, None
    x = np.array(ks, float); y = np.array([dec[k] for k in ks])
    b, a = np.polyfit(x, y, 1)
    return float(-b * math.log(10) / (2 * math.pi)), (min(ks), max(ks))


def main(argv):
    out = argv[0]
    nx = int(argv[1]) if len(argv) > 1 else 256
    nt = int(argv[2]) if len(argv) > 2 else 32
    Vs, res0 = periodic_orbit(nt)
    om0, tr = floquet(Vs)
    print("periodic orbit residual %.2e, max |psi*| = %.3e turns, omega0 = %.10f (trace %.12f)" % (
        res0, np.max(np.abs(Vs)) / (2 * np.pi), om0, tr))
    G = Grid(nx, nt)
    rec = dict(nx=nx, nt=nt, omega0=om0, psi_star_max=float(np.max(np.abs(Vs)) / (2 * np.pi)),
               psi_star_hat=[float(x) for x in np.imag(np.fft.fft(Vs) / nt)[:8] / (2 * np.pi)], tori=[])
    V = np.broadcast_to(Vs[None, :], (nx, nt)).copy()
    om = om0
    a = 0.0
    amps = [float(x) for x in argv[3].split(",")] if len(argv) > 3 else [
        0.02, 0.05, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0, 1.1, 1.2, 1.3, 1.4, 1.45, 1.5]
    prev = None
    for at in amps:
        if prev is None:
            V = V + at * np.sin(2 * np.pi * G.t1) * np.ones((1, nt))
        V, om, res = newton(G, V, om, a=at)
        U, I, X, Y, jumps = polar(G, V, om, Vs, om0)
        dV, _ = decay(V - Vs[None, :]); dU, _ = decay(U); dI, _ = decay(I)
        wV = width(dV); wU = width(dU); wI = width(dI)
        # coefficient decay in theta2 (orbital) direction, at the worst theta1 shell
        cU = np.abs(np.fft.fft2(U)) / (nx * nt)
        lt = [float(np.log10(max(np.max(cU[:, l]), 1e-300))) for l in range(0, nt // 2)]
        r = dict(a=at, omega=om, resid=res, psi_amp_deg=float(360 * np.max(np.abs(X))),
                 pm1_max=float(np.max(np.abs(Y + 0))), pm1_total=float(np.max(np.abs(G.Dt(V, om, 1)))),
                 I_min=float(np.min(I)), I_max=float(np.max(I)), I_mean=float(np.mean(I)), winding_jump=float(jumps),
                 width_V=wV[0], width_U=wU[0], width_I=wI[0],
                 decay_U={k: dU[k] for k in list(dU)[:: max(1, nx // 64)]},
                 decay_I={k: dI[k] for k in list(dI)[:: max(1, nx // 64)]},
                 decay_V={k: dV[k] for k in list(dV)[:: max(1, nx // 64)]},
                 decay_U_theta2=lt,
                 dom_dI=None)
        if prev is not None:
            r["dom_dI"] = (om - prev[0]) / (np.mean(I) - prev[1])
        prev = (om, float(np.mean(I)))
        rec["tori"].append(r)
        json.dump(rec, open(out, "w"), indent=1)
        print("a=%.2f omega=%.8f 1/omega-g=%.3f res=%.1e amp=%.2f deg |p-1|<=%.4f I=[%.3e,%.3e] jump=%.3f "
              "width V/U/I = %s/%s/%s" % (at, om, 1 / om - (math.sqrt(5) - 1) / 2, res, r["psi_amp_deg"],
                                          r["pm1_total"], r["I_min"], r["I_max"], jumps,
                                          *("%.4f" % w[0] if w[0] else "-" for w in (wV, wU, wI))))
        sys.stdout.flush()
    json.dump(rec, open(out, "w"), indent=1)


if __name__ == "__main__":
    main(sys.argv[1:])
