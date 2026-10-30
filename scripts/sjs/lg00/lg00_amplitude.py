#!/usr/bin/env python3
"""SJS-LG00: tori of LG00's model (11) further from the elliptic equilibrium than LG00's (amplitude scan).

Untrusted design tooling.  For f in a list, the target actions are f^2 I0 (I0 of the Gamma' torus); the frequency is
the averaged frequency at those actions with its ratio replaced by the nearest noble-type number of the same
continued-fraction prefix (here simply the averaged frequency: these runs test convergence and decay, not
Diophantine data), then the Newton solve of lg00_torus at N = 128 by continuation in f.  Reported: residual,
energy (against LG00's level E), the slowest decay rate (digits per unit |k|_2) and the kept count at L = 12, 13.
Usage: python3 -I lg00_amplitude.py
"""
import os, sys, math, json
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lg00_torus as TT     # noqa: E402
import lg00_model as MM     # noqa: E402

TP = 2 * math.pi


def averaged_freq(form, I):
    h0 = {m: C[TT.KM:TT.KM + 1, TT.KM:TT.KM + 1] for m, C in form.items()}
    A0 = TT.AAHam({m: np.pad(c, TT.KM) for m, c in h0.items()})
    _, g, _ = A0.derivs(np.zeros((1, 2)), np.asarray(I, float)[None, :])
    return g[0, 2:].real


def decay(u, v, I0):
    N = u.shape[0]
    k = np.fft.fftfreq(N, 1 / N)
    k1, k2 = np.meshgrid(k, k, indexing="ij")
    comps = [np.fft.fft2(u[..., i]) / N ** 2 for i in range(2)] + [np.fft.fft2(v[..., i]) / N ** 2 / I0[i] for i in range(2)]
    A = np.max([np.abs(c) for c in comps], axis=0)
    r = np.hypot(k1, k2); al = np.arctan2(k2, k1)
    ok = (A > 1e-13 * A.max()) & (r >= 4)
    slopes = []
    for j in range(36):
        lo, hi = -np.pi + 2 * np.pi * j / 36, -np.pi + 2 * np.pi * (j + 1) / 36
        m = ok & (al >= lo) & (al < hi)
        if m.sum() < 4:
            continue
        rb = np.floor(r[m]).astype(int); lv = np.log10(A[m] / A.max())
        env = {}
        for b, x in zip(rb, lv):
            env[b] = max(env.get(b, -99), x)
        xs = np.array(sorted(env)); ys = np.array([env[x] for x in xs])
        if len(xs) >= 3:
            slopes.append(np.polyfit(xs, ys, 1)[0])
    kept = {L: int((A >= 10.0 ** -L * A.max()).sum()) for L in (8, 12)}
    return max(slopes), kept


def main():
    Q, lam = MM.normal_modes()
    form = TT.action_angle_form(Q)
    base = np.load(os.path.join(HERE, "results", "lg00_torus_N128.npz"))
    I0b = base["I0"]
    N = 128
    G = TT.Grid(N)
    Hm = TT.AAHam(form)
    u = base["u"].copy(); v = base["v"].copy(); I0 = I0b.copy()
    out = []
    for f in (1.0, 1.25, 1.5, 1.75, 2.0, 2.5, 3.0):
        om = averaged_freq(form, f ** 2 * I0b)
        best = None
        for it in range(30):
            u2, v2, I02, err, Tav = TT.newton_step(Hm, G, om, u, v, I0)
            if not np.isfinite(err) or (best is not None and err >= 0.5 * best and err < 1e-15):
                break
            best = err
            u, v, I0 = u2, v2, I02
            if err < 1e-20:
                break
        E, g, Hs, h = TT.residual(Hm, G, om, u, v, I0)
        res = float(np.abs(E).max())
        sl, kept = decay(u, v, I0)
        row = dict(f=f, omega=om.tolist(), I0=I0.tolist(), residual=res, rel_residual=res / float(np.abs(om).max()),
                   energy=float(h.mean()), slowest_digits_per_unit_k=float(sl), kept=kept,
                   max_u=float(np.abs(u).max()), max_v_rel=float(max(np.abs(v[..., i]).max() / I0[i] for i in range(2))))
        out.append(row)
        if f in (2.0, 3.0):
            E2, g2, Hs2, h2 = TT.residual(Hm, G, om, u, v, I0)
            np.savez(os.path.join(HERE, "results", "lg00_torus_f%.0f.npz" % f), u=u, v=v, I0=I0, om=om, Q=Q, lam=lam,
                     err=res, energy=float(h2.mean()), Tavg=Tav)
        print("f %.2f  omega %s  I0 %s  |E|/|om| %.1e  energy %.4e  slowest %.3f digits/|k|  kept(L=8,12) %s  max|u| %.3f" % (
            f, np.array2string(om, precision=5), np.array2string(I0, precision=4), row["rel_residual"], row["energy"],
            sl, kept, row["max_u"]))
        if row["rel_residual"] > 1e-8:
            print("  not converged; stopping the scan")
            break
    json.dump(out, open(os.path.join(HERE, "results", "lg00_amplitude.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
