#!/usr/bin/env python3
"""SJS-X1: Fourier support S(L) of the synodic torus, in SJS-PLAN's definition, to large L.

Untrusted design tooling.  S(L, rho) = #{k : max_c |c_k^c| e^{rho |k|_1} / max_{k != 0} |c^c| >= 10^-L} over the full lattice
(sjs_spectrum.counts: each component relative to its own largest nonconstant coefficient; |k|_1 and rho in the theta lattice of
SJS-PLAN's coarse torus, 2 pi angles).  Two component sets: 'syn' = (b1, b2, b3, Lambda1, I5, I6) and 'reg' = (a1, a2, a3, Lambda1,
Lambda2, I6), the set of SJS-PLAN's table (1.3), a = SYN^-1 b, Lambda2 = C + I5 + I6 - Lambda1.
Also: the noise floor (normalized magnitudes in the outer shell of the band), extents of the support in the p frame (full and
99.5 %), the box ratio beta = box / S, the robust frame search of sjs_spectrum at a few L, and per-axis envelope rates.
Usage: x1_spectrum.py STATE.npz --json OUT.json [--frames 8,16]
"""
import argparse, itertools, json, os, sys
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))


def load_coeffs(path):
    d = np.load(path)
    shape = tuple(int(x) for x in d["grid"])
    if "C_hi" in d:
        C = d["C_hi"] + d["C_lo"]
        kind = "dd"
    else:
        C = np.fft.fftn(d["u"], axes=(-3, -2, -1)) / np.prod(shape)
        kind = "double"
    return C, d["G"], shape, kind, float(d["cut"])


def comps(C, which):
    if which == "syn":
        return C
    b1, b2, b3, L1, I5, I6 = C
    return np.stack([b1 + b2, b2, b3 - b2, L1, I5 + I6 - L1, I6])


def normalized_max(Cs):
    m = np.abs(Cs)
    m[:, 0, 0, 0] = 0
    top = m.reshape(m.shape[0], -1).max(axis=1)
    return (m / top.reshape(-1, 1, 1, 1)).max(axis=0)


def lattice(shape, G):
    kp = np.stack(np.meshgrid(*[np.fft.fftfreq(n, 1.0 / n) for n in shape], indexing="ij")).astype(int)
    Gi = np.rint(np.linalg.inv(np.array(G, dtype=float))).astype(int)
    k = np.einsum("ij,j...->i...", Gi, kp)
    return kp, k


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("src")
    ap.add_argument("--json")
    ap.add_argument("--frames", default="8")
    ap.add_argument("--Lmax", type=int, default=30)
    a = ap.parse_args()
    C, G, shape, kind, cut = load_coeffs(a.src)
    kp, k = lattice(shape, G)
    k1 = np.abs(k).sum(axis=0)
    band = np.ones(shape, dtype=bool)
    for i in range(3):
        band &= np.abs(kp[i]) <= cut * shape[i]
    edge =band & ~np.all([np.abs(kp[i]) <= 0.85 * cut * shape[i] for i in range(3)], axis=0)
    Ls = list(range(2, a.Lmax + 1))
    rhos = [0.0, 0.02, 0.05, 0.1]
    out = dict(src=os.path.basename(a.src), kind=kind, grid=list(shape), G=np.array(G).tolist(), cut=cut, Ls=Ls)
    for which in ("reg", "syn"):
        m = normalized_max(comps(C, which))
        floor = float(np.percentile(m[edge], 99)) if edge.any() else float("nan")
        S = {}
        for rho in rhos:
            w = m * np.exp(rho * k1)
            S[str(rho)] = [int(np.count_nonzero(w >= 10.0 ** -L)) for L in Ls]
        # support extents in the p frame, at rho = 0.02
        w = m * np.exp(0.02 * k1)
        ext = {}
        for L in Ls:
            sel = w >= 10.0 ** -L
            if sel.sum() < 2:
                continue
            pts = kp[:, sel]
            full = (pts.max(axis=1) - pts.min(axis=1) + 1).tolist()
            rob = [float(np.percentile(pts[i], 99.75) - np.percentile(pts[i], 0.25) + 1) for i in range(3)]
            ext[str(L)] = dict(S=int(sel.sum()), full=[int(x) for x in full], robust=rob,
                               beta_full=float(np.prod(full) / sel.sum()), beta_robust=float(np.prod(rob) / sel.sum()),
                               touches_band=bool((np.abs(pts) >= np.floor(cut * np.array(shape)).reshape(3, 1)).any()))
        # per-axis envelope in the p frame: max normalized magnitude on |k'_i| = j
        env = []
        for i in range(3):
            e = []
            for j in range(int(cut * shape[i]) + 1):
                e.append(float(m[np.abs(kp[i]) == j].max()))
            env.append(e)
        out[which] = dict(S=S, floor99=floor, ext=ext, env=env)
        print("== %s components (%s torus, grid %s): noise floor (99th pct of the outer band shell) %.2e" % (which, kind, shape, floor))
        for rho in rhos:
            print("  rho %.2f" % rho, " ".join("%d:%d" % (L, s) for L, s in zip(Ls, S[str(rho)])))
        for L in (8, 12, 16, 20, 24, 28):
            if str(L) in ext:
                e = ext[str(L)]
                print("  L %2d S %8d extents full %s robust %s beta %.2f / %.2f%s" % (
                    L, e["S"], e["full"], ["%.0f" % x for x in e["robust"]], e["beta_full"], e["beta_robust"],
                    "  (touches the band edge)" if e["touches_band"] else ""))
    # SJS-PLAN's table, for comparison
    ref = os.path.join(HERE, "..", "plan", "results", "spectrum128.json")
    if os.path.exists(ref):
        r = json.load(open(ref))
        plan = dict(zip(r["Ls"], r["regular"]["0.02"]))
        mine = dict(zip(Ls, out["reg"]["S"]["0.02"]))
        print("  SJS-PLAN regular chart, rho 0.02 (128^2 x 144 Delaunay torus):", plan)
        print("  ratio here / plan:", {L: round(mine[L] / plan[L], 3) for L in plan if L in mine and plan[L]})
        out["plan_regular_0.02"] = plan
    # robust frames (sjs_spectrum.robust_frames on the theta lattice), at a few L
    out["frames"] = {}
    mreg = normalized_max(comps(C, "reg"))
    for L in [int(x) for x in a.frames.split(",") if x]:
        sel = mreg * np.exp(0.02 * k1) >= 10.0 ** -L
        pts = k[:, sel]
        rng = range(-2, 3)
        rows = [np.array(r) for r in itertools.product(rng, rng, rng) if any(r)]
        ex = {}
        for row in rows:
            v = row @ pts
            ex[tuple(row)] = float(np.percentile(v, 99.75) - np.percentile(v, 0.25) + 1)
        order = sorted(ex, key=ex.get)[:30]
        best = []
        for r1, r2, r3 in itertools.combinations(order, 3):
            Gm = np.array([r1, r2, r3])
            if abs(round(np.linalg.det(Gm))) == 1:
                best.append((ex[r1] * ex[r2] * ex[r3] / pts.shape[1], Gm.tolist(), [ex[r1], ex[r2], ex[r3]]))
        best.sort(key=lambda t: t[0])
        out["frames"][str(L)] = dict(S=int(pts.shape[1]), best=best[:3])
        print("  robust frame at L %d: S %d, best beta %.2f frame %s extents %s" % (L, pts.shape[1], best[0][0], best[0][1],
                                                                               ["%.0f" % x for x in best[0][2]]))
    if a.json:
        json.dump(out, open(a.json, "w"), indent=1)


if __name__ == "__main__":
    main()
