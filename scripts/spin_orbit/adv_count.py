#!/usr/bin/env python3
"""SO-ADVCOUNT: count the real products of the Revision 5 checker on the R1 lunar data and their advice volume.

usage: adv_count.py which OUT.json          (which = lower | upper)

1. Rebuilds the R1 candidate exactly as SO-GEN2 emitted it (rot_build.build(which, 88, 88, 88, 318); the term
   counts are checked against certificates/lunar-spin-orbit/<which>_rot.json) and runs SO-GEN2's checker-style
   enclosures (rot_norms.norms, 72-bit models, trim 2^-56, the cfgLow stage) with every `SPoly.mul` RECORDED:
   factors (keys, mantissas, scales, parity phase) and the calling source line, which names the product.
2. Adds the products the emitter does not need but the checker does: the SOS witnesses of `checkSoGraph`
   (p range on the real torus; `mono` needs none), constructed here.
3. Classifies each recorded product: empty factor, scalar (a one-term constant factor), or a genuine model
   product; for a genuine one the complex product splits into four real products (re.re, im.im, re.im, im.re),
   of which exactly one is nonzero here (every factor has a definite parity: real coefficients, or i * real).
4. Simulates every genuine product as an advice-checked packed product (adv_pack.simulate) with an explicit
   error budget: 1e-80 for the full-precision products (the witness residuals r_psi = 1.7e-77, r_phi = 5.4e-79;
   the energy 3.9e-81 against e = 4.03e-78), 1e-13 for the cfgLow products (SO-GEN2's radii are >= 1e-12).
Untrusted tooling.  No Lean is run.
"""
import sys, os, json, time, inspect, linecache, math
import numpy as np
from fractions import Fraction as F
import rotlib
from rotlib import SPoly, Weights
import adv_pack

HERE = os.path.dirname(os.path.abspath(__file__))
REC = []
_orig_mul = SPoly.mul


def _site():
    """the calling source line that names the product (skipping Ctx.mul; a matmul call is named by its caller)."""
    chain = []
    for fr in inspect.stack()[2:10]:
        fn = os.path.basename(fr.filename)
        if fn in ("rot_build.py", "rot_norms.py"):
            text = linecache.getline(fr.filename, fr.lineno).strip()
            if text.startswith("return a.mul(b"):
                continue
            chain.append(("%s:%d" % (fn, fr.lineno), text))
    if not chain:
        return "?", ""
    site, text = chain[0]
    if text.startswith("return [[X.red(madd(") and len(chain) > 1:
        return chain[1][0], "matmul: " + chain[1][1]
    return site, text


def _rec_mul(self, o, Wt, S=None, thr=0):
    site, text = _site()
    REC.append(dict(site=site, text=text,
                    a=(self.k.copy(), self.l.copy(), self.v.copy(), self.S, self.ph),
                    b=(o.k.copy(), o.l.copy(), o.v.copy(), o.S, o.ph), stage=STAGE[0]))
    return _orig_mul(self, o, Wt, S, thr)


STAGE = ["?"]

# names of the recorded call sites (source text -> product family); the families follow rot_norms' order
FAMILY = [
    ("p2 = p.mul(p, Wt)", "energy: p~ * p~ (H o K value slot, (1*A0)*A0)", "full"),
    ("prod = dv.mul(E, Wt)", "exp witness residual: (d_j g0) * E", "full"),
    ("terms = [X.mul(DK[r][i], DK[r][j])", "Gram models DK^T DK", "low"),
    ("s = X.mul(Bm[i][0], G[0][j])", "Gram check B G", "low"),
    ("matmul: N = matmul", "torsion frame N = Omega0 DK G^-1", "low"),
    ("matmul: A1 = matmul", "torsion DG = DKw^T DK + DK^T DKw", "low"),
    ("matmul: T1 = matmul", "torsion D(G^-1) = -G^-1 DG G^-1", "low"),
    ("matmul: DGi = ", "torsion D(G^-1) = -G^-1 DG G^-1", "low"),
    ("matmul: M1m = matmul", "torsion DN = Omega0 (DKw G^-1 + DK D(G^-1))", "low"),
    ("madd(*[X.mul(VQQ[", "torsion DX_H(K) N (V_QQ * N)", "low"),
    ("T[a][b] = X.red(madd(*[X.mul(N[i][a], OW[i])", "torsion block N^T Omega W", "low"),
    ("Y[b] = X.red(madd(X.mul(VQ[0], N[0][b])", "torsion last row DH(K) N", "low"),
    ("SOS", "graph SOS g * g*", "low"),
]


def family(text):
    for key, name, prec in FAMILY:
        if text.startswith(key) or key in text:
            return name, prec
    return text, "?"


def to_dict(f):
    k, l, v, S, ph = f
    return {(int(a), int(b)): int(x) for a, b, x in zip(k, l, v) if x}


def classify(r):
    a, b = r["a"], r["b"]
    if len(a[2]) == 0 or len(b[2]) == 0:
        return "empty"
    def is_const(f):
        return len(f[2]) == 1 and int(f[0][0]) == 0 and int(f[1][0]) == 0
    if is_const(a) or is_const(b):
        return "scalar"
    return "model"


# ------------------------------------------------------------------------------------------------ SOS witnesses
def sos_witnesses(p, Wt, which, log=print):
    """`checkSoGraph` p-range witnesses on the real torus: f = p - m0 >= 0 (lower) and f = m0 - p >= 0 (upper).
    g ~ sqrt(f) (grid + FFT), real and even, truncated; the checked residual r = ||f - g g*||_w must be <= the
    slack, and the certified bound is m0 -+ r.  Slack: 1e-4 on the WINDOW side (lower torus pHi, upper torus pLo),
    the band margin on the band side (|p - 1| <= 33/1000).  Returns [(name, g dict, scale, info)]."""
    N1, N2 = 1024, 256
    G = p.eval_grid(N1, N2).real
    pmin, pmax = float(G.min()), float(G.max())
    out = []
    sides = ([("pHi (window side)", "up", 3e-4), ("pLo (band side)", "lo", None)] if which == "lower" else
             [("pLo (window side)", "lo", 3e-4), ("pHi (band side)", "up", None)])
    pext = (int(np.abs(p.k).max()), int(np.abs(p.l).max()))
    for name, side, slack in sides:
        if slack is None:
            slack = (pmin - 0.967) if side == "lo" else (1.033 - pmax)
            slack = min(slack * 0.9, 1e-2)
        best = None
        for gap_frac in (0.5,):
            m0 = (pmin - gap_frac * slack) if side == "lo" else (pmax + gap_frac * slack)
            f = (G - m0) if side == "lo" else (m0 - G)
            assert f.min() > 0
            g = np.sqrt(f)
            C = np.fft.fft2(g) / (N1 * N2)
            kk = np.fft.fftfreq(N1, 1 / N1).astype(int); ll = np.fft.fftfreq(N2, 1 / N2).astype(int)
            Cr = C.real
            # truncation sweep: keep |g_k| >= tau, residual r = ||f - g g*||_w (float estimate, strip weights)
            for tau in [10.0 ** (-j / 2) for j in range(4, 20)]:
                idx = np.nonzero(np.abs(Cr) >= tau)
                gd = {(int(kk[a]), int(ll[c])): float(Cr[a, c]) for a, c in zip(*idx)}
                # g g* = g^2 (g real even); residual f - g^2 as coefficients; only keys inside the true support
                # (|k| <= max(2 ext(g), ext(p))) count: outside it the FFT values are float noise
                gs = np.zeros((N1, N2), complex)
                for (a_, c_), x in gd.items():
                    gs[a_ % N1, c_ % N2] += x
                gv = np.fft.ifft2(gs).real * N1 * N2
                resid = np.fft.fft2(f - gv * gv) / (N1 * N2)
                ek = max(2 * max(abs(a_) for a_, _ in gd), pext[0]); el = max(2 * max(abs(c_) for _, c_ in gd), pext[1])
                mask = (np.abs(kk)[:, None] <= ek) & (np.abs(ll)[None, :] <= el)
                wts = np.exp(2 * math.pi / 70 * (np.abs(kk)[:, None] + np.abs(ll)[None, :]))
                rw = float((np.abs(resid) * wts * mask).sum())
                if rw <= slack / 2:
                    best = dict(m0=m0, tau=tau, terms=len(gd), resid_w=rw, slack=slack, g=gd)
                    break
            if best:
                break
        assert best, name
        Sg = 40
        gi = {k: int(round(x * 2**Sg)) for k, x in best["g"].items()}
        gi = {k: v for k, v in gi.items() if v}
        info = dict(name=name, pmin=pmin, pmax=pmax, m0=best["m0"], slack=best["slack"], tau=best["tau"],
                    g_terms=len(gi), resid_w_estimate=best["resid_w"])
        log("  SOS %s: p in [%.6f, %.6f], slack %.2e, g terms %d (|g_k| >= %.1e), residual %.2e" % (
            name, pmin, pmax, best["slack"], len(gi), best["tau"], best["resid_w"]))
        out.append((name, gi, Sg, info))
    return out


def main(which, outpath):
    t0 = time.time()
    import rot_build, rot_norms
    SPoly.mul = _rec_mul
    STAGE[0] = "build"
    cand = rot_build.build(which, 88, 88, 88, 318)
    d = json.load(open(os.path.join(rotlib.CERT, "%s_rot.json" % which)))
    assert cand["nv_half"] == d["stats"]["v_terms_half"] and cand["nE"] == d["stats"]["E_terms"], "R1 data mismatch"
    STAGE[0] = "norms"
    nr = rot_norms.norms(cand, cand["bounds"]["Delta"])
    SPoly.mul = _orig_mul
    Wt = Weights(F(1, 70))
    print("recorded %d SPoly.mul calls (%.0fs)" % (len(REC), time.time() - t0))
    # SOS (checkSoGraph)
    for name, gi, Sg, info in sos_witnesses(cand["p"], Wt, which):
        kk = np.array([k for k, _ in gi], dtype=np.int64); ll = np.array([l for _, l in gi], dtype=np.int64)
        vv = rotlib._obj(list(gi.values()))
        # g* = conjReflect g = g for a real even g: the product is g * g
        REC.append(dict(site="adv_count.py:sos", text="SOS " + name, a=(kk, ll, vv, Sg, 0), b=(kk, ll, vv, Sg, 0),
                        stage="graph", info=info))
    rows = []
    for i, r in enumerate(REC):
        fam, prec = family(r["text"])
        cls = classify(r)
        row = dict(idx=i, site=r["site"], family=fam, precision=prec, cls=cls, stage=r["stage"],
                   terms_a=len(r["a"][2]), terms_b=len(r["b"][2]), phase_a=r["a"][4], phase_b=r["b"][4])
        if "info" in r:
            row["sos"] = r["info"]
        if cls == "model":
            budget = 1e-80 if prec == "full" else 1e-13
            t1 = time.time()
            st = adv_pack.simulate(to_dict(r["a"]), to_dict(r["b"]), r["a"][3], r["b"][3], Wt, budget,
                                   label=fam)
            st.pop("rows_per_window", None)
            row.update(packed=st, nominal_real_products=4, nonzero_real_products=1)
            print("  #%d %-50s %5d x %5d  w %4d  shards %3d pairs %4d  adv %8d slots %7.2f MB dec  Pout %d  (%.1fs)" % (
                i, fam[:50], st["terms_a"], st["terms_b"], st["w"], st["shards"], st["pairs"], st["advice_slots"],
                st["advice_dec_bytes"] / 1e6, st["pout"], time.time() - t1))
        rows.append(row)
    res = dict(which=which, products=rows, norms_check=dict(delta=nr["gram"]["delta"], delta_T=nr["torsion"]["delta_T"]),
               seconds=time.time() - t0)
    json.dump(res, open(outpath, "w"), indent=1, default=float)
    print("wrote %s (%.0fs)" % (outpath, time.time() - t0))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
