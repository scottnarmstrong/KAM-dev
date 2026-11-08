#!/usr/bin/env python3
"""SJS-X1: double-double defect correction of the synodic torus (x1_torus.py).

Untrusted design tooling.  State: DD Fourier coefficients C of the six periodic components on the p grid, exactly zero outside
the band |k'_i| <= cut N_i and exactly Hermitian.  One iteration:
  E = X_H(K) - D K w' in DD (x1_torus.residual_dd);  the in-band part of E drives FH25's Newton correction, computed in double
  (x1_torus.newton_step with E supplied);  C <- C + band(FFT(du)) in DD.
The out-of-band part of E is the truncation residual of the grid: it cannot be corrected and measures the grid's adequacy.
Usage: x1_dd.py STATE.npz --iters 4 --out DD.npz      (STATE from x1_torus.py newton, or a previous DD.npz)
"""
import argparse, json, os, sys, time
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import x1_torus as XT
from dd import DD, CDD
sys.path.pop(0)


def log(*a):
    print(*a, flush=True)


def herm(Z):
    """(Z + conj(Z(-k))) / 2 on the full lattice"""
    return 0.5 * (Z + np.conj(XT._rev(Z)))


def to_cdd(hi, lo):
    return CDD(DD(np.ascontiguousarray(hi.real), np.ascontiguousarray(lo.real)), DD(np.ascontiguousarray(hi.imag), np.ascontiguousarray(lo.imag)))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("src")
    ap.add_argument("--iters", type=int, default=4)
    ap.add_argument("--out", required=True)
    ap.add_argument("--freeze", type=float, default=0.0, help="hold modes with |k.w'| < this fixed ...")
    ap.add_argument("--freeze-iters", type=int, default=0, help="... during the first this many iterations")
    a = ap.parse_args()
    t0 = time.time()
    d = np.load(a.src)
    G, Fs, phi, cut = d["G"], d["Fs"], float(d["phi"]), float(d["cut"])
    shape = tuple(int(x) for x in d["grid"])
    gr = XT.Grid(shape, G, Fs, cut)
    band = gr.cutf
    if "C_hi" in d:
        C = [to_cdd(d["C_hi"][c], d["C_lo"][c]) for c in range(6)]
        hist = json.loads(str(d["hist"]))
    else:
        U = np.fft.fftn(d["u"], axes=(-3, -2, -1)) / gr.n
        C = []
        for c in range(6):
            Z = herm(U[c] * band)
            C.append(to_cdd(Z, np.zeros_like(Z)))
        hist = []
    ID = XT.ident_dd(gr)
    KW = XT.kw_dd(gr)
    kwf = np.abs(KW[0].to_float())
    frozen = band & (kwf < a.freeze)
    frozen[0, 0, 0] = False
    log("grid %s, n %d, band %d modes, setup %.0f s; %d modes with |k.w'| < %.1e held during %d iterations" % (
        shape, gr.n, int(band.sum()), time.time() - t0, int(frozen.sum()), a.freeze, a.freeze_iters))
    for it in range(a.iters):
        E, Kg, tt = XT.residual_dd(gr, C, phi, ID, KW)
        del Kg
        Eg = np.empty((6,) + shape)
        out_l1 = []
        for c in range(6):
            Z = E[c].re.to_float() + 1j * E[c].im.to_float()
            E[c] = None
            out_l1.append(float(np.abs(Z[~band]).sum()))
            Eg[c] = np.real(np.fft.ifftn(Z * band)) * gr.n
            del Z
        del E
        in_sup = [float(np.abs(Eg[c]).max()) for c in range(6)]
        uh = np.empty((6,) + shape)
        for c in range(6):
            uh[c] = np.real(np.fft.ifftn(C[c].re.hi + 1j * C[c].im.hi)) * gr.n
        del ID, KW                                                # rebuilt below (memory during the Newton step)
        t1 = time.time()
        du, info = XT.newton_step(gr, uh, phi, E=Eg)
        del uh, Eg
        dmax = 0.0
        upd = band & ~frozen if it < a.freeze_iters else band
        for c in range(6):
            Z = herm((np.fft.fftn(du[c]) / gr.n) * upd)
            dmax = max(dmax, float(np.abs(Z).max()))
            C[c] = CDD(C[c].re + np.ascontiguousarray(Z.real), C[c].im + np.ascontiguousarray(Z.imag))
        del du
        ID = XT.ident_dd(gr)
        KW = XT.kw_dd(gr)
        rec = dict(it=len(hist), E_in_sup=in_sup, E_out_l1=out_l1, dC_max=dmax, Tinv=info["Tinv"],
                   t_resid=[round(x, 1) for x in tt], t_newton=round(time.time() - t1, 1))
        hist.append(rec)
        log("dd %d |E|in sup max %.3e (per comp %s) out-of-band l1 max %.3e |dC| %.2e |T^-1| %.3f t %.0f" % (
            rec["it"], max(in_sup), " ".join("%.1e" % x for x in in_sup), max(out_l1), dmax, info["Tinv"], time.time() - t0))
        np.savez(a.out, C_hi=np.stack([C[c].re.hi + 1j * C[c].im.hi for c in range(6)]),
                 C_lo=np.stack([C[c].re.lo + 1j * C[c].im.lo for c in range(6)]),
                 G=G, Fs=Fs, phi=phi, grid=np.array(shape), cut=cut, hist=json.dumps(hist))


if __name__ == "__main__":
    main()
