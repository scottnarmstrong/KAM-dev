#!/usr/bin/env python3
"""Emit exact candidate data (dyadic rationals, scale 2^-PBITS) from a high-precision state pickle.

v = sum_{kappa in H} b_kappa sin(2 pi kappa.(psi,phi)) with b_kappa = B/2^PBITS integers B (Nyquist removed, |b| >= thr);
E = exp(2 i v_emitted) recomputed from the EMITTED (rounded, thresholded) v on the grid, real coefficients (v odd),
Nyquist removed, thresholded.  Writes JSON with schema schema/candidate.schema.json (see there).
"""
import sys, json, pickle, subprocess, datetime, time, numpy as np, mpmath
from hpfft import P, fft2, zeros
from hpsolve import HP
import model

PBITS = 440
THRESHOLDS = ["1e-30", "1e-60", "1e-110", "1e-130"]
GEN_VERSION = "so-gen-0.1"

def thr_int(s):
    return -(-int(mpmath.ceil(mpmath.mpf(s) * mpmath.mpf(2) ** PBITS)) // 1)

def in_H(k, l):
    return k > 0 or (k == 0 and l > 0)

def stats(vb, Ec):
    out = {}
    for t in THRESHOLDS:
        ti = thr_int(t)
        sv = [(k, l) for (k, l), n in vb.items() if abs(n) >= ti]
        se = [(k, l) for (k, l), n in Ec.items() if abs(n) >= ti]
        def box(s):
            return dict(max_abs_k=max((abs(k) for k, _ in s), default=0), max_abs_l=max((abs(l) for _, l in s), default=0))
        out[t] = dict(v_terms_half_lattice=len(sv), v_terms_full_lattice=2 * len(sv), E_terms=len(se),
                      v_box=box(sv), E_box=box(se))
    return out

def main(which, pkl, out, thr="1e-130"):
    t0 = time.time()
    st = pickle.load(open(pkl, "rb"))
    vim = st["vim"]; vre = st["vre"]
    nx, nt = vim.shape
    H = HP(nx, nt, which)
    ti = thr_int(thr)
    sh = P - PBITS
    vb = {}
    maxre = 0
    for a in range(nx):
        for c in range(nt):
            k = a if a < nx // 2 else a - nx; l = c if c < nt // 2 else c - nt
            if a == nx // 2 or c == nt // 2 or not in_H(k, l): continue
            n = (-int(vim[a, c]) + (1 << (sh - 1))) >> sh
            maxre = max(maxre, abs(int(vre[a, c])))
            if abs(n) >= ti: vb[(k, l)] = n
    # rebuild v-hat from the emitted v: vhat_kappa = -i b/2 (kappa in H), +i b/2 at -kappa; scale 2^P
    re = zeros((nx, nt)); im = zeros((nx, nt))
    for (k, l), n in vb.items():
        im[k % nx, l % nt] = -n << (sh - 1); im[(-k) % nx, (-l) % nt] = n << (sh - 1)
    gr, gi = H.vgrid(re, im)
    er, ei = H.expj2(gr)
    Fr, Fi = fft2(er, ei, -1)
    Fr = Fr >> H.logN; Fi = Fi >> H.logN
    Ec = {}; max_im = 0
    for a in range(nx):
        for c in range(nt):
            if a == nx // 2 or c == nt // 2: continue
            k = a if a < nx // 2 else a - nx; l = c if c < nt // 2 else c - nt
            n = (int(Fr[a, c]) + (1 << (sh - 1))) >> sh
            max_im = max(max_im, abs(int(Fi[a, c])))
            if abs(n) >= ti: Ec[(k, l)] = n
    # p range on a refined grid (double): p = nu + Dt v
    s = float(H.s_mp)
    vh = np.zeros((nx, nt), dtype=complex)
    for (k, l), n in vb.items():
        b = float(n / 2**PBITS)
        vh[k % nx, l % nt] = -0.5j * b; vh[(-k) % nx, (-l) % nt] = 0.5j * b
    mult = 1j * (s * H.k[:, None] + H.l[None, :]) * vh
    pad = 8
    big = np.zeros((nx * pad, nt * pad), dtype=complex)
    ks = np.fft.fftfreq(nx, 1.0 / nx).astype(int); ls = np.fft.fftfreq(nt, 1.0 / nt).astype(int)
    for a in range(nx):
        for c in range(nt):
            if mult[a, c] != 0: big[ks[a] % (nx * pad), ls[c] % (nt * pad)] = mult[a, c]
    pg = 1 + s + np.real(np.fft.ifft2(big) * big.size)
    pmin, pmax = float(pg.min()), float(pg.max())
    meta = dict(generator="scripts/spin_orbit/emit.py", generator_version=GEN_VERSION, which=which,
                git_hash=subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip(),
                solver_bits=P, solver_digits_approx=int(P * 0.30103), grid=[nx, nt], thr_emitted=thr,
                date=datetime.date.today().isoformat(), mpmath=mpmath.__version__, numpy=np.__version__,
                p_range_refined_grid=[repr(pmin), repr(pmax)], p_refined_grid=[nx * pad, nt * pad],
                max_abs_imag_E_coeff_log10=float(mpmath.log10(mpmath.mpf(max_im) / 2**P)) if max_im else None,
                solver_history_512=st.get("hist2"), solver_history_256=st.get("hist1"))
    nu1 = model.nu_minus_one(which)
    data = dict(schema_version=1, metadata=meta, which=which, scale_bits=PBITS,
                nu_minus_one_Q_sqrt5=[str(nu1[0]), str(nu1[1])],
                params=dict(e=str(model.E_ORB), eps=str(model.EPS)),
                coordinates="rotating: psi=theta1-theta2, phi=theta2; characters exp(2 pi i (k psi + l phi)); v=2 pi u",
                v_sin=[[k, l, str(n)] for (k, l), n in sorted(vb.items())],
                E_re=[[k, l, str(n)] for (k, l), n in sorted(Ec.items())],
                stats=stats(vb, Ec))
    json.dump(data, open(out, "w"), separators=(",", ":"))
    print(which, "v terms", len(vb), "E terms", len(Ec), "p range", pmin, pmax, "time", time.time() - t0)

if __name__ == "__main__":
    main(*sys.argv[1:])
