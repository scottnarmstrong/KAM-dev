#!/usr/bin/env python3
"""G5 data: one real-size pair-structured Fourier x Taylor product, f_JS x chi1_JS at the nominal SJSU point, as
2-D packed real products (one per monomial pair), emitted for the core-only mirror G5/Mirror.lean.

The factors are the real parts of the Fourier-Taylor jets of the J-S pair perturbation f_JS and of its keep52
first-order generator chi1_JS (nf.py, exact Kepler divisors), Taylor degree D in the six J-S slow variables,
weighted by rho^alpha (rho_Lambda = 5e-5, rho_z = 3e-3; G4's census weights), scaled to CertFixed mantissas
(the largest weighted coefficient of each function is 2^(P-3), P = 128) and pruned below 2^(P-3) * TAU.  One
block per monomial pair (alpha, beta) with |alpha| + |beta| <= D: the product of the alpha-coefficient of f with
the beta-coefficient of chi1, both 2-D Fourier data on keys (k_J, k_S).  Each block is checked as gmpCheck
(guard, boundary checks, one packed multiplication, advice-free rounding to P-bit mantissas, read-back) against
the terms computed here with the exact Python mirror of the same arithmetic (as scripts/packed/gate_gen.py).

Writes OUT/blocks.txt (exe input), OUT/Kernel/B<i>.lean (decide +kernel), OUT/Native/B<i>.lean (native_decide),
OUT/meta.json.  usage: g5_gen.py OUT [--D 2] [--tau 1e-14] [--grid 128] [--kmax 0] [--blocks all|N]
"""
import argparse, json, math, os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import jets, model as M, nf

P = 128
PART = 300
JS_VARS = (0, 1, 3, 4, 6, 7)          # Lambda_J, Lambda_S, xi_J, xi_S, eta_J, eta_S


def zz(v):
    return 2 * v if v >= 0 else -2 * v - 1


def periodic(w, N, m):
    return m * ((2 ** (w * N) - 1) // (2 ** w - 1))


def gmp_round(w, N, l, s, Z):
    Y = Z + periodic(w, N, 2 ** l + 2 ** (s - 1))
    assert Y >= 0
    Y = (Y - (Y & periodic(w, N, 2 ** s - 1))) >> s
    return Y - periodic(w, N, 2 ** (l - s))


def pack_sum(w, cs):
    """sum_i cs_i 2^(w i), divide and conquer (exact)."""
    n = len(cs)
    if n <= 32:
        x = 0
        for c in reversed(cs):
            x = (x << w) + c
        return x
    h = n // 2
    return pack_sum(w, cs[:h]) + (pack_sum(w, cs[h:]) << (w * h))


def wrap(items, indent=4, width=100):
    lines, cur = [], " " * indent
    for i, it in enumerate(items):
        piece = it + ("," if i + 1 < len(items) else "")
        if len(cur) + len(piece) + 1 > width and cur.strip():
            lines.append(cur.rstrip()); cur = " " * indent
        cur += piece + " "
    if cur.strip():
        lines.append(cur.rstrip())
    return "\n".join(lines)


def lean_terms(name, ts, nc):
    kw = "noncomputable def" if nc else "def"
    items = ["tk %d %d %d" % (zz(k[0]), zz(k[1]), zz(v)) for k, v in ts]
    parts = [items[i:i + PART] for i in range(0, max(len(items), 1), PART)] if items else [[]]
    out = []
    for j, pt in enumerate(parts):
        out.append("%s %s_p%d : List (CertKey × Int) :=\n  [\n%s]\n" % (kw, name, j, wrap(pt)))
    joined = " ++ ".join("%s_p%d" % (name, j) for j in range(len(parts)))
    out.append("%s %s : List (CertKey × Int) :=\n%s\n" % (kw, name, wrap(joined.split(" "), indent=2)
                                                          .replace(" ++,", " ++").replace(",", "")))
    return "".join(out)


def layout_lean(lo, dims, stride, w):
    return "⟨[%d, %d], [%d, %d], [%d, %d], %d, 1⟩" % (lo[0], lo[1], dims[0], dims[1], stride[0], stride[1], w)


def factor_terms(F2, mon_idx, scale, thr):
    """2-D integer Fourier data of one monomial coefficient: [((kJ, kS), int)] with |int| >= thr."""
    c = F2[mon_idx]
    NJ, NS = c.shape
    kJ = np.round(np.fft.fftfreq(NJ, 1.0 / NJ)).astype(int)
    kS = np.round(np.fft.fftfreq(NS, 1.0 / NS)).astype(int)
    out = []
    v = np.rint(c.real * scale)
    for a in range(NJ):
        for b in range(NS):
            iv = int(v[a, b])
            if abs(iv) >= thr:
                out.append(((int(kJ[a]), int(kS[b])), iv))
    return out


def block(x, y):
    """Layouts, spec and the expected read-back terms of the packed product of x and y (mirror of gmpCheck)."""
    loA = (min(k[0] for k, _ in x), min(k[1] for k, _ in x))
    loB = (min(k[0] for k, _ in y), min(k[1] for k, _ in y))
    dA = (max(k[0] for k, _ in x) - loA[0] + 1, max(k[1] for k, _ in x) - loA[1] + 1)
    dB = (max(k[0] for k, _ in y) - loB[0] + 1, max(k[1] for k, _ in y) - loB[1] + 1)
    stride = (dA[1] + dB[1] - 1, 1)
    NA = 1 + (dA[0] - 1) * stride[0] + (dA[1] - 1)
    NB = 1 + (dB[0] - 1) * stride[0] + (dB[1] - 1)
    da = [0] * NA; db = [0] * NB
    xs = sorted(x, key=lambda t: (t[0][0] - loA[0]) * stride[0] + t[0][1] - loA[1])
    ys = sorted(y, key=lambda t: (t[0][0] - loB[0]) * stride[0] + t[0][1] - loB[1])
    for k, v in xs:
        da[(k[0] - loA[0]) * stride[0] + k[1] - loA[1]] = v
    for k, v in ys:
        db[(k[0] - loB[0]) * stride[0] + k[1] - loB[1]] = v
    ba, bb = max(abs(v) for v in da), max(abs(v) for v in db)
    l = (min(NA, NB) * ba * bb - 1).bit_length()
    w = -(-(l + 2) // 8) * 8          # l + 2 <= w (guard), a whole number of bytes for the read-back
    s = max(1, l - P)
    N = NA + NB - 1
    Za, Zb = pack_sum(w, da), pack_sum(w, db)
    Z = Za * Zb
    off = periodic(w, N, 2 ** (w - 1))
    Y = Z + off
    assert 0 <= Y < 2 ** (w * N)
    by = Y.to_bytes(w * N // 8, 'little')
    wb = w // 8
    conv = [int.from_bytes(by[wb * i: wb * (i + 1)], 'little') - 2 ** (w - 1) for i in range(N)]
    assert max(abs(c) for c in conv) <= 2 ** l
    rs = [(c + 2 ** (s - 1)) >> s for c in conv]
    if True:           # the operation-by-operation gmpRound mirror
        R = gmp_round(w, N, l, s, Z)
        assert R == pack_sum(w, rs), "gmpRound mirror disagrees with slotwise rounding"
    T = [((loA[0] + loB[0] + i // stride[0], loA[1] + loB[1] + i % stride[0]), r) for i, r in enumerate(rs) if r]
    return dict(xs=xs, ys=ys, loA=loA, loB=loB, dA=dA, dB=dB, stride=stride, w=w, ba=ba, bb=bb, l=l, s=s, N=N,
                T=T, bits=[Za.bit_length(), Zb.bit_length(), Z.bit_length()])


def spec_lean(b):
    return ("⟨%s,\n    %s,\n    %d, %d, %d, %d⟩" % (layout_lean(b['loA'], b['dA'], b['stride'], b['w']),
                                                      layout_lean(b['loB'], b['dB'], b['stride'], b['w']),
                                                      b['ba'], b['bb'], b['l'], b['s']))


def lean_file(name, b, mode):
    nc = mode == 'kernel'
    tac = 'decide +kernel' if mode == 'kernel' else 'native_decide'
    kw = "noncomputable def" if nc else "def"
    txt = ("import G5.Mirror\n\n/-! G5 block %s (%s): generated by g5_gen.py; throwaway measurement, not library code. -/\n\n"
           "namespace G5.Blk.%s\nopen G5\n\n" % (name, mode, name))
    txt += lean_terms("gx", b['xs'], nc) + lean_terms("gy", b['ys'], nc) + lean_terms("gT", b['T'], nc)
    txt += "%s gs : GmpSpec :=\n  %s\n\n" % (kw, spec_lean(b))
    txt += "set_option profiler true\nset_option profiler.threshold 1\n\n"
    txt += "theorem check : gmpCheck gs gx gy gT = true := by\n  %s\n\nend G5.Blk.%s\n" % (tac, name)
    return txt


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('out'); ap.add_argument('--D', type=int, default=2); ap.add_argument('--tau', type=float, default=1e-14)
    ap.add_argument('--grid', type=int, default=128); ap.add_argument('--kmax', type=int, default=0)
    ap.add_argument('--blocks', default='all')
    a = ap.parse_args()
    os.makedirs(os.path.join(a.out, 'Kernel'), exist_ok=True)
    os.makedirs(os.path.join(a.out, 'Native'), exist_ok=True)
    B = jets.Basis(9, a.D)
    slow = (M.LAM_STAR.copy(), M.XI0.copy(), M.ETA0.copy())
    ng = (a.grid, a.grid, 4)
    f, _ = nf.f_fourier(B, slow, ng, M.DN_STAR, M.LAM_STAR)
    E = nf.Engine(B, ng, slow, M.DN_STAR, divisor='kepler', keep='keep52')
    shJS = (ng[0], ng[1], 1)
    fJS = {shJS: f[shJS]}
    _, nonres, _ = E.split(fJS)
    chi = E.solve(nonres, a.D)
    rho = [5e-5] * 3 + [3e-3] * 6
    mons = [i for i, m in enumerate(B.mons) if all(m[v] == 0 for v in (2, 5, 8))]
    wgt = np.array([np.prod([rho[v] ** e for v, e in enumerate(B.mons[i])]) for i in range(len(B.mons))])
    Ff = f[shJS][:, :, :, 0] * wgt[:, None, None]
    Fc = chi[shJS][:, :, :, 0] * wgt[:, None, None]
    if a.kmax:
        kk = np.round(np.fft.fftfreq(a.grid, 1.0 / a.grid)).astype(int)
        m2 = (np.abs(kk)[:, None] <= a.kmax) & (np.abs(kk)[None, :] <= a.kmax)
        Ff = Ff * m2[None]; Fc = Fc * m2[None]
    sf = 2.0 ** (P - 3) / np.abs(Ff[mons].real).max()
    sc = 2.0 ** (P - 3) / np.abs(Fc[mons].real).max()
    thr = 2.0 ** (P - 3) * a.tau
    fac_f = {i: factor_terms(Ff, i, sf, thr) for i in mons}
    fac_c = {i: factor_terms(Fc, i, sc, thr) for i in mons}
    pairs = [(i, j) for i in mons for j in mons if B.deg[i] + B.deg[j] <= a.D and fac_f[i] and fac_c[j]]
    if a.blocks != 'all':
        pairs = pairs[: int(a.blocks)]
    meta = {'D': a.D, 'tau': a.tau, 'grid': a.grid, 'kmax': a.kmax, 'P': P, 'blocks': []}
    lines = []
    for n, (i, j) in enumerate(pairs):
        b = block(fac_f[i], fac_c[j])
        name = 'B%03d' % n
        for mode, sub in (('kernel', 'Kernel'), ('native', 'Native')):
            open(os.path.join(a.out, sub, name + '.lean'), 'w').write(lean_file(name, b, mode))
        lines.append('B %s' % name)
        for lo, d in ((b['loA'], b['dA']), (b['loB'], b['dB'])):
            lines.append('L %d %d %d %d %d %d %d' % (lo[0], lo[1], d[0], d[1], b['stride'][0], b['stride'][1], b['w']))
        lines.append('G %d %d %d %d' % (b['ba'], b['bb'], b['l'], b['s']))
        for tag, ts in (('X', b['xs']), ('Y', b['ys']), ('T', b['T'])):
            lines.append('%s %d' % (tag, len(ts)))
            lines.extend('%d %d %d' % (k[0], k[1], v) for k, v in ts)
        meta['blocks'].append({'name': name, 'alpha': list(B.mons[i]), 'beta': list(B.mons[j]),
                               'terms': [len(b['xs']), len(b['ys']), len(b['T'])], 'dims': [b['dA'], b['dB']],
                               'width': b['w'], 'l': b['l'], 's': b['s'], 'prodLen': b['N'], 'bits': b['bits']})
    lines.append('E')
    open(os.path.join(a.out, 'blocks.txt'), 'w').write('\n'.join(lines) + '\n')
    tot = [sum(bl['terms'][q] for bl in meta['blocks']) for q in range(3)]
    meta['totals'] = {'blocks': len(pairs), 'terms_x_y_T': tot,
                      'monomials_per_function': len(mons),
                      'harmonics_f_max': max(len(v) for v in fac_f.values()),
                      'harmonics_chi_max': max(len(v) for v in fac_c.values())}
    json.dump(meta, open(os.path.join(a.out, 'meta.json'), 'w'), indent=1)
    print(json.dumps(meta['totals']))


if __name__ == '__main__':
    main()
