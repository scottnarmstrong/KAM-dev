#!/usr/bin/env python3
"""SR-4 BALL-MIRROR: rigorous ball-arithmetic mirror of the gate-2 tube checks (a)-(e) (python-flint).

Model of record: the published complex form of SJSU18-O2, each 25-digit decimal an exact rational (SR-1).
Literal producer data (from a torus2.py run, default `sr-vp-L8`, V' coordinates): the shift generator S,
the reference actions Ibar = I* + c0, the observables F_j; all read as exact dyadic rationals and then
given exact reversible parity (F_j: even part, S: odd part).  The tube is centred on B0 (tau~ = 0):

  chart   z = V' w (V' exact orthogonal, SR-2), w_k = sqrt(I_k) e^{i q_k}, I = B0(phi) + u,
          B0_j = Ibar_j + d_{q_j} S (exact gradient: the shift is canonical), phi = (q1 - q3, q2 - q3);
  tube    T = {|u_j| <= r}, r = kappa delta;
  H~(u, phi) = sum_n T_n(phi) prod_j (B0_j + u_j)^{n_j/2}, T_n from H_w = H_z(V' w) exactly.

Checks (sup norms bounded by weighted l1 norms of enclosed Fourier-Taylor coefficients):
  (a) eta_j >= sup_T |{F_j, H~}|: exact truncated series of degree <= Lv (arb), Fourier truncation balls,
      dropped products (degree > Lv), binomial tails of dH~ beyond degree Lv (sup bounds over B0's range);
  (b) faces: sup_T |F_j - c_j - u_j| < (kappa - 1) delta;
  (d) regularity: min B0_j - r > 0;
  (e) eccentricity ranges on T (float grid + explicit Lipschitz margin; see report);
  (c) initial set: sr7_qradius.py.
PASS iff for j = J, S, U: (delta/2)/eta_j >= 1e10 yr and the face margin >= 0.3 delta.
Usage: python sr4_ball_mirror.py [--run sr-vp-L8] [--Lv 8] [--delta 1e-6] [--quick]
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

import numpy as np
from flint import arb, fmpq, fmpq_mpoly_ctx

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT / 'scripts/sjsu/gate2'))
sys.path.insert(0, str(HERE))
import ft  # noqa: E402
from ballft import FM, Acc, Layout, ZERO, binom_q, hexn, lincomb, to_arb  # noqa: E402

LOG = []


def log(*a):
    s = ' '.join(str(x) for x in a)
    LOG.append(s)
    print(s, flush=True)


def up(x):
    """float upper bound of a nonnegative arb."""
    return float(x.upper()) * (1 + 2 ** -50) if not isinstance(x, float) else x


# ------------------------------------------------------------------------------------------------ data
def load_Hw(maxdeg):
    data = json.loads((ROOT / 'applications/sjsu/data/sjsu18-o2.json').read_text())
    vp = json.loads((HERE / 'results/vprime.json').read_text())
    V = [[Fraction(x) for x in row] for row in vp['Vprime_exact']]
    cz = fmpq_mpoly_ctx.get(('z', 6), 'lex')
    cw = fmpq_mpoly_ctx.get(('w', 6), 'lex')
    terms = {}
    for t in data['complex_form']['terms']:
        if sum(t[:6]) <= maxdeg:
            f = Fraction(t[6])
            terms[tuple(t[:6])] = fmpq(f.numerator, f.denominator)
    Hz = cz.from_dict(terms)
    w = cw.gens()
    q = lambda x: fmpq(x.numerator, x.denominator)  # noqa: E731
    zero = cw.from_dict({})
    subs = []
    for j in range(3):  # z_j = sum_k V'_jk w_k, zbar_j = sum_k V'_jk wbar_k
        subs.append(sum((q(V[j][k]) * w[2 * k] for k in range(3)), zero))
        subs.append(sum((q(V[j][k]) * w[2 * k + 1] for k in range(3)), zero))
    Hw = Hz.compose(*subs)
    T = defaultdict(dict)
    for m, c in zip(Hw.monoms(), Hw.coeffs()):
        m = [int(x) for x in m]
        n = (m[0] + m[1], m[2] + m[3], m[4] + m[5])
        k = (m[0] - m[1], m[2] - m[3], m[4] - m[5])
        assert sum(k) == 0, 'charged term in H_w'
        T[n][(k[0], k[1])] = Fraction(int(c.numerator), int(c.denominator))
    for n, d in T.items():
        for k, v in d.items():
            assert d.get((-k[0], -k[1])) == v, 'H_w not reversible'
    return dict(T), V, data


def load_run(tag, Lsp=8, Ksp=50):
    z = np.load(ROOT / f'scripts/sjsu/gate2/results/{tag}-F.npz')
    S = ft.Space(L=Lsp, K=Ksp)
    G = S.G
    F = []
    for j in range(3):
        A = z[f'F{j}']
        Fm = {}
        for i, m in enumerate(S.mons):
            d = {}
            for k2 in range(-Ksp // 2, Ksp // 2 + 1):
                for k1 in range(-Ksp // 2, Ksp // 2 + 1):
                    if hexn(k1, k2) > Ksp:
                        continue
                    a = A[i, k1 % G, k2 % G].real
                    b = A[i, (-k1) % G, (-k2) % G].real
                    v = (Fraction(float(a)) + Fraction(float(b))) / 2  # exact even part
                    if v != 0:
                        d[(k1, k2)] = v
            Fm[m] = d
        F.append(Fm)
    sh = z['s_hat']
    G2 = sh.shape[0]
    sig = {}
    KS = 60
    for k2 in range(-KS // 2, KS // 2 + 1):
        for k1 in range(-KS // 2, KS // 2 + 1):
            if hexn(k1, k2) > KS or (k1, k2) == (0, 0):
                continue
            a = sh[k1 % G2, k2 % G2].imag
            b = sh[(-k1) % G2, (-k2) % G2].imag
            v = (Fraction(float(a)) - Fraction(float(b))) / 2  # exact odd part: S = sum i sigma_k e^{ik phi}
            if v != 0:
                sig[(k1, k2)] = v
    Ibar = [Fraction(float(z['Istar'][j])) + Fraction(float(z['c0'][j])) for j in range(3)]
    return F, sig, Ibar, S.mons


# ------------------------------------------------------------------------------------------- helpers
def grid_eval_even(coeffs, const, G):
    """float values on a G x G grid of const + sum a_k e^{ik phi} (a dict of Fraction/arb)."""
    c = np.zeros((G, G), dtype=complex)
    for (k1, k2), v in coeffs.items():
        c[k1 % G, k2 % G] += float(v)
    c[0, 0] += float(const)
    return np.fft.ifft2(c).real * G * G


def l1_k(coeffs, a):
    """sum |k_a| |c_k| (a = 0, 1, or 2 for k3 = -k1 - k2), as an arb upper bound."""
    s = ZERO
    for (k1, k2), v in coeffs.items():
        ka = (k1, k2, -k1 - k2)[a]
        if ka:
            s += abs(to_arb(v)) * abs(ka)
    return s


def b0_range(B0c, Ibar, G=512):
    """Rigorous [Bmin, Bmax] of B0_j over T^2: grid values +- Lipschitz * half spacing + float slack."""
    out = []
    for j in range(3):
        v = grid_eval_even(B0c[j], Ibar[j], G)
        lip = up(l1_k(B0c[j], 0)) + up(l1_k(B0c[j], 1))
        hh = math.pi / G  # half grid spacing
        l1 = up(sum((abs(to_arb(x)) for x in B0c[j].values()), ZERO)) + float(Ibar[j])
        slack = 1e-12 * l1 + 1e-30
        out.append((arb(v.min() - lip * hh - slack), arb(v.max() + lip * hh + slack), lip))
    return out


def witness_sqrt(L, B0c, Ibar, G=256):
    """Float witnesses W ~ sqrt(B0), Y ~ 1/sqrt(B0) as exact even models (truncated to h <= KH)."""
    v = grid_eval_even(B0c, Ibar, G)
    out = []
    for vals in (np.sqrt(v), 1 / np.sqrt(v)):
        c = np.fft.fft2(vals) / (G * G)
        d = {}
        for k1, k2, oi, h in L.op_modes:
            if h <= L.KH:
                a = c[k1 % G, k2 % G].real
                b = c[(-k1) % G, (-k2) % G].real
                x = (Fraction(float(a)) + Fraction(float(b))) / 2
                if x != 0 and abs(x) > 1e-40:
                    d[(k1, k2)] = x
        out.append(FM.from_coeffs(L, d, 0))
    return out


def mid_model(L, f):
    """The model's polynomial with every coefficient replaced by its (exact) midpoint; no remainder."""
    from flint import arb_poly
    return FM(L, arb_poly([c.mid() for c in f.poly.coeffs()]), f.par, ZERO, 0.0, f.c)


def full_residual_norm(L, terms_fm, terms_prod):
    """||sum s A + sum s' X Y||_W over the whole product box (no truncation), as arb, plus eps."""
    acc = Acc(L, 0)
    for s, A in terms_fm:
        acc.addfm(s, A)
    for s, X, Y in terms_prod:
        acc.addmul(s, X, Y, 'witness')
    n1, nW = acc.norms()
    return nW + acc.eps


# ----------------------------------------------------------------------------------------------- tails
class Tails:
    """Binomial tails: tail(alpha) >= sup_phi sum_{|m| > Lv} prod_j |binom(alpha_j, m_j)| B_j^{alpha_j - m_j} r^m."""

    def __init__(self, Brange, r, Lv, lmax=None):
        self.Bmin = [b[0] for b in Brange]
        self.Bmax = [b[1] for b in Brange]
        self.r = to_arb(r)
        self.Lv = Lv
        self.lmax = lmax or (Lv + 40)
        self.cache_seq = {}
        self.cache = {}

    def seq(self, j, al: Fraction):
        key = (j, al)
        if key in self.cache_seq:
            return self.cache_seq[key]
        s = []
        lmax = self.lmax
        intal = al.denominator == 1 and al >= 0
        for l in range(lmax + 1):
            b = binom_q(al, l)
            if b == 0:
                s.append(ZERO)
                continue
            e = al - l
            ea = to_arb(e)
            base = self.Bmax[j] if e >= 0 else self.Bmin[j]
            s.append(abs(to_arb(b)) * (ea * base.log()).exp() * self.r ** l)
        if intal:
            R = ZERO
        else:
            q = self.r / self.Bmin[j]
            assert float(q.upper()) < 1
            R = s[lmax] * q / (1 - q)
        self.cache_seq[key] = (s, R)
        return s, R

    def tail(self, alpha):
        if alpha in self.cache:
            return self.cache[alpha]
        seqs = [self.seq(j, alpha[j]) for j in range(3)]
        full = arb(1)
        for s, R in seqs:
            tot = R
            for x in s:
                tot += x
            full *= tot
        fin = ZERO
        Lv = self.Lv
        s0, s1, s2 = seqs[0][0], seqs[1][0], seqs[2][0]
        for a in range(Lv + 1):
            for b in range(Lv + 1 - a):
                t = s0[a] * s1[b]
                for c in range(Lv + 1 - a - b):
                    fin += t * s2[c]
        out = (full - fin).upper()
        out = arb(max(float(out), 0.0) * (1 + 1e-12) + 1e-300) if float(out) > 0 else arb(1e-300)
        self.cache[alpha] = out
        return out


# ------------------------------------------------------------------------------------------------ main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--run', default='sr-vp-L8')
    ap.add_argument('--Lv', type=int, default=8)
    ap.add_argument('--delta', type=float, default=1e-6)
    ap.add_argument('--kappa', type=float, default=2.0)
    ap.add_argument('--CP', type=int, default=30)
    ap.add_argument('--KH', type=int, default=60)
    ap.add_argument('--prec', type=int, default=160)
    ap.add_argument('--skip', type=float, default=1e-28, help='bracket slot pairs below this are bounded, not multiplied')
    ap.add_argument('--maxdeg', type=int, default=18, help='H degree cap (testing only)')
    ap.add_argument('--quick', action='store_true', help='Lv=3, CP=16, KH=32, maxdeg=6 (pipeline test)')
    ap.add_argument('--tag', default='')
    args = ap.parse_args()
    if args.quick:
        args.Lv, args.CP, args.KH, args.maxdeg = 3, 16, 32, 6
    t0 = time.time()
    L = Layout(args.CP, args.KH, args.prec)
    Lv, delta, kappa = args.Lv, args.delta, args.kappa
    r = kappa * delta
    ra = to_arb(Fraction(r))
    M = Lv + 1
    rep = {'gate': 'SR-4 BALL-MIRROR', 'args': vars(args)}

    # ---- data
    T, V, data = load_Hw(args.maxdeg)
    log(f'H_w: {sum(len(d) for d in T.values())} terms in {len(T)} groups n ({time.time() - t0:.1f}s)')
    Fd, sig, Ibar, mons = load_run(args.run)
    sig = {k: v for k, v in sig.items() if hexn(*k) <= L.KH}
    if L.KH < 50:  # testing only
        Fd = [{m: {k: v for k, v in d.items() if hexn(*k) <= L.KH} for m, d in Fj.items()} for Fj in Fd]
    log(f'producer data {args.run}: S {len(sig)} modes; F {[sum(len(d) for d in Fj.values()) for Fj in Fd]} '
        f'coefficients; Ibar {[float(x) for x in Ibar]}')
    # B0_j = Ibar_j + d_{q_j} S, coefficient a_{j,k} = -k_j sigma_k (k3 = -k1 - k2)
    B0c = []
    for j in range(3):
        d = {}
        for (k1, k2), s in sig.items():
            kj = (k1, k2, -k1 - k2)[j]
            if kj:
                d[(k1, k2)] = -kj * s
        B0c.append(d)
    Brange = b0_range(B0c, Ibar)
    rep['B0_range'] = [(float(b[0].lower()), float(b[1].upper())) for b in Brange]
    reg = [float((b[0] - ra).lower()) for b in Brange]
    rep['regularity_min_B0_minus_r'] = reg
    log('B0 range', rep['B0_range'], 'min B0 - r', reg)
    B0 = []
    for j in range(3):
        d = dict(B0c[j])
        d[(0, 0)] = d.get((0, 0), 0) + Ibar[j]
        B0.append(FM.from_coeffs(L, d, 0))

    # ---- powers P[j][s2] = B0_j^{s2/2}
    L.stage = 'powers'
    P = []
    wit = []
    one = FM.from_coeffs(L, {(0, 0): 1}, 0)
    for j in range(3):
        W, Y = witness_sqrt(L, B0c[j], Ibar[j])
        # one Newton step each in arb (W first, then Y against the new W), midpoints kept as exact witnesses
        acc = Acc(L, 0)
        acc.addfm(1, B0[j])
        acc.addmul(-1, W, W, 'witness')
        R0 = acc.unpack(False)
        acc = Acc(L, 0)
        acc.addfm(1, W)
        acc.addmul(Fraction(1, 2), Y, R0, 'witness')
        W = mid_model(L, acc.unpack(False))
        acc = Acc(L, 0)
        acc.addfm(1, one)
        acc.addmul(-1, W, Y, 'witness')
        E0 = acc.unpack(False)
        acc = Acc(L, 0)
        acc.addfm(1, Y)
        acc.addmul(1, Y, E0, 'witness')
        Y = mid_model(L, acc.unpack(False))
        R1 = full_residual_norm(L, [(1, B0[j])], [(-1, W, W)])          # ||B0 - W^2||_W
        E1 = full_residual_norm(L, [(1, one)], [(-1, W, Y)])  # ||1 - W Y||_W
        nY = Y.nW
        q = E1
        # contraction for e = Y/2 (B0 - W^2 - e^2) + (1 - W Y) e on ||e||_W <= rho
        rho = (nY / 2) * R1 * 2 / (1 - q)
        ok1 = float((nY / 2 * (R1 + rho * rho) + q * rho - rho).upper()) <= 0
        ok2 = float((nY * rho + q).upper()) < 1
        w0 = W.eval(arb(0), arb(0))
        ok3 = float((w0 - rho).lower()) > 0
        assert ok1 and ok2 and ok3, 'sqrt witness failed'
        q2 = q + nY * rho
        rho_inv = nY * q2 / (1 - q2)
        Wm = FM(L, W.poly, 0, rho, 0.0, W.c, (W.nW, W.n1, W.maxabs))
        Ym = FM(L, Y.poly, 0, rho_inv, 0.0, Y.c, (Y.nW, Y.n1, Y.maxabs))
        wit.append({'||B0-W^2||_W': up(R1), '||1-WY||_W': up(q), 'rho_sqrt': up(rho), 'rho_invsqrt': up(rho_inv)})
        Pj = {0: FM.from_coeffs(L, {(0, 0): 1}, 0), 1: Wm, -1: Ym, 2: B0[j]}
        for s2 in range(3, 19):
            acc = Acc(L, 0)
            acc.addmul(1, Pj[s2 - 2], B0[j], 'power')
            Pj[s2] = acc.unpack()
        acc = Acc(L, 0)
        acc.addmul(1, Ym, Ym, 'power')
        Pj[-2] = acc.unpack()
        for s2 in range(3, 2 * M + 2):
            acc = Acc(L, 0)
            acc.addmul(1, Pj[-(s2 - 2)], Pj[-2], 'power')
            Pj[-s2] = acc.unpack()
        P.append(Pj)
    rep['witnesses'] = wit
    log('witnesses', wit, f'({time.time() - t0:.1f}s)')

    # ---- T_n models (exact), with input rounding emulation
    Tm = {}
    for n, d in T.items():
        f = FM.from_coeffs(L, d, 0)
        wsum = sum(1 + hexn(*k) for k in d)
        Tm[n] = FM(L, f.poly, 0, ZERO, f.maxabs * wsum, f.c, (f.nW, f.n1, f.maxabs))

    # ---- h_m: Taylor coefficients of H~ in u, |m| <= M, nested over j = 3, 2, 1 (streamed over n1)
    L.stage = 'Hbuild'
    hacc = {m: Acc(L, 0) for m in ft.monomials(M)}
    by_n1 = defaultdict(list)
    for n in Tm:
        by_n1[n[0]].append(n)
    half = Fraction(1, 2)
    nprod0 = len(L.log)
    for n1, ns in sorted(by_n1.items()):
        # level 1: U[n2][m3] = sum_{n3} binom(n3/2, m3) T_n P3[n3 - 2 m3]
        Uacc = defaultdict(dict)
        for n in ns:
            for m3 in range(M + 1):
                b = binom_q(n[2] * half, m3)
                if b == 0:
                    continue
                a = Uacc[n[1]].get(m3)
                if a is None:
                    a = Uacc[n[1]][m3] = Acc(L, 0)
                a.addmul(b, Tm[n], P[2][n[2] - 2 * m3], 'L1')
        U = {n2: {m3: a.unpack() for m3, a in d.items()} for n2, d in Uacc.items()}
        del Uacc
        # level 2: Vv[(m2, m3)] = sum_{n2} binom(n2/2, m2) U[n2][m3] P2[n2 - 2 m2]
        Vacc = {}
        for n2, d in U.items():
            for m3, u in d.items():
                for m2 in range(M + 1 - m3):
                    b = binom_q(n2 * half, m2)
                    if b == 0:
                        continue
                    a = Vacc.get((m2, m3))
                    if a is None:
                        a = Vacc[(m2, m3)] = Acc(L, 0)
                    a.addmul(b, u, P[1][n2 - 2 * m2], 'L2')
        del U
        Vv = {k: a.unpack() for k, a in Vacc.items()}
        del Vacc
        # level 3: h[(m1, m2, m3)] += binom(n1/2, m1) Vv[(m2, m3)] P1[n1 - 2 m1]
        for (m2, m3), v in Vv.items():
            for m1 in range(M + 1 - m2 - m3):
                b = binom_q(n1 * half, m1)
                if b == 0:
                    continue
                hacc[(m1, m2, m3)].addmul(b, v, P[0][n1 - 2 * m1], 'L3')
        log(f'  n1={n1}: {len(ns)} groups, products so far {len(L.log) - nprod0} ({time.time() - t0:.1f}s)')
    h = {m: a.unpack() for m, a in hacc.items()}
    del hacc
    log(f'h_m built: {len(h)} models, {len(L.log)} products, {L.n_unpack} unpacks ({time.time() - t0:.1f}s)')
    rep['h_eps_max'] = max(up(f.eps) for f in h.values())

    # ---- sanity: H~(0, phi_nom) vs H(z*) (SR-1)
    xs = [float(Fraction(s)) for s in json.loads((HERE / 'results/sr1.json').read_text())['nominal']['decimals']]
    zst = [complex(xs[j], -xs[j + 3]) / math.sqrt(2) for j in range(3)]
    wst = [sum(float(V[j][k]) * zst[j] for j in range(3)) for k in range(3)]
    qn = [math.atan2(x.imag, x.real) for x in wst]
    phin = (arb(qn[0] - qn[2]), arb(qn[1] - qn[2]))
    un = [abs(wst[j]) ** 2 - float(B0[j].eval(*phin)) for j in range(3)]
    Hn = ZERO
    for m, f in h.items():
        t = f.eval(*phin)
        for j in range(3):
            t *= arb(un[j]) ** m[j]
        Hn += t
    rep['sanity'] = {'u_nominal': un, 'H_tilde_nominal': float(Hn), 'H_exact_SR1': -5.22983516352663049817339571061e-8}
    log('sanity: u at z* =', un, ' H~(z*) =', float(Hn))

    # ---- derivative models of H~ (degree <= Lv)
    mlist = ft.monomials(Lv)
    DH = [{}, {}]
    PH = [{}, {}]
    for m in mlist:
        for a in range(2):
            ea = list(m)
            ea[a] += 1
            e3 = list(m)
            e3[2] += 1
            DH[a][m] = lincomb(L, [(m[a] + 1, h[tuple(ea)]), (-(m[2] + 1), h[tuple(e3)])])
            PH[a][m] = h[m].dphi(a)
    del h
    # ---- tails of dH~ beyond degree Lv (sup bounds)
    tails = Tails(Brange, Fraction(r), Lv)
    supT = {n: sum((abs(to_arb(v)) for v in d.values()), ZERO) for n, d in T.items()}
    supdT = [{n: l1_k(d, a) for n, d in T.items()} for a in range(2)]
    supdB = [[l1_k(B0c[j], a) for j in range(3)] for a in range(2)]
    tu = [ZERO, ZERO, ZERO]
    tphi = [ZERO, ZERO]
    for n in T:
        al = tuple(Fraction(x, 2) for x in n)
        for i in range(3):
            if n[i]:
                ai = list(al)
                ai[i] -= 1
                tu[i] += supT[n] * abs(to_arb(al[i])) * tails.tail(tuple(ai))
        ta = tails.tail(al)
        for a in range(2):
            s = supdT[a][n] * ta
            for j in range(3):
                if n[j]:
                    aj = list(al)
                    aj[j] -= 1
                    s += supT[n] * abs(to_arb(al[j])) * supdB[a][j] * tails.tail(tuple(aj))
            tphi[a] += s
    tailD = [tu[0] + tu[2], tu[1] + tu[2]]
    rep['tails'] = {'dH/du_i': [up(x) for x in tu], 'D_a H': [up(x) for x in tailD], 'dH/dphi_a': [up(x) for x in tphi]}
    log('tails', rep['tails'], f'({time.time() - t0:.1f}s)')

    # ---- per observable: F models, bracket, faces
    rpow = [ra ** d for d in range(2 * Lv + 3)]
    rows = []
    L.stage = 'bracket'
    for j in range(3):
        Fm = {m: FM.from_coeffs(L, d, 0) for m, d in Fd[j].items()}
        LF = max(sum(m) for m in Fm)
        # faces: E = F_j - c_j - u_j ; c_j = F_j(z*) (float, then exact)
        cj = ZERO
        for m, f in Fm.items():
            t = f.eval(*phin)
            for i in range(3):
                t *= arb(un[i]) ** m[i]
            cj += t
        cj = Fraction(float(cj.mid()))
        Esup = ZERO
        for m, f in Fm.items():
            d = dict(Fd[j][m])
            if sum(m) == 0:
                d[(0, 0)] = d.get((0, 0), 0) - cj
            if sum(m) == 1 and m[j] == 1:
                d[(0, 0)] = d.get((0, 0), 0) - 1
            d = {k: v for k, v in d.items() if v != 0}
            if d:
                Esup += FM.from_coeffs(L, d, 0).n1 * rpow[sum(m)]
        margin = float((ra - Esup - to_arb(Fraction(delta))).lower())
        # derivative models of F
        DF = [{}, {}]
        PF = [{}, {}]
        zero = None
        for m in ft.monomials(LF):
            for a in range(2):
                PF[a][m] = Fm[m].dphi(a)
                if sum(m) < LF:
                    ea = list(m)
                    ea[a] += 1
                    e3 = list(m)
                    e3[2] += 1
                    DF[a][m] = lincomb(L, [(m[a] + 1, Fm[tuple(ea)]), (-(m[2] + 1), Fm[tuple(e3)])])
        del Fm
        # bracket G' = sum_a PF_a * DH_a - DF_a * PH_a (odd)
        G = {m: Acc(L, 1) for m in mlist}
        skipped = ZERO
        nskip = 0
        dropped = ZERO
        tailx = ZERO
        for a in range(2):
            for (A, B, sg, tl) in ((PF[a], DH[a], 1, tailD[a]), (DF[a], PH[a], -1, tphi[a])):
                adeg = defaultdict(lambda: ZERO)
                bdeg = defaultdict(lambda: ZERO)
                for s, x in A.items():
                    adeg[sum(s)] += x.n1 * rpow[sum(s)]
                for t, y in B.items():
                    bdeg[sum(t)] += (y.n1 + y.eps) * rpow[sum(t)]
                for d1, x in adeg.items():
                    for d2, y in bdeg.items():
                        if d1 + d2 > Lv:
                            dropped += x * y
                supA = sum(adeg.values(), ZERO)
                tailx += supA * tl
                for s, x in A.items():
                    xs_ = x.n1 * rpow[sum(s)]
                    if float(x.n1.upper()) == 0:
                        continue
                    for t, y in B.items():
                        if sum(s) + sum(t) > Lv:
                            continue
                        bound = xs_ * (y.n1 + y.eps) * rpow[sum(t)]
                        if float(bound.upper()) < args.skip:
                            skipped += bound
                            nskip += 1
                            continue
                        m = (s[0] + t[0], s[1] + t[1], s[2] + t[2])
                        G[m].addmul(sg, x, y, 'bracket')
            log(f'  j={j} a={a}: products {len(L.log)} skipped {nskip} ({time.time() - t0:.1f}s)')
        trunc = ZERO
        err = ZERO
        fx = 0.0
        bydeg = [0.0] * (Lv + 1)
        for m, g in G.items():
            n1, nW = g.norms()
            trunc += n1 * rpow[sum(m)]
            err += g.eps * rpow[sum(m)]
            fx += g.fx * float(rpow[sum(m)].upper())
            bydeg[sum(m)] += up(n1 * rpow[sum(m)])
        eta = trunc + err + skipped + dropped + tailx
        row = {'j': j, 'c_j': str(cj), 'eta': up(eta), 'trunc': up(trunc), 'fourier_balls': up(err),
               'skipped_pairs': up(skipped), 'n_skipped': nskip, 'dropped_products': up(dropped),
               'H_tails': up(tailx), 'trunc_by_degree': bydeg,
               'fx_coeff_of_2^-p': fx, 'face_sup_E': up(Esup), 'face_margin_over_delta': margin / delta,
               'T_years': (delta / 2) / up(eta)}
        rows.append(row)
        log(f'j={j}: eta={row["eta"]:.3e} (trunc {row["trunc"]:.2e}, balls {row["fourier_balls"]:.1e}, '
            f'skipped {row["skipped_pairs"]:.1e} [{nskip}], dropped {row["dropped_products"]:.1e}, '
            f'tails {row["H_tails"]:.1e}); T = {row["T_years"]:.3e} yr; face margin {margin / delta:.4f} delta; '
            f'by degree ' + ' '.join('%.0e' % x for x in bydeg) + f' ({time.time() - t0:.1f}s)')
        del G, DF, PF
    rep['rows'] = rows
    rep['T_years'] = min(r_['T_years'] for r_ in rows)
    rep['face_margin_min_over_delta'] = min(r_['face_margin_over_delta'] for r_ in rows)
    # fixed-point precision needed: eta(p) = eta + fx 2^-p <= 1.1 eta
    rep['fixed_point_bits_for_10pct'] = max(
        math.ceil(math.log2(max(r_['fx_coeff_of_2^-p'], 1e-300) / (0.1 * r_['eta']))) for r_ in rows)
    # ---- (e) eccentricities on the tube (float grid + Lipschitz margins)
    rep['eccentricity'] = eccentricities(B0c, Ibar, Brange, V, data, r)
    log('eccentricity', rep['eccentricity'])
    rep['ops'] = {'products': len(L.log), 'unpacks': L.n_unpack,
                  'by_stage': {s: sum(1 for x in L.log if x[0] == s) for s in ('powers', 'Hbuild', 'bracket')}}
    rep['verdict'] = 'PASS' if (rep['T_years'] >= 1e10 and rep['face_margin_min_over_delta'] >= 0.3
                                and min(reg) > 0) else 'FAIL'
    rep['seconds'] = time.time() - t0
    rep['log'] = LOG
    tag = args.tag or ('sr4-quick' if args.quick else f'sr4-{args.run}-Lv{Lv}-d{delta:g}')
    (HERE / 'results').mkdir(exist_ok=True)
    (HERE / f'results/{tag}.json').write_text(json.dumps(rep, indent=1, default=str) + '\n')
    oplog = defaultdict(int)
    for st, kind, ca, cb in L.log:
        oplog[(st, kind, ca, cb)] += 1
    (HERE / f'results/{tag}-ops.json').write_text(json.dumps(
        {'CP': L.CP, 'KH': L.KH, 'Lv': Lv, 'unpacks': L.n_unpack,
         'products': [list(k) + [v] for k, v in sorted(oplog.items())]}, indent=0) + '\n')
    log(f"verdict {rep['verdict']}: T = {rep['T_years']:.3e} yr, face margin {rep['face_margin_min_over_delta']:.4f} delta, "
        f"fixed-point bits {rep['fixed_point_bits_for_10pct']} ({rep['seconds']:.0f}s)")
    return 0


THETAS = np.linspace(-0.6, 0.6, 25)


def zono_lb(a, s0, ds):
    """Lower bound of min |sum_k a_k (s0_k + t_k)| over |t_k| <= ds_k: for unit u, the min is >=
    Re(c conj u) - sum_k ds_k |Re(a_k conj u)| (support function of the zonotope), c = sum a_k s0_k;
    the best of several directions u = (c/|c|) e^{i theta} is taken."""
    c = sum(a[k] * s0[k] for k in range(3))
    cu = c / np.maximum(np.abs(c), 1e-300)
    best = None
    for th in THETAS:
        u = cu * np.exp(1j * th)
        lb = np.real(c * np.conj(u)) - sum(ds[k] * np.abs(np.real(a[k] * np.conj(u))) for k in range(3))
        best = lb if best is None else np.maximum(best, lb)
    return np.maximum(best, 0)


def eval_even_at(coeffs, const, f1, f2):
    """const + sum a_k cos(k1 f1 + k2 f2) at arrays of points (float)."""
    ks = np.array(list(coeffs.keys()), dtype=float)
    av = np.array([float(v) for v in coeffs.values()])
    ang = np.multiply.outer(f1, ks[:, 0]) + np.multiply.outer(f2, ks[:, 1])
    return float(const) + np.cos(ang) @ av


def eccentricities(B0c, Ibar, Brange, V, data, r, G=2048):
    """Ranges of e_j over the tube, from Gamma_j = |z_j|^2 = |sum_k a_k s_k|^2, a_k = V'_jk e^{i q_k}, s_k = sqrt(I_k).

    At each grid angle, s ranges over a box [sqrt(B0 - r), sqrt(B0 + r)]: |.|^2 is convex in s, so its max is
    at one of the 8 vertices; its min is >= zono_lb^2 (support-function bound of the zonotope; s0 = sqrt(B0)).  Between
    grid angles the vertex functions vary by at most Lphi * h (h = half spacing per axis, both axes), with
    Lphi from l1 bounds of dB0/dphi.  Float evaluation (relative error far below the margins) is not enclosed.
    """
    Lam = [float(x) for x in data['parameters']['Lambda_star']]
    Vf = [[float(x) for x in row] for row in V]
    B = [grid_eval_even(B0c[j], Ibar[j], G) for j in range(3)]
    ph = np.arange(G) * 2 * np.pi / G
    P1, P2 = np.meshgrid(ph, ph, indexing='ij')
    ez = [np.exp(1j * P1), np.exp(1j * P2), np.ones_like(P1)]  # e^{i q_k} with q3 = 0
    Imax = [float(b[1].upper()) + r for b in Brange]
    Imin = [float(b[0].lower()) - r for b in Brange]
    dB = [sum(up(l1_k(B0c[k], a)) for a in range(2)) for k in range(3)]  # |dB0_k/dphi1| + |dB0_k/dphi2|
    hh = math.pi / G
    out = []
    for j in range(3):
        a = [Vf[j][k] * ez[k] for k in range(3)]
        gmax = np.full(P1.shape, -np.inf)
        for sg in np.array(np.meshgrid([-1, 1], [-1, 1], [-1, 1])).reshape(3, -1).T:
            zz = sum(a[k] * np.sqrt(B[k] + sg[k] * r) for k in range(3))
            gmax = np.maximum(gmax, np.abs(zz) ** 2)
        s0 = [np.sqrt(B[k]) for k in range(3)]
        ds = [np.maximum(np.sqrt(B[k] + r) - s0[k], s0[k] - np.sqrt(B[k] - r)) for k in range(3)]
        gmin = zono_lb(a, s0, ds) ** 2
        # Lipschitz in phi (sup-norm step h on each axis): |d/dphi_a sum a_k s_k| <= sum_k |V_jk| (|ds_k/dphi_a| +
        # s_k |dq_k/dphi_a|), |ds_k/dphi| <= |dB0_k/dphi| / (2 sqrt(Imin_k)); Gamma = |.|^2 => factor 2 sqrt(Gamma_max)
        smax = [math.sqrt(Imax[k]) for k in range(3)]
        lin = sum(abs(Vf[j][k]) * (dB[k] / (2 * math.sqrt(Imin[k])) + smax[k] * (1 if k < 2 else 0)) for k in range(3))
        zmax = sum(abs(Vf[j][k]) * smax[k] for k in range(3))
        marg = 2 * zmax * lin * hh + (lin * hh) ** 2
        # progressive refinement (rigorous for any cap): refine cells in order of their grid value; the
        # unrefined rest is bounded by value -/+ marg
        ref = 8
        sub = (np.arange(ref) + 0.5) / ref * 2 - 1  # offsets in units of hh, covering [-hh, hh]
        lohi = []
        for kind, arr in (('min', gmin), ('max', gmax)):
            flat = arr.ravel()
            order = np.argsort(flat) if kind == 'min' else np.argsort(-flat)
            best = np.inf if kind == 'min' else -np.inf
            nref = 0
            for idx in order[:300]:
                i1, i2 = divmod(int(idx), G)
                f1 = ph[i1] + np.repeat(sub, ref).reshape(ref, ref) * hh
                f2 = ph[i2] + np.tile(sub, ref).reshape(ref, ref) * hh
                Bl = [eval_even_at(B0c[k], Ibar[k], f1, f2) for k in range(3)]
                al = [Vf[j][0] * np.exp(1j * f1), Vf[j][1] * np.exp(1j * f2), Vf[j][2] * np.ones_like(f1)]
                if kind == 'max':
                    v = max(float(np.max(np.abs(sum(al[k] * np.sqrt(Bl[k] + sg[k] * r) for k in range(3))) ** 2))
                            for sg in np.array(np.meshgrid([-1, 1], [-1, 1], [-1, 1])).reshape(3, -1).T)
                    best = max(best, v + marg / ref)
                else:
                    s0l = [np.sqrt(Bl[k]) for k in range(3)]
                    dsl = [np.maximum(np.sqrt(Bl[k] + r) - s0l[k], s0l[k] - np.sqrt(Bl[k] - r)) for k in range(3)]
                    v = float((zono_lb(al, s0l, dsl) ** 2).min())
                    best = min(best, v - marg / ref)
                nref += 1
            rest = order[nref:]
            if kind == 'min':
                lohi.append(min(best, float(flat[rest].min()) - marg if len(rest) else np.inf))
            else:
                lohi.append(max(best, float(flat[rest].max()) + marg if len(rest) else -np.inf))
        glo, ghi = lohi
        glo = max(glo, 0.0)
        ghi = ghi + 1e-12 * ghi
        e = lambda g: math.sqrt(1 - (1 - g / Lam[j]) ** 2)  # noqa: E731
        out.append({'Gamma_range': [glo, ghi], 'e_range': [e(glo), e(ghi)], 'margin_Gamma_grid': marg,
                    'margin_Gamma_refined': marg / ref})
    return out


if __name__ == '__main__':
    sys.exit(main())
