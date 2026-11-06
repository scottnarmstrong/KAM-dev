#!/usr/bin/env python3
"""N7 ledger producer, H build (T2-CONF): inputs, witnesses, powers and the nested Horner of h_m.

Mirrors the kernel checks of KAM/EffectiveStability/Tube/Engine bit-exactly (claims are computed with
the same formulas, as exact Fractions, then rounded up to short dyadics).  Outputs a ledger plan
(JSON + pickled literals) consumed by emit.py, which writes the Lean data and check modules.

Usage: python3 produce.py [--small] [--out DIR]
"""
from __future__ import annotations

import argparse
import json
import math
import pickle
import sys
import time
from collections import defaultdict
from fractions import Fraction as Fr
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE))
from packing import Lit, lay_len, l1_guard, up  # noqa: E402
from poly import Poly, mul, hexn  # noqa: E402

LOG = []


def log(*a):
    s = ' '.join(str(x) for x in a)
    LOG.append(s)
    print(s, flush=True)


def gb(n, m):
    """gbinom(n/2, m) = prod_{i<m} (n/2 - i) / m!"""
    r = Fr(1)
    for i in range(m):
        r *= Fr(n, 2) - i
        r /= i + 1
    return r


def monomials(L):
    out = []
    for d in range(L + 1):
        for a in range(d, -1, -1):
            for b in range(d - a, -1, -1):
                out.append((a, b, d - a - b))
    return out


class Cfg:
    def __init__(self, small):
        self.small = small
        if small:
            self.M, self.CT, self.CP, self.KH, self.maxdeg, self.p = 3, 3, 8, 16, 6, 60
        else:
            self.M, self.CT, self.CP, self.KH, self.maxdeg, self.p = 9, 9, 30, 60, 18, 80
        self.b = self.p + 2          # compact digit width (mantissas < 2^p, offset 2^(b-1))
        self.S = 2 * (self.CT + 2 * self.CP) + 1  # stride: the largest product layout is U (CT+CP) x P (CP)
        self.salt = 0

    def next_salt(self):
        self.salt += 1
        return self.salt


# ------------------------------------------------------------------------------------------- models
class M:
    """A ledger model: a literal (or exact combination) with its certificate claims."""

    def __init__(self, name, poly, q, e0, e1, kind='lit', sym=False, cfg=None):
        self.name, self.poly, self.q = name, poly, Fr(q)
        self.e0, self.e1 = up(e0), up(e1)
        self.n = poly.l1()
        self.kind = kind
        self.sym = sym
        if kind == 'lit':
            self.lit = Lit(poly.C, poly.par, self.q, poly.s, cfg.b, cfg.next_salt())
            if sym:
                assert self.lit.sym_ok(), ('not symmetric', name)
        else:
            self.lit = None

    @property
    def C(self):
        return self.poly.C


def scale_round(coeffs, C, p):
    """mantissas of exact rational coefficients {(c, r): Fraction} at scale 2^-e (max |m| < 2^p)"""
    mx = max(abs(v) for v in coeffs.values())
    e = p - 1 - (mx.numerator.bit_length() - mx.denominator.bit_length())
    while max(abs(v) for v in coeffs.values()) * (Fr(2) ** e) >= 2 ** p:
        e -= 1
    s = {}
    for k, v in coeffs.items():
        x = v * (Fr(2) ** e)
        m = math.floor(x + Fr(1, 2)) if x >= 0 else -math.floor(-x + Fr(1, 2))
        if m:
            s[k] = m
    return s, Fr(1, 2 ** e) if e >= 0 else Fr(2 ** -e)


def input_model(name, coeffs, C, cfg):
    """an exact dense cosine input (T_n, B_j): rounded literal + exact errors (inputCheck)"""
    s, q = scale_round(coeffs, C, cfg.p)
    K = 2 * C + 1
    e0 = Fr(0)
    e1 = [Fr(0), Fr(0)]
    for r in range(K):
        for c in range(K):
            d = abs(coeffs.get((c, r), Fr(0)) - q * s.get((c, r), 0))
            e0 += d
            e1[0] += abs(c - C) * d
            e1[1] += abs(r - C) * d
    return M(name, Poly(C, False, s), q, e0, max(e1), cfg=cfg, sym=True), {'data': coeffs, 'e0x': e0,
                                                                         'e1x': e1}


# --------------------------------------------------------------------------------------- the steps
class Term:
    def __init__(self, rho, A: M, B: M, tag=None):
        self.rho, self.A, self.B, self.tag = Fr(rho), A, B, tag

    def r(self):
        sg = -1 if (self.A.poly.par and self.B.poly.par) else 1
        return self.rho * self.A.q * self.B.q * sg

    def err0(self):
        A, B = self.A, self.B
        return abs(A.q) * A.n * B.e0 + abs(B.q) * B.n * A.e0 + A.e0 * B.e0

    def err1(self):
        A, B = self.A, self.B
        return (abs(A.q) * (A.C * A.n) * B.e0 + abs(A.q) * A.n * B.e1 + abs(B.q) * (B.C * B.n) * A.e0
                + abs(B.q) * B.n * A.e1 + A.e1 * B.e0 + A.e0 * B.e1)


def comb(terms, cfg, mxb):
    """the exact combination X = sum c_t conv(A_t, B_t) with Q, c_t (sh = 0), E0, E1, BX"""
    rs = [t.r() for t in terms]
    L = 1
    for r in rs:
        L = L * r.denominator // math.gcd(L, r.denominator)
    Ns = [int(r * L) for r in rs]
    G = 0
    for n in Ns:
        G = math.gcd(G, n)
    Q = Fr(G, L)
    cs = [n // G for n in Ns]
    X = None
    for c, t in zip(cs, terms):
        pr = mul(t.A.poly, t.B.poly)  # includes the sign psgn(pA and pB)
        # kernel X = sum c * conv(raw); mul already applied psgn; the kernel's c absorbs psgn via r
        sg = -1 if (t.A.poly.par and t.B.poly.par) else 1
        pr = pr.scale_int(c * sg)
        X = pr if X is None else X.add(pr)
    E0 = sum((abs(t.rho) * t.err0() for t in terms), Fr(0))
    E1 = sum((abs(t.rho) * t.err1() for t in terms), Fr(0))
    BX = sum(abs(c) * t.A.n * mxb for c, t in zip(cs, terms))
    return X, Q, cs, up(E0), up(E1), BX


class Ledger:
    def __init__(self, cfg):
        self.cfg = cfg
        self.models = {}
        self.steps = []
        self.wreq = 0  # bits needed for the slot width w

    def need(self, bits):
        self.wreq = max(self.wreq, bits)

    def add(self, m):
        self.models[m.name] = m
        return m

    def out_step(self, name, kind, terms, Cp, p_out, sym, keep):
        """a sum of products compared with a new output literal (litCheck)"""
        cfg = self.cfg
        mxb = 1 << (cfg.b - 1)
        X, Q, cs, E0, E1, BX = comb(terms, cfg, mxb)
        assert X.C == Cp
        mxX = X.maxabs()
        a = max(0, mxX.bit_length() - cfg.p)
        O = X.trunc_round(cfg.CP, keep, a)
        aO = 1 << a
        qO = Q * aO
        D = X.add(O.embed(Cp).scale_int(-aO))
        N = lay_len(Cp, cfg.S)
        slots = list(D.s.values()) + [0]
        l1D = D.l1()
        lD = max(abs(v) for v in slots).bit_length() + 1
        F0 = up(abs(Q) * l1D)
        F1 = up(abs(Q) * Cp * l1D)
        e0, e1 = E0 + F0, E1 + F1
        m = M(name, O, qO, e0, e1, cfg=cfg, sym=sym)
        # width requirements (outCheck, prodCheck, l1Ok of D and of the literal)
        self.need((2 * (BX + aO * mxb)).bit_length() + 1)
        self.need((N << lD).bit_length() + 1)
        self.need(lD + 2)
        self.need((N << (cfg.b - 1)).bit_length() + 1)
        self.steps.append({'kind': kind, 'name': name, 'terms': [(t.tag, str(t.rho), t.A.name, t.B.name) for t in terms],
                           'Q': Q, 'cs': cs, 'E0': E0, 'E1': E1, 'BX': BX, 'aX': 1, 'aO': aO, 'lD': lD,
                           'F0': F0, 'F1': F1, 'e0': m.e0, 'e1': m.e1, 'n': m.n})
        return self.add(m)

    def comb_step(self, name, terms):
        """an exact combination used as an operand (combCheck)"""
        cfg = self.cfg
        mxb = 1 << (cfg.b - 1)
        X, Q, cs, E0, E1, BX = comb(terms, cfg, mxb)
        N = lay_len(X.C, cfg.S)
        l = max(X.maxabs(), 1).bit_length() + 1
        self.need((2 * BX).bit_length() + 1)
        self.need((N << l).bit_length() + 1)
        m = M(name, X, Q, E0, E1, kind='exact', cfg=cfg)
        self.steps.append({'kind': 'comb', 'name': name, 'terms': [(t.tag, str(t.rho), t.A.name, t.B.name) for t in terms],
                           'Q': Q, 'cs': cs, 'E0': E0, 'E1': E1, 'BX': BX, 'l': l, 'n': m.n})
        return self.add(m)


# ------------------------------------------------------------------------------------------- data
def load_T(cfg):
    hw = json.loads((ROOT / 'scripts/sjsu/rigor/results/hw.json').read_text())
    T = defaultdict(dict)
    for key, val in hw['Hw'].items():
        bs, bps = key.split('|')
        b = [int(x) for x in bs.split(',')]
        bp = [int(x) for x in bps.split(',')]
        n = tuple(b[i] + bp[i] for i in range(3))
        if sum(n) > cfg.maxdeg:
            continue
        k = (b[0] - bp[0], b[1] - bp[1])
        num, den = val.split('/')
        T[n][(k[0] + cfg.CT, k[1] + cfg.CT)] = Fr(int(num), int(den))
    return dict(T)


def load_B(cfg):
    d = json.loads((ROOT / '.drafts/g2/data/literal-v1.json').read_text())
    Ibar = [Fr(x) for x in d['Ibar']]
    sig = {tuple(map(int, k.split(','))): Fr(v) for k, v in d['sigma'].items()}
    B = []
    for j in range(3):
        c = {(cfg.CP, cfg.CP): Ibar[j]}
        for (k1, k2), s in sig.items():
            if hexn(k1, k2) > cfg.KH:
                continue
            kj = (k1, k2, -k1 - k2)[j]
            if kj:
                key = (k1 + cfg.CP, k2 + cfg.CP)
                c[key] = c.get(key, 0) - kj * s
        B.append(c)
    return B


def float_coeffs(poly_coeffs_fn, C, G=256):
    """float Fourier coefficients (even) of a grid function on the box C"""
    raise NotImplementedError


def grid_eval(coeffs, C, G):
    """float values on a G x G grid of sum c cos(k.phi) (coeffs keyed by box coordinates)"""
    a = np.zeros((G, G), dtype=complex)
    for (c, r), v in coeffs.items():
        a[(c - C) % G, (r - C) % G] += float(v)
    return np.fft.ifft2(a).real * G * G


def witness_float(Bc, C, KH, G=256):
    v = grid_eval(Bc, C, G)
    outs = []
    for vals in (np.sqrt(v), 1 / np.sqrt(v)):
        f = np.fft.fft2(vals) / (G * G)
        d = {}
        for r in range(2 * C + 1):
            for c in range(2 * C + 1):
                k1, k2 = c - C, r - C
                if hexn(k1, k2) > KH:
                    continue
                x = 0.5 * (f[k1 % G, k2 % G].real + f[(-k1) % G, (-k2) % G].real)
                d[(c, r)] = Fr(float(x))
        outs.append(d)
    return outs


def exact_mul(a, b, C_out, KH):
    """exact rational product of two coefficient dicts (box coordinates), truncated to the hexagon
    of the box C_out; inputs keyed on boxes Ca, Cb (inferred), returns {(c, r): Fraction}."""
    raise NotImplementedError


def to_poly(d, C):
    """rational dict -> (Poly with integer slots, common scale)"""
    L = 1
    for v in d.values():
        L = L * v.denominator // math.gcd(L, v.denominator)
    return Poly(C, False, {k: int(v * L) for k, v in d.items()}), Fr(1, L)


def from_poly(pl, q, C_out, KH):
    """Poly with scale q -> rational dict truncated to the hexagon of the box C_out"""
    d = pl.C - C_out
    out = {}
    for (c, r), v in pl.s.items():
        cc, rr = c - d, r - d
        if 0 <= cc <= 2 * C_out and 0 <= rr <= 2 * C_out and hexn(cc - C_out, rr - C_out) <= KH:
            out[(cc, rr)] = q * v
    return out


def round_dict(d, bits):
    """round every value to a dyadic with about `bits` bits below the largest"""
    mx = max(abs(v) for v in d.values())
    e = bits - (mx.numerator.bit_length() - mx.denominator.bit_length())
    return {k: Fr(round(v * 2 ** e), 2 ** e) for k, v in d.items()}


def newton(Wf, Yf, Bmod, cfg):
    """one exact Newton step: W1 = W + Y (B - W^2)/2, Y1 = Y + Y (1 - W1 Y) (hexagon-truncated)"""
    C, KH = cfg.CP, cfg.KH
    bits = cfg.p + 24
    Wd = round_dict(Wf, 60)
    Yd = round_dict(Yf, 60)
    Bd = {k: Bmod.q * v for k, v in Bmod.poly.s.items()}
    Wp, qw = to_poly(Wd, C)
    Yp, qy = to_poly(Yd, C)
    Bp, qb = to_poly(Bd, C)
    WW = mul(Wp, Wp)
    # R = B - W^2 on the box 2C (common scale)
    L = qb.denominator * (qw * qw).denominator // math.gcd(qb.denominator, (qw * qw).denominator)
    R = Bp.embed(2 * C).scale_int(int(qb * L)).add(WW.scale_int(-int(qw * qw * L)))
    corr = from_poly(mul(Yp, R), qy / L / 2, C, KH)
    W1 = dict(Wd)
    for k, v in corr.items():
        W1[k] = W1.get(k, 0) + v
    W1 = round_dict(W1, bits)
    W1p, qw1 = to_poly(W1, C)
    E = mul(W1p, Yp)  # scale qw1 qy
    one = Poly(2 * C, False, {(2 * C, 2 * C): 1})
    L2 = (qw1 * qy).denominator
    En = one.scale_int(L2).add(E.scale_int(-int(qw1 * qy * L2)))
    corr2 = from_poly(mul(Yp, En), qy / L2, C, KH)
    Y1 = dict(Yd)
    for k, v in corr2.items():
        Y1[k] = Y1.get(k, 0) + v
    Y1 = round_dict(Y1, bits)
    # exact symmetry (even): average with the reflection
    K = 2 * C + 1
    W1 = {k: (v + W1.get((K - 1 - k[0], K - 1 - k[1]), 0)) / 2 for k, v in W1.items()}
    Y1 = {k: (v + Y1.get((K - 1 - k[0], K - 1 - k[1]), 0)) / 2 for k, v in Y1.items()}
    return W1, Y1


# ------------------------------------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--small', action='store_true')
    ap.add_argument('--out', default=None)
    args = ap.parse_args()
    cfg = Cfg(args.small)
    out = Path(args.out or (HERE / ('out-small' if args.small else 'out')))
    out.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    led = Ledger(cfg)
    keep = lambda k1, k2: hexn(k1, k2) <= cfg.KH  # noqa: E731
    T = load_T(cfg)
    log(f'T: {len(T)} groups, {sum(len(d) for d in T.values())} terms ({time.time() - t0:.1f}s)')
    Bc = load_B(cfg)
    inputs = {}
    # ---- inputs
    for n, d in sorted(T.items()):
        m, info = input_model(f'T_{n[0]}_{n[1]}_{n[2]}', d, cfg.CT, cfg)
        led.add(m); inputs[m.name] = info
    Bm = []
    for j in range(3):
        m, info = input_model(f'B_{j}', Bc[j], cfg.CP, cfg)
        led.add(m); inputs[m.name] = info; Bm.append(m)
    one = led.add(M('one', Poly(cfg.CP, False, {(cfg.CP, cfg.CP): 1 << cfg.p}), Fr(1, 2 ** cfg.p), 0, 0,
                    cfg=cfg, sym=True))
    inputs['one'] = {'data': {(cfg.CP, cfg.CP): Fr(1)}, 'e0x': Fr(0), 'e1x': [Fr(0), Fr(0)]}
    log(f'inputs: max T e0 {max(float(led.models[k].e0) for k in led.models if k.startswith("T_")):.2e} '
        f'B e0 {[float(m.e0) for m in Bm]} ({time.time() - t0:.1f}s)')
    # ---- witnesses and powers
    P = []
    wit = []
    for j in range(3):
        Wf, Yf = witness_float(Bc[j], cfg.CP, cfg.KH)
        Wf, Yf = newton(Wf, Yf, Bm[j], cfg)
        sW, qW = scale_round(Wf, cfg.CP, cfg.p)
        sY, qY = scale_round(Yf, cfg.CP, cfg.p)
        W = M(f'W_{j}', Poly(cfg.CP, False, sW), qW, 0, 0, cfg=cfg, sym=True)
        Y = M(f'Y_{j}', Poly(cfg.CP, False, sY), qY, 0, 0, cfg=cfg, sym=True)
        # sqrt witness: W*W against B
        X, Q, cs, E0, E1, BX = comb([Term(1, W, W)], cfg, 1 << (cfg.b - 1))
        Bpo = Bm[j]
        aO = Q.denominator // Bpo.q.denominator if Bpo.q.denominator <= Q.denominator else None
        assert Bpo.q * 1 == Q * aO
        Cp = 2 * cfg.CP
        D = X.add(Bpo.poly.embed(Cp).scale_int(-aO))
        l1D = D.l1()
        F0s, F1s = up(abs(Q) * l1D), up(abs(Q) * Cp * l1D)
        rho = up(Bpo.e0 + E0 + F0s)
        rhop = up(Bpo.e1 + E1 + F1s)
        Bmin = Bpo.q * (2 * Bpo.poly.s.get((cfg.CP, cfg.CP), 0) - Bpo.n) - Bpo.e0
        assert Bmin > 0, ('B lower bound fails', j, float(Bmin))
        sig0 = Fr(math.floor(math.sqrt(float(Bmin)) * 2 ** 60), 2 ** 60)
        while sig0 * sig0 > Bmin:
            sig0 -= Fr(1, 2 ** 60)
        w0 = W.q * (2 * W.poly.s.get((cfg.CP, cfg.CP), 0) - W.n)
        assert w0 > 0
        om1 = W.q * (W.C * W.n)
        eW0 = up(rho / (sig0 + w0))
        eW1 = up((rhop + 2 * (rho / (sig0 + w0)) * om1) / (2 * sig0))
        W.e0, W.e1 = eW0, eW1
        W.e0, W.e1 = eW0, eW1
        lD = max(abs(v) for v in D.s.values()).bit_length() + 1
        led.need((2 * (BX + aO * (1 << (cfg.b - 1)))).bit_length() + 1)
        led.need((lay_len(Cp, cfg.S) << lD).bit_length() + 1)
        led.steps.append({'kind': 'sqrt', 'name': W.name, 'B': Bpo.name, 'Q': Q, 'E0': E0, 'E1': E1, 'BX': BX,
                          'aX': 1, 'aO': aO, 'lD': lD, 'F0': F0s, 'F1': F1s,
                          'rho': rho, 'rhop': rhop, 'sigma0': sig0, 'w0': w0, 'e0': eW0, 'e1': eW1,
                          'nW': W.n})
        led.add(W)
        # inverse: W*Y against one
        X, Q, cs, E0, E1, BX = comb([Term(1, W, Y)], cfg, 1 << (cfg.b - 1))
        X2, _, _, _, _, _ = comb([Term(1, W.__class__('Wx', W.poly, W.q, 0, 0, kind='exact'),
                                       Y.__class__('Yx', Y.poly, Y.q, 0, 0, kind='exact'))], cfg, 1)
        aO = one.q / Q
        assert aO.denominator == 1
        aO = int(aO)
        D = X.add(one.poly.embed(Cp).scale_int(-aO))
        l1D = D.l1()
        F0i, F1i = up(abs(Q) * l1D), up(abs(Q) * Cp * l1D)
        qq = up(E0 + F0i)
        qqp = up(E1 + F1i)
        Y0 = Y.q * Y.n
        Y1 = Y.q * (Y.C * Y.n)
        eY0 = up((qq + eW0 * Y0) / sig0)
        eY1 = up((qqp + eW1 * Y0 + eW0 * Y1) / sig0 + (qq + eW0 * Y0) * (om1 + eW1) / sig0 ** 2)
        Y.e0, Y.e1 = eY0, eY1
        lD = max(abs(v) for v in D.s.values()).bit_length() + 1
        led.need((2 * (BX + aO * (1 << (cfg.b - 1)))).bit_length() + 1)
        led.need((lay_len(Cp, cfg.S) << lD).bit_length() + 1)
        led.steps.append({'kind': 'invsqrt', 'name': Y.name, 'W': W.name, 'Q': Q, 'E0': E0, 'E1': E1, 'BX': BX,
                          'aX': 1, 'aO': aO, 'lD': lD, 'F0': F0i, 'F1': F1i,
                          'qq': qq, 'qqp': qqp, 'sigma0': sig0, 'e0': eY0, 'e1': eY1, 'nY': Y.n})
        led.add(Y)
        wit.append({'j': j, 'rho': float(rho), 'sigma0': float(sig0), 'w0': float(w0), 'eW0': float(eW0),
                    'eW1': float(eW1), 'qq': float(qq), 'eY0': float(eY0), 'eY1': float(eY1)})
        # powers
        Pj = {0: one, 1: W, -1: Y, 2: Bpo}
        for k in range(3, 2 * cfg.M + 1):
            Pj[k] = led.out_step(f'P_{j}_{k}', 'pow', [Term(1, Pj[k - 2], Bpo, tag=('pos', j, k))], 2 * cfg.CP,
                                 False, True, keep)
        Pj[-2] = led.out_step(f'P_{j}_m2', 'pow', [Term(1, Y, Y, tag=('neg2', j))], 2 * cfg.CP, False, True,
                              keep)
        for k in range(3, 2 * cfg.M + 2):
            Pj[-k] = led.out_step(f'P_{j}_m{k}', 'pow', [Term(1, Pj[-(k - 2)], Pj[-2], tag=('neg', j, k))],
                                  2 * cfg.CP, False, True, keep)
        P.append(Pj)
        log(f'  j={j}: witness {wit[-1]}; powers done ({time.time() - t0:.1f}s)')
    # ---- nested Horner: U (exact), V (literal), h (literal)
    Mx = cfg.M
    ns = sorted(T)
    n1s = sorted({n[0] for n in ns})
    Vm = {}
    for n1 in n1s:
        n2s = sorted({n[1] for n in ns if n[0] == n1})
        for m3 in range(Mx + 1):
            U = {}
            for n2 in n2s:
                uidx = [n for n in ns if n[0] == n1 and n[1] == n2 and gb(n[2], m3) != 0]
                if not uidx:
                    continue
                terms = [Term(gb(n[2], m3), led.models[f'T_{n[0]}_{n[1]}_{n[2]}'], P[2][n[2] - 2 * m3], tag=n)
                         for n in uidx]
                U[n2] = led.comb_step(f'U_{n1}_{n2}_{m3}', terms)
            for m2 in range(Mx + 1 - m3):
                vidx = [n2 for n2 in n2s if gb(n2, m2) != 0 and n2 in U]
                if not vidx:
                    continue
                terms = [Term(gb(n2, m2), U[n2], P[1][n2 - 2 * m2], tag=n2) for n2 in vidx]
                Vm[(n1, m2, m3)] = led.out_step(f'V_{n1}_{m2}_{m3}', 'V', terms, cfg.CT + 2 * cfg.CP, False,
                                                False, keep)
        log(f'  n1={n1}: V models {len(Vm)}, steps {len(led.steps)} ({time.time() - t0:.1f}s)')
    Hm = {}
    for m in monomials(Mx):
        m1, m2, m3 = m
        hidx = [n1 for n1 in n1s if gb(n1, m1) != 0 and (n1, m2, m3) in Vm]
        if not hidx:
            continue
        terms = [Term(gb(n1, m1), Vm[(n1, m2, m3)], P[0][n1 - 2 * m1], tag=n1) for n1 in hidx]
        Hm[m] = led.out_step(f'H_{m1}_{m2}_{m3}', 'H', terms, 2 * cfg.CP, False, False, keep)
    log(f'h: {len(Hm)} models; ledger: {len(led.models)} models, {len(led.steps)} steps, '
        f'w >= {led.wreq} ({time.time() - t0:.1f}s)')
    rep = {'cfg': vars(cfg), 'w_required': led.wreq, 'n_models': len(led.models), 'n_steps': len(led.steps),
           'witnesses': wit,
           'H_err': {f'{m}': [float(h.e0), float(h.e1)] for m, h in Hm.items()},
           'V_err_max': [max(float(v.e0) for v in Vm.values()), max(float(v.e1) for v in Vm.values())],
           'seconds': time.time() - t0, 'log': LOG}
    (out / 'hbuild.json').write_text(json.dumps(rep, indent=1, default=str) + '\n')
    with open(out / 'hbuild.pkl', 'wb') as f:
        pickle.dump({'cfg': cfg, 'models': led.models, 'steps': led.steps, 'inputs': inputs,
                     'wreq': led.wreq, 'T': T, 'B': Bc}, f)
    return 0


if __name__ == '__main__':
    sys.exit(main())
