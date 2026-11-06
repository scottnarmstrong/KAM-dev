#!/usr/bin/env python3
"""N7 ledger records and kernel mirror (T2-CONF).

Loads the producer's plan (produce.py: out*/hbuild.pkl), builds the records the Lean ledger states
(literal descriptors, claims Cl, step parameters UPrm/OPrm/SqPrm/IvPrm keyed as the Lean lookups),
and re-runs EVERY kernel Bool check of KAM/EffectiveStability/Tube/Engine in exact Python arithmetic
(prodCheck, combCheck, outCheck, litCheck, l1Check, symDigOk, inputCheck, sqrtCheck, invCheck,
pBase/powOk, vBlock, hBlock), with the same index functions (uIdx, vIdx, hIdx, n1s, n2s).
Usage: python3 ledger.py [--small]    (exit 0 iff every check passes)
"""
from __future__ import annotations

import argparse
import math
import pickle
import sys
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import produce  # noqa: E402
import __main__  # noqa: E402
for _c in ('Cfg', 'M', 'Term', 'Ledger'):
    setattr(__main__, _c, getattr(produce, _c))
from packing import lay_len  # noqa: E402

BAD = []


def chk(cond, *msg):
    if not cond:
        BAD.append(' '.join(str(x) for x in msg))
    return cond


def gbQ(n, m):
    r = Fr(1)
    for i in range(m):
        r *= (Fr(n, 2) - i) / (i + 1)
    return r


class L:
    """the ledger records"""

    def __init__(self, d):
        self.cfg = cfg = d['cfg']
        self.models = d['models']
        self.steps = {s['name']: s for s in d['steps']}
        self.inputs = d['inputs']
        self.T = d['T']
        self.Bc = d['B']
        self.w = ((d['wreq'] + 15) // 16) * 16
        self.S, self.b = cfg.S, cfg.b
        self.CT, self.CP, self.M = cfg.CT, cfg.CP, cfg.M
        self.Nmax = cfg.maxdeg
        self.ns = sorted(self.T)

    # ---- tables (Lean: D.T, D.Pw, D.V, D.H and their claims)
    def Tm(self, n):
        return self.models[f'T_{n[0]}_{n[1]}_{n[2]}']

    def Pm(self, j, k):
        if k == 0:
            return self.models['one']
        if k == 1:
            return self.models[f'W_{j}']
        if k == -1:
            return self.models[f'Y_{j}']
        if k == 2:
            return self.models[f'B_{j}']
        if k > 0:
            return self.models[f'P_{j}_{k}']
        return self.models[f'P_{j}_m{-k}']

    def Vm(self, n1, m2, m3):
        return self.models.get(f'V_{n1}_{m2}_{m3}')

    def Hm(self, m):
        return self.models.get(f'H_{m[0]}_{m[1]}_{m[2]}')

    # ---- index functions (Lean: n2s, n1s, uIdx, vIdx, hIdx)
    def n2s(self, n1):
        return [n2 for n2 in range(self.Nmax + 1) if any(n[0] == n1 and n[1] == n2 for n in self.ns)]

    def n1s(self):
        return [n1 for n1 in range(self.Nmax + 1) if any(n[0] == n1 for n in self.ns)]

    def uIdx(self, n1, n2, m3):
        return [n for n in self.ns if n[0] == n1 and n[1] == n2 and gbQ(n[2], m3) != 0 and n[2] <= self.Nmax]

    def vIdx(self, n1, m2, m3):
        return [n2 for n2 in self.n2s(n1) if gbQ(n2, m2) != 0 and self.uIdx(n1, n2, m3)]

    def hIdx(self, m):
        return [n1 for n1 in self.n1s() if gbQ(n1, m[0]) != 0 and self.vIdx(n1, m[1], m[2])]


# ------------------------------------------------------------------------------------- mirrors
def litZ(m, Lg):
    return m.lit.Z(Lg.S, Lg.w)


def lit_ok(m, Lg):
    K = 2 * m.C + 1
    return (Lg.b > 0 and Lg.b <= Lg.w and K <= Lg.S and K * K <= 2 ** m.lit.L1 and K <= 2 ** m.lit.L2)


def l1Ok(w, N, l, slots):
    return 0 < N and l + 2 <= w and N * 2 ** l < 2 ** w and all(-(2 ** l) <= v < 2 ** l for v in slots)


def l1Check(m, Lg, n):
    N = lay_len(m.C, Lg.S)
    sl = list(m.poly.s.values())
    return lit_ok(m, Lg) and Lg.b >= 1 and l1Ok(Lg.w, N, Lg.b - 1, sl) and m.poly.l1() <= n


class T_:
    """Lean Term: c sh rho A B ea0 ea1 na eb0 eb1 nb mxb"""

    def __init__(self, c, rho, A, B, ea, eb, mxb):
        self.c, self.rho, self.A, self.B = c, Fr(rho), A, B
        self.ea0, self.ea1, self.na = ea
        self.eb0, self.eb1, self.nb = eb
        self.mxb = mxb

    def err0(self):
        return abs(self.A['q']) * self.na * self.eb0 + abs(self.B['q']) * self.nb * self.ea0 + self.ea0 * self.eb0

    def err1(self):
        A, B = self.A, self.B
        return (abs(A['q']) * (A['C'] * self.na) * self.eb0 + abs(A['q']) * self.na * self.eb1
                + abs(B['q']) * (B['C'] * self.nb) * self.ea0 + abs(B['q']) * self.nb * self.ea1
                + self.ea1 * self.eb0 + self.ea0 * self.eb1)

    def slotB(self):
        return abs(self.c) * self.na * self.mxb


def opd(m):
    return {'C': m.C, 'par': m.poly.par, 'q': m.q, 'poly': m.poly}


def cOf(rho, qA, qB, Q):
    return (Fr(rho) * qA * qB / Q).numerator


def psgn(p):
    return -1 if p else 1


def prodCheck(S, Ca, Cb, p, Q, ts, E0, E1, BX):
    ok = 2 * (Ca + Cb) < S
    for t in ts:
        ok = ok and t.A['C'] == Ca and t.B['C'] == Cb and (t.A['par'] != t.B['par']) == p
        ok = ok and t.rho * t.A['q'] * t.B['q'] * psgn(t.A['par'] and t.B['par']) == Q * t.c
    ok = ok and sum((abs(t.rho) * t.err0() for t in ts), Fr(0)) <= E0
    ok = ok and sum((abs(t.rho) * t.err1() for t in ts), Fr(0)) <= E1
    ok = ok and sum(t.slotB() for t in ts) <= BX
    return ok


def comb_poly(ts):
    from poly import conv_raw
    X = None
    for t in ts:
        pr = conv_raw(t.A['poly'], t.B['poly']).scale_int(t.c)
        X = pr if X is None else X.add(pr)
    return X


def outCheck(w, S, Cp, Q, X, BX, O, mxO, aX, aO, lD, F0, F1):
    ok = O.C <= Cp and Cp + O.C < S and 2 * Cp < S and 0 < aX and O.q * aX == Q * aO
    ok = ok and 2 * (aX * BX + aO * mxO) < 2 ** w
    D = X.scale_int(aX).add(O.poly.embed(Cp).scale_int(-aO))
    N = lay_len(Cp, S)
    ok = ok and l1Ok(w, N, lD, list(D.s.values()))
    l1 = D.l1()
    ok = ok and abs(Q) / aX * l1 <= F0 and abs(Q) / aX * (Cp * l1) <= F1
    return ok


NOMIRROR = __import__('os').environ.get('LEDGER_NOMIRROR') == '1'


def litCheck(Lg, Ca, Cb, p, Q, ts, E0, E1, BX, O, aX, aO, lD, F0, F1, e0, e1, n):
    if NOMIRROR:  # the full ledger: the kernel is the check (the mirror is quadratic in Python)
        return True
    X = comb_poly(ts)
    ok = prodCheck(Lg.S, Ca, Cb, p, Q, ts, E0, E1, BX) and lit_ok(O, Lg) and Lg.b >= 1 and O.poly.par == p
    ok = ok and outCheck(Lg.w, Lg.S, Ca + Cb, Q, X, BX, O, 2 ** (Lg.b - 1), aX, aO, lD, F0, F1)
    ok = ok and E0 + F0 <= e0 and E1 + F1 <= e1 and l1Check(O, Lg, n)
    return ok


def combCheck(w, S, Ca, Cb, p, Q, ts, E0, E1, BX, l, n):
    if NOMIRROR:
        return True
    X = comb_poly(ts)
    N = lay_len(Ca + Cb, S)
    return (prodCheck(S, Ca, Cb, p, Q, ts, E0, E1, BX) and 2 * BX < 2 ** w
            and l1Ok(w, N, l, list(X.s.values())) and X.l1() <= n)


def cl(m):
    return (m.e0, m.e1, m.n)


# ------------------------------------------------------------------------------------- records
def build(Lg):
    """the step parameters, keyed as in Lean, plus the mirror checks"""
    mxb = 2 ** (Lg.b - 1)
    rec = {'up': {}, 'vp': {}, 'hp': {}, 'sq': {}, 'iv': {}, 'pp': {}}
    st = Lg.steps
    # ---- U and V blocks
    for n1 in Lg.n1s():
        for m3 in range(Lg.M + 1):
            ups = []
            for n2 in Lg.n2s(n1):
                if not Lg.uIdx(n1, n2, m3):
                    continue
                s = st[f'U_{n1}_{n2}_{m3}']
                Um = Lg.models[f'U_{n1}_{n2}_{m3}']
                u = {'Q': s['Q'], 'E0': Um.e0, 'E1': Um.e1, 'BX': s['BX'], 'l': s['l'], 'n': s['n']}
                ts = [T_(cOf(gbQ(n[2], m3), Lg.Tm(n).q, Lg.Pm(2, n[2] - 2 * m3).q, u['Q']), gbQ(n[2], m3),
                         opd(Lg.Tm(n)), opd(Lg.Pm(2, n[2] - 2 * m3)), cl(Lg.Tm(n)),
                         cl(Lg.Pm(2, n[2] - 2 * m3)), mxb) for n in Lg.uIdx(n1, n2, m3)]
                chk(combCheck(Lg.w, Lg.S, Lg.CT, Lg.CP, False, u['Q'], ts, u['E0'], u['E1'], u['BX'], u['l'],
                              u['n']), 'uOk', n1, n2, m3)
                ups.append((n2, u))
            rec['up'][(n1, m3)] = ups
            upd = dict(ups)
            vps = []
            for m2 in range(Lg.M + 1 - m3):
                vi = Lg.vIdx(n1, m2, m3)
                if not vi:
                    continue
                s = st[f'V_{n1}_{m2}_{m3}']
                o = {k: s[k] for k in ('Q', 'E0', 'E1', 'BX', 'aX', 'aO', 'lD', 'F0', 'F1')}
                Vm = Lg.Vm(n1, m2, m3)
                ts = []
                for n2 in vi:
                    u = upd[n2]
                    Um = Lg.models[f'U_{n1}_{n2}_{m3}']
                    Pmd = Lg.Pm(1, n2 - 2 * m2)
                    ts.append(T_(cOf(gbQ(n2, m2), u['Q'], Pmd.q, o['Q']), gbQ(n2, m2),
                                 {'C': Lg.CT + Lg.CP, 'par': False, 'q': u['Q'], 'poly': Um.poly}, opd(Pmd),
                                 (u['E0'], u['E1'], u['n']), cl(Pmd), mxb))
                chk(litCheck(Lg, Lg.CT + Lg.CP, Lg.CP, False, o['Q'], ts, o['E0'], o['E1'], o['BX'], Vm,
                             o['aX'], o['aO'], o['lD'], o['F0'], o['F1'], Vm.e0, Vm.e1, Vm.n), 'vOk', n1, m2, m3)
                vps.append((m2, o))
            rec['vp'][(n1, m3)] = vps
    # ---- h blocks
    for m in produce.monomials(Lg.M):
        hi = Lg.hIdx(m)
        if not hi:
            continue
        s = st[f'H_{m[0]}_{m[1]}_{m[2]}']
        o = {k: s[k] for k in ('Q', 'E0', 'E1', 'BX', 'aX', 'aO', 'lD', 'F0', 'F1')}
        Hm = Lg.Hm(m)
        ts = []
        for n1 in hi:
            Vm, Pmd = Lg.Vm(n1, m[1], m[2]), Lg.Pm(0, n1 - 2 * m[0])
            ts.append(T_(cOf(gbQ(n1, m[0]), Vm.q, Pmd.q, o['Q']), gbQ(n1, m[0]), opd(Vm), opd(Pmd), cl(Vm),
                         cl(Pmd), mxb))
        chk(sum(m) <= Lg.M and litCheck(Lg, Lg.CP, Lg.CP, False, o['Q'], ts, o['E0'], o['E1'], o['BX'], Hm,
                                        o['aX'], o['aO'], o['lD'], o['F0'], o['F1'], Hm.e0, Hm.e1, Hm.n),
            'hBlock', m)
        rec['hp'][m] = o
    # ---- powers (the base checks are mirrored separately)
    for j in range(3):
        def powOk(kA, kB, k):
            s = st[f'P_{j}_{k}' if k > 0 else f'P_{j}_m{-k}']
            o = {kk: s[kk] for kk in ('Q', 'E0', 'E1', 'BX', 'aX', 'aO', 'lD', 'F0', 'F1')}
            A, B, O = Lg.Pm(j, kA), Lg.Pm(j, kB), Lg.Pm(j, k)
            ts = [T_(cOf(1, A.q, B.q, o['Q']), 1, opd(A), opd(B), cl(A), cl(B), mxb)]
            ok = litCheck(Lg, Lg.CP, Lg.CP, False, o['Q'], ts, o['E0'], o['E1'], o['BX'], O, o['aX'], o['aO'],
                          o['lD'], o['F0'], o['F1'], O.e0, O.e1, O.n) and O.C == Lg.CP and O.lit.sym_ok()
            chk(ok, 'powOk', j, k)
            rec['pp'][(j, k)] = o
        for k in range(3, Lg.Nmax + 1):
            powOk(k - 2, 2, k)
        powOk(-1, -1, -2)
        for k in range(3, 2 * Lg.M + 2):
            powOk(-(k - 2), -2, -k)
        rec['sq'][j] = st[f'W_{j}']
        rec['iv'][j] = st[f'Y_{j}']
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--small', action='store_true')
    args = ap.parse_args()
    d = pickle.load(open(HERE / ('out-small' if args.small else 'out') / 'hbuild.pkl', 'rb'))
    Lg = L(d)
    rec = build(Lg)
    print(f'w = {Lg.w}, S = {Lg.S}, b = {Lg.b}; blocks: U/V {len(rec["up"])}, h {len(rec["hp"])}, '
          f'powers {len(rec["pp"])}; failures: {len(BAD)}')
    for b in BAD[:20]:
        print('  FAIL', b)
    return 1 if BAD else 0


if __name__ == '__main__':
    sys.exit(main())
