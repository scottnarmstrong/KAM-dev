#!/usr/bin/env python3
"""N7 bracket mirror (T2-CONF): eta_j >= sup_tube |reducedBracket f_j h~| from the ledger's h models.

f_j = sum_s u^s F_s(phi) is the literal observable (F-v1.json even parts, pruned at
|a| (2e-6)^|s| < THR, rounded to p bits: the rounded, pruned literal IS the observable).  h~ is
replaced by its model sum_{|t| <= M} u^t H_t + errors; the model bracket is
  sum_a sum_{s,t} [s_a u^(s+t-e_a) - s_2 u^(s+t-e_2)] F_s d_a H_t - [t_a u^(s+t-e_a) - t_2 u^(s+t-e_2)] d_a F_s H_t,
its kept coefficients G_p (|p| <= Lb) computed exactly (l1 bounds the sup), the rest bounded by sup
norms (dropped degrees, skipped small products).  Model errors and N4 tails are added (tails: TODO).
Usage: python3 bracket.py [--small] [--thr 1e-21] [--skip 1e-29]
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

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE))
from poly import Poly, mul, hexn  # noqa: E402
import produce  # noqa: E402,F401  (pickle classes)
from produce import Cfg, M, monomials, scale_round  # noqa: E402,F401


def deriv(p: Poly, a):
    """d/dphi_a of q evalK p: the parity flips, slot k times psgn(par) k_a"""
    sg = -1 if p.par else 1
    s = {}
    for (c, r), v in p.s.items():
        ka = (c - p.C) if a == 0 else (r - p.C)
        if ka:
            s[(c, r)] = sg * ka * v
    return Poly(p.C, not p.par, s)


def load_F(cfg, thr, r0=Fr(2, 10 ** 6)):
    raw = json.loads((ROOT / '.drafts/g2/data/F-v1.json').read_text())
    out = []
    for j in range(3):
        Fj = {}
        nkeep = 0
        for ms, d in raw[str(j)].items():
            m = tuple(int(x) for x in ms.split(','))
            co = {}
            for ks, v in d.items():
                k = tuple(int(x) for x in ks.split(','))
                v = Fr(v)
                if abs(v) * r0 ** sum(m) < thr:
                    continue
                if max(abs(k[0]), abs(k[1])) > cfg.CF:
                    continue
                co[(k[0] + cfg.CF, k[1] + cfg.CF)] = v
            if co:
                Fj[m] = co
                nkeep += len(co)
        out.append((Fj, nkeep))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--small', action='store_true')
    ap.add_argument('--thr', type=float, default=1e-21)
    ap.add_argument('--skip', type=float, default=1e-29)
    ap.add_argument('--Lb', type=int, default=8)
    args = ap.parse_args()
    t0 = time.time()
    d = pickle.load(open(HERE / ('out-small' if args.small else 'out') / 'hbuild.pkl', 'rb'))
    cfg, models = d['cfg'], d['models']
    cfg.CF = 25 if not args.small else 8
    r = Fr(2, 10 ** 6)
    thr = Fr(args.thr)
    H = {}
    for name, m in models.items():
        if name.startswith('H_'):
            t = tuple(int(x) for x in name.split('_')[1:])
            H[t] = m
    Lb = args.Lb
    rep = {'thr': args.thr, 'skip': args.skip, 'rows': []}
    for j, (Fj, nkeep) in enumerate(load_F(cfg, thr)):
        # F literals: one scale per u-monomial (rounded to p bits relative to its largest mode)
        Fpoly, qFs = {}, {}
        for s, co in Fj.items():
            mant, q = scale_round(co, cfg.CF, cfg.p)
            Fpoly[s] = Poly(cfg.CF, False, mant)
            qFs[s] = q
        # sup norms
        supF = {s: qFs[s] * p.l1() for s, p in Fpoly.items()}
        supdF = {(s, a): qFs[s] * deriv(p, a).l1() for s, p in Fpoly.items() for a in range(2)}
        supH = {t: abs(h.q) * h.poly.l1() for t, h in H.items()}
        supdH = {(t, a): abs(h.q) * deriv(h.poly, a).l1() for t, h in H.items() for a in range(2)}
        # contributions
        G = defaultdict(list)  # p -> list of (coef rational, product key)
        dropped = Fr(0)
        skipped = Fr(0)
        nprod_keys = set()
        for a in range(2):
            ea = [0, 0, 0]
            ea[a] = 1
            for s in Fpoly:
                for t in H:
                    st = tuple(s[i] + t[i] for i in range(3))
                    for (kind, A, B, sup) in (('FdH', s, t, supF[s] * supdH[(t, a)]),
                                              ('dFH', s, t, supdF[(s, a)] * supH[t])):
                        for (e, coef) in ((ea, s[a] if kind == 'FdH' else -t[a]),
                                          ([0, 0, 1], -s[2] if kind == 'FdH' else t[2])):
                            if coef == 0:
                                continue
                            p = tuple(st[i] - e[i] for i in range(3))
                            if min(p) < 0:
                                continue
                            bnd = abs(coef) * sup * r ** sum(p)
                            if sum(p) > Lb:
                                dropped += bnd
                            elif bnd < Fr(args.skip):
                                skipped += bnd
                            else:
                                G[p].append((Fr(coef), (kind, a, s, t)))
                                nprod_keys.add((kind, a, s, t))
        # exact kept coefficients
        trunc = Fr(0)
        cache = {}
        for p, lst in G.items():
            # common integer combination
            items = []
            for coef, key in lst:
                kind, a, s, t = key
                q = coef * qFs[s] * H[t].q
                items.append((q, key))
            L = 1
            for q, _ in items:
                L = L * q.denominator // math.gcd(L, q.denominator)
            X = None
            for q, key in items:
                if key not in cache:
                    kind, a, s, t = key
                    if kind == 'FdH':
                        cache[key] = mul(Fpoly[s], deriv(H[t].poly, a))
                    else:
                        cache[key] = mul(deriv(Fpoly[s], a), H[t].poly)
                pr = cache[key].scale_int(int(q * L))
                X = pr if X is None else X.add(pr)
            trunc += r ** sum(p) * Fr(X.l1(), L)
        # model errors: sup|Df_a| * sum_t r^|t| e1_t + sup|d_a f| * sum_t (t_a + t_2) r^(|t|-1) e0_t
        errm = Fr(0)
        for a in range(2):
            supDf = sum((s[a] + s[2]) * r ** (sum(s) - 1) * supF[s] for s in Fpoly if s[a] + s[2] > 0)
            supdf = sum(r ** sum(s) * supdF[(s, a)] for s in Fpoly)
            e1 = sum(r ** sum(t) * h.e1 for t, h in H.items())
            e0 = sum((t[a] + t[2]) * r ** (sum(t) - 1) * h.e0 for t, h in H.items() if t[a] + t[2] > 0)
            errm += supDf * e1 + supdf * e0
        eta = trunc + dropped + skipped + errm
        row = {'j': j, 'F_coeffs': nkeep, 'kept_p': len(G), 'products': len(cache), 'trunc': float(trunc),
               'dropped': float(dropped), 'skipped': float(skipped), 'model_err': float(errm),
               'eta_wo_tails': float(eta), 'T_years': float(Fr(1, 2 * 10 ** 6) / eta),
               'seconds': time.time() - t0}
        rep['rows'].append(row)
        print(row, flush=True)
    (HERE / ('out-small' if args.small else 'out') / 'bracket.json').write_text(json.dumps(rep, indent=1) + '\n')


if __name__ == '__main__':
    sys.exit(main())
