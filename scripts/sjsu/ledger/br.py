#!/usr/bin/env python3
"""N7 bracket ledger (T2-CONF): the kept coefficients G_{j,p} of {f_j, h~} (Engine/Bracket.lean).

Every G_{j,p} (|p| <= L) is bounded by exact sums over chunks of MCH consecutive terms of
Regroup.brList (Engine/BrChunk.lean; their cancellation is about 10 orders of magnitude, so each chunk
is one exact sum and only the chunk bounds are added; chunks of ~100 terms lose a factor 2-3).  The operands are literals:
certified copies FL of the sparse observable entries (digit width b), derivative literals dFL, dHL
(digit width bd = b + 6) and the h literals H_t of the H ledger.  For each (j, p): the scale Q (the
rational gcd of the coef q_A q_B), c = coef q_A q_B / Q, the slot bound BX = sum |c| len(A) mxA mxB
(as brTerm), the exact X = sum c conv(A, B) and the claim G = up(|Q| l1(X)) (dyadic, rounded up).
The packing width w satisfies 2 BX < 2^w and BX < 2^(w - 16) (load level w - 16).

Writes under KAM/EffectiveStability/SJSU/Ledger/Br (Ledger/Small/Br with --small, plus small F data):
  Lit<k>    the literal copies and derivative literals
  Prm       brPb, brPd, brPc, brPcd, the literal tables, brD j, brInH, sjsuG
  Cert<k>   the certificate checks (fCheck, dCheck, ok, symDigOk), in chunks
  P<k>      one kept-coefficient check per module (heavy: 10 GB lane, one thread)
  Main      the assembly: brD_ok j, br_all j, sjsu_G_bound
Usage: python3 br.py [--small] [--L 8] [--emit-only]
"""
from __future__ import annotations

import argparse
import json
import math
import pickle
import sys
import time
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE))
import fobs  # noqa: E402
import ledger  # noqa: E402
import produce  # noqa: E402,F401
from emit import spd_lines  # noqa: E402
from emit_h import Mod, tri, wrap_expr, list_def, lit_lines  # noqa: E402
from packing import Lit  # noqa: E402
from poly import Poly, mul  # noqa: E402

R0 = Fr(2, 10 ** 6)
WC = 96        # certification width
CHUNK = 8      # certificate chunk
MCH = int(__import__("os").environ.get("BR_MCH", "100"))  # terms per kept-coefficient chunk (about 7 GB at 100)


def mons_upto(L):
    """Engine/Bracket.monsUpTo, same order"""
    return [(a, b, c) for a in range(L + 1) for b in range(L + 1 - a) for c in range(L + 1 - a - b)]


def deriv(C, par, mant, a):
    """dlist / SpD.deriv: psgn par * kc (c - C, r - C) a * m"""
    sg = -1 if par else 1
    out = {}
    for (c, r), m in mant.items():
        k = (c - C) if a == 0 else (r - C)
        if k * m:
            out[(c, r)] = sg * k * m
    return out


def up_dyadic(x: Fr, bits=32):
    """(m, e) with m / 2^e >= x, about `bits` significant bits"""
    if x <= 0:
        return 0, 0
    e = max(bits - (x.numerator.bit_length() - x.denominator.bit_length()), 0)
    m = -(-(x.numerator << e) // x.denominator)
    return m, e


def lay_len(C, S):
    return 2 * C * S + 2 * C + 1


def terms(Fj, M, p):
    """Regroup.brList: (a, s, kind, sh, t, coef)"""
    out = []
    for a in (0, 1):
        for s in sorted(Fj):
            for kind in (False, True):
                for sh in (False, True):
                    ax = 2 if sh else a
                    d = [1 if ax == k else 0 for k in range(3)]
                    if not all(s[k] <= p[k] + d[k] for k in range(3)):
                        continue
                    t = tuple(p[k] + d[k] - s[k] for k in range(3))
                    if sum(t) > M:
                        continue
                    if not kind:
                        coef = s[a] if not sh else -s[2]
                    else:
                        coef = -t[a] if not sh else t[2]
                    if coef:
                        out.append((a, s, kind, sh, t, coef))
    return out


def compute(small, L):
    d = pickle.load(open(HERE / ('out-small' if small else 'out') / 'hbuild.pkl', 'rb'))
    Lg = ledger.L(d)
    Fs, cf = fobs.load(small)
    if small:
        # the small test: |s| <= L + 1, mantissas re-rounded to fit the small digit width
        sh = 80 - (Lg.b - 2)
        Fs = [{s: (q * (1 << sh), {k: (m + (1 << (sh - 1))) >> sh for k, m in mant.items()
                                   if (m + (1 << (sh - 1))) >> sh})
               for s, (q, mant) in Fj.items() if sum(s) <= L + 1} for Fj in Fs]
    M = Lg.M
    H = {}
    for t in mons_upto(M):
        m = Lg.Hm(t)
        assert m is not None, ('empty h model', t)
        assert m.poly.s == m.lit.mant and not m.poly.par, t
        H[t] = m
    Cb = H[(0, 0, 0)].C
    assert all(m.C == Cb for m in H.values())
    Ca, S, b = cf, Lg.S, Lg.b
    bd = b + 6
    assert 2 * (Ca + Cb) < S
    N = lay_len(Ca + Cb, S)
    assert N < 1 << 15
    dH = {(t, a): deriv(Cb, False, H[t].poly.s, a) for t in H for a in (0, 1)}
    dF = [{(s, a): deriv(Ca, False, Fj[s][1], a) for s in Fj for a in (0, 1)} for Fj in Fs]
    for D in [dH] + dF:
        assert all(abs(x) < 1 << (bd - 1) for v in D.values() for x in v.values())
    mxA = {False: 1 << (b - 1), True: 1 << (bd - 1)}
    mxB = {True: 1 << (b - 1), False: 1 << (bd - 1)}
    lenA = lay_len(Ca, S)
    G, Gc, NC, bxmax, t0, nt = {}, {}, {}, 0, time.time(), 0
    for j, Fj in enumerate(Fs):
        for p in mons_upto(L):
            ts = terms(Fj, M, p)
            chunks = [ts[i:i + MCH] for i in range(0, len(ts), MCH)]
            NC[(j, p)] = len(chunks)
            tot = Fr(0)
            for k, ch in enumerate(chunks):
                vals = [Fr(coef) * Fj[s][0] * H[t].q for (a, s, kind, sh, t, coef) in ch]
                Q = abs(vals[0])
                for v in vals[1:]:
                    Q = Fr(math.gcd(Q.numerator, abs(v.numerator)), math.lcm(Q.denominator, v.denominator))
                BX = 0
                grp = {}
                for (a, s, kind, sh, t, coef), v in zip(ch, vals):
                    c = v / Q
                    assert c.denominator == 1
                    c = c.numerator
                    BX += abs(c) * lenA * mxA[kind] * mxB[kind]
                    A = dF[j][(s, a)] if kind else Fj[s][1]
                    acc = grp.setdefault((t, kind, a if not kind else -1), {})
                    for kk, x in A.items():
                        acc[kk] = acc.get(kk, 0) + c * x
                X = {}
                for (t, kind, a), acc in grp.items():
                    B = Poly(Cb, False, H[t].poly.s) if kind else Poly(Cb, True, dH[(t, a)])
                    pr = mul(Poly(Ca, kind, acc), B)   # never both odd: the raw convolution
                    for kk, x in pr.s.items():
                        X[kk] = X.get(kk, 0) + x
                g = up_dyadic(Q * sum(abs(x) for x in X.values()))
                Gc[(j, p, k)] = g
                tot += Fr(g[0], 1 << g[1])
                bxmax = max(bxmax, BX)
            # the total, exactly (a sum of dyadics)
            e = max((Gc[(j, p, k)][1] for k in range(len(chunks))), default=0)
            G[(j, p)] = (int(tot * (1 << e)), e)
            assert Fr(G[(j, p)][0], 1 << e) == tot
            nt += len(ts)
        print(f'j={j}: terms {nt}, chunks {sum(v for (jj, _), v in NC.items() if jj == j)}, '
              f'BX < 2^{bxmax.bit_length()} ({time.time() - t0:.0f}s)', flush=True)
    w = ((bxmax.bit_length() + 17 + 15) // 16) * 16
    kept = [sum(R0 ** sum(p) * Fr(G[(j, p)][0], 1 << G[(j, p)][1]) for p in mons_upto(L)) for j in range(3)]
    print('KEPT = sum_p r^|p| G_p:', [float(x) for x in kept], 'w =', w, flush=True)
    nH = {t: sum(abs(x) for x in H[t].poly.s.values()) for t in H}
    Dr = drop(Fs, dF, H, nH, Cb, L)
    print('DROP:', [float(x) for x in Dr], flush=True)
    return dict(Fs=Fs, cf=cf, Ca=Ca, Cb=Cb, S=S, b=b, bd=bd, w=w, M=M, L=L, G=G, Gc=Gc, NC=NC, kept=kept, dF=dF,
                dH=dH, Hq={t: H[t].q for t in H}, nH=nH, D=[up_dyadic(x) for x in Dr])


def drop(Fs, dF, H, nH, Cb, L, r=R0):
    """Engine/Drop.dropSum, exactly: sum_a sum_i sum_kind dropF * sum_e dropH * sum_sh dropC"""
    out = []
    for j, Fj in enumerate(Fs):
        tot = Fr(0)
        for a in (0, 1):
            for s in sorted(Fj):
                q, mant = Fj[s]
                for kind in (False, True):
                    fF = abs(q) * sum(abs(x) for x in (dF[j][(s, a)] if kind else mant).values())
                    acc = Fr(0)
                    for t in mons_upto(max(sum(k) for k in H)):
                        if t not in H:
                            continue
                        fH = abs(H[t].q) * (nH[t] if kind else Cb * nH[t])
                        dd = sum(s) + sum(t)
                        if not L + 2 <= dd:
                            continue
                        c = Fr(0)
                        for sh in (False, True):
                            if not kind:
                                coef = s[a] if not sh else -s[2]
                            else:
                                coef = -t[a] if not sh else t[2]
                            c += abs(coef) * r ** (dd - 1)
                        acc += fH * c
                    tot += fF * acc
        out.append(tot)
    return out


class LM:
    """the shape lit_lines expects"""

    def __init__(self, name, C, par, q, mant, bits, salt):
        self.name, self.C, self.q = name, C, Fr(q)
        self.poly = Poly(C, par, mant)
        self.lit = Lit(C, par, q, mant, bits, salt)


def emit(R, small):
    root = 'KAM.EffectiveStability.SJSU.Ledger.' + ('Small.Br' if small else 'Br')
    ns = 'KAM.EffectiveStability.SJSU' + ('.Small' if small else '')
    md = Mod(ns, root)
    types = 'KAM.EffectiveStability.Tube.Engine.Types'
    hroot = 'KAM.EffectiveStability.SJSU.Ledger.' + ('Small' if small else 'H')
    L, M, b, bd, Ca, Cb = R['L'], R['M'], R['b'], R['bd'], R['Ca'], R['Cb']
    Fs = R['Fs']
    fimps = []
    if small:
        parts, cur, names = [], [], {}
        for j, Fj in enumerate(Fs):
            for s, (q, mant) in sorted(Fj.items()):
                nm = f'F_{j}_{s[0]}_{s[1]}_{s[2]}'
                names[(j, s)] = nm
                ls = spd_lines(nm, R['cf'], q, mant)
                if len(cur) + len(ls) > 1300 and cur:
                    parts.append(cur)
                    cur = []
                cur += ls
        parts.append(cur)
        pmods = [md.write(f'F{i}', ['KAM.EffectiveStability.Tube.Engine.Sparse'],
                          '# The small observables, part (generated by br.py --small)', ls)
                 for i, ls in enumerate(parts)]
        lines = ['/-- The packing parameters of the (small) observables. -/',
                 f'def Fprm : Prm := ⟨{R["w"]}, {R["S"]}, {b}⟩', '']
        for j, Fj in enumerate(Fs):
            lines += list_def(f'Ftab{j}', 'List ((ℕ × ℕ × ℕ) × SpD)',
                              [f'({tri(s)}, {names[(j, s)]})' for s in sorted(Fj)], f'The small `f_{j}`.')
        lines += ['/-- The small observables by index. -/', 'def Ftab (j : ℕ) : List ((ℕ × ℕ × ℕ) × SpD) :=',
                  '  if j = 0 then Ftab0 else if j = 1 then Ftab1 else if j = 2 then Ftab2 else []', '']
        fimps.append(md.write('F', pmods, '# The small observables (generated by br.py --small)', lines))
    else:
        fimps.append('KAM.EffectiveStability.SJSU.Ledger.F')
    # ---- literals
    salt = 900000
    lits = []
    for j, Fj in enumerate(Fs):
        for s, (q, mant) in sorted(Fj.items()):
            salt += 1
            lits.append(LM(f'FL_{j}_{s[0]}_{s[1]}_{s[2]}', R['cf'], False, q, mant, b, salt))
            for a in (0, 1):
                salt += 1
                lits.append(LM(f'dFL_{j}_{s[0]}_{s[1]}_{s[2]}_{a}', R['cf'], True, q, R['dF'][j][(s, a)], bd,
                               salt))
    for t in mons_upto(M):
        for a in (0, 1):
            salt += 1
            lits.append(LM(f'dHL_{t[0]}_{t[1]}_{t[2]}_{a}', Cb, True, R['Hq'][t], R['dH'][(t, a)], bd, salt))
    litmods, cur = [], []
    for m in lits:
        ls = lit_lines(m)
        if len(cur) + len(ls) > 1300 and cur:
            litmods.append(md.write(f'Lit{len(litmods)}', [types], '# Bracket literals (generated)', cur))
            cur = []
        cur += ls
    litmods.append(md.write(f'Lit{len(litmods)}', [types], '# Bracket literals (generated)', cur))
    litfac = [md.write(f'Lits{i}', litmods[k:k + 1000], '# Bracket literals, facade (generated)', [])
              for i, k in enumerate(range(0, len(litmods), 1000))]
    # ---- parameters and tables
    body = ['/-- The packing of the bracket products (plain literals). -/',
            f'def brPb : Prm := ⟨{R["w"]}, Fprm.S, sjsuHD.P.b⟩', '',
            '/-- The packing of the derivative literals. -/',
            f'def brPd : Prm := ⟨{R["w"]}, Fprm.S, {bd}⟩', '',
            '/-- The certification packing (plain). -/', f'def brPc : Prm := ⟨{WC}, Fprm.S, sjsuHD.P.b⟩', '',
            '/-- The certification packing (derivatives). -/', f'def brPcd : Prm := ⟨{WC}, Fprm.S, {bd}⟩', '']
    for j, Fj in enumerate(Fs):
        body += list_def(f'brFLtab{j}', 'List ((ℕ × ℕ × ℕ) × LitD)',
                         [f'({tri(s)}, L_FL_{j}_{s[0]}_{s[1]}_{s[2]})' for s in sorted(Fj)],
                         f'The literal copies of `f_{j}`.')
        body += list_def(f'brdFLtab{j}', 'List (((ℕ × ℕ × ℕ) × ℕ) × LitD)',
                         [f'(({tri(s)}, {a}), L_dFL_{j}_{s[0]}_{s[1]}_{s[2]}_{a})' for s in sorted(Fj)
                          for a in (0, 1)], f'The derivative literals of `f_{j}`.')
    body += list_def('brdHLtab', 'List (((ℕ × ℕ × ℕ) × ℕ) × LitD)',
                     [f'(({tri(t)}, {a}), L_dHL_{t[0]}_{t[1]}_{t[2]}_{a})' for t in mons_upto(M) for a in (0, 1)],
                     'The derivative literals of the `h` literals.')
    body += ['/-- The literal copies of `f_j` by index. -/',
             'def brFLt (j : ℕ) : List ((ℕ × ℕ × ℕ) × LitD) :=',
             '  if j = 0 then brFLtab0 else if j = 1 then brFLtab1 else brFLtab2', '',
             '/-- The derivative literals of `f_j` by index. -/',
             'def brdFLt (j : ℕ) : List (((ℕ × ℕ × ℕ) × ℕ) × LitD) :=',
             '  if j = 0 then brdFLtab0 else if j = 1 then brdFLtab1 else brdFLtab2', '',
             '/-- The literal data of the bracket of `f_j`. -/',
             'def brD (j : ℕ) : BrD where',
             '  Pb := brPb', '  Pd := brPd',
             '  FL := fun i => ((brFLt j).lookup i.1).getD LitD.dflt',
             '  dFL := fun i a => ((brdFLt j).lookup (i.1, a.val)).getD LitD.dflt',
             '  HL := sjsuHD.H',
             '  dHL := fun t a => (brdHLtab.lookup (t, a.val)).getD LitD.dflt', '',
             '/-- Membership in the `h` monomials `|t| ≤ M`. -/',
             f'def brInH (t : ℕ × ℕ × ℕ) : Bool := decide (t.1 + t.2.1 + t.2.2 ≤ {M})', '']
    body += list_def('brGtab', 'List ((ℕ × ℕ × ℕ × ℕ) × ℕ × ℕ)',
                     [f'(({j}, {p[0]}, {p[1]}, {p[2]}), {m}, {e})' for (j, p), (m, e) in sorted(R['G'].items())],
                     'The kept bracket coefficient bounds (dyadic `m / 2^e`).')
    body += list_def('brGctab', 'List ((ℕ × ℕ × ℕ × ℕ × ℕ) × ℕ × ℕ)',
                     [f'(({j}, {p[0]}, {p[1]}, {p[2]}, {k}), {m}, {e})' for (j, p, k), (m, e) in sorted(R['Gc'].items())],
                     'The chunk claims (dyadic `m / 2^e`).')
    body += list_def('brNtab', 'List ((ℕ × ℕ × ℕ × ℕ) × ℕ)',
                     [f'(({j}, {p[0]}, {p[1]}, {p[2]}), {n})' for (j, p), n in sorted(R['NC'].items())],
                     'The number of chunks of a kept coefficient.')
    body += ['/-- The claim of chunk `k` of `G_{j,p}`. -/',
             'def brGc (j : ℕ) (p : ℕ × ℕ × ℕ) (k : ℕ) : ℚ :=',
             '  match brGctab.lookup (j, p.1, p.2.1, p.2.2, k) with',
             '  | some me => (me.1 : ℚ) / 2 ^ me.2',
             '  | none => 0', '',
             '/-- The number of chunks of `G_{j,p}`. -/',
             'def brN (j : ℕ) (p : ℕ × ℕ × ℕ) : ℕ := (brNtab.lookup (j, p.1, p.2.1, p.2.2)).getD 0', '']
    body += ['/-- **The kept bracket coefficient bounds**: `sup_φ |G_{j,p}(φ)| ≤ sjsuG j p`. -/',
             'def sjsuG (j : ℕ) (p : ℕ × ℕ × ℕ) : ℚ :=',
             '  match brGtab.lookup (j, p.1, p.2.1, p.2.2) with',
             '  | some me => (me.1 : ℚ) / 2 ^ me.2',
             '  | none => 0', '']
    body += list_def('brNHtab', 'List ((ℕ × ℕ × ℕ) × ℕ)', [f'({tri(t)}, {R["nH"][t]})' for t in mons_upto(M)],
                     'The `ℓ¹` claims of the `h` literals (for the dropped terms).')
    body += ['/-- The `ℓ¹` claim of `H_t`. -/',
             'def brNH (t : ℕ × ℕ × ℕ) : ℕ := (brNHtab.lookup t).getD 0', '',
             '/-- **The bound of the dropped bracket terms** (`|mon| > 8`) of `f_j` on the box. -/',
             'def sjsuDrop (j : ℕ) : ℚ :=']
    dl = R['D']
    body += [f'  if j = 0 then ({dl[0][0]} : ℚ) / 2 ^ {dl[0][1]} else if j = 1 then ({dl[1][0]} : ℚ) / 2 ^ {dl[1][1]}',
             f'  else ({dl[2][0]} : ℚ) / 2 ^ {dl[2][1]}', '']
    prm = md.write('Prm', [f'{hroot}.HData', 'KAM.EffectiveStability.Tube.Engine.Bracket'] + fimps + litfac,
                   '# The bracket ledger: parameters and tables (generated by br.py)', body)
    # ---- certificates, in chunks
    cert = []
    for j, Fj in enumerate(Fs):
        for k in range(-(-len(Fj) // CHUNK)):
            cert += wrap_expr(f'theorem brc_f_{j}_{k} :',
                              f'((((Ftab {j}).drop ({CHUNK} * {k})).take {CHUNK}).all fun i => '
                              f'((brD {j}).FL i).ok brPb && fCheck brPc ((brD {j}).FL i) i.2) = true := by')
            cert += ['  decide +kernel', '']
            cert += wrap_expr(f'theorem brc_df_{j}_{k} :',
                              f'((((Ftab {j}).drop ({CHUNK} * {k})).take {CHUNK}).all fun i => '
                              f'([0, 1] : List (Fin 2)).all fun a => ((brD {j}).dFL i a).ok brPd && '
                              f'dCheck brPc brPcd ((brD {j}).FL i) ((brD {j}).dFL i a) a) = true := by')
            cert += ['  decide +kernel', '']
    nH = -(-len(mons_upto(M)) // CHUNK)
    for k in range(nH):
        cert += wrap_expr(f'theorem brc_h_{k} :',
                          f'(((sjsuMons.drop ({CHUNK} * {k})).take {CHUNK}).all fun t => (sjsuHD.H t).ok brPb && '
                          'symDigOk (sjsuHD.H t).par (sjsuHD.H t).C brPb.b (sjsuHD.H t).X) = true := by')
        cert += ['  decide +kernel', '']
        cert += wrap_expr(f'theorem brc_dh_{k} :',
                          f'(((sjsuMons.drop ({CHUNK} * {k})).take {CHUNK}).all fun t => '
                          '([0, 1] : List (Fin 2)).all fun a => ((brD 0).dHL t a).ok brPd && '
                          'dCheck brPc brPcd (sjsuHD.H t) ((brD 0).dHL t a) a) = true := by')
        cert += ['  decide +kernel', '']
    for k in range(nH):
        cert += wrap_expr(f'theorem brc_n_{k} :',
                          f'(((sjsuMons.drop ({CHUNK} * {k})).take {CHUNK}).all fun t => (sjsuHD.H t).ok brPb && '
                          '(sjsuHD.H t).l1Check brPb (brNH t)) = true := by')
        cert += ['  decide +kernel', '']
    for j in range(3):
        cert += [f'theorem brc_fok_{j} : ((Ftab {j}).all fun i => i.2.ok brPb.S) = true := by decide +kernel', '']
    certmods, cur = [], []
    for line in cert:
        cur.append(line)
        if len(cur) > 600 and line == '':
            certmods.append(md.write(f'Cert{len(certmods)}', [prm, f'{hroot}.Main'],
                                     '# Bracket certificates (generated)', cur))
            cur = []
    certmods.append(md.write(f'Cert{len(certmods)}', [prm, f'{hroot}.Main'],
                             '# Bracket certificates (generated)', cur))
    # ---- the kept coefficients: one module per check
    pmods = []
    for j in range(3):
        for p in mons_upto(L):
            for k in range(R['NC'][(j, p)]):
                ls = wrap_expr(f'theorem brp_{j}_{p[0]}_{p[1]}_{p[2]}_{k} :',
                               f'brCheckC (brD {j}) {Ca} {Cb} true (Ftab {j}) brInH {tri(p)} {MCH} {k} '
                               f'(brGc {j} {tri(p)} {k}) = true := by')
                ls += ['  decide +kernel']
                pmods.append(md.write(f'P{len(pmods)}', [prm, 'KAM.EffectiveStability.Tube.Engine.BrChunk'],
                                      '# A chunk of a kept bracket coefficient (generated)', ls))
    pfac = [md.write(f'Ps{i}', pmods[k:k + 1000], '# Kept coefficient chunks, facade (generated)', [])
            for i, k in enumerate(range(0, len(pmods), 1000))]
    # ---- assembly
    nF = [-(-len(Fj) // CHUNK) for Fj in Fs]
    asm = ['theorem brMons_nodup : sjsuMons.Nodup := by decide +kernel', '',
           'theorem brInH_iff (t : ℕ × ℕ × ℕ) : brInH t = true ↔ t ∈ sjsuMons := by',
           '  have h1 : (sjsuMons.all fun t => brInH t) = true := by decide +kernel',
           f'  have h2 : ((monsUpTo {M}).all fun t => sjsuMons.contains t) = true := by decide +kernel',
           '  constructor',
           '  · intro h',
           f'    have hm : t ∈ monsUpTo {M} := mem_monsUpTo.mpr (by simpa [brInH] using h)',
           '    simpa using List.all_eq_true.mp h2 t hm',
           '  · intro h',
           '    exact List.all_eq_true.mp h1 t h', '',
           f'theorem brH_len : sjsuMons.length ≤ {CHUNK} * {nH} := by decide', '',
           'theorem brH_ok : (sjsuMons.all fun t => (sjsuHD.H t).ok brPb &&',
           '    symDigOk (sjsuHD.H t).par (sjsuHD.H t).C brPb.b (sjsuHD.H t).X) = true := by',
           '  refine all_of_chunks _ _ brH_len fun k hk => ?_',
           '  interval_cases k']
    asm += wrap_expr('  exacts [', ', '.join(f'brc_h_{k}' for k in range(nH)) + ']', '    ')
    asm += ['', 'theorem brdH_ok : (sjsuMons.all fun t => ([0, 1] : List (Fin 2)).all fun a =>',
            '    ((brD 0).dHL t a).ok brPd && dCheck brPc brPcd (sjsuHD.H t) ((brD 0).dHL t a) a) = true := by',
            '  refine all_of_chunks _ _ brH_len fun k hk => ?_',
            '  interval_cases k']
    asm += wrap_expr('  exacts [', ', '.join(f'brc_dh_{k}' for k in range(nH)) + ']', '    ')
    asm += ['']
    for j in range(3):
        asm += [f'theorem brF_len_{j} : (Ftab {j}).length ≤ {CHUNK} * {nF[j]} := by decide', '',
                f'theorem brD_ok_{j} : (brD {j}).Ok (Ftab {j}) sjsuMons := by',
                '  refine BrD.ok_of (Pc := brPc) (Pcd := brPcd) rfl rfl rfl rfl (by decide) (by decide) rfl rfl',
                '    ?_ ?_ (List.all_eq_true.mp brH_ok) (List.all_eq_true.mp brdH_ok)',
                f'  · refine List.all_eq_true.mp (all_of_chunks _ _ brF_len_{j} fun k hk => ?_)',
                '    interval_cases k']
        asm += wrap_expr('    exacts [', ', '.join(f'brc_f_{j}_{k}' for k in range(nF[j])) + ']', '      ')
        asm += [f'  · refine List.all_eq_true.mp (all_of_chunks _ _ brF_len_{j} fun k hk => ?_)',
                '    interval_cases k']
        asm += wrap_expr('    exacts [', ', '.join(f'brc_df_{j}_{k}' for k in range(nF[j])) + ']', '      ')
        asm += ['']
    # one lemma per kept coefficient, in assembly modules (no kernel work but the cheap length/sum)
    pq = []
    for j in range(3):
        for p in mons_upto(L):
            n = R['NC'][(j, p)]
            pq += [f'theorem brq_{j}_{p[0]}_{p[1]}_{p[2]} : BrPOk (brD {j}) {Ca} {Cb} true (Ftab {j}) brInH {MCH}',
                   f'    (brN {j} {tri(p)}) (brGc {j} {tri(p)}) (sjsuG {j} {tri(p)}) {tri(p)} := by',
                   f'  have hn : brN {j} {tri(p)} = {n} := by decide +kernel',
                   '  refine ⟨by rw [hn]; decide +kernel, fun k hk => ?_, by rw [hn]; decide +kernel⟩',
                   '  rw [hn] at hk']
            if n == 0:
                pq += ['  omega', '']
            else:
                pq += ['  interval_cases k']
                pq += [f'  · exact brp_{j}_{p[0]}_{p[1]}_{p[2]}_{k}' for k in range(n)]
                pq += ['']
    qmods, cur = [], []
    for line in pq:
        cur.append(line)
        if len(cur) > 1200 and line == '':
            qmods.append(md.write(f'Q{len(qmods)}', pfac + qmods[-1:], '# Kept coefficients (generated)', cur))
            cur = []
    qmods.append(md.write(f'Q{len(qmods)}', pfac + qmods[-1:], '# Kept coefficients (generated)', cur))
    for j in range(3):
        names = ', '.join(f'brq_{j}_{p[0]}_{p[1]}_{p[2]}' for p in mons_upto(L))
        asm += [f'theorem br_all_{j} : ∀ t ∈ monsUpTo {L}, BrPOk (brD {j}) {Ca} {Cb} true (Ftab {j}) brInH {MCH}',
                f'    (brN {j} t) (brGc {j} t) (sjsuG {j} t) t := by']
        asm += wrap_expr(f'  rw [show monsUpTo {L} =',
                         '[' + ', '.join(tri(p) for p in mons_upto(L)) + '] from rfl]', '    ')
        asm += ['  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]']
        asm += wrap_expr('  exact ⟨', names + '⟩', '    ')
        asm += ['']
    asm += ['/-- **The kept bracket coefficients** of `{f_j, h~}` (N9\'s `hG`). -/',
            f'theorem sjsu_G_bound (j : Fin 3) : ∀ p ∈ truncSet (Fin 3) {L}, ∀ φ : Fin 2 → ℝ,',
            '    |((bterms (Ftab j) sjsuMons).filter fun b =>',
            '      decide (b.mon (fun e => monOf e.1) monOf = p)).map (fun b =>',
            '        (b.coef (fun e => monOf e.1) monOf : ℝ) *',
            '          b.val (fun e => (e.2.opd Fprm.w Fprm.S).eval Fprm.S)',
            '            (fun t => ((sjsuHD.H t).opd sjsuHD.P).eval sjsuHD.P.S) φ) |>.sum| ≤',
            '      ((sjsuG j (p 0, p 1, p 2) : ℚ) : ℝ) := by',
            '  intro p hp φ',
            f"  have hp' : mdeg p ≤ {L} := mem_truncSet_iff.mp hp",
            '  fin_cases j']
    for j in range(3):
        asm += [f'  · exact brAllC_sound (D := brD {j}) (P0 := sjsuHD.P) br_all_{j} brMons_nodup brInH_iff',
                f"      brD_ok_{j} Fprm.w rfl rfl p hp' φ"]
    # the dropped terms: one heavy module per observable
    dmods = []
    for j in range(3):
        ls = [f'theorem brdrop_{j} : dropCheck brPb sjsuHD.H brNH (2 / 1000000) {L} (Ftab {j}) sjsuMons',
              f'    (sjsuDrop {j}) = true := by',
              '  decide +kernel']
        dmods.append(md.write(f'Drop{j}', [prm, f'{hroot}.Main', 'KAM.EffectiveStability.Tube.Engine.Drop'],
                              '# The dropped bracket terms (generated)', ls))
    asm += ['', 'theorem brN_ok : (sjsuMons.all fun t => (sjsuHD.H t).ok brPb &&',
            '    (sjsuHD.H t).l1Check brPb (brNH t)) = true := by',
            '  refine all_of_chunks _ _ brH_len fun k hk => ?_',
            '  interval_cases k']
    asm += wrap_expr('  exacts [', ', '.join(f'brc_n_{k}' for k in range(nH)) + ']', '    ')
    asm += ['', '/-- **The dropped bracket terms** of `{f_j, h~}` (N9\'s `hDrop`, `L = 8`, `r = 2·10⁻⁶`). -/',
            'theorem sjsu_drop_bound (j : Fin 3) {u : Fin 3 → ℝ} (hu : ∀ l, |u l| ≤ ((2 / 1000000 : ℚ) : ℝ))',
            '    (φ : Fin 2 → ℝ) :',
            f'    |((bterms (Ftab j) sjsuMons).filter fun b => decide ({L} < mdeg (b.mon (fun e => monOf e.1)',
            '      monOf))).map (fun b => (b.coef (fun e => monOf e.1) monOf : ℝ) *',
            '        umon (b.mon (fun e => monOf e.1) monOf) u *',
            '          b.val (fun e => (e.2.opd Fprm.w Fprm.S).eval Fprm.S)',
            '            (fun t => ((sjsuHD.H t).opd sjsuHD.P).eval sjsuHD.P.S) φ) |>.sum| ≤',
            '      ((sjsuDrop j : ℚ) : ℝ) := by',
            '  have hH : ∀ t ∈ sjsuMons, (sjsuHD.H t).ok brPb = true ∧',
            '      (sjsuHD.H t).l1Check brPb (brNH t) = true := fun t ht => by',
            '    simpa only [Bool.and_eq_true] using List.all_eq_true.mp brN_ok t ht',
            '  fin_cases j']
    for j in range(3):
        asm += [f'  · exact dropCheck_sound brdrop_{j} (by decide) (List.all_eq_true.mp brc_fok_{j}) hH Fprm.w',
                '      (P0 := sjsuHD.P) rfl rfl hu φ']
    md.write('Main', certmods + qmods[-1:] + dmods + [f'{hroot}.Main', 'KAM.EffectiveStability.Tube.Check.BracketBound'],
             '# The bracket ledger: assembly (generated by br.py)', asm)
    (HERE / f'manifest-{"br-small" if small else "br"}.json').write_text(json.dumps(md.files, indent=1) + '\n')
    print(f'modules: {len(md.files)} (literals {len(litmods)}, certificates {len(certmods)}, '
          f'checks {len(pmods)}), w {R["w"]}')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--small', action='store_true')
    ap.add_argument('--L', type=int, default=8)
    ap.add_argument('--emit-only', action='store_true')
    args = ap.parse_args()
    out = HERE / ('out-small' if args.small else 'out')
    if args.emit_only:
        R = pickle.load(open(out / 'br.pkl', 'rb'))
    else:
        R = compute(args.small, args.L)
        with open(out / 'br.pkl', 'wb') as f:
            pickle.dump(R, f)
    emit(R, args.small)
    return 0


if __name__ == '__main__':
    sys.exit(main())
