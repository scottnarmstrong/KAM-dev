#!/usr/bin/env python3
"""N7 ledger emitter, H stage (T2-CONF): literals, inputs, tables, HData, kernel checks, assembly.

Reads the producer's plan (out*/hbuild.pkl), re-runs the kernel mirror (ledger.py; aborts on any
failure), then writes under KAM/EffectiveStability/SJSU/Ledger/<root>/ (root `H`, or `Small` for
--small with namespace KAM.EffectiveStability.SJSU.Small):
  Lit<i>.lean     literal models (whitened Nat.add/Nat.shiftLeft trees, <= 256 chunks per sub-def)
  Inputs.lean     sjsuNs, sjsuTdat (exact H_w data), sjsuBdat (exact B_j data)
  Tables.lean     the lookup tables of literals, claims and step parameters
  HData.lean      sjsuHD : HData
  Check<i>.lean   the kernel checks (decide +kernel), one declaration per block
  Main.lean       the assembly: TCerts, PCerts, VCerts, and the certificate of every h literal
and a manifest (sha256 per module).
Usage: python3 emit_h.py [--small]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pickle
import sys
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE))
import ledger  # noqa: E402
import produce  # noqa: E402
from emit import HEADER, MAXL, wrap_tokens  # noqa: E402

CH = 288
BLOCK = 256
MAXLINES = 1400


def chunks(n):
    out = []
    while n:
        out.append(n & ((1 << CH) - 1))
        n >>= CH
    return out or [0]


def tree(cs, lo, hi):
    if hi - lo == 1:
        return hex(cs[lo])
    mid = (lo + hi) // 2
    return f'(Nat.add {tree(cs, lo, mid)} (Nat.shiftLeft {tree(cs, mid, hi)} {CH * (mid - lo)}))'


def nat_tok(n: int) -> str:
    """a Nat literal or, if long, an inline chunk tree"""
    assert n >= 0
    h = hex(n)
    if len(h) <= 70:
        return h if n > 9 else str(n)
    cs = chunks(n)
    return tree(cs, 0, len(cs))


def int_tok(n: int) -> str:
    return f'(-{nat_tok(-n)} : Int)' if n < 0 else nat_tok(n)


def rat_tok(q) -> str:
    q = Fr(q)
    return f'(mkQ {"true" if q < 0 else "false"} {nat_tok(abs(q.numerator))} {nat_tok(q.denominator)})'


def toks(s):
    return s.replace('(', ' ( ').replace(')', ' ) ').replace('⟨', ' ⟨ ').replace('⟩', ' ⟩ ').replace(
        '[', ' [ ').replace(']', ' ] ').replace(',', ' , ').split()


def wrap_expr(head, expr, indent='  '):
    """wrap an expression on token boundaries (lines <= MAXL)"""
    out, cur = [], head
    tk = []
    for t in toks(expr):
        if t == '+kernel' and tk:
            tk[-1] += ' +kernel'   # never break `decide +kernel`
        else:
            tk.append(t)
    for t in tk:
        glue = '' if (cur.endswith('(') or cur.endswith('[') or cur.endswith('⟨') or t in (')', ']', '⟩', ',')
                      or t.startswith('.') or cur == '') else ' '
        if len(cur) + len(glue) + len(t) > MAXL:
            out.append(cur)
            cur = indent + t
        else:
            cur = cur + glue + t
    out.append(cur)
    return out


class Mod:
    def __init__(self, ns, root):
        self.ns, self.root = ns, root
        self.files = {}

    def write(self, name, imports, doc, body):
        mod = f'{self.root}.{name}'
        txt = HEADER + ''.join(f'public import {m}\n' for m in imports)
        txt += f'\n/-!\n{doc}\n-/\n\n@[expose] public section\n\nnamespace {self.ns}\n\n'
        txt += 'open KAM.EffectiveStability.Tube\n\n' + '\n'.join(body) + f'\n\nend {self.ns}\n\nend\n'
        path = ROOT / (mod.replace('.', '/') + '.lean')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(txt)
        nl = txt.count('\n')
        assert nl <= 1500, (mod, nl)
        assert all(len(x) <= MAXL for x in txt.split('\n')), mod
        self.files[mod] = hashlib.sha256(txt.encode()).hexdigest()
        return mod


def lname(m):
    return 'L_' + m.name


def lit_lines(m):
    X = m.lit.lit
    cs = chunks(X)
    nb = (len(cs) + BLOCK - 1) // BLOCK
    out, subs = [], []
    for bi in range(nb):
        part = cs[bi * BLOCK:(bi + 1) * BLOCK]
        sub = f'{lname(m)}_c{bi}'
        out += wrap_expr(f'def {sub} : Nat :=', tree(part, 0, len(part)))
        out.append('')
        subs.append(sub)

    def jt(lo, hi):
        if hi - lo == 1:
            return subs[lo]
        mid = (lo + hi) // 2
        return f'(Nat.add {jt(lo, mid)} (Nat.shiftLeft {jt(mid, hi)} {CH * BLOCK * (mid - lo)}))'
    out += wrap_expr(f'def {lname(m)}_lit : Nat :=', jt(0, nb))
    out.append('')
    L = m.lit
    out += wrap_expr(f'def {lname(m)} : LitD :=',
                     f'⟨{m.C}, {"true" if m.poly.par else "false"}, {rat_tok(m.q)}, {L.salt}, {L.nch}, '
                     f'{lname(m)}_lit, {L.L1}, {L.L2}⟩')
    out.append('')
    return out


def cl_tok(m):
    return f'⟨{rat_tok(m.e0)}, {rat_tok(m.e1)}, {nat_tok(m.n)}⟩'


def oprm_tok(o):
    return (f'⟨{rat_tok(o["Q"])}, {rat_tok(o["E0"])}, {rat_tok(o["E1"])}, {nat_tok(o["BX"])}, {nat_tok(o["aX"])}, '
            f'{nat_tok(o["aO"])}, {o["lD"]}, {rat_tok(o["F0"])}, {rat_tok(o["F1"])}⟩')


def uprm_tok(u):
    return (f'⟨{rat_tok(u["Q"])}, {rat_tok(u["E0"])}, {rat_tok(u["E1"])}, {nat_tok(u["BX"])}, {u["l"]}, '
            f'{nat_tok(u["n"])}⟩')


def sq_tok(s):
    return (f'⟨{rat_tok(s["Q"])}, {rat_tok(s["E0"])}, {rat_tok(s["E1"])}, {nat_tok(s["BX"])}, {nat_tok(s["aX"])}, '
            f'{nat_tok(s["aO"])}, {s["lD"]}, {rat_tok(s["F0"])}, {rat_tok(s["F1"])}, {rat_tok(s["rho"])}, '
            f'{rat_tok(s["rhop"])}, {rat_tok(s["sigma0"])}, {rat_tok(s["w0"])}⟩')


def iv_tok(s):
    return (f'⟨{rat_tok(s["Q"])}, {rat_tok(s["E0"])}, {rat_tok(s["E1"])}, {nat_tok(s["BX"])}, {nat_tok(s["aX"])}, '
            f'{nat_tok(s["aO"])}, {s["lD"]}, {rat_tok(s["F0"])}, {rat_tok(s["F1"])}, {rat_tok(s["qq"])}, '
            f'{rat_tok(s["qqp"])}⟩')


def list_def(name, ty, items, doc):
    """a list definition, items as strings, wrapped; long lists are split into chunk defs"""
    out = [f'/-- {doc} -/']
    if len(items) <= 40 and sum(len(x) for x in items) < 8000:
        out += wrap_expr(f'def {name} : {ty} :=', '[' + ', '.join(items) + ']')
        out.append('')
        return out
    # chunks of <= 40 items and about <= 100 lines (blank-line separated, so modules can split)
    parts, cur, sz = [], [], 0
    for x in items:
        if cur and (len(cur) >= 40 or sz + len(x) > 9000):
            parts.append(cur)
            cur, sz = [], 0
        cur.append(x)
        sz += len(x)
    parts.append(cur)
    pn = []
    for i, p in enumerate(parts):
        out += wrap_expr(f'def {name}_{i} : {ty} :=', '[' + ', '.join(p) + ']')
        out.append('')
        pn.append(f'{name}_{i}')
    out += [f'/-- {doc} -/'] + wrap_expr(f'def {name} : {ty} :=', ' ++ '.join(pn))
    out.append('')
    return out


def tri(n):
    return f'({n[0]}, {n[1]}, {n[2]})'


def emit(Lg, rec, small):
    root = 'KAM.EffectiveStability.SJSU.Ledger.' + ('Small' if small else 'H')
    ns = 'KAM.EffectiveStability.SJSU' + ('.Small' if small else '')
    md = Mod(ns, root)
    types = 'KAM.EffectiveStability.Tube.Engine.Types'
    # ---- literals
    lits = [m for m in Lg.models.values() if m.kind == 'lit']
    lits.sort(key=lambda m: m.name)
    litmods, cur, cnt = [], [], 0
    for m in lits:
        ls = lit_lines(m)
        if cnt + len(ls) > MAXLINES and cur:
            litmods.append(md.write(f'Lit{len(litmods)}', [types], '# Ledger literals (generated)', cur))
            cur, cnt = [], 0
        cur += ls
        cnt += len(ls)
    if cur:
        litmods.append(md.write(f'Lit{len(litmods)}', [types], '# Ledger literals (generated)', cur))
    # facades over the literal modules (an import list stays below the line cap)
    litfac = [md.write(f'Lits{i}', litmods[k:k + 1000], '# Ledger literals, facade (generated)', [])
              for i, k in enumerate(range(0, len(litmods), 1000))]
    # ---- inputs: exact T_n (sparse, per-degree denominators) and B_j
    body = []
    dens = {}
    tsp = []
    for n in Lg.ns:
        ents = []
        for (c, r), v in sorted(Lg.T[n].items(), key=lambda x: (x[0][1], x[0][0])):
            i = c + (2 * Lg.CT + 1) * r
            ents.append(f'({i}, {rat_tok(v)})')
        tsp.append(f'({tri(n)}, [' + ', '.join(ents) + '])')
    body += list_def('sjsuTsp', 'List ((Nat × Nat × Nat) × List (Nat × Rat))', tsp,
                     'The exact `T_n` (sparse; box index `c + (2C_T+1) r`).')
    body += list_def('sjsuNs', 'List (Nat × Nat × Nat)', [tri(n) for n in Lg.ns], 'The groups `n`.')
    body += ['/-- The exact `T_n` as dense box lists. -/',
             'def sjsuTdat (n : Nat × Nat × Nat) : List Rat :=',
             f'  denseQ {(2 * Lg.CT + 1) ** 2} ((sjsuTsp.lookup n).getD [])', '']
    for j in range(3):
        ents = [f'({c + (2 * Lg.CP + 1) * r}, {rat_tok(v)})'
                for (c, r), v in sorted(Lg.Bc[j].items(), key=lambda x: (x[0][1], x[0][0]))]
        body += list_def(f'sjsuBsp{j}', 'List (Nat × Rat)', ents, f'The exact `B_{j}` (sparse).')
    body += ['/-- The exact `B_j` as dense box lists. -/', 'def sjsuBdat (j : Nat) : List Rat :=',
             f'  denseQ {(2 * Lg.CP + 1) ** 2} (if j = 0 then sjsuBsp0 else if j = 1 then sjsuBsp1 else sjsuBsp2)', '']
    # inputs may exceed 1500 lines: split by writing chunk defs into parts
    inmods = []
    part, cnt = [], 0
    for line in body:
        part.append(line)
        cnt += 1
        if cnt > 900 and line == '':
            inmods.append(md.write(f'Inputs{len(inmods)}', [types] + inmods[-1:], '# Ledger inputs (generated)', part))
            part, cnt = [], 0
    inmods.append(md.write(f'Inputs{len(inmods)}', [types] + inmods[-1:], '# Ledger inputs (generated)', part))
    # ---- tables
    tb = []
    tb += list_def('sjsuTlist', 'List ((Nat × Nat × Nat) × LitD)',
                   [f'({tri(n)}, {lname(Lg.Tm(n))})' for n in Lg.ns], 'The `T_n` literals.')
    tb += list_def('sjsuTclist', 'List ((Nat × Nat × Nat) × Cl)',
                   [f'({tri(n)}, {cl_tok(Lg.Tm(n))})' for n in Lg.ns], 'The `T_n` claims.')
    pk = [(j, k) for j in range(3) for k in range(-(2 * Lg.M + 1), Lg.Nmax + 1)]
    tb += list_def('sjsuPwlist', 'List ((Nat × Int) × LitD)',
                   [f'(({j}, {int_tok(k)}), {lname(Lg.Pm(j, k))})' for j, k in pk], 'The power literals.')
    tb += list_def('sjsuPclist', 'List ((Nat × Int) × Cl)',
                   [f'(({j}, {int_tok(k)}), {cl_tok(Lg.Pm(j, k))})' for j, k in pk], 'The power claims.')
    vkeys = sorted(tuple(int(x) for x in nm.split('_')[1:]) for nm in Lg.models if nm.startswith('V_'))
    tb += list_def('sjsuVlist', 'List ((Nat × Nat × Nat) × LitD)',
                   [f'({tri(k)}, {lname(Lg.Vm(*k))})' for k in vkeys], 'The `V` literals.')
    tb += list_def('sjsuVclist', 'List ((Nat × Nat × Nat) × Cl)',
                   [f'({tri(k)}, {cl_tok(Lg.Vm(*k))})' for k in vkeys], 'The `V` claims.')
    hkeys = sorted(tuple(int(x) for x in nm.split('_')[1:]) for nm in Lg.models if nm.startswith('H_'))
    tb += list_def('sjsuHlist', 'List ((Nat × Nat × Nat) × LitD)',
                   [f'({tri(k)}, {lname(Lg.Hm(k))})' for k in hkeys], 'The `h` literals.')
    tb += list_def('sjsuHclist', 'List ((Nat × Nat × Nat) × Cl)',
                   [f'({tri(k)}, {cl_tok(Lg.Hm(k))})' for k in hkeys], 'The `h` claims.')
    tb += list_def('sjsuUP', 'List ((Nat × Nat) × List (Nat × UPrm))',
                   [f'(({a}, {b}), [' + ', '.join(f'({n2}, {uprm_tok(u)})' for n2, u in v) + '])'
                    for (a, b), v in sorted(rec['up'].items())], 'The `U` parameters.')
    tb += list_def('sjsuVP', 'List ((Nat × Nat) × List (Nat × OPrm))',
                   [f'(({a}, {b}), [' + ', '.join(f'({m2}, {oprm_tok(o)})' for m2, o in v) + '])'
                    for (a, b), v in sorted(rec['vp'].items())], 'The `V` parameters.')
    tb += list_def('sjsuHP', 'List ((Nat × Nat × Nat) × OPrm)',
                   [f'({tri(m)}, {oprm_tok(o)})' for m, o in sorted(rec['hp'].items())], 'The `h` parameters.')
    tb += list_def('sjsuSQ', 'List (Nat × SqPrm)', [f'({j}, {sq_tok(rec["sq"][j])})' for j in range(3)],
                   'The square-root witness parameters.')
    tb += list_def('sjsuIV', 'List (Nat × IvPrm)', [f'({j}, {iv_tok(rec["iv"][j])})' for j in range(3)],
                   'The inverse-square-root witness parameters.')
    tb += list_def('sjsuPP', 'List ((Nat × Int) × OPrm)',
                   [f'(({j}, {int_tok(k)}), {oprm_tok(o)})' for (j, k), o in sorted(rec['pp'].items())],
                   'The power-step parameters.')
    tbmods = []
    part, cnt = [], 0
    for line in tb:
        part.append(line)
        cnt += 1
        if cnt > 900 and line == '':
            tbmods.append(md.write(f'Tables{len(tbmods)}', [types] + litfac + tbmods[-1:], '# Ledger tables (generated)', part))
            part, cnt = [], 0
    tbmods.append(md.write(f'Tables{len(tbmods)}', [types] + litfac + tbmods[-1:], '# Ledger tables (generated)', part))
    # ---- HData
    hd = [
        '/-- The Horner-stage ledger of `SJSU18-O2`. -/', 'def sjsuHD : HData where',
        f'  P := ⟨{Lg.w}, {Lg.S}, {Lg.b}⟩', f'  CT := {Lg.CT}', f'  CP := {Lg.CP}', f'  M := {Lg.M}',
        f'  Nmax := {Lg.Nmax}', '  ns := sjsuNs',
        '  T := fun n => (sjsuTlist.lookup n).getD LitD.dflt',
        '  Tc := fun n => (sjsuTclist.lookup n).getD Cl.dflt',
        '  Pw := fun j k => (sjsuPwlist.lookup (j, k)).getD LitD.dflt',
        '  Pc := fun j k => (sjsuPclist.lookup (j, k)).getD Cl.dflt',
        '  V := fun k => (sjsuVlist.lookup k).getD LitD.dflt',
        '  Vc := fun k => (sjsuVclist.lookup k).getD Cl.dflt',
        '  H := fun k => (sjsuHlist.lookup k).getD LitD.dflt',
        '  Hc := fun k => (sjsuHclist.lookup k).getD Cl.dflt',
        '  Tdat := sjsuTdat', '  Bdat := sjsuBdat', '',
        '/-- The `U` parameters of a block. -/',
        'def sjsuUp (n1 m3 : Nat) : List (Nat × UPrm) := (sjsuUP.lookup (n1, m3)).getD []', '',
        '/-- The `V` parameters of a block. -/',
        'def sjsuVp (n1 m3 : Nat) : List (Nat × OPrm) := (sjsuVP.lookup (n1, m3)).getD []', '',
        '/-- The `h` parameters. -/', 'def sjsuHp (m : Nat × Nat × Nat) : OPrm := (sjsuHP.lookup m).getD OPrm.dflt', '',
        '/-- The witness and power parameters. -/',
        'def sjsuSq (j : Nat) : SqPrm := (sjsuSQ.lookup j).getD SqPrm.dflt', '',
        'def sjsuIv (j : Nat) : IvPrm := (sjsuIV.lookup j).getD IvPrm.dflt', '',
        'def sjsuPp (j : Nat) (k : Int) : OPrm := (sjsuPP.lookup (j, k)).getD OPrm.dflt', '']
    hdmod = md.write('HData', ['KAM.EffectiveStability.Tube.Engine.Powers'] + inmods[-1:] + tbmods[-1:],
                     '# The Horner-stage ledger as `HData` (generated)', hd)
    # ---- checks: atomic declarations (the kernel keeps every intermediate of a declaration, so a
    # declaration holds one step), packed into modules by estimated cost (<= 4 heavy steps per module)
    decl = []   # (name, statement, cost)
    ns = list(Lg.ns)
    tin_chunks = [ns[i:i + 2] for i in range(0, len(ns), 2)]
    for k, ch in enumerate(tin_chunks):
        decl.append((f'tin_{k}', '([' + ', '.join(tri(n) for n in ch) + '] : List (Nat × Nat × Nat)).all sjsuHD.tIn = true', 3))
    for j in range(3):
        decl.append((f'pb_{j}', f'sjsuHD.pBase {j} (sjsuSq {j}) (sjsuIv {j}) = true', 9))
        for k in range(3, Lg.Nmax + 1):
            decl.append((f'pw_{j}_{k}', f'(fun k : Nat => decide (k < 3) || sjsuHD.powOk {j} ((k : Int) - 2) 2 k '
                         f'(sjsuPp {j} k)) {k} = true', 1))
        decl.append((f'pm_{j}', f'sjsuHD.powOk {j} (-1) (-1) (-2) (sjsuPp {j} (-2)) = true', 1))
        for k in range(3, 2 * Lg.M + 2):
            decl.append((f'pn_{j}_{k}', f'(fun k : Nat => decide (k < 3) || sjsuHD.powOk {j} (-((k : Int) - 2)) (-2) '
                         f'(-(k : Int)) (sjsuPp {j} (-(k : Int)))) {k} = true', 1))
    n1s = Lg.n1s()
    for n1 in n1s:
        for m3 in range(Lg.M + 1):
            for n2 in Lg.n2s(n1):
                decl.append((f'vu_{n1}_{m3}_{n2}',
                             f'(fun n2 : Nat => (sjsuHD.uIdx {n1} n2 {m3}).isEmpty || sjsuHD.uOk {n1} n2 {m3} '
                             f'(uPrmOf (sjsuUp {n1} {m3}) n2)) {n2} = true', 1 if Lg.uIdx(n1, n2, m3) else 0))
            for m2 in range(Lg.M + 1 - m3):
                decl.append((f'vv_{n1}_{m3}_{m2}',
                             f'(fun m2 : Nat => (sjsuHD.vIdx {n1} m2 {m3}).isEmpty || sjsuHD.vOk {n1} m2 {m3} '
                             f'(sjsuUp {n1} {m3}) (((sjsuVp {n1} {m3}).lookup m2).getD ⟨1, 0, 0, 0, 1, 1, 0, 0, 0⟩)) '
                             f'{m2} = true', 2 if Lg.vIdx(n1, m2, m3) else 0))
    mons = produce.monomials(Lg.M)
    for m in mons:
        decl.append((f'hb_{m[0]}_{m[1]}_{m[2]}',
                     f'((sjsuHD.hIdx {tri(m)}).isEmpty || sjsuHD.hBlock {tri(m)} (sjsuHp {tri(m)})) = true',
                     2 if Lg.hIdx(m) else 0))
    chmods = []
    cur, cost = [], 0
    def flush():
        lines = []
        for nm, stmt, _ in cur:
            lines += wrap_expr(f'theorem {nm} :', f'{stmt} := by')
            lines += ['  decide +kernel', '']
        chmods.append(md.write(f'Check{len(chmods)}', [hdmod], '# Ledger kernel checks (generated)', lines))
    for d in decl:
        if cur and (cost + d[2] > 8 or len(cur) >= 24):
            flush()
            cur, cost = [], 0
        cur.append(d)
        cost += d[2]
    if cur:
        flush()
    chfac = [md.write(f'Checks{i}', chmods[k:k + 1000], '# Ledger kernel checks, facade (generated)', [])
             for i, k in enumerate(range(0, len(chmods), 1000))]
    # the blocks from the atomic checks (no kernel work)
    pre = []
    pre += wrap_expr('theorem tin : sjsuHD.ns.all sjsuHD.tIn = true := by', '')
    pre = ['theorem tin : sjsuHD.ns.all sjsuHD.tIn = true := by']
    pre += wrap_expr('  rw [show sjsuHD.ns =', ' ++ '.join('[' + ', '.join(tri(n) for n in ch) + ']'
                                                        for ch in tin_chunks) + ' from by decide +kernel]', '    ')
    pre += wrap_expr('  simp only [List.all_append,', ', '.join(f'tin_{k}' for k in range(len(tin_chunks)))
                     + ', Bool.and_self]', '    ')
    pre += ['']

    def cases(var, hyp, items, names):
        """the proof of `f x = true` for `x ∈ [items]` from per-item theorems"""
        out = []
        if not items:
            out += [f'    simp at {hyp}']
            return out
        out += [f'    simp only [List.mem_cons, List.not_mem_nil, or_false] at {hyp}']
        out += wrap_expr(f'    rcases {hyp} with', ' | '.join('rfl' for _ in items), '      ')
        out += wrap_expr('    exacts [', ', '.join(names) + ']', '      ')
        return out
    for j in range(3):
        ks = list(range(Lg.Nmax + 1))
        kn = list(range(2 * Lg.M + 2))
        pre += [f'theorem pall{j} : sjsuHD.pAll {j} (sjsuSq {j}) (sjsuIv {j}) (sjsuPp {j}) = true := by',
                '  simp only [HData.pAll, Bool.and_eq_true]',
                f'  refine ⟨⟨⟨pb_{j}, ?_⟩, pm_{j}⟩, ?_⟩',
                '  · rw [List.all_eq_true]',
                '    intro k hk',
                f'    rw [show List.range (sjsuHD.Nmax + 1) = [{", ".join(map(str, ks))}] from by decide] at hk']
        pre += cases('k', 'hk', ks, ['rfl' if k < 3 else f'pw_{j}_{k}' for k in ks])
        pre += ['  · rw [List.all_eq_true]',
                '    intro k hk',
                f'    rw [show List.range (2 * sjsuHD.M + 2) = [{", ".join(map(str, kn))}] from by decide] at hk']
        pre += cases('k', 'hk', kn, ['rfl' if k < 3 else f'pn_{j}_{k}' for k in kn])
        pre += ['']
    for n1 in n1s:
        for m3 in range(Lg.M + 1):
            n2l = Lg.n2s(n1)
            m2l = list(range(Lg.M + 1 - m3))
            pre += [f'theorem vb_{n1}_{m3} : sjsuHD.vBlock {n1} {m3} (sjsuUp {n1} {m3}) (sjsuVp {n1} {m3}) = true := by',
                    '  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]',
                    '  refine ⟨⟨by decide, ?_⟩, ?_⟩',
                    '  · rw [List.all_eq_true]',
                    '    intro n2 hn2',
                    f'    rw [show sjsuHD.n2s {n1} = [{", ".join(map(str, n2l))}] from by decide +kernel] at hn2']
            pre += cases('n2', 'hn2', n2l, [f'vu_{n1}_{m3}_{n2}' for n2 in n2l])
            pre += ['  · rw [List.all_eq_true]',
                    '    intro m2 hm2',
                    f'    rw [show List.range (sjsuHD.M + 1 - {m3}) = [{", ".join(map(str, m2l))}] from by decide] at hm2']
            pre += cases('m2', 'hm2', m2l, [f'vv_{n1}_{m3}_{m2}' for m2 in m2l])
            pre += ['']
    pre2 = []
    for line in pre:
        if len(line) <= MAXL:
            pre2.append(line)
            continue
        ind = len(line) - len(line.lstrip())
        first, rest = line.strip().split(' ', 1)
        pre2 += wrap_expr(' ' * ind + first, rest, ' ' * (ind + 4))
    pre = pre2
    asmods, cur = [], []
    for line in pre:
        cur.append(line)
        if len(cur) > 1200 and line == '':
            asmods.append(md.write(f'Asm{len(asmods)}', chfac + asmods[-1:], '# Ledger blocks (generated)', cur))
            cur = []
    asmods.append(md.write(f'Asm{len(asmods)}', chfac + asmods[-1:], '# Ledger blocks (generated)', cur))
    # ---- assembly
    mon_list = '[' + ', '.join(tri(m) for m in mons) + ']'
    n1_list = '[' + ', '.join(str(x) for x in n1s) + ']'
    m3_list = '[' + ', '.join(str(x) for x in range(Lg.M + 1)) + ']'
    vb_names = ', '.join(f'vb_{n1}_{m3}' for n1 in n1s for m3 in range(Lg.M + 1))
    hb_names = ', '.join(f'hb_{m[0]}_{m[1]}_{m[2]}' for m in mons)
    asm = ['theorem sjsu_tcerts : sjsuHD.TCerts sjsuHD.Tt := sjsuHD.TCerts_of tin', '',
           'theorem sjsu_pcerts : sjsuHD.PCerts sjsuHD.Pt := sjsuHD.PCerts_of (s := sjsuSq) (i := sjsuIv)',
           '  (pp := sjsuPp) fun j hj => by',
           '    interval_cases j',
           '    · exact pall0', '    · exact pall1', '    · exact pall2', '',
           'theorem sjsu_n1s : sjsuHD.n1s =', '    ' + n1_list + ' := by decide +kernel', '',
           'theorem sjsu_range : List.range (sjsuHD.M + 1) = ' + m3_list + ' := by decide', '']
    asm += wrap_expr('theorem sjsu_allV :', '(sjsuHD.n1s.all fun n1 => (List.range (sjsuHD.M + 1)).all fun m3 => '
                     'sjsuHD.vBlock n1 m3 (sjsuUp n1 m3) (sjsuVp n1 m3)) = true := by')
    asm += ['  rw [sjsu_n1s, sjsu_range]']
    asm += wrap_expr('  simp only [List.all_cons, List.all_nil, Bool.and_true,', vb_names + ']', '    ')
    asm += ['', 'theorem sjsu_vcerts : sjsuHD.VCerts sjsuHD.Tt sjsuHD.Pt :=',
            '  sjsuHD.VCerts_of sjsuHD.Tt sjsuHD.Pt sjsu_allV sjsu_tcerts sjsu_pcerts', '',
            '/-- The monomials `|m| ≤ M`. -/']
    asm += wrap_expr('def sjsuMons : List (Nat × Nat × Nat) :=', mon_list)
    asm += ['']
    asm += wrap_expr('theorem sjsu_allH :', '(sjsuMons.all fun m => (sjsuHD.hIdx m).isEmpty || '
                     'sjsuHD.hBlock m (sjsuHp m)) = true := by')
    asm += wrap_expr('  simp only [sjsuMons, List.all_cons, List.all_nil, Bool.and_true,', hb_names + ']', '    ')
    asm += ['', '/-- Every `h` monomial of the ledger has a nonempty block. -/',
            'theorem sjsu_hIdx_ne : ∀ t ∈ sjsuMons, sjsuHD.hIdx t ≠ [] := by',
            '  have h : (sjsuMons.all fun m => !(sjsuHD.hIdx m).isEmpty) = true := by decide +kernel',
            '  intro t ht',
            '  have := List.all_eq_true.mp h t ht',
            '  simpa [List.isEmpty_iff] using this']
    asm += ['', '/-- **The certificates of all `h` literals** of the ledger. -/',
            'theorem sjsu_hcerts {m : Nat × Nat × Nat} (hm : m ∈ sjsuMons) (hne : sjsuHD.hIdx m ≠ []) :',
            '    ((sjsuHD.H m).opd sjsuHD.P).Cert sjsuHD.P.w sjsuHD.P.S (sjsuHD.Ht sjsuHD.Tt sjsuHD.Pt m)',
            '      (sjsuHD.Hc m).e₀ (sjsuHD.Hc m).e₁ (sjsuHD.Hc m).n :=',
            '  sjsuHD.HCert_of sjsuHD.Tt sjsuHD.Pt sjsu_allH sjsu_vcerts sjsu_pcerts hm hne']
    md.write('Main', asmods, '# The Horner-stage ledger: assembly (generated)', asm)
    (HERE / f'manifest-{"small" if small else "H"}.json').write_text(json.dumps(md.files, indent=1) + '\n')
    print(f'modules: {len(md.files)} (literals {len(litmods)}, checks {len(chmods)})')
    return md


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--small', action='store_true')
    args = ap.parse_args()
    d = pickle.load(open(HERE / ('out-small' if args.small else 'out') / 'hbuild.pkl', 'rb'))
    Lg = ledger.L(d)
    rec = ledger.build(Lg)
    if ledger.BAD:
        print('mirror failures:', ledger.BAD[:10])
        return 1
    emit(Lg, rec, args.small)
    return 0


if __name__ == '__main__':
    sys.exit(main())
