#!/usr/bin/env python3
"""Generate the candidate frozen texts of T2-CONF and of the SJSU18-O2 data definition (standard library only).

Model of record (D75): the published complex form of applications/sjsu/data/sjsu18-o2.json, each 25-digit
decimal read exactly; H(x) = Re sum_t c_t prod_j z_j^{a_j} conj(z_j)^{b_j}, z_j = (xi_j - i eta_j)/sqrt 2,
with the repository ordering q = eta = x.1, p = xi = x.2.

Output (one declaration per file, the frozen-anchor rule), into --out:
  SJSUTerm.lean            `sjsuTerm`, a typed row constructor (fast elaboration of long literal lists)
  SJSU18O2Part<k>.lean     `sjsu18O2Part<k>`, k = 0..5, the 7,941 rows in JSON order, one row per line
  SJSU18O2Terms.lean       `sjsu18O2Terms`, the concatenation
  SJSU18O2.lean            `sjsu18O2`, the Hamiltonian
  SecularConfinement.lean  `sjsu_secular_confinement`, the T2-CONF statement (body `sorry` only in drafts)
and a single scratch module `Check.lean` with all of them (statement as `example : stmt -> True`) for a
typecheck under `lake env lean`.  `--roundtrip` re-parses the rows from the generated files and checks them
byte-for-byte against the JSON.
Usage: python3 gen_t2conf.py --out <dir> [--roundtrip]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
DATA = ROOT / 'applications/sjsu/data/sjsu18-o2.json'
SHA = '702b0b3a3c7c713d48cc3044f90bd13795b79f255550275cc7937c5d8a067772'
NS = 'KAM.EffectiveStability'
NPART = 6
# statement constants (working defaults, kam-38 2026-11-06; owner approval pending)
R_Q = '1 / 10 ^ 6'
T_YR = '5 * 10 ^ 9'
E_LO = ['0.026', '0.009', '0.006']
E_HI = ['0.062', '0.085', '0.063']
NOMINAL = ROOT / 'applications/sjsu/validation/table2_map_poincare_order1.json'

HEADER = '''/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/'''


def raw_decimals(path, key):
    m = re.search(r'"%s"\s*:\s*\[([^\]]*)\]' % re.escape(key), path.read_text())
    return [x.strip() for x in m.group(1).split(',')]


def texts():
    raw = DATA.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == SHA, 'dataset hash'
    d = json.loads(raw)
    assert d['complex_form']['monomial_order'] == ['z_J', 'zbar_J', 'z_S', 'zbar_S', 'z_U', 'zbar_U']
    terms = d['complex_form']['terms']
    lam = d['parameters']['Lambda_star']
    nom = raw_decimals(NOMINAL, 'xi_eta_secular')  # xi_J xi_S xi_U eta_J eta_S eta_U
    out = {}
    out['sjsuTerm'] = f'''/-- A row of `SJSU18-O2` (complex form, D75): the exponents of
`z_J, conj z_J, z_S, conj z_S, z_U, conj z_U` and the coefficient, in the dataset's column order. -/
def sjsuTerm (aJ bJ aS bS aU bU : ℕ) (c : ℚ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℚ :=
  (aJ, bJ, aS, bS, aU, bU, c)'''
    size = -(-len(terms) // NPART)
    parts = []
    for k in range(NPART):
        rows = terms[k * size:(k + 1) * size]
        body = ',\n'.join(f"  sjsuTerm {' '.join(str(x) for x in t[:6])} ({t[6]})" for t in rows)
        name = f'sjsu18O2Part{k}'
        parts.append(name)
        out[name] = (f'''/-- Rows {k * size + 1}–{k * size + len(rows)} of the complex form of `SJSU18-O2`
(`applications/sjsu/data/sjsu18-o2.json`, sha256 `{SHA[:16]}…`, `complex_form.terms`, in file order). -/
def {name} : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℚ) := [
''' + body + '\n]')
    out['sjsu18O2Terms'] = ('''/-- The 7,941 rows of the complex form of `SJSU18-O2` (D75), in file order. -/
def sjsu18O2Terms : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℚ) :=
  ''' + ' ++ '.join(parts))
    out['sjsu18O2'] = '''/-- **`SJSU18-O2`** (D75): the planar secular Sun–Jupiter–Saturn–Uranus Hamiltonian of degree 18,
`H = Re Σ c zᵃ z̄ᵇ` over `sjsu18O2Terms`, with `z_j = (ξ_j - i η_j)/√2`, `η = x.1` (coordinates) and
`ξ = x.2` (momenta); units AU, year, `G = 1`. The sum is real; `Re` only fixes the type. -/
noncomputable def sjsu18O2 (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : ℝ :=
  let z : Fin 3 → ℂ := fun j => ((x.2 j : ℂ) - Complex.I * (x.1 j : ℂ)) / (Real.sqrt 2 : ℂ)
  ((sjsu18O2Terms.map fun t =>
      ((t.2.2.2.2.2.2 : ℚ) : ℂ) * z 0 ^ t.1 * star (z 0) ^ t.2.1 * z 1 ^ t.2.2.1 *
        star (z 1) ^ t.2.2.2.1 * z 2 ^ t.2.2.2.2.1 * star (z 2) ^ t.2.2.2.2.2.1).sum).re'''
    xi = ', '.join(nom[:3])
    eta = ', '.join(nom[3:])
    lams = ', '.join(lam)
    ecc = (f'Real.sqrt (1 - (1 - KAM.Planetary.oscillatorAction (z t).2 (z t).1 j / ![{lams}] j) ^ 2)')
    stmt = f'''theorem sjsu_secular_confinement (z₀ : (Fin 3 → ℝ) × (Fin 3 → ℝ))
    (hz₀ : ∀ j, |z₀.2 j - ![{xi}] j| ≤ {R_Q} ∧
      |z₀.1 j - ![{eta}] j| ≤ {R_Q}) :
    ∃ T₁ : ℝ, {T_YR} < T₁ ∧ ∃ z : ℝ → (Fin 3 → ℝ) × (Fin 3 → ℝ), z 0 = z₀ ∧
      (∀ t ∈ Set.Ioo (-T₁) T₁, HasDerivAt z (KAM.hamiltonianVectorField sjsu18O2 (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin 3 → ℝ) × (Fin 3 → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I → y 0 = z₀ →
        (∀ t ∈ I, HasDerivAt y (KAM.hamiltonianVectorField sjsu18O2 (y t)) t) →
        ∀ t ∈ I, t ∈ Set.Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ {T_YR} → ∀ j,
        ![{', '.join(E_LO)}] j ≤ {ecc} ∧
        {ecc} ≤ ![{', '.join(E_HI)}] j'''
    out['stmt'] = stmt
    out['doc'] = f'''/-- **SJSU secular confinement** (T2-CONF, D74/D75; `docs/explorations/sjs-rigor-plan.md` §1.1): for
every initial state within `10⁻⁶` (sup norm in `(ξ, η)`) of the nominal secular state (SLG13 Table 1 read
as Poincaré elements and mapped to secular variables, `applications/sjsu/validation/
table2_map_poincare_order1.json`), `SJSU18-O2` has a solution on `(-T₁, T₁)` with `T₁ > 5·10⁹` yr,
unique among solutions on intervals through `0`, along which for `|t| ≤ 5·10⁹` yr the eccentricities
`e_j = √(1 - (1 - Γ_j/Λ*_j)²)`, `Γ_j = (ξ_j² + η_j²)/2`, of Jupiter, Saturn and Uranus stay in
`[0.026, 0.062]`, `[0.009, 0.085]` and `[0.006, 0.063]`. -/'''
    return out, terms


def module(name_decl, body, imports, doc):
    return f'''{HEADER}
module

{imports}

/-!
{doc}
-/

@[expose] public noncomputable section

namespace {NS}

{body}

end {NS}

end
'''


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--roundtrip', action='store_true')
    args = ap.parse_args()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    tx, terms = texts()
    # scratch check module (not a repository module)
    chk = ['import Mathlib.Analysis.Complex.Basic', 'import Mathlib.Analysis.Calculus.Deriv.Basic',
           'import Mathlib.Order.Interval.Set.OrdConnected', 'import KAM.Frozen.Defs.HamiltonianVectorField',
           'import KAM.Frozen.Planetary.Defs.OscillatorAction', '', 'noncomputable section', '',
           f'namespace {NS}', '']
    for k in ['sjsuTerm'] + [f'sjsu18O2Part{k}' for k in range(NPART)] + ['sjsu18O2Terms', 'sjsu18O2']:
        chk += [tx[k], '']
    chk += ['/-- T2-CONF statement typecheck (no proof). -/',
            'example : (' + tx['stmt'].replace('theorem sjsu_secular_confinement ', '∀ ', 1)
            .replace(' :\n    ∃ T₁', ',\n    ∃ T₁', 1) + ') → True := fun _ => trivial', '',
            'theorem terms_length : sjsu18O2Terms.length = 7941 := by decide +kernel', '',
            f'end {NS}', '']
    (out / 'Check.lean').write_text('\n'.join(chk))
    for k, v in tx.items():
        (out / f'{k}.txt').write_text(v + '\n')
    if args.roundtrip:
        rows = []
        for k in range(NPART):
            for line in tx[f'sjsu18O2Part{k}'].splitlines():
                m = re.match(r'^  sjsuTerm (\d+) (\d+) (\d+) (\d+) (\d+) (\d+) \((\S+)\),?$', line)
                if m:
                    rows.append([int(m.group(i)) for i in range(1, 7)] + [m.group(7)])
        assert rows == terms, 'roundtrip mismatch'
        print(f'roundtrip OK: {len(rows)} rows byte-identical to complex_form.terms')
    print('written', sorted(p.name for p in out.iterdir()))


if __name__ == '__main__':
    main()
