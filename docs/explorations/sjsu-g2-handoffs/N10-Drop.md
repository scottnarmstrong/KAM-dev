# N10-Drop handoff (T2-CONF): the DROP kernel check, and the `emit.py --small` manifest fix

Worker g2-n6, 6 November 2026. Status: **complete.**
- `dropCheck_sound` is proved in N7's target form and plugs into N9's `hDrop` verbatim.
- `emit.py --small` now hashes its own output. The production F regenerates byte-identical.
- No `sorry`, `axiom` or `set_option`; `Drop.lean` is 243 lines; the axioms are only `propext`,
  `Classical.choice` and `Quot.sound`.

## Files

| file | lines | content |
|---|---:|---|
| `KAM/EffectiveStability/Tube/Engine/Drop.lean` (new, core) | 243 | `dropT` (N7's text), `dropF`, `dropH`, `dropC`, `dropSum`, `dropCheck`; `dropT_eq`, `dropSum_eq`, `mdeg_mon_eq`, `dropT_nonneg`, `abs_val_le`, `abs_dropTerm_le`, **`dropCheck_sound`** |
| `scripts/sjsu/ledger/emit.py` | +20 | audit N7-N8-1 N1 fix (below) |

Scratch: `.drafts/g2/scratch/N10-Drop/`:
- `Check.lean`: axioms and the `hDrop` fit;
- `Smoke*.lean`: kernel smoke tests on the real `Ftab0`;
- `emit-prod/`, `emit-small/`: regenerated outputs;
- `emit.py.orig`.

## Main statements (namespace `KAM.EffectiveStability.Tube`)

```lean
def dropT (_Pb : Prm) (HL : ℕ×ℕ×ℕ → LitD) (nH : ℕ×ℕ×ℕ → ℕ) (r : ℚ) (L : ℕ) (b : BrT) : ℚ :=
  let d := b.i.1.1 + b.i.1.2.1 + b.i.1.2.2 + (b.e.1 + b.e.2.1 + b.e.2.2)
  if L + 2 ≤ d then |(b.coef muF monOf : ℚ)| * r ^ (d - 1) * (|(brSp b).q| * (brSp b).l1E) *
    (|(HL b.e).q| * (if b.kind then nH b.e else (HL b.e).C * nH b.e)) else 0

def dropCheck (Pb : Prm) (HL : ℕ×ℕ×ℕ → LitD) (nH : ℕ×ℕ×ℕ → ℕ) (r : ℚ) (L : ℕ)
    (Fl : List ((ℕ × ℕ × ℕ) × SpD)) (Hl : List (ℕ × ℕ × ℕ)) (D : ℚ) : Bool :=
  decide (0 ≤ r) && decide (dropSum Pb HL nH r L Fl Hl ≤ D)

theorem dropSum_eq … : dropSum Pb HL nH r L Fl Hl = ((bterms Fl Hl).map (dropT Pb HL nH r L)).sum

theorem dropCheck_sound {Pb : Prm} {HL : ℕ×ℕ×ℕ → LitD} {nH : ℕ×ℕ×ℕ → ℕ} {r : ℚ} {L : ℕ}
    {Fl : List ((ℕ × ℕ × ℕ) × SpD)} {Hl : List (ℕ × ℕ × ℕ)} {D : ℚ}
    (hchk : dropCheck Pb HL nH r L Fl Hl D = true) (_hb : 1 ≤ Pb.b)
    (hF : ∀ i ∈ Fl, i.2.ok Pb.S = true)
    (hH : ∀ t ∈ Hl, (HL t).ok Pb = true ∧ (HL t).l1Check Pb (nH t) = true) (w₀ : ℕ) {P0 : Prm}
    (hS0 : P0.S = Pb.S) (hb0 : P0.b = Pb.b) {u : Fin 3 → ℝ} (hu : ∀ l, |u l| ≤ (r : ℝ))
    (φ : Fin 2 → ℝ) :
    |((bterms Fl Hl).filter fun b => decide (L < mdeg (b.mon muF monOf))).map (fun b =>
      (b.coef muF monOf : ℝ) * umon (b.mon muF monOf) u *
      b.val (fun i => (i.2.opd w₀ Pb.S).eval Pb.S) (fun t => ((HL t).opd P0).eval P0.S) φ) |>.sum| ≤ D
```

`.drafts/g2/scratch/N10-Drop/Check.lean` contains `dropCheck_sound hchk hb hF hH w₀ hS0 hb0 hu φ`. It
typechecks as N9's `hDrop` with `μ := muF`, `ν := monOf`, `g := fun i => (i.2.opd w₀ Pb.S).eval Pb.S`,
`k := fun t => ((HL t).opd P0).eval P0.S`, `r := (r : ℝ)` and `D := (D : ℝ)`.

## Approach (N7's plan, as written)

- **Sum to terms.** `sum_map_filter_ite` turns the filtered sum into a sum over all of `bterms`, and
  `abs_list_sum_le` gives the termwise bound.
- **One term.**
  - If `coef = 0` the term is `0 ≤ dropT` (needs `0 ≤ r`).
  - Otherwise `mdeg mon = d − 1` (`mdeg_mon_eq`, from `one_le_of_coef_ne_zero`), so a dropped term has
    `L + 2 ≤ d`.
  - `|umon| ≤ r^{d−1}` (`abs_umon_le`).
  - `|val| ≤ (|q| l1E)_brSp · (|q_H| (nH or C·nH))` (`abs_val_le`):
    - for `kind`: `SpD.deriv_eval` and `Opd.abs_eval_le` with `SpD.l1_list_le`;
    - otherwise: `Opd.abs_pderiv_eval_le` with `LitD.wf`, `2C < S` from `LitD.ok`, and `LitD.l1_le`;
    - `k` is moved to the `Pb` form by `LitD.opd_eval_congr`.
- **Terms to `dropSum`.** `Σ_bterms dropT = dropSum` (`dropSum_eq`), cast from ℚ.

## Deviation (deliberate): `dropSum` is factored

`dropSum` is still nested sums in the order (axis, entry), never one flat list. But it factors each term
as `dropT = dropF · dropH · dropC` (`dropT_eq`):
- `dropF a i kind = (|q| Σ|m|)` of `brSp`, which depends only on the axis, the entry and the kind;
- `dropH e kind = |q_H| (nH or C nH)`;
- `dropC = [L + 2 ≤ d] |coef| r^{d−1}`.

It sums `Σ_a Σ_i Σ_kind dropF · Σ_e dropH · Σ_sh dropC`, the kind loop moved outside the `e` loop. The
equality with `Σ_bterms dropT` is proved (`dropSum_eq`: `sum_map_commQ`, `List.sum_map_mul_left`).

The reason is kernel cost. Recomputing the F-side factor per term costs about 55 ms: the `l1E` of
`brSp`, including the derivative model; the `u⁰` model alone has about 700 entries. Factored, each F
factor is computed once per (axis, entry, kind). Measured with a dummy literal `H` (`Smoke.lean`,
`Smoke3.lean`):

| test | unfactored | factored |
|---|---:|---:|
| 12 entries × 2 H-monomials (192 terms, L = 0) | 10.7 s | 5.0 s |
| full `Ftab0` (87 entries) × 10 H-monomials (L = 8) | — | 18.3 s |

The degree test alone is about 0.7 ms per term (133 ms for 192 terms). Estimate for the full check
(about 87–96 entries × the H list × 8 terms): about 15 s of F factors plus about 0.4–0.7 ms per term,
so roughly 1–2 minutes per observable. That is an estimate; N7's run is the measurement.

Two binder names in N7's target are prefixed with `_` to silence the unused-variable linter: `_Pb` in
`dropT` and `dropSum`, and `_hb` in `dropCheck_sound`. Positions and types are unchanged.

## (3) `emit.py --small` manifest (audit N7-N8-1 N1)

- **Defect.** The small run wrote its files under the small output directory but hashed the production
  paths, and wrote `manifest-F.json`.
- **Fix.**
  - `module_path(outdir, mod)` maps each emitted module to its file under the selected output directory.
  - A missing file aborts the run.
  - The manifest hashes exactly those files.
  - Small runs write `manifest-F-small.json`.
  - A new `--outdir` option writes the tree and its manifest elsewhere, for checks.
  - The production default (no flags) writes the same paths and `scripts/sjsu/ledger/manifest-F.json`
    as before.
- **Production check.**
  - `python3 emit.py F --outdir .drafts/g2/scratch/N10-Drop/emit-prod` prints
    `F: 277 models, 25349 entries, 11 parts` and `manifest: 12 modules` (5.4 s).
  - `diff -r` against `KAM/EffectiveStability/SJSU/Ledger/F` plus `cmp` of `F.lean`: byte-identical.
  - `cmp` of the regenerated manifest with `scripts/sjsu/ledger/manifest-F.json`: identical.
  - The tree was never overwritten.
- **Small check.**
  - `python3 emit.py F --small --outdir .drafts/g2/scratch/N10-Drop/emit-small` prints
    `F: 277 models, 21263 entries, 9 parts` and `manifest: 10 modules -> …/manifest-F-small.json`.
  - All 10 hashes match the small files and differ from production.
  - (Run into my scratch so that N7's `.drafts/g2/scratch/n7/ledger-small` work is not overwritten.)
- **Files touched.** Only `emit.py` among the tracked files (`git status`).

## Checks

- **Build.** `.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Engine.Drop` gives "Build completed
  successfully (2948 jobs)", with no warning in `Drop.lean` and no line over 100 columns.
- **Axioms** (`Check.lean`): `dropCheck_sound`, `dropSum_eq` and `mdeg_mon_eq` all show
  `[propext, Classical.choice, Quot.sound]`.
- **Kernel smoke tests on real data** (`Smoke.lean`, `Smoke3.lean`):
  - `dropCheck … (Ftab0.take 12) … 1 = true` and `… 0 = false`, both by `decide +kernel`; the check
    reduces and is nontrivial;
  - full `Ftab0` with 10 H-monomials, `L = 8`.
- **Lint.** See the section "Lint result".

## Design signal

`dropT_nonneg` first timed out at `whnf` with `unfold dropT; split_ifs` under the `let` of `dropT`. Fixed
by zeta-reducing first (`simp only [dropT]`) and closing each branch with explicit `mul_nonneg`. No
options were used.

## Uncertainties

- **Untested on N7's real H data.** The real H literals and `nH` are N7's; `dropCheck` was smoke-tested
  only with a dummy `H`. Its kernel cost on the full H list is an estimate.
- **`hb` is unused** by the proof (renamed `_hb`) but kept in the signature, as N7's target has it.

No suspected errata in pinned sources.

## Lint result

`.drafts/g2/lint_noabi.sh` (`abi_hashes` skipped, per the rule) exited 1, with no finding in `Drop.lean`
or `emit.py`.
- Overlong lines: 21, all in other workers' files.
- `KAM.lean is out of date` (`KAM/Root/EffectiveStability.lean`, `KAMSJSU/EffectiveStability.lean`): the
  roots are kam-g2's step; `Drop.lean` is core.
- Passed: `check_lean_modules: PASS (18599 Lean files)`, the unit tests `OK`,
  `FROZEN-ANCHOR GUARD OK`.

N7 (kam-sjsu-g2-4d) accepted the factored `dropSum` and is wiring `dropCheck` into `Ledger.Br.Main` with
its Python `D`.

READY g2-n10
