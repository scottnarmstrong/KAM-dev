# N8-Obs handoff (T2-CONF): the literal observables and their bounds

Worker g2-n6 (session kam-sjsu-g2-70), 6 November 2026. Status: **complete.** Every N7-side obligation of
`sjsu_secular_confinement_of_obs` except the rates (`hη`, `hTη`) is proved for the literal observables over
N7's landed data. g2-n5b confirmed that the names plug into its staged proof unchanged. There is no
`sorry`, `axiom` or `set_option`, every file is ≤ 1500 lines, and the axioms are only `propext`,
`Classical.choice` and `Quot.sound`.

## Interface (agreed with N7 kam-sjsu-g2-4d and N5b kam-sjsu-g2-69)

- **Split.** Generic lemmas go in `KAM/EffectiveStability/Tube/Obs/` (core). The instance goes in
  `KAM/EffectiveStability/SJSU/Obs/` (KAMSJSU).
- **Data.** N7's `KAM.EffectiveStability.SJSU.Ledger.F` provides `Fprm : Prm` and `Ftab (j : ℕ)`, each
  a `List ((ℕ × ℕ × ℕ) × SpD)` of sparse literals (C = 25, even parity; 277 models, 25,349 entries). There
  is no separate claim list: the bounds are computed from the entries (`SpD.eval_eq`).
- **The definition (adopted as agreed):**
  `fObs j p = ((Ftab j).map fun e => umon (monOf e.1) p.1 * (e.2.opd Fprm.w Fprm.S).eval Fprm.S p.2).sum`,
  `sjsuObs j := fObs j`. Here `monOf (s₀, s₁, s₂) = ![s₀, s₁, s₂]`, because `umon` takes `Fin 3 → ℕ`.
- **For N7's bracket.** The joint partial formulas are generic over any list (`fderiv_listObs_u/φ`), and
  `fObs_eq_litObs`, `litObs_eq_listObs` are `rfl`.

## Files

| file | lines | content |
|---|---:|---|
| `Tube/Obs/ListObs.lean` (core) | 168 | `monOf`, `listObs`; `hasFDerivAt_listObs`, `differentiable_listObs`, **`fderiv_listObs_u`, `fderiv_listObs_φ`**, `abs_fderiv_listObs_u_le`, `abs_fderiv_listObs_φ_le`, `abs_listObs_sub_le` (face form), `listObs_add_two_pi` |
| `Tube/Obs/Sparse.lean` (core) | 159 | `spMode`, `spSum`, `spW`, `spZ0`, `spNZ`; `hasFDerivAt_spSum`, `abs_fderiv_spSum_le`, `abs_spSum_sub_le`; `SpD.eval_fun_eq`, `SpD.differentiable_eval`, `SpD.eval_add_two_pi`, `SpD.abs_eval_le'`, `SpD.abs_fderiv_eval_le` (exact `Σ_e |k_b| |m_e|`), `SpD.abs_eval_sub_le` (centred bound) |
| `Tube/Obs/Check.lean` (core) | 220 | `litObs`; `degT`, `compT`, `subT`, `unitT`, `kapT`; `fuSum`, `phiSum`, `faceSum`; the checks `obsWF`, `obsFuOK`, `obsPhiOK`, `obsFaceOK` and **`obsFuOK_sound`, `obsPhiOK_sound`, `obsFaceOK_sound`**; `differentiable_litObs`, `litObs_add_two_pi` |
| `SJSU/Obs/Data.lean` (generated) | 36 | `sjsuObsCtQ`, `sjsuObsEpsQ` |
| `SJSU/Obs/Main.lean` | 121 | `fObs`, `sjsuObs`, `sjsuObsCt`, `sjsuObsEps`, `fObs_eq_litObs`; the 9 kernel checks; **`sjsu_hfper`, `sjsu_hfd`, `sjsu_hFu`, `sjsu_hFφ`, `sjsu_hface`, `sjsu_hερ`** |

Scratch (not repository code): `.drafts/g2/scratch/N8-Obs/` contains:
- `parse.py`: parses N7's Lean data and mirrors the checks exactly in Fractions; writes `obs.pkl`;
- `gen_obs.py`: writes `Data.lean`;
- `est.py`: phase-1 estimate from F-v1;
- `Axioms.lean`: axioms and the consumer application check.

## Main statements (namespace `KAM.EffectiveStability.SJSU`)

```lean
def fObs (j : ℕ) (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  ((Ftab j).map fun e => umon (monOf e.1) p.1 * (e.2.opd Fprm.w Fprm.S).eval Fprm.S p.2).sum
def sjsuObs : Fin 3 → (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ := fun j => fObs j
theorem sjsu_hfper (j : Fin 3) : ObsPeriodic (sjsuObs j)
theorem sjsu_hfd (j : Fin 3) : Differentiable ℝ (sjsuObs j)
theorem sjsu_hFu : ∀ (j : Fin 3) (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ), (∀ l, |u l| ≤ 2 / 10 ^ 6) →
    ∀ l, |fderiv ℝ (sjsuObs j) (u, φ) (Pi.single l 1, 0)| ≤ (sjsuFuMax j l : ℝ)
theorem sjsu_hFφ : ∀ (j : Fin 3) (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ), (∀ l, |u l| ≤ 2 / 10 ^ 6) →
    ∀ b, |fderiv ℝ (sjsuObs j) (u, φ) (0, Pi.single b 1)| ≤ (sjsuFphiMax j b : ℝ)
theorem sjsu_hface : ∀ (j : Fin 3) (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ), (∀ l, |u l| ≤ 2 / 10 ^ 6) →
    |sjsuObs j (u, φ) - sjsuObsCt j - u j| ≤ sjsuObsEps j
theorem sjsu_hερ : ∀ j : Fin 3, 1 / 10 ^ 6 + sjsuObsEps j + (sjsuObsEps j + (sjsuMu : ℝ)) <
    2 / 10 ^ 6
```

`sjsuFuMax` and `sjsuFphiMax` are N5c's ceilings, unchanged.

## Numbers (exact mirror of the kernel checks, `parse.py`)

| j | Fu (l = 0, 1, 2) | ceiling | Fφ (b = 0, 1) | ceiling | face sum | ε_j | `δ + 2ε + μ` |
|---|---|---|---|---|---|---|---|
| J | 1.1295, 0.0217, 0.0274 | 1.2, 0.03, 0.035 | 3.67e-7, 3.11e-7 | 5e-7, 4e-7 | 3.5459e-7 | 3.546e-7 | 1.710δ |
| S | 0.1385, 1.0213, 0.0530 | 0.16, 1.1, 0.065 | 3.16e-7, 4.50e-7 | 4e-7, 6e-7 | 4.2325e-7 | 4.233e-7 | 1.848δ |
| U | 0.0235, 0.0017, 1.0714 | 0.03, 0.002, 1.15 | 6.70e-8, 1.55e-7 | 1e-7, 2e-7 | 1.8692e-7 | 1.870e-7 | 1.375δ |

- **Centres.** `c̃_j = q₀ m₀`, the mode-0 value of the u⁰ coefficient, exact:
  (3.04e-16, −2.36e-15, 2.05e-15).
- **Face bound.** It is the exact centred ℓ¹ bound. Per term (s, d) it is
  `ρ^|s| (|q m₀ − κ_s| + |q| Σ_{k≠0}|m|)`, with `κ = c̃` for s = 0, `κ = 1` for s = e_j and `κ = 0`
  otherwise. It is dominated by `ρ|g_{j,e_j} − 1|` and the linear cross terms, matching phase 1's 0.42δ.
- **Margins.** `hερ` holds with a margin of at least 0.15δ (Saturn). The tightest ceiling is
  `Fφ_{S,0}` (3.16e-7 ≤ 4e-7, about 21 % headroom).

## Checks run

- **Builds.** `.drafts/g2/g2lake build KAM.EffectiveStability.SJSU.Obs.Main` gives "Build completed
  successfully (2994 jobs)" (17:30 UTC). It builds `Tube.Obs.ListObs`, `Tube.Obs.Sparse`, `Tube.Obs.Check`
  (each ≈ 3 s), `SJSU.Obs.Data` and `SJSU.Obs.Main` (44 s, of which about 10 s is import replay; the nine
  `decide +kernel` checks, one declaration each). There are no warnings in my files.
- **`#print axioms`** (`.drafts/g2/scratch/N8-Obs/Axioms.lean`): `sjsu_hFu`, `sjsu_hFφ`, `sjsu_hface`,
  `sjsu_hερ`, `sjsu_hfper`, `sjsu_hfd`, `fderiv_listObs_u`, `fderiv_listObs_φ` all show
  `[propext, Classical.choice, Quot.sound]`.
- **Consumer check (same file).**
  `sjsu_secular_confinement_of_obs hHh hhd sjsu_hfper sjsu_hfd hη hTη sjsu_hface sjsu_hερ sjsu_hFu sjsu_hFφ z₀`
  typechecks, with h, η, hHh, hhd, hη, hTη abstract. g2-n5b reports that its staged
  `sjsu_secular_confinement_of_rate` uses the names unchanged and leaves only `hη`, `hTη` (N7).
- **Lint.** `.drafts/g2/lint_noabi.sh` (`abi_hashes` skipped, per the rule) exited 1, with no finding in
  my files.
  - Overlong lines: 27, all in other workers' files (e.g. N5a's `SJSU/Model` dev copies). My files were
    re-checked with `awk 'length > 100'` after the reflow: none.
  - `KAM.lean is out of date`: the roots are kam-g2's step.
  - Passed: `check_lean_modules: PASS (18569 Lean files)`, the unit tests (29 + 8) `OK`,
    `FROZEN-ANCHOR GUARD OK`.

## Design signals

None at default heartbeats. There is no decoding: the sparse format reduces every bound to entry sums,
and the kernel cost is about 4 s per check.

## Uncertainties

- **Dependence on N7's data.** The checks depend on N7's data as landed (not yet committed when I built).
  A regeneration with the same values only re-runs the checks. `w` in `Fprm` is provisional and does not
  matter, since my checks use only `Fprm.S` (through `SpD.ok`) and the entries. New values need
  `parse.py` → `gen_obs.py` (new `ε_j`) and a rebuild; the margins (≥ 21 % on ceilings, ≥ 0.15δ on the
  face condition) absorb small changes.
- **Partial formulas for N7.** `fderiv_listObs_φ` states the φ-partial with
  `fderiv ℝ (g e) p.2 (Pi.single b 1)`, which is N3's `pderiv (g e) p.2 b` by abbrev.

## Deviations from the brief

- **No `l1Check` claims.** There is no separate `Fcl`/`l1Check` path: N7 switched to sparse literals, and
  `SpD.l1E` and the entry sums replace the claims (agreed with N7).
- **Exact ∂_φ norms.** The ∂_φ bound uses the exact weighted entry sum `Σ_e |k_b||m_e|`, not `C·l1`, so
  N5c's ceilings did not need to be raised.

No suspected errata in pinned sources.

READY g2-n8
