# Package LP-NRR: the engine's analytic data and the stopped drift (MAIN Lemma 13)

Wave 2, the last analytic package. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules,
capped wrappers, handoff). Base: `inp-lp-nrr` = LP-DOM + LP-NRS on top of the landed wave 1. Handoffs:
`docs/tracks/LP/audits/LP-{DOM,NRS,DICT}-handoff.md`.

## Goal

For each centre `I⁰ ∈ 𝓛_δ` satisfying the Diophantine condition (5), and every small `μ`:
1. build a `KAM.Nekhoroshev.PartialBlock n n` and complex data `h, f`;
2. prove `ExtNFHyp b s K α L 2 ε {0} h f` and the smallness premise `hsmall`;
3. prove the trace identity against the rescaled chart Hamiltonian;
4. compose with LP-DICT's conditional `nonresonant_drift_of_chartData` into the stopped drift bound
   `‖Λ(z u) − I⁰‖ ≤ r/2` up to time `T₀ exp(c μ^{-a})`.

Every constant is chosen before `μ`, `I⁰` and the solution.

## Source

`docs/tracks/LP/source/MAIN.md` Lemma 13 (lines 429–464), with `source/AMENDMENTS.md`:
- **N6** (binding): `2πs₁ < 4s` with margin for the weighted sum; `w < 4b`; `D₀√μ < r_*`;
  `F = realWfield b.c (realHamiltonianExt b b.rB (liftFast h + f))`; `realDom` open; stopped radius
  `r = D₀√μ`, improvement to `r/2`.
- **N4:** (35) is not a dependency.

Roadmap §3 row 13.

## Pieces (all exist)

- **Engine:** `KAM/Nekhoroshev/Partial/{Setting,Nonresonant}.lean` (`PartialBlock`: `Ic`, `S`, `rB`, `w`,
  `lam = w/rB`, `c = 2π/lam²`, `base`, `realDom`; `ExtNFHyp` fields; `ext_class` = `InClass` ∧ `extReal`),
  `KAM/Nekhoroshev/NormalForm/Setting.lean` (`IsNonresonant`, `FreqLipschitz`, `zBall` (ℓ¹), `freq`, `dotC`,
  `conjExp`), and `KAM/Weighted/SupWeighted.lean` (`wbound_of_sup_bound`: `InClass D r (s+σ) u` + sup bound
  `M` on `Dom n D r (s+σ)` ⇒ `WBound D r s u (coth(πσ)^n M)`).
- **LP-DOM:** `exists_isSharedTube`, `strongCore`, `exists_strongTube` (holomorphic periodic `fc`, sup bound `M`
  on `complexTube core (R/2)`, real trace = `fMov 1 1 ν ∘ poincareProd ν 1`), `strongCore_containment` (the
  (22) set ⊆ `complexTube core (R/2)`), `secularBall`, `movingHamiltonian_poincareProd_split`.
- **LP-NRS:** `lp_scale_choice` (items (a)–(g)), `diophantine_to_period_one`.
- **LP-DICT:** `lpRescale`, `lpRescaleHam`, `lpRealDom_isOpen`, `lpIndicator_field`,
  `nonresonant_drift_of_chartData`.
- **Kepler part:** `planetaryKeplerC ν I = −Σ ν_i³/(2 I_i²)` (`Exponential/Setting.lean`).

## Owned files

`KAM/Planetary/StrongAMD/NonresonantReuse.lean` (facade) and parts `KAM/Planetary/StrongAMD/NonresonantReuse/*.lean`.
Nothing else.

## Statements

1. **Kepler data (period one).** `lpKepler ν I := planetaryKeplerC ν I / (2π)`. On
   `polyNbhd {I⁰} ρ`, with `ρ ≤ I_min/2` (`I_min` a positive lower bound of the actions over `U`), prove:
   - holomorphy;
   - reality on real points;
   - `freq lpKepler I⁰ = ω(I⁰)/(2π)` (`ω_i = ν_i³/I_i³`);
   - `FreqLipschitz {I⁰} ρ L lpKepler`, with `L` uniform over `I⁰ ∈ U` (e.g. `L = max_i 3ν_i³/(2π (I_min/2)⁴)`).
2. **Nonresonance.** From (5) at `I⁰` (stated with `modeSize`, real dot product and `ω(I⁰)`): with
   `IsNonresonant {I⁰} K (γ/(2π) K^{-τ}) {0} lpKepler`, use `diophantine_to_period_one`. `{0}` is symmetric.
3. **Perturbation.** `lpPert ν μ ℓ fc : EC n n → ℂ := (μ/(2π)) · fc (complex unrescaling: λ = 2πθ, Λ = I,
   (ξ, η) = ℓ·(slow q, slow p))`. With `b := ⟨I⁰, secularBall ν δ I⁰, D₀√μ, w⟩`, prove:
   - the complex unrescaling maps `Dom n b.base b.rB (s+σ)` into the (22) set of `strongCore_containment`, under
     explicit fixed width conditions `2π(s+σ) ≤ 4s₀`, `w < 4b₀`, `rB ≤ r_s ≤ 4 r_g`, `max r_s (4s₀) (4b₀) < R/2`
     (N6);
   - `ext_class b b.rB (s+σ) lpPert`: holomorphy and period-one periodicity from `fc`; reality from the real
     trace;
   - `WBound b.base b.rB s lpPert ε` with `ε = M₂ μ`, `M₂ := coth(πσ)^n · M/(2π)`, via `wbound_of_sup_bound`.
4. **`ExtNFHyp` and `hsmall`.** For `0 < μ ≤ μ₀` (with `μ₀`, `κ`, `c`, `T₀` from `lp_scale_choice` fed with
   `γ, τ, L, M₂, D₀, s, w, ρ`), assemble `ExtNFHyp b s K α L 2 ε {0} lpKepler lpPert`, field by field, and
   `hsmall`.
5. **Trace identity.** On `b.realDom b.rB`:
   `((liftFast lpKepler + lpPert) (extCx y)).re = lpRescaleHam b.lam (liftChartHam ν μ) y`. Use
   `movingHamiltonian_poincareProd_split` and DOM's real trace; DICT's adapter needs exactly this form.
6. **Stopped drift (MAIN L13 conclusion; the main theorem of the package).** `∃ μ₀ c T₀ > 0` (and the fixed
   widths), chosen before `μ`, such that for every `0 < μ ≤ μ₀`, every `I⁰ ∈ 𝓛_δ` with (5), and every moving
   solution with chart lift `w` meeting DICT item 9's premises:
   - `fastAction (lpRescale b.lam (w 0)) = I⁰`;
   - `realDom` membership along `J`;
   - stopped slow membership in `secularBall ν δ I⁰` on `uIcc 0 t1`;
   - `|t1| ≤ T₀ exp(c μ^{-a})`;

   it holds that `‖(fun i => keplerAction ν (z u) i) − I⁰‖ ≤ D₀√μ/2` for `u ∈ uIcc 0 t1`. The premises are the
   physical solution, its chart lift and the stopped/outer-domain localization (audit note D1; LP-CONF supplies
   them). Never a drift or AMD bound.

Out of scope: the first-exit argument (L14) and the planar theorem (T15).

## Checks and stop condition

- `lp_build.sh` on each module (import order).
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of items 1–6.

Stop when done or blocked. If a field of `ExtNFHyp` cannot be met with the data above (e.g. a width
mismatch), STOP and report the exact field and inequality; do not weaken the engine or add a hypothesis.
Expected size 1,000–2,500 lines, split into parts (`Kepler`, `Pert`, `Hyp`, `Drift`).

## Handoff

`docs/tracks/LP/audits/LP-NRR-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-NRR.md`, then
`touch .drafts/READY-LP-NRR`.
