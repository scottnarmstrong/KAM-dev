# Handoff B2-COMPOSE

Files: `KAM/EffectiveStability/ChartChain.lean` (new, ~190 lines). No other file touched.

## Declarations (namespace KAM.EffectiveStability; n implicit)
- `structure IsCanonicalChart (Ψ Ψinv) (D V : Set Ph) : Prop` with fields `chart_open`, `chart_smooth`
  (ContDiffOn ℝ 2 Ψ D), `chart_maps` (MapsTo Ψ D V), `chart_symp`, `chart_leftInv` (the five B1 premises).
- `IsCanonicalChart.chart_comp (h₂ : IsCanonicalChart Ψ₂ Ψ₂inv D₂ V₂) (h₁ : IsCanonicalChart Ψ₁ Ψ₁inv D₁ V₁)
  (hsub : V₂ ⊆ D₁) : IsCanonicalChart (Ψ₁ ∘ Ψ₂) (Ψ₂inv ∘ Ψ₁inv) D₂ V₁`
  (named `chart_comp`, not `comp`: short-name gate collides with Mathlib).
- `IsCanonicalChart.id_chart (hD : IsOpen D) : IsCanonicalChart id id D D`
- `IsCanonicalChart.mono_chart (h) (hD' : IsOpen D') (hD : D' ⊆ D) (hV : V ⊆ V') : IsCanonicalChart Ψ Ψinv D' V'`
  (shrink domain to an open subset, enlarge target; openness of D' is required since the structure bundles it).
- Finite chains: `structure ChartStep n` (stepMap, stepInv, stepDom, stepTgt), `chartChainMap`, `chartChainInv`,
  `chartChainTarget D`, `ChartChainOK D l`, and
  `chartChain_isCanonical D : ∀ l, ChartChainOK D l → IsCanonicalChart (chartChainMap l) (chartChainInv l) D (chartChainTarget D l)`.
  List is outermost-first; `ChartChainOK` = each step canonical, inner target ⊆ step domain, `IsOpen D` at the
  innermost position (empty chain = identity on D).
- `hamiltonian_comp_transfer (h₁ : ∀ w ∈ D₁, H (Ψ₁ w) = K₁ w) (h₂ : ∀ w ∈ D₂, K₁ (Ψ₂ w) = K₂ w)
  (hm : MapsTo Ψ₂ D₂ D₁) : ∀ w ∈ D₂, H ((Ψ₁ ∘ Ψ₂) w) = K₂ w`
- `oscillator_confinement_of_chart`, `torus_confinement_of_chart`: same conclusions/other binders as the B1
  theorems, chart premises replaced by `IsCanonicalChart Ψ Ψinv (osc fun j => b j + ε) V` (resp. `cyl`); proved by
  direct application of the B1 theorems.
- `chart_id_comp_id` smoke test: `IsCanonicalChart (id ∘ id) (id ∘ id) D D`.

## Approach
Chain rule `fderiv_comp` (differentiability from ContDiffOn on open sets), symplectic identities rewritten
successively, inverse identity via `MapsTo Ψ₂ D₂ D₁` from `V₂ ⊆ D₁`. Chain by list induction using `chart_comp`.

## Checks
- `b_build.sh … KAM.EffectiveStability.ChartChain`: built, no warnings.
- Line-length script: `[]`. Short-name gate: `short-name check OK`, exit 0.
- `#print axioms` (scratch, untracked) for chart_comp, chartChain_isCanonical, both wrappers, transfer, smoke test:
  `[propext, Classical.choice, Quot.sound]` each.
- `scripts/lint_sources.sh` (after rename): OK, FROZEN-ANCHOR GUARD OK, ABI HASHES OK.

## Deviations / signature changes
`comp` renamed `chart_comp`; `mono_chart` takes `IsOpen D'`. Required items 1–7 otherwise as requested; no `Fin m` family version (list version only).
Design signals: none. Errata: none.

## AUDIT FOCUS (kam-b1)
Track B, program B2 (overnight D71; nothing frozen; scope OD-B7). Brief: /root/code/KAM-inp-b1/.drafts/B/brief-B2-COMPOSE.md and
brief-B1-common.md; design: program-b-plan §3.2 "Composition of exact flows remains canonical"
(/root/code/KAM/docs/explorations/program-b-plan.md lines 341-420). Consumers: multi-generator normalizations, and the
B1 headlines (KAM/EffectiveStability/Oscillator.lean, Torus.lean). Check: (1) IsCanonicalChart bundles exactly the
five B1 chart premises (source premises, not conclusions) and the `_of_chart` wrappers are faithful conveniences that
do NOT replace or weaken the B1 headlines (distinct names, same conclusion); (2) chart_comp's chain rule, symplectic
composition and inverse composition are correct, with the needed domain inclusion; (3) the list-chain definition
(outermost-first) composes in the intended order and ChartChainOK is decidable-in-spirit finite data; (4) hygiene
(AGENTS rules 3, 4, 7; line length ≤ 100), names, axioms. Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.
