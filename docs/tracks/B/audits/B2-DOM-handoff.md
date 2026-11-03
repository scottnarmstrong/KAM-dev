# Handoff B2-DOM
Files: new `KAM/EffectiveStability/PolyDomain.lean` (~200 lines). Nothing else changed.
Approach: direct coordinate estimates. `gaugeScalar` = `ContinuousLinearEquiv.smulLeft (Units.mk0 (δ:ℂ)⁻¹ _)`;
holomorphy of `hamiltonianVectorFieldℂ φ` via `KAM.contDiffOn_infty_of_differentiableOn` + `fderiv_of_isOpen`.
Declarations (all in `KAM.EffectiveStability`):
- `cpolyOpen (ρ : ℝ) : Set P`; `isOpen_cpolyOpen (ρ)`
- `gaugeScalar (δ) (hδ : 0 < δ) : P ≃L[ℂ] P`; `gaugeScalar_apply`; `norm_gaugeScalar_apply : ‖gaugeScalar δ hδ v‖ = ‖v‖ / δ`
- `mem_gaugeInterior_cpolyOpen (hδ) (_hc : 0 ≤ c) (hz : ∀ i, ‖z.1 i‖ + c*δ < ρ ∧ ‖z.2 i‖ + c*δ < ρ) : z ∈ gaugeInterior (gaugeScalar δ hδ) (cpolyOpen ρ) c`
- `differentiableOn_hamVFℂ_poly (hΩ : IsOpen Ω) (hφ : DifferentiableOn ℂ φ Ω) : DifferentiableOn ℂ (hamiltonianVectorFieldℂ φ) Ω`
- `smallField_of_coord_bounds (hδ) (hφ) (hε0) (hε) (h1) (h2) : SmallField (gaugeScalar δ hδ) (cpolyOpen ρ) (hamiltonianVectorFieldℂ φ) ε`
- `mem_realInterior_cpolyOpen (hδ) (hr : ∀ i, r i + δ < ρ) (hx : ∀ i, |x.1 i| ≤ r i ∧ |x.2 i| ≤ r i) : x ∈ realInterior (gaugeScalar δ hδ) (cpolyOpen ρ) 1`
- `osc_subset_realInterior`, `oscClosed_subset_realInterior` (hyps `2 * c i ≤ r i ^ 2`, `0 ≤ r i`, `r i + δ < ρ`)
- `cauchyDisc_subset_gaugeInterior (hδ) (hr : ∀ i, r i + δc + δ/2 < ρ) (hx) : {w | ∀ i, ‖w.1 i - (ι x).1 i‖ ≤ δc ∧ ‖w.2 i - (ι x).2 i‖ ≤ δc} ⊆ gaugeInterior … (1/2)` (0<δc not needed)
- `flow_mem_cpolyOpen (h : SmallField W (cpolyOpen ρ) F ε) (hz) (ht) : flow F (cpolyOpen ρ) t z ∈ cpolyOpen ρ`
- `smallField_zero_smoke`, `zero_mem_gaugeInterior_smoke`
Signature notes: item 5's oscillator form needs no extra hypotheses; `_hc : 0 ≤ c` in item 3 is unused (kept per brief); `0 < δc` dropped in item 6 (unneeded). Smoke test item 3 part states `0 ∈ gaugeInterior` under `c*δ < ρ`.
Checks: `b_build.sh … PolyDomain` built, no warnings; `scripts/lint_sources.sh` OK (25 tests, anchor guard, ABI hashes OK);
line-length check printed `[]`; short-name check "OK (no reused public short name)", rc=0.
`#print axioms` of every declaration above: [propext, Classical.choice, Quot.sound].
Design signals: none (build ~3 s). Errata: none.

## AUDIT FOCUS (kam-b1)
Track B, program B2 (overnight D71; nothing frozen; scope OD-B7). Brief: /root/code/KAM-inp-b1/.drafts/B/brief-B2-DOM.md and
brief-B1-common.md; design: program-b-plan §3.1 "nested complex domains, radii and rational strict margins"
(/root/code/KAM/docs/explorations/program-b-plan.md lines 300-340). Consumers: the one-step soundness theorem (next
package), through KAM.Canonical.SmallField / gaugeInterior / flow (KAM/Canonical/Flow.lean, FlowRegular.lean) and
KAM/EffectiveStability/RealFlow (realInterior). Check: (1) each lemma true as stated, minimal premises, no
conclusion-shaped hypotheses; (2) norms: the sup norms on Fin n → ℂ and products, the gauge identity ‖W v‖ = ‖v‖/δ,
the gaugeInterior characterization with strict margins; (3) the small-field lemma really bounds ‖W (X_ℂ φ z)‖ by ε
from the coordinate partials; (4) chart/Cauchy-disc inclusions are correct for the stated radii; (5) hygiene (AGENTS
rules 3, 4, 7; line length ≤ 100), names, axioms. Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.
