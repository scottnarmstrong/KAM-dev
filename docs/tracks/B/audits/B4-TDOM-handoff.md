# Handoff B4-TDOM

Files: `KAM/EffectiveStability/TorusDomain.lean` (295 lines, new; imports `PolyDomain`). Nothing else touched.

Notation: `P := (Fin n → ℂ) × (Fin n → ℂ)`, `W := scaleCLE ρ' σ' hρ' hσ'`, `ι := KAM.realInclusion₂ n`.

## Declarations (all in `KAM.EffectiveStability`)
- `def cstripOpen (σ ρ : ℝ) : Set P := {z | ∀ i, |(z.1 i).im| < σ ∧ ‖z.2 i‖ < ρ}`; `isOpen_cstripOpen`.
- `def cshiftVec (s : Fin n → ℝ) : P := (fun i => (s i : ℂ), 0)`; `cshiftVec_integer`;
  `add_cshiftVec_mem_cstripOpen`; `image_add_cshiftVec_cstripOpen (σ ρ) (s) :
  (fun w => w + cshiftVec s) '' cstripOpen σ ρ = cstripOpen σ ρ` (any real shift, so integer m too).
- Gauge: `mem_gaugeInterior_cstripOpen (hρ' hσ') (hz : ∀ i, |(z.1 i).im| + c*σ' < σ ∧ ‖z.2 i‖ + c*ρ' < ρ) :
  z ∈ gaugeInterior W (cstripOpen σ ρ) c`.
- Small field: `smallField_of_strip_bounds (hρ' hσ') (hφ : DifferentiableOn ℂ φ (cstripOpen σ ρ)) (hε0 : 0 ≤ ε)
  (hε : ε ≤ 1/2) (hJ : ∀ z ∈ cstripOpen σ ρ, ∀ i, ‖fderiv ℂ φ z (0, Pi.single i 1)‖ ≤ ε*σ')
  (hθ : ∀ z ∈ cstripOpen σ ρ, ∀ i, ‖fderiv ℂ φ z (Pi.single i 1, 0)‖ ≤ ε*ρ') :
  SmallField W (cstripOpen σ ρ) (KAM.hamiltonianVectorFieldℂ φ) ε`. Weights: first field component
  (angle velocity ∂_J φ) gets σ', second (∂_φ φ) gets ρ'. Also `differentiableOn_hamVFℂ_strip`.
- Equivariance: `hamVFℂ_shift`; `flow_shift_equivariant (h : SmallField W …) (s) (hper : ∀ w ∈ cstripOpen σ ρ,
  φ (w + cshiftVec s) = φ w) (hz : z ∈ gaugeInterior W _ (1/2)) (ht : t ∈ Icc (-1) 1) :
  flow F Ω t (z + cshiftVec s) = flow F Ω t z + cshiftVec s`;
  `def rshiftVec s := (s, 0)`, `rshiftVec_integer m : rshiftVec (↑m) = angleShift m` (rfl),
  `realInclusion₂_rshiftVec`, `realInterior_add_rshiftVec`;
  `realFlow_shift_equivariant` (real s) and `realFlow_angleShift_equivariant (m : Fin n → ℤ)
  (hper : ∀ w ∈ cstripOpen σ ρ, φ (w + ((fun i => (m i : ℂ)), 0)) = φ w) (hx : x ∈ realInterior W _ (1/2))
  (ht : t ∈ Icc (-1) 1) : realFlow φ Ω t (x + angleShift m) = realFlow φ Ω t x + angleShift m`
  (premises hφ, small field, `hreal` as in `realInclusion₂_realFlow`);
  `comp_realFlow_angleShift`: `H (y + angleShift m) = H y` for all y ⇒ `H ∘ realFlow` angle-periodic there.
- Cylinder: `cyl_subset_realInterior_cstrip (hσ : σ' < σ) (hc : ∀ i, c i + ρ' ≤ ρ) : cyl c ⊆ realInterior W
  (cstripOpen σ ρ) 1`; `cylClosed_subset_realInterior_cstrip` (needs `c i + ρ' < ρ`).
- Cauchy: `cauchyDisc_subset_gaugeInterior_strip (hσ : δc + σ'/2 < σ) (hr : ∀ i, r i + δc + ρ'/2 < ρ)
  (hx : ∀ i, |x.2 i| ≤ r i) : {w | ∀ i, ‖w.1 i - (ι x).1 i‖ ≤ δc ∧ ‖w.2 i - (ι x).2 i‖ ≤ δc} ⊆
  gaugeInterior W (cstripOpen σ ρ) (1/2)`.
- Smoke: `smallField_strip_zero_smoke`, `zero_mem_gaugeInterior_strip_smoke` (φ = 0, ε = 0).

Approach: mirrors PolyDomain; shift invariance of the field from `fderiv_comp_add_right` + `EventuallyEq.fderiv_eq`
(strip open); real flow via `realInclusion₂_realFlow` + `flow_d`.

## Checks
- `b_build.sh … KAM.EffectiveStability.TorusDomain`: `Build completed successfully (2941 jobs)`, no warnings.
- `scripts/lint_sources.sh`: OK (25 tests OK, FROZEN-ANCHOR GUARD OK, ABI HASHES OK).
- Line-length check: `[]`. Short-name check: `short-name check OK`, rc=0.
- `#print axioms` (all main lemmas): `[propext, Classical.choice, Quot.sound]`.

Signature changes: none requested beyond brief (item 4 stated for any real shift, with integer corollary).
Design signals: none. Errata: none.

## AUDIT FOCUS (kam-b1)
Track B, program B4 (overnight D71; nothing frozen; scope OD-B11 by root-b8; OD-B12). Brief:
/root/code/KAM-inp-b1/.drafts/B/brief-B4-TDOM.md and brief-B1-common.md. Mirrors the landed, audited B2-DOM
(PolyDomain.lean) for the torus/cylinder route ending in B1-T (KAM/EffectiveStability/Torus.lean). Check: (1) each lemma
true as stated, minimal premises, no conclusion-shaped hypotheses; (2) the strip domain is translation invariant under
real angle shifts and the scaleCLE gauge weights match the field components (angle velocity ∂_J φ with σ', action
velocity ∂_φ φ with ρ'); (3) the equivariance of the complex and real flows under integer angle shifts (flow_d) and the
periodicity consequence for H ∘ realFlow are correct — this is what B1-T's angle-periodic R premise will rest on;
(4) cylinder and Cauchy-disc inclusions for the stated radii; (5) hygiene (AGENTS rules 3, 4, 7; widths ≤ 100), names,
axioms. Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.
