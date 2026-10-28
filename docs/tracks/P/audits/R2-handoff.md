# R2 prover handoff (branch inp-p11c-r2, 98374b01; offloaded package run by the main orchestrator)


## Files (all new; none exceed 270 lines; Local.lean untouched)
- `KAM/Planetary/PlanarTorsion/RealFlow/PicardOp.lean` (156): `p11cSp`, `p11cTimeScale`, `p11cDom`,
  `p11cPicardOp v ζ = w + s•∫₀¹ v(σs,w)dσ`; `p11cPicardOp_differentiableOn` (holomorphy, via U5
  `KAM.Weighted.holomorphic_parametric_integral`).
- `.../PicardComplex.lean` (270): `P11cPicardData`, `p11cPicardOp_sub_le`, iterates `p11cIter`,
  stay-in-ball, geometric Cauchy bound, limit `P11cPicardData.picardLim` (holomorphic via U5
  `KAM.Weighted.uniform_limit_holomorphic`), fixed-point equation, reality on real data.
- `.../PicardData.lean` (68): `p11c_picardData_exists` (bounds/Lipschitz from Cauchy, `general_cauchy`).
- `.../Analytic.lean` (262): `p11cPt`, `p11c_hasDerivAt_of_integral_eq`,
  `p11c_analytic_flow_fin` (ℝⁿ core), `p11c_hamField_analyticAt`, `p11cPhaseEquiv`,
  **`p11c_analytic_hamiltonian_flow`**.

## Result for R3
`p11c_analytic_hamiltonian_flow (hW : IsOpen W) (hH : AnalyticOnNhd ℝ H W) (hx : x ∈ W) :
 ∃ r T, 0<r ∧ 0<T ∧ ∃ Φ, AnalyticOnNhd ℝ (fun u : ℝ × Phase d => Φ u.1 u.2) (Ioo (-T) T ×ˢ ball x r)
 ∧ ∀ y ∈ ball x r, Φ 0 y = y ∧ IsSolutionIn (hamiltonianVectorField H) W (Ioo (-T) T) (fun t => Φ t y)`
= first two conjuncts of the signature theorem `real_analytic_hamiltonian_local_flow` (symplecticity is R3).
The signature file contains no R2-specific declaration; all names above are new helpers (p11c-prefixed,
grep-checked for no short-name clash in KAM).

## Approach
Complexify the field (`p11_complexification`, existing), run Picard in complex time on ℂ×ℂⁿ ≅ ℂⁿ⁺¹
(operator along the real segment σ↦σs so the parametric-integral theorem applies), uniform limit is
holomorphic hence real-analytic; reality of iterates on real data gives the real flow; the integral equation
gives HasDerivAt by FTC. Transfer Phase d ≅ ℝ^(d+d) by a continuous linear equivalence. Only local at a
point x (no compact/common-neighbourhood statement was needed by the signature theorem).

## Checks
- Gate build `KAM.Planetary.PlanarTorsion.RealFlow.Analytic` (and its 3 new deps): success, no warnings.
- `#print axioms` of `p11c_analytic_hamiltonian_flow` and `p11c_analytic_flow_fin`:
  [propext, Classical.choice, Quot.sound].
- `scripts/lint_sources.sh`: my files clean. Reports pre-existing `AmdConfinement.lean:77` (101 cols,
  frozen, not mine) and "KAM.lean is out of date" (generated; I did not edit it — orchestrator must regen
  for the 4 new modules). check_lean_modules PASS, frozen guard OK, ABI hashes OK.
- No sorry/axiom/maxHeartbeats/EuclideanSpace; lines ≤ 100.

## Uncertainties / errata / deviations
None. No suspected source errata. Design signals: none (default heartbeats everywhere; one mid-development
timeout in `p11cPicardOp_differentiableOn` was fixed by giving `fun_prop`-free explicit continuity terms).
Deviation: R2 delivers the local-at-a-point statement only (what the signature needs); a compact-set
common-neighbourhood version was not proved.

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row R2 ('real analytic parametric Picard convergence on common neighbourhoods; R1, U5') and its node table; P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean (R2 may have no signed declarations; the real-flow bridges are local obligations, line 20). The handoff states a DEVIATION: only the local-at-a-point statement was proved, not the compact-set common-neighbourhood version the row names. Decide whether R3 (variational equation, Hessian symmetry, real_analytic_hamiltonian_local_flow) and T9 (compact-uniform displacement) can be built from the at-a-point form, or whether the common-neighbourhood version is a required R2 deliverable (then it is a finding). Audit ONLY KAM/Planetary/PlanarTorsion/RealFlow/Analytic.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
