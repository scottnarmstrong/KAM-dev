# S9-L prover handoff (branch inp-s9l, a7d5bf4; contains inp-s9n (audited); offloaded package run by the main orchestrator; prover on claude-12)


## Files (all new)
`KAM/Planetary/SecularSpectrum/Lift.lean` (facade; holds `theorem lift`, byte-identical statement to
P810Signatures.lean), plus `KAM/Planetary/SecularSpectrum/Lift/`:
- `Basic.lean` (168 lines): `liftMap`, `liftInv`, `liftDomain` verbatim; algebra: `liftInv_liftMap_of_isSO`,
  `liftMap_liftInv_of_isSO`, `fast_snd_liftMap`, `length2_slow_{fst,snd}_liftMap`, `liftMap_add_append`
  (stepP:p9:lift-bij).
- `Analytic.lean`: `analyticAt_liftMap` (analyticity via entries; avoids a norm instance on `Vec n →L Mat n`).
- `Calculus.lean`: coordinatewise `HasDerivAt` rules, `deriv_orth` / `deriv_orth'` (differentiating R Rᵀ = 1),
  `fderiv_transpose`, `liftInv_eq_liftMap_transpose` (liftInv R = liftMap Rᵀ on the domain; used to get
  analyticity and symplecticity of the inverse).
- `Hessian.lean`: entrywise second derivative `hess`, linearity, symmetry (`hess_symm`, commuting second derivatives),
  line derivative of `fderiv R`.
- `Deriv.lean`: explicit derivative `dLift` (with dTheta/dP/dQ) and `fderiv_liftMap_eq`.
- `Core.lean`: `core_identity`, the matrix identity (Maurer–Cartan step) giving cancellation of all first-derivative terms.
- `Symplectic.lean`: `sum_dTheta`, `symplecticForm_dLift` (full frozen symplectic form identity).
Largest file 168 lines.

## Approach
liftMap's derivative is computed as a line derivative; the angle shift contributes dp·(A_l q), p·(A_l dq),
p·(dA_l q) with A_l = ∂_l R Rᵀ. Pairing against the frozen `symplecticForm` (split into fast/slow sums), the Hessian
terms cancel by `hess_symm`, the rest by `core_identity` (uses R Ruᵀ = −Ru Rᵀ). Inverse: via liftInv R = liftMap Rᵀ.

## Checks
- Gate build `inp_lake_build.sh /root/code/KAM-inp-s9l KAM.Planetary.SecularSpectrum.Lift`: success, no warnings in my files.
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK, no long lines. Only note:
  "KAM.lean is out of date" (expected; not edited, orchestrator regenerates).
- No sorry/axiom/maxHeartbeats (grep clean).
- `#print axioms KAM.Planetary.SecularSpectrum.lift`: [propext, Classical.choice, Quot.sound].

## Uncertainties / errata / deviations
None. Statements unchanged; no extra hypotheses (hW, hAn, hR only). The only Lean-side design note: `fderiv ℝ (fderiv ℝ R)` has
no norm instance with the elementwise `Mat n` norm, so second derivatives are handled entrywise (`hess`); no heartbeat issues.
Imports: Mathlib, Norms (S9-N), Kepler/Basic (IsSymplecticOn); no providers, no frozen theorems.

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S9-L and its proof plan; audits DESIGN-P810-design-audit-{1,2}.md; signatures .drafts/design/P810Signatures.lean): (1) statements/definitions = design signatures (liftMap, liftInv, lift; bijectivity, Maurer-Cartan); (2) proofs sound; no added premises; (3) hygiene. Audit ONLY SecularSpectrum/Lift*.lean (compare with branch inp-s9n).
