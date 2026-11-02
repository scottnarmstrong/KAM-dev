# Handoff B1-TRANSFER (branch inp-b1xfer)

## Files
- `KAM/EffectiveStability/Transfer.lean` (~150 lines), `KAM/EffectiveStability/ActionDerivative.lean` (~150 lines). Both new.

## Lemmas (namespace `KAM.EffectiveStability`; all signatures exactly as requested in the brief)
Transfer: `symplecticForm_hamiltonianVectorField (H z v) : ω (X H z) v = - fderiv ℝ H z v`;
`symplecticForm_nondegenerate (h : ∀ v, ω u v = 0) : u = 0`;
`bijective_of_symplectic {L : P n →L[ℝ] P n} (h : ∀ u v, ω (L u) (L v) = ω u v) : Function.Bijective L`;
`fderiv_apply_hamiltonianVectorField_comp`; `hasDerivAt_comp_chart`
(hypotheses order: `hc hΨ hH hsymp`); `contDiffOn_hamiltonianVectorField (hH : ContDiffOn ℝ 2 H V) (hV : IsOpen V)`
(= `KAM.ODE.ham_smooth_c1`); `observable_transfer_bound`.
ActionDerivative: `fderiv_eq_zero_of_const_curve` (helper), `fderiv_angle_eq_of_eventuallyEq`,
`hamiltonianVectorField_snd_apply` (rfl), `bracket_action_eq_of_eventuallyEq`, `hasDerivAt_oscillatorAction`.
No signature changes. Statements of the main lemmas are as in the brief (copied verbatim).

## Approach
Chart transport: ω(DΨ X_K, DΨ u) = ω(X_K,u) = -dK u = -dH(DΨ u) = ω(X_H, DΨ u); DΨ surjective (symplectic ⇒ injective ⇒
surjective, `LinearMap.injective_iff_surjective`); nondegeneracy. Action derivatives: `G = K - R` is differentiable at w
and eventually constant along a curve (line in the angle direction; rotation curve `w + a(θ)e₁ + b(θ)e₂` for the
oscillator), so `dG(w)·(velocity) = 0` (generic helper `fderiv_eq_zero_of_const_curve`); N is never differentiated.

## Checks
- `b_build.sh` of `KAM.EffectiveStability.Transfer` and `...ActionDerivative`: both "Build completed successfully", no warnings.
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, 25 tests OK, FROZEN-ANCHOR GUARD OK, ABI HASHES OK.
- `#print axioms` of every lemma above: only `propext`, `Classical.choice`, `Quot.sound`.

## Design signals / uncertainties / errata
None. No heartbeat issues; builds take ~2–3 s each. No errata.
