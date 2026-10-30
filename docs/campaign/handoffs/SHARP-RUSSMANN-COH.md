# Handoff SHARP-RUSSMANN-COH

Merged `apost-sharp` first. Exponent `τ` (Rüssmann) for `KAM.cohomological`, no `δ ≤ 1`, same premises.

## Files (all new; `KAM.lean` regenerated)
- `KAM/Strip/CohomologicalRussmannCount.lean` (108): `sum_inv_sq_le_of_separated_pos` / `sum_inv_sq_le_of_separated`
  (standalone counting lemma for finite sets of reals: pairwise `s`-separated, `|x| ≥ t₀` gives
  `∑ x⁻² ≤ 2 (t₀⁻² + 1/(s t₀))`; induction removing the minimum with the invariant `t⁻² + 1/(s t)`).
- `KAM/Strip/CohomologicalRussmannSep.lean` (114): `modeNat`, separation of `k·ω`, shell bound
  `sum_inv_sq_frequencyDot_le`: `∑_{0<|k|₁≤N} |k·ω|⁻² ≤ 2(1+2^τ)γ⁻² N^{2τ}`.
- `KAM/Strip/CohomologicalRussmannLattice.lean` (227): discrete Abel summation `abel_finite`, `abel_term_le`,
  `sum_exp_neg_Ico_le`, `sum_inv_sq_exp_le`
  (`∑_{k≠0} |k·ω|⁻² e^{-2πδ|k|₁} ≤ 6(1+2^τ)γ⁻²(2τ/(eπδ))^{2τ}`), `cohConstR`, `cohConstR_nonneg`,
  `cohConstR_pos` (`τ ≥ 0`, any `n`), `lattice_bound_eq_russmann`.
- `KAM/Strip/CohomologicalRussmannBound.lean` (133): `norm_cohSolution_russmann_le` (reuses
  `sum_sq_torusCoeff_exp_le` from the Parseval Bessel file; `ρ' = ρ - δ/2`).
- `KAM/Strip/CohomologicalRussmann.lean` (287): vector/matrix/a-priori transfers and the targets
  `KAM.cohomological_russmann`, `KAM.cohomological_operator_russmann`.

## Approach / deviation from the brief's step 3
`cohConstR n τ = (2π)⁻¹ √(2ⁿ · 6(1+2^τ)(2τ/(eπ))^{2τ})`. I did **not** use a dyadic decomposition: it
produces a `log(1/δ)` factor at `τ = 0` and needs an explicit constant for the dyadic series. Instead
`S_N` is combined with `w(N) = e^{-2πδN}` by exact discrete Abel summation (finite form, last term kept),
then `1 - e^{-b} ≤ b`, `N^{2τ}e^{-bN/2} ≤ (2τ/(eπδ))^{2τ}` and a geometric sum `≤ 2/b`. The constant 6 = 2+1 times
the shell constant 2(1+2^τ)/... as in the file docstring. Valid for all `δ > 0` and `τ ≥ 0`.

## Numerics (python)
`cohConstR 2 1 = 0.31628`, `cohConstR 3 2 = 0.54095`. For comparison `cohConstP 2 1 = 0.37967`,
`cohConst 2 1 = 0.48341`; `cohConstP 3 2 = 2.0854`, `cohConst 3 2 = 3.8920`.

## Checks
- Builds: `KAM.Strip.CohomologicalRussmann{Count,Sep,Lattice,Bound}` and `KAM.Strip.CohomologicalRussmann`, all succeed.
- `#print axioms` of `cohomological_russmann`, `cohomological_operator_russmann`, `cohConstR_pos`,
  `sum_inv_sq_le_of_separated`: `[propext, Classical.choice, Quot.sound]` each.
- `scripts/lint_sources.sh`: module check PASS, frozen guard OK, no over-length lines; only the known
  ABI-scratch failure (`BorderedHessian.olean` missing from the partial snapshot).
- Warnings: one deprecation (`if_neg`) in the Bound file and one in the Lattice file (cosmetic).

## Uncertainties / errata
None found. Total new code 869 lines; no file above 300.
