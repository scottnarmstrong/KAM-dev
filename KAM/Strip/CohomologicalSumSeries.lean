/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.CohomologicalRussmannLattice
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The small-divisor series of a frequency

`KAM.smallDivisorSum ω δ = S(ω, δ) = ∑_{k≠0} |k·ω|⁻² e^{-2πδ|k|₁}`, the series through which the
Parseval and Rüssmann estimates pass before any lattice counting (Bessel on the corners and
Cauchy–Schwarz give `‖𝓡 g‖ ≤ (2π)⁻¹ 2^{n/2} S(ω, δ)^{1/2} A`, `KAM.norm_cohSolution_sum_le`).

* `KAM.smallDivisorTerm`, `KAM.smallDivisorSum`: the terms (nonnegative, `0` at `k = 0`) and the
  `tsum`.
* `KAM.summable_smallDivisorTerm`: for `(γ, τ)`-Diophantine `ω` and `δ > 0` the series is summable,
  by Rüssmann's lattice bound on all finite partial sums (`KAM.sum_inv_sq_exp_le`).
* `KAM.smallDivisorSum_le_russmann`: `S(ω, δ) ≤ 6 (1 + 2^τ) γ⁻² (2τ/(eπδ))^{2τ}`, and
  `KAM.cohConstSum_le_russmann`: `(2π)⁻¹ 2^{n/2} S^{1/2} ≤ cohConstR n τ / (γ δ^τ)`, so the
  frequency-specific estimate is never worse than `KAM.cohomological_russmann`.
-/

public noncomputable section

namespace KAM

variable {n : ℕ}

/-- The term `|k·ω|⁻² e^{-2πδ|k|₁}` of the small-divisor series, `0` at `k = 0`. -/
@[expose] def smallDivisorTerm (ω : Fin n → ℝ) (δ : ℝ) (k : Fin n → ℤ) : ℝ :=
  if k = 0 then 0 else
    ((Diophantine.frequencyDot ω k) ^ 2)⁻¹ * Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k)

/-- The small-divisor series `S(ω, δ) = ∑_{k≠0} |k·ω|⁻² e^{-2πδ|k|₁}`. -/
@[expose] def smallDivisorSum (ω : Fin n → ℝ) (δ : ℝ) : ℝ := ∑' k, smallDivisorTerm ω δ k

theorem smallDivisorTerm_nonneg (ω : Fin n → ℝ) (δ : ℝ) (k : Fin n → ℤ) :
    0 ≤ smallDivisorTerm ω δ k := by
  unfold smallDivisorTerm
  split_ifs
  · exact le_rfl
  · positivity

theorem smallDivisorTerm_of_ne {ω : Fin n → ℝ} {δ : ℝ} {k : Fin n → ℤ} (hk : k ≠ 0) :
    smallDivisorTerm ω δ k =
      ((Diophantine.frequencyDot ω k) ^ 2)⁻¹ * Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) := by
  simp only [smallDivisorTerm, hk, ↓reduceIte]

theorem smallDivisorSum_nonneg (ω : Fin n → ℝ) (δ : ℝ) : 0 ≤ smallDivisorSum ω δ :=
  tsum_nonneg (smallDivisorTerm_nonneg ω δ)

section Diophantine

variable {ω : Fin n → ℝ} {γ τ δ : ℝ}

/-- Every finite partial sum of the series is at most Rüssmann's lattice bound. -/
theorem sum_smallDivisorTerm_le (hω : Diophantine.Condition ω γ τ) (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (hδ : 0 < δ) (s : Finset (Fin n → ℤ)) :
    ∑ k ∈ s, smallDivisorTerm ω δ k ≤
      6 * (1 + 2 ^ τ) * (γ ^ 2)⁻¹ * (2 * τ / (Real.exp 1 * (Real.pi * δ))) ^ (2 * τ) := by
  classical
  have h : ∑ k ∈ s, smallDivisorTerm ω δ k = ∑ k ∈ s.filter (· ≠ 0),
      ((Diophantine.frequencyDot ω k) ^ 2)⁻¹ *
        Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = 0
    · simp [smallDivisorTerm, hk]
    · simp [smallDivisorTerm, hk]
  rw [h]
  exact sum_inv_sq_exp_le hω hγ hτ hδ s

/-- The small-divisor series is summable for Diophantine `ω` and `δ > 0`. -/
theorem summable_smallDivisorTerm (hω : Diophantine.Condition ω γ τ) (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (hδ : 0 < δ) : Summable (smallDivisorTerm ω δ) :=
  summable_of_sum_le (smallDivisorTerm_nonneg ω δ) (sum_smallDivisorTerm_le hω hγ hτ hδ)

/-- A finite partial sum is at most `S(ω, δ)`. -/
theorem sum_le_smallDivisorSum (hω : Diophantine.Condition ω γ τ) (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (hδ : 0 < δ) (s : Finset (Fin n → ℤ)) :
    ∑ k ∈ s, smallDivisorTerm ω δ k ≤ smallDivisorSum ω δ :=
  (summable_smallDivisorTerm hω hγ hτ hδ).sum_le_tsum s fun k _ => smallDivisorTerm_nonneg ω δ k

/-- Rüssmann's bound of the series: `S(ω, δ) ≤ 6 (1 + 2^τ) γ⁻² (2τ/(eπδ))^{2τ}`. -/
theorem smallDivisorSum_le_russmann (hω : Diophantine.Condition ω γ τ) (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (hδ : 0 < δ) :
    smallDivisorSum ω δ ≤
      6 * (1 + 2 ^ τ) * (γ ^ 2)⁻¹ * (2 * τ / (Real.exp 1 * (Real.pi * δ))) ^ (2 * τ) :=
  (summable_smallDivisorTerm hω hγ hτ hδ).tsum_le_of_sum_le (sum_smallDivisorTerm_le hω hγ hτ hδ)

/-- The frequency-specific constant is never worse than Rüssmann's:
`(2π)⁻¹ 2^{n/2} S(ω, δ)^{1/2} ≤ cohConstR n τ / (γ δ^τ)`. -/
theorem cohConstSum_le_russmann (hω : Diophantine.Condition ω γ τ) (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (hδ : 0 < δ) :
    (2 * Real.pi)⁻¹ * Real.sqrt (2 ^ n) * Real.sqrt (smallDivisorSum ω δ) ≤
      cohConstR n τ / (γ * δ ^ τ) := by
  set Q : ℝ := 6 * (1 + 2 ^ τ) * (2 * τ / (Real.exp 1 * Real.pi)) ^ (2 * τ) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hD : 0 < γ * δ ^ τ := mul_pos hγ (Real.rpow_pos_of_pos hδ τ)
  have hS : smallDivisorSum ω δ ≤ Q / (γ * δ ^ τ) ^ 2 := by
    refine (smallDivisorSum_le_russmann hω hγ hτ hδ).trans (le_of_eq ?_)
    rw [lattice_bound_eq_russmann hτ hδ, hQ, mul_pow]
    field_simp
  have hsq : Real.sqrt (smallDivisorSum ω δ) ≤ Real.sqrt Q / (γ * δ ^ τ) := by
    refine (Real.sqrt_le_sqrt hS).trans (le_of_eq ?_)
    rw [Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hD.le]
  calc (2 * Real.pi)⁻¹ * Real.sqrt (2 ^ n) * Real.sqrt (smallDivisorSum ω δ)
      ≤ (2 * Real.pi)⁻¹ * Real.sqrt (2 ^ n) * (Real.sqrt Q / (γ * δ ^ τ)) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = cohConstR n τ / (γ * δ ^ τ) := by
        rw [cohConstR, ← hQ, Real.sqrt_mul (show (0 : ℝ) ≤ 2 ^ n by positivity) Q]
        ring

end Diophantine

end KAM

end
