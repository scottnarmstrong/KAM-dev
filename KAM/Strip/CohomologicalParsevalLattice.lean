/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.CohomologicalDefs
public import KAM.Fourier.ExpSums
public import KAM.Fourier.ExponentialDecay
import Mathlib.Tactic.Positivity

/-!
# The constant `cohConstP` and the lattice sum of the Parseval cohomological estimate

`KAM.cohConstP n τ = (2π)⁻¹ (2ⁿ (2τ/(eπ))^{2τ} (8n/π)ⁿ)^{1/2}` is the constant of the estimate
`‖u‖ ≤ cohConstP n τ / (γ δ^{τ+n/2}) A` obtained from Bessel's inequality instead of the `ℓ¹` sum.

The lattice sum is `∑_{k≠0} |k|₁^{2τ} e^{-2πδ|k|₁} ≤ (2τ/(eπδ))^{2τ} (8n/(πδ))ⁿ`, valid for all
`δ > 0` (no restriction `δ ≤ 1`): split `e^{-2πδ m} = e^{-πδ m} e^{-πδ m}`, bound
`m^{2τ} e^{-πδ m}` by its supremum, and sum the rest with `KAM.Fourier.tsum_exp_neg_modeSize_ne_zero_le`.
-/

public noncomputable section

namespace KAM

variable {n : ℕ}

/-- The constant of the Parseval cohomological estimate:
`cohConstP n τ = (2π)⁻¹ √(2ⁿ (2τ/(eπ))^{2τ} (8n/π)ⁿ)`. -/
@[expose] def cohConstP (n : ℕ) (τ : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    Real.sqrt (2 ^ n * ((2 * τ / (Real.exp 1 * Real.pi)) ^ (2 * τ) * (8 * (n : ℝ) / Real.pi) ^ n))

theorem cohConstP_nonneg (n : ℕ) (τ : ℝ) : 0 ≤ cohConstP n τ := by
  unfold cohConstP
  positivity

theorem cohConstP_pos {n : ℕ} (hn : 1 ≤ n) {τ : ℝ} (hτ : 0 ≤ τ) : 0 < cohConstP n τ := by
  unfold cohConstP
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : 0 < (2 * τ / (Real.exp 1 * Real.pi)) ^ (2 * τ) := by
    rcases eq_or_lt_of_le hτ with h | h
    · rw [← h]
      simp
    · exact Real.rpow_pos_of_pos (by positivity) _
  have h2 : 0 < 2 ^ n * ((2 * τ / (Real.exp 1 * Real.pi)) ^ (2 * τ) * (8 * (n : ℝ) / Real.pi) ^ n) := by
    positivity
  exact mul_pos (by positivity) (Real.sqrt_pos.mpr h2)

/-- **Lattice sum.** For every finite set of modes and `δ > 0`,
`∑_{k≠0, k∈s} |k|₁^{2τ} e^{-2πδ|k|₁} ≤ (2τ/(eπδ))^{2τ} (8n/(πδ))ⁿ`. -/
theorem sum_modeSize_rpow_exp_le {τ δ : ℝ} (hτ : 0 ≤ τ) (hδ : 0 < δ) (s : Finset (Fin n → ℤ)) :
    ∑ k ∈ s.filter (· ≠ 0), Fourier.modeSize k ^ (2 * τ) *
        Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) ≤
      (2 * τ / (Real.exp 1 * (Real.pi * δ))) ^ (2 * τ) * (8 * (n : ℝ) / (Real.pi * δ)) ^ n := by
  have hx : 0 < Real.pi * δ := by positivity
  set B : ℝ := (2 * τ / (Real.exp 1 * (Real.pi * δ))) ^ (2 * τ) with hB
  have hB0 : 0 ≤ B := Real.rpow_nonneg (by positivity) _
  have hS := (Fourier.hasSum_exp_neg_modeSize n hx).summable
  set f : (Fin n → ℤ) → ℝ := {k | k ≠ 0}.indicator
    fun k => Real.exp (-(Real.pi * δ) * Fourier.modeSize k) with hf_def
  have hf : Summable f := hS.indicator _
  have hpt : ∀ k ∈ s.filter (· ≠ 0), Fourier.modeSize k ^ (2 * τ) *
      Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) ≤ B * f k := by
    intro k hk
    have hk0 : k ≠ 0 := (Finset.mem_filter.mp hk).2
    rw [hf_def, Set.indicator_of_mem (show k ∈ {k : Fin n → ℤ | k ≠ 0} from hk0)]
    have h := Fourier.rpow_mul_exp_neg_le (x := Fourier.modeSize k) (τ := 2 * τ) (δ := Real.pi * δ)
      (Fourier.modeSize_nonneg k) (by linarith) hx
    have hsplit : Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) =
        Real.exp (-(Real.pi * δ) * Fourier.modeSize k) *
          Real.exp (-(Real.pi * δ) * Fourier.modeSize k) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  have hnn : ∀ k, 0 ≤ f k := fun k =>
    Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
  have htail : ∑' k, f k ≤ (8 * n / (Real.pi * δ)) ^ n := by
    rw [hf_def, ← tsum_subtype]
    exact Fourier.tsum_exp_neg_modeSize_ne_zero_le n hx
  calc _ ≤ ∑ k ∈ s.filter (· ≠ 0), B * f k := Finset.sum_le_sum hpt
    _ ≤ ∑ k ∈ s, B * f k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun k _ _ => mul_nonneg hB0 (hnn k)
    _ = B * ∑ k ∈ s, f k := by rw [Finset.mul_sum]
    _ ≤ B * ∑' k, f k := mul_le_mul_of_nonneg_left (hf.sum_le_tsum _ fun k _ => hnn k) hB0
    _ ≤ B * (8 * n / (Real.pi * δ)) ^ n := mul_le_mul_of_nonneg_left htail hB0

/-- The lattice bound in the `δ^{-(2τ+n)}` form: with `D = δ^{τ+n/2}`,
`(2τ/(eπδ))^{2τ} (8n/(πδ))ⁿ = (2τ/(eπ))^{2τ} (8n/π)ⁿ / D²`. -/
theorem lattice_bound_eq {τ δ : ℝ} (hτ : 0 ≤ τ) (hδ : 0 < δ) :
    (2 * τ / (Real.exp 1 * (Real.pi * δ))) ^ (2 * τ) * (8 * (n : ℝ) / (Real.pi * δ)) ^ n =
      ((2 * τ / (Real.exp 1 * Real.pi)) ^ (2 * τ) * (8 * (n : ℝ) / Real.pi) ^ n) /
        (δ ^ (τ + (n : ℝ) / 2)) ^ 2 := by
  have h1 : 2 * τ / (Real.exp 1 * (Real.pi * δ)) = 2 * τ / (Real.exp 1 * Real.pi) / δ := by
    field_simp
  have h2 : 8 * (n : ℝ) / (Real.pi * δ) = 8 * n / Real.pi / δ := by field_simp
  have hτ' : 0 ≤ 2 * τ / (Real.exp 1 * Real.pi) := by positivity
  have hD : (δ ^ (τ + (n : ℝ) / 2)) ^ 2 = δ ^ (2 * τ) * δ ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le, ← Real.rpow_natCast δ n,
      ← Real.rpow_add hδ]
    congr 1
    push_cast
    ring
  rw [h1, h2, Real.div_rpow hτ' hδ.le, div_pow, hD]
  have hδτ : δ ^ (2 * τ) ≠ 0 := (Real.rpow_pos_of_pos hδ _).ne'
  have hδn : δ ^ n ≠ 0 := (pow_pos hδ n).ne'
  field_simp

end KAM

end
