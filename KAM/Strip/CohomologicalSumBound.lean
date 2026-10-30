/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.Cohomological
public import KAM.Strip.CohomologicalParsevalBessel
public import KAM.Strip.CohomologicalSumSeries
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The frequency-specific bound for the cohomological solution

For `ω` `(γ, τ)`-Diophantine and `g` holomorphic, `1`-periodic, bounded by `A` on `T_ρ` with zero
average, `‖𝓡 g‖ ≤ (2π)⁻¹ 2^{n/2} S(ω, δ)^{1/2} A` on `T_{ρ-δ}`
(`KAM.norm_cohSolution_sum_le`), for every `0 < δ < ρ`, with `S = KAM.smallDivisorSum`.

The proof is that of `KAM.norm_cohSolution_russmann_le` without the lattice counting: with
`ρ' = ρ - δ/2`, Cauchy–Schwarz splits `∑ |û_k| e^{2π(ρ-δ)|k|₁}` into the corner Bessel factor
`(∑ |ĝ_k|² e^{4πρ'|k|₁})^{1/2} ≤ (2ⁿ A²)^{1/2}` (`KAM.sum_sq_torusCoeff_exp_le`) and
`(2π)⁻¹ (∑_{k≠0} |k·ω|⁻² e^{-2πδ|k|₁})^{1/2} ≤ (2π)⁻¹ S(ω, δ)^{1/2}`. The Diophantine condition is
used only for the summability of `S` and of the solution's coefficients.
-/

public noncomputable section

namespace KAM

variable {n : ℕ}

/-- **The frequency-specific cohomological estimate** (scalar):
`‖𝓡 g‖ ≤ (2π)⁻¹ 2^{n/2} S(ω, δ)^{1/2} A`. -/
theorem norm_cohSolution_sum_le {ω : Fin n → ℝ} {γ τ ρ δ A : ℝ}
    (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδρ : δ < ρ)
    {g : (Fin n → ℂ) → ℂ} (hg : DifferentiableOn ℂ g (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z)
    (hA : ∀ z ∈ complexStrip n ρ, ‖g z‖ ≤ A)
    (h0 : torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (ρ - δ)) :
    ‖cohSolution ω g θ‖ ≤
      (2 * Real.pi)⁻¹ * Real.sqrt (2 ^ n) * Real.sqrt (smallDivisorSum ω δ) * A := by
  have hρ : 0 < ρ := hδ.trans hδρ
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA _ (ofReal_mem_complexStrip hρ 0))
  obtain ⟨hsum, -⟩ := summableWeighted_solve_torusCoeff hω hγ hτ hδ hδρ hg hp hA h0
  set a : (Fin n → ℤ) → ℂ := torusCoeff fun x : Fin n → ℝ => g fun j => (x j : ℂ) with ha_def
  set S : ℝ := smallDivisorSum ω δ with hS_def
  have hS0 : 0 ≤ S := smallDivisorSum_nonneg ω δ
  set ρ' : ℝ := ρ - δ / 2 with hρ'_def
  have hC : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have hfd : ∀ k : Fin n → ℤ, k ≠ 0 → 0 < |Diophantine.frequencyDot ω k| := fun k hk =>
    abs_pos.mpr (hω.condition.nonresonant hγ k hk)
  have key : ∀ s : Finset (Fin n → ℤ),
      ∑ k ∈ s, ‖Diophantine.solve ω a k‖ * Real.exp (2 * Real.pi * (ρ - δ) * Fourier.modeSize k) ≤
        (2 * Real.pi)⁻¹ * (|A| * Real.sqrt (2 ^ n * S)) := by
    intro s
    set x : (Fin n → ℤ) → ℝ := fun k => ‖a k‖ * Real.exp (2 * Real.pi * ρ' * Fourier.modeSize k)
      with hx_def
    set y : (Fin n → ℤ) → ℝ := fun k => |Diophantine.frequencyDot ω k|⁻¹ *
      Real.exp (-(Real.pi * δ) * Fourier.modeSize k) with hy_def
    have hterm : ∀ k ∈ s, ‖Diophantine.solve ω a k‖ *
        Real.exp (2 * Real.pi * (ρ - δ) * Fourier.modeSize k) ≤
        if k ≠ 0 then (2 * Real.pi)⁻¹ * (x k * y k) else 0 := by
      intro k _
      by_cases hk : k = 0
      · subst hk
        simp
      · simp only [ne_eq, hk, not_false_eq_true, ite_true]
        have hpos := hfd k hk
        have hn : ‖Diophantine.solve ω a k‖ =
            ‖a k‖ / (2 * Real.pi * |Diophantine.frequencyDot ω k|) := by
          simp only [Diophantine.solve, hk, ↓reduceIte, norm_div, Diophantine.norm_flowMultiplier]
        have : Real.exp (2 * Real.pi * (ρ - δ) * Fourier.modeSize k) =
            Real.exp (2 * Real.pi * ρ' * Fourier.modeSize k) *
              Real.exp (-(Real.pi * δ) * Fourier.modeSize k) := by
          rw [← Real.exp_add]
          congr 1
          rw [hρ'_def]
          ring
        rw [hn, this]
        simp only [hx_def, hy_def]
        refine le_of_eq ?_
        field_simp
    set s' := s.filter (· ≠ 0) with hs'
    have hsum_if : ∑ k ∈ s, (if k ≠ 0 then (2 * Real.pi)⁻¹ * (x k * y k) else 0) =
        ∑ k ∈ s', (2 * Real.pi)⁻¹ * (x k * y k) := by
      rw [hs', Finset.sum_filter]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [hsum_if, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hC
    have hx2 : ∑ k ∈ s', x k ^ 2 ≤ 2 ^ n * A ^ 2 := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun k _ _ => by positivity) ?_
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
        (sum_sq_torusCoeff_exp_le (ρ' := ρ') (by rw [hρ'_def]; linarith)
          (by rw [hρ'_def]; linarith) hg hp hA s)
      simp only [hx_def, mul_pow]
      rw [← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    have hy2 : ∑ k ∈ s', y k ^ 2 ≤ S := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun k hk => ?_))
        (sum_le_smallDivisorSum hω.condition hγ hτ hδ s')
      have hk0 : k ≠ 0 := (Finset.mem_filter.mp hk).2
      rw [smallDivisorTerm_of_ne hk0]
      simp only [hy_def, mul_pow]
      rw [← Real.exp_nat_mul, inv_pow, sq_abs]
      congr 2
      push_cast
      ring
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s' x y
    have hprod : (∑ k ∈ s', x k * y k) ^ 2 ≤ 2 ^ n * A ^ 2 * S :=
      hcs.trans (mul_le_mul hx2 hy2 (Finset.sum_nonneg fun _ _ => by positivity) (by positivity))
    have habs := Real.abs_le_sqrt hprod
    refine (le_abs_self _).trans (habs.trans (le_of_eq ?_))
    rw [show 2 ^ n * A ^ 2 * S = A ^ 2 * (2 ^ n * S) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  have hsum' : Summable fun k => ‖Diophantine.solve ω a k‖ *
      Real.exp (2 * Real.pi * (ρ - δ) * Fourier.modeSize k) := hsum
  have hw : Fourier.weightedNorm (2 * Real.pi * (ρ - δ)) (Diophantine.solve ω a) ≤
      (2 * Real.pi)⁻¹ * (|A| * Real.sqrt (2 ^ n * S)) :=
    hsum'.tsum_le_of_sum_le key
  refine (norm_fourierSum_le hsum hθ).trans (hw.trans (le_of_eq ?_))
  rw [abs_of_nonneg hA0, Real.sqrt_mul (show (0 : ℝ) ≤ 2 ^ n by positivity) S]
  ring

end KAM

end
