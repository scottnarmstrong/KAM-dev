/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.SmallDiv.Defs
public import KAM.Strip.CohomologicalSumBound
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The solution bound with the small-divisor sum `S(ω, b)` (full-strip Bessel)

* `sum_sq_torusCoeff_exp_le_full` (blueprint `bp:p2s2sd:bessel`): the corner Bessel inequality at
  the full strip radius `r`, by the monotone limit `r' ↑ r` of `KAM.sum_sq_torusCoeff_exp_le`.
* `sdSum_eq_smallDivisorSum`: `S(ω, b) = KAM.smallDivisorSum ω (2 b)`.
* `norm_cohSolution_sdSum_le` (`bp:p2s2sd:cs`, step `cs-one`): for `0 < δ ≤ r` and a point `θ` with
  `|Im θ_j| ≤ r - δ`, `‖𝓡 g (θ)‖ ≤ (2π)⁻¹ 2^{n/2} S(ω, δ)^{1/2} A`. The closed strip includes the
  real points of the bite `δ = r`.
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Sharp2

open KAM KAM.Torus

variable {n : ℕ}

/-- **Bessel on the full strip.** -/
theorem sum_sq_torusCoeff_exp_le_full {r A : ℝ} (hr : 0 < r)
    {g : (Fin n → ℂ) → ℂ} (hg : DifferentiableOn ℂ g (complexStrip n r))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n r → g (z + Pi.single i 1) = g z)
    (hA : ∀ z ∈ complexStrip n r, ‖g z‖ ≤ A) (s : Finset (Fin n → ℤ)) :
    ∑ k ∈ s, ‖torusCoeff (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) k‖ ^ 2 *
        Real.exp (4 * Real.pi * r * Fourier.modeSize k) ≤ 2 ^ n * A ^ 2 := by
  set F : ℝ → ℝ := fun t => ∑ k ∈ s,
    ‖torusCoeff (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) k‖ ^ 2 *
      Real.exp (4 * Real.pi * t * Fourier.modeSize k) with hF
  have hcont : Continuous F := by
    refine continuous_finsetSum _ fun k _ => ?_
    fun_prop
  have hlim : Tendsto F (𝓝[<] r) (𝓝 (F r)) := (hcont.tendsto r).mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  have : Set.Ioo 0 r ∈ 𝓝[<] r := Ioo_mem_nhdsLT hr
  filter_upwards [this] with t ht
  exact sum_sq_torusCoeff_exp_le ht.1.le ht.2 hg hp hA s

theorem sdSum_term_eq (ω : Fin n → ℝ) (b : ℝ) (k : Fin n → ℤ) :
    (if k = 0 then 0 else
      (|∑ i, (k i : ℝ) * ω i|)⁻¹ ^ 2 * Real.exp (-4 * Real.pi * b * ∑ i, |(k i : ℝ)|)) =
      smallDivisorTerm ω (2 * b) k := by
  unfold smallDivisorTerm
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ite_false, Diophantine.frequencyDot, Fourier.modeSize]
    rw [inv_pow, sq_abs]
    congr 2
    ring

theorem sdSum_eq_smallDivisorSum (ω : Fin n → ℝ) (b : ℝ) :
    sdSum ω b = smallDivisorSum ω (2 * b) := by
  unfold sdSum smallDivisorSum
  exact tsum_congr fun k => sdSum_term_eq ω b k

theorem norm_character_le_closed {ρ : ℝ} (k : Fin n → ℤ) {θ : Fin n → ℂ}
    (hθ : ∀ j, |(θ j).im| ≤ ρ) :
    ‖character k θ‖ ≤ Real.exp (2 * Real.pi * ρ * Fourier.modeSize k) := by
  rw [norm_character]
  apply Real.exp_le_exp.mpr
  have h1 : ∀ j, -((k j : ℝ) * (θ j).im) ≤ ρ * |(k j : ℝ)| := by
    intro j
    calc -((k j : ℝ) * (θ j).im) ≤ |(k j : ℝ) * (θ j).im| := neg_le_abs _
      _ = |(k j : ℝ)| * |(θ j).im| := abs_mul _ _
      _ ≤ |(k j : ℝ)| * ρ := mul_le_mul_of_nonneg_left (hθ j) (abs_nonneg _)
      _ = ρ * |(k j : ℝ)| := mul_comm _ _
  have h2 : -(∑ j, (k j : ℝ) * (θ j).im) ≤ ρ * Fourier.modeSize k := by
    rw [Fourier.modeSize, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun j _ => h1 j
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 hpi]

/-- **The solution bound by `S(ω, δ)`.** For `0 < δ ≤ r` and `|Im θ_j| ≤ r - δ`:
`‖𝓡 g (θ)‖ ≤ (2π)⁻¹ 2^{n/2} S(ω, δ)^{1/2} A`. -/
theorem norm_cohSolution_sdSum_le {ω : Fin n → ℝ} {γ τ r δ A : ℝ}
    (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδr : δ ≤ r)
    {g : (Fin n → ℂ) → ℂ} (hg : DifferentiableOn ℂ g (complexStrip n r))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n r → g (z + Pi.single i 1) = g z)
    (hA : ∀ z ∈ complexStrip n r, ‖g z‖ ≤ A)
    {θ : Fin n → ℂ} (hθ : ∀ j, |(θ j).im| ≤ r - δ) :
    ‖cohSolution ω g θ‖ ≤
      (2 * Real.pi)⁻¹ * Real.sqrt (2 ^ n) * Real.sqrt (sdSum ω δ) * A := by
  have hr : 0 < r := hδ.trans_le hδr
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA _ (ofReal_mem_complexStrip hr 0))
  set a : (Fin n → ℤ) → ℂ := torusCoeff fun x : Fin n → ℝ => g fun j => (x j : ℂ) with ha_def
  set S : ℝ := sdSum ω δ with hS_def
  have hS0 : 0 ≤ S := by
    rw [hS_def, sdSum_eq_smallDivisorSum]; exact smallDivisorSum_nonneg _ _
  have h2δ : 0 < 2 * δ := by positivity
  have hfd : ∀ k : Fin n → ℤ, k ≠ 0 → 0 < |Diophantine.frequencyDot ω k| := fun k hk =>
    abs_pos.mpr (hω.condition.nonresonant hγ k hk)
  have key : ∀ s : Finset (Fin n → ℤ),
      ∑ k ∈ s, ‖Diophantine.solve ω a k‖ * Real.exp (2 * Real.pi * (r - δ) * Fourier.modeSize k) ≤
        (2 * Real.pi)⁻¹ * (|A| * Real.sqrt (2 ^ n * S)) := by
    intro s
    set x : (Fin n → ℤ) → ℝ := fun k => ‖a k‖ * Real.exp (2 * Real.pi * r * Fourier.modeSize k)
      with hx_def
    set y : (Fin n → ℤ) → ℝ := fun k => |Diophantine.frequencyDot ω k|⁻¹ *
      Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) with hy_def
    have hterm : ∀ k ∈ s, ‖Diophantine.solve ω a k‖ *
        Real.exp (2 * Real.pi * (r - δ) * Fourier.modeSize k) ≤
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
        have : Real.exp (2 * Real.pi * (r - δ) * Fourier.modeSize k) =
            Real.exp (2 * Real.pi * r * Fourier.modeSize k) *
              Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) := by
          rw [← Real.exp_add]
          congr 1
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
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hx2 : ∑ k ∈ s', x k ^ 2 ≤ 2 ^ n * A ^ 2 := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun k _ _ => by positivity) ?_
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
        (sum_sq_torusCoeff_exp_le_full hr hg hp hA s)
      simp only [hx_def, mul_pow]
      rw [← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    have hy2 : ∑ k ∈ s', y k ^ 2 ≤ S := by
      have hle := sum_le_smallDivisorSum hω.condition hγ hτ h2δ s'
      rw [hS_def, sdSum_eq_smallDivisorSum]
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun k hk => ?_)) hle
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
  have hsum : Summable fun k => ‖Diophantine.solve ω a k‖ *
      Real.exp (2 * Real.pi * (r - δ) * Fourier.modeSize k) :=
    summable_of_sum_le (fun k => by positivity) key
  have hw := hsum.tsum_le_of_sum_le key
  unfold cohSolution
  refine (norm_tsum_le_tsum_norm (hsum.of_nonneg_of_le (fun _ => norm_nonneg _) fun k => ?_)).trans ?_
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_character_le_closed k hθ) (norm_nonneg _)
  · refine (Summable.tsum_le_tsum (fun k => ?_) (hsum.of_nonneg_of_le (fun _ => norm_nonneg _)
      fun k => ?_) hsum).trans (hw.trans (le_of_eq ?_))
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_character_le_closed k hθ) (norm_nonneg _)
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_character_le_closed k hθ) (norm_nonneg _)
    · rw [abs_of_nonneg hA0, Real.sqrt_mul (show (0 : ℝ) ≤ 2 ^ n by positivity) S]
      ring

end KAM.Sharp2

end
