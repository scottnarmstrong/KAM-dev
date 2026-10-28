/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Defs.IsDiophantine

/-!
# Diophantine conversions (blueprint-P Part 1, `two-scale`, `dio-basic`, `dio-sources`)

The two-scale set `𝒟_{γ₁,γ₂,τ}`, monotonicity, comparison with other norms, scaling, and the
conversions from the CP09 and CP10 hypotheses to the frozen `IsDiophantine`.
-/

@[expose] public noncomputable section

open Set Real

namespace KAM.Planetary

open KAM

section Diophantine

/-- `bpP:p1:two-scale`: `𝒟_{γ₁,γ₂,τ}` on `ℝ^{n₁} × ℝ^{n₂}` (first `n₁` coordinates via
`Fin.castAdd`), with the frozen `γ / |k|₁^τ` form of the bound. -/
def twoScaleDiophantine (n₁ n₂ : ℕ) (γ₁ γ₂ τ : ℝ) : Set (Fin (n₁ + n₂) → ℝ) :=
  {ω | (∀ k : Fin (n₁ + n₂) → ℤ, (fun i : Fin n₁ => k (Fin.castAdd n₂ i)) ≠ 0 →
        γ₁ / (∑ i, |(k i : ℝ)|) ^ τ ≤ |∑ i, (k i : ℝ) * ω i|) ∧
    (∀ k : Fin (n₁ + n₂) → ℤ, k ≠ 0 → (fun i : Fin n₁ => k (Fin.castAdd n₂ i)) = 0 →
        γ₂ / (∑ i, |(k i : ℝ)|) ^ τ ≤ |∑ i, (k i : ℝ) * ω i|)}

variable {d : ℕ}

/-- The `ℓ¹` norm of a nonzero integer vector is at least one. -/
theorem one_le_l1_of_ne_zero {k : Fin d → ℤ} (hk : k ≠ 0) : 1 ≤ ∑ i, |(k i : ℝ)| := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hk
  have h1 : (1 : ℝ) ≤ |(k j : ℝ)| := by
    have : (1 : ℤ) ≤ |k j| := Int.one_le_abs hj
    exact_mod_cast this
  exact h1.trans (Finset.single_le_sum (f := fun i => |(k i : ℝ)|)
    (fun i _ => abs_nonneg _) (Finset.mem_univ j))

/-- `bpP:p1:dio-basic` (a) monotonicity. -/
theorem IsDiophantine.mono {γ τ γ' τ' : ℝ} {ω : Fin d → ℝ} (h : IsDiophantine γ τ ω)
    (hγ : γ' ≤ γ) (hτ : τ ≤ τ') : IsDiophantine γ' τ' ω := by
  intro k hk
  have hN := one_le_l1_of_ne_zero hk
  have hNp : (0 : ℝ) < ∑ i, |(k i : ℝ)| := lt_of_lt_of_le one_pos hN
  rcases le_or_gt γ' 0 with hg | hg
  · exact (div_nonpos_of_nonpos_of_nonneg hg (rpow_nonneg hNp.le _)).trans (abs_nonneg _)
  · calc γ' / (∑ i, |(k i : ℝ)|) ^ τ'
        ≤ γ / (∑ i, |(k i : ℝ)|) ^ τ' :=
          div_le_div_of_nonneg_right hγ (rpow_nonneg hNp.le _)
      _ ≤ γ / (∑ i, |(k i : ℝ)|) ^ τ :=
          div_le_div_of_nonneg_left (hg.le.trans hγ) (rpow_pos_of_pos hNp _)
            (rpow_le_rpow_of_exponent_le hN hτ)
      _ ≤ _ := h k hk

/-- `bpP:p1:dio-basic` (b) other norms `0 < ν k ≤ |k|₁`. -/
theorem isDiophantine_of_le_l1 {γ τ : ℝ} (hτ : 0 < τ) {ω : Fin d → ℝ} {ν : (Fin d → ℤ) → ℝ}
    (hν : ∀ k, k ≠ 0 → 0 < ν k ∧ ν k ≤ ∑ i, |(k i : ℝ)|)
    (h : ∀ k : Fin d → ℤ, k ≠ 0 → γ / ν k ^ τ ≤ |∑ i, (k i : ℝ) * ω i|) :
    IsDiophantine γ τ ω := by
  intro k hk
  obtain ⟨hp, hle⟩ := hν k hk
  have hNp : (0 : ℝ) < ∑ i, |(k i : ℝ)| := hp.trans_le hle
  rcases le_or_gt γ 0 with hg | hg
  · exact (div_nonpos_of_nonpos_of_nonneg hg (rpow_nonneg hNp.le _)).trans (abs_nonneg _)
  · exact (div_le_div_of_nonneg_left hg.le (rpow_pos_of_pos hp _)
      (rpow_le_rpow hp.le hle hτ.le)).trans (h k hk)

/-- Scaling of the Diophantine bound, termwise. -/
theorem dio_smul_bound (γ τ N s : ℝ) (hs : 0 < s) (k : Fin d → ℤ) (ω : Fin d → ℝ) :
    ((γ / s) / N ^ τ ≤ |∑ i, (k i : ℝ) * (s⁻¹ • ω) i|) ↔ γ / N ^ τ ≤ |∑ i, (k i : ℝ) * ω i| := by
  have h1 : ∑ i, (k i : ℝ) * (s⁻¹ • ω) i = s⁻¹ * ∑ i, (k i : ℝ) * ω i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have h2 : (γ / s) / N ^ τ = s⁻¹ * (γ / N ^ τ) := by
    rw [div_div, div_eq_mul_inv, div_eq_mul_inv]; field_simp
  rw [h1, h2, abs_mul, abs_of_pos (inv_pos.mpr hs)]
  exact mul_le_mul_iff_right₀ (inv_pos.mpr hs)

/-- `bpP:p1:dio-basic` (c) scaling. -/
theorem isDiophantine_smul_iff {γ τ s : ℝ} (hs : 0 < s) (ω : Fin d → ℝ) :
    IsDiophantine γ τ ω ↔ IsDiophantine (γ / s) τ (s⁻¹ • ω) := by
  unfold IsDiophantine
  refine forall_congr' fun k => forall_congr' fun _ => ?_
  exact (dio_smul_bound γ τ _ s hs k ω).symm

/-- `bpP:p1:dio-basic` (d) two scales. -/
theorem isDiophantine_min_of_mem_twoScale {n₁ n₂ : ℕ} {γ₁ γ₂ τ : ℝ} {ω : Fin (n₁ + n₂) → ℝ}
    (h : ω ∈ twoScaleDiophantine n₁ n₂ γ₁ γ₂ τ) : IsDiophantine (min γ₁ γ₂) τ ω := by
  intro k hk
  have hN := one_le_l1_of_ne_zero hk
  have hNp : (0 : ℝ) < ∑ i, |(k i : ℝ)| := lt_of_lt_of_le one_pos hN
  have hpos : 0 ≤ (∑ i, |(k i : ℝ)|) ^ τ := rpow_nonneg hNp.le _
  by_cases h0 : (fun i : Fin n₁ => k (Fin.castAdd n₂ i)) = 0
  · exact (div_le_div_of_nonneg_right (min_le_right _ _) hpos).trans (h.2 k hk h0)
  · exact (div_le_div_of_nonneg_right (min_le_left _ _) hpos).trans (h.1 k h0)

/-- `bpP:p1:dio-sources` (a) scaling of `𝒟`. -/
theorem smul_mem_twoScale {n₁ n₂ : ℕ} {γ₁ γ₂ τ s : ℝ} (hs : 0 < s) {ω : Fin (n₁ + n₂) → ℝ}
    (h : ω ∈ twoScaleDiophantine n₁ n₂ γ₁ γ₂ τ) :
    s⁻¹ • ω ∈ twoScaleDiophantine n₁ n₂ (γ₁ / s) (γ₂ / s) τ :=
  ⟨fun k hk => (dio_smul_bound γ₁ τ _ s hs k ω).mpr (h.1 k hk),
    fun k hk h0 => (dio_smul_bound γ₂ τ _ s hs k ω).mpr (h.2 k hk h0)⟩

/-- `bpP:p1:dio-sources` (a) CP10: the clause of `IsCylinderKolmogorovSet`. -/
theorem cp10_isDiophantine {n₁ n₂ : ℕ} {γ₁ γ₂ τ : ℝ} (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (hτ : ((n₁ + n₂ : ℕ) : ℝ) < τ) {ω : Fin (n₁ + n₂) → ℝ}
    (h : ω ∈ twoScaleDiophantine n₁ n₂ γ₁ γ₂ τ) :
    IsDiophantine (min γ₁ γ₂) τ ω ∧
      ∃ γ τ' : ℝ, 0 < γ ∧ ((n₁ + n₂ : ℕ) : ℝ) < τ' ∧ IsDiophantine γ τ' ω :=
  ⟨isDiophantine_min_of_mem_twoScale h,
    min γ₁ γ₂, τ, lt_min hγ₁ hγ₂, hτ, isDiophantine_min_of_mem_twoScale h⟩

/-- `bpP:p1:dio-sources` (b) CP09 (6) with the Euclidean norm `√(∑ kᵢ²)` (no `EuclideanSpace`). -/
theorem cp09_isDiophantine {γ τ : ℝ} (hγ : 0 < γ) {μ : ℕ} (hμ : 1 ≤ μ)
    (hτ : (d : ℝ) * μ < τ) {ω : Fin d → ℝ}
    (h : ∀ k : Fin d → ℤ, k ≠ 0 →
      γ / (√(∑ i, (k i : ℝ) ^ 2)) ^ τ ≤ |∑ i, (k i : ℝ) * ω i|) :
    IsDiophantine γ τ ω ∧ IsDiophantine (γ / (2 * π)) τ ((2 * π)⁻¹ • ω) ∧ (d : ℝ) - 1 < τ := by
  have hdμ : (d : ℝ) ≤ d * μ := by
    have : (1 : ℝ) ≤ μ := by exact_mod_cast hμ
    nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hτ0 : 0 < τ := lt_of_le_of_lt (by positivity) hτ
  have hD : IsDiophantine γ τ ω := by
    refine isDiophantine_of_le_l1 hτ0 (ν := fun k => √(∑ i, (k i : ℝ) ^ 2)) ?_ h
    intro k hk
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hk
    have hkj : (0 : ℝ) < (k j : ℝ) ^ 2 := by
      have : (k j : ℝ) ≠ 0 := by exact_mod_cast hj
      positivity
    have hS : 0 < ∑ i, (k i : ℝ) ^ 2 :=
      lt_of_lt_of_le hkj (Finset.single_le_sum (f := fun i => (k i : ℝ) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j))
    refine ⟨Real.sqrt_pos.mpr hS,
      Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg fun i _ => abs_nonneg _, ?_⟩⟩
    calc ∑ i, (k i : ℝ) ^ 2 = ∑ i, |(k i : ℝ)| ^ 2 := by simp only [sq_abs]
      _ ≤ (∑ i, |(k i : ℝ)|) ^ 2 :=
          Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg _
  exact ⟨hD, (isDiophantine_smul_iff (by positivity) ω).mp hD, by linarith⟩

end Diophantine

end KAM.Planetary

end
