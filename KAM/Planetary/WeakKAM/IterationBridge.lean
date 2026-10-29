/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.Budgets
public import KAM.Planetary.MaximalStep.StepRealFlow
public import KAM.Planetary.MaximalStep.StepParameter

/-! # P11B iteration: bridges to the P11A canonical step

Domain, `Λ` and sup-norm bridges between the selection schedule and the exact P11A objects.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

theorem selectionDomain_eq_domain_def (r s : ℝ) (B : Set (SelectionC n)) :
    selectionDomain r s B = domain_def n r s B := by
  ext ⟨⟨θ, η⟩, b⟩
  rw [p11_mem_domain_def]
  rfl

theorem coth_eq_exp (x : ℝ) :
    KAM.Weighted.coth x = (Real.exp (2 * x) + 1) / (Real.exp (2 * x) - 1) := by
  unfold KAM.Weighted.coth
  rw [Real.cosh_eq, Real.sinh_eq]
  have h2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
  have hx := Real.exp_pos x
  by_cases h0 : Real.exp x * Real.exp x - 1 = 0
  · have : Real.exp x - (Real.exp x)⁻¹ = 0 := by
      field_simp
      linarith
    rw [h2, h0, h3, this]
    simp
  · have h1 : Real.exp x - (Real.exp x)⁻¹ ≠ 0 := by
      intro h
      apply h0
      field_simp at h
      linarith
    rw [h2, h3, div_div_div_cancel_right₀ (two_ne_zero)]
    field_simp

theorem selectionΛ_eq_p11Lambda (n : ℕ) (δ : ℝ) :
    selectionΛ n δ = p11Lambda n δ := by
  unfold selectionΛ p11Lambda
  rw [coth_eq_exp]
  ring_nf

end KAM.Planetary

end
