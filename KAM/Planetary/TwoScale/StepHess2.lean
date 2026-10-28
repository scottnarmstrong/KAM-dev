/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.StepHess

/-!
# Two-scale KAM step: Hessian bounds of the new Hamiltonian (`stepP:p3:st-U`)

`‖D²(h+g)‖ ≤ 2M`, last rows `≤ 2M̂`, and the inverse with `‖·⁻¹‖ ≤ 2M̄`, first rows `≤ 2M̄₁`,
last rows `≤ 2M̄₂`, on the quarter-radius neighbourhood. Design package P23-14.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

namespace KamHyp

/-- The Hessian bound `β = 80 E / R²` of `g`. -/
theorem beta_facts (H : KamHyp D sbar p h f) :
    80 * p.E / rhoHat p ^ 2 ≤ p.M / 100 ∧ 80 * p.E / rhoHat p ^ 2 ≤ p.Mhat / 100 ∧
    p.Mbar * (80 * p.E / rhoHat p ^ 2) ≤ 1 / 100 := by
  have hR := H.R_pos
  have hs := H.eHat_small
  have h0 := H.eHat_nonneg
  have hR2 : 0 < rhoHat p ^ 2 := by positivity
  have hM := H.positive.2.2.2.2.1
  have hMh := H.positive.2.2.2.2.2.1
  have hMb := H.positive.2.2.2.2.2.2.1
  have hL := H.L_pos
  have hLb : p.Mbar ≤ p.L := ((le_max_left _ _)).trans H.L_bound
  have e1 := H.E_le_M
  have e2 := H.E_le_Mhat
  have hE : eHat p * rhoHat p ^ 2 = p.E * p.L := by
    rw [KamHyp.eHat_eq]; field_simp
  have h8 : 8000 * eHat p ≤ 1 := by norm_num at hs; linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ hR2]
    nlinarith [mul_nonneg (mul_pos hM hR2).le (sub_nonneg.2 h8)]
  · rw [div_le_iff₀ hR2]
    nlinarith [mul_nonneg (mul_pos hMh hR2).le (sub_nonneg.2 h8)]
  · have : p.Mbar * (80 * p.E / rhoHat p ^ 2) = 80 * eHat p * (p.Mbar / p.L) := by
      rw [KamHyp.eHat_eq]; field_simp
    rw [this]
    have h1 : p.Mbar / p.L ≤ 1 := (div_le_one hL).2 hLb
    have h2 : 0 ≤ p.Mbar / p.L := by positivity
    nlinarith

end KamHyp

end KAM.Planetary

end
