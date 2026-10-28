/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.StepAvg

/-!
# Two-scale KAM step: displacement constants (`stepP:p3:st-disp`)

Conversion of the averaging displacement bounds `α₁ s |ΔI₁| ≤ 3E`, `α₂ s |ΔI₂| ≤ 3E`,
`2π α₂ R |Δθ| ≤ 9E` into the step bounds `3/4 (M̂/M) Ê R`, `3/4 Ê R`, `3/4 Ê s`, using `(3.2)`,
`K s ≥ 6` and `E ≤ Ê R² M̂` (source `P3a`, step `st-disp`). Design package P23-14.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

namespace KamHyp

theorem disp_first (H : KamHyp D sbar p h f) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : alpha₁ p * p.s * x ≤ 3 * p.E) :
    x ≤ 3 / 4 * (p.Mhat / p.M) * eHat p * rhoHat p := by
  have hR := H.R_pos
  have hM := H.positive.2.2.2.2.1
  have hMh := H.positive.2.2.2.2.2.1
  have hs := H.positive.2.1
  have hK := H.K_mul_s
  have hα := H.alpha₁_ge
  have hEh := H.E_le_Mhat
  have h0 := H.eHat_nonneg
  have h1 : 12 * p.M * rhoHat p ≤ alpha₁ p * p.s := by
    have : 2 * p.M * rhoHat p * (cutoff p * p.s) ≤ alpha₁ p * p.s := by
      nlinarith [mul_pos hs hR]
    nlinarith [mul_pos hM hR]
  have h2 : 12 * p.M * rhoHat p * x ≤ 3 * p.E :=
    (mul_le_mul_of_nonneg_right h1 hx0).trans hx
  have e : 3 / 4 * (p.Mhat / p.M) * eHat p * rhoHat p =
      3 * p.Mhat * eHat p * rhoHat p / (4 * p.M) := by field_simp
  rw [e, le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg h0 hR.le, mul_pos hR hM]

theorem disp_last (H : KamHyp D sbar p h f) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : alpha₂ p * p.s * x ≤ 3 * p.E) :
    x ≤ 3 / 4 * eHat p * rhoHat p := by
  have hR := H.R_pos
  have hMh := H.positive.2.2.2.2.2.1
  have hs := H.positive.2.1
  have hK := H.K_mul_s
  have hα := H.alpha₂_ge
  have hEh := H.E_le_Mhat
  have h0 := H.eHat_nonneg
  have h1 : 12 * p.Mhat * rhoHat p ≤ alpha₂ p * p.s := by
    have : 2 * p.Mhat * rhoHat p * (cutoff p * p.s) ≤ alpha₂ p * p.s := by
      nlinarith [mul_pos hs hR]
    nlinarith [mul_pos hMh hR]
  have h2 : 12 * p.Mhat * rhoHat p * x ≤ 3 * p.E :=
    (mul_le_mul_of_nonneg_right h1 hx0).trans hx
  have h3 : 12 * p.Mhat * rhoHat p * x ≤ 3 * (eHat p * rhoHat p ^ 2 * p.Mhat) := by linarith
  have h4 : 0 < p.Mhat * rhoHat p := mul_pos hMh hR
  nlinarith [mul_nonneg h0 hR.le]

theorem disp_theta (H : KamHyp D sbar p h f) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : 2 * π * alpha₂ p * rhoHat p * x ≤ 9 * p.E) :
    2 * π * x ≤ 3 / 4 * eHat p * p.s := by
  have hR := H.R_pos
  have hMh := H.positive.2.2.2.2.2.1
  have hs := H.positive.2.1
  have hK := H.K_mul_s
  have hα := H.alpha₂_ge
  have hEh := H.E_le_Mhat
  have h0 := H.eHat_nonneg
  have hKp := H.K_pos
  have hπ := Real.pi_pos
  -- `2 π α₂ R x ≥ 4 π Mhat K R² x`
  have h1 : 4 * π * p.Mhat * cutoff p * rhoHat p ^ 2 * x ≤ 9 * p.E := by
    have : 2 * π * (2 * p.Mhat * cutoff p * rhoHat p) * rhoHat p * x ≤
        2 * π * alpha₂ p * rhoHat p * x := by gcongr
    nlinarith
  have h2 : 4 * π * p.Mhat * cutoff p * rhoHat p ^ 2 * x ≤
      9 * (eHat p * rhoHat p ^ 2 * p.Mhat) := by linarith
  have h3 : 0 < p.Mhat * rhoHat p ^ 2 := by positivity
  have h4 : 4 * π * cutoff p * x ≤ 9 * eHat p := by
    have : (4 * π * cutoff p * x - 9 * eHat p) * (p.Mhat * rhoHat p ^ 2) ≤ 0 := by nlinarith
    by_contra hc
    rw [not_le] at hc
    nlinarith [mul_pos (sub_pos.2 hc) h3]
  -- `K s ≥ 6`
  have h5 : 2 * π * x * 6 ≤ 2 * π * x * (cutoff p * p.s) :=
    mul_le_mul_of_nonneg_left hK (by positivity)
  nlinarith [mul_nonneg h0 hs.le, mul_nonneg (mul_nonneg hπ.le hx0) hs.le]

end KamHyp

end KAM.Planetary

end
