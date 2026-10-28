/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.StepFreq

/-!
# Two-scale KAM step: constants facts and nonresonance (`stepP:p3:st-nonres`)

Consequences of `KamHyp` on the constants (`rhoHat`, `cutoff`, `eHat`, `L`), and the two-scale
nonresonance estimate on the complex `rhoHat`-neighbourhood of `D` with the divisors
`α₁ = (2/3) γ₁ K^(-τ)`, `α₂ = (2/3) γ₂ K^(-τ)`, from the mean value inequality on the Hessian
bounds. Design package P23-14.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

namespace KamHyp

theorem γ₁_pos (H : KamHyp D sbar p h f) : 0 < p.γ₁ := lt_of_lt_of_le H.positive.1 H.gamma_order

theorem τ_pos (H : KamHyp D sbar p h f) : 0 < p.τ := by
  have h1 := H.τ_gt
  have h2 : (0 : ℝ) ≤ ((a + b : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

theorem L_pos (H : KamHyp D sbar p h f) : 0 < p.L := by
  have h1 := H.L_bound
  have : p.Mbar ≤ initialL p.M p.Mhat p.Mbar := le_max_left _ _
  linarith [H.positive.2.2.2.2.2.2.1]

theorem K_pos (H : KamHyp D sbar p h f) : 0 < cutoff p := cutoff_pos H.positive.2.1

theorem R_pos (H : KamHyp D sbar p h f) : 0 < rhoHat p :=
  rhoHat_pos H.positive.2.1 H.γ₁_pos H.positive.1 H.positive.2.2.2.2.1
    H.positive.2.2.2.2.2.1 H.positive.2.2.1

theorem K_mul_s (H : KamHyp D sbar p h f) : 6 ≤ cutoff p * p.s := by
  have hs := H.positive.2.1
  unfold cutoff constants
  have h1 : (1 : ℝ) ≤ max 1 (log (1 / (p.E * p.M ^ 2 * p.L / p.γ₁ ^ 2))) := le_max_left _ _
  have : 6 / p.s ≤ 6 / p.s * max 1 (log (1 / (p.E * p.M ^ 2 * p.L / p.γ₁ ^ 2))) :=
    le_mul_of_one_le_right (by positivity) h1
  calc (6 : ℝ) = 6 / p.s * p.s := by field_simp
    _ ≤ _ := by gcongr

theorem R_le_ρ (_H : KamHyp D sbar p h f) : rhoHat p ≤ p.ρ := by
  unfold rhoHat constants; exact min_le_right _ _

theorem R_le_γ₁ (H : KamHyp D sbar p h f) :
    3 * p.M * cutoff p ^ (p.τ + 1) * rhoHat p ≤ p.γ₁ := by
  have hK := H.K_pos
  have hM := H.positive.2.2.2.2.1
  have hd : 0 < 3 * p.M * cutoff p ^ (p.τ + 1) := by positivity
  have : rhoHat p ≤ p.γ₁ / (3 * p.M * cutoff p ^ (p.τ + 1)) := by
    unfold rhoHat constants
    exact (min_le_left _ _).trans ((min_le_left _ _))
  rw [le_div_iff₀ hd] at this; linarith

theorem R_le_γ₂ (H : KamHyp D sbar p h f) :
    3 * p.Mhat * cutoff p ^ (p.τ + 1) * rhoHat p ≤ p.γ₂ := by
  have hK := H.K_pos
  have hM := H.positive.2.2.2.2.2.1
  have hd : 0 < 3 * p.Mhat * cutoff p ^ (p.τ + 1) := by positivity
  have : rhoHat p ≤ p.γ₂ / (3 * p.Mhat * cutoff p ^ (p.τ + 1)) := by
    unfold rhoHat constants
    exact (min_le_left _ _).trans ((min_le_right _ _))
  rw [le_div_iff₀ hd] at this; linarith

theorem eHat_eq (p : ScaleData) : eHat p = p.E * p.L / rhoHat p ^ 2 := rfl

theorem eHat_nonneg (H : KamHyp D sbar p h f) : 0 ≤ eHat p := by
  rw [eHat_eq]
  have := H.positive.2.2.2.1; have := H.L_pos
  positivity

/-- `E = Ê R² / L`; with `L ≥ M̂⁻¹` this gives `E ≤ Ê R² M̂` (and likewise for `M`). -/
theorem E_le_Mhat (H : KamHyp D sbar p h f) :
    p.E ≤ eHat p * rhoHat p ^ 2 * p.Mhat := by
  have hL := H.L_pos; have hR := H.R_pos
  have hMh := H.positive.2.2.2.2.2.1
  have h1 : p.Mhat⁻¹ ≤ p.L := (le_max_right _ _).trans' (le_max_right _ _) |>.trans H.L_bound
  have h2 : p.Mhat * p.L ≥ 1 := by
    have := mul_le_mul_of_nonneg_left h1 hMh.le
    rwa [mul_inv_cancel₀ hMh.ne'] at this
  have hE : eHat p * rhoHat p ^ 2 = p.E * p.L := by
    rw [eHat_eq]; field_simp
  have h3 : eHat p * p.Mhat * rhoHat p ^ 2 = (p.E * p.L) * p.Mhat := by rw [← hE]; ring
  nlinarith [H.positive.2.2.2.1]

theorem E_le_M (H : KamHyp D sbar p h f) : p.E ≤ eHat p * rhoHat p ^ 2 * p.M := by
  have hL := H.L_pos; have hR := H.R_pos
  have hMh := H.positive.2.2.2.2.1
  have h1 : p.M⁻¹ ≤ p.L := ((le_max_left _ _).trans (le_max_right _ _)).trans H.L_bound
  have h2 : p.M * p.L ≥ 1 := by
    have := mul_le_mul_of_nonneg_left h1 hMh.le
    rwa [mul_inv_cancel₀ hMh.ne'] at this
  have hE : eHat p * rhoHat p ^ 2 = p.E * p.L := by
    rw [eHat_eq]; field_simp
  have h3 : eHat p * p.M * rhoHat p ^ 2 = (p.E * p.L) * p.M := by rw [← hE]; ring
  nlinarith [H.positive.2.2.2.1]

theorem eHat_small (H : KamHyp D sbar p h f) : 2 ^ 14 * eHat p < 1 := by
  have h1 := H.small
  have h2 : 2 ^ 13 * ((a + b : ℕ) : ℝ) ≤ kamConstant (a + b) p.τ := le_max_left _ _
  have h3 : (2 : ℝ) ≤ ((a + b : ℕ) : ℝ) := by
    have := H.a_pos; have := H.b_pos
    exact_mod_cast (by omega : 2 ≤ a + b)
  have h4 := H.eHat_nonneg
  nlinarith

end KamHyp

end KAM.Planetary

end
