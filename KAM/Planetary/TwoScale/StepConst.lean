/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.StepNonres

/-!
# Two-scale KAM step: the new constants (`stepP:p3:st-const`, `stepP:p3:st-quad`)

`cutoff (nextScale p) ≤ 24 cutoff p`, `rhoHat (nextScale p) ≥ rhoHat p / (2·24^(τ+1))`,
`eHat (nextScale p) ≤ (8/9) (4s)^(2(τ+1)) eHat p²` and the strict quadratic bound.
Design package P23-14.
-/

@[expose] public noncomputable section

open Set Real

namespace KAM.Planetary

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

/-- The quantity `x = E M² L / γ₁²` of the cutoff. -/
def xval (p : ScaleData) : ℝ := p.E * p.M ^ 2 * p.L / p.γ₁ ^ 2

theorem cutoff_eq (p : ScaleData) : cutoff p = 6 / p.s * max 1 (log (1 / xval p)) := rfl

@[simp] theorem nextScale_s (p : ScaleData) : (nextScale p).s = p.s / 12 := rfl
@[simp] theorem nextScale_E (p : ScaleData) :
    (nextScale p).E = p.E ^ 2 * p.L * p.M ^ 2 / p.γ₁ ^ 2 := rfl
@[simp] theorem nextScale_M (p : ScaleData) : (nextScale p).M = 2 * p.M := rfl
@[simp] theorem nextScale_Mhat (p : ScaleData) : (nextScale p).Mhat = 2 * p.Mhat := rfl
@[simp] theorem nextScale_L (p : ScaleData) : (nextScale p).L = 2 * p.L := rfl
@[simp] theorem nextScale_γ₁ (p : ScaleData) : (nextScale p).γ₁ = p.γ₁ := rfl
@[simp] theorem nextScale_γ₂ (p : ScaleData) : (nextScale p).γ₂ = p.γ₂ := rfl
@[simp] theorem nextScale_τ (p : ScaleData) : (nextScale p).τ = p.τ := rfl
@[simp] theorem nextScale_ρ (p : ScaleData) : (nextScale p).ρ = rhoHat p / 16 := rfl

theorem xval_pos (H : KamHyp D sbar p h f) : 0 < xval p := by
  have := H.positive.2.2.2.1; have := H.positive.2.2.2.2.1; have := H.L_pos; have := H.γ₁_pos
  unfold xval; positivity

theorem xval_next (p : ScaleData) : xval (nextScale p) = 8 * xval p ^ 2 := by
  unfold xval; simp only [nextScale_E, nextScale_M, nextScale_L, nextScale_γ₁]
  ring

theorem cutoff_next_le (H : KamHyp D sbar p h f) : cutoff (nextScale p) ≤ 24 * cutoff p := by
  have hs := H.positive.2.1
  have hx := xval_pos H
  rw [cutoff_eq, cutoff_eq, xval_next, nextScale_s]
  have h1 : log (1 / (8 * xval p ^ 2)) ≤ 2 * log (1 / xval p) := by
    have : 1 / (8 * xval p ^ 2) = (1 / 8) * (1 / xval p) ^ 2 := by field_simp
    rw [this, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have : log (1 / 8 : ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
    push_cast; linarith
  have h2 : max 1 (log (1 / (8 * xval p ^ 2))) ≤ 2 * max 1 (log (1 / xval p)) := by
    refine max_le ?_ ?_
    · have := le_max_left 1 (log (1 / xval p)); linarith
    · have := le_max_right 1 (log (1 / xval p)); linarith
  have h3 : 0 < 6 / (p.s / 12) := by positivity
  calc 6 / (p.s / 12) * max 1 (log (1 / (8 * xval p ^ 2)))
      ≤ 6 / (p.s / 12) * (2 * max 1 (log (1 / xval p))) := by gcongr
    _ = 24 * (6 / p.s * max 1 (log (1 / xval p))) := by field_simp; ring

theorem rhoHat_eq (p : ScaleData) : rhoHat p =
    min (min (p.γ₁ / (3 * p.M * cutoff p ^ (p.τ + 1)))
      (p.γ₂ / (3 * p.Mhat * cutoff p ^ (p.τ + 1)))) p.ρ := rfl

theorem rhoHat_aux {R c M K Kp γ : ℝ} (hc : 0 < c) (hM : 0 ≤ M) (hR : 0 ≤ R) (hKK : Kp ≤ c * K)
    (h : 3 * M * K * R ≤ γ) : R / (2 * c) * (3 * (2 * M) * Kp) ≤ γ := by
  have h1 : R / (2 * c) * (3 * (2 * M) * Kp) ≤ R / (2 * c) * (3 * (2 * M) * (c * K)) := by
    gcongr
  refine h1.trans (le_of_eq_of_le ?_ h)
  field_simp

theorem rhoHat_next_ge (H : KamHyp D sbar p h f) :
    rhoHat p / (2 * 24 ^ (p.τ + 1)) ≤ rhoHat (nextScale p) := by
  have hK := H.K_pos
  have hR := H.R_pos
  have hτ := H.τ_pos
  have hM := H.positive.2.2.2.2.1
  have hMh := H.positive.2.2.2.2.2.1
  have hK' : 0 < cutoff (nextScale p) := by
    have := H.positive.2.1
    exact cutoff_pos (by simp; positivity)
  have h24 : (1 : ℝ) ≤ 24 ^ (p.τ + 1) := Real.one_le_rpow (by norm_num) (by linarith)
  have h24' : (24 : ℝ) ≤ 24 ^ (p.τ + 1) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 24)
      (by linarith : (1 : ℝ) ≤ p.τ + 1)
  have hc : (0 : ℝ) < 24 ^ (p.τ + 1) := by linarith
  have hKK : cutoff (nextScale p) ^ (p.τ + 1) ≤ 24 ^ (p.τ + 1) * cutoff p ^ (p.τ + 1) := by
    rw [← Real.mul_rpow (by norm_num) hK.le]
    exact Real.rpow_le_rpow hK'.le (cutoff_next_le H) (by linarith)
  have hKp' : 0 < cutoff (nextScale p) ^ (p.τ + 1) := Real.rpow_pos_of_pos hK' _
  have hR1 := H.R_le_γ₁
  have hR2 := H.R_le_γ₂
  rw [rhoHat_eq (nextScale p)]
  simp only [nextScale_τ, nextScale_γ₁, nextScale_γ₂, nextScale_M, nextScale_Mhat, nextScale_ρ]
  refine le_min (le_min ?_ ?_) ?_
  · rw [le_div_iff₀ (by positivity)]
    exact rhoHat_aux hc hM.le hR.le hKK hR1
  · rw [le_div_iff₀ (by positivity)]
    exact rhoHat_aux hc hMh.le hR.le hKK hR2
  · exact div_le_div_of_nonneg_left hR.le (by norm_num) (by linarith)

/-- Quadratic bound of the new error constant. -/
theorem xval_le (H : KamHyp D sbar p h f) :
    xval p ≤ eHat p / 9 * (p.s / 6) ^ (2 * (p.τ + 1)) := by
  have hK := H.K_pos
  have hR := H.R_pos
  have hτ := H.τ_pos
  have hM := H.positive.2.2.2.2.1
  have hs := H.positive.2.1
  have hγ := H.γ₁_pos
  have hKs := H.K_mul_s
  have hKt : cutoff p ^ (p.τ + 1) = cutoff p ^ p.τ * cutoff p := Real.rpow_add_one hK.ne' _
  have hT : 0 < cutoff p ^ p.τ := Real.rpow_pos_of_pos hK _
  have h1 := H.R_le_γ₁
  have h2 : xval p = eHat p * (rhoHat p * p.M / p.γ₁) ^ 2 := by
    unfold xval; rw [KamHyp.eHat_eq]; field_simp
  have h3 : rhoHat p * p.M / p.γ₁ ≤ 1 / (3 * cutoff p ^ (p.τ + 1)) := by
    rw [div_le_div_iff₀ hγ (by positivity)]; nlinarith
  have h4 : 1 / cutoff p ^ (p.τ + 1) ≤ (p.s / 6) ^ (p.τ + 1) := by
    have : 1 / cutoff p ≤ p.s / 6 := by
      rw [div_le_div_iff₀ hK (by norm_num)]; nlinarith
    rw [one_div, ← Real.inv_rpow hK.le]
    exact Real.rpow_le_rpow (by positivity) (by simpa using this) (by linarith)
  have h5 : (rhoHat p * p.M / p.γ₁) ^ 2 ≤ 1 / 9 * (p.s / 6) ^ (2 * (p.τ + 1)) := by
    have h0 : 0 ≤ rhoHat p * p.M / p.γ₁ := by positivity
    have h6 : rhoHat p * p.M / p.γ₁ ≤ 1 / 3 * (p.s / 6) ^ (p.τ + 1) := by
      refine h3.trans ?_
      have e : 1 / (3 * cutoff p ^ (p.τ + 1)) = 1 / 3 * (1 / cutoff p ^ (p.τ + 1)) := by
        field_simp
      rw [e]; gcongr
    have h7 : (p.s / 6) ^ (2 * (p.τ + 1)) = ((p.s / 6) ^ (p.τ + 1)) ^ 2 := by
      rw [mul_comm, Real.rpow_mul (by positivity), Real.rpow_two]
    rw [h7]
    calc (rhoHat p * p.M / p.γ₁) ^ 2 ≤ (1 / 3 * (p.s / 6) ^ (p.τ + 1)) ^ 2 :=
          pow_le_pow_left₀ h0 h6 2
      _ = 1 / 9 * ((p.s / 6) ^ (p.τ + 1)) ^ 2 := by ring
  rw [h2]
  have := H.eHat_nonneg
  nlinarith

theorem eHat_pos (H : KamHyp D sbar p h f) : 0 < eHat p := by
  rw [KamHyp.eHat_eq]
  have := H.positive.2.2.2.1; have := H.L_pos; have := H.R_pos
  positivity

theorem eHat_next_le (H : KamHyp D sbar p h f) :
    eHat (nextScale p) ≤ 8 / 9 * (4 * p.s) ^ (2 * (p.τ + 1)) * eHat p ^ 2 := by
  have hR := H.R_pos
  have hτ := H.τ_pos
  have hs := H.positive.2.1
  have hL := H.L_pos
  have hE := H.positive.2.2.2.1
  have hx := xval_pos H
  have hxl := xval_le H
  have hge := rhoHat_next_ge H
  set c : ℝ := 24 ^ (p.τ + 1) with hc
  have hc0 : 0 < c := by positivity
  have hR' : 0 < rhoHat (nextScale p) := lt_of_lt_of_le (by positivity) hge
  have hE' : (nextScale p).E = p.E * xval p := by
    simp only [nextScale_E, xval]; ring
  have h1 : eHat (nextScale p) = p.E * xval p * (2 * p.L) / rhoHat (nextScale p) ^ 2 := by
    rw [KamHyp.eHat_eq, nextScale_L, hE']
  have h2 : (rhoHat p / (2 * c)) ^ 2 ≤ rhoHat (nextScale p) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hge 2
  have h3 : eHat (nextScale p) ≤ p.E * xval p * (2 * p.L) / (rhoHat p / (2 * c)) ^ 2 := by
    rw [h1]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) h2
  have h4 : p.E * xval p * (2 * p.L) / (rhoHat p / (2 * c)) ^ 2 = 8 * c ^ 2 * xval p * eHat p := by
    rw [KamHyp.eHat_eq]; field_simp; ring
  have h5 : c ^ 2 * (p.s / 6) ^ (2 * (p.τ + 1)) = (4 * p.s) ^ (2 * (p.τ + 1)) := by
    have e1 : c ^ 2 = 24 ^ (2 * (p.τ + 1)) := by
      rw [hc, mul_comm, Real.rpow_mul (by norm_num), Real.rpow_two]
    rw [e1, ← Real.mul_rpow (by norm_num) (by positivity)]
    congr 1; ring
  have hEh := (eHat_pos H).le
  calc eHat (nextScale p) ≤ 8 * c ^ 2 * xval p * eHat p := h3.trans_eq h4
    _ ≤ 8 * c ^ 2 * (eHat p / 9 * (p.s / 6) ^ (2 * (p.τ + 1))) * eHat p := by gcongr
    _ = 8 / 9 * (c ^ 2 * (p.s / 6) ^ (2 * (p.τ + 1))) * eHat p ^ 2 := by ring
    _ = _ := by rw [h5]

theorem eHat_next_lt (H : KamHyp D sbar p h f) : eHat (nextScale p) < eHat p ^ 2 := by
  have hs := H.positive.2.1
  have hw := H.widths
  have h4s : 4 * p.s < 1 := by linarith
  have hτ := H.τ_pos
  have h1 : (4 * p.s) ^ (2 * (p.τ + 1)) ≤ 1 :=
    Real.rpow_le_one (by positivity) h4s.le (by linarith)
  have hp := eHat_pos H
  have h2 := eHat_next_le H
  have : 8 / 9 * (4 * p.s) ^ (2 * (p.τ + 1)) * eHat p ^ 2 < eHat p ^ 2 := by
    have : 0 < eHat p ^ 2 := by positivity
    nlinarith
  linarith

theorem small_next (H : KamHyp D sbar p h f) :
    kamConstant (a + b) (nextScale p).τ * eHat (nextScale p) < 1 := by
  have hp := eHat_pos H
  have h1 := H.small
  have h2 := eHat_next_lt H
  have h3 := H.eHat_small
  have hk : 0 ≤ kamConstant (a + b) p.τ :=
    (by positivity : (0 : ℝ) ≤ 2 ^ 13 * ((a + b : ℕ) : ℝ)).trans (le_max_left _ _)
  simp only [nextScale_τ]
  have : kamConstant (a + b) p.τ * eHat (nextScale p) ≤ kamConstant (a + b) p.τ * eHat p ^ 2 :=
    mul_le_mul_of_nonneg_left h2.le hk
  have h4 : kamConstant (a + b) p.τ * eHat p ^ 2 < eHat p := by nlinarith
  nlinarith

end KAM.Planetary

end
