/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.StepNonres
public import KAM.Planetary.Averaging.Finite

/-!
# Two-scale KAM step: smallness and the averaging hypotheses (`stepP:p3:st-small`)

`KamHyp` together with `hD` yields `AvgHyp` at radius `rhoHat p` with the divisors
`alpha₁ p`, `alpha₂ p` and the strict smallness `64 e K E < α₂ R`, so `avg` applies.
Design package P23-14.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

theorem inClass_mono_dom {n m : ℕ} {D : Set (Fin m → ℂ)} {r r' s s' : ℝ}
    {u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} (hu : InClass D r s u) (hr : r' ≤ r) (hs : s' ≤ s) :
    InClass D r' s' u :=
  ⟨hu.differentiableOn.mono (Dom_mono hr hs), fun j z hz => hu.periodic j z (Dom_mono hr hs hz)⟩

theorem realOn_mono_dom {n : ℕ} {U V : Set (CPhase n)} {u : CHam n} (hu : RealOn U u)
    (hV : V ⊆ U) : RealOn V u := fun x hx => hu x (hV hx)

namespace KamHyp

theorem alpha₂_pos (H : KamHyp D sbar p h f) : 0 < alpha₂ p := by
  have := H.K_pos
  unfold alpha₂
  have := H.positive.1
  positivity

theorem alpha_le (H : KamHyp D sbar p h f) : alpha₂ p ≤ alpha₁ p := by
  have := H.K_pos
  unfold alpha₁ alpha₂
  have := H.positive.1
  have h2 := H.gamma_order
  gcongr

theorem alpha₂_ge (H : KamHyp D sbar p h f) :
    2 * p.Mhat * cutoff p * rhoHat p ≤ alpha₂ p := by
  have hK := H.K_pos
  have hT : 0 < cutoff p ^ p.τ := Real.rpow_pos_of_pos hK _
  have hKt : cutoff p ^ (p.τ + 1) = cutoff p ^ p.τ * cutoff p := Real.rpow_add_one hK.ne' _
  have h2 := H.R_le_γ₂
  rw [hKt] at h2
  unfold alpha₂
  rw [le_div_iff₀ hT]
  nlinarith

theorem alpha₁_ge (H : KamHyp D sbar p h f) :
    2 * p.M * cutoff p * rhoHat p ≤ alpha₁ p := by
  have hK := H.K_pos
  have hT : 0 < cutoff p ^ p.τ := Real.rpow_pos_of_pos hK _
  have hKt : cutoff p ^ (p.τ + 1) = cutoff p ^ p.τ * cutoff p := Real.rpow_add_one hK.ne' _
  have h2 := H.R_le_γ₁
  rw [hKt] at h2
  unfold alpha₁
  rw [le_div_iff₀ hT]
  nlinarith

/-- `64 e K E < α₂ R` and `128 K E ≤ α₂ R` (`stepP:p3:st-small`). -/
theorem small_avg (H : KamHyp D sbar p h f) :
    64 * exp 1 * cutoff p * p.E < alpha₂ p * rhoHat p ∧
    p.E ≤ alpha₂ p * rhoHat p / (128 * cutoff p) := by
  have hK := H.K_pos
  have hR := H.R_pos
  have hMh := H.positive.2.2.2.2.2.1
  have hE := H.positive.2.2.2.1
  have hs := H.eHat_small
  have h0 := H.eHat_nonneg
  have h1 := H.E_le_Mhat
  have h2 := H.alpha₂_ge
  have he : exp 1 < 3 := by
    have := Real.exp_one_lt_d9; linarith
  have hKR : 0 < cutoff p * rhoHat p := by positivity
  have h3 : p.E * cutoff p ≤ eHat p * p.Mhat * (rhoHat p ^ 2 * cutoff p) := by
    have := mul_le_mul_of_nonneg_right h1 hK.le
    nlinarith
  have h4 : 2 * p.Mhat * cutoff p * rhoHat p * rhoHat p ≤ alpha₂ p * rhoHat p :=
    mul_le_mul_of_nonneg_right h2 hR.le
  have h5 : 0 < eHat p * p.Mhat * (rhoHat p ^ 2 * cutoff p) + 1 := by positivity
  constructor
  · have hex : 0 < exp 1 := Real.exp_pos 1
    have h6 : 64 * exp 1 * cutoff p * p.E ≤ 192 * (p.E * cutoff p) := by
      have := mul_pos (sub_pos.2 he) (mul_pos hK hE); nlinarith
    have h7 : 192 * (p.E * cutoff p) ≤
        96 * eHat p * (2 * p.Mhat * cutoff p * rhoHat p * rhoHat p) := by
      nlinarith
    have h8 : 96 * eHat p < 1 := by nlinarith
    have hpos : 0 < 2 * p.Mhat * cutoff p * rhoHat p * rhoHat p := by positivity
    nlinarith
  · rw [le_div_iff₀ (by positivity)]
    have h7 : p.E * (128 * cutoff p) ≤
        64 * eHat p * (2 * p.Mhat * cutoff p * rhoHat p * rhoHat p) := by
      nlinarith
    have hpos : 0 < 2 * p.Mhat * cutoff p * rhoHat p * rhoHat p := by positivity
    nlinarith

/-- The averaging hypotheses at radius `rhoHat p` (`stepP:p3:st-small`). -/
theorem avgHyp (H : KamHyp D sbar p h f)
    (hD : ∀ I ∈ D, realFreq h I ∈ twoScaleDiophantine a b p.γ₁ p.γ₂ p.τ) :
    AvgHyp D (rhoHat p) (geometricWidth sbar) (geometricWidth p.s) (cutoff p) (alpha₁ p)
      (alpha₂ p) p.E h f := by
  have hs := H.positive.2.1
  have hπ := Real.pi_pos
  have hw : geometricWidth sbar + geometricWidth p.s = geometricWidth (sbar + p.s) := by
    unfold geometricWidth; ring
  have hsb : 0 < sbar := by have := H.widths.1; linarith
  refine ⟨H.R_pos, ?_, ?_, H.K_pos, ?_, H.alpha₂_pos, H.alpha_le, H.positive.2.2.2.1.le, ?_,
    ?_, ?_, ?_, ?_, twoDiv_of_kamHyp H hD, (H.small_avg).2⟩
  · unfold geometricWidth; positivity
  · unfold geometricWidth; positivity
  · have : 2 * π * cutoff p * geometricWidth p.s = cutoff p * p.s := by
      unfold geometricWidth; field_simp
    rw [this]; exact H.K_mul_s
  · exact H.holo.mono (actionNbhd_mono H.R_le_ρ)
  · rw [hw]
    exact realOn_mono_dom H.real_h (fun z hz => Dom_mono H.R_le_ρ le_rfl hz)
  · rw [hw]
    exact realOn_mono_dom H.real_f (fun z hz => Dom_mono H.R_le_ρ le_rfl hz)
  · rw [hw]; exact inClass_mono_dom H.f_class H.R_le_ρ le_rfl
  · rw [hw]; exact H.f_bound.mono H.R_le_ρ le_rfl le_rfl

end KamHyp

end KAM.Planetary

end
