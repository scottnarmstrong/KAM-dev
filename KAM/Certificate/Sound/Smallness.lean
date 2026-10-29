/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Sound.Static

/-!
# Soundness of the smallness sub-check

`checkSmallness_sound`: the two exact rational inequalities of `checkSmallness` give the
threshold `C₁ e / (γ⁴ ρ^{4τ}) < 1` and the displacement bound `C₂ e / (γ² ρ^{2τ}) ≤ disp`, through
`isoC1_le_isoC1Q`, `isoC2_le_isoC2Q`, `0 ≤ e` and `Real.rpow_natCast`.
-/

public section

namespace KAM.Certificate

open KAM KAM.Torus CertArith

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

theorem checkSmallness_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (h : checkSmallness c = true) :
    Iso.Apost.isoC1 n c.params.tau c.params.rho c.params.rhoInf c.params.M c.params.σK
      c.params.σB c.params.σT c.params.μ c.params.nuRay c.params.γbar * c.params.err /
      ((c.params.γ : ℝ) ^ 4 * (c.params.rho : ℝ) ^ (4 * (c.params.tau : ℝ))) < 1 ∧
    Iso.Apost.isoC2 n c.params.tau c.params.rho c.params.rhoInf c.params.M c.params.σK
      c.params.σB c.params.σT * c.params.err /
      ((c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * (c.params.tau : ℝ))) ≤ c.params.disp := by
  have S := checkStatic_sound hs
  simp only [checkSmallness, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hτ : n - 1 ≤ c.params.tau := by
    have : (n : ℝ) ≤ c.params.tau + 1 := by linarith [S.hτ]
    have : n ≤ c.params.tau + 1 := by exact_mod_cast this
    omega
  have hρinf : (0 : ℚ) < c.params.rhoInf := by exact_mod_cast S.hρinf
  have hρρ : c.params.rhoInf < c.params.rho := by exact_mod_cast S.hρinfρ
  have hc1 := isoC1_le_isoC1Q (γbar := c.params.γbar) S.hn hτ hρinf hρρ
    (by exact_mod_cast S.hM) (by exact_mod_cast S.hσK) (by exact_mod_cast S.hσB)
    (by exact_mod_cast S.hσT) (by exact_mod_cast S.hμ) (by exact_mod_cast S.hν)
    (by exact_mod_cast S.hγbar)
  have hc2 := isoC2_le_isoC2Q S.hn hτ hρinf hρρ
    (by exact_mod_cast S.hM) (by exact_mod_cast S.hσK) (by exact_mod_cast S.hσB)
    (by exact_mod_cast S.hσT)
  have hρ0 : (0 : ℝ) < c.params.rho := S.hρinf.trans S.hρinfρ
  have h4 : (4 : ℝ) * (c.params.tau : ℝ) = ((4 * c.params.tau : ℕ) : ℝ) := by push_cast; ring
  have h2' : (2 : ℝ) * (c.params.tau : ℝ) = ((2 * c.params.tau : ℕ) : ℝ) := by push_cast; ring
  rw [h4, h2', Real.rpow_natCast, Real.rpow_natCast]
  have hd4 : (0 : ℝ) < (c.params.γ : ℝ) ^ 4 * (c.params.rho : ℝ) ^ (4 * c.params.tau) := by
    positivity [S.hγ]
  have hd2 : (0 : ℝ) < (c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * c.params.tau) := by
    positivity [S.hγ]
  have h1' : ((isoC1Q n c.params.tau c.params.rho c.params.rhoInf c.params.M c.params.σK
      c.params.σB c.params.σT c.params.μ c.params.nuRay c.params.γbar : ℚ) : ℝ) * c.params.err <
      (c.params.γ : ℝ) ^ 4 * (c.params.rho : ℝ) ^ (4 * c.params.tau) := by exact_mod_cast h1
  have h2'' : ((isoC2Q n c.params.tau c.params.rho c.params.rhoInf c.params.M c.params.σK
      c.params.σB c.params.σT : ℚ) : ℝ) * c.params.err ≤
      (c.params.disp : ℝ) * ((c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * c.params.tau)) := by
    exact_mod_cast h2
  constructor
  · rw [div_lt_one hd4]
    exact (mul_le_mul_of_nonneg_right hc1 S.he0).trans_lt h1'
  · rw [div_le_iff₀ hd2]
    exact (mul_le_mul_of_nonneg_right hc2 S.he0).trans h2''

end KAM.Certificate
