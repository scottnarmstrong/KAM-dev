/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.StepHess
public import KAM.Planetary.TwoScale.StepPerturb

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

/-- Hessian, row and inverse bounds of `h + g` on the quarter-radius neighbourhood. -/
theorem hessian_next (H : KamHyp D sbar p h f) {g : (Fin (a + b) → ℂ) → ℂ}
    (hg : DifferentiableOn ℂ g (KAM.actionNbhd D (rhoHat p / 2)))
    (hgb : ∀ I ∈ KAM.actionNbhd D (rhoHat p / 2), ‖g I‖ ≤ 5 / 4 * p.E) :
    ∀ I ∈ KAM.actionNbhd D (rhoHat p / 4),
      ‖fderiv ℂ (freq (fun J => h J + g J)) I‖ ≤ 2 * p.M ∧
      (∀ v, ‖lastBlock (a := a) (fderiv ℂ (freq (fun J => h J + g J)) I v)‖ ≤
        2 * p.Mhat * ‖v‖) ∧
      ∃ A : (Fin (a + b) → ℂ) ≃L[ℂ] (Fin (a + b) → ℂ),
        (A : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ)) =
          fderiv ℂ (freq (fun J => h J + g J)) I ∧
        ‖(A.symm : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ))‖ ≤ 2 * p.Mbar ∧
        (∀ v, ‖firstBlock (b := b) (A.symm v)‖ ≤ 2 * p.Mbar₁ * ‖v‖) ∧
        (∀ v, ‖lastBlock (a := a) (A.symm v)‖ ≤ 2 * p.Mbar₂ * ‖v‖) := by
  intro I hI
  have hR := H.R_pos
  have hM := H.positive.2.2.2.2.1
  have hMh := H.positive.2.2.2.2.2.1
  have hMb := H.positive.2.2.2.2.2.2.1
  obtain ⟨hb1, hb2, hb3⟩ := H.beta_facts
  set β : ℝ := 80 * p.E / rhoHat p ^ 2 with hβ
  have hβ0 : 0 ≤ β := by have := H.positive.2.2.2.1; positivity
  have hU := isOpen_actionNbhd' D (rhoHat p / 2)
  have hI2 : I ∈ KAM.actionNbhd D (rhoHat p / 2) := actionNbhd_mono (by linarith) hI
  have hhU : DifferentiableOn ℂ h (KAM.actionNbhd D (rhoHat p / 2)) :=
    H.holo.mono (actionNbhd_mono (by linarith [H.R_le_ρ]))
  have hIρ : I ∈ KAM.actionNbhd D p.ρ := actionNbhd_mono (by linarith [H.R_le_ρ]) hI
  rw [fderiv_freq_add hU hhU hg hI2]
  obtain ⟨-, hg2⟩ := g_bounds (by positivity) hg hgb (A := 5 / 4 * p.E)
    (show I ∈ KAM.actionNbhd D (rhoHat p / 2 / 2) by
      have : rhoHat p / 2 / 2 = rhoHat p / 4 := by ring
      rw [this]; exact hI)
  have hg2' : ‖fderiv ℂ (fderiv ℂ g) I‖ ≤ β := by
    refine hg2.trans_eq ?_
    rw [hβ]; field_simp; ring
  have hgd : DifferentiableAt ℂ (fderiv ℂ g) I :=
    (differentiableOn_fderiv_of_isOpen hU hg).differentiableAt (hU.mem_nhds hI2)
  have hFg : ∀ v, ‖fderiv ℂ (freq g) I v‖ ≤ β * ‖v‖ := freq_g_fderiv hgd hg2'
  have hFgn : ‖fderiv ℂ (freq g) I‖ ≤ β := ContinuousLinearMap.opNorm_le_bound _ hβ0 hFg
  obtain ⟨hh1, hh2, A, hA, hA1, hA2, hA3⟩ := H.hessian I hIρ
  refine ⟨?_, fun v => ?_, ?_⟩
  · have := norm_add_le (fderiv ℂ (freq h) I) (fderiv ℂ (freq g) I)
    linarith
  · have e : lastBlock (a := a) ((fderiv ℂ (freq h) I + fderiv ℂ (freq g) I) v) =
        lastBlock (a := a) (fderiv ℂ (freq h) I v) + lastBlock (a := a) (fderiv ℂ (freq g) I v) :=
      rfl
    have h3 : ‖lastBlock (a := a) (fderiv ℂ (freq g) I v)‖ ≤ β * ‖v‖ :=
      (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j =>
        (norm_le_pi_norm (fderiv ℂ (freq g) I v) (Fin.natAdd a j)).trans (hFg v)
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have := hh2 v
    nlinarith [norm_nonneg v]
  · have hB1 : ‖fderiv ℂ (freq g) I‖ * ‖(A.symm : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ))‖ ≤ 1 / 2 := by
      have := mul_le_mul hFgn hA1 (norm_nonneg _) hβ0
      linarith
    obtain ⟨A', hA', hA'w⟩ := perturb_equiv A _ hB1
    refine ⟨A', by rw [hA', hA], ?_, ?_, ?_⟩
    · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
      obtain ⟨u, hu, hu2⟩ := hA'w w
      show ‖A'.symm w‖ ≤ 2 * p.Mbar * ‖w‖
      rw [hu]
      have h6 := (A.symm : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ)).le_opNorm u
      calc ‖A.symm u‖ ≤ ‖(A.symm : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ))‖ * ‖u‖ := h6
        _ ≤ p.Mbar * (2 * ‖w‖) :=
          mul_le_mul hA1 hu2 (norm_nonneg _) hMb.le
        _ = _ := by ring
    · intro v
      obtain ⟨u, hu, hu2⟩ := hA'w v
      rw [hu]
      calc _ ≤ p.Mbar₁ * ‖u‖ := hA2 u
        _ ≤ p.Mbar₁ * (2 * ‖v‖) := mul_le_mul_of_nonneg_left hu2 (by
            have := H.positive.2.2.2.2.2.2.2.1; exact this.le)
        _ = _ := by ring
    · intro v
      obtain ⟨u, hu, hu2⟩ := hA'w v
      rw [hu]
      calc _ ≤ p.Mbar₂ * ‖u‖ := hA3 u
        _ ≤ p.Mbar₂ * (2 * ‖v‖) := mul_le_mul_of_nonneg_left hu2 (by
            have := H.positive.2.2.2.2.2.2.2.2; exact this.le)
        _ = _ := by ring

end KamHyp

end KAM.Planetary

end
