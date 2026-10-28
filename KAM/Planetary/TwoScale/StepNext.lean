/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.StepReal
public import KAM.Planetary.TwoScale.StepConst

/-!
# Two-scale KAM step: assembly of the next `KamHyp`

`KamHyp Dp sbar (nextScale p) hp fs` from the averaging outputs `g`, `fs`, the Hessian bounds
of `hp = h + g`, injectivity of `ω₊` and the new constants. Design package P23-14.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

namespace KamHyp

theorem exp_cutoff_le (H : KamHyp D sbar p h f) :
    exp (-cutoff p * p.s / 6) ≤ xval p := by
  have hx := xval_pos H
  have hs := H.positive.2.1
  have e : cutoff p * p.s / 6 = max 1 (log (1 / xval p)) := by
    rw [cutoff_eq]; field_simp
  have e2 : -cutoff p * p.s / 6 = - (cutoff p * p.s / 6) := by ring
  rw [e2, e]
  calc exp (-max 1 (log (1 / xval p))) ≤ exp (-log (1 / xval p)) :=
        Real.exp_le_exp.2 (neg_le_neg (le_max_right _ _))
    _ = xval p := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp

variable {g : (Fin (a + b) → ℂ) → ℂ} {fs : CHam (a + b)} {Dp : Set (Fin (a + b) → ℝ)}

theorem next_hyp (H : KamHyp D sbar p h f)
    (hg : DifferentiableOn ℂ g (KAM.actionNbhd D (rhoHat p / 2)))
    (hgb : ∀ I ∈ KAM.actionNbhd D (rhoHat p / 2), ‖g I‖ ≤ 5 / 4 * p.E)
    (hgr : RealOn (coefficientDom D (rhoHat p / 2) (sbar + p.s / 6)) (fun z => g z.2))
    (hfsr : RealOn (coefficientDom D (rhoHat p / 2) (sbar + p.s / 6)) fs)
    (hfsc : InClass (realBase D) (rhoHat p / 2) (geometricWidth (sbar + p.s / 6)) fs)
    (hfsb : WBound (realBase D) (rhoHat p / 2) (geometricWidth (sbar + p.s / 6)) fs
      (exp (-cutoff p * p.s / 6) * p.E))
    (hDp : KAM.actionNbhd Dp (rhoHat p / 16) ⊆ KAM.actionNbhd D (rhoHat p / 8)) :
    KamHyp Dp sbar (nextScale p) (fun I => h I + g I) fs := by
  have hR := H.R_pos
  have hs := H.positive.2.1
  have hw := H.widths
  have hRρ := H.R_le_ρ
  obtain ⟨hγ₂, -, -, hE, hM, hMh, hMb, hMb₁, hMb₂⟩ := H.positive
  have hL := H.L_pos
  have hγ₁ := H.γ₁_pos
  have hsub2 : KAM.actionNbhd Dp (rhoHat p / 16) ⊆ KAM.actionNbhd D (rhoHat p / 2) :=
    hDp.trans (actionNbhd_mono (by linarith))
  have hsubΩ : KAM.actionNbhd Dp (rhoHat p / 16) ⊆ KAM.actionNbhd D (rhoHat p / 8) := hDp
  have hU2 := isOpen_actionNbhd' D (rhoHat p / 2)
  have hhU : DifferentiableOn ℂ h (KAM.actionNbhd D (rhoHat p / 2)) :=
    H.holo.mono (actionNbhd_mono (by linarith))
  have hess := H.hessian_next hg hgb
  have hwd : geometricWidth (sbar + p.s / 12) ≤ geometricWidth (sbar + p.s / 6) := by
    unfold geometricWidth; gcongr; linarith
  have hsubP : polyNbhd (realBase Dp) (rhoHat p / 16) ⊆ polyNbhd (realBase D) (rhoHat p / 2) :=
    polyNbhd_realBase_subset hsub2
  have hxE : (nextScale p).E = p.E * xval p := by
    simp only [nextScale_E, xval]; ring
  refine ⟨H.a_pos, H.b_pos, H.τ_gt, ?_, H.gamma_order, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, small_next H⟩
  · show 0 < p.γ₂ ∧ 0 < p.s / 12 ∧ 0 < rhoHat p / 16 ∧ 0 < (nextScale p).E ∧ 0 < 2 * p.M ∧
      0 < 2 * p.Mhat ∧ 0 < 2 * p.Mbar ∧ 0 < 2 * p.Mbar₁ ∧ 0 < 2 * p.Mbar₂
    refine ⟨hγ₂, by positivity, by positivity, ?_, by positivity, by positivity, by positivity,
      by positivity, by positivity⟩
    rw [hxE]; have := xval_pos H; positivity
  · show 4 * (p.s / 12) ≤ sbar ∧ sbar < 1
    exact ⟨by linarith [hw.1], hw.2⟩
  · show 2 * p.Mhat ≤ 2 * p.M ∧ 2 * p.Mbar₁ ≤ 2 * p.Mbar ∧ 2 * p.Mbar₂ ≤ 2 * p.Mbar
    have := H.normalized
    refine ⟨?_, ?_, ?_⟩ <;> linarith [this.1, this.2.1, this.2.2]
  · have h1 : p.Mbar ≤ initialL p.M p.Mhat p.Mbar := le_max_left _ _
    have h2 : p.M⁻¹ ≤ initialL p.M p.Mhat p.Mbar := (le_max_left _ _).trans (le_max_right _ _)
    have h3 : p.Mhat⁻¹ ≤ initialL p.M p.Mhat p.Mbar := (le_max_right _ _).trans (le_max_right _ _)
    have hL' := H.L_bound
    show max (2 * p.Mbar) (max (2 * p.M)⁻¹ (2 * p.Mhat)⁻¹) ≤ 2 * p.L
    refine max_le (by linarith) (max_le ?_ ?_)
    · rw [mul_inv]; nlinarith [inv_pos.2 hM]
    · rw [mul_inv]; nlinarith [inv_pos.2 hMh]
  · exact (hhU.add hg).mono hsub2
  · exact realOn_mono_dom (H.hp_realOn hgr)
      (coefficientDom_mono hsub2 (by show sbar + p.s / 12 ≤ sbar + p.s / 6; linarith))
  · intro x hx
    exact hfsr x (coefficientDom_mono hsub2
      (by show sbar + p.s / 12 ≤ sbar + p.s / 6; linarith) hx)
  · simp only [nextScale_ρ, nextScale_s]
    exact inClass_mono_set hfsc hsubP hwd
  · simp only [nextScale_ρ, nextScale_s]
    refine wbound_mono_set hfsb hsubP hwd ?_
    rw [hxE]
    have := H.exp_cutoff_le
    nlinarith
  · exact (H.freq_inj hg hgb).mono hsubΩ
  · intro I hI
    exact hess I (actionNbhd_mono (by linarith) (hDp hI))

end KamHyp

end KAM.Planetary

end
