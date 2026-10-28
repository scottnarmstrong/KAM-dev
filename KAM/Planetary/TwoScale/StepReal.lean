/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.StepIhat
public import KAM.Planetary.TwoScale.StepSchwarz

/-!
# Two-scale KAM step: reality of `ĩ₊` (`stepP:p3:st-ihat`, last paragraph)

For real `I ∈ D` the point `ĩ₊(I)` is real: `ω₊` commutes with complex conjugation on a polydisc
centred at a real point (Schwarz reflection, `schwarz_vec`), so `conj ĩ₊(I)` is a second preimage of
the real `ω₀(I)` in the injectivity domain. Design package P23-14.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

/-- `h` is real at the real points of an action neighbourhood where it is real on the phase domain. -/
theorem im_realInclusion_zero {n : ℕ} {D : Set (Fin n → ℝ)} {ρ sb : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hsb : 0 < sb) (hreal : RealOn (coefficientDom D ρ sb) (fun z => h z.2)) {J : Fin n → ℝ}
    (hJ : KAM.realInclusion n J ∈ KAM.actionNbhd D ρ) : (h (KAM.realInclusion n J)).im = 0 := by
  have hm : KAM.realInclusion₂ n (0, J) ∈ coefficientDom D ρ sb := by
    refine ⟨fun j => ?_, ?_⟩
    · simpa [KAM.realInclusion₂_apply, geometricWidth] using div_pos hsb (by positivity)
    · simpa [KAM.realInclusion₂_apply] using
        ((conv_data D ρ 0).1.symm ▸ hJ : KAM.realInclusion n J ∈ polyNbhd (realBase D) ρ)
  simpa [KAM.realInclusion₂_apply] using hreal (0, J) hm

namespace KamHyp

variable {g : (Fin (a + b) → ℂ) → ℂ}

theorem ihat_real (H : KamHyp D sbar p h f)
    (hg : DifferentiableOn ℂ g (KAM.actionNbhd D (rhoHat p / 2)))
    (hgb : ∀ I ∈ KAM.actionNbhd D (rhoHat p / 2), ‖g I‖ ≤ 5 / 4 * p.E)
    (hgr : RealOn (coefficientDom D (rhoHat p / 2) (sbar + p.s / 6)) (fun z => g z.2))
    {ihat : (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)}
    (hih : ∀ I ∈ KAM.actionNbhd D (rhoHat p / 16),
      ihat I ∈ Metric.ball I (rhoHat p / 16) ∧ freq (fun J => h J + g J) (ihat I) = freq h I)
    {I : Fin (a + b) → ℝ} (hI : I ∈ D) (i : Fin (a + b)) :
    (ihat (KAM.realInclusion (a + b) I) i).im = 0 := by
  have hR := H.R_pos
  have hs := H.positive.2.1
  have hw := H.widths
  have hRρ := H.R_le_ρ
  have hsb : 0 < sbar + p.s / 6 := by linarith [hw.1]
  have hU2 := isOpen_actionNbhd' D (rhoHat p / 2)
  have hhU : DifferentiableOn ℂ h (KAM.actionNbhd D (rhoHat p / 2)) :=
    H.holo.mono (actionNbhd_mono (by linarith))
  have hpd : DifferentiableOn ℂ (fun J => h J + g J) (KAM.actionNbhd D (rhoHat p / 2)) :=
    hhU.add hg
  have hpr : RealOn (coefficientDom D (rhoHat p / 2) (sbar + p.s / 6))
      (fun z => (fun J => h J + g J) z.2) := by
    intro x hx
    have h1 := hgr x hx
    have h2 := H.real_h x (coefficientDom_mono (actionNbhd_mono (by linarith))
      (by linarith [hw.1]) hx)
    simp only [Complex.add_im, h1, h2, add_zero]
  set c : Fin (a + b) → ℂ := KAM.realInclusion (a + b) I with hc
  have hcmem : c ∈ KAM.actionNbhd D (rhoHat p / 16) := mem_actionNbhd_of_mem (by positivity) hI
  obtain ⟨hJb, hJe⟩ := hih c hcmem
  set J := ihat c with hJ
  have hballsub : Metric.ball c (rhoHat p / 8) ⊆ KAM.actionNbhd D (rhoHat p / 8) :=
    actionNbhd_ball hI
  have hF : DifferentiableOn ℂ (freq (fun J => h J + g J)) (Metric.ball c (rhoHat p / 8)) :=
    fun z hz => (differentiableAt_freq hU2 hpd
      (actionNbhd_mono (by linarith) (hballsub hz))).differentiableWithinAt
  have hrealF : ∀ x : Fin (a + b) → ℝ, KAM.realInclusion (a + b) x ∈
      Metric.ball c (rhoHat p / 8) → ∀ i, (freq (fun J => h J + g J)
        (KAM.realInclusion (a + b) x) i).im = 0 := by
    intro x hx i
    exact freq_im_zero hpd hsb hpr (actionNbhd_mono (by linarith) (hballsub hx)) i
  have hsch := schwarz_vec (by positivity : 0 < rhoHat p / 8) hF hrealF
  have hJb8 : J ∈ Metric.ball c (rhoHat p / 8) := by
    have : J ∈ Metric.ball c (rhoHat p / 16) := hJb
    exact Metric.ball_subset_ball (by linarith) this
  have hconj8 : (fun i => starRingEnd ℂ (J i)) ∈ Metric.ball c (rhoHat p / 8) := by
    rw [mem_ball, dist_eq_norm] at hJb8 ⊢
    rw [pi_norm_lt_iff (by positivity)] at hJb8 ⊢
    intro i
    have := hJb8 i
    simp only [Pi.sub_apply, hc, KAM.realInclusion_apply] at this ⊢
    have e : starRingEnd ℂ (J i) - ((I i : ℝ) : ℂ) = starRingEnd ℂ (J i - ((I i : ℝ) : ℂ)) := by
      simp
    rw [e, Complex.norm_conj]; exact this
  have hfreq_c : ∀ j, (freq h c j).im = 0 := fun j =>
    freq_im_zero H.holo (by linarith [hw.1]) H.real_h
      (mem_actionNbhd_of_mem H.positive.2.2.1 hI) j
  have hEq : freq (fun J => h J + g J) (fun i => starRingEnd ℂ (J i)) =
      freq (fun J => h J + g J) J := by
    rw [hsch J hJb8, hJe]
    funext j
    exact Complex.conj_eq_iff_im.mpr (hfreq_c j)
  have hinj := H.freq_inj hg hgb (hballsub hconj8) (hballsub hJb8) hEq
  have := congrFun hinj i
  exact Complex.conj_eq_iff_im.mp this

end KamHyp

end KAM.Planetary

end
