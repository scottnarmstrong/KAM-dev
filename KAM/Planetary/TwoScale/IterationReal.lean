/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.StepReal
public import KAM.Planetary.TwoScale.IterationCompose

/-!
# Two-scale KAM iteration: reality of `ĩ₊` from the output of `step`

The statement of `step` does not record that `ĩ₊` maps real points of `D` to real points. It
follows from the other outputs: `ĩ₊(I)` lies within `10 Ê R < R/16` of the real point `I`, hence
in the ball of radius `R/16` around the real point `q = Re ĩ₊(I) ∈ D₊`, on which the new frequency
map is holomorphic, real at real points and injective; Schwarz reflection then shows that
`conj ĩ₊(I)` is a second preimage of the real frequency `ω₀(I)`. Design package P23-16.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

namespace KamHyp

variable {a b : ℕ} {D Dp : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h g : (Fin (a + b) → ℂ) → ℂ} {f fs : CHam (a + b)}
  {ihat : (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)}

/-- `Ê` is tiny. -/
theorem eHat_lt_small (H : KamHyp D sbar p h f) : eHat p < 1 / 160 := by
  have h0 := H.eHat_nonneg
  have hk : 2 ^ 13 * ((a + b : ℕ) : ℝ) ≤ kamConstant (a + b) p.τ := le_max_left _ _
  have hn : (1 : ℝ) ≤ ((a + b : ℕ) : ℝ) := by
    have := H.a_pos; exact_mod_cast (by omega : 1 ≤ a + b)
  have := H.small
  nlinarith

theorem sup_norm_le (_H : KamHyp D sbar p h f) {v : Fin (a + b) → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (h1 : ‖firstBlock (b := b) v‖ ≤ B) (h2 : ‖lastBlock (a := a) v‖ ≤ B) : ‖v‖ ≤ B := by
  refine (pi_norm_le_iff_of_nonneg hB).2 fun i => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · exact (norm_le_pi_norm (firstBlock (b := b) v) i).trans h1
  · exact (norm_le_pi_norm (lastBlock (a := a) v) i).trans h2

/-- Reality of `ĩ₊` at the real points of `D`, from the outputs of `step`. -/
theorem ihat_real_of (H : KamHyp D sbar p h f)
    (H' : KamHyp Dp sbar (nextScale p) (fun I => h I + g I) fs)
    (hDp : Dp = (fun I => fun j => (ihat (KAM.realInclusion (a + b) I) j).re) '' D)
    (hih : ∀ I ∈ KAM.actionNbhd D (rhoHat p / 16),
      freq (fun J => h J + g J) (ihat I) = freq h I ∧
      ‖firstBlock (b := b) (ihat I - I)‖ ≤ 10 * (p.Mbar₁ / p.Mbar) * eHat p * rhoHat p ∧
      ‖lastBlock (a := a) (ihat I - I)‖ ≤ 10 * (p.Mbar₂ / p.Mbar) * eHat p * rhoHat p)
    {I : Fin (a + b) → ℝ} (hI : I ∈ D) (i : Fin (a + b)) :
    (ihat (KAM.realInclusion (a + b) I) i).im = 0 := by
  have hR := H.R_pos
  have hw := H.widths
  have hs := H.positive.2.1
  have hMb := H.positive.2.2.2.2.2.2.1
  have hMb₁ := H.positive.2.2.2.2.2.2.2.1
  have hMb₂ := H.positive.2.2.2.2.2.2.2.2
  obtain ⟨-, hn₁, hn₂⟩ := H.normalized
  set c : Fin (a + b) → ℂ := KAM.realInclusion (a + b) I with hc
  have hcmem : c ∈ KAM.actionNbhd D (rhoHat p / 16) := mem_actionNbhd_of_mem (by positivity) hI
  obtain ⟨hJe, hJ₁, hJ₂⟩ := hih c hcmem
  set J := ihat c with hJ
  have h0 := H.eHat_nonneg
  have hsmall := H.eHat_lt_small
  have hr₁ : p.Mbar₁ / p.Mbar ≤ 1 := (div_le_one hMb).2 hn₁
  have hr₂ : p.Mbar₂ / p.Mbar ≤ 1 := (div_le_one hMb).2 hn₂
  have hEB : 10 * eHat p * rhoHat p < rhoHat p / 16 := by nlinarith
  have hJc : ‖J - c‖ < rhoHat p / 16 := by
    refine lt_of_le_of_lt (H.sup_norm_le (B := 10 * eHat p * rhoHat p) (by positivity)
      (hJ₁.trans ?_) (hJ₂.trans ?_)) hEB
    · have : 0 ≤ 10 * eHat p * rhoHat p := by positivity
      nlinarith
    · have : 0 ≤ 10 * eHat p * rhoHat p := by positivity
      nlinarith
  -- the real point `q = Re J` of `D₊`
  set q : Fin (a + b) → ℝ := fun j => (J j).re with hq
  have hqD : q ∈ Dp := by rw [hDp]; exact ⟨I, hI, rfl⟩
  have hρ' : (0 : ℝ) < rhoHat p / 16 := by positivity
  have hJB : J ∈ Metric.ball (KAM.realInclusion (a + b) q) (rhoHat p / 16) := by
    rw [mem_ball, dist_eq_norm]
    refine lt_of_le_of_lt ?_ hJc
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
    have e : (J - KAM.realInclusion (a + b) q) j = ((J j).im : ℂ) * Complex.I := by
      simp only [Pi.sub_apply, KAM.realInclusion_apply, hq]
      apply Complex.ext <;> simp
    have e2 : ‖(J j).im * Complex.I‖ = |(J j).im| := by simp
    rw [e, e2]
    have : (J j).im = (J j - c j).im := by simp [hc, KAM.realInclusion_apply]
    rw [this]
    exact (Complex.abs_im_le_norm _).trans (norm_le_pi_norm (J - c) j)
  have hU' := isOpen_actionNbhd' Dp (rhoHat p / 16)
  have hhol : DifferentiableOn ℂ (fun J => h J + g J) (KAM.actionNbhd Dp (rhoHat p / 16)) :=
    H'.holo
  have hball : Metric.ball (KAM.realInclusion (a + b) q) (rhoHat p / 16) ⊆
      KAM.actionNbhd Dp (rhoHat p / 16) := actionNbhd_ball hqD
  have hsb : 0 < sbar + p.s / 12 := by linarith [hw.1]
  have hF : DifferentiableOn ℂ (freq (fun J => h J + g J))
      (Metric.ball (KAM.realInclusion (a + b) q) (rhoHat p / 16)) :=
    fun z hz => (differentiableAt_freq hU' hhol (hball hz)).differentiableWithinAt
  have hrealF : ∀ x : Fin (a + b) → ℝ, KAM.realInclusion (a + b) x ∈
      Metric.ball (KAM.realInclusion (a + b) q) (rhoHat p / 16) →
      ∀ i, (freq (fun J => h J + g J) (KAM.realInclusion (a + b) x) i).im = 0 := fun x hx i =>
    freq_im_zero hhol hsb H'.real_h (hball hx) i
  have hsch := schwarz_vec hρ' hF hrealF
  have hconj : (fun i => starRingEnd ℂ (J i)) ∈
      Metric.ball (KAM.realInclusion (a + b) q) (rhoHat p / 16) := by
    rw [mem_ball, dist_eq_norm] at hJB ⊢
    rw [pi_norm_lt_iff hρ'] at hJB ⊢
    intro i
    have := hJB i
    simp only [Pi.sub_apply, KAM.realInclusion_apply] at this ⊢
    have e : starRingEnd ℂ (J i) - ((q i : ℝ) : ℂ) = starRingEnd ℂ (J i - ((q i : ℝ) : ℂ)) := by
      simp
    rw [e, Complex.norm_conj]; exact this
  have hfreq_c : ∀ j, (freq h c j).im = 0 := fun j =>
    freq_im_zero H.holo (by linarith [hw.1]) H.real_h
      (mem_actionNbhd_of_mem H.positive.2.2.1 hI) j
  have hEq : freq (fun J => h J + g J) (fun i => starRingEnd ℂ (J i)) =
      freq (fun J => h J + g J) J := by
    rw [hsch J hJB, hJe]
    funext j
    exact Complex.conj_eq_iff_im.mpr (hfreq_c j)
  have hinj := H'.injective (hball hconj) (hball hJB) hEq
  exact Complex.conj_eq_iff_im.mp (congrFun hinj i)

end KamHyp

end KAM.Planetary

end
