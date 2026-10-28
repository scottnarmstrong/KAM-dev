/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.ToriInvField
public import KAM.Planetary.TwoScale.ToriSetup

/-!
# Two-scale KAM: the stage field error (`stepP:p3:inv-err`)

For one stage Hamiltonian `h + f` with `KamHyp`, `field_err` bounds `‖(ω, 0) − X_{h+f}(θ, I)‖ ≤
M‖I − c‖ + E/δ` for a frequency `ω = ω(c)`, `c ∈ D`, and a real point `(θ, I)` with
`I ∈ Re(D)_{ρ/2}`, `δ = min(ρ/2, s̄/4π)`: the frequency increment is the mean value bound of
`freq_lip`, and the two partial derivatives of `f` (the terms (2), (3) of P3b L137–141) are bounded
together by the Cauchy estimate `‖Df‖ ≤ E/δ` on a polydisc of radius `δ` about `(θ, I)`.
Design package P23-20.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

/-- Frequency increments are `M`-Lipschitz on the ball of radius `R̂` about a real point. -/
theorem freq_lip (H : KamHyp D sbar p h f) {J : Fin (a + b) → ℝ} (hJ : J ∈ D)
    {I : Fin (a + b) → ℂ} (hI : ‖I - KAM.realInclusion (a + b) J‖ < rhoHat p) :
    ‖freq h I - freq h (KAM.realInclusion (a + b) J)‖ ≤
      p.M * ‖I - KAM.realInclusion (a + b) J‖ := by
  have hR := H.R_pos
  have hM := H.positive.2.2.2.2.1
  have hsub : Metric.ball (KAM.realInclusion (a + b) J) (rhoHat p) ⊆ KAM.actionNbhd D p.ρ :=
    (actionNbhd_ball hJ).trans (actionNbhd_mono H.R_le_ρ)
  have hopen := isOpen_actionNbhd' D p.ρ
  have hF : ∀ x ∈ Metric.ball (KAM.realInclusion (a + b) J) (rhoHat p),
      DifferentiableAt ℂ (freq h) x := fun x hx =>
    differentiableAt_freq hopen H.holo (hsub hx)
  have hmem : I ∈ Metric.ball (KAM.realInclusion (a + b) J) (rhoHat p) := by
    simpa [dist_eq_norm] using hI
  have hc : ∀ x ∈ Metric.ball (KAM.realInclusion (a + b) J) (rhoHat p), ∀ v (j : Fin (a + b)),
      ‖fderiv ℂ (freq h) x v j‖ ≤ p.M * ‖v‖ := by
    intro x hx v j
    exact (norm_le_pi_norm _ j).trans
      (((fderiv ℂ (freq h) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (H.hessian x (hsub hx)).1 (norm_nonneg _)))
  have hcen : KAM.realInclusion (a + b) J ∈ Metric.ball (KAM.realInclusion (a + b) J) (rhoHat p) :=
    Metric.mem_ball_self hR
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  exact coord_mvt (convex_ball _ _) (by positivity) j hF (fun x hx v => hc x hx v j) hmem hcen

/-- Cauchy estimate for `f` on a polydisc of radius `δ = min (ρ/2) (s̄/4π)` about a real point
with action in `Re(D)_{ρ/2}`. -/
theorem fderiv_f_le (H : KamHyp D sbar p h f) {θ I J : Fin (a + b) → ℝ} (hJ : J ∈ D)
    (hIJ : ‖I - J‖ < p.ρ / 2) :
    ‖fderiv ℂ f (KAM.realInclusion₂ (a + b) (θ, I))‖ ≤
      p.E / min (p.ρ / 2) (sbar / (4 * π)) := by
  have hρ := H.positive.2.2.1
  have hs0 := H.positive.2.1
  have hsb : 0 < sbar := by have := H.widths.1; linarith
  have hδ : 0 < min (p.ρ / 2) (sbar / (4 * π)) := lt_min (by positivity) (by positivity)
  have hf : DifferentiableOn ℂ f (coefficientDom D p.ρ (sbar + p.s)) :=
    H.f_class.differentiableOn
  have hA : ∀ w ∈ coefficientDom D p.ρ (sbar + p.s), ‖f w‖ ≤ p.E :=
    sup_le_wbound H.f_class H.f_bound
  refine KAM.norm_fderiv_le_of_closedBall (isOpen_coefficientDom _ _ _) hf hδ ?_ hA
  intro z hz
  have hz' : ‖z - KAM.realInclusion₂ (a + b) (θ, I)‖ ≤ min (p.ρ / 2) (sbar / (4 * π)) := by
    simpa [mem_closedBall, dist_eq_norm] using hz
  simp only [Prod.norm_def, max_le_iff, Prod.fst_sub, Prod.snd_sub, KAM.realInclusion₂_apply]
    at hz'
  obtain ⟨h1, h2⟩ := hz'
  rw [(conv_data D p.ρ (sbar + p.s)).2]
  refine ⟨fun k => ?_, ⟨J, hJ, ?_⟩⟩
  · have e1 : |(z.1 k).im| ≤ ‖z.1 - KAM.realInclusion (a + b) θ‖ := by
      have : (z.1 k).im = ((z.1 - KAM.realInclusion (a + b) θ) k).im := by simp
      rw [this]
      exact (Complex.abs_im_le_norm _).trans (norm_le_pi_norm (z.1 - KAM.realInclusion (a + b) θ) k)
    have e2 : sbar / (4 * π) < (sbar + p.s) / (2 * π) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.pi_pos]
    exact e1.trans_lt (lt_of_le_of_lt (h1.trans (min_le_right _ _)) e2)
  · have e3 : ‖z.2 - KAM.realInclusion (a + b) I‖ ≤ p.ρ / 2 := h2.trans (min_le_left _ _)
    have e4 : ‖KAM.realInclusion (a + b) I - KAM.realInclusion (a + b) J‖ < p.ρ / 2 := by
      rw [← map_sub, KAM.norm_realInclusion]; exact hIJ
    calc ‖z.2 - KAM.realInclusion (a + b) J‖
        ≤ ‖z.2 - KAM.realInclusion (a + b) I‖ +
            ‖KAM.realInclusion (a + b) I - KAM.realInclusion (a + b) J‖ := by
          have := norm_add_le (z.2 - KAM.realInclusion (a + b) I)
            (KAM.realInclusion (a + b) I - KAM.realInclusion (a + b) J)
          simpa using this
      _ < p.ρ := by linarith

/-- The stage field error: for `c ∈ D`, `ω = ω(c)`, a real point `(θ, I)` with `I` within `ρ/2` of
`D` and within `R̂` of `c`, `‖(ω, 0) − X_{h+f}(θ, I)‖ ≤ M‖I − c‖ + E/δ`. -/
theorem field_err (H : KamHyp D sbar p h f) {c J : Fin (a + b) → ℝ} (hc : c ∈ D) (hJ : J ∈ D)
    {θ I : Fin (a + b) → ℝ} (hIJ : ‖I - J‖ < p.ρ / 2) (hIc : ‖I - c‖ < rhoHat p) :
    ‖((realFreq h c, 0) : Phase (a + b)) -
      KAM.hamiltonianVectorField (fun z : Phase (a + b) =>
        (h (KAM.realInclusion (a + b) z.2) + f (KAM.realInclusion₂ (a + b) z)).re) (θ, I)‖ ≤
      p.M * ‖I - c‖ + p.E / min (p.ρ / 2) (sbar / (4 * π)) := by
  have hρ := H.positive.2.2.1
  have hs0 := H.positive.2.1
  have hM := H.positive.2.2.2.2.1
  have hE := H.positive.2.2.2.1
  have hsb : 0 < sbar := by have := H.widths.1; linarith
  have hδ : 0 < min (p.ρ / 2) (sbar / (4 * π)) := lt_min (by positivity) (by positivity)
  have hW := isOpen_coefficientDom D p.ρ (sbar + p.s)
  set W := coefficientDom D p.ρ (sbar + p.s) with hWdef
  set G : CPhase (a + b) → ℂ := fun z => h z.2 + f z with hG
  have hmemW : ∀ z ∈ W, z.2 ∈ KAM.actionNbhd D p.ρ := fun z hz => by
    rw [hWdef, (conv_data D p.ρ (sbar + p.s)).2] at hz; exact hz.2
  have hGd : DifferentiableOn ℂ G W :=
    (H.holo.comp differentiable_snd.differentiableOn hmemW).add H.f_class.differentiableOn
  have hreal : ∀ x : Phase (a + b), KAM.realInclusion₂ (a + b) x ∈ W →
      (G (KAM.realInclusion₂ (a + b) x)).im = 0 := fun x hx => by
    have h1 := H.real_h x hx
    have h2 := H.real_f x hx
    simp only [hG, Complex.add_im]
    simp only at h1
    rw [h1, h2, add_zero]
  have hz : KAM.realInclusion₂ (a + b) (θ, I) ∈ W := by
    rw [hWdef, (conv_data D p.ρ (sbar + p.s)).2]
    refine ⟨fun k => ?_, ⟨J, hJ, ?_⟩⟩
    · simp only [KAM.realInclusion₂_apply, KAM.realInclusion_apply, Complex.ofReal_im, abs_zero]
      positivity
    · show ‖KAM.realInclusion (a + b) I - KAM.realInclusion (a + b) J‖ < p.ρ
      rw [← map_sub, KAM.norm_realInclusion]; linarith
  have hX := KAM.hamiltonianVectorField_eq_of_real hW hGd hreal hz
    (Eventually.of_forall fun _ => rfl)
  have hDf := fderiv_f_le H hJ hIJ (θ := θ)
  set w := KAM.realInclusion₂ (a + b) (θ, I) with hw
  have hhd : DifferentiableAt ℂ h w.2 :=
    H.holo.differentiableAt ((isOpen_actionNbhd' D p.ρ).mem_nhds (hmemW w hz))
  have hfd : DifferentiableAt ℂ f w := H.f_class.differentiableOn.differentiableAt (hW.mem_nhds hz)
  have hGder : ∀ v, fderiv ℂ G w v = fderiv ℂ h w.2 v.2 + fderiv ℂ f w v := by
    intro v
    have h1 : HasFDerivAt (fun z : CPhase (a + b) => h z.2)
        ((fderiv ℂ h w.2).comp (ContinuousLinearMap.snd ℂ _ _)) w :=
      hhd.hasFDerivAt.comp w hasFDerivAt_snd
    have := (h1.add hfd.hasFDerivAt).fderiv
    have e : G = (fun z : CPhase (a + b) => h z.2) + f := rfl
    rw [e, this]; rfl
  have hI' : KAM.realInclusion (a + b) c ∈ KAM.actionNbhd D p.ρ :=
    ⟨c, hc, by
      show ‖KAM.realInclusion (a + b) c - KAM.realInclusion (a + b) c‖ < p.ρ
      rw [sub_self, norm_zero]; exact hρ⟩
  have hfr := freq_realInclusion_eq H.holo (by linarith : 0 < sbar + p.s) H.real_h hI'
  have hl := freq_lip H hc (I := KAM.realInclusion (a + b) I) (by
    rw [← map_sub, KAM.norm_realInclusion]; exact hIc)
  rw [← map_sub, KAM.norm_realInclusion] at hl
  have hDf1 : ∀ v : CPhase (a + b), ‖v‖ ≤ 1 →
      ‖fderiv ℂ f w v‖ ≤ p.E / min (p.ρ / 2) (sbar / (4 * π)) := fun v hv =>
    ((fderiv ℂ f w).le_opNorm v).trans
      ((mul_le_mul hDf hv (norm_nonneg _) (by positivity)).trans (by rw [mul_one]))
  have hP : 0 ≤ p.M * ‖I - c‖ + p.E / min (p.ρ / 2) (sbar / (4 * π)) := by positivity
  have hX' : KAM.realInclusion₂ (a + b) (KAM.hamiltonianVectorField (fun z : Phase (a + b) =>
      (h (KAM.realInclusion (a + b) z.2) + f (KAM.realInclusion₂ (a + b) z)).re) (θ, I)) =
      KAM.hamiltonianVectorFieldℂ G w := hX
  rw [← KAM.norm_realInclusion₂, map_sub, hX']
  simp only [KAM.hamiltonianVectorFieldℂ, KAM.realInclusion₂_apply, map_zero, Prod.norm_def,
    Prod.fst_sub, Prod.snd_sub]
  refine max_le ((pi_norm_le_iff_of_nonneg hP).2 fun i => ?_)
    ((pi_norm_le_iff_of_nonneg hP).2 fun i => ?_)
  · rw [Pi.sub_apply, hGder, ← hfr]
    have e1 : ‖fderiv ℂ f w (0, Pi.single i 1)‖ ≤ p.E / min (p.ρ / 2) (sbar / (4 * π)) :=
      hDf1 _ (by rw [Prod.norm_def]; simp [Pi.norm_single])
    have e2 : ‖freq h (KAM.realInclusion (a + b) c) i - freq h (KAM.realInclusion (a + b) I) i‖ ≤
        p.M * ‖I - c‖ := by
      rw [norm_sub_rev]
      exact (norm_le_pi_norm _ i).trans hl
    have e3 : fderiv ℂ h w.2 (Pi.single i 1) = freq h (KAM.realInclusion (a + b) I) i := rfl
    calc ‖freq h (KAM.realInclusion (a + b) c) i -
          (fderiv ℂ h w.2 (0, Pi.single i 1).2 + fderiv ℂ f w (0, Pi.single i 1))‖
        = ‖(freq h (KAM.realInclusion (a + b) c) i - freq h (KAM.realInclusion (a + b) I) i) -
            fderiv ℂ f w (0, Pi.single i 1)‖ := by
          simp only [e3]; ring_nf
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add e2 e1)
  · 
    have e1 : ‖fderiv ℂ f w (Pi.single i 1, 0)‖ ≤ p.E / min (p.ρ / 2) (sbar / (4 * π)) :=
      hDf1 _ (by rw [Prod.norm_def]; simp [Pi.norm_single])
    have : 0 ≤ p.M * ‖I - c‖ := by positivity
    simp only [Pi.sub_apply, Pi.zero_apply, zero_sub, neg_neg]
    rw [hGder]
    simp only [map_zero, zero_add]
    exact e1.trans (by linarith)

end KAM.Planetary

end
