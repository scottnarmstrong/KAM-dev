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
  have hA : ∀ w ∈ coefficientDom D p.ρ (sbar + p.s), ‖f w‖ ≤ p.E := sup_le_wbound H.f_class H.f_bound
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

end KAM.Planetary

end
