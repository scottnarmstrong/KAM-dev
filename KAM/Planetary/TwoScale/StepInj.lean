/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.StepHess2
public import KAM.Planetary.TwoScale.StepMono

/-!
# Two-scale KAM step: bounds on `∂g` and injectivity of `ω₊` (`stepP:p3:st-inj`)

`g` is holomorphic on `D_{R/2}` with `|g| ≤ 5E/4`. Then `|∂g| ≤ 5E/R`, `‖∂²g‖ ≤ 80E/R²` on
`D_{R/4}`, and `ω₊ = ω₀ + ∂g` is injective on `D_{R/8}`, by the ball lemma `ball` and the mean value
inequality for `∂g` (source `P3a`, step `st-inj`). Design package P23-14.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

theorem ball_subset_actionNbhd {n : ℕ} {D : Set (Fin n → ℝ)} {I : Fin n → ℂ} {r₁ r₂ : ℝ}
    (hI : I ∈ KAM.actionNbhd D r₁) : Metric.ball I r₂ ⊆ KAM.actionNbhd D (r₁ + r₂) := by
  obtain ⟨J, hJ, hlt⟩ := hI
  intro z hz
  refine ⟨J, hJ, ?_⟩
  rw [mem_ball, dist_eq_norm] at hz
  calc ‖z - fun i => (J i : ℂ)‖ = ‖(z - I) + (I - fun i => (J i : ℂ))‖ := by congr 1; abel
    _ ≤ ‖z - I‖ + ‖I - fun i => (J i : ℂ)‖ := norm_add_le _ _
    _ < r₂ + r₁ := add_lt_add hz hlt
    _ = r₁ + r₂ := add_comm _ _

theorem norm_freq_le {n : ℕ} {g : (Fin n → ℂ) → ℂ} {I : Fin n → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hg : ‖fderiv ℂ g I‖ ≤ c) : ‖freq g I‖ ≤ c := by
  refine (pi_norm_le_iff_of_nonneg hc).2 fun i => ?_
  refine ((fderiv ℂ g I).le_opNorm _).trans ?_
  simp only [Pi.norm_single, norm_one, mul_one]
  exact hg

namespace KamHyp

variable {g : (Fin (a + b) → ℂ) → ℂ}

theorem g_deriv_bounds (H : KamHyp D sbar p h f)
    (hg : DifferentiableOn ℂ g (KAM.actionNbhd D (rhoHat p / 2)))
    (hgb : ∀ I ∈ KAM.actionNbhd D (rhoHat p / 2), ‖g I‖ ≤ 5 / 4 * p.E)
    {I : Fin (a + b) → ℂ} (hI : I ∈ KAM.actionNbhd D (rhoHat p / 4)) :
    ‖fderiv ℂ g I‖ ≤ 5 * p.E / rhoHat p ∧
      ‖fderiv ℂ (fderiv ℂ g) I‖ ≤ 80 * p.E / rhoHat p ^ 2 := by
  have hR := H.R_pos
  obtain ⟨h1, h2⟩ := g_bounds (by positivity) hg hgb (A := 5 / 4 * p.E)
    (show I ∈ KAM.actionNbhd D (rhoHat p / 2 / 2) by
      have : rhoHat p / 2 / 2 = rhoHat p / 4 := by ring
      rw [this]; exact hI)
  exact ⟨h1.trans_eq (by field_simp; ring), h2.trans_eq (by field_simp; ring)⟩

theorem freq_g_le (H : KamHyp D sbar p h f)
    (hg : DifferentiableOn ℂ g (KAM.actionNbhd D (rhoHat p / 2)))
    (hgb : ∀ I ∈ KAM.actionNbhd D (rhoHat p / 2), ‖g I‖ ≤ 5 / 4 * p.E)
    {I : Fin (a + b) → ℂ} (hI : I ∈ KAM.actionNbhd D (rhoHat p / 4)) :
    ‖freq g I‖ ≤ 5 * p.E / rhoHat p := by
  have hR := H.R_pos
  have hE := H.positive.2.2.2.1
  exact norm_freq_le (by positivity) (H.g_deriv_bounds hg hgb hI).1

/-- Mean value inequality for `∂g` on a convex subset of the quarter-radius neighbourhood. -/
theorem freq_g_lip (H : KamHyp D sbar p h f)
    (hg : DifferentiableOn ℂ g (KAM.actionNbhd D (rhoHat p / 2)))
    (hgb : ∀ I ∈ KAM.actionNbhd D (rhoHat p / 2), ‖g I‖ ≤ 5 / 4 * p.E)
    {S : Set (Fin (a + b) → ℂ)} (hS : Convex ℝ S) (hSU : S ⊆ KAM.actionNbhd D (rhoHat p / 4))
    {x y : Fin (a + b) → ℂ} (hx : x ∈ S) (hy : y ∈ S) :
    ‖freq g x - freq g y‖ ≤ 80 * p.E / rhoHat p ^ 2 * ‖x - y‖ := by
  have hR := H.R_pos
  have hE := H.positive.2.2.2.1
  have hβ0 : 0 ≤ 80 * p.E / rhoHat p ^ 2 := by positivity
  have hU := isOpen_actionNbhd' D (rhoHat p / 2)
  have hU2 : ∀ z ∈ S, z ∈ KAM.actionNbhd D (rhoHat p / 2) := fun z hz =>
    actionNbhd_mono (by linarith) (hSU hz)
  have hd : ∀ z ∈ S, DifferentiableAt ℂ (freq g) z := fun z hz =>
    differentiableAt_freq hU hg (hU2 z hz)
  have hc : ∀ z ∈ S, ∀ v, ‖fderiv ℂ (freq g) z v‖ ≤ 80 * p.E / rhoHat p ^ 2 * ‖v‖ := by
    intro z hz v
    have hgd : DifferentiableAt ℂ (fderiv ℂ g) z :=
      (differentiableOn_fderiv_of_isOpen hU hg).differentiableAt (hU.mem_nhds (hU2 z hz))
    exact freq_g_fderiv hgd (H.g_deriv_bounds hg hgb (hSU hz)).2 v
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have := coord_mvt hS hβ0 j hd (fun z hz v => (norm_le_pi_norm _ j).trans (hc z hz v)) hx hy
  simpa using this

/-- `stepP:p3:st-inj`: `ω₊ = ω₀ + ∂g` is injective on `D_{R/8}`. -/
theorem freq_inj (H : KamHyp D sbar p h f)
    (hg : DifferentiableOn ℂ g (KAM.actionNbhd D (rhoHat p / 2)))
    (hgb : ∀ I ∈ KAM.actionNbhd D (rhoHat p / 2), ‖g I‖ ≤ 5 / 4 * p.E) :
    Set.InjOn (freq (fun J => h J + g J)) (KAM.actionNbhd D (rhoHat p / 8)) := by
  intro I hI I' hI' heq
  have hR := H.R_pos
  have hE := H.positive.2.2.2.1
  have hMb := H.positive.2.2.2.2.2.2.1
  obtain ⟨-, -, hb3⟩ := H.beta_facts
  have hRρ := H.R_le_ρ
  have hU := isOpen_actionNbhd' D (rhoHat p / 2)
  have hhU : DifferentiableOn ℂ h (KAM.actionNbhd D (rhoHat p / 2)) :=
    H.holo.mono (actionNbhd_mono (by linarith))
  have hI4 : I ∈ KAM.actionNbhd D (rhoHat p / 4) := actionNbhd_mono (by linarith) hI
  have hI4' : I' ∈ KAM.actionNbhd D (rhoHat p / 4) := actionNbhd_mono (by linarith) hI'
  have hI2 : I ∈ KAM.actionNbhd D (rhoHat p / 2) := actionNbhd_mono (by linarith) hI
  have hI2' : I' ∈ KAM.actionNbhd D (rhoHat p / 2) := actionNbhd_mono (by linarith) hI'
  rw [freq_add (hhU.differentiableAt (hU.mem_nhds hI2)) (hg.differentiableAt (hU.mem_nhds hI2)),
    freq_add (hhU.differentiableAt (hU.mem_nhds hI2')) (hg.differentiableAt (hU.mem_nhds hI2'))]
    at heq
  have hw : freq h I - freq h I' = freq g I' - freq g I := by
    have := congrFun heq
    funext i; have := this i; simp only [Pi.add_apply, Pi.sub_apply] at this ⊢; linear_combination this
  have hw1 : ‖freq h I - freq h I'‖ ≤ 10 * p.E / rhoHat p := by
    rw [hw]
    have := norm_sub_le (freq g I') (freq g I)
    have h1 := H.freq_g_le hg hgb hI4
    have h2 := H.freq_g_le hg hgb hI4'
    linarith [show 10 * p.E / rhoHat p = 5 * p.E / rhoHat p + 5 * p.E / rhoHat p by ring]
  -- the ball lemma for `ω₀` on `D_ρ`
  have hΩ := isOpen_actionNbhd' D p.ρ
  have hballΩ : Metric.ball I (rhoHat p / 8) ⊆ KAM.actionNbhd D p.ρ := by
    refine (ball_subset_actionNbhd hI).trans (actionNbhd_mono ?_)
    linarith
  have hF : DifferentiableOn ℂ (freq h) (KAM.actionNbhd D p.ρ) := fun z hz =>
    (differentiableAt_freq hΩ H.holo hz).differentiableWithinAt
  have hder : ∀ x ∈ KAM.actionNbhd D p.ρ, ∃ A : (Fin (a + b) → ℂ) ≃L[ℂ] (Fin (a + b) → ℂ),
      (A : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ)) = fderiv ℂ (freq h) x ∧
        ‖(A.symm : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ))‖ ≤ p.Mbar := by
    intro x hx
    obtain ⟨-, -, A, hA, hA1, -⟩ := H.hessian x hx
    exact ⟨A, hA, hA1⟩
  obtain ⟨hb1, hb2⟩ := KAM.Planetary.ball hΩ hF H.injective hMb
    (show 0 < rhoHat p / 8 by positivity) hder hballΩ
  have hlt : ‖freq h I' - freq h I‖ < rhoHat p / 8 / p.Mbar := by
    have h1 : 10 * p.E / rhoHat p < rhoHat p / 8 / p.Mbar := by
      rw [div_lt_div_iff₀ hR hMb]
      have : p.Mbar * (80 * p.E) ≤ 1 / 100 * rhoHat p ^ 2 := by
        have h5 : p.Mbar * (80 * p.E) / rhoHat p ^ 2 ≤ 1 / 100 := by
          rw [mul_div_assoc]; exact hb3
        exact (div_le_iff₀ (by positivity)).1 h5
      nlinarith [sq_nonneg (rhoHat p)]
    rw [norm_sub_rev]; exact lt_of_le_of_lt hw1 h1
  have hmem : freq h I' ∈ Metric.ball (freq h I) (rhoHat p / 8 / p.Mbar) := by
    rw [mem_ball, dist_eq_norm]; exact hlt
  obtain ⟨I'', hI'', hI''e⟩ := hb1 hmem
  have hI''Ω : I'' ∈ KAM.actionNbhd D p.ρ := hballΩ hI''
  have hI'Ω : I' ∈ KAM.actionNbhd D p.ρ := actionNbhd_mono (by linarith) hI'
  have heq2 : I'' = I' := H.injective hI''Ω hI'Ω hI''e
  subst heq2
  have hself : freq h I ∈ Metric.ball (freq h I) (rhoHat p / 8 / p.Mbar) :=
    mem_ball_self (by positivity)
  have hIb : I ∈ Metric.ball I (rhoHat p / 8) := mem_ball_self (by positivity)
  have key := hb2 I hIb I'' hI'' hself hmem
  have hconv : Convex ℝ (Metric.ball I (rhoHat p / 8)) := convex_ball _ _
  have hSU : Metric.ball I (rhoHat p / 8) ⊆ KAM.actionNbhd D (rhoHat p / 4) := by
    refine (ball_subset_actionNbhd hI).trans (actionNbhd_mono ?_)
    linarith
  have hlip := H.freq_g_lip hg hgb hconv hSU hI'' hIb
  have e2 : ‖freq h I - freq h I''‖ = ‖freq g I'' - freq g I‖ := by rw [hw]
  have hn : 0 ≤ ‖I - I''‖ := norm_nonneg _
  rw [e2, norm_sub_rev (freq g I'') (freq g I)] at key
  have key2 : ‖I - I''‖ ≤ p.Mbar * (80 * p.E / rhoHat p ^ 2 * ‖I'' - I‖) :=
    key.trans (mul_le_mul_of_nonneg_left (by rw [norm_sub_rev (freq g I) (freq g I'')]; exact hlip)
      hMb.le)
  rw [norm_sub_rev I'' I] at key2
  have : ‖I - I''‖ ≤ 1 / 100 * ‖I - I''‖ := by
    refine key2.trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hb3 hn
  have : ‖I - I''‖ = 0 := by nlinarith
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

end KamHyp

end KAM.Planetary

end
