/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepPlusClass
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `∫₀¹ {R(t),F} ∘ φ^t` is a smoothing Hamiltonian on `D_+` (blueprint-W `bpW:w5:new-ham` (ii))

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

variable {a p pb s r σ η Mf e₁ : ℝ} [Fact (0 < r)]

theorem stepPlus_integral_smoothing (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hσs : 5 * σ < s) (hη0 : 0 < η) (hη : η ≤ 1 / 8)
    (T : HomTaylor_gen a p pb s) (FT : HomTaylor_gen a p pb (s - σ)) (he₁ : 0 ≤ e₁)
    (hT : HomFieldBound_gen ha hp hpb r e₁ T)
    (hTn : HomFieldBound_gen ha hp hpb r (2 * e₁) (homNhatTaylor_gen T))
    (hF : HomFieldBound_gen ha hp hpb r Mf FT) (hMf0 : 0 < Mf) (hMf : Mf ≤ σ / 1024) :
    let ι := stepEmbedCLM a p pb hpb r
    let Z := stepFieldS ha hp hpb FT r
    let B := stepSympCLM (q := p) (q' := p) ha (by linarith) r
    DifferentiableOn ℂ (fun w => ∫ t in (0 : ℝ)..1,
        stepGfam ha hp hpb T FT t (holoFlow (smoothField ι Z) t w))
      (stepDomain r (s - 5 * σ) (η * r)) ∧
    DifferentiableOn ℂ (fun w => ∫ t in (0 : ℝ)..1, yfam ι Z (stepZgfam ha hp hpb T FT) t w)
      (stepDomain r (s - 5 * σ) (η * r)) ∧
    ∀ w ∈ stepDomain r (s - 5 * σ) (η * r),
      HasFDerivAt (fun w => ∫ t in (0 : ℝ)..1,
        stepGfam ha hp hpb T FT t (holoFlow (smoothField ι Z) t w))
        ((B.comp ι) (∫ t in (0 : ℝ)..1, yfam ι Z (stepZgfam ha hp hpb T FT) t w)) w := by
  intro ι Z B
  have hr : 0 < r := Fact.out
  have hMδ : Mf < σ / 4 := by linarith
  have hFlow := stepFlowHyp_concrete' (S := s) ha hp hpb FT r hσ hσ1 (by linarith : 2 * σ < s)
    le_rfl hF hMf0 hMδ
  have hVd : ∀ z ∈ stepDomain r (s - σ) r,
      z ∈ {z : StepPhase r | (StepPhase.toK z).1 ∈ complexStrip 2 (s - σ)} := fun z hz =>
    stepDomain_theta_mem le_rfl hz
  have hZ : DifferentiableOn ℂ Z (stepDomain r (s - σ) r) :=
    (stepFieldS_differentiableOn_theta ha hp hpb FT).mono hVd
  have hb : ∀ z ∈ stepDomain r (s - σ) r, ‖Z z‖ ≤ Mf := fun z hz =>
    stepFieldS_bound ha hp hpb FT r hF le_rfl hz
  have hι : ∀ g, ‖ι g‖ ≤ ‖g‖ := norm_stepEmbedCLM_apply_le a p pb hpb r
  have hskew : ∀ z ∈ stepDomain r (s - σ) r, ∀ x y,
      B (fderiv ℂ (smoothField ι Z) z x) y + B x (fderiv ℂ (smoothField ι Z) z y) = 0 :=
    fun z hz x y => stepFieldS_skew ha hp hpb FT r (stepDomain_theta_mem le_rfl hz) x y
  have hU'sub : stepDomain r (s - 5 * σ) (η * r) ⊆ stepDomain r (s - 3 * σ) (r / 4) :=
    stepDomain_mono' (by linarith) (by positivity) (by nlinarith)
  have hU'U : stepDomain r (s - 5 * σ) (η * r) ⊆ stepDomain r (s - 2 * σ) (r / 2) :=
    hU'sub.trans (stepDomain_mono' (by linarith) (by positivity) (by linarith))
  have hδ₂ : 0 < σ / 16 := by positivity
  have hMδ₂ : Mf < σ / 16 := by linarith
  have hball : ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), ∀ z ∈ ball w (σ / 16),
      ball z (σ / 16) ⊆ stepDomain r (s - 2 * σ) (r / 2) := by
    intro w hw z hz y hy
    have hm := stepDomain_U_margin hσ hσ1 (by linarith : 3 * σ < s) (hU'sub hw)
    refine hm ?_
    rw [mem_ball] at hz hy ⊢
    have := dist_triangle y z w
    linarith
  have hN : ∀ w ∈ stepDomain r (s - 5 * σ) (η * r), ∀ t ∈ Icc (0 : ℝ) 1,
      ‖transNop ι Z t w‖ ≤ 1 / 128 := fun w hw t ht =>
    stepN_bound ha hp hpb hσ hσ1 (by linarith : 3 * σ < s) hFlow hZ hb hMf (hU'sub hw)
      ⟨by linarith [ht.1], ht.2⟩
  have hYb : 0 ≤ 8 * e₁ * Mf / σ := by positivity
  have hY0 := fun t (ht : t ∈ Icc (0 : ℝ) 1) z (hz : z ∈ stepDomain r (s - 2 * σ) (r / 2)) =>
    norm_stepZgfam_le hσ hσ1 (by linarith : 2 * σ < s) he₁ hMf0.le hT hTn hF ht hz
  have hcpos : 0 ≤ (4 * Real.pi + 1) * r ^ 2 * (e₁ * Mf) := by positivity
  refine newHam_integral_smoothing hFlow hZ hb hι B hskew (stepDomain_isOpen _ _ _) hδ₂ hMδ₂
    (stepDomain_isOpen _ _ _) hU'U hball (q := 1 / 128) (by norm_num) hN
    (g := stepGfam ha hp hpb T FT) (Zg := stepZgfam ha hp hpb T FT)
    (Y0 := 8 * e₁ * Mf / σ) (Lt := 12 * e₁ * Mf / σ)
    (Gb := 2 * ((4 * Real.pi + 1) * r ^ 2 * (e₁ * Mf)))
    (Lg := 3 * ((4 * Real.pi + 1) * r ^ 2 * (e₁ * Mf))) hYb (by positivity) (by positivity)
    (by positivity) ?_ ?_ ?_ ?_ ?_ ?_
  · intro t ht z hz
    exact stepGfam_hasFDerivAt hσ (by linarith : 2 * σ < s) t hz
  · intro t ht
    exact stepZgfam_differentiableOn hσ hσ1 (by linarith : 2 * σ < s) he₁ hMf0.le hT hTn hF t
  · intro t ht z hz
    exact hY0 t ht z hz
  · intro t ht t' ht' z hz
    exact norm_stepZgfam_sub_le hσ hσ1 (by linarith : 2 * σ < s) he₁ hMf0.le hT hTn hF hz
  · intro t ht z hz
    exact norm_stepGfam_le hσ hσ1 (by linarith : 2 * σ < s) he₁ hMf0.le hT hTn hF ht hz
  · intro t ht t' ht' z hz
    exact norm_stepGfam_sub_le hσ hσ1 (by linarith : 2 * σ < s) he₁ hMf0.le hT hTn hF hz

end KAM.Wave
