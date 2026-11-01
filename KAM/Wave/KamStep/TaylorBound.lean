/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.TaylorData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Boundedness of the Taylor components (blueprint-W `bpW:w5:taylor` (i), step `t-comp`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`kamNorm_fderiv_normal_le`: along a purely normal direction `d = (0,0,u,v)` the derivative of the
field at `(θ,0,0,0)` has `kamNorm r (DX d) ≤ ε (‖u‖+‖v‖)/r` (Cauchy in the single variable `λ`,
without any margin in `θ`). With this the components of `R` are bounded on the strip.
-/

@[expose] public noncomputable section

open Metric Set

namespace KAM.Wave

open KAM

variable {a p pb s r : ℝ} {X : KamPhase → KamPhase}

theorem norm_stepZ_le (Y : KamPhase) : ‖stepZ Y‖ ≤ ‖Y.2.2.1‖ + ‖Y.2.2.2‖ := by
  obtain ⟨θ, y, u, v⟩ := Y
  rw [stepZ_apply, norm_smul]
  have h1 : ‖homSqrt2⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_homSqrt2]
    exact inv_le_one_of_one_le₀ (by
      have : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by norm_num)
      exact this)
  calc ‖homSqrt2⁻¹‖ * ‖u + Complex.I • v‖ ≤ 1 * (‖u‖ + ‖v‖) := by
        refine mul_le_mul h1 ?_ (norm_nonneg _) zero_le_one
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Complex.norm_I, one_mul]
    _ = ‖u‖ + ‖v‖ := one_mul _

theorem norm_stepZb_le (Y : KamPhase) : ‖stepZb Y‖ ≤ ‖Y.2.2.1‖ + ‖Y.2.2.2‖ := by
  obtain ⟨θ, y, u, v⟩ := Y
  rw [stepZb_apply, norm_smul]
  have h1 : ‖homSqrt2⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_homSqrt2]
    exact inv_le_one_of_one_le₀ (by
      have : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by norm_num)
      exact this)
  calc ‖homSqrt2⁻¹‖ * ‖u - Complex.I • v‖ ≤ 1 * (‖u‖ + ‖v‖) := by
        refine mul_le_mul h1 ?_ (norm_nonneg _) zero_le_one
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, Complex.norm_I, one_mul]
    _ = ‖u‖ + ‖v‖ := one_mul _

theorem norm_normal_le_kamNorm (hr : 0 < r) {ε : ℝ} {Y : KamPhase} (hY : kamNorm r Y ≤ ε) :
    ‖Y.2.2.1‖ + ‖Y.2.2.2‖ ≤ r * ε := by
  unfold kamNorm at hY
  have h1 : 0 ≤ ‖Y.1‖ := norm_nonneg _
  have h2 : 0 ≤ ‖Y.2.1‖ / r ^ 2 := by positivity
  have h3 : ‖Y.2.2.1‖ / r + ‖Y.2.2.2‖ / r ≤ ε := by linarith
  rw [← add_div, div_le_iff₀ hr] at h3
  linarith

theorem kamNorm_fderiv_normal_le (hr : 0 < r) (hX : DifferentiableOn ℂ X (kamDomain s r)) {ε : ℝ}
    (hb : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε) (hε : 0 ≤ ε) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 s) {m : ℝ} (hm : 0 < m) {d : KamPhase} (hd1 : d.1 = 0)
    (hd2 : d.2.1 = 0) (hdm : ‖d.2.2.1‖ + ‖d.2.2.2‖ ≤ m) :
    kamNorm r (fderiv ℂ X (stepW0L θ) d) ≤ ε * m / r := by
  haveI : Fact (0 < r) := ⟨hr⟩
  set w0 := stepW0L θ with hw0
  have hmem : ∀ l ∈ ball (0 : ℂ) (r / m), w0 + l • d ∈ kamDomain s r := by
    intro l hl
    rw [mem_ball_zero_iff, lt_div_iff₀ hm] at hl
    refine ⟨fun i => ?_, ?_, ?_⟩
    · have : (w0 + l • d).1 = θ := by simp [hw0, stepW0L_apply, hd1]
      rw [this]; exact hθ i
    · have : (w0 + l • d).2.1 = 0 := by simp [hw0, stepW0L_apply, hd2]
      rw [this]; simpa using pow_pos hr 2
    · have e : ‖(w0 + l • d).2.2.1‖ + ‖(w0 + l • d).2.2.2‖ =
          ‖l‖ * (‖d.2.2.1‖ + ‖d.2.2.2‖) := by
        simp [hw0, stepW0L_apply, norm_smul, mul_add]
      rw [e]
      calc ‖l‖ * (‖d.2.2.1‖ + ‖d.2.2.2‖) ≤ ‖l‖ * m :=
            mul_le_mul_of_nonneg_left hdm (norm_nonneg _)
        _ < r := hl
  set f : ℂ → StepPhase r := fun l => StepPhase.ofK (X (w0 + l • d)) with hf
  have hline : ∀ l : ℂ, HasDerivAt (fun l : ℂ => w0 + l • d) d l := fun l => by
    simpa using ((hasDerivAt_id l).smul_const d).const_add w0
  have hfd : DifferentiableOn ℂ f (ball 0 (r / m)) := by
    intro l hl
    have h1 : DifferentiableAt ℂ X (w0 + l • d) :=
      hX.differentiableAt ((kamDomain_isOpen s r).mem_nhds (hmem l hl))
    have h2 : DifferentiableAt ℂ (fun l : ℂ => X (w0 + l • d)) l :=
      h1.comp l (hline l).differentiableAt
    exact ((stepOfKCLM r).differentiableAt.comp l h2).differentiableWithinAt
  have hfb : ∀ l ∈ ball (0 : ℂ) (r / m), ‖f l‖ ≤ ε := fun l hl => hb _ (hmem l hl)
  have hc := norm_fderiv_le_div_of_ball (by positivity : 0 < r / m) hε hfd hfb
  have hder : HasDerivAt (fun l : ℂ => X (w0 + l • d)) (fderiv ℂ X w0 d) 0 := by
    have h1 : HasFDerivAt X (fderiv ℂ X w0) (w0 + (0 : ℂ) • d) := by
      simpa using (hX.differentiableAt ((kamDomain_isOpen s r).mem_nhds
        (by simpa using hmem 0 (by simp [hm, hr]) ))).hasFDerivAt
    exact h1.comp_hasDerivAt 0 (hline 0)
  have hder' : HasDerivAt f (StepPhase.ofK (r := r) (fderiv ℂ X w0 d)) 0 :=
    (stepOfKCLM r).hasFDerivAt.comp_hasDerivAt 0 hder
  have hnorm : ‖StepPhase.ofK (r := r) (fderiv ℂ X w0 d)‖ ≤ ε / (r / m) := by
    have h3 : StepPhase.ofK (r := r) (fderiv ℂ X w0 d) = fderiv ℂ f 0 1 := by
      show _ = deriv f 0
      exact hder'.deriv.symm
    rw [h3]
    refine ((fderiv ℂ f 0).le_opNorm 1).trans ?_
    simpa using hc
  show ‖StepPhase.ofK (r := r) (fderiv ℂ X w0 d)‖ ≤ _
  refine hnorm.trans (le_of_eq ?_)
  field_simp

theorem norm_homSqrt2_inv_le : ‖homSqrt2⁻¹‖ ≤ 1 := by
  rw [norm_inv, norm_homSqrt2]
  exact inv_le_one_of_one_le₀ (by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num))

/-- Bound of `‖DX(w₀) ι z‖` in the normal directions. -/
theorem kamNorm_fderiv_iota_le (hr : 0 < r) (hX : DifferentiableOn ℂ X (kamDomain s r)) {ε : ℝ}
    (hb : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε) (hε : 0 ≤ ε) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 s) (z : HomL2) :
    (‖(fderiv ℂ X (stepW0L θ) (stepIotaZ z)).2.2.1‖ + ‖(fderiv ℂ X (stepW0L θ) (stepIotaZ
        z)).2.2.2‖ ≤
        2 * ε * ‖z‖) ∧
    (‖(fderiv ℂ X (stepW0L θ) (stepIotaZb z)).2.2.1‖ + ‖(fderiv ℂ X (stepW0L θ) (stepIotaZb
        z)).2.2.2‖ ≤
        2 * ε * ‖z‖) := by
  have hc := norm_homSqrt2_inv_le
  have hz0 := norm_nonneg z
  by_cases hz : z = 0
  · subst hz; simp
  have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  constructor
  · have hdm : ‖(stepIotaZ z).2.2.1‖ + ‖(stepIotaZ z).2.2.2‖ ≤ 2 * ‖z‖ := by
      simp only [stepIotaZ_apply, norm_smul, norm_mul, Complex.norm_I, norm_neg, one_mul]
      nlinarith
    have := kamNorm_fderiv_normal_le hr hX hb hε hθ (by positivity : 0 < 2 * ‖z‖)
      (d := stepIotaZ z) rfl rfl hdm
    have h2 := norm_normal_le_kamNorm hr this
    refine h2.trans (le_of_eq ?_)
    field_simp
  · have hdm : ‖(stepIotaZb z).2.2.1‖ + ‖(stepIotaZb z).2.2.2‖ ≤ 2 * ‖z‖ := by
      simp only [stepIotaZb_apply, norm_smul, norm_mul, Complex.norm_I, one_mul]
      nlinarith
    have := kamNorm_fderiv_normal_le hr hX hb hε hθ (by positivity : 0 < 2 * ‖z‖)
      (d := stepIotaZb z) rfl rfl hdm
    have h2 := norm_normal_le_kamNorm hr this
    refine h2.trans (le_of_eq ?_)
    field_simp

section blocks

variable (hr : 0 < r) (hX : DifferentiableOn ℂ X (kamDomain s r)) {ε : ℝ}
  (hb : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε) (hε : 0 ≤ ε) {θ : Fin 2 → ℂ}
  (hθ : θ ∈ complexStrip 2 s)
include hr hX hb hε hθ

theorem norm_tP_le : ‖tP X θ‖ ≤ 2 * ε := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
  have h := (kamNorm_fderiv_iota_le hr hX hb hε hθ z).1
  have h2 := norm_stepZb_le (fderiv ℂ X (stepW0L θ) (stepIotaZ z))
  simp only [tP, blockP, smul_apply, ContinuousLinearMap.comp_apply, norm_smul, norm_div,
    norm_neg, Complex.norm_I, Complex.norm_two]
  nlinarith [norm_nonneg z, norm_nonneg (stepZb (fderiv ℂ X (stepW0L θ) (stepIotaZ z)))]

theorem norm_tP'_le : ‖tP' X θ‖ ≤ 2 * ε := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
  have h := (kamNorm_fderiv_iota_le hr hX hb hε hθ z).2
  have h2 := norm_stepZ_le (fderiv ℂ X (stepW0L θ) (stepIotaZb z))
  simp only [tP', blockP', smul_apply, ContinuousLinearMap.comp_apply, norm_smul, norm_div,
    Complex.norm_I, Complex.norm_two]
  nlinarith [norm_nonneg z, norm_nonneg (stepZ (fderiv ℂ X (stepW0L θ) (stepIotaZb z)))]

theorem norm_tQ_le : ‖tQ X θ‖ ≤ 2 * ε := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
  have h := (kamNorm_fderiv_iota_le hr hX hb hε hθ z).1
  have h2 := norm_stepZ_le (fderiv ℂ X (stepW0L θ) (stepIotaZ z))
  simp only [tQ, blockQ, smul_apply, ContinuousLinearMap.comp_apply, norm_smul, Complex.norm_I,
    one_mul]
  linarith

theorem norm_tQt_le : ‖tQt X θ‖ ≤ 2 * ε := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
  have h := (kamNorm_fderiv_iota_le hr hX hb hε hθ z).2
  have h2 := norm_stepZb_le (fderiv ℂ X (stepW0L θ) (stepIotaZb z))
  simp only [tQt, blockQt, smul_apply, ContinuousLinearMap.comp_apply, norm_smul, norm_neg,
    Complex.norm_I, one_mul]
  linarith

end blocks

theorem norm_tB_le (hr : 0 < r) {ε : ℝ} (hb : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε)
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 s) : ‖tB X θ‖ ≤ 2 * Real.pi * ε := by
  have hz := hb _ (stepW0L_mem hr hθ)
  have h1 : ‖(X (stepW0L θ)).1‖ ≤ ε := by
    unfold kamNorm at hz
    have : 0 ≤ ‖(X (stepW0L θ)).2.1‖ / r ^ 2 := by positivity
    have : 0 ≤ ‖(X (stepW0L θ)).2.2.1‖ / r := by positivity
    have : 0 ≤ ‖(X (stepW0L θ)).2.2.2‖ / r := by positivity
    linarith
  have e : tB X θ = ((2 * Real.pi : ℂ)) • (X (stepW0L θ)).1 := by
    funext i; simp [tB]
  rw [e, norm_smul]
  have : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul]; simp [abs_of_pos Real.pi_pos]
  rw [this]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

theorem norm_tCp_le (hr : 0 < r) {ε : ℝ} (hb : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε)
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 s) : ‖tCp X θ‖ ≤ r * ε := by
  have h := norm_normal_le_kamNorm hr (hb _ (stepW0L_mem hr hθ))
  unfold tCp
  rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
  exact (norm_stepZb_le _).trans h

theorem norm_tCm_le (hr : 0 < r) {ε : ℝ} (hb : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε)
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 s) : ‖tCm X θ‖ ≤ r * ε := by
  have h := norm_normal_le_kamNorm hr (hb _ (stepW0L_mem hr hθ))
  unfold tCm
  rw [norm_smul, Complex.norm_I, one_mul]
  exact (norm_stepZ_le _).trans h

end KAM.Wave
