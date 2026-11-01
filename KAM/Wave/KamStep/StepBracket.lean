/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepPlus
public import KAM.Wave.KamStep.StepSolve
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The brackets `{G, F}` for `G ∈ 𝒯_s` (blueprint-W `bpW:w5:new-ham` step `n-br`, `bpW:w5:commutator`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

On `U = D(s-2σ, r/2)`: `stepBrG TG z = B(ι Z_G z, ι Z_F z)` has derivative `B(ι stepBrZ TG z, ·)` with
`stepBrZ = DZ_G(ι Z_F) - DZ_F(ι Z_G)`; holomorphy, and the Cauchy bounds `‖stepBrZ‖ ≤ 4 e M/σ`
(`‖Z_G‖ ≤ e`, `‖Z_F‖ ≤ M`).
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

variable {a p pb s r σ M e : ℝ} [Fact (0 < r)]

section bracket

variable (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (TG : HomTaylor_gen a p pb s)
  (FT : HomTaylor_gen a p pb (s - σ))

/-- `B(ι Z_G, ι Z_F)`. -/
def stepBrG : StepPhase r → ℂ := fun z =>
  stepSympCLM (q := p) (q' := p) ha (by linarith) r
    (stepEmbedCLM a p pb hpb r (stepFieldS ha hp hpb TG r z))
    (stepEmbedCLM a p pb hpb r (stepFieldS ha hp hpb FT r z))

/-- The bracket field `DZ_G(ι Z_F) - DZ_F(ι Z_G)`. -/
def stepBrZ : StepPhase r → StepPhase r := fun z =>
  fderiv ℂ (stepFieldS ha hp hpb TG r) z (stepEmbedCLM a p pb hpb r (stepFieldS ha hp hpb FT r z)) -
    fderiv ℂ (stepFieldS ha hp hpb FT r) z (stepEmbedCLM a p pb hpb r (stepFieldS ha hp hpb TG r z))

variable {ha hp hpb TG FT}

theorem stepSkew_embedded {a' p' pb' s' : ℝ} (ha' : 0 ≤ a') (hp' : 0 ≤ p') (hpb' : p' ≤ pb')
    (T' : HomTaylor_gen a' p' pb' s') {x : StepPhase r}
    (hx : (StepPhase.toK x).1 ∈ complexStrip 2 s') (A C : StepPhase r) :
    stepSympCLM (q := p') (q' := p') ha' (by linarith) r
        (stepEmbedCLM a' p' pb' hpb' r (fderiv ℂ (stepFieldS ha' hp' hpb' T' r) x A)) C +
      stepSympCLM (q := p') (q' := p') ha' (by linarith) r A
        (stepEmbedCLM a' p' pb' hpb' r (fderiv ℂ (stepFieldS ha' hp' hpb' T' r) x C)) = 0 := by
  have h := stepFieldS_skew ha' hp' hpb' T' r hx A C
  rw [fderiv_smoothField (stepFieldS_differentiableAt ha' hp' hpb' T' r hx)] at h
  simpa using h

theorem stepBrG_hasFDerivAt (hσ : 0 < σ) (hσs : 2 * σ < s) {z : StepPhase r}
    (hz : z ∈ stepDomain r (s - 2 * σ) (r / 2)) :
    HasFDerivAt (stepBrG ha hp hpb TG FT)
      (stepSympCLM (q := p) (q' := p) ha (by linarith) r
        (stepEmbedCLM a p pb hpb r (stepBrZ ha hp hpb TG FT z))) z := by
  have hθs : (StepPhase.toK z).1 ∈ complexStrip 2 s := stepDomain_theta_mem (by linarith) hz
  have hθF : (StepPhase.toK z).1 ∈ complexStrip 2 (s - σ) := stepDomain_theta_mem (by linarith) hz
  have h := hasFDerivAt_bracket_smooth (ι := stepEmbedCLM a p pb hpb r)
    (stepSympCLM (q := p) (q' := p) ha (by linarith) r)
    (fun A C => stepSympCLM_antisymm ha (by linarith) r A C)
    (stepFieldS_differentiableAt ha hp hpb TG r hθs)
    (stepFieldS_differentiableAt ha hp hpb FT r hθF)
    (fun A C => stepSkew_embedded ha hp hpb TG hθs A C)
    (fun A C => stepSkew_embedded ha hp hpb FT hθF A C)
  exact h

section bounds

theorem stepFieldS_cauchy (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {s' S : ℝ}
    (T' : HomTaylor_gen a p pb s') (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hσS : 2 * σ < S)
    (hSs : S - σ ≤ s')
    {e : ℝ} (he : 0 ≤ e) (hX : HomFieldBound_gen ha hp hpb r e T') {z : StepPhase r}
    (hz : z ∈ stepDomain r (S - 2 * σ) (r / 2)) :
    ‖fderiv ℂ (stepFieldS ha hp hpb T' r) z‖ ≤ e / (σ / 2) := by
  have hball : ball z (2 * (σ / 4)) ⊆ stepDomain r (S - σ) r := stepDomain_margin hσ hσ1 hσS hz
  have hb2 : (2 * (σ / 4)) = σ / 2 := by ring
  rw [hb2] at hball
  refine norm_fderiv_le_div_of_ball (by positivity) he ?_ ?_
  · intro w hw
    exact (stepFieldS_differentiableAt ha hp hpb T' r
      (stepDomain_theta_mem hSs (hball hw))).differentiableWithinAt
  · intro w hw
    exact stepFieldS_bound ha hp hpb T' r hX hSs (hball hw)

theorem stepDomain_mono' {ρ s₁ s₂ r₁ r₂ : ℝ} (hs : s₁ ≤ s₂) (hr₁ : 0 < r₁) (hr : r₁ ≤ r₂) :
    stepDomain ρ s₁ r₁ ⊆ stepDomain ρ s₂ r₂ := fun W hW =>
  kamDomain_mono hs hr₁ hr hW

theorem stepBrZ_norm_le (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσs : 2 * σ < s) {e Mf : ℝ} (he : 0 ≤ e) (hMf : 0 ≤ Mf)
    (hTG : HomFieldBound_gen ha hp hpb r e TG) (hF : HomFieldBound_gen ha hp hpb r Mf FT)
    {z : StepPhase r} (hz : z ∈ stepDomain r (s - 2 * σ) (r / 2)) :
    ‖stepBrZ ha hp hpb TG FT z‖ ≤ 4 * e * Mf / σ := by
  have hr : 0 < r := Fact.out
  have hzV : z ∈ stepDomain r (s - σ) r := stepDomain_mono' (by linarith) (by positivity)
    (by linarith) hz
  have h1 := stepFieldS_cauchy (σ := σ) ha hp hpb TG hσ hσ1 hσs (by linarith) he hTG hz
  have h2 := stepFieldS_cauchy (σ := σ) (S := s) ha hp hpb FT hσ hσ1 hσs le_rfl hMf hF hz
  have hZG : ‖stepFieldS ha hp hpb TG r z‖ ≤ e :=
    stepFieldS_bound ha hp hpb TG r hTG (by linarith) hzV
  have hZF : ‖stepFieldS ha hp hpb FT r z‖ ≤ Mf :=
    stepFieldS_bound ha hp hpb FT r hF le_rfl hzV
  have hι := fun g : StepPhase r => norm_stepEmbedCLM_apply_le a p pb hpb r g
  unfold stepBrZ
  refine (norm_sub_le _ _).trans ?_
  have t1 : ‖fderiv ℂ (stepFieldS ha hp hpb TG r) z
      (stepEmbedCLM a p pb hpb r (stepFieldS ha hp hpb FT r z))‖ ≤ e / (σ / 2) * Mf :=
    ((fderiv ℂ (stepFieldS ha hp hpb TG r) z).le_opNorm _).trans
      (mul_le_mul h1 ((hι _).trans hZF) (norm_nonneg _) (by positivity))
  have t2 : ‖fderiv ℂ (stepFieldS ha hp hpb FT r) z
      (stepEmbedCLM a p pb hpb r (stepFieldS ha hp hpb TG r z))‖ ≤ Mf / (σ / 2) * e :=
    ((fderiv ℂ (stepFieldS ha hp hpb FT r) z).le_opNorm _).trans
      (mul_le_mul h2 ((hι _).trans hZG) (norm_nonneg _) (by positivity))
  have : e / (σ / 2) * Mf + Mf / (σ / 2) * e = 4 * e * Mf / σ := by field_simp; ring
  linarith

theorem stepFieldS_differentiableOn_theta (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {s' : ℝ}
    (T' : HomTaylor_gen a p pb s') :
    DifferentiableOn ℂ (stepFieldS ha hp hpb T' r)
      {z : StepPhase r | (StepPhase.toK z).1 ∈ complexStrip 2 s'} := fun z hz =>
  (stepFieldS_differentiableAt ha hp hpb T' r hz).differentiableWithinAt

theorem isOpen_theta_strip (s' : ℝ) :
    IsOpen {z : StepPhase r | (StepPhase.toK z).1 ∈ complexStrip 2 s'} :=
  (isOpen_complexStrip 2 s').preimage (continuous_fst.comp (stepPhase_toK_continuous r))

theorem stepBrZ_differentiableOn (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ)
    (hσs : 2 * σ < s) :
    DifferentiableOn ℂ (stepBrZ ha hp hpb TG FT) (stepDomain r (s - 2 * σ) (r / 2)) := by
  have hUs : ∀ z ∈ stepDomain r (s - 2 * σ) (r / 2),
      z ∈ {z : StepPhase r | (StepPhase.toK z).1 ∈ complexStrip 2 s} := fun z hz =>
    stepDomain_theta_mem (by linarith) hz
  have hUF : ∀ z ∈ stepDomain r (s - 2 * σ) (r / 2),
      z ∈ {z : StepPhase r | (StepPhase.toK z).1 ∈ complexStrip 2 (s - σ)} := fun z hz =>
    stepDomain_theta_mem (by linarith) hz
  have d1 := (differentiableOn_fderiv_of_holomorphic (isOpen_theta_strip s)
    (stepFieldS_differentiableOn_theta ha hp hpb TG)).mono hUs
  have d2 := (differentiableOn_fderiv_of_holomorphic (isOpen_theta_strip (s - σ))
    (stepFieldS_differentiableOn_theta ha hp hpb FT)).mono hUF
  have e1 : DifferentiableOn ℂ (fun z => stepEmbedCLM a p pb hpb r (stepFieldS ha hp hpb FT r z))
      (stepDomain r (s - 2 * σ) (r / 2)) :=
    (stepEmbedCLM a p pb hpb r).differentiable.comp_differentiableOn
      ((stepFieldS_differentiableOn_theta ha hp hpb FT).mono hUF)
  have e2 : DifferentiableOn ℂ (fun z => stepEmbedCLM a p pb hpb r (stepFieldS ha hp hpb TG r z))
      (stepDomain r (s - 2 * σ) (r / 2)) :=
    (stepEmbedCLM a p pb hpb r).differentiable.comp_differentiableOn
      ((stepFieldS_differentiableOn_theta ha hp hpb TG).mono hUs)
  exact (d1.clm_apply e1).sub (d2.clm_apply e2)

theorem norm_stepBrG_le (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ)
    (hσs : 2 * σ < s) {e Mf : ℝ} (hTG : HomFieldBound_gen ha hp hpb r e TG)
    (hF : HomFieldBound_gen ha hp hpb r Mf FT) {z : StepPhase r}
    (hz : z ∈ stepDomain r (s - 2 * σ) (r / 2)) :
    ‖stepBrG ha hp hpb TG FT z‖ ≤ (4 * Real.pi + 1) * r ^ 2 * (e * Mf) := by
  have hr : 0 < r := Fact.out
  have hzV : z ∈ stepDomain r (s - σ) r := stepDomain_mono' (by linarith) (by positivity)
    (by linarith) hz
  have hZG : ‖stepFieldS ha hp hpb TG r z‖ ≤ e :=
    stepFieldS_bound ha hp hpb TG r hTG (by linarith) hzV
  have hZF : ‖stepFieldS ha hp hpb FT r z‖ ≤ Mf :=
    stepFieldS_bound ha hp hpb FT r hF le_rfl hzV
  have hι := fun g : StepPhase r => norm_stepEmbedCLM_apply_le a p pb hpb r g
  unfold stepBrG
  refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
  have hB := norm_stepSympCLM_le (q := p) (q' := p) ha (by linarith : 0 ≤ p + p) r
  have h1 := (hι (stepFieldS ha hp hpb TG r z)).trans hZG
  have h2 := (hι (stepFieldS ha hp hpb FT r z)).trans hZF
  calc _ ≤ (4 * Real.pi + 1) * r ^ 2 * ‖stepEmbedCLM a p pb hpb r (stepFieldS ha hp hpb TG r z)‖ *
        ‖stepEmbedCLM a p pb hpb r (stepFieldS ha hp hpb FT r z)‖ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
          (norm_nonneg _)
    _ ≤ (4 * Real.pi + 1) * r ^ 2 * e * Mf := by
        have hc : 0 ≤ (4 * Real.pi + 1) * r ^ 2 := by positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 (norm_nonneg _)
          (by have := (norm_nonneg _).trans h1; positivity)
    _ = _ := by ring


theorem stepFieldS_sub (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {s' : ℝ}
    (T₁ T₂ : HomTaylor_gen a p pb s') {z : StepPhase r}
    (hz : (StepPhase.toK z).1 ∈ complexStrip 2 s') :
    stepFieldS ha hp hpb (T₁.homSub T₂) r z =
      stepFieldS ha hp hpb T₁ r z - stepFieldS ha hp hpb T₂ r z := by
  unfold stepFieldS
  rw [stepField_sub ha hp hpb T₁ T₂ hz]
  rfl

theorem fderiv_stepFieldS_sub (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {s' : ℝ}
    (T₁ T₂ : HomTaylor_gen a p pb s') {z : StepPhase r}
    (hz : (StepPhase.toK z).1 ∈ complexStrip 2 s') :
    fderiv ℂ (stepFieldS ha hp hpb (T₁.homSub T₂) r) z =
      fderiv ℂ (stepFieldS ha hp hpb T₁ r) z - fderiv ℂ (stepFieldS ha hp hpb T₂ r) z := by
  have hev : stepFieldS ha hp hpb (T₁.homSub T₂) r =ᶠ[nhds z]
      fun y => stepFieldS ha hp hpb T₁ r y - stepFieldS ha hp hpb T₂ r y := by
    filter_upwards [(isOpen_theta_strip (r := r) s').mem_nhds hz] with y hy using
      stepFieldS_sub ha hp hpb T₁ T₂ hy
  rw [hev.fderiv_eq]
  exact fderiv_sub (stepFieldS_differentiableAt ha hp hpb T₁ r hz)
    (stepFieldS_differentiableAt ha hp hpb T₂ r hz)


theorem stepBrZ_sub_norm_le (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσs : 2 * σ < s) {TG₂ : HomTaylor_gen a p pb s} {FT₂ : HomTaylor_gen a p pb (s - σ)}
    {e ΔG Mf N₁ : ℝ} (he : 0 ≤ e) (hΔG : 0 ≤ ΔG) (hMf : 0 ≤ Mf) (hN₁ : 0 ≤ N₁)
    (hTG₂ : HomFieldBound_gen ha hp hpb r e TG₂) (hFT₂ : HomFieldBound_gen ha hp hpb r Mf FT₂)
    (hTG : HomFieldBound_gen ha hp hpb r e TG)
    (hΔG' : HomFieldBound_gen ha hp hpb r ΔG (TG.homSub TG₂))
    (hF : HomFieldBound_gen ha hp hpb r Mf FT)
    (hΔF : HomFieldBound_gen ha hp hpb r N₁ (FT.homSub FT₂))
    {z : StepPhase r} (hz : z ∈ stepDomain r (s - 2 * σ) (r / 2)) :
    ‖stepBrZ ha hp hpb TG FT z - stepBrZ ha hp hpb TG₂ FT₂ z‖ ≤ 4 * (Mf * ΔG + e * N₁) / σ := by
  have hr : 0 < r := Fact.out
  have hzV : z ∈ stepDomain r (s - σ) r := stepDomain_mono' (by linarith) (by positivity)
    (by linarith) hz
  have hθs : (StepPhase.toK z).1 ∈ complexStrip 2 s := stepDomain_theta_mem (by linarith) hz
  have hθF : (StepPhase.toK z).1 ∈ complexStrip 2 (s - σ) := stepDomain_theta_mem (by linarith) hz
  have c1 := stepFieldS_cauchy (σ := σ) ha hp hpb (TG.homSub TG₂) hσ hσ1 hσs (by linarith) hΔG hΔG' hz
  have c2 := stepFieldS_cauchy (σ := σ) ha hp hpb TG₂ hσ hσ1 hσs (by linarith) he hTG₂ hz
  have c3 := stepFieldS_cauchy (σ := σ) (S := s) ha hp hpb (FT.homSub FT₂) hσ hσ1 hσs le_rfl hN₁
    hΔF hz
  have c4 := stepFieldS_cauchy (σ := σ) (S := s) ha hp hpb FT₂ hσ hσ1 hσs le_rfl hMf hFT₂ hz
  have d1 := fderiv_stepFieldS_sub ha hp hpb TG TG₂ hθs
  have d2 := fderiv_stepFieldS_sub ha hp hpb FT FT₂ hθF
  rw [d1] at c1
  rw [d2] at c3
  have bΔG : ‖stepFieldS ha hp hpb TG r z - stepFieldS ha hp hpb TG₂ r z‖ ≤ ΔG := by
    rw [← stepFieldS_sub ha hp hpb TG TG₂ hθs]
    exact stepFieldS_bound ha hp hpb _ r hΔG' (by linarith) hzV
  have bΔF : ‖stepFieldS ha hp hpb FT r z - stepFieldS ha hp hpb FT₂ r z‖ ≤ N₁ := by
    rw [← stepFieldS_sub ha hp hpb FT FT₂ hθF]
    exact stepFieldS_bound ha hp hpb _ r hΔF le_rfl hzV
  have bG : ‖stepFieldS ha hp hpb TG r z‖ ≤ e :=
    stepFieldS_bound ha hp hpb TG r hTG (by linarith) hzV
  have bF : ‖stepFieldS ha hp hpb FT r z‖ ≤ Mf := stepFieldS_bound ha hp hpb FT r hF le_rfl hzV
  have hι := fun g : StepPhase r => norm_stepEmbedCLM_apply_le a p pb hpb r g
  have hid : stepBrZ ha hp hpb TG FT z - stepBrZ ha hp hpb TG₂ FT₂ z =
      ((fderiv ℂ (stepFieldS ha hp hpb TG r) z - fderiv ℂ (stepFieldS ha hp hpb TG₂ r) z)
          (stepEmbedCLM a p pb hpb r (stepFieldS ha hp hpb FT r z)) +
        fderiv ℂ (stepFieldS ha hp hpb TG₂ r) z (stepEmbedCLM a p pb hpb r
          (stepFieldS ha hp hpb FT r z - stepFieldS ha hp hpb FT₂ r z))) -
      ((fderiv ℂ (stepFieldS ha hp hpb FT r) z - fderiv ℂ (stepFieldS ha hp hpb FT₂ r) z)
          (stepEmbedCLM a p pb hpb r (stepFieldS ha hp hpb TG r z)) +
        fderiv ℂ (stepFieldS ha hp hpb FT₂ r) z (stepEmbedCLM a p pb hpb r
          (stepFieldS ha hp hpb TG r z - stepFieldS ha hp hpb TG₂ r z))) := by
    unfold stepBrZ
    simp only [sub_apply, map_sub]
    abel
  rw [hid]
  have t1 : ‖(fderiv ℂ (stepFieldS ha hp hpb TG r) z - fderiv ℂ (stepFieldS ha hp hpb TG₂ r) z)
      (stepEmbedCLM a p pb hpb r (stepFieldS ha hp hpb FT r z))‖ ≤ ΔG / (σ / 2) * Mf :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul c1 ((hι _).trans bF) (norm_nonneg _) (by positivity))
  have t2 : ‖fderiv ℂ (stepFieldS ha hp hpb TG₂ r) z (stepEmbedCLM a p pb hpb r
      (stepFieldS ha hp hpb FT r z - stepFieldS ha hp hpb FT₂ r z))‖ ≤ e / (σ / 2) * N₁ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul c2 ((hι _).trans bΔF) (norm_nonneg _) (by positivity))
  have t3 : ‖(fderiv ℂ (stepFieldS ha hp hpb FT r) z - fderiv ℂ (stepFieldS ha hp hpb FT₂ r) z)
      (stepEmbedCLM a p pb hpb r (stepFieldS ha hp hpb TG r z))‖ ≤ N₁ / (σ / 2) * e :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul c3 ((hι _).trans bG) (norm_nonneg _) (by positivity))
  have t4 : ‖fderiv ℂ (stepFieldS ha hp hpb FT₂ r) z (stepEmbedCLM a p pb hpb r
      (stepFieldS ha hp hpb TG r z - stepFieldS ha hp hpb TG₂ r z))‖ ≤ Mf / (σ / 2) * ΔG :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul c4 ((hι _).trans bΔG) (norm_nonneg _) (by positivity))
  refine (norm_sub_le _ _).trans ?_
  have n1 := norm_add_le ((fderiv ℂ (stepFieldS ha hp hpb TG r) z -
      fderiv ℂ (stepFieldS ha hp hpb TG₂ r) z) (stepEmbedCLM a p pb hpb r (stepFieldS ha hp hpb FT r z)))
      (fderiv ℂ (stepFieldS ha hp hpb TG₂ r) z (stepEmbedCLM a p pb hpb r
          (stepFieldS ha hp hpb FT r z - stepFieldS ha hp hpb FT₂ r z)))
  have n2 := norm_add_le ((fderiv ℂ (stepFieldS ha hp hpb FT r) z -
      fderiv ℂ (stepFieldS ha hp hpb FT₂ r) z) (stepEmbedCLM a p pb hpb r (stepFieldS ha hp hpb TG r z)))
      (fderiv ℂ (stepFieldS ha hp hpb FT₂ r) z (stepEmbedCLM a p pb hpb r
          (stepFieldS ha hp hpb TG r z - stepFieldS ha hp hpb TG₂ r z)))
  have : ΔG / (σ / 2) * Mf + e / (σ / 2) * N₁ + (N₁ / (σ / 2) * e + Mf / (σ / 2) * ΔG) =
      4 * (Mf * ΔG + e * N₁) / σ := by field_simp; ring
  linarith

end bounds


theorem stepN_le' [Fact (0 < r)] (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hσs : 3 * σ < s) {FT : HomTaylor_gen a p pb (s - σ)}
    (hF : HomFieldBound_gen ha hp hpb r M FT) (hM0 : 0 < M) (hM : M ≤ σ / 1024)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 3 * σ) (r / 4)) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖transNop (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r) t w‖ ≤ 1 / 128 := by
  have hMδ : M < σ / 4 := by linarith
  have hFlow := stepFlowHyp_concrete' (S := s) ha hp hpb FT r hσ hσ1 (by linarith : 2 * σ < s)
    le_rfl hF hM0 hMδ
  have hVd : ∀ z ∈ stepDomain r (s - σ) r,
      z ∈ {z : StepPhase r | (StepPhase.toK z).1 ∈ complexStrip 2 (s - σ)} := fun z hz =>
    stepDomain_theta_mem le_rfl hz
  exact stepN_bound ha hp hpb hσ hσ1 hσs hFlow
    ((stepFieldS_differentiableOn_theta ha hp hpb FT).mono hVd)
    (fun z hz => stepFieldS_bound ha hp hpb FT r hF le_rfl hz) hM hw ht

end bracket

end KAM.Wave
