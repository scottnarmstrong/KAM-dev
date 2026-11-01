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

end bounds

end bracket

end KAM.Wave
