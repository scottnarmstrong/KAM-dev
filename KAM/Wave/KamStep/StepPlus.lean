/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.NewHamBracket
public import KAM.Wave.KamStep.StepMargin
public import KAM.Wave.KamStep.StepSolve
public import KAM.Wave.KamStep.FlowStepBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The concrete new Hamiltonian `P_+` (blueprint-W `bpW:w5:new-ham` (ii))

Concrete instantiation of the abstract transport engine on `StepPhase r`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

variable {a p pb s r σ η M : ℝ}

/-- The concrete flow data: `F = G = StepPhase r`, `ι = stepEmbedCLM`, `Z = stepFieldS FT`. -/
abbrev stepZF (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (FT : HomTaylor_gen a p pb (s - σ))
    (r : ℝ) : StepPhase r → StepPhase r := stepFieldS ha hp hpb FT r

theorem stepN_bound [Fact (0 < r)] (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hσs : 3 * σ < s) {FT : HomTaylor_gen a p pb (s - σ)}
    (h : FlowHyp (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r))
      (stepDomain r (s - σ) r) (stepDomain r (s - 2 * σ) (r / 2)) M (σ / 4))
    (hZ : DifferentiableOn ℂ (stepFieldS ha hp hpb FT r) (stepDomain r (s - σ) r))
    (hb : ∀ z ∈ stepDomain r (s - σ) r, ‖stepFieldS ha hp hpb FT r z‖ ≤ M)
    (hM : M ≤ σ / 1024) {w : StepPhase r} (hw : w ∈ stepDomain r (s - 3 * σ) (r / 4)) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖transNop (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb FT r) t w‖ ≤ 1 / 128 := by
  have hρ : 0 < σ / 8 := by positivity
  have hwU : w ∈ stepDomain r (s - 2 * σ) (r / 2) := by
    refine stepDomain_U_margin hσ hσ1 hσs hw (mem_ball_self hρ)
  have hball := stepDomain_U_margin hσ hσ1 hσs hw
  have h1 := norm_fderiv_smoothDisp_le h hZ hb hρ hball ht
  have hι : ‖stepEmbedCLM a p pb hpb r‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => by
      simpa using norm_stepEmbedCLM_apply_le a p pb hpb r g
  unfold transNop
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have ht1 : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
  have h2 : M * |t| / (σ / 8) ≤ 1 / 128 := by
    rw [div_le_iff₀ hρ]
    have : M * |t| ≤ M := by nlinarith [h.M_pos]
    nlinarith
  calc _ ≤ (M * |t| / (σ / 8)) * ‖stepEmbedCLM a p pb hpb r‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ (1 / 128) * 1 := by
        refine mul_le_mul h2 hι (norm_nonneg _) (by norm_num)
    _ = 1 / 128 := mul_one _

end KAM.Wave
