/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepPlusAssemble
public import KAM.Wave.KamStep.StepPullbackBound
public import KAM.Wave.KamStep.StepNuIntegral
public import KAM.Wave.KamStep.StepBracket
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Bounds of the field of `P_+` (blueprint-W `bpW:w5:new-ham` (ii), `bpW:w5:step` (ii))

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

open KAM

variable {a p pb s r σ η Mf e₁ : ℝ} [Fact (0 < r)]

/-- **The pulled-back term**: bounds of `y_A = (1 + N_1)⁻¹ (X_P - X_R)(Φ w)` for two parameters. -/
theorem stepXplusA_bounds (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσs : 5 * σ < s) (hη0 : 0 < η) (hη : η ≤ 1 / 8)
    {X₁ X₂ : KamPhase → KamPhase} {T₁ T₂ : HomTaylor_gen a p pb s}
    {FT₁ FT₂ : HomTaylor_gen a p pb (s - σ)}
    (hF₁ : HomFieldBound_gen ha hp hpb r Mf FT₁) (hF₂ : HomFieldBound_gen ha hp hpb r Mf FT₂)
    (hM0 : 0 < Mf) (hMs : 16 * Mf ≤ σ * η ^ 2) {N₁ : ℝ} (hN₁ : 0 ≤ N₁)
    (hZZ : ∀ z ∈ stepDomain r (s - σ) r,
      ‖stepFieldS ha hp hpb FT₁ r z - stepFieldS ha hp hpb FT₂ r z‖ ≤ N₁)
    {Y0 Yd : ℝ} (hY0 : 0 ≤ Y0)
    (hY₁ : DifferentiableOn ℂ (fun x => X₁ x - stepField ha hp hpb T₁ x)
      (kamDomain (s - 3 * σ) (4 * (η * r))))
    (hY₂ : DifferentiableOn ℂ (fun x => X₂ x - stepField ha hp hpb T₂ x)
      (kamDomain (s - 3 * σ) (4 * (η * r))))
    (hb₁ : ∀ z ∈ kamDomain (s - 3 * σ) (4 * (η * r)),
      kamNorm (η * r) (X₁ z - stepField ha hp hpb T₁ z) ≤ Y0)
    (hb₂ : ∀ z ∈ kamDomain (s - 3 * σ) (4 * (η * r)),
      kamNorm (η * r) (X₂ z - stepField ha hp hpb T₂ z) ≤ Y0)
    (hd : ∀ z ∈ kamDomain (s - 3 * σ) (4 * (η * r)),
      kamNorm (η * r) ((X₁ z - stepField ha hp hpb T₁ z) - (X₂ z - stepField ha hp hpb T₂ z)) ≤ Yd)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 5 * σ) (η * r)) :
    let ι := stepEmbedCLM a p pb hpb r
    stepNu (η * r) (transSolve (transNop ι (stepFieldS ha hp hpb FT₁ r) 1 w)
        (stepXPS X₁ r (holoFlow (smoothField ι (stepFieldS ha hp hpb FT₁ r)) 1 w) -
          stepFieldS ha hp hpb T₁ r (holoFlow (smoothField ι (stepFieldS ha hp hpb FT₁ r)) 1 w)))
      ≤ 2 * Y0 ∧
    stepNu (η * r) (transSolve (transNop ι (stepFieldS ha hp hpb FT₁ r) 1 w)
        (stepXPS X₁ r (holoFlow (smoothField ι (stepFieldS ha hp hpb FT₁ r)) 1 w) -
          stepFieldS ha hp hpb T₁ r (holoFlow (smoothField ι (stepFieldS ha hp hpb FT₁ r)) 1 w)) -
      transSolve (transNop ι (stepFieldS ha hp hpb FT₂ r) 1 w)
        (stepXPS X₂ r (holoFlow (smoothField ι (stepFieldS ha hp hpb FT₂ r)) 1 w) -
          stepFieldS ha hp hpb T₂ r (holoFlow (smoothField ι (stepFieldS ha hp hpb FT₂ r)) 1 w)))
      ≤ 2 * (Yd + 2 * Y0 / σ * (η⁻¹ ^ 2 * (2 * N₁))) +
        4 * (η⁻¹ ^ 2 * (2 * N₁ / (σ / 8))) * Y0 := by
  intro ι
  have hr : 0 < r := Fact.out
  have hη2 : η ^ 2 ≤ 1 / 64 := by nlinarith
  have hMσ : Mf ≤ σ / 1024 := by nlinarith
  have hMδ : Mf < σ / 4 := by linarith
  have hF1 := stepFlowHyp_concrete' (S := s) ha hp hpb FT₁ r hσ hσ1 (by linarith : 2 * σ < s)
    le_rfl hF₁ hM0 hMδ
  have hF2 := stepFlowHyp_concrete' (S := s) ha hp hpb FT₂ r hσ hσ1 (by linarith : 2 * σ < s)
    le_rfl hF₂ hM0 hMδ
  have hU'sub : stepDomain r (s - 5 * σ) (η * r) ⊆ stepDomain r (s - 3 * σ) (r / 4) :=
    stepDomain_mono' (by linarith) (by positivity) (by nlinarith)
  have hU'U : stepDomain r (s - 5 * σ) (η * r) ⊆ stepDomain r (s - 2 * σ) (r / 2) :=
    hU'sub.trans (stepDomain_mono' (by linarith) (by positivity) (by linarith))
  have hq1 : ‖transNop ι (stepFieldS ha hp hpb FT₁ r) 1 w‖ < 1 :=
    lt_of_le_of_lt (stepN_le' ha hp hpb hσ hσ1 (by linarith : 3 * σ < s) hF₁ hM0 hMσ (hU'sub hw)
      ⟨by norm_num, le_rfl⟩) (by norm_num)
  have hq2 : ‖transNop ι (stepFieldS ha hp hpb FT₂ r) 1 w‖ < 1 :=
    lt_of_le_of_lt (stepN_le' ha hp hpb hσ hσ1 (by linarith : 3 * σ < s) hF₂ hM0 hMσ (hU'sub hw)
      ⟨by norm_num, le_rfl⟩) (by norm_num)
  have hy₁ := transSolve_spec hq1 (stepXPS X₁ r (holoFlow (smoothField ι (stepFieldS ha hp hpb FT₁ r)) 1 w) -
          stepFieldS ha hp hpb T₁ r (holoFlow (smoothField ι (stepFieldS ha hp hpb FT₁ r)) 1 w))
  have hy₂ := transSolve_spec hq2 (stepXPS X₂ r (holoFlow (smoothField ι (stepFieldS ha hp hpb FT₂ r)) 1 w) -
          stepFieldS ha hp hpb T₂ r (holoFlow (smoothField ι (stepFieldS ha hp hpb FT₂ r)) 1 w))
  have := stepPullback_bounds ha hp hpb hσ hσ1 hσs hη0 hη hF₁ hF₂ hM0 hMs hN₁ hZZ hY0
    hY₁ hY₂ hb₁ hb₂ hd hw (t := 1) ⟨by norm_num, le_rfl⟩ hy₁ hy₂
  exact this

end KAM.Wave
