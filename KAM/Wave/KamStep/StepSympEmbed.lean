/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepCLM
public import KAM.Wave.KamStep.TaylorFieldDiff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The embedded field pairs like the `p_+` field (blueprint-W `bpW:w5:flow`, `bpW:w5:omega`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`ϖ_{p,p}(ι X, W) = ϖ_{p,p_+}(X, W)`: pairing the `p`-weighted image of a `p_+`-representative
against a `p`-representative is the pairing of `X` itself (with the weight `1/(ω_p ω_{p_+})`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb : ℝ}

theorem stepPairCLM_embed (ha : 0 ≤ a) (hpb : p ≤ pb) (hpp : 0 ≤ p + p) (hpp' : 0 ≤ p + pb)
    (c z : HomL2) :
    stepPairCLM (q := p) (q' := p) ha hpp (homEmbed_gen a p pb hpb c) z =
      stepPairCLM (q := p) (q' := pb) ha hpp' c z := by
  show homPairF (weightedDiagCLM (stepWinv a p p) _ (homEmbed_gen a p pb hpb c)) z =
    homPairF (weightedDiagCLM (stepWinv a p pb) _ c) z
  unfold homPairF
  refine tsum_congr fun j => ?_
  simp only [weightedDiagCLM_apply, homEmbed_gen, homEmbedCoef_gen, stepWinv]
  have h1 := homWt_pos a p j
  have h2 := homWt_pos a pb j
  push_cast
  field_simp

/-- `ϖ_{p,p}(ι X, W) = ϖ_{p,p_+}(X, W)`. -/
theorem stepSymp_embed (ha : 0 ≤ a) (hpb : p ≤ pb) (hpp : 0 ≤ p + p) (hpp' : 0 ≤ p + pb)
    (X W : KamPhase) :
    stepSymp (q := p) (q' := p) ha hpp (kamHomEmbed a p pb hpb X) W =
      stepSymp (q := p) (q' := pb) ha hpp' X W := by
  unfold stepSymp
  rw [kamHomEmbed_apply]
  simp only
  rw [stepPairCLM_embed ha hpb hpp hpp', stepPairCLM_embed ha hpb hpp hpp']

end KAM.Wave
