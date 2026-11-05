/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.FlowSymplectic
public import KAM.Wave.KamStep.StepFieldBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Symplecticity of `Φ` (blueprint-W `bpW:w5:flow-calc` (ii), `bpW:w5:step` (v))

`stepFlow_symplectic`: `ϖ(Dφ^t(w) W, Dφ^t(w) W') = ϖ(W, W')` for `w ∈ D(s-2σ, r/2)`, `|t| ≤ 1`, on
the
concrete flow of `X_F` (`B = ϖ_{p,p}`; the skewness of `DX_F` is `stepFieldS_skew`).
-/

@[expose] public noncomputable section

open Set

namespace KAM.Wave

open KAM

variable {a p pb s r σ Mf : ℝ} [Fact (0 < r)]

theorem stepFlow_symplectic (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσs : 2 * σ < s) (FT : HomTaylor_gen a p pb (s - σ))
    (hF : HomFieldBound_gen ha hp hpb r Mf FT) (hMf0 : 0 < Mf) (hMδ : Mf < σ / 4)
    {w : StepPhase r} (hw : w ∈ stepDomain r (s - 2 * σ) (r / 2)) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    (W W' : StepPhase r) :
    stepSympCLM (q := p) (q' := p) ha (by linarith) r
        (fderiv ℂ (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
          (stepFieldS ha hp hpb FT r)) t) w W)
        (fderiv ℂ (holoFlow (smoothField (stepEmbedCLM a p pb hpb r)
          (stepFieldS ha hp hpb FT r)) t) w W') =
      stepSympCLM (q := p) (q' := p) ha (by linarith) r W W' := by
  have hFlow := stepFlowHyp_concrete' (S := s) ha hp hpb FT r hσ hσ1 hσs le_rfl hF hMf0 hMδ
  exact holoFlow_preserves_form hFlow _ (fun z hz x y =>
    stepFieldS_skew ha hp hpb FT r (stepDomain_theta_mem le_rfl hz) x y) hw ht W W'

end KAM.Wave
