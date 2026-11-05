/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Analytic.Flow.Holomorphic

/-!
# Time derivative along the flow (`bpW:w5:flow-calc` (v), step `c-time`)

`d/dt G(φ^t w) = DG(φ^t w) X(φ^t w)` for `G` differentiable at `φ^t w`
(`hasDerivWithinAt_comp_holoFlow`), and the integrated form `G(φ^t w) - G(w) = ∫₀ᵗ …` for `C¹` `G`
is the fundamental theorem of calculus on the resulting continuous derivative.
-/

@[expose] public section

open Set Metric

namespace KAM.Wave

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {X : F → F} {V U : Set F} {M δ : ℝ} (h : FlowHyp X V U M δ)
include h

theorem hasDerivWithinAt_comp_holoFlow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {G : F → E} {DG : F →L[ℂ] E} {w : F} (hw : w ∈ U)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (hG : HasFDerivAt G DG (holoFlow X t w)) :
    HasDerivWithinAt (fun s => G (holoFlow X s w)) (DG (X (holoFlow X t w))) (Icc (-1) 1) t := by
  have h1 := hasDerivWithinAt_holoFlow h hw ht
  have h2 : HasFDerivAt G (DG.restrictScalars ℝ) (holoFlow X t w) := hG.restrictScalars ℝ
  exact h2.comp_hasDerivWithinAt t h1

end KAM.Wave
