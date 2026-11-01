/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepSolve
public import KAM.Wave.KamStep.TaylorSmoothing
public import KAM.Wave.KamStep.FlowEquivariant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Periodicity of the Taylor objects (blueprint-W `bpW:w5:flow` (iv), step `f-real`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

For `T ∈ 𝒯_s`: `waveStepFun T` and `stepField T` are invariant under the angle translations
`stepTau k` (components `1`-periodic, hence so are their `θ`-derivatives).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s : ℝ}

theorem stepZ_add_tau (w : KamPhase) (k : Fin 2) : stepZ (w + stepTau k) = stepZ w := by
  obtain ⟨θ, y, u, v⟩ := w
  simp [stepTau, stepZ_apply]

theorem stepZb_add_tau (w : KamPhase) (k : Fin 2) : stepZb (w + stepTau k) = stepZb w := by
  obtain ⟨θ, y, u, v⟩ := w
  simp [stepTau, stepZb_apply]

/-- `stepField T` is periodic in the angles. -/
theorem stepField_add_tau (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a p pb s)
    {w : KamPhase} (hw : w.1 ∈ complexStrip 2 s) (k : Fin 2) :
    stepField ha hp hpb T (w + stepTau k) = stepField ha hp hpb T w := by
  have h1 : (w + stepTau k).1 = w.1 + Pi.single k 1 := by simp [stepTau]
  have h2 : (w + stepTau k).2.1 = w.2.1 := by simp [stepTau]
  have pa := T.comp_a0.2.1 k
  have pb' := T.comp_b.2.1 k
  have pcp := T.comp_cp.2.1 k
  have pcm := T.comp_cm.2.1 k
  have pP := T.comp_P.2.1 k
  have pP' := T.comp_P'.2.1 k
  have pQ := T.comp_Q.2.1 k
  have pQt := T.comp_Qt.2.1 k
  simp only [stepField, h1, h2, stepZ_add_tau, stepZb_add_tau, homRtheta_gen, homRu_gen, homRv_gen,
    homRz_gen, homRzb_gen, pb' _ hw, pcp _ hw, pcm _ hw, pP _ hw, pP' _ hw, pQ _ hw, pQt _ hw,
    fun i => homPartial_periodic T.comp_a0.2.1 i k hw,
    fun i => homPartial_periodic T.comp_b.2.1 i k hw,
    fun i => homPartial_periodic T.comp_cp.2.1 i k hw,
    fun i => homPartial_periodic T.comp_cm.2.1 i k hw,
    fun i => homPartial_periodic T.comp_P.2.1 i k hw,
    fun i => homPartial_periodic T.comp_P'.2.1 i k hw,
    fun i => homPartial_periodic T.comp_Q.2.1 i k hw,
    fun i => homPartial_periodic T.comp_Qt.2.1 i k hw]

/-- `waveStepFun T` is periodic in the angles. -/
theorem stepFun_add_tau (ha : 0 ≤ a) (hpp : 0 ≤ p + pb) (T : HomTaylor_gen a p pb s)
    {w : KamPhase} (hw : w.1 ∈ complexStrip 2 s) (k : Fin 2) :
    waveStepFun ha hpp T (w + stepTau k) = waveStepFun ha hpp T w := by
  have h1 : (w + stepTau k).1 = w.1 + Pi.single k 1 := by simp [stepTau]
  have h2 : (w + stepTau k).2.1 = w.2.1 := by simp [stepTau]
  simp only [waveStepFun, h1, h2, stepZ_add_tau, stepZb_add_tau, T.comp_a0.2.1 k _ hw,
    T.comp_b.2.1 k _ hw, T.comp_cp.2.1 k _ hw, T.comp_cm.2.1 k _ hw, T.comp_P.2.1 k _ hw,
    T.comp_P'.2.1 k _ hw, T.comp_Q.2.1 k _ hw]

end KAM.Wave
