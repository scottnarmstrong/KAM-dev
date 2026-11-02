/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepFieldBound
public import KAM.Wave.KamStep.TaylorEst
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Margins of the step domains (blueprint-W `bpW:w5:flow` step `f-der`, `bpW:w5:pullback` step
`p-dy`)

`stepDomain_U_margin`: every `w ∈ D(s-3σ, r/4)` has `B(w, σ/8) ⊆ D(s-2σ, r/2)` in the norm
`|·|_{p,r}` of `StepPhase r`.
-/

@[expose] public noncomputable section

open Metric

namespace KAM.Wave

theorem stepDomain_U_margin {s σ r : ℝ} [Fact (0 < r)] (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσs : 3 * σ < s) {w : StepPhase r} (hw : w ∈ stepDomain r (s - 3 * σ) (r / 4)) :
    ball w (σ / 8) ⊆ stepDomain r (s - 2 * σ) (r / 2) := by
  have hr : 0 < r := Fact.out
  intro z hz
  rw [mem_ball, dist_eq_norm, stepPhase_norm_eq] at hz
  have hz4 : kamNorm (r / 2) (StepPhase.toK z - StepPhase.toK w) < σ / 2 := by
    have h1 := kamNorm_le_ratio_sq (r₁ := r / 2) (r₂ := r) (by positivity) (by linarith)
      (StepPhase.toK z - StepPhase.toK w)
    have : (r / (r / 2)) ^ 2 = 4 := by field_simp; norm_num
    rw [this] at h1
    have hz' : kamNorm r (StepPhase.toK z - StepPhase.toK w) < σ / 8 := hz
    linarith
  have hw' : StepPhase.toK w ∈ kamDomain ((s - σ) - 2 * σ) (r / 2 / 2) := by
    have e1 : (s - σ) - 2 * σ = s - 3 * σ := by ring
    have e2 : r / 2 / 2 = r / 4 := by ring
    rw [e1, e2]; exact hw
  have h := kamDomain_add_mem (s := s - σ) hσ hσ1 (by linarith) (by positivity : 0 < r / 2) hw' hz4
  have e : StepPhase.toK w + (StepPhase.toK z - StepPhase.toK w) = StepPhase.toK z := by
    rw [add_sub_cancel]
  rw [e] at h
  have e3 : (s - σ) - σ = s - 2 * σ := by ring
  rw [e3] at h
  exact h

end KAM.Wave
