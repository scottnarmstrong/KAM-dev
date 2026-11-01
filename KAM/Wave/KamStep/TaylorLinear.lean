/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.TaylorEst
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Linearity of the Taylor field (blueprint-W `bpW:w5:taylor` (iv), parameter-Lipschitz part)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`taylorXR (X₁ - X₂) w = taylorXR X₁ w - taylorXR X₂ w` for fields holomorphic on `D(s,r)`.
-/

@[expose] public noncomputable section

open Metric

namespace KAM.Wave

variable {X₁ X₂ : KamPhase → KamPhase} {s r : ℝ} {w : KamPhase}

theorem taylorG_sub (t : ℂ) :
    taylorG (fun z => X₁ z - X₂ z) w t = taylorG X₁ w t - taylorG X₂ w t := by
  unfold taylorG scaleT
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp [smul_sub]

theorem taylorXR_sub (h₁ : DifferentiableOn ℂ X₁ (kamDomain s r))
    (h₂ : DifferentiableOn ℂ X₂ (kamDomain s r)) (hr : 0 < r) (hw : w ∈ kamDomain s r) :
    taylorXR (fun z => X₁ z - X₂ z) w = taylorXR X₁ w - taylorXR X₂ w := by
  have hρ : 0 < r / r := by rw [div_self hr.ne']; exact one_pos
  have c₁ := contDiffAt_taylorG h₁ hr hρ hw
  have c₂ := contDiffAt_taylorG h₂ hr hρ hw
  unfold taylorXR taylorField
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : taylorG (fun z => X₁ z - X₂ z) w = fun t => taylorG X₁ w t - taylorG X₂ w t :=
    funext fun t => taylorG_sub t
  rw [e, iteratedDeriv_fun_sub (c₁.of_le le_top) (c₂.of_le le_top), smul_sub]

end KAM.Wave
