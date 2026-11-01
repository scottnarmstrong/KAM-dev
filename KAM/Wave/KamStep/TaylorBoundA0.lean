/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.TaylorBound
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Boundedness of `a(θ) = P(θ,0,0,0)` (blueprint-W `bpW:w5:taylor` (i), step `t-comp`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`P(θ,0,0,0)` is `1`-periodic and its `θ`-gradient is `-2π X^y`, bounded by `2π r² ε`; hence it is
bounded on the strip by its sup over the unit cube plus `4π r² ε s`.
-/

@[expose] public noncomputable section

open Metric Set Filter Topology

namespace KAM.Wave

open KAM

variable {a p pb s r : ℝ} {P : KamPhase → ℂ} {X : KamPhase → KamPhase}

/-- The real points of the angle slice. -/
def realPt (x : Fin 2 → ℝ) : Fin 2 → ℂ := fun i => (x i : ℂ)

theorem realPt_mem_strip (hs : 0 < s) (x : Fin 2 → ℝ) : realPt x ∈ complexStrip 2 s := fun i => by
  simpa [realPt] using hs

theorem tA0_real_bound (ha : 0 ≤ a) (hqq : 0 ≤ pb + p) (hs : 0 < s) (hr : 0 < r)
    (hP : IsSmoothing (p := p) ha hqq (kamDomain s r) P X)
    (hper : ∀ i, ∀ w ∈ kamDomain s r, P (w + stepTau i) = P w) :
    ∃ M0 : ℝ, ∀ x : Fin 2 → ℝ, ‖tA0 P (realPt x)‖ ≤ M0 := by
  set Q : (Fin 2 → ℝ) → ℂ := fun x => tA0 P (realPt x) with hQ
  have hcont : Continuous Q := by
    have h1 : Continuous fun x : Fin 2 → ℝ => stepW0L (realPt x) := by
      unfold realPt; exact stepW0L.continuous.comp (by fun_prop)
    exact hP.holoP.continuousOn.comp_continuous h1 (fun x => stepW0L_mem hr (realPt_mem_strip hs x))
  have hper1 : ∀ i y, Q (y + Pi.single i 1) = Q y := fun i y => by
    have : realPt (y + Pi.single i 1) = realPt y + Pi.single i 1 := by
      funext j; by_cases h : j = i <;> simp [realPt, Pi.single_apply, h]
    simp only [hQ]
    rw [this]
    exact tA0_periodic ha hqq hr hP hper i (realPt_mem_strip hs y)
  obtain ⟨M0, hM0⟩ := (isCompact_Icc (a := (0 : Fin 2 → ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨M0, fun x => ?_⟩
  have hper_coord : ∀ i (y : Fin 2 → ℝ), Q y = Q (Function.update y i (Int.fract (y i))) := by
    intro i y
    have hp : Function.Periodic (fun t : ℝ => Q (Function.update y i t)) 1 := fun t => by
      have : Function.update y i (t + 1) = Function.update y i t + Pi.single i 1 := by
        funext j; by_cases h : j = i <;> simp [Function.update_apply, Pi.single_apply, h]
      simp only [this]; exact hper1 i _
    have h2 := hp.sub_int_mul_eq (x := y i) ⌊y i⌋
    simp only [mul_one] at h2
    have h3 : y i - (⌊y i⌋ : ℝ) = Int.fract (y i) := rfl
    rw [h3] at h2
    simpa using h2.symm
  have hx1 : Q x = Q (Function.update x 0 (Int.fract (x 0))) := hper_coord 0 x
  set x1 := Function.update x 0 (Int.fract (x 0))
  have hx2 : Q x1 = Q (Function.update x1 1 (Int.fract (x1 1))) := hper_coord 1 x1
  set x2 := Function.update x1 1 (Int.fract (x1 1))
  have hmem : x2 ∈ Icc (0 : Fin 2 → ℝ) 1 := by
    constructor <;> intro i <;> fin_cases i <;> simp [x2, x1, Int.fract_nonneg, (Int.fract_lt_one _).le]
  show ‖Q x‖ ≤ M0
  rw [hx1, hx2]
  exact hM0 x2 hmem

end KAM.Wave
